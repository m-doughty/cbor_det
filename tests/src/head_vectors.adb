--  cbor_det tests: the head helpers, which are ordinary functions and run
--  in every cell of the build matrix.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause

with Ada.Text_IO;
with Interfaces; use Interfaces;

with Cbor_Det;             use Cbor_Det;
with Cbor_Det.Proof;       use Cbor_Det.Proof;
with Cbor_Det.Proof.Heads; use Cbor_Det.Proof.Heads;

with Support; use Support;

package body Head_Vectors is

   type U64_List is array (Positive range <>) of Unsigned_64;

   Boundaries : constant U64_List :=
     [0, 1, 23, 24, 255, 256, 65_535, 65_536,
      2**32 - 1, 2**32, Unsigned_64'Last];

   type Width_List is array (Positive range <>) of Natural;
   Widths : constant Width_List := [1, 2, 4, 8];

   --  The additional information that announces an argument of W bytes.
   function Info_For (W : Natural) return Byte is
     (case W is when 1 => 24, when 2 => 25, when 4 => 26, when others => 27);

   --  The shortest width for A, 0 when A is in the initial byte. Written
   --  here from RFC 8949, section 4.2.1, not taken from the library.
   function Shortest_Width (A : Unsigned_64) return Natural is
     (if A < 24 then 0 elsif A < 2**8 then 1 elsif A < 2**16 then 2
      elsif A < 2**32 then 4 else 8);

   --  The head of major type M with argument A in W argument bytes
   --  (W = 0: A in the initial byte), built byte by byte.
   function Build (M : Byte; A : Unsigned_64; W : Natural) return Bytes is
      R : Bytes (1 .. 1 + W);
   begin
      if W = 0 then
         R (1) := M * 32 + Byte (A);
      else
         R (1) := M * 32 + Info_For (W);
         for K in 1 .. W loop
            R (1 + K) :=
              Byte (Shift_Right (A, 8 * (W - K)) and 16#FF#);
         end loop;
      end if;
      return R;
   end Build;

   procedure Expect (Cond : Boolean; What : String) is
   begin
      if Cond then
         Pass;
      else
         Fail (What);
      end if;
   end Expect;

   --  The head at B'First, which must hold exactly the shortest head of
   --  M and A, at the place it sits.
   procedure Check_Accepted (B : Bytes; M : Byte; A : Unsigned_64;
                             Len : Positive; What : String) is
      P : constant Positive := B'First;
   begin
      Expect (Head_Len (B (P)) = Len, What & ": length");
      Expect (Head_Fits (B, P), What & ": fits");
      if Head_Fits (B, P) then
         Expect (Arg (B, P) = A, What & ": argument");
         Expect (Shortest (B, P), What & ": shortest");
         Expect (Head_OK (B, P), What & ": accepted");
      end if;
      Expect (Major_Of (B (P)) = M, What & ": major type");
      Expect (Len_Of_Arg (A) = Len, What & ": Len_Of_Arg");
   end Check_Accepted;

   procedure Check_Wide (B : Bytes; A : Unsigned_64; What : String) is
      P : constant Positive := B'First;
   begin
      Expect (Head_Fits (B, P), What & ": wide form fits");
      if Head_Fits (B, P) then
         Expect (Arg (B, P) = A, What & ": wide form argument");
         Expect (not Shortest (B, P), What & ": wide form not shortest");
         Expect (not Head_OK (B, P), What & ": wide form refused");
      end if;
   end Check_Wide;

   procedure Check_Cut (B : Bytes; What : String) is
      P : constant Positive := B'First;
   begin
      Expect (not Head_Fits (B, P), What & ": truncation does not fit");
      Expect (not Head_OK (B, P), What & ": truncation refused");
   end Check_Cut;

   procedure Run is
      Passes : constant Natural := Passed;
      Fails  : constant Natural := Failed;
   begin
      for M in Byte range 0 .. 7 loop
         for A of Boundaries loop
            declare
               W    : constant Natural := Shortest_Width (A);
               E    : constant Bytes := Build (M, A, W);
               Name : constant String :=
                 "major" & M'Image & " argument" & A'Image;
            begin
               --  Encode_Head writes exactly these bytes.
               declare
                  H : constant Bytes := Encode_Head (M, A);
               begin
                  Expect (H'First = 1 and then H = E, Name & ": Encode_Head");
               end;
               Check_Accepted (E, M, A, E'Length, Name);
               Check_Accepted (At_Top (E), M, A, E'Length,
                               Name & " at the top");
               Check_Accepted (Rebase (E & [16#FF#, 16#00#], 7), M, A,
                               E'Length, Name & " with bytes after");
               --  The same argument in every wider form.
               for V of Widths loop
                  if V > W then
                     Check_Wide (Build (M, A, V), A,
                                 Name & " in" & V'Image & " bytes");
                     Check_Wide (At_Top (Build (M, A, V)), A,
                                 Name & " in" & V'Image & " bytes at top");
                  end if;
               end loop;
               for Cut in 1 .. E'Length - 1 loop
                  Check_Cut (E (1 .. Cut), Name & " cut to" & Cut'Image);
                  Check_Cut (At_Top (E (1 .. Cut)),
                             Name & " cut to" & Cut'Image & " at top");
               end loop;
            end;
         end loop;
         --  Additional information 28 to 31 is never a head.
         for Info in Byte range 28 .. 31 loop
            declare
               B : constant Bytes := [M * 32 + Info] & [1 .. 9 => 0];
            begin
               Expect (Head_Len (B (1)) = 0,
                       "info" & Info'Image & " major" & M'Image & ": length");
               Expect (not Head_Fits (B, 1),
                       "info" & Info'Image & " major" & M'Image & ": fits");
               Expect (not Head_OK (B, 1),
                       "info" & Info'Image & " major" & M'Image & ": ok");
            end;
         end loop;
      end loop;
      Ada.Text_IO.Put_Line ("head vectors: passed"
                            & Natural'Image (Passed - Passes) & ", failed"
                            & Natural'Image (Failed - Fails));
   end Run;

end Head_Vectors;
