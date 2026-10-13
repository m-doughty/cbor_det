--  cbor_det tests: the differential test against the reference decoder.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause

with Ada.Assertions;
with Ada.Exceptions;
with Ada.Real_Time;
with Ada.Streams;           use Ada.Streams;
with Ada.Streams.Stream_IO;
with Ada.Text_IO;           use Ada.Text_IO;
with Ada.Unchecked_Deallocation;
with Interfaces;

with Cbor_Det;             use Cbor_Det;
with Cbor_Det.Proof;       use Cbor_Det.Proof;
with Cbor_Det.Proof.Heads; use Cbor_Det.Proof.Heads;
with Cbor_Det.Proof.Det;   use Cbor_Det.Proof.Det;

with Ghost_Vectors;
with Support; use Support;

package body Differential is

   use type Interfaces.Unsigned_64;

   Enabled : Boolean := False;

   function Enable return Boolean is
   begin
      Enabled := True;
      return True;
   end Enable;

   function Ran return Boolean is (Enabled);

   --  Field N (from 1) of a line of tab-separated fields.
   function Field (Line : String; N : Positive) return String is
      Start : Natural := Line'First;
      Count : Positive := 1;
   begin
      for I in Line'Range loop
         if Line (I) = ASCII.HT then
            if Count = N then
               return Line (Start .. I - 1);
            end if;
            Count := Count + 1;
            Start := I + 1;
         end if;
      end loop;
      if Count = N then
         return Line (Start .. Line'Last);
      end if;
      raise Constraint_Error with "missing field";
   end Field;

   --  Det_End (B, B'First, Max_Depth) against the reference's end (-1, or
   --  the 0-based end), and Accept_Whole against its verdict, separately.
   procedure Compare (Line : Natural; B : Bytes; Ref_End : Integer;
                      Ref_Whole : Boolean; Where : String) is
   begin
      if B'Length > 0 then
         begin
            if Ref_End < 0 then
               pragma Assert (Det_End (B, B'First, Max_Depth) = 0);
            else
               pragma Assert
                 (Det_End (B, B'First, Max_Depth) = B'First + Ref_End);
            end if;
            Pass;
         exception
            when Ada.Assertions.Assertion_Error =>
               Fail ("row" & Line'Image & " " & Where & ": end differs from"
                     & " the reference's" & Ref_End'Image & " (bytes "
                     & To_Hex (B) & ")");
            when E : others =>
               Fail ("row" & Line'Image & " " & Where & ": end: exception "
                     & Ada.Exceptions.Exception_Name (E));
         end;
      end if;
      begin
         pragma Assert (Accept_Whole (B) = Ref_Whole);
         Pass;
      exception
         when Ada.Assertions.Assertion_Error =>
            Fail ("row" & Line'Image & " " & Where & ": Accept_Whole differs"
                  & " from the reference's " & Ref_Whole'Image & " (bytes "
                  & To_Hex (B) & ")");
         when E : others =>
            Fail ("row" & Line'Image & " " & Where & ": Accept_Whole:"
                  & " exception " & Ada.Exceptions.Exception_Name (E));
      end;
   end Compare;

   procedure Corpus (Path : String; Timings : String := "") is
      F           : File_Type;
      T           : File_Type;
      Line_No     : Natural := 0;
      Rows_Run    : Natural := 0;
      Rows_Top    : Natural := 0;
      Rows_Lemmas : Natural := 0;
      Deferred    : Natural := 0;
      Unmodelled  : Natural := 0;
      Accepted    : Natural := 0;
      Refused     : Natural := 0;
      Empty       : Natural := 0;
      Before      : constant Natural := Failed;
      use Ada.Real_Time;
   begin
      if not Enabled then
         return;
      end if;
      Open (F, In_File, Path);
      if Timings /= "" then
         Create (T, Out_File, Timings);
      end if;
      while not End_Of_File (F) loop
         declare
            Line      : constant String := Get_Line (F);
            B         : constant Bytes := Hex (Field (Line, 1));
            Ref_End   : constant Integer := Integer'Value (Field (Line, 2));
            Ref_Whole : constant Boolean := Field (Line, 3) = "1";
            Class     : constant String := Field (Line, 4);
            Count     : constant String := Field (Line, 5);
         begin
            Line_No := Line_No + 1;
            if Class = "run" then
               Rows_Run := Rows_Run + 1;
               if B'Length = 0 then
                  Empty := Empty + 1;
               elsif Ref_End < 0 then
                  Refused := Refused + 1;
               else
                  Accepted := Accepted + 1;
               end if;
               declare
                  Start : constant Time := Clock;
               begin
                  Compare (Line_No, B, Ref_End, Ref_Whole, "at index 1");
                  if Timings /= "" then
                     Put_Line (T, Count & Duration'Image
                                 (To_Duration (Clock - Start)));
                  end if;
               end;
               if Count'Length <= 7 and then Natural'Value (Count) <= Top_Limit
               then
                  Rows_Top := Rows_Top + 1;
                  Compare (Line_No, At_Top (B), Ref_End, Ref_Whole,
                           "at the top of Index");
               end if;
               if Ref_End > 0 and then Count'Length <= 7
                 and then Natural'Value (Count) <= Lemma_Limit
               then
                  Rows_Lemmas := Rows_Lemmas + 1;
                  Ghost_Vectors.Lemmas
                    ("row" & Line_No'Image, B (1 .. Ref_End));
               end if;
            elsif Class = "deferred" then
               Deferred := Deferred + 1;
            elsif Class = "unmodelled" then
               --  The cost model and the reference disagree on this row's
               --  end: the classification is wrong, so the run fails.
               Unmodelled := Unmodelled + 1;
               Fail ("row" & Line_No'Image & ": unmodelled: the cost model's"
                     & " end differs from the reference's"
                     & Ref_End'Image & " (bytes " & To_Hex (B) & ")");
            else
               Fail ("row" & Line_No'Image & ": unknown class " & Class);
            end if;
         end;
      end loop;
      Close (F);
      if Timings /= "" then
         Close (T);
      end if;
      Put_Line ("corpus: rows" & Line_No'Image & ", compared" & Rows_Run'Image
                & " (accepted" & Accepted'Image & ", refused" & Refused'Image
                & ", empty" & Empty'Image & "), also at the top of Index"
                & Rows_Top'Image & ", lemmas run on" & Rows_Lemmas'Image
                & ", deferred" & Deferred'Image & ", unmodelled"
                & Unmodelled'Image & ", failures"
                & Natural'Image (Failed - Before));
   end Corpus;

   procedure Heads (Path : String) is
      F          : File_Type;
      Line_No    : Natural := 0;
      Compared   : Natural := 0;
      Not_Heads  : Natural := 0;
      Major_6_7  : Natural := 0;
      Empty      : Natural := 0;
      Before     : constant Natural := Failed;
   begin
      Open (F, In_File, Path);
      while not End_Of_File (F) loop
         declare
            Line : constant String := Get_Line (F);
            B    : constant Bytes := Hex (Field (Line, 1));
            None : constant Boolean := Field (Line, 2) = "NONE";
            Name : constant String :=
              "head row" & Natural'Image (Line_No + 1) & " (" & To_Hex (B)
              & ")";
         begin
            Line_No := Line_No + 1;
            if B'Length = 0 then
               Empty := Empty + 1;
               if not None then
                  Fail (Name & ": the reference has a head in no bytes");
               end if;
            elsif Major_Of (B (1)) >= 6 then
               --  The reference reads heads of major types 0 to 5 only.
               Major_6_7 := Major_6_7 + 1;
               if not None then
                  Fail (Name & ": the reference has a major 6 or 7 head");
               end if;
            elsif None then
               Not_Heads := Not_Heads + 1;
               if Head_OK (B, 1) then
                  Fail (Name & ": Head_OK, the reference has no head");
               else
                  Pass;
               end if;
            else
               Compared := Compared + 1;
               declare
                  M : constant Interfaces.Unsigned_64 :=
                    Decimal (Field (Line, 2));
                  A : constant Interfaces.Unsigned_64 :=
                    Decimal (Field (Line, 3));
                  L : constant Interfaces.Unsigned_64 :=
                    Decimal (Field (Line, 4));
               begin
                  if not Head_OK (B, 1) then
                     Fail (Name & ": not Head_OK, the reference has a head");
                  elsif Interfaces.Unsigned_64 (Major_Of (B (1))) /= M then
                     Fail (Name & ": major type");
                  elsif Interfaces.Unsigned_64 (Head_Len (B (1))) /= L then
                     Fail (Name & ": length");
                  elsif Arg (B, 1) /= A then
                     Fail (Name & ": argument");
                  elsif not Shortest (B, 1) then
                     Fail (Name & ": not Shortest");
                  else
                     Pass;
                  end if;
               end;
            end if;
         end;
      end loop;
      Close (F);
      Put_Line ("heads: rows" & Line_No'Image & ", heads compared"
                & Compared'Image & ", refused by both" & Not_Heads'Image
                & ", major 6 or 7 (no reference head)" & Major_6_7'Image
                & ", empty" & Empty'Image & ", failures"
                & Natural'Image (Failed - Before));
   end Heads;

   procedure Exhaustive (Path : String) is
      type Buffer_Access is access Stream_Element_Array;
      procedure Free is new Ada.Unchecked_Deallocation
        (Stream_Element_Array, Buffer_Access);
      Total   : constant Stream_Element_Offset :=
        1 + 256 + 65_536 + 16_777_216;
      Data    : Buffer_Access := new Stream_Element_Array (1 .. Total);
      F       : Ada.Streams.Stream_IO.File_Type;
      Last    : Stream_Element_Offset;
      Next    : Stream_Element_Offset := 1;
      Rows    : Natural := 0;
      Accepts : Natural := 0;
      Before  : constant Natural := Failed;
   begin
      if not Enabled then
         Free (Data);
         return;
      end if;
      Ada.Streams.Stream_IO.Open (F, Ada.Streams.Stream_IO.In_File, Path);
      Ada.Streams.Stream_IO.Read (F, Data.all, Last);
      Ada.Streams.Stream_IO.Close (F);
      if Last /= Total then
         Fail ("exhaustive: the verdict file has" & Last'Image
               & " bytes, not" & Total'Image);
         Free (Data);
         return;
      end if;
      for Len in 0 .. 3 loop
         declare
            B : Bytes (1 .. Len);
         begin
            for V in 0 .. 256**Len - 1 loop
               for K in 1 .. Len loop
                  B (K) := Byte ((V / 256**(Len - K)) mod 256);
               end loop;
               declare
                  Verdict   : constant Natural := Natural (Data (Next));
                  Ref_End   : constant Integer := Verdict mod 128 - 1;
                  Ref_Whole : constant Boolean := Verdict >= 128;
               begin
                  Next := Next + 1;
                  Rows := Rows + 1;
                  if Ref_Whole then
                     Accepts := Accepts + 1;
                  end if;
                  Compare (Rows, B, Ref_End, Ref_Whole, "exhaustive");
               end;
            end loop;
         end;
      end loop;
      Free (Data);
      Put_Line ("exhaustive: inputs of 0 to 3 bytes" & Rows'Image
                & ", accepted whole by the reference" & Accepts'Image
                & ", failures" & Natural'Image (Failed - Before));
   end Exhaustive;

begin
   pragma Assert (Enable);
end Differential;
