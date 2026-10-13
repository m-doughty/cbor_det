--  cbor_det tests: counters, byte strings and the checks the runner makes
--  of its own build.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause

with Ada.Assertions;
with Ada.Text_IO;

with Cbor_Det.Proof.Det;

package body Support is

   use type Interfaces.Unsigned_64;

   Pass_Count : Natural := 0;
   --  Where Library_Has_Contracts puts a result it does not use.
   Sink : Natural := 0 with Volatile;
   Fail_Count : Natural := 0;

   procedure Pass is
   begin
      Pass_Count := Pass_Count + 1;
   end Pass;

   procedure Fail (What : String) is
   begin
      Fail_Count := Fail_Count + 1;
      Ada.Text_IO.Put_Line ("FAIL: " & What);
   end Fail;

   function Passed return Natural is (Pass_Count);
   function Failed return Natural is (Fail_Count);

   function Nibble (C : Character) return Byte is
   begin
      case C is
         when '0' .. '9' => return Character'Pos (C) - Character'Pos ('0');
         when 'a' .. 'f' =>
            return Character'Pos (C) - Character'Pos ('a') + 10;
         when 'A' .. 'F' =>
            return Character'Pos (C) - Character'Pos ('A') + 10;
         when others => raise Constraint_Error with "not a hex digit";
      end case;
   end Nibble;

   function Hex (Text : String) return Bytes is
      R : Bytes (1 .. Text'Length / 2);
   begin
      if Text'Length mod 2 /= 0 then
         raise Constraint_Error with "odd hex length";
      end if;
      for I in R'Range loop
         R (I) := Nibble (Text (Text'First + 2 * (I - 1))) * 16
                  + Nibble (Text (Text'First + 2 * (I - 1) + 1));
      end loop;
      return R;
   end Hex;

   function Rebase (B : Bytes; First : Integer) return Bytes is
   begin
      if B'Length = 0 then
         declare
            R : constant Bytes (First .. First - 1) := [];
         begin
            return R;
         end;
      end if;
      declare
         R : Bytes (First .. First + B'Length - 1);
      begin
         R := B;
         return R;
      end;
   end Rebase;

   function To_Hex (B : Bytes) return String is
      Digits_Of : constant String := "0123456789abcdef";
      R : String (1 .. 2 * B'Length);
      J : Positive := 1;
   begin
      for X of B loop
         R (J) := Digits_Of (Natural (X / 16) + 1);
         R (J + 1) := Digits_Of (Natural (X mod 16) + 1);
         J := J + 2;
      end loop;
      return R;
   end To_Hex;

   function Decimal (Text : String) return Interfaces.Unsigned_64 is
      R : Interfaces.Unsigned_64 := 0;
   begin
      if Text'Length = 0 or else Text'Length > 20 then
         raise Constraint_Error with "bad decimal";
      end if;
      for C of Text loop
         if C not in '0' .. '9' then
            raise Constraint_Error with "bad decimal";
         end if;
         declare
            D : constant Interfaces.Unsigned_64 :=
              Character'Pos (C) - Character'Pos ('0');
         begin
            if R > (Interfaces.Unsigned_64'Last - D) / 10 then
               raise Constraint_Error with "decimal overflow";
            end if;
            R := R * 10 + D;
         end;
      end loop;
      return R;
   end Decimal;

   function At_Top (B : Bytes) return Bytes is
     (Rebase (B, Index'Last - B'Length + 1));

   function Library_Has_Contracts return Boolean is
      --  Arg_Nat's precondition needs an argument that fits a Natural;
      --  this one is 2**64 - 1.
      B : constant Bytes := Hex ("1bffffffffffffffff");
   begin
      Sink := Cbor_Det.Proof.Det.Arg_Nat (B, 1);
      return False;
   exception
      when Ada.Assertions.Assertion_Error =>
         return True;
      when Constraint_Error =>
         return False;
   end Library_Has_Contracts;

end Support;
