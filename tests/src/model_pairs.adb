--  cbor_det tests: the value relation Same against the denotation oracle.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause

with Ada.Assertions;
with Ada.Exceptions;
with Ada.Text_IO;           use Ada.Text_IO;

with Cbor_Det;               use Cbor_Det;
with Cbor_Det.Proof.Det;     use Cbor_Det.Proof.Det;
with Cbor_Det.Proof.Model;   use Cbor_Det.Proof.Model;
with Cbor_Det.Proof.Unique;  use Cbor_Det.Proof.Unique;

with Support; use Support;

package body Model_Pairs is

   Enabled : Boolean := False;

   function Enable return Boolean is
   begin
      Enabled := True;
      return True;
   end Enable;

   function Ran return Boolean is (Enabled);

   --  What evaluating a ghost Boolean gave: a ghost value can be read
   --  only inside an assertion, so it is asked both ways round; if both
   --  raise, a contract inside the evaluation failed.
   type Verdict is (Yes, No, Error);

   function Accepted (B : Bytes) return Verdict is
      Is_Yes, Is_No : Boolean := True;
   begin
      begin
         pragma Assert (Accept_Whole (B));
      exception
         when Ada.Assertions.Assertion_Error => Is_Yes := False;
      end;
      begin
         pragma Assert (not Accept_Whole (B));
      exception
         when Ada.Assertions.Assertion_Error => Is_No := False;
      end;
      return (if Is_Yes and then not Is_No then Yes
              elsif Is_No and then not Is_Yes then No
              else Error);
   end Accepted;

   --  Same on two inputs accepted whole, at Max_Depth.
   function Same_Of (B1, B2 : Bytes) return Verdict is
      Is_Yes, Is_No : Boolean := True;
   begin
      begin
         pragma Assert (Same (B1, B1'First, B2, B2'First, Max_Depth));
      exception
         when Ada.Assertions.Assertion_Error => Is_Yes := False;
      end;
      begin
         pragma Assert (not Same (B1, B1'First, B2, B2'First, Max_Depth));
      exception
         when Ada.Assertions.Assertion_Error => Is_No := False;
      end;
      return (if Is_Yes and then not Is_No then Yes
              elsif Is_No and then not Is_Yes then No
              else Error);
   end Same_Of;

   --  A lemma on a pair: a failed contract is a failure of the row.
   type Lemma_Kind is (Iff, CU, Converse);

   procedure Run_Lemma (Row : Natural; Kind : Lemma_Kind; Where : String;
                        B1, B2 : Bytes; Ok : in out Boolean) is
   begin
      case Kind is
         when Iff      => Lemma_Same_Iff_Bytes_Whole (B1, B2);
         when CU       => Lemma_CU_Whole (B1, B2);
         when Converse => Lemma_Same_Of_Bytes_Whole (B1, B2);
      end case;
   exception
      when Ada.Assertions.Assertion_Error =>
         Ok := False;
         Fail ("row" & Row'Image & " " & Where & ": a contract of "
               & Kind'Image & " failed (bytes " & To_Hex (B1) & " and "
               & To_Hex (B2) & ")");
      when E : others =>
         Ok := False;
         Fail ("row" & Row'Image & " " & Where & ": " & Kind'Image
               & ": exception " & Ada.Exceptions.Exception_Name (E));
   end Run_Lemma;

   procedure Same_Pairs (Path : String; Rows : Integer; Same_Rows : Integer)
   is
      F         : File_Type;
      Row       : Natural := 0;
      Accepts   : Natural := 0;
      S_Rows    : Natural := 0;
      D_Rows    : Natural := 0;
      Agree     : Natural := 0;
      Lemma_S   : Natural := 0;
      Malformed : Natural := 0;
      Before    : constant Natural := Failed;
   begin
      if not Enabled then
         Fail ("same: nothing was compared: this mode needs the library's"
               & " contracts (the contracts cell)");
         return;
      end if;
      Open (F, In_File, Path);
      while not End_Of_File (F) loop
         declare
            Line : constant String := Get_Line (F);
            S1, S2 : Natural := 0;
         begin
            if Line'Length > 0 and then Line (Line'First) = '#' then
               goto Next;
            end if;
            Row := Row + 1;
            for I in Line'Range loop
               if Line (I) = ' ' then
                  if S1 = 0 then
                     S1 := I;
                  elsif S2 = 0 then
                     S2 := I;
                  else
                     S2 := 0;
                     exit;
                  end if;
               end if;
            end loop;
            if S1 = 0 or else S2 = 0 or else S2 /= Line'Last - 1
              or else Line (Line'Last) not in 'S' | 'D'
              or else S1 = Line'First or else S2 = S1 + 1
            then
               --  The line is not printed: it is the file's text.
               Malformed := Malformed + 1;
               Fail ("row" & Row'Image & ": malformed");
               goto Next;
            end if;
            declare
               B1 : constant Bytes := Hex (Line (Line'First .. S1 - 1));
               B2 : constant Bytes := Hex (Line (S1 + 1 .. S2 - 1));
               R2 : constant Bytes := Rebase (B2, Rebased_First);
               Label : constant Verdict :=
                 (if Line (Line'Last) = 'S' then Yes else No);
               Ok : Boolean := True;
            begin
               if Label = Yes then
                  S_Rows := S_Rows + 1;
               else
                  D_Rows := D_Rows + 1;
               end if;
               if Accepted (B1) /= Yes or else Accepted (B2) /= Yes
                 or else Accepted (R2) /= Yes
               then
                  Fail ("row" & Row'Image & ": an input is not accepted"
                        & " whole (bytes " & To_Hex (B1) & " and "
                        & To_Hex (B2) & ")");
                  goto Next;
               end if;
               Accepts := Accepts + 1;
               declare
                  Got   : constant Verdict := Same_Of (B1, B2);
                  Got_R : constant Verdict := Same_Of (B1, R2);
               begin
                  if Got /= Label or else Got_R /= Label then
                     Ok := False;
                     Fail ("row" & Row'Image & ": Same is "
                           & Got'Image & " (rebased " & Got_R'Image
                           & "), the oracle says "
                           & (if Label = Yes then "S" else "D")
                           & " (bytes " & To_Hex (B1) & " and "
                           & To_Hex (B2) & ")");
                  end if;
               end;
               --  The lemmas, on the rebased pair: on a D row the two-way
               --  lemma (Same False, the bytes differ); on an S row the
               --  two directions, each once (Lemma_CU_Whole executes its
               --  whole proof, so it is the costly one).
               if Label = Yes then
                  Lemma_S := Lemma_S + 1;
                  Run_Lemma (Row, CU, "rebased", B1, R2, Ok);
                  Run_Lemma (Row, Converse, "rebased", R2, B1, Ok);
               else
                  Run_Lemma (Row, Iff, "rebased", B1, R2, Ok);
               end if;
               if Ok then
                  Agree := Agree + 1;
                  Pass;
               end if;
            end;
         exception
            when E : Constraint_Error =>
               Malformed := Malformed + 1;
               Fail ("row" & Row'Image & ": malformed: "
                     & Ada.Exceptions.Exception_Name (E));
         end;
         <<Next>>
      end loop;
      Close (F);
      if Row = 0 then
         Fail ("same: nothing was compared (no data line)");
      end if;
      if Rows >= 0 and then Row /= Rows then
         Fail ("same: rows" & Row'Image & ", expected" & Rows'Image
               & " rows");
      end if;
      if Same_Rows >= 0 and then S_Rows /= Same_Rows then
         Fail ("same: S rows" & S_Rows'Image & ", expected"
               & Same_Rows'Image);
      end if;
      Put_Line ("same: rows" & Row'Image & ", accepted" & Accepts'Image
                & ", S" & S_Rows'Image & ", D" & D_Rows'Image
                & ", agreeing" & Agree'Image & ", lemmas on S rows"
                & Lemma_S'Image & ", malformed" & Malformed'Image
                & ", failures" & Natural'Image (Failed - Before));
   end Same_Pairs;

begin
   pragma Assert (Enable);
end Model_Pairs;
