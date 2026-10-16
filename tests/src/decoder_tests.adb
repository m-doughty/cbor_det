--  cbor_det tests: the decoder against the two references.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause

with Ada.Characters.Handling;
with Ada.Exceptions;
with Ada.Streams;           use Ada.Streams;
with Ada.Streams.Stream_IO;
with Ada.Text_IO;           use Ada.Text_IO;
with Ada.Unchecked_Deallocation;

with Cbor_Det;         use Cbor_Det;
with Cbor_Det.Decoder; use Cbor_Det.Decoder;

with Support; use Support;

package body Decoder_Tests is

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

   --  The bytes, shortened for a message.
   function Shown (B : Bytes) return String is
     (if B'Length <= 40 then To_Hex (B)
      else To_Hex (B (B'First .. B'First + 39)) & "...("
           & Natural'Image (B'Length) & " bytes)");

   -------------
   -- Verdict --
   -------------

   --  Opens Path for reading; on failure reports the role of the file
   --  and the name of the exception only (never the path, which may be
   --  absolute), and returns False.
   function Opened (F : in out File_Type; Path : String; Role : String)
     return Boolean is
   begin
      Open (F, In_File, Path);
      return True;
   exception
      when E : others =>
         Fail (Role & ": the input file cannot be read ("
               & Ada.Exceptions.Exception_Name (E) & ")");
         return False;
   end Opened;

   procedure Verdict
     (Path : String; Contracts : Boolean; Expected_Rows : Integer := -1) is
      F          : File_Type;
      Line_No    : Natural := 0;
      Run        : Natural := 0;
      Ok_Rows    : Natural := 0;
      Deferred   : Natural := 0;
      Unmodelled : Natural := 0;
      Before     : constant Natural := Failed;
   begin
      if not Opened (F, Path, "verdict") then
         return;
      end if;
      while not End_Of_File (F) loop
         declare
            Line   : constant String := Get_Line (F);
            B      : constant Bytes := Hex (Field (Line, 1));
            Whole  : constant Boolean := Field (Line, 3) = "1";
            Class  : constant String := Field (Line, 4);
            Result : Cbor_Det.Status;
            Where  : Integer;
         begin
            Line_No := Line_No + 1;
            if Class = "unmodelled" then
               Unmodelled := Unmodelled + 1;
               Fail ("verdict row" & Line_No'Image & ": unmodelled");
            elsif Class = "deferred" and then Contracts then
               Deferred := Deferred + 1;
            else
               Run := Run + 1;
               Check (B, Result, Where);
               if Result = Ok then
                  Ok_Rows := Ok_Rows + 1;
               end if;
               if (Result = Ok) = Whole
                 and then (Result /= Ok or else Where = B'Last + 1)
               then
                  Pass;
               else
                  Fail ("verdict row" & Line_No'Image & ": Check gives "
                        & Result'Image & " at" & Where'Image
                        & ", the reference's whole-input verdict is "
                        & Whole'Image & " (bytes " & Shown (B) & ")");
               end if;
            end if;
         exception
            when E : others =>
               Fail ("verdict row" & Line_No'Image & ": exception "
                     & Ada.Exceptions.Exception_Name (E));
         end;
      end loop;
      Close (F);
      if Run = 0 then
         Fail ("verdict: nothing was compared (no row run)");
      end if;
      if Expected_Rows >= 0 and then Line_No /= Expected_Rows then
         Fail ("verdict: the file has" & Line_No'Image & " rows, expected"
               & Expected_Rows'Image & " rows");
      end if;
      Put_Line ("verdict: rows" & Line_No'Image & ", run" & Run'Image
                & " (Ok" & Ok_Rows'Image & "), not run under contracts"
                & " (deferred by the cost model)" & Deferred'Image
                & ", unmodelled" & Unmodelled'Image & ", failures"
                & Natural'Image (Failed - Before));
   end Verdict;

   ------------------------
   -- Verdict_Exhaustive --
   ------------------------

   procedure Verdict_Exhaustive (Path : String) is
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
      Oks     : Natural := 0;
      Wrong   : Natural := 0;
      Before  : constant Natural := Failed;
   begin
      begin
         Ada.Streams.Stream_IO.Open (F, Ada.Streams.Stream_IO.In_File, Path);
         Ada.Streams.Stream_IO.Read (F, Data.all, Last);
         if Last = Total and then not Ada.Streams.Stream_IO.End_Of_File (F)
         then
            Last := Total + 1;   --  more bytes than the inputs
         end if;
         Ada.Streams.Stream_IO.Close (F);
      exception
         when E : others =>
            Fail ("verdict-exhaustive: the input file cannot be read ("
                  & Ada.Exceptions.Exception_Name (E) & ")");
            Free (Data);
            return;
      end;
      if Last > Total then
         Fail ("verdict-exhaustive: the verdict file has more bytes than"
               & Total'Image);
         Free (Data);
         return;
      elsif Last /= Total then
         Fail ("verdict-exhaustive: the verdict file has" & Last'Image
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
                  Whole  : constant Boolean := Natural (Data (Next)) >= 128;
                  Result : Cbor_Det.Status;
                  Where  : Integer;
               begin
                  Next := Next + 1;
                  Rows := Rows + 1;
                  Check (B, Result, Where);
                  if Result = Ok then
                     Oks := Oks + 1;
                  end if;
                  if (Result = Ok) /= Whole then
                     Wrong := Wrong + 1;
                     if Wrong <= 20 then
                        Fail ("verdict-exhaustive: " & To_Hex (B)
                              & ": Check gives " & Result'Image
                              & ", the reference " & Whole'Image);
                     end if;
                  end if;
               end;
            end loop;
         end;
      end loop;
      Free (Data);
      if Wrong > 20 then
         for I in 21 .. Wrong loop
            Fail ("verdict-exhaustive: (not printed)");
         end loop;
      end if;
      if Wrong = 0 then
         Pass;
      end if;
      Put_Line ("verdict-exhaustive: inputs of 0 to 3 bytes" & Rows'Image
                & ", Ok" & Oks'Image & ", disagreements" & Wrong'Image
                & ", failures" & Natural'Image (Failed - Before));
   end Verdict_Exhaustive;

   ------------
   -- Status --
   ------------

   procedure Status (Path : String; Expected_Rows : Integer := -1) is
      type Count_Array is array (Cbor_Det.Status) of Natural;
      Agree     : Count_Array := [others => 0];
      Disagree  : Count_Array := [others => 0];
      F         : File_Type;
      Line_No   : Natural := 0;
      Printed   : Natural := 0;
      Before    : constant Natural := Failed;

      --  Check on B against the oracle's status and 0-based position.
      procedure One (B : Bytes; Want : Cbor_Det.Status; Offset : Integer;
                     Placement : String) is
         Result : Cbor_Det.Status;
         Where  : Integer;
      begin
         Check (B, Result, Where);
         if Result = Want and then Where = B'First + Offset then
            Agree (Want) := Agree (Want) + 1;
            Pass;
         else
            Disagree (Want) := Disagree (Want) + 1;
            Printed := Printed + 1;
            Fail ((if Printed <= 30
                   then "status row" & Line_No'Image & " " & Placement
                        & ": Check gives " & Result'Image & " at offset"
                        & Integer'Image (Where - B'First) & ", the oracle "
                        & Want'Image & " at offset" & Offset'Image
                        & " (bytes " & Shown (B) & ")"
                   else "status: (not printed)"));
         end if;
      exception
         when E : others =>
            Disagree (Want) := Disagree (Want) + 1;
            Fail ("status row" & Line_No'Image & " " & Placement
                  & ": exception " & Ada.Exceptions.Exception_Name (E));
      end One;

   begin
      if not Opened (F, Path, "status") then
         return;
      end if;
      while not End_Of_File (F) loop
         declare
            Line   : constant String := Get_Line (F);
            B      : constant Bytes := Hex (Field (Line, 1));
            Name   : constant String :=
              Ada.Characters.Handling.To_Upper (Field (Line, 2));
            Want   : constant Cbor_Det.Status :=
              Cbor_Det.Status'Value (Name);
            Offset : constant Integer := Integer'Value (Field (Line, 3));
         begin
            Line_No := Line_No + 1;
            One (B, Want, Offset, "at index 1");
            One (Rebase (B, 1000), Want, Offset, "at index 1000");
            One (At_Top (B), Want, Offset, "ending at Index'Last");
            if B'Length = 0 then
               One (Rebase (B, -1), Want, Offset, "null at -1");
               One (Rebase (B, 0), Want, Offset, "null at 0");
               One (Rebase (B, Index'Last), Want, Offset,
                    "null at Index'Last");
               One (Rebase (B, Index'Last + 1), Want, Offset,
                    "null at Index'Last + 1");
               One (Rebase (B, Integer'Last), Want, Offset,
                    "null at Integer'Last");
               One (Rebase (B, Integer'First + 1), Want, Offset,
                    "null at Integer'First + 1");
            end if;
         exception
            when E : Constraint_Error =>
               Fail ("status row" & Line_No'Image & ": bad row ("
                     & Ada.Exceptions.Exception_Name (E) & ")");
         end;
      end loop;
      Close (F);
      if Line_No = 0 then
         Fail ("status: nothing was compared (no row)");
      end if;
      if Expected_Rows >= 0 and then Line_No /= Expected_Rows then
         Fail ("status: the file has" & Line_No'Image & " rows, expected"
               & Expected_Rows'Image & " rows");
      end if;
      Put_Line ("status: rows" & Line_No'Image & ", failures"
                & Natural'Image (Failed - Before));
      for S in Cbor_Det.Status loop
         Put_Line ("status " & S'Image & ": agree" & Agree (S)'Image
                   & ", disagree" & Disagree (S)'Image);
      end loop;
   end Status;

end Decoder_Tests;
