--  cbor_det tests: a first run of the decoder (smoke vectors).
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause

with Ada.Assertions;
with Ada.Exceptions;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;
with Ada.Text_IO;

with Cbor_Det;                  use Cbor_Det;
with Cbor_Det.Decoder;          use Cbor_Det.Decoder;
with Cbor_Det.Decoder.Counters;

with Appendix_A_Table; use Appendix_A_Table;
with Support;          use Support;

package body Decoder_Vectors is

   use type Cbor_Det.U64;

   Enabled : Boolean := False;

   function Enable return Boolean is
   begin
      Enabled := True;
      return True;
   end Enable;

   function Ran return Boolean is (Enabled);

   --  Check on Data: Result and Where (as an offset from Data'First)
   --  as expected, and Result = Ok exactly when Accepts.
   procedure One
     (Name : String; Data : Bytes; Want : Status; Want_Offset : Integer)
   is
      Result : Status;
      Where  : Integer;
   begin
      Check (Data, Result, Where);
      if Result = Want and then Where = Data'First + Want_Offset then
         Pass;
      else
         Fail ("decoder " & Name & " (" & To_Hex (Data) & "): got "
               & Result'Image & " at offset"
               & Integer'Image (Where - Data'First) & ", expected "
               & Want'Image & " at offset" & Want_Offset'Image);
      end if;
      begin
         pragma Assert ((Result = Ok) = Accepts (Data));
      exception
         when Ada.Assertions.Assertion_Error =>
            Fail ("decoder " & Name & ": Result disagrees with Accepts");
      end;
   exception
      when E : others =>
         Fail ("decoder " & Name & ": exception "
               & Ada.Exceptions.Exception_Name (E));
   end One;

   --  The same, at index 1, at index 1000 and ending at Index'Last.
   procedure Three
     (Name : String; Hex_Text : String; Want : Status; Want_Offset : Integer)
   is
      B : constant Bytes := Hex (Hex_Text);
   begin
      One (Name, B, Want, Want_Offset);
      One (Name & " at 1000", Rebase (B, 1000), Want, Want_Offset);
      One (Name & " at the top", At_Top (B), Want, Want_Offset);
   end Three;

   function Deep (Last : String) return String is
     ("81818181818181818181818181818181" & Last);

   ---------------------------------------------------------------------
   --  RFC 8949 Appendix A: every example, its verdict, at three places.
   ---------------------------------------------------------------------

   procedure Run_Appendix_A is
      Oks : Natural := 0;
   begin
      for X of Appendix_A loop
         declare
            B : constant Bytes := Hex (To_String (X.Encoded));
            procedure At_Place (D : Bytes; Place : String) is
               Result : Status;
               Where  : Integer;
            begin
               Check (D, Result, Where);
               if (Result = Ok) = X.Accepted
                 and then (Result /= Ok or else Where = D'Last + 1)
               then
                  Pass;
               else
                  Fail ("decoder Appendix A " & To_String (X.Name) & " "
                        & Place & ": " & Result'Image);
               end if;
               if Result = Ok then
                  Oks := Oks + 1;
               end if;
            end At_Place;
         begin
            At_Place (B, "at 1");
            At_Place (Rebase (B, 1000), "at 1000");
            At_Place (At_Top (B), "at the top");
         end;
      end loop;
      if Appendix_A'Length /= 81 or else Oks /= 3 * 37 then
         Fail ("decoder Appendix A: 81 examples, 37 Ok, expected");
      end if;
      Ada.Text_IO.Put_Line ("decoder Appendix A: examples"
                            & Appendix_A'Length'Image & ", Ok at each of"
                            & " three places" & Natural'Image (Oks / 3));
   end Run_Appendix_A;

   ---------------------------------------------------------------------
   --  Operation counts, with the ghost counters, so in the contracts
   --  cell only.
   --
   --  The envelope tested, for an input of N bytes, comes from charging
   --  each operation to a byte of the input. The parse consumes each
   --  byte once. Each key's end is saved and siblings are never scanned
   --  again, so a key is compared only with the keys next to it in its
   --  map, and a byte inside a key nested in other keys is charged again
   --  at each enclosing map:
   --
   --    Bytes_Parsed = N for an accepted input, and Bytes_Parsed <= N
   --    for any input. The counter measures bytes consumed, not bytes
   --    read: each head's bytes and each string's payload are consumed
   --    once, and a payload is charged without its bytes being read
   --    (Check checks a string's length and skips its bytes);
   --
   --    Bytes_Compared <= Max_Depth * N. A key is compared only with the
   --    key before it in the same map, and that comparison examines at
   --    most as many byte pairs as the shorter key has bytes, so at most
   --    the current key's length. Each byte is then charged at most once
   --    per map in whose key it lies (as part of the current key), and a
   --    byte lies in the keys of at most Max_Depth maps, since at most
   --    Max_Depth containers are nested. (Charging a key's bytes twice
   --    per map, as the current key and as the previous one, gives the
   --    looser bound 2 * Max_Depth * N; the test checks the tighter one,
   --    and prints the measured ratio.)
   --
   --  The workloads are sized so that the ghost code this cell executes
   --  finishes: Check's postcondition (the unmemoised Det_End) and, inside
   --  the decoder, the lemma calls and loop invariants, which re-evaluate
   --  Members_End and Keys_Ascending at every member (quadratic in an
   --  array's width, cubic in a map's). Wider inputs are tested for
   --  their verdict and status in the plain cells (boundary.py).
   ---------------------------------------------------------------------

   function Uint (V : Natural) return String is
     (if V < 24 then To_Hex (Bytes'(1 => Byte (V)))
      elsif V < 256 then "18" & To_Hex (Bytes'(1 => Byte (V)))
      else "19" & To_Hex (Bytes'(1 => Byte (V / 256), 2 => Byte (V mod 256))));

   --  A head of major type M and count or length V (V < 65 536).
   function Head (M : Natural; V : Natural) return String is
     (if V < 24 then To_Hex (Bytes'(1 => Byte (M * 32 + V)))
      elsif V < 256
      then To_Hex (Bytes'(1 => Byte (M * 32 + 24), 2 => Byte (V)))
      else To_Hex (Bytes'(1 => Byte (M * 32 + 25), 2 => Byte (V / 256),
                          3 => Byte (V mod 256))));

   function Repeat (Text : String; N : Natural) return String is
      R : Unbounded_String;
   begin
      for I in 1 .. N loop
         Append (R, Text);
      end loop;
      return To_String (R);
   end Repeat;

   --  Prints one workload's counts and ratios; called from an assertion,
   --  so only where the counters exist. Returns True.
   function Note
     (Name : String; N : Natural;
      Parsed, Compared, Comparisons : Cbor_Det.U64) return Boolean
   is
      function Ratio (X : Cbor_Det.U64) return String is
        (Integer'Image (Integer (Float (X) / Float (N) * 1000.0)) & "/1000");
   begin
      Ada.Text_IO.Put_Line
        ("operation counts, " & Name & ": N =" & N'Image
         & ", bytes consumed (Bytes_Parsed) =" & Parsed'Image & " (" & Ratio (Parsed)
         & " N), Bytes_Compared =" & Compared'Image & " ("
         & Ratio (Compared) & " N), Key_Comparisons =" & Comparisons'Image);
      return True;
   end Note;

   procedure Count_One (Name : String; Text : String; Accepted : Boolean) is
      B      : constant Bytes := Hex (Text);
      N      : constant Cbor_Det.U64 := Cbor_Det.U64 (B'Length);
      Result : Status;
      Where  : Integer;
   begin
      Counters.Reset;
      Check (B, Result, Where);
      if (Result = Ok) = Accepted then
         Pass;
      else
         Fail ("operation counts " & Name & ": " & Result'Image);
      end if;
      begin
         pragma Assert
           (if Accepted then Counters.Bytes_Parsed = N
            else Counters.Bytes_Parsed <= N);
         pragma Assert (Counters.Bytes_Compared <= Max_Depth * N);
         Pass;
      exception
         when Ada.Assertions.Assertion_Error =>
            Fail ("operation counts " & Name & ": outside the envelope");
      end;
      pragma Assert
        (Note (Name, B'Length, Counters.Bytes_Parsed, Counters.Bytes_Compared,
               Counters.Key_Comparisons));
   end Count_One;

   procedure Run_Counts is
   begin
      --  Many keys with long common prefixes: 64 byte strings of 200
      --  bytes, the same but for their last byte.
      declare
         T : Unbounded_String := To_Unbounded_String (Head (5, 64));
      begin
         for K in 0 .. 63 loop
            Append (T, Head (2, 200) & Repeat ("61", 199)
                       & To_Hex (Bytes'(1 => Byte (K))) & "00");
         end loop;
         Count_One ("64 keys of 200 bytes, common prefix 199",
                    To_String (T), True);
      end;
      --  Deeply nested container keys: a map of 64 keys, each 15 arrays
      --  nested (so 16 deep with the map), the same but for the integer
      --  at the bottom.
      declare
         T : Unbounded_String := To_Unbounded_String (Head (5, 64));
      begin
         for K in 0 .. 63 loop
            Append (T, Repeat ("81", 15) & Uint (K) & "00");
         end loop;
         Count_One ("64 keys of 15 nested arrays", To_String (T), True);
      end;
      --  Keys nested in keys: at each of 6 levels a map of two pairs
      --  whose two keys are the next level's maps, the second one greater
      --  only in its last pair's value, so each comparison runs to the
      --  last byte and the inner bytes are compared at every level.
      declare
         function Level (D : Natural; Last : String) return String is
           (if D = 0 then Last
            else "a2" & Level (D - 1, "00") & "00"
                 & Level (D - 1, "01") & Last);
      begin
         Count_One ("keys nested in keys, 6 levels",
                    Level (6, "00"), True);
      end;
      --  A wide map: 256 integer keys.
      declare
         T : Unbounded_String := To_Unbounded_String (Head (5, 256));
      begin
         for K in 0 .. 255 loop
            Append (T, Uint (K) & "f6");
         end loop;
         Count_One ("a map of 256 pairs", To_String (T), True);
      end;
      --  A wide array: 2 000 members.
      Count_One ("an array of 2000 members",
                 Head (4, 2_000) & Repeat ("00", 2_000), True);
      --  Sixteen nested arrays, and seventeen.
      Count_One ("16 nested arrays", Deep ("00"), True);
      Count_One ("17 nested arrays", Deep ("8100"), False);
      --  A refusal half way: the same long keys, the last one out of
      --  order.
      declare
         T : Unbounded_String := To_Unbounded_String (Head (5, 4));
      begin
         for K in reverse 0 .. 3 loop
            Append (T, Head (2, 200) & Repeat ("61", 199)
                       & To_Hex (Bytes'(1 => Byte (K))) & "00");
         end loop;
         Count_One ("4 long keys, descending", To_String (T), False);
      end;
   end Run_Counts;

   procedure Run is
   begin
      --  Accepted.
      Three ("unsigned 0", "00", Ok, 1);
      Three ("map of two pairs", "a201000200", Ok, 5);
      Three ("sixteen nested arrays", Deep ("00"), Ok, 17);
      Three ("empty string, text, array, map; true", "85406080a0f5", Ok, 6);
      --  Refused: the precedence table's examples.
      Three ("d8", "d8", Truncated, 0);
      Three ("dc", "dc", Reserved_Info, 0);
      Three ("df", "df", Indefinite_Length, 0);
      Three ("ff", "ff", Indefinite_Length, 0);
      Three ("d8 01", "d801", Unsupported_Type, 0);
      Three ("f8 14", "f814", Unsupported_Simple, 0);
      Three ("59 00 01", "590001", Non_Shortest, 0);
      Three ("98 00 at 17", Deep ("9800"), Non_Shortest, 16);
      Three ("81 at 17", Deep ("81"), Truncated, 16);
      Three ("80 at 17", Deep ("80"), Too_Deep, 16);
      Three ("82 f8 14 1f", "82f8141f", Unsupported_Simple, 1);
      Three ("82 01", "8201", Truncated, 0);
      Three ("81 42 00", "814200", Truncated, 1);
      Three ("a2 01 00 01 18", "a201000118", Duplicate_Key, 3);
      Three ("a2 02 01 01 18 05", "a20201011805", Unsorted_Key, 3);
      Three ("a2 01 00 81 c0 00", "a2010081c000", Unsupported_Type, 4);
      --  Members owed at the end of the buffer: Truncated at the head of
      --  the innermost container that still owes one; a map's count
      --  against half the bytes left, at its head.
      Three ("82 81 00", "828100", Truncated, 0);
      Three ("82 82 00 00", "82820000", Truncated, 0);
      Three ("a1 81 00", "a18100", Truncated, 0);
      Three ("a2 00 81 81 00", "a200818100", Truncated, 0);
      Three ("a1 00", "a100", Truncated, 0);
      Three ("00 c0", "00c0", Trailing_Bytes, 1);
      Three ("01 ff", "01ff", Trailing_Bytes, 1);
      --  Empty input, with any bounds.
      One ("empty at 1", Rebase (Hex (""), 1), Truncated, 0);
      One ("empty at -1", Rebase (Hex (""), -1), Truncated, 0);
      One ("empty at Integer'Last", Rebase (Hex (""), Integer'Last),
           Truncated, 0);
      One ("empty at Integer'First + 1", Rebase (Hex (""), Integer'First + 1),
           Truncated, 0);

      Run_Appendix_A;
      Run_Counts;

      --  The operation counters (contracts cell only): a map of three
      --  keys makes two key comparisons.
      Counters.Reset;
      One ("counted map", Hex ("a3010002000300"), Ok, 7);
      begin
         pragma Assert (Counters.Key_Comparisons = 2
                        and then Counters.Bytes_Compared = 2
                        and then Counters.Bytes_Parsed = 7);
      exception
         when Ada.Assertions.Assertion_Error =>
            Fail ("decoder counters: not as expected");
      end;
      Ada.Text_IO.Put_Line ("decoder vectors: done");
   end Run;

begin
   pragma Assert (Enable);
end Decoder_Vectors;
