--  cbor_det measurements of the decoder, as information, never a gate.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause
--
--  bench_main throughput         bytes per second of Check on four
--                                workloads, minimum, median and maximum
--                                of the repeats
--  bench_main stack WORKLOAD     the stack Check used on WORKLOAD
--                                (none, deep16, wide65536, wide1000000,
--                                widemap65536), by stack painting: the
--                                bytes below the calling frame that the
--                                call overwrote ("none": the overhead
--                                of the measurement itself)
--
--  Built in every cell like the test runner; the figures mean something
--  only in a production cell (-O3, checks off, no contracts: ghost code
--  erased). Inputs are built on the heap, so that their size does not
--  count against the stack.

with Ada.Command_Line; use Ada.Command_Line;
with Ada.Real_Time;    use Ada.Real_Time;
with Ada.Text_IO;      use Ada.Text_IO;

with Cbor_Det;         use Cbor_Det;
with Cbor_Det.Decoder; use Cbor_Det.Decoder;

procedure Bench_Main is

   type Bytes_Access is access Bytes;

   --  The shortest head of major type M and argument V.
   function Head (M : Natural; V : Natural) return Bytes is
     (if V < 24 then Bytes'(1 => Byte (M * 32 + V))
      elsif V < 256 then Bytes'(1 => Byte (M * 32 + 24), 2 => Byte (V))
      elsif V < 65_536
      then Bytes'(1 => Byte (M * 32 + 25), 2 => Byte (V / 256),
                  3 => Byte (V mod 256))
      else Bytes'(1 => Byte (M * 32 + 26), 2 => Byte (V / 2**24),
                  3 => Byte (V / 2**16 mod 256), 4 => Byte (V / 256 mod 256),
                  5 => Byte (V mod 256)));

   --  An array of N members, each the byte 00.
   function Wide_Array (N : Natural) return Bytes_Access is
      H : constant Bytes := Head (4, N);
      R : constant Bytes_Access := new Bytes (1 .. H'Length + N);
   begin
      R (1 .. H'Length) := H;
      R (H'Length + 1 .. R'Last) := [others => 0];
      return R;
   end Wide_Array;

   --  A map of N pairs: keys 0 .. N - 1 (integers, in order), values f6.
   function Wide_Map (N : Natural) return Bytes_Access is
      H     : constant Bytes := Head (5, N);
      Size  : Natural := H'Length;
      R     : Bytes_Access;
      Next  : Positive;
   begin
      for K in 0 .. N - 1 loop
         Size := Size + Head (0, K)'Length + 1;
      end loop;
      R := new Bytes (1 .. Size);
      R (1 .. H'Length) := H;
      Next := H'Length + 1;
      for K in 0 .. N - 1 loop
         declare
            Key : constant Bytes := Head (0, K);
         begin
            R (Next .. Next + Key'Length - 1) := Key;
            Next := Next + Key'Length;
            R (Next) := 16#F6#;
            Next := Next + 1;
         end;
      end loop;
      return R;
   end Wide_Map;

   --  Sixteen nested arrays around a map of six pairs.
   function Deep16 return Bytes_Access is
      Inner : constant Bytes :=
        [16#A6#, 16#01#, 16#00#, 16#02#, 16#00#, 16#03#, 16#00#,
         16#04#, 16#00#, 16#05#, 16#00#, 16#06#, 16#00#];
      R     : constant Bytes_Access := new Bytes (1 .. 15 + Inner'Length);
   begin
      R (1 .. 15) := [others => 16#81#];
      R (16 .. R'Last) := Inner;
      return R;
   end Deep16;

   procedure Must_Accept (Name : String; B : Bytes) is
      Result : Status;
      Where  : Integer;
   begin
      Check (B, Result, Where);
      if Result /= Ok then
         Put_Line ("bench: " & Name & " was not accepted: " & Result'Image
                   & " at" & Where'Image);
         Set_Exit_Status (Failure);
      end if;
   end Must_Accept;

   --  Times Check on B, Repeats times per sample, Samples samples; prints
   --  bytes per second, minimum, median and maximum of the samples.
   procedure Time_It
     (Name : String; B : Bytes; Repeats : Positive; Samples : Positive)
   is
      type Rates is array (1 .. Samples) of Long_Float;
      R      : Rates;
      Result : Status;
      Where  : Integer;
      Sink   : Integer := 0;
   begin
      Must_Accept (Name, B);
      for S in R'Range loop
         declare
            Start : constant Time := Clock;
         begin
            for I in 1 .. Repeats loop
               Check (B, Result, Where);
               Sink := (Sink + Where mod 1024) mod 1024;
            end loop;
            R (S) := Long_Float (B'Length) * Long_Float (Repeats)
                     / Long_Float (To_Duration (Clock - Start));
         end;
      end loop;
      for I in R'First + 1 .. R'Last loop
         for J in reverse R'First + 1 .. I loop
            exit when R (J - 1) <= R (J);
            declare
               T : constant Long_Float := R (J);
            begin
               R (J) := R (J - 1);
               R (J - 1) := T;
            end;
         end loop;
      end loop;
      Put_Line ("throughput, " & Name & " (" & Natural'Image (B'Length)
                & " bytes, " & Repeats'Image & " checks per sample,"
                & Samples'Image & " samples): MB/s min"
                & Long_Float'Image (R (R'First) / 1.0E6) & ", median"
                & Long_Float'Image (R ((R'First + R'Last) / 2) / 1.0E6)
                & ", max" & Long_Float'Image (R (R'Last) / 1.0E6)
                & (if Sink = 0 then " " else ""));
   end Time_It;

   Small : constant Bytes :=
     [16#A6#, 16#01#, 16#18#, 16#2A#, 16#02#, 16#63#, 16#61#, 16#62#,
      16#63#, 16#03#, 16#F5#, 16#04#, 16#82#, 16#01#, 16#02#, 16#05#,
      16#F6#, 16#06#, 16#44#, 16#DE#, 16#AD#, 16#BE#, 16#EF#];

begin
   if Argument_Count = 1 and then Argument (1) = "throughput" then
      Time_It ("small message (a map of 6 pairs)", Small, 200_000, 11);
      declare
         S : constant Bytes_Access := new Bytes (1 .. 5 + 1_000_000);
      begin
         S (1 .. 5) := Head (2, 1_000_000);
         S (6 .. S'Last) := [others => 16#61#];
         --  Check reads a string's head and skips its bytes, so this one
         --  measures a head, not a megabyte.
         Time_It ("long byte string (1 MB)", S.all, 1_000_000, 11);
      end;
      Time_It ("deep nesting (16 deep)", Deep16.all, 200_000, 11);
      Time_It ("wide map (65536 pairs)", Wide_Map (65_536).all, 50, 11);
   elsif Argument_Count = 2 and then Argument (1) = "stack" then
      declare
         W     : constant String := Argument (2);
         Input : constant Bytes_Access :=
           (if W = "deep16" then Deep16
            elsif W = "wide65536" then Wide_Array (65_536)
            elsif W = "wide1000000" then Wide_Array (1_000_000)
            elsif W = "widemap65536" then Wide_Map (65_536)
            else null);
         Size  : constant := 64 * 1024;
         Used  : Natural;

         --  Stack painting: Probe (True) fills an area of its frame with a
         --  pattern; Check is then called from the same place, so its
         --  frames fall on that area; Probe (False), the same frame
         --  again, counts the bytes no longer holding the pattern.
         procedure Probe (Paint : Boolean; Changed : out Natural) is
            Area : array (1 .. Size) of Byte with Volatile;
         begin
            Changed := 0;
            if Paint then
               for I in Area'Range loop
                  Area (I) := 16#A5#;
               end loop;
            else
               --  The stack grows down; Area (Area'Last) is the end next
               --  to this frame's caller, where Check's frames start.
               for I in Area'Range loop
                  if Area (I) /= 16#A5# then
                     Changed := Size - I + 1;
                     exit;
                  end if;
               end loop;
            end if;
         end Probe;

         procedure Run is
         begin
            if Input /= null then
               Must_Accept (W, Input.all);
            end if;
         end Run;
      begin
         if W /= "none" and then Input = null then
            --  A fixed message: the argument is the caller's text.
            Put_Line ("bench: unknown workload");
            Set_Exit_Status (Failure);
         else
            Probe (True, Used);
            Run;
            Probe (False, Used);
            Put_Line ("stack " & W & ": " & Used'Image
                      & " bytes below the caller's frame");
         end if;
      end;
   else
      Put_Line ("usage: bench_main throughput"
                & " | bench_main stack WORKLOAD");
      Set_Exit_Status (Failure);
   end if;
end Bench_Main;
