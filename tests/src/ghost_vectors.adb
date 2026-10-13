--  cbor_det tests: vectors for the ghost predicate Det_End, the whole-input
--  wrapper Accept_Whole and the lemmas, run as executable checks.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause
--
--  A ghost function can be called only from ghost code or an assertion,
--  so every check is a pragma Assert (or a lemma call, whose contract is
--  checked) inside a block that turns Assertion_Error into a counted
--  failure. When a check of an end fails, the end Det_End did return is
--  found by asking, candidate by candidate, and printed.

with Ada.Assertions;
with Ada.Exceptions;
with Ada.Real_Time;
with Ada.Text_IO;
with Ada.Strings.Unbounded; use Ada.Strings.Unbounded;

with Cbor_Det.Proof;           use Cbor_Det.Proof;
with Cbor_Det.Proof.Heads;     use Cbor_Det.Proof.Heads;
with Cbor_Det.Proof.Det;       use Cbor_Det.Proof.Det;
with Cbor_Det.Proof.Transport; use Cbor_Det.Proof.Transport;

with Support; use Support;

package body Ghost_Vectors is

   Enabled : Boolean := False;

   --  Called from an assertion at elaboration: True only when this unit's
   --  assertions, and so its ghost code, are executed.
   function Enable return Boolean is
   begin
      Enabled := True;
      return True;
   end Enable;

   function Ran return Boolean is (Enabled);

   function "+" (S : String) return Unbounded_String
     renames To_Unbounded_String;

   --  The end Det_End (B, B'First, D) returns, found without reading a
   --  ghost value outside an assertion; -1 if none was found.
   function Found_End (B : Bytes; D : Natural) return Integer is
   begin
      if B'Length > 1024 then
         return -1;   --  not searched: too slow on a long input
      end if;
      for C in B'First .. B'Last + 1 loop
         declare
            Candidate : constant Natural := (if C = B'First then 0 else C);
         begin
            pragma Assert (Det_End (B, B'First, D) /= Candidate);
         exception
            when Ada.Assertions.Assertion_Error =>
               return Candidate;
            when others =>
               return -1;
         end;
      end loop;
      return -1;
   end Found_End;

   --  Det_End (B, B'First, D) is B'First + Len, or 0 when Len < 0.
   procedure Check_End (Name : String; B : Bytes; D : Natural;
                        Len : Integer) is
   begin
      if Len < 0 then
         pragma Assert (Det_End (B, B'First, D) = 0);
      else
         pragma Assert (Det_End (B, B'First, D) = B'First + Len);
      end if;
      Pass;
   exception
      when Ada.Assertions.Assertion_Error =>
         Fail (Name & ": end at" & B'First'Image & ", expected"
               & Integer'Image (if Len < 0 then 0 else B'First + Len)
               & ", Det_End gives" & Found_End (B, D)'Image
               & " (bytes " & To_Hex (B) & ")");
      when E : others =>
         Fail (Name & ": end at" & B'First'Image & ": exception "
               & Ada.Exceptions.Exception_Name (E));
   end Check_End;

   procedure Check_Whole (Name : String; B : Bytes; Expected : Boolean) is
   begin
      pragma Assert (Accept_Whole (B) = Expected);
      Pass;
   exception
      when Ada.Assertions.Assertion_Error =>
         Fail (Name & ": Accept_Whole at" & B'First'Image & " is not "
               & Expected'Image & " (bytes " & To_Hex (B) & ")");
      when E : others =>
         Fail (Name & ": Accept_Whole at" & B'First'Image & ": exception "
               & Ada.Exceptions.Exception_Name (E));
   end Check_Whole;

   --  The lemmas on an item B accepted whole at Max_Depth: each call
   --  checks the lemma's precondition and postcondition on real bytes.
   procedure Lemmas (Name : String; B : Bytes) is
      F : constant Positive := B'First;
      T : constant Bytes := At_Top (B);
      J : constant Bytes := Hex ("ff1f") & B & Hex ("c000");
      L : constant Positive := Head_Len (B (F));
      M : constant Major := Major_Of (B (F));
      E : constant Positive := B'Last + 1;
   begin
      Lemma_Det_Step (B, F, Max_Depth);
      Lemma_Head_Canonical (B, F);
      Lemma_Head_Encoded (B, F, M, Arg (B, F));
      Lemma_Head_Unique (B, F, T, T'First);
      Lemma_Head_Same (B, F, J, 3);
      Lemma_Arg_Same (B, F, T, T'First);
      if M in 4 | 5 then
         declare
            N : constant Natural :=
              (if M = 5 then 2 * Arg_Nat (B, F) else Arg_Nat (B, F));
         begin
            Lemma_Det_Container (B, F, Max_Depth);
            Lemma_Members_Start (B, F + L, Max_Depth - 1);
            Lemma_Members_Monotone (B, F + L, N, Max_Depth - 1);
            Lemma_Members_Prefix (B, F + L, N / 2, N, Max_Depth - 1);
            if N > 0 then
               Lemma_Members_Last (B, F + L, N, Max_Depth - 1);
               Lemma_Members_Step (B, F + L, N, Max_Depth - 1);
            end if;
            Lemma_Members_Transport
              (B, F + L, T, T'First + L, N, Max_Depth - 1);
            if M = 5 then
               Lemma_Keys_All (B, F + L, N / 2, Max_Depth - 1);
               Lemma_Keys_Prefix (B, F + L, N / 2, N / 4, Max_Depth - 1);
               Lemma_Keys_Step (B, F + L, N / 2, Max_Depth - 1);
               Lemma_Keys_Transport
                 (B, F + L, T, T'First + L, N / 2, N, Max_Depth - 1);
            end if;
         end;
      end if;
      Lemma_Transport (B, F, T, T'First, Max_Depth);
      Lemma_Transport (T, T'First, B, F, Max_Depth);
      Lemma_Transport (B, F, J, 3, Max_Depth);
      Lemma_Same_Bytes_Refl (B, F, E);
      Lemma_Same_Bytes_Sym (B, F, E, T, T'First, T'Last + 1);
      Lemma_Same_Bytes_Trans (B, F, E, T, T'First, T'Last + 1, J, 3, E + 2);
      Lemma_Same_Bytes_Len (B, F, E, T, T'First, T'Last + 1);
      Lemma_Same_Bytes_Sub (B, F, E, T, T'First, T'Last + 1, F, F + L);
      Lemma_Same_Bytes_Join
        (B, F, F + L, E, T, T'First, T'First + L, T'Last + 1);
      Lemma_Lex_Less_Same (B, F, F + L, B, F, E,
                           T, T'First, T'First + L, J, 3, E + 2);
      --  Prefix-freedom on this item: no proper prefix of it holds an
      --  accepted item at its first byte (one would be a proper prefix
      --  of the item, against Lemma_Prefix_Free). Quadratic, so only for
      --  short items.
      if B'Length <= 300 then
         for K in 1 .. B'Length - 1 loop
            pragma Assert (Det_End (B (F .. F + K - 1), F, Max_Depth) = 0);
         end loop;
      end if;
      Pass;
   exception
      when Ada.Assertions.Assertion_Error =>
         Fail (Name & ": a lemma's contract does not hold (bytes "
               & To_Hex (B) & ")");
      when E : others =>
         Fail (Name & ": lemmas: exception "
               & Ada.Exceptions.Exception_Name (E));
   end Lemmas;

   --  A vector: B (from index 1) holds an item of Len bytes at depth D at
   --  its first byte, or none when Len < 0. Checked at index 1, with its
   --  last byte at Index'Last and, when accepted, with unrelated bytes
   --  after it. At Max_Depth the wrapper is checked too, and the lemmas
   --  are run on an item accepted whole, unless With_Lemmas is False.
   --  (Checking the lemmas' contracts on maps nested in maps costs about
   --  twice as much per level: some 40 s at 16 levels at -O0.)
   procedure Item (Name : String; B : Bytes; Len : Integer;
                   D : Natural := Max_Depth; With_Lemmas : Boolean := True) is
   begin
      if B'Length = 0 then
         Check_Whole (Name, B, False);
         return;
      end if;
      Check_End (Name, B, D, Len);
      Check_End (Name & " (at the top)", At_Top (B), D, Len);
      if Len >= 0 then
         Check_End (Name & " (bytes after)",
                    Rebase (B & Hex ("ff1f00"), 7), D, Len);
         Check_End (Name & " (bytes after, at the top)",
                    At_Top (B & Hex ("00")), D, Len);
      end if;
      if D = Max_Depth then
         Check_Whole (Name, B, Len = B'Length);
         Check_Whole (Name & " (at the top)", At_Top (B), Len = B'Length);
         if Len >= 0 then
            Check_Whole (Name & " (bytes after)", B & Hex ("00"), False);
         end if;
         if Len = B'Length and then With_Lemmas then
            Lemmas (Name, B);
         end if;
      end if;
   end Item;

   procedure Accepted (Name : String; Text : String) is
      B : constant Bytes := Hex (Text);
   begin
      Item (Name, B, B'Length);
   end Accepted;

   procedure Refused (Name : String; Text : String) is
   begin
      Item (Name, Hex (Text), -1);
   end Refused;

   function Repeat (Text : String; N : Natural) return String is
     (if N = 0 then "" else Text & Repeat (Text, N - 1));

   ---------------------------------------------------------------------
   --  RFC 8949, Appendix A (Table 6), every example, from the RFC's text.
   ---------------------------------------------------------------------

   type Example is record
      Name     : Unbounded_String;
      Encoded  : Unbounded_String;
      Accepted : Boolean;   --  in the profile and deterministic
   end record;

   type Example_List is array (Positive range <>) of Example;

   Appendix_A : constant Example_List :=
     [
      (+"0",
       +("00"),
       True),
      (+"1",
       +("01"),
       True),
      (+"10",
       +("0a"),
       True),
      (+"23",
       +("17"),
       True),
      (+"24",
       +("1818"),
       True),
      (+"25",
       +("1819"),
       True),
      (+"100",
       +("1864"),
       True),
      (+"1000",
       +("1903e8"),
       True),
      (+"1000000",
       +("1a000f4240"),
       True),
      (+"1000000000000",
       +("1b000000e8d4a51000"),
       True),
      (+"18446744073709551615",
       +("1bffffffffffffffff"),
       True),
      (+"18446744073709551616",
       +("c249010000000000000000"),
       False),
      (+"-18446744073709551616",
       +("3bffffffffffffffff"),
       True),
      (+"-18446744073709551617",
       +("c349010000000000000000"),
       False),
      (+"-1",
       +("20"),
       True),
      (+"-10",
       +("29"),
       True),
      (+"-100",
       +("3863"),
       True),
      (+"-1000",
       +("3903e7"),
       True),
      (+"0.0",
       +("f90000"),
       False),
      (+"-0.0",
       +("f98000"),
       False),
      (+"1.0",
       +("f93c00"),
       False),
      (+"1.1",
       +("fb3ff199999999999a"),
       False),
      (+"1.5",
       +("f93e00"),
       False),
      (+"65504.0",
       +("f97bff"),
       False),
      (+"100000.0",
       +("fa47c35000"),
       False),
      (+"3.4028234663852886e+38",
       +("fa7f7fffff"),
       False),
      (+"1.0e+300",
       +("fb7e37e43c8800759c"),
       False),
      (+"5.960464477539063e-8",
       +("f90001"),
       False),
      (+"0.00006103515625",
       +("f90400"),
       False),
      (+"-4.0",
       +("f9c400"),
       False),
      (+"-4.1",
       +("fbc010666666666666"),
       False),
      (+"Infinity",
       +("f97c00"),
       False),
      (+"NaN",
       +("f97e00"),
       False),
      (+"-Infinity",
       +("f9fc00"),
       False),
      (+"Infinity",
       +("fa7f800000"),
       False),
      (+"NaN",
       +("fa7fc00000"),
       False),
      (+"-Infinity",
       +("faff800000"),
       False),
      (+"Infinity",
       +("fb7ff0000000000000"),
       False),
      (+"NaN",
       +("fb7ff8000000000000"),
       False),
      (+"-Infinity",
       +("fbfff0000000000000"),
       False),
      (+"false",
       +("f4"),
       True),
      (+"true",
       +("f5"),
       True),
      (+"null",
       +("f6"),
       True),
      (+"undefined",
       +("f7"),
       False),
      (+"simple(16)",
       +("f0"),
       False),
      (+"simple(255)",
       +("f8ff"),
       False),
      (+"0(""2013-03-21T20:04:00Z"")",
       +("c074323031332d30332d32315432303a30343a30" &
          "305a"),
       False),
      (+"1(1363896240)",
       +("c11a514b67b0"),
       False),
      (+"1(1363896240.5)",
       +("c1fb41d452d9ec200000"),
       False),
      (+"23(h'01020304')",
       +("d74401020304"),
       False),
      (+"24(h'6449455446')",
       +("d818456449455446"),
       False),
      (+"32(""http://www.example.com"")",
       +("d82076687474703a2f2f7777772e6578616d706c" &
          "652e636f6d"),
       False),
      (+"h''",
       +("40"),
       True),
      (+"h'01020304'",
       +("4401020304"),
       True),
      (+"""""",
       +("60"),
       True),
      (+"""a""",
       +("6161"),
       True),
      (+"""IETF""",
       +("6449455446"),
       True),
      (+"""\""\\""",
       +("62225c"),
       True),
      (+"""\u00fc""",
       +("62c3bc"),
       True),
      (+"""\u6c34""",
       +("63e6b0b4"),
       True),
      (+"""\ud800\udd51""",
       +("64f0908591"),
       True),
      (+"[]",
       +("80"),
       True),
      (+"[1, 2, 3]",
       +("83010203"),
       True),
      (+"[1, [2, 3], [4, 5]]",
       +("8301820203820405"),
       True),
      (+"[1, 2, 3, ..., 25]",
       +("98190102030405060708090a0b0c0d0e0f101112" &
          "131415161718181819"),
       True),
      (+"{}",
       +("a0"),
       True),
      (+"{1: 2, 3: 4}",
       +("a201020304"),
       True),
      (+"{""a"": 1, ""b"": [2, 3]}",
       +("a26161016162820203"),
       True),
      (+"[""a"", {""b"": ""c""}]",
       +("826161a161626163"),
       True),
      (+"{""a"": ""A"", ..., ""e"": ""E""}",
       +("a561616141616261426163614361646144616561" &
          "45"),
       True),
      (+"(_ h'0102', h'030405')",
       +("5f42010243030405ff"),
       False),
      (+"(_ ""strea"", ""ming"")",
       +("7f657374726561646d696e67ff"),
       False),
      (+"[_ ]",
       +("9fff"),
       False),
      (+"[_ 1, [2, 3], [_ 4, 5]]",
       +("9f018202039f0405ffff"),
       False),
      (+"[_ 1, [2, 3], [4, 5]]",
       +("9f01820203820405ff"),
       False),
      (+"[1, [2, 3], [_ 4, 5]]",
       +("83018202039f0405ff"),
       False),
      (+"[1, [_ 2, 3], [4, 5]]",
       +("83019f0203ff820405"),
       False),
      (+"[_ 1, 2, 3, ..., 25]",
       +("9f0102030405060708090a0b0c0d0e0f10111213" &
          "1415161718181819ff"),
       False),
      (+"{_ ""a"": 1, ""b"": [_ 2, 3]}",
       +("bf61610161629f0203ffff"),
       False),
      (+"[""a"", {_ ""b"": ""c""}]",
       +("826161bf61626163ff"),
       False),
      (+"{_ ""Fun"": true, ""Amt"": -2}",
       +("bf6346756ef563416d7421ff"),
       False)
     ];

   procedure Run_Appendix_A is
      In_Profile : Natural := 0;
   begin
      for X of Appendix_A loop
         declare
            Name : constant String := "Appendix A " & To_String (X.Name);
            B    : constant Bytes := Hex (To_String (X.Encoded));
         begin
            if X.Accepted then
               In_Profile := In_Profile + 1;
               Item (Name, B, B'Length);
            else
               Item (Name, B, -1);
            end if;
         end;
      end loop;
      if Appendix_A'Length /= 81 or else In_Profile /= 37 then
         Fail ("Appendix A: 81 examples, 37 in the profile, expected");
      end if;
   end Run_Appendix_A;

   ---------------------------------------------------------------------
   --  One refusal for each rule, and the examples with several faults.
   ---------------------------------------------------------------------

   procedure Run_Rules is
   begin
      --  The head's own bytes run past the end.
      Refused ("truncated head 19", "19");
      Refused ("truncated head 1901", "1901");
      Refused ("truncated head 1a000000", "1a000000");
      Refused ("truncated head 3b", "3b00000000000000");
      Refused ("truncated head 98", "98");
      --  Additional information 28 to 30, any major type.
      Refused ("reserved 1c", "1c00000000000000000000");
      Refused ("reserved 3d", "3d00");
      Refused ("reserved 5e", "5e00");
      Refused ("reserved 7c", "7c00");
      Refused ("reserved 9d", "9d00");
      Refused ("reserved be", "be00");
      Refused ("reserved dc", "dc00");
      Refused ("reserved fd", "fd00");
      --  Additional information 31: indefinite lengths and the break.
      Refused ("indefinite 1f", "1f");
      Refused ("indefinite byte string", "5f4100ff");
      Refused ("indefinite text string", "7f6161ff");
      Refused ("indefinite array", "9f00ff");
      Refused ("indefinite map", "bf0000ff");
      Refused ("break", "ff");
      --  Tags.
      Refused ("tag 0", "c000");
      Refused ("tag 24", "d818456449455446");
      Refused ("tag 55799", "d9d9f700");
      Refused ("bignum", "c249010000000000000000");
      --  Major type 7 other than false, true and null.
      Refused ("undefined", "f7");
      Refused ("simple 0", "e0");
      Refused ("simple 16", "f0");
      Refused ("simple 19", "f3");
      Refused ("f8 14", "f814");
      Refused ("f8 18", "f818");
      Refused ("f8 20", "f820");
      Refused ("f8 ff", "f8ff");
      Refused ("half float", "f93c00");
      Refused ("single float", "fa47c35000");
      Refused ("double float", "fb3ff199999999999a");
      --  An argument wider than it needs to be (majors 0 to 5).
      Refused ("non-shortest 1817", "1817");
      Refused ("non-shortest 190017", "190017");
      Refused ("non-shortest 1a0000ffff", "1a0000ffff");
      Refused ("non-shortest 1b00000000ffffffff", "1b00000000ffffffff");
      Refused ("non-shortest 3800", "3800");
      Refused ("non-shortest 5800", "5800");
      Refused ("non-shortest 7800", "7800");
      Refused ("non-shortest 9800", "9800");
      Refused ("non-shortest b800", "b800");
      Refused ("non-shortest map value", "a1001800");
      --  A length or count that does not fit in the bytes left.
      Refused ("string past the end", "42aa");
      Refused ("text past the end", "6261");
      Refused ("array past the end", "8201");
      Refused ("map past the end", "a100");
      Refused ("map pairs past the end", "a2000001");
      Refused ("member past the end", "811901");
      --  Keys out of order and equal keys.
      Refused ("unsorted keys", "a202000100");
      Refused ("duplicate keys", "a2010001" & "00");
      Refused ("duplicate keys, other values", "a20100" & "01f6");
      Refused ("unsorted keys at depth", "8181a2020001" & "00");
      --  Several faults: the item is refused whichever is found first.
      Refused ("array, unsupported simple then indefinite", "82f8141f");
      Refused ("map, unsorted key then non-shortest", "a20201011805");
      Refused ("array count past the end", "8201");
   end Run_Rules;

   ---------------------------------------------------------------------
   --  The mandatory witnesses of the differential test, and key order.
   ---------------------------------------------------------------------

   procedure Run_Witnesses is
   begin
      Accepted ("invalid UTF-8 text 61 ff", "61ff");
      Accepted ("overlong UTF-8 text", "62c080");
      Accepted ("surrogate in text", "63eda080");
      Accepted ("1 and true as distinct keys", "a20100f500");
      Accepted ("byte and text string keys of the same bytes",
                "a2416100616100");
      Accepted ("array and map keys", "a28000a000");
      Accepted ("array keys sharing a prefix", "a282010200820103" & "00");
      Refused ("array keys sharing a prefix, reversed",
               "a282010300820102" & "00");
      Accepted ("map keys sharing a prefix", "a2a1000000a1000100");
      Refused ("map keys sharing a prefix, reversed", "a2a1000100a1000000");
      Accepted ("string keys sharing a prefix",
                "a2626161006361616100");
      Accepted ("18 18 before 20 (bytewise, not length-first)",
                "a21818002000");
      Refused ("20 before 18 18", "a22000181800");
      Accepted ("keys of every kind", "a8" & "0000" & "2000" & "4000" & "6000"
                & "8000" & "a000" & "f400" & "f600");
      Refused ("f5 before f4", "a2f500f400");
   end Run_Witnesses;

   ---------------------------------------------------------------------
   --  The depth bound: D is the container depth still allowed.
   ---------------------------------------------------------------------

   type Text_List is array (Positive range <>) of Unbounded_String;

   Scalars : constant Text_List :=
     [+"00", +"17", +"20", +"40", +"60", +"f4", +"f5", +"f6",
      +"1bffffffffffffffff", +"4100"];

   procedure Run_Depth is
   begin
      for Scalar of Scalars loop
         Item ("scalar " & To_String (Scalar) & " at D = 0",
               Hex (To_String (Scalar)), To_String (Scalar)'Length / 2, 0);
      end loop;
      Item ("empty array at D = 0", Hex ("80"), -1, 0);
      Item ("empty map at D = 0", Hex ("a0"), -1, 0);
      Item ("empty array at D = 1", Hex ("80"), 1, 1);
      Item ("empty map at D = 1", Hex ("a0"), 1, 1);
      Item ("two arrays at D = 1", Hex ("8180"), -1, 1);
      Item ("two arrays at D = 2", Hex ("8180"), 2, 2);
      Item ("siblings at D = 2", Hex ("828080"), 3, 2);
      Item ("a map key container at D = 1", Hex ("a18000"), -1, 1);
      Item ("a map key container at D = 2", Hex ("a18000"), 3, 2);
      for N in 1 .. Max_Depth + 1 loop
         declare
            In_Bound : constant Boolean := N <= Max_Depth;
            Arrays   : constant Bytes := Hex (Repeat ("81", N) & "00");
            Empty    : constant Bytes := Hex (Repeat ("81", N - 1) & "80");
            Maps     : constant Bytes := Hex (Repeat ("a100", N) & "00");
            Keys     : constant Bytes :=
              Hex (Repeat ("a1", N) & Repeat ("00", N + 1));
            Mixed    : constant Bytes :=
              Hex (Repeat ("82a1", N / 2) & Repeat ("81", N mod 2) & "f6"
                   & Repeat ("00f5", N / 2));
         begin
            Item (N'Image & " nested arrays", Arrays,
                  (if In_Bound then Arrays'Length else -1));
            Item (N'Image & " nested containers, the last empty", Empty,
                  (if In_Bound then Empty'Length else -1));
            Item (N'Image & " nested maps", Maps,
                  (if In_Bound then Maps'Length else -1),
                  With_Lemmas => N <= 10);
            Item (N'Image & " nested map keys", Keys,
                  (if In_Bound then Keys'Length else -1),
                  With_Lemmas => N <= 10);
            Item (N'Image & " nested arrays and maps", Mixed,
                  (if In_Bound then Mixed'Length else -1));
         end;
      end loop;
   end Run_Depth;

   ---------------------------------------------------------------------
   --  Cases only Ada can build.
   ---------------------------------------------------------------------

   --  Null arrays with any bounds: never accepted whole; the definitions
   --  that take a position are total on them.
   procedure Null_Array (First : Integer; Last : Integer) is
      N    : constant Bytes (First .. Last) := [];
      Name : constant String :=
        "null array" & First'Image & " .." & Last'Image;
   begin
      Check_Whole (Name, N, False);
      if First >= 1 and then First = Last + 1 then
         declare
            Q : constant Positive := First;
         begin
            pragma Assert (Members_End (N, Q, 0, Max_Depth) = Q);
            pragma Assert (Members_End (N, Q, 1, Max_Depth) = 0);
            pragma Assert (Keys_Ascending (N, Q, 1, Max_Depth));
            pragma Assert (not Lex_Less (N, Q, Q, N, Q, Q));
            pragma Assert (Slice_OK (N, Q, Q));
            pragma Assert (Same_Bytes (N, Q, Q, N, Q, Q));
            Lemma_Members_Zero (N, Q, 1, 3, Max_Depth);
            Pass;
         exception
            when Ada.Assertions.Assertion_Error =>
               Fail (Name & ": the definitions on a null array");
            when E : others =>
               Fail (Name & ": exception "
                     & Ada.Exceptions.Exception_Name (E));
         end;
      end if;
   end Null_Array;

   Oversized : constant Text_List :=
     [+"5a7fffffff", +"5a80000000", +"5bffffffffffffffff",
      +"5b0000000100000000", +"5b7fffffffffffffff",
      +"7a7fffffff", +"7a80000000", +"7bffffffffffffffff",
      +"9a7fffffff", +"9a80000000", +"9bffffffffffffffff",
      +"9b0000000100000000",
      +"ba3ffffffe", +"ba3fffffff", +"ba40000000",
      +"ba7fffffff", +"ba80000000", +"bb000000003fffffff",
      +"bb0000000040000000", +"bbffffffffffffffff"];

   procedure Run_Ada_Cases is
   begin
      Null_Array (1, 0);
      Null_Array (3, 1);
      Null_Array (7, 6);
      Null_Array (0, -1);
      Null_Array (-1, -2);
      Null_Array (Integer'First + 1, Integer'First);
      Null_Array (Cbor_Det.Index'Last + 1, Cbor_Det.Index'Last);
      Null_Array (Integer'Last, Integer'Last - 1);

      --  Lengths and counts that do not fit a Natural, or the buffer: each
      --  refused, never an exception (the conversion to Natural is
      --  guarded, and a map's count is checked by division before it is
      --  doubled).
      for Head of Oversized loop
         Refused ("oversized " & To_String (Head),
                  To_String (Head) & "0000000000000000");
      end loop;

      --  Exact fits: a length or count equal to the bytes left is
      --  accepted, one more is refused.
      Accepted ("string filling the buffer", "43010203");
      Refused ("string one past the buffer", "430102");
      Accepted ("256-byte string", "590100" & Repeat ("ab", 256));
      Refused ("256-byte string, one short", "590100" & Repeat ("ab", 255));
      Accepted ("array filling the buffer", "83010203");
      Refused ("array one past the buffer", "830102");
      Accepted ("map filling the buffer", "a201000200");
      Refused ("map one past the buffer", "a2010002");
      declare
         Wide : constant Bytes := Hex ("5a00010000") & [1 .. 65_536 => 7];
         Long : constant Bytes := Hex ("9a00010000") & [1 .. 65_536 => 0];
      begin
         Check_End ("65536-byte string", Wide, Max_Depth, Wide'Length);
         Check_End ("65536-byte string at the top", At_Top (Wide),
                    Max_Depth, Wide'Length);
         Check_Whole ("65536-byte string", Wide, True);
         Check_End ("65536-member array", Long, Max_Depth, Long'Length);
         Check_End ("65536-member array at the top", At_Top (Long),
                    Max_Depth, Long'Length);
         Check_Whole ("65536-member array", Long, True);
         Check_End ("65536-member array, one short",
                    Long (1 .. Long'Last - 1), Max_Depth, -1);
      end;
   end Run_Ada_Cases;

   --  Runs Part and prints its counts and time.
   procedure Timed (Name : String; Part : not null access procedure) is
      use Ada.Real_Time;
      Start  : constant Time := Clock;
      Passes : constant Natural := Passed;
      Fails  : constant Natural := Failed;
   begin
      Part.all;
      Ada.Text_IO.Put_Line
        ("ghost vectors, " & Name & ": passed"
         & Natural'Image (Passed - Passes) & ", failed"
         & Natural'Image (Failed - Fails) & ", in"
         & Duration'Image (To_Duration (Clock - Start)) & " s");
   end Timed;

   procedure Run is
   begin
      if not Enabled then
         return;
      end if;
      Timed ("Appendix A", Run_Appendix_A'Access);
      Timed ("a refusal per rule", Run_Rules'Access);
      Timed ("witnesses", Run_Witnesses'Access);
      Timed ("depth", Run_Depth'Access);
      Timed ("Ada-side cases", Run_Ada_Cases'Access);
   end Run;

begin
   pragma Assert (Enable);
end Ghost_Vectors;
