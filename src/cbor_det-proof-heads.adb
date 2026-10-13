--  Deterministic CBOR: heads.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause
--
--  The argument's decoding (Arg, Shortest and the big-endian readers) is
--  unfolded here and nowhere else: in Encode_Head, Lemma_Head_Canonical
--  and Lemma_Head_Same. Every other proof goes through those.

package body Cbor_Det.Proof.Heads with SPARK_Mode is

   function Encode_Head (M : Major; A : U64) return Bytes is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Arg);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Shortest);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Be2);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Be4);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Be8);
      IB : constant Byte := M * 32;
   begin
      if A < 24 then
         return [1 => IB + Byte (A)];
      elsif A < 2**8 then
         return [1 => IB + 24, 2 => Byte (A)];
      elsif A < 2**16 then
         return [1 => IB + 25, 2 => Byte (A / 2**8), 3 => Byte (A mod 2**8)];
      elsif A < 2**32 then
         return [1 => IB + 26,
                 2 => Byte (A / 2**24),
                 3 => Byte ((A / 2**16) mod 2**8),
                 4 => Byte ((A / 2**8) mod 2**8),
                 5 => Byte (A mod 2**8)];
      else
         return [1 => IB + 27,
                 2 => Byte (A / 2**56),
                 3 => Byte ((A / 2**48) mod 2**8),
                 4 => Byte ((A / 2**40) mod 2**8),
                 5 => Byte ((A / 2**32) mod 2**8),
                 6 => Byte ((A / 2**24) mod 2**8),
                 7 => Byte ((A / 2**16) mod 2**8),
                 8 => Byte ((A / 2**8) mod 2**8),
                 9 => Byte (A mod 2**8)];
      end if;
   end Encode_Head;

   procedure Lemma_Head_Canonical (B : Bytes; P : Positive) is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Same_Bytes);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Arg);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Shortest);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Be2);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Be4);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Be8);
      A : constant U64 := Arg (B, P);
      E : constant Bytes := Encode_Head (Major_Of (B (P)), A);
   begin
      case Info_Of (B (P)) is
         when 0 .. 23 =>
            pragma Assert (E'Length = 1);
            pragma Assert (B (P) = E (1));
         when 24 =>
            pragma Assert (E'Length = 2);
            pragma Assert (B (P) = E (1));
            pragma Assert (B (P + 1) = E (2));
         when 25 =>
            pragma Assert (E'Length = 3);
            pragma Assert (B (P) = E (1));
            pragma Assert (B (P + 1) = E (2));
            pragma Assert (B (P + 2) = E (3));
         when 26 =>
            pragma Assert (E'Length = 5);
            pragma Assert (B (P) = E (1));
            pragma Assert (B (P + 1) = E (2));
            pragma Assert (B (P + 2) = E (3));
            pragma Assert (B (P + 3) = E (4));
            pragma Assert (B (P + 4) = E (5));
         when 27 =>
            pragma Assert (E'Length = 9);
            pragma Assert (B (P) = E (1));
            pragma Assert (B (P + 1) = E (2));
            pragma Assert (B (P + 2) = E (3));
            pragma Assert (B (P + 3) = E (4));
            pragma Assert (B (P + 4) = E (5));
            pragma Assert (B (P + 5) = E (6));
            pragma Assert (B (P + 6) = E (7));
            pragma Assert (B (P + 7) = E (8));
            pragma Assert (B (P + 8) = E (9));
         when others =>
            pragma Assert (False);
      end case;
   end Lemma_Head_Canonical;

   procedure Lemma_Head_Unique
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Same_Bytes);
   begin
      Lemma_Head_Canonical (B1, P1);
      Lemma_Head_Canonical (B2, P2);
   end Lemma_Head_Unique;

   procedure Lemma_Head_Encoded
     (B : Bytes; P : Positive; M : Major; A : U64)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Same_Bytes);
      E : constant Bytes := Encode_Head (M, A);
   begin
      pragma Assert (for all K in 0 .. Head_Len (E (1)) - 1 =>
                       B (P + K) = E (1 + K));
      Lemma_Head_Same (E, 1, B, P);
   end Lemma_Head_Encoded;

   procedure Lemma_Head_Same
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Arg);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Shortest);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Be2);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Be4);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Be8);
   begin
      pragma Assert (B2 (P2) = B1 (P1));
      case Info_Of (B1 (P1)) is
         when 0 .. 23 =>
            null;
         when 24 =>
            pragma Assert (B2 (P2 + 1) = B1 (P1 + 1));
         when 25 =>
            pragma Assert (B2 (P2 + 1) = B1 (P1 + 1));
            pragma Assert (B2 (P2 + 2) = B1 (P1 + 2));
         when 26 =>
            pragma Assert (B2 (P2 + 1) = B1 (P1 + 1));
            pragma Assert (B2 (P2 + 2) = B1 (P1 + 2));
            pragma Assert (B2 (P2 + 3) = B1 (P1 + 3));
            pragma Assert (B2 (P2 + 4) = B1 (P1 + 4));
         when 27 =>
            pragma Assert (B2 (P2 + 1) = B1 (P1 + 1));
            pragma Assert (B2 (P2 + 2) = B1 (P1 + 2));
            pragma Assert (B2 (P2 + 3) = B1 (P1 + 3));
            pragma Assert (B2 (P2 + 4) = B1 (P1 + 4));
            pragma Assert (B2 (P2 + 5) = B1 (P1 + 5));
            pragma Assert (B2 (P2 + 6) = B1 (P1 + 6));
            pragma Assert (B2 (P2 + 7) = B1 (P1 + 7));
            pragma Assert (B2 (P2 + 8) = B1 (P1 + 8));
         when others =>
            pragma Assert (False);
      end case;
      pragma Assert (Arg (B2, P2) = Arg (B1, P1));
   end Lemma_Head_Same;

end Cbor_Det.Proof.Heads;
