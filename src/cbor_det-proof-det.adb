--  Deterministic CBOR: the deterministic-item predicate.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause

package body Cbor_Det.Proof.Det with SPARK_Mode is

   procedure Lemma_Lex_Step
     (B1 : Bytes; P1 : Natural; E1 : Natural;
      B2 : Bytes; P2 : Natural; E2 : Natural)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Lex_Less);
   begin
      null;
   end Lemma_Lex_Step;

   procedure Lemma_Lex_Not_Slice
     (B1 : Bytes; P1 : Natural; E1 : Natural;
      B2 : Bytes; P2 : Natural; E2 : Natural)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Lex_Less);
   begin
      null;
   end Lemma_Lex_Not_Slice;

   procedure Lemma_Nat_Round (N : Natural) is
   begin
      pragma Assert (Natural (U64 (N)) = N);
   end Lemma_Nat_Round;

   procedure Lemma_Arg_Is (B : Bytes; P : Positive; N : Natural) is
   begin
      pragma Assert (Arg_Small (B, P));
      pragma Assert (Natural (U64 (N)) = N);
      pragma Assert (Arg_Nat (B, P) = Natural (Arg (B, P)));
      pragma Assert (Natural (Arg (B, P)) = Natural (U64 (N)));
   end Lemma_Arg_Is;

   procedure Lemma_Arg_Small_Of (B : Bytes; P : Positive) is
   begin
      null;
   end Lemma_Arg_Small_Of;

   procedure Lemma_Arg_Same
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive)
   is
   begin
      null;
   end Lemma_Arg_Same;

   procedure Lemma_Members_Start (B : Bytes; Q : Positive; D : Natural) is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Members_End);
   begin
      null;
   end Lemma_Members_Start;

   procedure Lemma_Members_Step
     (B : Bytes; Q : Positive; K : Positive; D : Natural)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Members_End);
   begin
      null;
   end Lemma_Members_Step;

   procedure Lemma_Det_Step (B : Bytes; P : Positive; D : Natural) is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Det_End);
   begin
      null;
   end Lemma_Det_Step;

   procedure Lemma_Keys_Step
     (B : Bytes; Q : Positive; N : Natural; D : Natural)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Keys_Ascending);
   begin
      null;
   end Lemma_Keys_Step;

   procedure Lemma_Det_Container (B : Bytes; P : Positive; D : Natural) is
   begin
      Lemma_Det_Step (B, P, D);
   end Lemma_Det_Container;

   procedure Lemma_Members_Last
     (B : Bytes; Q : Positive; K : Positive; D : Natural)
   is
   begin
      Lemma_Members_Step (B, Q, K, D);
   end Lemma_Members_Last;

   procedure Lemma_Members_Prefix
     (B : Bytes; Q : Positive; I : Natural; K : Natural; D : Natural)
   is
   begin
      if I < K then
         Lemma_Members_Last (B, Q, K, D);
         Lemma_Members_Prefix (B, Q, I, K - 1, D);
      end if;
   end Lemma_Members_Prefix;

   procedure Lemma_Members_Monotone
     (B : Bytes; Q : Positive; K : Natural; D : Natural)
   is
   begin
      if K > 0 then
         Lemma_Members_Last (B, Q, K, D);
         Lemma_Members_Monotone (B, Q, K - 1, D);
      end if;
   end Lemma_Members_Monotone;

   procedure Lemma_Members_Zero
     (B : Bytes; Q : Positive; I : Natural; K : Natural; D : Natural)
   is
   begin
      if I < K then
         Lemma_Members_Zero (B, Q, I, K - 1, D);
         Lemma_Members_Step (B, Q, K, D);
      end if;
   end Lemma_Members_Zero;

   procedure Lemma_Keys_Extend
     (B : Bytes; Q : Positive; KN : Positive; D : Natural)
   is
   begin
      Lemma_Keys_Step (B, Q, KN, D);
   end Lemma_Keys_Extend;

   procedure Lemma_Keys_Prefix
     (B : Bytes; Q : Positive; N : Natural; M : Natural; D : Natural)
   is
   begin
      for X in reverse M + 1 .. N loop
         pragma Loop_Invariant (Keys_Ascending (B, Q, X, D));
         Lemma_Keys_Step (B, Q, X, D);
         Lemma_Keys_Step (B, Q, X - 1, D);
         pragma Assert (Keys_Ascending (B, Q, X - 1, D));
      end loop;
   end Lemma_Keys_Prefix;

   procedure Lemma_Keys_Break
     (B : Bytes; Q : Positive; N : Natural; J : Positive; D : Natural)
   is
   begin
      if Keys_Ascending (B, Q, N, D) then
         Lemma_Keys_Prefix (B, Q, N, J, D);
         pragma Assert (Keys_Ascending (B, Q, J, D));
         Lemma_Keys_Step (B, Q, J, D);
         pragma Assert (False);
      end if;
   end Lemma_Keys_Break;

   procedure Lemma_Keys_All
     (B : Bytes; Q : Positive; N : Natural; D : Natural)
   is
   begin
      if N >= 2 then
         Lemma_Keys_Step (B, Q, N, D);
         pragma Assert (Keys_Ascending (B, Q, N - 1, D));
         pragma Assert (Lex_Less (B, Members_End (B, Q, 2 * N - 4, D),
                                     Members_End (B, Q, 2 * N - 3, D),
                                  B, Members_End (B, Q, 2 * N - 2, D),
                                     Members_End (B, Q, 2 * N - 1, D)));
         Lemma_Keys_All (B, Q, N - 1, D);
         pragma Assert (for all J in 2 .. N - 1 =>
                          Lex_Less (B, Members_End (B, Q, 2 * J - 4, D),
                                       Members_End (B, Q, 2 * J - 3, D),
                                    B, Members_End (B, Q, 2 * J - 2, D),
                                       Members_End (B, Q, 2 * J - 1, D)));
      end if;
   end Lemma_Keys_All;

   procedure Lemma_Same_Bytes_Refl (B : Bytes; P : Natural; E : Natural) is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Same_Bytes);
   begin
      null;
   end Lemma_Same_Bytes_Refl;

   procedure Lemma_Same_Bytes_Sym
     (BL : Bytes; PL : Natural; EL : Natural;
      BR : Bytes; PR : Natural; ER : Natural)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Same_Bytes);
   begin
      null;
   end Lemma_Same_Bytes_Sym;

   procedure Lemma_Same_Bytes_Trans
     (B1 : Bytes; P1 : Natural; E1 : Natural;
      B2 : Bytes; P2 : Natural; E2 : Natural;
      B3 : Bytes; P3 : Natural; E3 : Natural)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Same_Bytes);
   begin
      null;
   end Lemma_Same_Bytes_Trans;

   procedure Lemma_Same_Bytes_Len
     (B1 : Bytes; P1 : Natural; E1 : Natural;
      B2 : Bytes; P2 : Natural; E2 : Natural)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Same_Bytes);
   begin
      null;
   end Lemma_Same_Bytes_Len;

   procedure Lemma_Same_Bytes_Join
     (B1 : Bytes; P1 : Natural; M1 : Natural; E1 : Natural;
      B2 : Bytes; P2 : Natural; M2 : Natural; E2 : Natural)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Same_Bytes);
   begin
      null;
   end Lemma_Same_Bytes_Join;

   procedure Lemma_Same_Bytes_Sub
     (B1 : Bytes; P1 : Natural; E1 : Natural;
      B2 : Bytes; P2 : Natural; E2 : Natural;
      Q1 : Natural; F1 : Natural)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Same_Bytes);
   begin
      null;
   end Lemma_Same_Bytes_Sub;

end Cbor_Det.Proof.Det;
