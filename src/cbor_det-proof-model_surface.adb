--  Deterministic CBOR: proof clients of the value relation and of the
--  uniqueness lemmas.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause

package body Cbor_Det.Proof.Model_Surface with SPARK_Mode is

   procedure Client_Child
     (B : Bytes; P : Positive; I : Positive; D : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      pragma Assert
        (Child (B, P, I, D) in B'Range);
      pragma Assert
        (Child (B, P, I, D)
         = Members_End
             (B, P + Head_Len (B (P)), I - 1, D - 1));
      pragma Assert
        (Det_End (B, Child (B, P, I, D), D - 1) /= 0);
   end Client_Child;

   procedure Client_Lemma_Child_At
     (B : Bytes; P : Positive; I : Positive; D : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Child_At (B, P, I, D);
      pragma Assert
        (Child (B, P, I, D)
         = Members_End (B, P + Head_Len (B (P)), I - 1, D - 1));
      pragma Assert
        (Det_End (B, Child (B, P, I, D), D - 1)
         = Members_End (B, P + Head_Len (B (P)), I, D - 1));
      pragma Assert
        (Det_End (B, Child (B, P, I, D), D - 1)
         <= Det_End (B, P, D));
   end Client_Lemma_Child_At;

   procedure Client_Key_S
     (B : Bytes; P : Positive; M : Positive; D : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      pragma Assert
        (Key_S (B, P, M, D) in B'Range);
      pragma Assert
        (Det_End (B, Key_S (B, P, M, D), D - 1) /= 0);
   end Client_Key_S;

   procedure Client_Key_E
     (B : Bytes; P : Positive; M : Positive; D : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      pragma Assert
        (Key_E (B, P, M, D) in B'Range);
      pragma Assert
        (Det_End (B, Key_E (B, P, M, D), D - 1) /= 0);
   end Client_Key_E;

   procedure Client_Val_E
     (B : Bytes; P : Positive; M : Positive; D : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      pragma Assert
        (Val_E (B, P, M, D) in B'First + 1 .. B'Last + 1);
   end Client_Val_E;

   procedure Client_Lemma_Key_Slice
     (B : Bytes; P : Positive; M : Positive; D : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Key_Slice (B, P, M, D);
      pragma Assert
        (Key_S (B, P, M, D) in B'Range);
      pragma Assert
        (Key_E (B, P, M, D)
         in Key_S (B, P, M, D) + 1 .. B'Last);
      pragma Assert
        (Val_E (B, P, M, D)
         in Key_E (B, P, M, D) + 1 .. B'Last + 1);
      pragma Assert
        (Val_E (B, P, M, D) <= Det_End (B, P, D));
      pragma Assert
        (Det_End (B, Key_S (B, P, M, D), D - 1)
         = Key_E (B, P, M, D));
      pragma Assert
        (Det_End (B, Key_E (B, P, M, D), D - 1)
         = Val_E (B, P, M, D));
      pragma Assert
        (Key_S (B, P, M, D)
         = Members_End
             (B, P + Head_Len (B (P)), 2 * M - 2, D - 1));
      pragma Assert
        (Key_E (B, P, M, D)
         = Members_End
             (B, P + Head_Len (B (P)), 2 * M - 1, D - 1));
      pragma Assert
        (Val_E (B, P, M, D)
         = Members_End
             (B, P + Head_Len (B (P)), 2 * M, D - 1));
   end Client_Lemma_Key_Slice;

   procedure Client_Lemma_Same_Open
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Natural)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Same_Open (B1, P1, B2, P2, D);
      pragma Assert
        (Major_Of (B1 (P1)) = Major_Of (B2 (P2)));
      pragma Assert
        (Major_Of (B1 (P1)) in 0 .. 5 | 7);
      pragma Assert
        ((if Major_Of (B1 (P1)) in 0 | 1
          then Arg (B1, P1) = Arg (B2, P2)));
      pragma Assert
        ((if Major_Of (B1 (P1)) in 2 | 3
          then Arg_Nat (B1, P1) = Arg_Nat (B2, P2)
               and then Same_Bytes
                 (B1, P1 + Head_Len (B1 (P1)), Det_End (B1, P1, D),
                  B2, P2 + Head_Len (B2 (P2)), Det_End (B2, P2, D))));
      pragma Assert
        ((if Major_Of (B1 (P1)) = 4
          then Arg_Nat (B1, P1) = Arg_Nat (B2, P2)
               and then
                 (for all I in 1 .. Arg_Nat (B1, P1) =>
                    Same (B1, Child (B1, P1, I, D),
                          B2, Child (B2, P2, I, D), D - 1))));
      pragma Assert
        ((if Major_Of (B1 (P1)) = 5
          then Arg_Nat (B1, P1) = Arg_Nat (B2, P2)));
      pragma Assert
        ((if Major_Of (B1 (P1)) = 7
          then Info_Of (B1 (P1)) = Info_Of (B2 (P2))));
   end Client_Lemma_Same_Open;

   procedure Client_Lemma_Same_Map
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Same_Map (B1, P1, B2, P2, D);
      pragma Assert
        (Is_Map (B2, P2, D));
      pragma Assert
        (Pairs (B1, P1) = Pairs (B2, P2));
      pragma Assert
        (Same_Map_Clause (B1, P1, B2, P2, D));
   end Client_Lemma_Same_Map;

   procedure Client_Lemma_Same_Map_At
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      I : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Same_Map_At (B1, P1, B2, P2, D, I);
      pragma Assert
        ((for some J in 1 .. Pairs (B1, P1) =>
            Same (B1, Key_S (B1, P1, I, D),
                  B2, Key_S (B2, P2, J, D), D - 1)
            and then Same (B1, Key_E (B1, P1, I, D),
                           B2, Key_E (B2, P2, J, D), D - 1)));
   end Client_Lemma_Same_Map_At;

   procedure Client_Lemma_Same_Map_Back_At
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      J : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Same_Map_Back_At (B1, P1, B2, P2, D, J);
      pragma Assert
        ((for some I in 1 .. Pairs (B1, P1) =>
            Same (B1, Key_S (B1, P1, I, D),
                  B2, Key_S (B2, P2, J, D), D - 1)
            and then Same (B1, Key_E (B1, P1, I, D),
                           B2, Key_E (B2, P2, J, D), D - 1)));
   end Client_Lemma_Same_Map_Back_At;

   procedure Client_Lemma_Same_Close
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Natural)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Same_Close (B1, P1, B2, P2, D);
      pragma Assert
        (Same (B1, P1, B2, P2, D));
   end Client_Lemma_Same_Close;

   procedure Client_Lemma_Same_Map_In_Order
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Same_Map_In_Order (B1, P1, B2, P2, D);
      pragma Assert
        (Same_Map_Clause (B1, P1, B2, P2, D));
   end Client_Lemma_Same_Map_In_Order;

   procedure Client_Lemma_Same_Refl
     (B : Bytes; P : Positive; D : Natural)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Same_Refl (B, P, D);
      pragma Assert
        (Same (B, P, B, P, D));
   end Client_Lemma_Same_Refl;

   procedure Client_Lemma_Lex_Irrefl
     (B1 : Bytes; P1 : Natural; E1 : Natural;
      B2 : Bytes; P2 : Natural; E2 : Natural)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Lex_Irrefl (B1, P1, E1, B2, P2, E2);
      pragma Assert
        (not Lex_Less (B1, P1, E1, B2, P2, E2));
   end Client_Lemma_Lex_Irrefl;

   procedure Client_Lemma_Lex_Trans
     (A : Bytes; PA : Natural; EA : Natural;
      B : Bytes; PB : Natural; EB : Natural;
      C : Bytes; PC : Natural; EC : Natural)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Lex_Trans (A, PA, EA, B, PB, EB, C, PC, EC);
      pragma Assert
        (Lex_Less (A, PA, EA, C, PC, EC));
   end Client_Lemma_Lex_Trans;

   procedure Client_Lemma_Strict_Zero
     (B : Bytes; P : Positive; D : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Strict_Zero (B, P, D);
      pragma Assert
        (Keys_Strict_Upto (B, P, D, 0));
   end Client_Lemma_Strict_Zero;

   procedure Client_Lemma_Strict_Extend
     (B : Bytes; P : Positive; D : Positive; I : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Strict_Extend (B, P, D, I);
      pragma Assert
        (Keys_Strict_Upto (B, P, D, I));
   end Client_Lemma_Strict_Extend;

   procedure Client_Lemma_Strict_At
     (B : Bytes; P : Positive; D : Positive; I : Positive; J : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Strict_At (B, P, D, I, J);
      pragma Assert
        (Lex_Less (B, Key_S (B, P, I, D), Key_E (B, P, I, D),
                   B, Key_S (B, P, J, D), Key_E (B, P, J, D)));
   end Client_Lemma_Strict_At;

   procedure Client_Lemma_Keys_Strict
     (B : Bytes; P : Positive; D : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Keys_Strict (B, P, D);
      pragma Assert
        (Keys_Strict_Upto (B, P, D, Pairs (B, P)));
   end Client_Lemma_Keys_Strict;

   procedure Client_Lemma_Keys_Distinct
     (B : Bytes; P : Positive; I : Positive; J : Positive; D : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Keys_Distinct (B, P, I, J, D);
      pragma Assert
        (not Same_Bytes (B, Key_S (B, P, I, D), Key_E (B, P, I, D),
                         B, Key_S (B, P, J, D), Key_E (B, P, J, D)));
   end Client_Lemma_Keys_Distinct;

   procedure Client_Lemma_Match_Zero
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Match_Zero (B1, P1, B2, P2, D);
      pragma Assert
        (Match_Fwd (B1, P1, B2, P2, D, 0));
   end Client_Lemma_Match_Zero;

   procedure Client_Lemma_Match_Fwd_Extend
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      I : Positive; J : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Match_Fwd_Extend (B1, P1, B2, P2, D, I, J);
      pragma Assert
        (Match_Fwd (B1, P1, B2, P2, D, I));
   end Client_Lemma_Match_Fwd_Extend;

   procedure Client_Lemma_Match_Fwd_At
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      I : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Match_Fwd_At (B1, P1, B2, P2, D, I);
      pragma Assert
        ((for some J in 1 .. Pairs (B1, P1) =>
            Same_Bytes
              (B1, Key_S (B1, P1, I, D), Key_E (B1, P1, I, D),
               B2, Key_S (B2, P2, J, D), Key_E (B2, P2, J, D))));
   end Client_Lemma_Match_Fwd_At;

   procedure Client_Find_Key
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      I : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      pragma Assert
        (Find_Key (B1, P1, B2, P2, D, I) <= Pairs (B1, P1));
      pragma Assert
        (Same_Bytes
         (B1, Key_S (B1, P1, I, D), Key_E (B1, P1, I, D),
         B2, Key_S (B2, P2, Find_Key (B1, P1, B2, P2, D, I), D),
         Key_E (B2, P2, Find_Key (B1, P1, B2, P2, D, I), D)));
   end Client_Find_Key;

   procedure Client_Lemma_Key_In_Place
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      I : Positive; J : Positive; M : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Key_In_Place (B1, P1, B2, P2, D, I, J, M);
      pragma Assert
        (Same_Bytes
           (B1, Key_S (B1, P1, I, D), Key_E (B1, P1, I, D),
            B2, Key_S (B2, P2, I, D), Key_E (B2, P2, I, D)));
   end Client_Lemma_Key_In_Place;

   procedure Client_Lemma_Map_Keys
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Map_Keys (B1, P1, B2, P2, D);
      pragma Assert
        ((for all I in 1 .. Pairs (B1, P1) =>
            Same_Bytes
              (B1, Key_S (B1, P1, I, D), Key_E (B1, P1, I, D),
               B2, Key_S (B2, P2, I, D), Key_E (B2, P2, I, D))));
   end Client_Lemma_Map_Keys;

   procedure Client_Lemma_Keys_Match_In_Order
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Keys_Match_In_Order (B1, P1, B2, P2, D);
      pragma Assert
        (Keys_Match (B1, P1, B2, P2, D));
   end Client_Lemma_Keys_Match_In_Order;

   procedure Client_Find_Pair
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      I : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      pragma Assert
        (Find_Pair (B1, P1, B2, P2, D, I) <= Pairs (B1, P1));
      pragma Assert
        (Same (B1, Key_S (B1, P1, I, D),
               B2, Key_S (B2, P2, Find_Pair (B1, P1, B2, P2, D, I), D),
               D - 1));
      pragma Assert
        (Same (B1, Key_E (B1, P1, I, D),
               B2, Key_E (B2, P2, Find_Pair (B1, P1, B2, P2, D, I), D),
               D - 1));
   end Client_Find_Pair;

   procedure Client_Find_Pair_Back
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      J : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      pragma Assert
        (Find_Pair_Back (B1, P1, B2, P2, D, J) <= Pairs (B1, P1));
      pragma Assert
        (Same (B1, Key_S (B1, P1, Find_Pair_Back (B1, P1, B2, P2, D, J), D),
               B2, Key_S (B2, P2, J, D), D - 1));
      pragma Assert
        (Same (B1, Key_E (B1, P1, Find_Pair_Back (B1, P1, B2, P2, D, J), D),
               B2, Key_E (B2, P2, J, D), D - 1));
   end Client_Find_Pair_Back;

   procedure Client_Lemma_Map_Match
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Map_Match (B1, P1, B2, P2, D);
      pragma Assert
        (Keys_Match (B1, P1, B2, P2, D));
   end Client_Lemma_Map_Match;

   procedure Client_Lemma_Map_Values
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Map_Values (B1, P1, B2, P2, D);
      pragma Assert
        ((for all I in 1 .. Pairs (B1, P1) =>
            Same_Bytes
              (B1, Key_E (B1, P1, I, D), Val_E (B1, P1, I, D),
               B2, Key_E (B2, P2, I, D), Val_E (B2, P2, I, D))));
   end Client_Lemma_Map_Values;

   procedure Client_Lemma_Map_Concat
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Map_Concat (B1, P1, B2, P2, D);
      pragma Assert
        (Det_End (B1, P1, D) - P1 = Det_End (B2, P2, D) - P2);
      pragma Assert
        (Same_Bytes (B1, P1, Det_End (B1, P1, D),
                     B2, P2, Det_End (B2, P2, D)));
   end Client_Lemma_Map_Concat;

   procedure Client_Lemma_CU
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Natural)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_CU (B1, P1, B2, P2, D);
      pragma Assert
        (Det_End (B1, P1, D) - P1 = Det_End (B2, P2, D) - P2);
      pragma Assert
        (Same_Bytes (B1, P1, Det_End (B1, P1, D),
                     B2, P2, Det_End (B2, P2, D)));
   end Client_Lemma_CU;

   procedure Client_Lemma_CU_Whole
     (B1 : Bytes; B2 : Bytes)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_CU_Whole (B1, B2);
      pragma Assert
        (B1'Length = B2'Length);
      pragma Assert
        ((for all K in B1'Range =>
            B1 (K) = B2 (K - B1'First + B2'First)));
      pragma Assert
        (Same_Bytes (B1, B1'First, B1'Last + 1,
                     B2, B2'First, B2'Last + 1));
   end Client_Lemma_CU_Whole;

   procedure Client_Lemma_Head_Rebased
     (B1 : Bytes; P1 : Positive; E1 : Natural;
      B2 : Bytes; P2 : Positive; E2 : Natural)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Head_Rebased (B1, P1, E1, B2, P2, E2);
      pragma Assert
        (Head_Fits (B2, P2));
      pragma Assert
        (B2 (P2) = B1 (P1));
      pragma Assert
        (Head_Len (B2 (P2)) = Head_Len (B1 (P1)));
      pragma Assert
        (Major_Of (B2 (P2)) = Major_Of (B1 (P1)));
      pragma Assert
        (Arg (B2, P2) = Arg (B1, P1));
      pragma Assert
        (Head_OK (B2, P2) = Head_OK (B1, P1));
   end Client_Lemma_Head_Rebased;

   procedure Client_Lemma_Members_Rebased
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Members_Rebased (B1, P1, B2, P2, D);
      pragma Assert
        (Major_Of (B2 (P2)) = Major_Of (B1 (P1)));
      pragma Assert
        (Head_Len (B2 (P2)) = Head_Len (B1 (P1)));
      pragma Assert
        (Arg_Nat (B2, P2) = Arg_Nat (B1, P1));
      pragma Assert
        ((for all J in 0 .. Member_Count (B1, P1) =>
            Members_End (B2, P2 + Head_Len (B2 (P2)), J, D - 1)
            = Members_End (B1, P1 + Head_Len (B1 (P1)), J, D - 1)
              - P1 + P2));
   end Client_Lemma_Members_Rebased;

   procedure Client_Lemma_Same_Of_Bytes
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Natural)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Same_Of_Bytes (B1, P1, B2, P2, D);
      pragma Assert
        (Same (B1, P1, B2, P2, D));
   end Client_Lemma_Same_Of_Bytes;

   procedure Client_Lemma_Child_Same_Of_Bytes
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      I : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Child_Same_Of_Bytes (B1, P1, B2, P2, D, I);
      pragma Assert
        (Major_Of (B2 (P2)) = 4);
      pragma Assert
        (Arg_Nat (B2, P2) = Arg_Nat (B1, P1));
      pragma Assert
        (Same (B1, Child (B1, P1, I, D),
               B2, Child (B2, P2, I, D), D - 1));
   end Client_Lemma_Child_Same_Of_Bytes;

   procedure Client_Lemma_Array_Same_Of_Bytes
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Array_Same_Of_Bytes (B1, P1, B2, P2, D);
      pragma Assert
        (Major_Of (B2 (P2)) = 4);
      pragma Assert
        (Arg_Nat (B2, P2) = Arg_Nat (B1, P1));
      pragma Assert
        ((for all I in 1 .. Arg_Nat (B1, P1) =>
            Same (B1, Child (B1, P1, I, D),
                  B2, Child (B2, P2, I, D), D - 1)));
   end Client_Lemma_Array_Same_Of_Bytes;

   procedure Client_Lemma_Pair_Same_Of_Bytes
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      I : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Pair_Same_Of_Bytes (B1, P1, B2, P2, D, I);
      pragma Assert
        (Is_Map (B2, P2, D));
      pragma Assert
        (Pairs (B2, P2) = Pairs (B1, P1));
      pragma Assert
        (Same (B1, Key_S (B1, P1, I, D),
               B2, Key_S (B2, P2, I, D), D - 1));
      pragma Assert
        (Same (B1, Key_E (B1, P1, I, D),
               B2, Key_E (B2, P2, I, D), D - 1));
   end Client_Lemma_Pair_Same_Of_Bytes;

   procedure Client_Lemma_Map_Same_Of_Bytes
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Map_Same_Of_Bytes (B1, P1, B2, P2, D);
      pragma Assert
        (Is_Map (B2, P2, D));
      pragma Assert
        (Pairs (B2, P2) = Pairs (B1, P1));
      pragma Assert
        ((for all I in 1 .. Pairs (B1, P1) =>
            Same (B1, Key_S (B1, P1, I, D),
                  B2, Key_S (B2, P2, I, D), D - 1)
            and then Same (B1, Key_E (B1, P1, I, D),
                           B2, Key_E (B2, P2, I, D), D - 1)));
   end Client_Lemma_Map_Same_Of_Bytes;

   procedure Client_Lemma_Same_Of_Bytes_Whole
     (B1 : Bytes; B2 : Bytes)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Same_Of_Bytes_Whole (B1, B2);
      pragma Assert
        (Same (B1, B1'First, B2, B2'First, Max_Depth));
   end Client_Lemma_Same_Of_Bytes_Whole;

   procedure Client_Lemma_Same_Iff_Bytes_Whole
     (B1 : Bytes; B2 : Bytes)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Same_Map_Clause);
   begin
      Lemma_Same_Iff_Bytes_Whole (B1, B2);
      pragma Assert
        (Same (B1, B1'First, B2, B2'First, Max_Depth)
         = (B1'Length = B2'Length
            and then (for all K in B1'Range =>
                        B1 (K) = B2 (K - B1'First + B2'First))));
   end Client_Lemma_Same_Iff_Bytes_Whole;

end Cbor_Det.Proof.Model_Surface;
