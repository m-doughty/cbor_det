--  Deterministic CBOR: the value an accepted item denotes.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause

package body Cbor_Det.Proof.Model with SPARK_Mode is

   --  Every proof here hides the recursive definitions of
   --  Cbor_Det.Proof.Det (their Hide_Info, which follows a completion,
   --  hides them only within that unit), so it proves from the lemmas'
   --  contracts alone.

   function Child
     (B : Bytes; P : Positive; I : Positive; D : Positive) return Positive
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      L  : constant Positive := Head_Len (B (P));
      Q0 : constant Positive := P + L;
      NM : constant Natural  := Member_Count (B, P);
   begin
      Lemma_Det_Container (B, P, D);
      pragma Assert (Members_End (B, Q0, NM, D - 1) = Det_End (B, P, D));
      Lemma_Members_Prefix (B, Q0, I, NM, D - 1);
      Lemma_Members_Last (B, Q0, I, D - 1);
      return Members_End (B, Q0, I - 1, D - 1);
   end Child;

   procedure Lemma_Child_At
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
      L  : constant Positive := Head_Len (B (P));
      Q0 : constant Positive := P + L;
      NM : constant Natural  := Member_Count (B, P);
   begin
      Lemma_Det_Container (B, P, D);
      Lemma_Members_Prefix (B, Q0, I, NM, D - 1);
      Lemma_Members_Last (B, Q0, I, D - 1);
      pragma Assert (Child (B, P, I, D) = Members_End (B, Q0, I - 1, D - 1));
   end Lemma_Child_At;

   procedure Lemma_Key_Slice
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
        (GNATprove, Unhide_Info, "Expression_Function_Body", Key_S);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Key_E);
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Val_E);
   begin
      Lemma_Child_At (B, P, 2 * M - 1, D);
      Lemma_Child_At (B, P, 2 * M, D);
   end Lemma_Key_Slice;

   procedure Lemma_Same_Open
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
        (GNATprove, Unhide_Info, "Expression_Function_Body", Same);
   begin
      null;
   end Lemma_Same_Open;

   procedure Lemma_Same_Map
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
        (GNATprove, Unhide_Info, "Expression_Function_Body", Same);
   begin
      null;
   end Lemma_Same_Map;

   procedure Lemma_Same_Map_At
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
        (GNATprove, Unhide_Info, "Expression_Function_Body",
         Same_Map_Clause);
   begin
      null;
   end Lemma_Same_Map_At;

   procedure Lemma_Same_Map_Back_At
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
        (GNATprove, Unhide_Info, "Expression_Function_Body",
         Same_Map_Clause);
   begin
      null;
   end Lemma_Same_Map_Back_At;

   procedure Lemma_Same_Close
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
        (GNATprove, Unhide_Info, "Expression_Function_Body", Same);
   begin
      null;
   end Lemma_Same_Close;

   procedure Lemma_Same_Map_In_Order
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
        (GNATprove, Unhide_Info, "Expression_Function_Body",
         Same_Map_Clause);
      N : constant Natural := Pairs (B1, P1);
   begin
      for I in 1 .. N loop
         pragma Assert
           (Same (B1, Key_S (B1, P1, I, D), B2, Key_S (B2, P2, I, D), D - 1)
            and then Same (B1, Key_E (B1, P1, I, D),
                           B2, Key_E (B2, P2, I, D), D - 1));
         pragma Loop_Invariant
           (for all Y in 1 .. I =>
              (for some J in 1 .. N =>
                 Same (B1, Key_S (B1, P1, Y, D),
                       B2, Key_S (B2, P2, J, D), D - 1)
                 and then Same (B1, Key_E (B1, P1, Y, D),
                                B2, Key_E (B2, P2, J, D), D - 1)));
         pragma Loop_Invariant
           (for all J in 1 .. I =>
              (for some X in 1 .. N =>
                 Same (B1, Key_S (B1, P1, X, D),
                       B2, Key_S (B2, P2, J, D), D - 1)
                 and then Same (B1, Key_E (B1, P1, X, D),
                                B2, Key_E (B2, P2, J, D), D - 1)));
      end loop;
      pragma Assert
        (for all I in 1 .. N =>
           (for some J in 1 .. N =>
              Same (B1, Key_S (B1, P1, I, D), B2, Key_S (B2, P2, J, D), D - 1)
              and then Same (B1, Key_E (B1, P1, I, D),
                             B2, Key_E (B2, P2, J, D), D - 1)));
      pragma Assert
        (for all J in 1 .. N =>
           (for some I in 1 .. N =>
              Same (B1, Key_S (B1, P1, I, D), B2, Key_S (B2, P2, J, D), D - 1)
              and then Same (B1, Key_E (B1, P1, I, D),
                             B2, Key_E (B2, P2, J, D), D - 1)));
   end Lemma_Same_Map_In_Order;

   procedure Lemma_Same_Refl (B : Bytes; P : Positive; D : Natural) is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      L : constant Positive := Head_Len (B (P));
   begin
      if Major_Of (B (P)) in 2 | 3 then
         Lemma_Same_Bytes_Refl (B, P + L, Det_End (B, P, D));
      elsif Major_Of (B (P)) = 4 then
         for I in 1 .. Arg_Nat (B, P) loop
            Lemma_Same_Refl (B, Child (B, P, I, D), D - 1);
            pragma Loop_Invariant
              (for all Y in 1 .. I =>
                 Same (B, Child (B, P, Y, D), B, Child (B, P, Y, D), D - 1));
         end loop;
      elsif Major_Of (B (P)) = 5 then
         for I in 1 .. Pairs (B, P) loop
            Lemma_Same_Refl (B, Key_S (B, P, I, D), D - 1);
            Lemma_Same_Refl (B, Key_E (B, P, I, D), D - 1);
            pragma Loop_Invariant
              (for all Y in 1 .. I =>
                 Same (B, Key_S (B, P, Y, D), B, Key_S (B, P, Y, D), D - 1)
                 and then Same (B, Key_E (B, P, Y, D),
                                B, Key_E (B, P, Y, D), D - 1));
         end loop;
         Lemma_Same_Map_In_Order (B, P, B, P, D);
      end if;
      Lemma_Same_Close (B, P, B, P, D);
   end Lemma_Same_Refl;

end Cbor_Det.Proof.Model;
