--  Deterministic CBOR: canonical uniqueness.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause

with Cbor_Det.Proof.Transport; use Cbor_Det.Proof.Transport;

package body Cbor_Det.Proof.Unique with SPARK_Mode is

   --  Every proof here hides the recursive definitions of
   --  Cbor_Det.Proof.Det and of Cbor_Det.Proof.Model (their Hide_Info,
   --  which follows a completion, hides them only within their own unit),
   --  so it proves from the lemmas' contracts alone.

   procedure Lemma_Lex_Irrefl
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
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Same_Bytes);
   begin
      Lemma_Lex_Step (B1, P1, E1, B2, P2, E2);
      if P1 < E1 then
         Lemma_Lex_Irrefl (B1, P1 + 1, E1, B2, P2 + 1, E2);
      end if;
   end Lemma_Lex_Irrefl;

   procedure Lemma_Lex_Trans
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
      Lemma_Lex_Step (A, PA, EA, B, PB, EB);
      Lemma_Lex_Step (B, PB, EB, C, PC, EC);
      Lemma_Lex_Step (A, PA, EA, C, PC, EC);
      if PA < EA and then A (PA) = B (PB) and then B (PB) = C (PC) then
         Lemma_Lex_Trans (A, PA + 1, EA, B, PB + 1, EB, C, PC + 1, EC);
      end if;
   end Lemma_Lex_Trans;

   procedure Lemma_Strict_Zero (B : Bytes; P : Positive; D : Positive) is
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
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body",
         Keys_Strict_Upto);
   begin
      null;
   end Lemma_Strict_Zero;

   procedure Lemma_Strict_Extend
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
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body",
         Keys_Strict_Upto);
   begin
      null;
   end Lemma_Strict_Extend;

   procedure Lemma_Strict_At
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
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body",
         Keys_Strict_Upto);
   begin
      pragma Assert
        (J in I + 1 .. Pairs (B, P)
         and then (for all X in I + 1 .. Pairs (B, P) =>
                     Lex_Less (B, Key_S (B, P, I, D), Key_E (B, P, I, D),
                               B, Key_S (B, P, X, D), Key_E (B, P, X, D))));
   end Lemma_Strict_At;

   procedure Lemma_Keys_Strict (B : Bytes; P : Positive; D : Positive) is
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
      N  : constant Natural  := Pairs (B, P);
      Q0 : constant Positive := P + Head_Len (B (P));
   begin
      Lemma_Det_Container (B, P, D);
      Lemma_Strict_Zero (B, P, D);
      for I in 1 .. N loop
         Lemma_Key_Slice (B, P, I, D);
         for J in I + 1 .. N loop
            Lemma_Key_Slice (B, P, J, D);
            Lemma_Key_Slice (B, P, J - 1, D);
            Lemma_Keys_Prefix (B, Q0, N, J, D - 1);
            Lemma_Keys_Step (B, Q0, J, D - 1);
            pragma Assert
              (Lex_Less (B, Key_S (B, P, J - 1, D), Key_E (B, P, J - 1, D),
                         B, Key_S (B, P, J, D), Key_E (B, P, J, D)));
            if J > I + 1 then
               Lemma_Lex_Trans
                 (B, Key_S (B, P, I, D), Key_E (B, P, I, D),
                  B, Key_S (B, P, J - 1, D), Key_E (B, P, J - 1, D),
                  B, Key_S (B, P, J, D), Key_E (B, P, J, D));
            end if;
            pragma Loop_Invariant
              (for all X in I + 1 .. J =>
                 Lex_Less (B, Key_S (B, P, I, D), Key_E (B, P, I, D),
                           B, Key_S (B, P, X, D), Key_E (B, P, X, D)));
         end loop;
         Lemma_Strict_Extend (B, P, D, I);
         pragma Loop_Invariant (Keys_Strict_Upto (B, P, D, I));
      end loop;
   end Lemma_Keys_Strict;

   procedure Lemma_Keys_Distinct
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
      KSI : constant Positive := Key_S (B, P, I, D);
      KEI : constant Positive := Key_E (B, P, I, D);
      KSJ : constant Positive := Key_S (B, P, J, D);
      KEJ : constant Positive := Key_E (B, P, J, D);
   begin
      Lemma_Keys_Strict (B, P, D);
      Lemma_Key_Slice (B, P, I, D);
      Lemma_Key_Slice (B, P, J, D);
      if Same_Bytes (B, KSI, KEI, B, KSJ, KEJ) then
         Lemma_Same_Bytes_Refl (B, KSI, KEI);
         Lemma_Same_Bytes_Sym (B, KSI, KEI, B, KSJ, KEJ);
         if I < J then
            Lemma_Strict_At (B, P, D, I, J);
            Lemma_Lex_Less_Same (B, KSI, KEI, B, KSJ, KEJ,
                                 B, KSI, KEI, B, KSI, KEI);
         else
            Lemma_Strict_At (B, P, D, I => J, J => I);
            Lemma_Lex_Less_Same (B, KSJ, KEJ, B, KSI, KEI,
                                 B, KSI, KEI, B, KSI, KEI);
         end if;
         Lemma_Lex_Irrefl (B, KSI, KEI, B, KSI, KEI);
         pragma Assert (False);
      end if;
   end Lemma_Keys_Distinct;

   procedure Lemma_Match_Zero
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
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Match_Fwd);
   begin
      null;
   end Lemma_Match_Zero;

   procedure Lemma_Match_Fwd_Extend
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
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Match_Fwd);
   begin
      null;
   end Lemma_Match_Fwd_Extend;

   procedure Lemma_Match_Fwd_At
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
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Match_Fwd);
   begin
      null;
   end Lemma_Match_Fwd_At;

   function Find_Key
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      I : Positive) return Positive
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
      N : constant Natural := Pairs (B1, P1);
      R : Positive := 1;
   begin
      Lemma_Key_Slice (B1, P1, I, D);
      Lemma_Match_Fwd_At (B1, P1, B2, P2, D, I);
      for X in 1 .. N loop
         Lemma_Key_Slice (B2, P2, X, D);
         if Same_Bytes (B1, Key_S (B1, P1, I, D), Key_E (B1, P1, I, D),
                        B2, Key_S (B2, P2, X, D), Key_E (B2, P2, X, D))
         then
            R := X;
            exit;
         end if;
         pragma Loop_Invariant
           (for all Y in 1 .. X =>
              not Same_Bytes
                (B1, Key_S (B1, P1, I, D), Key_E (B1, P1, I, D),
                 B2, Key_S (B2, P2, Y, D), Key_E (B2, P2, Y, D)));
      end loop;
      return R;
   end Find_Key;

   procedure Lemma_Key_In_Place
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
      Lemma_Key_Slice (B1, P1, I, D);
      Lemma_Key_Slice (B2, P2, I, D);
      Lemma_Key_Slice (B1, P1, M, D);
      Lemma_Key_Slice (B2, P2, J, D);
      declare
         S1I : constant Positive := Key_S (B1, P1, I, D);
         E1I : constant Positive := Key_E (B1, P1, I, D);
         S2I : constant Positive := Key_S (B2, P2, I, D);
         E2I : constant Positive := Key_E (B2, P2, I, D);
         S2J : constant Positive := Key_S (B2, P2, J, D);
         E2J : constant Positive := Key_E (B2, P2, J, D);
         S1M : constant Positive := Key_S (B1, P1, M, D);
         E1M : constant Positive := Key_E (B1, P1, M, D);
      begin
         Lemma_Same_Bytes_Sym (B2, S2I, E2I, B1, S1M, E1M);
         if J < I then
            --  Key J of map 1 = key J of map 2 = key I of map 1, but key J
            --  of map 1 < key I of map 1.
            Lemma_Key_Slice (B1, P1, J, D);
            Lemma_Strict_At (B1, P1, D, I => J, J => I);
            Lemma_Same_Bytes_Sym (B1, S1I, E1I, B2, S2J, E2J);
            Lemma_Same_Bytes_Trans
              (B1, Key_S (B1, P1, J, D), Key_E (B1, P1, J, D),
               B2, S2J, E2J, B1, S1I, E1I);
            Lemma_Same_Bytes_Refl (B1, S1I, E1I);
            Lemma_Lex_Less_Same
              (B1, Key_S (B1, P1, J, D), Key_E (B1, P1, J, D),
               B1, S1I, E1I, B1, S1I, E1I, B1, S1I, E1I);
            Lemma_Lex_Irrefl (B1, S1I, E1I, B1, S1I, E1I);
            pragma Assert (False);
         elsif J > I and then M < I then
            --  Key M of map 2 = key M of map 1 = key I of map 2, but key M
            --  of map 2 < key I of map 2.
            Lemma_Key_Slice (B2, P2, M, D);
            Lemma_Strict_At (B2, P2, D, I => M, J => I);
            Lemma_Same_Bytes_Sym
              (B1, S1M, E1M,
               B2, Key_S (B2, P2, M, D), Key_E (B2, P2, M, D));
            Lemma_Same_Bytes_Trans
              (B2, Key_S (B2, P2, M, D), Key_E (B2, P2, M, D),
               B1, S1M, E1M, B2, S2I, E2I);
            Lemma_Same_Bytes_Refl (B2, S2I, E2I);
            Lemma_Lex_Less_Same
              (B2, Key_S (B2, P2, M, D), Key_E (B2, P2, M, D),
               B2, S2I, E2I, B2, S2I, E2I, B2, S2I, E2I);
            Lemma_Lex_Irrefl (B2, S2I, E2I, B2, S2I, E2I);
            pragma Assert (False);
         elsif J > I and then M > I then
            --  Key I of map 1 < key M of map 1 = key I of map 2 < key J of
            --  map 2 = key I of map 1.
            Lemma_Strict_At (B1, P1, D, I, M);
            Lemma_Strict_At (B2, P2, D, I, J);
            Lemma_Same_Bytes_Refl (B1, S1I, E1I);
            Lemma_Same_Bytes_Refl (B2, S2I, E2I);
            Lemma_Same_Bytes_Sym (B1, S1I, E1I, B2, S2J, E2J);
            Lemma_Lex_Less_Same
              (B1, S1I, E1I, B1, S1M, E1M, B1, S1I, E1I, B2, S2I, E2I);
            Lemma_Lex_Less_Same
              (B2, S2I, E2I, B2, S2J, E2J, B2, S2I, E2I, B1, S1I, E1I);
            Lemma_Lex_Trans (B1, S1I, E1I, B2, S2I, E2I, B1, S1I, E1I);
            Lemma_Lex_Irrefl (B1, S1I, E1I, B1, S1I, E1I);
            pragma Assert (False);
         end if;
         --  J = I, or M = I with key I of map 2 = key I of map 1.
         pragma Assert (J = I or else M = I);
      end;
   end Lemma_Key_In_Place;

   procedure Lemma_Map_Keys
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
      N : constant Natural := Pairs (B1, P1);
   begin
      Lemma_Keys_Strict (B1, P1, D);
      Lemma_Keys_Strict (B2, P2, D);
      for I in 1 .. N loop
         Lemma_Key_In_Place
           (B1, P1, B2, P2, D, I,
            J => Find_Key (B1, P1, B2, P2, D, I),
            M => Find_Key
                   (B1 => B2, P1 => P2, B2 => B1, P2 => P1, D => D, I => I));
         pragma Loop_Invariant
           (for all Y in 1 .. I =>
              Same_Bytes (B1, Key_S (B1, P1, Y, D), Key_E (B1, P1, Y, D),
                          B2, Key_S (B2, P2, Y, D), Key_E (B2, P2, Y, D)));
      end loop;
   end Lemma_Map_Keys;

   procedure Lemma_Keys_Match_In_Order
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
      N : constant Natural := Pairs (B1, P1);
   begin
      Lemma_Match_Zero (B1, P1, B2, P2, D);
      for I in 1 .. N loop
         Lemma_Match_Fwd_Extend (B1, P1, B2, P2, D, I, I);
         pragma Loop_Invariant (Match_Fwd (B1, P1, B2, P2, D, I));
      end loop;
      Lemma_Match_Zero
        (B1 => B2, P1 => P2, B2 => B1, P2 => P1, D => D);
      for I in 1 .. N loop
         Lemma_Key_Slice (B1, P1, I, D);
         Lemma_Key_Slice (B2, P2, I, D);
         Lemma_Same_Bytes_Sym
           (B1, Key_S (B1, P1, I, D), Key_E (B1, P1, I, D),
            B2, Key_S (B2, P2, I, D), Key_E (B2, P2, I, D));
         Lemma_Match_Fwd_Extend (B2, P2, B1, P1, D, I, I);
         pragma Loop_Invariant (Match_Fwd
              (B1 => B2, P1 => P2, B2 => B1, P2 => P1, D => D, I => I));
      end loop;
   end Lemma_Keys_Match_In_Order;

   function Find_Pair
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      I : Positive) return Positive
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
      N : constant Natural := Pairs (B1, P1);
      R : Positive := 1;
   begin
      Lemma_Key_Slice (B1, P1, I, D);
      Lemma_Same_Map_At (B1, P1, B2, P2, D, I);
      for X in 1 .. N loop
         Lemma_Key_Slice (B2, P2, X, D);
         if Same (B1, Key_S (B1, P1, I, D), B2, Key_S (B2, P2, X, D), D - 1)
           and then Same (B1, Key_E (B1, P1, I, D),
                          B2, Key_E (B2, P2, X, D), D - 1)
         then
            R := X;
            exit;
         end if;
         pragma Loop_Invariant
           (for all Y in 1 .. X =>
              not (Same (B1, Key_S (B1, P1, I, D),
                         B2, Key_S (B2, P2, Y, D), D - 1)
                   and then Same (B1, Key_E (B1, P1, I, D),
                                  B2, Key_E (B2, P2, Y, D), D - 1)));
      end loop;
      return R;
   end Find_Pair;

   function Find_Pair_Back
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Positive;
      J : Positive) return Positive
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
      N : constant Natural := Pairs (B1, P1);
      R : Positive := 1;
   begin
      Lemma_Key_Slice (B2, P2, J, D);
      Lemma_Same_Map_Back_At (B1, P1, B2, P2, D, J);
      for X in 1 .. N loop
         Lemma_Key_Slice (B1, P1, X, D);
         if Same (B1, Key_S (B1, P1, X, D), B2, Key_S (B2, P2, J, D), D - 1)
           and then Same (B1, Key_E (B1, P1, X, D),
                          B2, Key_E (B2, P2, J, D), D - 1)
         then
            R := X;
            exit;
         end if;
         pragma Loop_Invariant
           (for all Y in 1 .. X =>
              not (Same (B1, Key_S (B1, P1, Y, D),
                         B2, Key_S (B2, P2, J, D), D - 1)
                   and then Same (B1, Key_E (B1, P1, Y, D),
                                  B2, Key_E (B2, P2, J, D), D - 1)));
      end loop;
      return R;
   end Find_Pair_Back;

   procedure Lemma_Map_Match
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
      N : constant Natural := Pairs (B1, P1);
   begin
      Lemma_Same_Map (B1, P1, B2, P2, D);
      pragma Assert (Pairs (B2, P2) = N);
      --  Every key of map 1 is the same bytes as a key of map 2.
      Lemma_Match_Zero (B1, P1, B2, P2, D);
      for I in 1 .. N loop
         declare
            X : constant Positive := Find_Pair (B1, P1, B2, P2, D, I);
         begin
            Lemma_Key_Slice (B1, P1, I, D);
            Lemma_Key_Slice (B2, P2, X, D);
            Lemma_CU (B1, Key_S (B1, P1, I, D),
                      B2, Key_S (B2, P2, X, D), D - 1);
            Lemma_Match_Fwd_Extend (B1, P1, B2, P2, D, I, X);
         end;
         pragma Loop_Invariant (Match_Fwd (B1, P1, B2, P2, D, I));
      end loop;
      --  Every key of map 2 is the same bytes as a key of map 1: the same,
      --  with the maps swapped.
      Lemma_Match_Zero
        (B1 => B2, P1 => P2, B2 => B1, P2 => P1, D => D);
      for J in 1 .. N loop
         declare
            X : constant Positive := Find_Pair_Back (B1, P1, B2, P2, D, J);
         begin
            Lemma_Key_Slice (B1, P1, X, D);
            Lemma_Key_Slice (B2, P2, J, D);
            Lemma_CU (B1, Key_S (B1, P1, X, D),
                      B2, Key_S (B2, P2, J, D), D - 1);
            Lemma_Same_Bytes_Sym
              (B1, Key_S (B1, P1, X, D), Key_E (B1, P1, X, D),
               B2, Key_S (B2, P2, J, D), Key_E (B2, P2, J, D));
            Lemma_Match_Fwd_Extend (B2, P2, B1, P1, D, J, X);
         end;
         pragma Loop_Invariant
           (Match_Fwd
              (B1 => B2, P1 => P2, B2 => B1, P2 => P1, D => D, I => J));
      end loop;
   end Lemma_Map_Match;

   procedure Lemma_Map_Values
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
      N : constant Natural := Pairs (B1, P1);
   begin
      Lemma_Same_Map (B1, P1, B2, P2, D);
      for I in 1 .. N loop
         declare
            X : constant Positive := Find_Pair (B1, P1, B2, P2, D, I);
         begin
            Lemma_Key_Slice (B1, P1, I, D);
            Lemma_Key_Slice (B2, P2, I, D);
            Lemma_Key_Slice (B2, P2, X, D);
            if X /= I then
               --  Key X of map 2 = key I of map 1 = key I of map 2: two
               --  keys of one map.
               Lemma_CU (B1, Key_S (B1, P1, I, D),
                         B2, Key_S (B2, P2, X, D), D - 1);
               Lemma_Same_Bytes_Sym
                 (B1, Key_S (B1, P1, I, D), Key_E (B1, P1, I, D),
                  B2, Key_S (B2, P2, I, D), Key_E (B2, P2, I, D));
               Lemma_Same_Bytes_Trans
                 (B2, Key_S (B2, P2, I, D), Key_E (B2, P2, I, D),
                  B1, Key_S (B1, P1, I, D), Key_E (B1, P1, I, D),
                  B2, Key_S (B2, P2, X, D), Key_E (B2, P2, X, D));
               Lemma_Keys_Distinct (B2, P2, I, X, D);
               pragma Assert (False);
            end if;
            Lemma_CU (B1, Key_E (B1, P1, I, D),
                      B2, Key_E (B2, P2, I, D), D - 1);
         end;
         pragma Loop_Invariant
           (for all Y in 1 .. I =>
              Same_Bytes (B1, Key_E (B1, P1, Y, D), Val_E (B1, P1, Y, D),
                          B2, Key_E (B2, P2, Y, D), Val_E (B2, P2, Y, D)));
      end loop;
   end Lemma_Map_Values;

   procedure Lemma_Map_Concat
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
      N  : constant Natural  := Pairs (B1, P1);
      L  : constant Positive := Head_Len (B1 (P1));
      S1 : constant Positive := P1 + L;
      S2 : constant Positive := P2 + L;
   begin
      Lemma_Det_Container (B1, P1, D);
      Lemma_Det_Container (B2, P2, D);
      Lemma_Members_Start (B1, S1, D - 1);
      Lemma_Members_Start (B2, S2, D - 1);
      for I in 1 .. N loop
         Lemma_Key_Slice (B1, P1, I, D);
         Lemma_Key_Slice (B2, P2, I, D);
         Lemma_Same_Bytes_Join
           (B1, P1, Key_S (B1, P1, I, D), Key_E (B1, P1, I, D),
            B2, P2, Key_S (B2, P2, I, D), Key_E (B2, P2, I, D));
         Lemma_Same_Bytes_Join
           (B1, P1, Key_E (B1, P1, I, D), Val_E (B1, P1, I, D),
            B2, P2, Key_E (B2, P2, I, D), Val_E (B2, P2, I, D));
         pragma Loop_Invariant
           (Same_Bytes (B1, P1, Members_End (B1, S1, 2 * I, D - 1),
                        B2, P2, Members_End (B2, S2, 2 * I, D - 1)));
      end loop;
      pragma Assert (Members_End (B1, S1, 2 * N, D - 1) = Det_End (B1, P1, D));
      pragma Assert (Members_End (B2, S2, 2 * N, D - 1) = Det_End (B2, P2, D));
      Lemma_Same_Bytes_Len
        (B1, P1, Det_End (B1, P1, D), B2, P2, Det_End (B2, P2, D));
   end Lemma_Map_Concat;

   procedure Lemma_CU
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
      L  : constant Positive := Head_Len (B1 (P1));
      Q1 : constant Positive := Det_End (B1, P1, D);
      Q2 : constant Positive := Det_End (B2, P2, D);
   begin
      Lemma_Same_Open (B1, P1, B2, P2, D);
      --  The same major type and argument: for a simple value the same
      --  initial byte, for a string or a container the same count.
      if Major_Of (B1 (P1)) = 7 then
         pragma Assert (B2 (P2) = B1 (P1));
         Lemma_Head_Same (B1, P1, B2, P2);
      elsif Major_Of (B1 (P1)) in 2 .. 5 then
         pragma Assert (Arg (B1, P1) = Arg (B2, P2));
      end if;
      Lemma_Head_Unique (B1, P1, B2, P2);
      pragma Assert (Head_Len (B2 (P2)) = L);
      pragma Assert (Same_Bytes (B1, P1, P1 + L, B2, P2, P2 + L));
      if Major_Of (B1 (P1)) in 0 | 1 | 7 then
         pragma Assert (Q1 = P1 + L and then Q2 = P2 + L);
      elsif Major_Of (B1 (P1)) in 2 | 3 then
         pragma Assert (Q1 = P1 + L + Arg_Nat (B1, P1));
         pragma Assert (Q2 = P2 + L + Arg_Nat (B2, P2));
         pragma Assert (Same_Bytes (B1, P1 + L, Q1, B2, P2 + L, Q2));
         Lemma_Same_Bytes_Join (B1, P1, P1 + L, Q1, B2, P2, P2 + L, Q2);
      elsif Major_Of (B1 (P1)) = 4 then
         declare
            N  : constant Natural  := Arg_Nat (B1, P1);
            S1 : constant Positive := P1 + L;
            S2 : constant Positive := P2 + L;
         begin
            Lemma_Det_Container (B1, P1, D);
            Lemma_Det_Container (B2, P2, D);
            Lemma_Members_Start (B1, S1, D - 1);
            Lemma_Members_Start (B2, S2, D - 1);
            for I in 1 .. N loop
               declare
                  C1 : constant Positive := Child (B1, P1, I, D);
                  C2 : constant Positive := Child (B2, P2, I, D);
               begin
                  Lemma_Child_At (B1, P1, I, D);
                  Lemma_Child_At (B2, P2, I, D);
                  Lemma_CU (B1, C1, B2, C2, D - 1);
                  Lemma_Same_Bytes_Join
                    (B1, P1, C1, Det_End (B1, C1, D - 1),
                     B2, P2, C2, Det_End (B2, C2, D - 1));
               end;
               pragma Loop_Invariant
                 (Same_Bytes (B1, P1, Members_End (B1, S1, I, D - 1),
                              B2, P2, Members_End (B2, S2, I, D - 1)));
            end loop;
            pragma Assert (Members_End (B1, S1, N, D - 1) = Q1);
            pragma Assert (Members_End (B2, S2, N, D - 1) = Q2);
            Lemma_Same_Bytes_Len (B1, P1, Q1, B2, P2, Q2);
         end;
      else
         pragma Assert (Major_Of (B1 (P1)) = 5);
         Lemma_Map_Match (B1, P1, B2, P2, D);
         Lemma_Map_Keys (B1, P1, B2, P2, D);
         Lemma_Map_Values (B1, P1, B2, P2, D);
         Lemma_Map_Concat (B1, P1, B2, P2, D);
      end if;
   end Lemma_CU;

   procedure Lemma_CU_Whole (B1 : Bytes; B2 : Bytes) is
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
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Same_Bytes);
   begin
      Lemma_CU (B1, B1'First, B2, B2'First, Max_Depth);
      pragma Assert (Det_End (B1, B1'First, Max_Depth) = B1'Last + 1);
      pragma Assert (Det_End (B2, B2'First, Max_Depth) = B2'Last + 1);
   end Lemma_CU_Whole;

   procedure Lemma_Head_Rebased
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
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Same_Bytes);
   begin
      pragma Assert
        (E2 - P2 = E1 - P1
         and then (for all K in 0 .. Head_Len (B1 (P1)) - 1 =>
                     B2 (P2 + K) = B1 (P1 + K)));
      Lemma_Head_Same (B1, P1, B2, P2);
   end Lemma_Head_Rebased;

   procedure Lemma_Members_Rebased
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
      E1 : constant Positive := Det_End (B1, P1, D);
      E2 : constant Positive := Det_End (B2, P2, D);
      L  : constant Positive := Head_Len (B1 (P1));
      NM : constant Natural  := Member_Count (B1, P1);
   begin
      Lemma_Det_Container (B1, P1, D);
      Lemma_Head_Rebased (B1, P1, E1, B2, P2, E2);
      Lemma_Arg_Same (B1, P1, B2, P2);
      pragma Assert (Members_End (B1, P1 + L, NM, D - 1) = E1);
      Lemma_Same_Bytes_Sub (B1, P1, E1, B2, P2, E2, P1 + L, E1);
      pragma Assert (P1 + L - P1 + P2 = P2 + L);
      pragma Assert (E1 - P1 + P2 = E2);
      Lemma_Members_Transport (B1, P1 + L, B2, P2 + L, NM, D - 1);
   end Lemma_Members_Rebased;

   procedure Lemma_Child_Same_Of_Bytes
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
      E1 : constant Positive := Det_End (B1, P1, D);
      E2 : constant Positive := Det_End (B2, P2, D);
   begin
      Lemma_Members_Rebased (B1, P1, B2, P2, D);
      Lemma_Child_At (B1, P1, I, D);
      Lemma_Child_At (B2, P2, I, D);
      declare
         C1 : constant Positive := Child (B1, P1, I, D);
         C2 : constant Positive := Child (B2, P2, I, D);
         F1 : constant Positive := Det_End (B1, C1, D - 1);
         F2 : constant Positive := Det_End (B2, C2, D - 1);
      begin
         pragma Assert (C2 = C1 - P1 + P2);
         pragma Assert (F2 = F1 - P1 + P2);
         Lemma_Same_Bytes_Sub (B1, P1, E1, B2, P2, E2, C1, F1);
         Lemma_Same_Of_Bytes (B1, C1, B2, C2, D - 1);
      end;
   end Lemma_Child_Same_Of_Bytes;

   procedure Lemma_Array_Same_Of_Bytes
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
      N : constant Natural := Arg_Nat (B1, P1);
   begin
      Lemma_Members_Rebased (B1, P1, B2, P2, D);
      for I in 1 .. N loop
         Lemma_Child_Same_Of_Bytes (B1, P1, B2, P2, D, I);
         pragma Loop_Invariant
           (for all Y in 1 .. I =>
              Same (B1, Child (B1, P1, Y, D),
                    B2, Child (B2, P2, Y, D), D - 1));
      end loop;
   end Lemma_Array_Same_Of_Bytes;

   procedure Lemma_Pair_Same_Of_Bytes
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
      E1 : constant Positive := Det_End (B1, P1, D);
      E2 : constant Positive := Det_End (B2, P2, D);
   begin
      Lemma_Members_Rebased (B1, P1, B2, P2, D);
      pragma Assert (Is_Map (B2, P2, D));
      Lemma_Key_Slice (B1, P1, I, D);
      Lemma_Key_Slice (B2, P2, I, D);
      declare
         KS1 : constant Positive := Key_S (B1, P1, I, D);
         KE1 : constant Positive := Key_E (B1, P1, I, D);
         VE1 : constant Positive := Val_E (B1, P1, I, D);
         KS2 : constant Positive := Key_S (B2, P2, I, D);
         KE2 : constant Positive := Key_E (B2, P2, I, D);
         VE2 : constant Positive := Val_E (B2, P2, I, D);
      begin
         pragma Assert (KS2 = KS1 - P1 + P2);
         pragma Assert (KE2 = KE1 - P1 + P2);
         pragma Assert (VE2 = VE1 - P1 + P2);
         Lemma_Same_Bytes_Sub (B1, P1, E1, B2, P2, E2, KS1, KE1);
         Lemma_Same_Of_Bytes (B1, KS1, B2, KS2, D - 1);
         Lemma_Same_Bytes_Sub (B1, P1, E1, B2, P2, E2, KE1, VE1);
         Lemma_Same_Of_Bytes (B1, KE1, B2, KE2, D - 1);
      end;
   end Lemma_Pair_Same_Of_Bytes;

   procedure Lemma_Map_Same_Of_Bytes
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
      N : constant Natural := Pairs (B1, P1);
   begin
      Lemma_Members_Rebased (B1, P1, B2, P2, D);
      for I in 1 .. N loop
         Lemma_Pair_Same_Of_Bytes (B1, P1, B2, P2, D, I);
         pragma Loop_Invariant
           (for all Y in 1 .. I =>
              Same (B1, Key_S (B1, P1, Y, D),
                    B2, Key_S (B2, P2, Y, D), D - 1)
              and then Same (B1, Key_E (B1, P1, Y, D),
                             B2, Key_E (B2, P2, Y, D), D - 1));
      end loop;
   end Lemma_Map_Same_Of_Bytes;

   procedure Lemma_Same_Of_Bytes
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
      E1 : constant Positive := Det_End (B1, P1, D);
      E2 : constant Positive := Det_End (B2, P2, D);
      L  : constant Positive := Head_Len (B1 (P1));
   begin
      --  A container ends no earlier than its head.
      if Major_Of (B1 (P1)) in 4 | 5 then
         Lemma_Det_Container (B1, P1, D);
      end if;
      Lemma_Head_Rebased (B1, P1, E1, B2, P2, E2);
      if Major_Of (B1 (P1)) in 2 | 3 then
         Lemma_Arg_Same (B1, P1, B2, P2);
         Lemma_Same_Bytes_Sub (B1, P1, E1, B2, P2, E2, P1 + L, E1);
         pragma Assert (P1 + L - P1 + P2 = P2 + L);
         pragma Assert (E1 - P1 + P2 = E2);
      elsif Major_Of (B1 (P1)) = 4 then
         Lemma_Array_Same_Of_Bytes (B1, P1, B2, P2, D);
      elsif Major_Of (B1 (P1)) = 5 then
         Lemma_Map_Same_Of_Bytes (B1, P1, B2, P2, D);
         Lemma_Same_Map_In_Order (B1, P1, B2, P2, D);
      end if;
      Lemma_Same_Close (B1, P1, B2, P2, D);
   end Lemma_Same_Of_Bytes;

   procedure Lemma_Same_Of_Bytes_Whole (B1 : Bytes; B2 : Bytes) is
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
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Same_Bytes);
   begin
      pragma Assert (Det_End (B1, B1'First, Max_Depth) = B1'Last + 1);
      pragma Assert (Det_End (B2, B2'First, Max_Depth) = B2'Last + 1);
      pragma Assert (for all Y in B2'Range =>
                       B2 (Y) = B1 (Y - B2'First + B1'First));
      pragma Assert (Same_Bytes (B1, B1'First, B1'Last + 1,
                                 B2, B2'First, B2'Last + 1));
      Lemma_Same_Of_Bytes (B1, B1'First, B2, B2'First, Max_Depth);
   end Lemma_Same_Of_Bytes_Whole;

   procedure Lemma_Same_Iff_Bytes_Whole (B1 : Bytes; B2 : Bytes) is
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
      if Same (B1, B1'First, B2, B2'First, Max_Depth) then
         Lemma_CU_Whole (B1, B2);
      elsif B1'Length = B2'Length
        and then (for all K in B1'Range =>
                    B1 (K) = B2 (K - B1'First + B2'First))
      then
         Lemma_Same_Of_Bytes_Whole (B1, B2);
      end if;
   end Lemma_Same_Iff_Bytes_Whole;

end Cbor_Det.Proof.Unique;
