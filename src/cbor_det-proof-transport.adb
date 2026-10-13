--  Deterministic CBOR: transport and prefix-freedom.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause

with Cbor_Det.Proof.Heads; use Cbor_Det.Proof.Heads;

package body Cbor_Det.Proof.Transport with SPARK_Mode is

   procedure Lemma_Lex_Less_Same
     (A1 : Bytes; P1 : Natural; E1 : Natural;
      A2 : Bytes; P2 : Natural; E2 : Natural;
      C1 : Bytes; R1 : Natural; F1 : Natural;
      C2 : Bytes; R2 : Natural; F2 : Natural)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Same_Bytes);
   begin
      if P1 = E1 or else P2 = E2 or else A1 (P1) /= A2 (P2) then
         null;
      else
         Lemma_Lex_Less_Same (A1, P1 + 1, E1, A2, P2 + 1, E2,
                              C1, R1 + 1, F1, C2, R2 + 1, F2);
      end if;
   end Lemma_Lex_Less_Same;

   procedure Lemma_Keys_Transport
     (B1 : Bytes; Q1 : Positive; B2 : Bytes; Q2 : Positive;
      N : Natural; K : Natural; D : Natural)
   is
      E1 : constant Positive := Members_End (B1, Q1, K, D);
      E2 : constant Positive := Q2 + (E1 - Q1);
   begin
      Lemma_Keys_Step (B2, Q2, 1, D);
      for J in 2 .. N loop
         declare
            A1 : constant Positive := Members_End (B1, Q1, 2 * J - 4, D);
            A2 : constant Positive := Members_End (B1, Q1, 2 * J - 3, D);
            A3 : constant Positive := Members_End (B1, Q1, 2 * J - 2, D);
            A4 : constant Positive := Members_End (B1, Q1, 2 * J - 1, D);
         begin
            Lemma_Keys_Prefix (B1, Q1, N, J, D);
            Lemma_Keys_Step (B1, Q1, J, D);
            pragma Assert (Lex_Less (B1, A1, A2, B1, A3, A4));
            Lemma_Same_Bytes_Sub (B1, Q1, E1, B2, Q2, E2, A1, A2);
            Lemma_Same_Bytes_Sub (B1, Q1, E1, B2, Q2, E2, A3, A4);
            Lemma_Lex_Less_Same (B1, A1, A2, B1, A3, A4,
                                 B2, A1 - Q1 + Q2, A2 - Q1 + Q2,
                                 B2, A3 - Q1 + Q2, A4 - Q1 + Q2);
            pragma Assert (Lex_Less (B2, Members_End (B2, Q2, 2 * J - 4, D),
                                         Members_End (B2, Q2, 2 * J - 3, D),
                                     B2, Members_End (B2, Q2, 2 * J - 2, D),
                                         Members_End (B2, Q2, 2 * J - 1, D)));
            Lemma_Keys_Extend (B2, Q2, J, D);
            pragma Assert (Keys_Ascending (B2, Q2, J, D));
         end;
         pragma Loop_Invariant (Keys_Ascending (B2, Q2, J, D));
      end loop;
   end Lemma_Keys_Transport;

   procedure Lemma_Members_Transport
     (B1 : Bytes; Q1 : Positive; B2 : Bytes; Q2 : Positive;
      K : Natural; D : Natural)
   is
      pragma Annotate
        (GNATprove, Unhide_Info, "Expression_Function_Body", Same_Bytes);
   begin
      if K = 0 then
         return;
      end if;
      Lemma_Members_Monotone (B1, Q1, K, D);
      declare
         S1 : constant Positive := Members_End (B1, Q1, K - 1, D);
         E1 : constant Positive := Members_End (B1, Q1, K, D);
         S2 : constant Positive := Q2 + (S1 - Q1);
         E2 : constant Positive := Q2 + (E1 - Q1);
      begin
         --  The first K - 1 members, by the induction hypothesis on K.
         Lemma_Members_Transport (B1, Q1, B2, Q2, K - 1, D);
         pragma Assert (Members_End (B2, Q2, K - 1, D) = S2);
         pragma Assert (S1 <= B1'Last and then S2 <= B2'Last);
         pragma Assert (Det_End (B1, S1, D) = E1);
         Lemma_Det_Step (B1, S1, D);
         Lemma_Det_Step (B2, S2, D);
         Lemma_Members_Step (B2, Q2, K, D);
         --  Member K: the same head at S1 and at S2.
         declare
            L : constant Positive := Head_Len (B1 (S1));
         begin
            pragma Assert (for all X in S1 .. E1 - 1 =>
                             B2 (X - S1 + S2) = B1 (X));
            pragma Assert (for all Y in S2 .. E2 - 1 =>
                             B2 (Y) = B1 (Y - S2 + S1));
            pragma Assert (E1 >= S1 + L);
            pragma Assert (for all X in 0 .. L - 1 =>
                             B2 (S2 + X) = B1 (S1 + X));
            Lemma_Head_Same (B1, S1, B2, S2);
            Lemma_Arg_Same (B1, S1, B2, S2);
            pragma Assert (Head_OK (B2, S2));
            pragma Assert (Head_Len (B2 (S2)) = L);
            pragma Assert (Major_Of (B2 (S2)) = Major_Of (B1 (S1)));
            case Major_Of (B1 (S1)) is
               when 0 | 1 =>
                  pragma Assert (Det_End (B2, S2, D) = S2 + L);
               when 2 | 3 =>
                  pragma Assert (Arg_Fits (B2, S2, Remaining (B2, S2) - L));
                  pragma Assert
                    (Det_End (B2, S2, D) = S2 + L + Arg_Nat (B2, S2));
               when 4 =>
                  declare
                     N : constant Natural := Arg_Nat (B1, S1);
                  begin
                     Lemma_Det_Container (B1, S1, D);
                     pragma Assert (Members_End (B1, S1 + L, N, D - 1) = E1);
                     pragma Assert
                       (Same_Bytes (B1, S1 + L, E1, B2, S2 + L, E2));
                     Lemma_Members_Transport
                       (B1, S1 + L, B2, S2 + L, N, D - 1);
                     pragma Assert (Members_End (B2, S2 + L, N, D - 1) = E2);
                     Lemma_Members_Monotone (B2, S2 + L, N, D - 1);
                     pragma Assert (E2 >= S2 + L + N);
                     pragma Assert (Arg_Nat (B2, S2) = N);
                     pragma Assert
                       (Arg_Fits (B2, S2, Remaining (B2, S2) - L));
                     pragma Assert (Det_End (B2, S2, D) = E2);
                  end;
               when 5 =>
                  declare
                     N : constant Natural := Arg_Nat (B1, S1);
                  begin
                     Lemma_Det_Container (B1, S1, D);
                     pragma Assert
                       (Members_End (B1, S1 + L, 2 * N, D - 1) = E1);
                     pragma Assert (Keys_Ascending (B1, S1 + L, N, D - 1));
                     pragma Assert
                       (Same_Bytes (B1, S1 + L, E1, B2, S2 + L, E2));
                     Lemma_Members_Transport
                       (B1, S1 + L, B2, S2 + L, 2 * N, D - 1);
                     pragma Assert
                       (Members_End (B2, S2 + L, 2 * N, D - 1) = E2);
                     Lemma_Members_Monotone (B1, S1 + L, 2 * N, D - 1);
                     Lemma_Members_Monotone (B2, S2 + L, 2 * N, D - 1);
                     pragma Assert (E2 >= S2 + L + 2 * N);
                     pragma Assert (Arg_Nat (B2, S2) = N);
                     pragma Assert
                       (Arg_Fits (B2, S2, (Remaining (B2, S2) - L) / 2));
                     --  The keys sit at corresponding places, so their
                     --  order carries.
                     Lemma_Keys_Transport
                       (B1, S1 + L, B2, S2 + L, N, 2 * N, D - 1);
                     pragma Assert (Keys_Ascending (B2, S2 + L, N, D - 1));
                     pragma Assert (Det_End (B2, S2, D) = E2);
                  end;
               when 7 =>
                  pragma Assert (Info_Of (B2 (S2)) = Info_Of (B1 (S1)));
                  pragma Assert (Det_End (B2, S2, D) = S2 + L);
               when others =>
                  pragma Assert (False);
            end case;
            pragma Assert (Det_End (B2, S2, D) = E2);
            pragma Assert (Members_End (B2, Q2, K, D) = E2);
         end;
      end;
   end Lemma_Members_Transport;

   procedure Lemma_Transport
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Natural)
   is
   begin
      Lemma_Members_Start (B1, P1, D);
      Lemma_Members_Step (B1, P1, 1, D);
      Lemma_Members_Start (B2, P2, D);
      Lemma_Members_Step (B2, P2, 1, D);
      Lemma_Members_Transport (B1, P1, B2, P2, 1, D);
   end Lemma_Transport;

   procedure Lemma_Prefix_Free
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; D : Natural)
   is
   begin
      Lemma_Transport (B1, P1, B2, P2, D);
   end Lemma_Prefix_Free;

end Cbor_Det.Proof.Transport;
