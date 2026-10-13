--  Deterministic CBOR: proof clients of the exported lemmas.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause

with Cbor_Det.Proof.Transport; use Cbor_Det.Proof.Transport;

package body Cbor_Det.Proof.Surface with SPARK_Mode is

   --  Every client hides the recursive definitions (Det_End, Members_End,
   --  Keys_Ascending, Lex_Less): their Hide_Info, which follows a
   --  completion in Cbor_Det.Proof.Det, hides them only within that unit.
   --  Same_Bytes, Arg and Shortest are hidden everywhere already. So each
   --  client proves from the lemmas' contracts alone. Only
   --  Client_Head_Unique_Bytes and Client_Head_Canonical_Bytes open
   --  Same_Bytes, to state their guarantees byte by byte.

   procedure Client_Head_Unique_Bytes
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; K : Natural)
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
        (GNATprove, Unhide_Info, "Expression_Function_Body", Same_Bytes);
   begin
      Lemma_Head_Unique (B1, P1, B2, P2);
      pragma Assert (P1 + K in P1 .. P1 + Head_Len (B1 (P1)) - 1);
   end Client_Head_Unique_Bytes;

   procedure Client_Encoded_Integer
     (B : Bytes; P : Positive; M : Major; A : U64; D : Natural)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
   begin
      Lemma_Head_Encoded (B, P, M, A);
      Lemma_Det_Step (B, P, D);
   end Client_Encoded_Integer;

   procedure Client_Map_Keys_Ordered (B : Bytes; P : Positive; D : Natural)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
   begin
      Lemma_Det_Container (B, P, D);
      Lemma_Keys_All (B, P + Head_Len (B (P)), Arg_Nat (B, P), D - 1);
   end Client_Map_Keys_Ordered;

   procedure Client_Map_Members (B : Bytes; P : Positive; D : Natural) is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
   begin
      Lemma_Det_Container (B, P, D);
   end Client_Map_Members;

   procedure Client_Array_Members (B : Bytes; P : Positive; D : Natural) is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
   begin
      Lemma_Det_Container (B, P, D);
      Lemma_Members_Monotone
        (B, P + Head_Len (B (P)), Arg_Nat (B, P), D - 1);
      pragma Assert
        (for all J in 1 .. Arg_Nat (B, P) =>
           Members_End (B, P + Head_Len (B (P)), J - 1, D - 1)
           < Members_End (B, P + Head_Len (B (P)), J, D - 1)
           and then Members_End (B, P + Head_Len (B (P)), J, D - 1)
                    <= B'Last + 1);
   end Client_Array_Members;

   procedure Client_Array_Member_Fails
     (B : Bytes; P : Positive; D : Natural; I : Natural)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
   begin
      Lemma_Members_Zero
        (B, P + Head_Len (B (P)), I, Arg_Nat (B, P), D - 1);
      Lemma_Det_Step (B, P, D);
   end Client_Array_Member_Fails;

   procedure Client_Map_Unsorted
     (B : Bytes; P : Positive; D : Natural; J : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
   begin
      Lemma_Keys_Break
        (B, P + Head_Len (B (P)), Arg_Nat (B, P), J, D - 1);
      Lemma_Det_Step (B, P, D);
   end Client_Map_Unsorted;

   procedure Client_Member_Takes_A_Byte
     (B : Bytes; Q : Positive; K : Positive; D : Natural)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
   begin
      Lemma_Members_Last (B, Q, K, D);
   end Client_Member_Takes_A_Byte;

   procedure Client_Run_Prefix
     (B : Bytes; Q : Positive; I : Natural; K : Natural; D : Natural)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
   begin
      Lemma_Members_Prefix (B, Q, I, K, D);
   end Client_Run_Prefix;

   procedure Client_Run_Bounds
     (B : Bytes; Q : Positive; K : Natural; D : Natural)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
   begin
      Lemma_Members_Monotone (B, Q, K, D);
   end Client_Run_Bounds;

   procedure Client_Lex_Irreflexive (B : Bytes; P : Natural; E : Natural) is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
   begin
      Lemma_Lex_Step (B, P, E, B, P, E);
      if P < E then
         Client_Lex_Irreflexive (B, P + 1, E);
      end if;
   end Client_Lex_Irreflexive;

   procedure Client_Lex_First_Byte
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
   begin
      Lemma_Lex_Step (B1, P1, E1, B2, P2, E2);
   end Client_Lex_First_Byte;

   procedure Client_Lex_Not_A_Slice
     (B : Bytes; P : Natural; E : Natural; Q : Natural; F : Natural)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
   begin
      Lemma_Lex_Not_Slice (B, P, E, B, Q, F);
      Lemma_Lex_Not_Slice (B, Q, F, B, P, E);
   end Client_Lex_Not_A_Slice;

   procedure Client_Same_Bytes_Copies
     (B1 : Bytes; P1 : Natural; E1 : Natural;
      B2 : Bytes; P2 : Natural; E2 : Natural;
      B3 : Bytes; P3 : Natural; E3 : Natural)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
   begin
      Lemma_Same_Bytes_Sym (B3, P3, E3, B2, P2, E2);
      Lemma_Same_Bytes_Trans (B1, P1, E1, B2, P2, E2, B3, P3, E3);
      Lemma_Same_Bytes_Sym (B1, P1, E1, B3, P3, E3);
      Lemma_Same_Bytes_Len (B1, P1, E1, B3, P3, E3);
   end Client_Same_Bytes_Copies;

   procedure Client_Same_Bytes_Whole
     (B1 : Bytes; P1 : Natural; M1 : Natural; E1 : Natural;
      B2 : Bytes; P2 : Natural; M2 : Natural; E2 : Natural)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
   begin
      Lemma_Same_Bytes_Refl (B1, P1, E1);
      Lemma_Same_Bytes_Join (B1, P1, M1, E1, B2, P2, M2, E2);
   end Client_Same_Bytes_Whole;

   procedure Client_Prefix_Free_Equal_Length
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
   begin
      if Det_End (B2, P2, D) - P2 > Det_End (B1, P1, D) - P1 then
         Lemma_Prefix_Free (B1, P1, B2, P2, D);
      end if;
   end Client_Prefix_Free_Equal_Length;

   procedure Client_Head_Canonical_Bytes (B : Bytes; P : Positive; K : Natural)
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
        (GNATprove, Unhide_Info, "Expression_Function_Body", Same_Bytes);
   begin
      Lemma_Head_Canonical (B, P);
      pragma Assert (K < Head_Len (B (P)));
   end Client_Head_Canonical_Bytes;

   procedure Client_Head_Copy
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
   begin
      Lemma_Head_Same (B1, P1, B2, P2);
   end Client_Head_Copy;

   procedure Client_Encode_Integer (M : Major; A : U64; D : Natural) is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
   begin
      Lemma_Det_Step (Encode_Head (M, A), 1, D);
   end Client_Encode_Integer;

   procedure Client_Arg_Counts
     (B1 : Bytes; P1 : Positive; B2 : Bytes; P2 : Positive; N : Natural)
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
        (GNATprove, Hide_Info, "Expression_Function_Body", Arg_Small);
   begin
      Lemma_Arg_Is (B1, P1, N);
      Lemma_Arg_Same (B1, P1, B2, P2);
   end Client_Arg_Counts;

   procedure Client_Arg_Small (B : Bytes; P : Positive) is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Arg_Small);
   begin
      Lemma_Arg_Small_Of (B, P);
   end Client_Arg_Small;

   procedure Client_Accepted_Item (B : Bytes; P : Positive; D : Natural) is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
   begin
      null;
   end Client_Accepted_Item;

   procedure Client_Run_Steps
     (B : Bytes; Q : Positive; K : Positive; D : Natural)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
   begin
      Lemma_Members_Start (B, Q, D);
      Lemma_Members_Step (B, Q, K, D);
   end Client_Run_Steps;

   procedure Client_Keys_One_At_A_Time
     (B : Bytes; Q : Positive; N : Positive; M : Natural; D : Natural)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
   begin
      Lemma_Keys_Step (B, Q, N, D);
      if Keys_Ascending (B, Q, N, D) then
         Lemma_Keys_Prefix (B, Q, N, M, D);
      end if;
      if Keys_Ascending (B, Q, N - 1, D)
        and then Lex_Less (B, Members_End (B, Q, 2 * N - 4, D),
                              Members_End (B, Q, 2 * N - 3, D),
                           B, Members_End (B, Q, 2 * N - 2, D),
                              Members_End (B, Q, 2 * N - 1, D))
      then
         Lemma_Keys_Extend (B, Q, N, D);
      end if;
   end Client_Keys_One_At_A_Time;

   procedure Client_Keys_Extend
     (B : Bytes; Q : Positive; N : Positive; D : Natural)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
   begin
      Lemma_Keys_Extend (B, Q, N, D);
   end Client_Keys_Extend;

   procedure Client_Lex_Copies
     (A1 : Bytes; P1 : Natural; E1 : Natural;
      A2 : Bytes; P2 : Natural; E2 : Natural;
      C1 : Bytes; R1 : Natural; F1 : Natural;
      C2 : Bytes; R2 : Natural; F2 : Natural)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
   begin
      Lemma_Lex_Less_Same (A1, P1, E1, A2, P2, E2, C1, R1, F1, C2, R2, F2);
   end Client_Lex_Copies;

   procedure Client_Item_Copy
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
   begin
      Lemma_Transport (B1, P1, B2, P2, D);
   end Client_Item_Copy;

   procedure Client_Run_Copy
     (B1 : Bytes; Q1 : Positive; B2 : Bytes; Q2 : Positive;
      K : Natural; J : Natural; D : Natural)
   is
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Det_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Members_End);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Keys_Ascending);
      pragma Annotate
        (GNATprove, Hide_Info, "Expression_Function_Body", Lex_Less);
   begin
      Lemma_Members_Transport (B1, Q1, B2, Q2, K, D);
      pragma Assert (J <= K);
   end Client_Run_Copy;

end Cbor_Det.Proof.Surface;
