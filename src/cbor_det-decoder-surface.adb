--  Deterministic CBOR: proof clients of the decoder's contract.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause

package body Cbor_Det.Decoder.Surface with SPARK_Mode is

   procedure Client_Ok_Accepted
     (Data : Bytes; Result : out Status; Where : out Integer) is
   begin
      Check (Data, Result, Where);
   end Client_Ok_Accepted;

   procedure Client_Accepted_Ok
     (Data : Bytes; Result : out Status; Where : out Integer) is
   begin
      Check (Data, Result, Where);
   end Client_Accepted_Ok;

   procedure Client_Rejected_Not_Accepted
     (Data : Bytes; Result : out Status; Where : out Integer) is
   begin
      Check (Data, Result, Where);
   end Client_Rejected_Not_Accepted;

   procedure Client_Empty
     (Data : Bytes; Result : out Status; Where : out Integer) is
   begin
      Check (Data, Result, Where);
   end Client_Empty;

   procedure Client_Rejected_In_Range
     (Data : Bytes; Result : out Status; Where : out Integer) is
   begin
      Check (Data, Result, Where);
   end Client_Rejected_In_Range;

end Cbor_Det.Decoder.Surface;
