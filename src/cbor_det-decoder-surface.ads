--  Deterministic CBOR: proof clients of the decoder's contract.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause
--
--  Each procedure here calls Check and proves, from Check's contract
--  alone, one clause of it, stated on its own: so if Check's
--  postcondition said less, a client here would no longer prove. The
--  clients pin the contract a caller of Check relies on, as the clients
--  in Cbor_Det.Proof.Surface pin the lemmas of the proof core.
--
--  Nothing here runs: the package is ghost.

package Cbor_Det.Decoder.Surface with SPARK_Mode, Ghost is

   --  Ok means Data is accepted, and Where is one past its last byte.
   procedure Client_Ok_Accepted
     (Data : Bytes; Result : out Status; Where : out Integer)
   with Post => (if Result = Ok
                 then Accepts (Data) and then Where = Data'Last + 1);

   --  Accepted data gives Ok.
   procedure Client_Accepted_Ok
     (Data : Bytes; Result : out Status; Where : out Integer)
   with Post => (if Accepts (Data) then Result = Ok);

   --  A rejection means Data is not accepted.
   procedure Client_Rejected_Not_Accepted
     (Data : Bytes; Result : out Status; Where : out Integer)
   with Post => (if Result /= Ok then not Accepts (Data));

   --  An empty input is Truncated at its first index, whatever its bounds.
   procedure Client_Empty
     (Data : Bytes; Result : out Status; Where : out Integer)
   with Post => (if Result /= Ok and then Data'Length = 0
                 then Result = Truncated and then Where = Data'First);

   --  A rejection of a non-empty input is at an index of it.
   procedure Client_Rejected_In_Range
     (Data : Bytes; Result : out Status; Where : out Integer)
   with Post => (if Result /= Ok and then Data'Length > 0
                 then Where in Data'Range);

end Cbor_Det.Decoder.Surface;
