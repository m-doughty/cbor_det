--  cbor_det tests: a first run of the decoder (smoke vectors).
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause
--
--  Check on a handful of inputs, accepted and refused, at index 1, at a
--  shifted first index and ending at Index'Last, and on null arrays with
--  any bounds: its Result and Where against the expected ones. In the
--  contracts cell this unit is compiled with assertions on, so it also
--  asserts that Result is Ok exactly when Accepts holds (Check's own
--  postcondition is checked there too) and reads the operation counters.

package Decoder_Vectors is

   procedure Run;

   --  Whether the assertions of this unit, which call ghost code, ran.
   function Ran return Boolean;

end Decoder_Vectors;
