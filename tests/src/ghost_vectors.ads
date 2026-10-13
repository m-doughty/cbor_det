--  cbor_det tests: vectors for the ghost predicate Det_End, the whole-input
--  wrapper Accept_Whole and the lemmas, run as executable checks.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause
--
--  These checks call the library's ghost code, so they run only in the
--  build-matrix cell where the library is compiled with assertions on
--  (the contracts cell). In every other cell this unit is compiled with
--  assertions off, its checks are ignored, and Ran is False.

with Cbor_Det; use Cbor_Det;

package Ghost_Vectors is

   --  RFC 8949 Appendix A, every example (accepted when in the profile,
   --  refused otherwise); a refusal for each rule; the mandatory
   --  witnesses; item ends with unrelated bytes after the item; the
   --  depth bound; the whole-input wrapper on its own; and the cases only
   --  Ada can build: null arrays with any bounds, buffers ending at
   --  Index'Last, copies elsewhere (transport), oversized lengths and
   --  counts, map counts around 2**30 - 1. On every accepted vector the
   --  lemmas are called, so their preconditions and postconditions are
   --  checked on it.
   procedure Run;

   --  The lemmas, called on an item that B (from index 1) holds whole at
   --  Max_Depth, so that their contracts are checked on it; and the
   --  prefix-freedom check that no proper prefix of B holds an item.
   procedure Lemmas (Name : String; B : Bytes);

   --  Whether the checks of this unit executed.
   function Ran return Boolean;

end Ghost_Vectors;
