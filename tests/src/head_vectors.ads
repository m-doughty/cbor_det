--  cbor_det tests: the head helpers, which are ordinary functions and run
--  in every cell of the build matrix.
--
--  Copyright (c) 2026, Matt Doughty
--  SPDX-License-Identifier: BSD-3-Clause

package Head_Vectors is

   --  Every head form of every major type at the argument boundaries (0,
   --  1, 23/24, 255/256, 65535/65536, 2**32 - 1/2**32, 2**64 - 1): the
   --  shortest form's bytes from Encode_Head, its length and argument;
   --  every wider form (accepted as well formed, refused as not
   --  shortest); every truncation; and additional information 28 to 31.
   --  Each case is checked at index 1 and again with its last byte at
   --  Index'Last.
   procedure Run;

end Head_Vectors;
