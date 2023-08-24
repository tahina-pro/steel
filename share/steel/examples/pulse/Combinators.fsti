module Combinators
open Pulse.Lib.Pervasives
module R = Pulse.Lib.Reference
module U32 = FStar.UInt32

inline_for_extraction
unfold
noextract
let validator = (r: ref U32.t) -> (#contents: Ghost.erased U32.t) -> stt bool (R.pts_to r contents) (fun _ -> R.pts_to r contents)

inline_for_extraction
noextract
let validate
  (v: validator)
  (r: ref U32.t)
  (#contents: Ghost.erased U32.t)
: stt bool
  (R.pts_to r contents)
  (fun _ -> R.pts_to r contents)
= v r #contents

inline_for_extraction
noextract
val validate_filter
  (v: validator)
  (cond: (U32.t -> bool))
: Tot validator

inline_for_extraction
noextract
val validate_always
: validator

let test = validate_filter validate_always (fun x -> x `U32.lt` 256ul)
