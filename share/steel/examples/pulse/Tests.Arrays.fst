module Tests.Arrays
module T = FStar.Tactics
open Pulse.Syntax
open Pulse.Main
open Steel.ST.Util 
open Steel.ST.Reference
open Steel.FractionalPermission
open FStar.Ghost

module U32 = FStar.UInt32

open Pulse.Steel.Wrapper
include Tests.Common

module US = FStar.SizeT
module A = Steel.ST.Array

let byte = FStar.UInt8.t
let bytes = Ghost.erased (Seq.seq byte)
let byte_array = A.array byte
let byte_array_pts_to
  (a: byte_array)
  (p: perm)
  (s: bytes)
: Tot vprop
= A.pts_to a p s

let true_prop : prop = True
let sz_gt (a b: US.t) : Tot bool = a `US.gt` b
let sz_zero : US.t = 0sz

(*
%splice_t[lex_check_FAIL_1] (check (`(
  fun (#pa: perm) (#sa: bytes) (a: byte_array) (la: US.t)
    (#pb: perm) (#sb: bytes) (b: byte_array) (lb: US.t)
    ->
    (expects (byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * pure ((US.v la `eq2_prop` A.length a) `and_prop` (US.v lb `eq2_prop` A.length b))))
    (provides (fun (res: bool) -> byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * pure (true_prop)))
    (
      if la = sz_zero
      then begin
        return (US.gt lb sz_zero)
      end else if lb = sz_zero
      then return false
      else
        return false
    )
  )))
*) // FAIL: inexpressible term, presumably because FStar.SizeT.gt is in the Pure effect, not Tot

%splice_t[lex_check_success_2] (check (`(
  fun (#pa: perm) (#sa: bytes) (a: byte_array) (la: US.t)
    (#pb: perm) (#sb: bytes) (b: byte_array) (lb: US.t)
    ->
    (expects (byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * pure ((US.v la `eq2_prop` A.length a) `and_prop` (US.v lb `eq2_prop` A.length b))))
    (provides (fun (res: bool) -> byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * pure (true_prop)))
    (
      if la = sz_zero
      then begin
        return (sz_gt lb sz_zero)
      end else if lb = sz_zero
      then return false
      else
        return false
    )
  )))

(*
%splice_t[lex_check_FAIL_3] (check (`(
  fun (#pa: perm) (#sa: bytes) (a: byte_array) (la: US.t)
    (#pb: perm) (#sb: bytes) (b: byte_array) (lb: US.t)
    ->
    (expects (byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * pure ((US.v la `eq2_prop` A.length a) `and_prop` (US.v lb `eq2_prop` A.length b))))
    (provides (fun (res: bool) -> byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * pure (true_prop)))
    (
      if la = sz_zero
      then begin
        let res : bool = sz_gt lb sz_zero in
        return res
      end else if lb = sz_zero
      then return false
      else
        return false
    )
  )))
*) // FAIL: Unexpected c in infer_logical

(*
%splice_t[lex_check_FAIL_4] (check (`(
  fun (#pa: perm) (#sa: bytes) (a: byte_array) (la: US.t)
    (#pb: perm) (#sb: bytes) (b: byte_array) (lb: US.t)
    ->
    (expects (byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * pure ((US.v la `eq2_prop` A.length a) `and_prop` (US.v lb `eq2_prop` A.length b))))
    (provides (fun (res: bool) -> byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * pure (true_prop)))
    (
      if la = sz_zero
      then begin
        let res = local (sz_gt lb sz_zero) in
        return !res
      end else if lb = sz_zero
      then return false
      else
        return false
    )
  )))
*) // FAIL: Not typable as a universe

(*
%splice_t[lex_check_FAIL_5] (check (`(
  fun (#pa: perm) (#sa: bytes) (a: byte_array) (la: US.t)
    (#pb: perm) (#sb: bytes) (b: byte_array) (lb: US.t)
    (pres: ref bool)
    ->
    (expects (byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * (exists res. (pts_to pres full_perm res)) * pure ((US.v la `eq2_prop` A.length a) `and_prop` (US.v lb `eq2_prop` A.length b))))
    (provides (fun _ -> byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * (exists res . pts_to pres full_perm res *  pure (true_prop))))
    (
        if la = sz_zero
        then begin
          pres := (sz_gt lb sz_zero)
        end else if lb = sz_zero
        then begin
          pres := false
        end
        else begin
          pres := false
        end
    )
  )))
*) // FAIL: vprops not equivalent

(*
%splice_t[lex_check_FAIL_6] (check (`(
  fun (#pa: perm) (#sa: bytes) (a: byte_array) (la: US.t)
    (#pb: perm) (#sb: bytes) (b: byte_array) (lb: US.t)
    (pres: ref bool)
    ->
    (expects (byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * (exists res. (pts_to pres full_perm res)) * pure ((US.v la `eq2_prop` A.length a) `and_prop` (US.v lb `eq2_prop` A.length b))))
    (provides (fun _ -> byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * (exists res . pts_to pres full_perm res *  pure (true_prop))))
    (
        if la = sz_zero
        then begin
          pres := (sz_gt lb sz_zero);
          intro (exists res . pts_to pres full_perm res) _
        end else if lb = sz_zero
        then begin
          pres := false;
          intro (exists res . pts_to pres full_perm res) _
        end
        else begin
          pres := false;
          intro (exists res . pts_to pres full_perm res) _
        end
    )
  )))
*) // FAIL: vprops not equivalent

#set-options "--ide_id_info_off" // WHY WHY WHY?

%splice_t[lex_check_SUCCESS_7] (check (`(
  fun (#pa: perm) (#sa: bytes) (a: byte_array) (la: US.t)
    (#pb: perm) (#sb: bytes) (b: byte_array) (lb: US.t)
    (pres: ref bool)
    ->
    (expects (byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * (exists res . pts_to pres full_perm res) * pure ((US.v la `eq2_prop` A.length a) `and_prop` (US.v lb `eq2_prop` A.length b))))
    (provides (fun _ -> byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * (exists res . pts_to pres full_perm res *  pure (true_prop))))
    (
        if la = sz_zero
        then begin
          pres := (sz_gt lb sz_zero);
          intro (exists res . pts_to pres full_perm res * pure true_prop) _
        end else if lb = sz_zero
        then begin
          pres := false;
          intro (exists res . pts_to pres full_perm res * pure true_prop) _
        end
        else begin
          pres := false;
          intro (exists res . pts_to pres full_perm res * pure true_prop) _
        end
    )
  )))

(*
%splice_t[lex_check_FAIL_8] (check (`(
  fun (#pa: perm) (#sa: bytes) (a: byte_array) (la: US.t)
    (#pb: perm) (#sb: bytes) (b: byte_array) (lb: US.t)
    ->
    (expects (byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * pure ((US.v la `eq2_prop` A.length a) `and_prop` (US.v lb `eq2_prop` A.length b))))
    (provides (fun _ -> byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * pure (true_prop)))
    (
      let pres = local true in
      begin
        if la = sz_zero
        then begin
          pres := (sz_gt lb sz_zero)
        end else if lb = sz_zero
        then begin
          pres := false
        end
        else begin
          pres := false
        end
      end;
      intro (exists res . pts_to pres full_perm res `star` pure true_prop);
      return !pres
    )
  )))
*) // FAIL: either two annotations for if_post or none

let lex_order0 (sa sb: Seq.seq byte) : Tot bool (decreases (Seq.length sa)) =
  if Seq.length sa = 0
  then Seq.length sb > 0
  else if Seq.length sb = 0
  then false
  else
    let hda = Seq.head sa in
    let hdb = Seq.head sb in
    hda `FStar.UInt8.lt` hdb

let lex_order_bytes0 (sa sb: bytes) : GTot bool = lex_order0 sa sb

let byte_length (s: bytes) : GTot nat = Seq.length s

let byte_index (s: bytes) (i: nat) : GTot byte =
  if i >= Seq.length s
  then 0uy // dummy
  else Seq.index s i

assume val byte_array_read
  (#p: perm)
  (a: byte_array)
  (#s: bytes)
  (i: US.t)
: stt byte
    (byte_array_pts_to a p s `star` pure ((US.v i < byte_length s) `eq2_prop` true))
    (fun res -> byte_array_pts_to a p s `star` pure (res `eq2_prop` byte_index s (US.v i)))

%splice_t[lex_check_SUCCESS_9] (check (`(
  fun (#pa: perm) (#sa: bytes) (a: byte_array) (la: US.t)
    (#pb: perm) (#sb: bytes) (b: byte_array) (lb: US.t)
    ->
    (expects (byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * pure ((US.v la `eq2_prop` byte_length sa) `and_prop` (US.v lb `eq2_prop` byte_length sb))))
    (provides (fun (res: bool) -> byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * pure (res `eq2_prop` lex_order_bytes0 sa sb)))
    (
      if la = sz_zero
      then begin
        return (sz_gt lb sz_zero)
      end else if lb = sz_zero
      then return false
      else
        let hda = byte_array_read #pa a #sa sz_zero in
        let hdb = byte_array_read #pb b #sb sz_zero in
        return (hda `FStar.UInt8.lt` hdb)
    )
  )))

%splice_t[lex_check_SUCCESS_10] (check (`(
  fun (#pa: perm) (#sa: bytes) (a: byte_array) (la: US.t)
    (#pb: perm) (#sb: bytes) (b: byte_array) (lb: US.t)
    (pres: ref bool)
    ->
    (expects (byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * (exists res . pts_to pres full_perm res) * pure ((US.v la `eq2_prop` byte_length sa) `and_prop` (US.v lb `eq2_prop` byte_length sb))))
    (provides (fun _ -> byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * pts_to pres full_perm (lex_order_bytes0 sa sb)))
    (
      if la = sz_zero
      then begin
        pres := (sz_gt lb sz_zero)
      end else if lb = sz_zero
      then pres := false
      else
        let hda = byte_array_read #pa a #sa sz_zero in
        let hdb = byte_array_read #pb b #sb sz_zero in
        pres := (hda `FStar.UInt8.lt` hdb)
    )
  )))

let bytes_from (sa: bytes) (i: nat) : Tot bytes =
  if i >= Seq.length sa
  then Seq.empty
  else Seq.slice sa i (Seq.length sa)

let sz_gte (a b: US.t) : Tot bool = US.gte a b // from Pure to Tot
let sz_lt (a b: US.t) : Tot bool = US.lt a b // from Pure to Tot

%splice_t[lex_check_SUCCESS_11] (check (`(
  fun (#pa: perm) (#sa: bytes) (a: byte_array) (la: US.t)
    (#pb: perm) (#sb: bytes) (b: byte_array) (lb: US.t)
    (pos: US.t)
    ->
    (expects (byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * pure ((US.v la `eq2_prop` byte_length sa) `and_prop` (US.v lb `eq2_prop` byte_length sb))))
    (provides (fun (res: bool) -> byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * pure (res `eq2_prop` lex_order_bytes0 (bytes_from sa (US.v pos)) (bytes_from sb (US.v pos)))))
    (
      if pos `sz_gte` la
      then begin
        return (pos `sz_lt` lb)
      end else if pos `sz_gte` lb
      then return false
      else
        let hda = byte_array_read #pa a #sa pos in
        let hdb = byte_array_read #pb b #sb pos in
        return (hda `FStar.UInt8.lt` hdb)
    )
  )))

module I16 = FStar.Int16

let byte_compare (a b: byte) : Tot I16.t =
  if a = b
  then 0s
  else if a `FStar.UInt8.lt` b
  then -1s
  else 1s

let rec lex_compare (sa sb: Seq.seq byte) : Tot I16.t (decreases (Seq.length sa)) =
  if Seq.length sa = 0
  then
    if Seq.length sb > 0
    then -1s
    else 0s
  else if Seq.length sb = 0
  then 1s
  else
    let hda = Seq.head sa in
    let hdb = Seq.head sb in
    let c = byte_compare hda hdb in
    if c = 0s
    then lex_compare (Seq.tail sa) (Seq.tail sb)
    else c

let lex_compare_bytes (sa sb: bytes) : GTot I16.t = lex_compare sa sb

let bytes_from_zero (s: bytes) : Lemma
  (bytes_from s 0 == s)
//  [SMTPat (bytes_from s 0)]
= ()

let bytes_from_tail (s: bytes) (i: nat) : Lemma
  (requires (Seq.length s > i))
  (ensures (Seq.tail (bytes_from s i) == Ghost.reveal (bytes_from s (i + 1))))
= ()

let imp_prop (p1 p2: prop) : GTot prop = p1 ==> p2

let sz_add (n1 n2: US.t) (prf: squash (US.fits (US.v n1 + US.v n2))) : Tot US.t =
  US.add n1 n2

(*
%splice_t[psz_incr] (check  (`(
   fun (#n:erased US.t)
     (x:ref US.t)
      -> 
     (expects (
        pts_to x full_perm n `star`
        pure (US.fits (US.v (Ghost.reveal n) + 1))
     ))
     (provides (fun (n': US.t) ->
        pts_to x full_perm n' `star`
        pure (US.v n' `eq2_prop` US.v (Ghost.reveal n) + 1)
     ))
     (
       let n = !x in
       x := sz_add n 1sz ();
       return (sz_add n 1sz ())
     )
   ))) // not typeable (probably I can't use reveal)
*)

let can_incr (x: Ghost.erased US.t) : GTot prop = US.fits (US.v (Ghost.reveal x) + 1)
let eq_incr (y: US.t) (x: Ghost.erased US.t) : GTot prop = US.v y == US.v (Ghost.reveal x) + 1

%splice_t[psz_incr] (check  (`(
   fun (#n:erased US.t)
     (x:ref US.t)
      -> 
     (expects (
        pts_to x full_perm n `star`
        pure (can_incr n)
     ))
     (provides (fun (n': US.t) ->
        pts_to x full_perm n' `star`
        pure (n' `eq_incr` n)
     ))
     (
       let n = !x in
       x := sz_add n 1sz ();
       return (sz_add n 1sz ())
     )
   )))

let if_then_else_reveal
  (#t: Type)
  (cond: bool)
  (x: t)
  (y: Ghost.erased t)
: GTot t
= if cond then x else Ghost.reveal y

(*
%splice_t[write_if] (check  (`(
   fun (#t: Type)
     (#y:Ghost.erased t)
     (cond: bool)
     (p: ref t)
     (x: t)
      -> 
     (expects (
        pts_to p full_perm y
     ))
     (provides (fun (_: unit) ->
        pts_to p full_perm (if_then_else_reveal #t cond x y)
     ))
     (
       if cond
       then p := x
     )
   )))
*) // FAIL: check_tot _ elaborated to _ Not typeable . Probably because of universe polymorphism

%splice_t[write_if] (check  (`(
   fun (#t: Type0)
     (#y:Ghost.erased t)
     (cond: bool)
     (p: ref t)
     (x: t)
      -> 
     (expects (
        pts_to p full_perm y
     ))
     (provides (fun (_: unit) ->
        pts_to p full_perm (if_then_else_reveal #t cond x y)
     ))
     (
       if cond
       then p := x
     )
   )))

(*
%splice_t[lex_check_FAIL_12] (check (`(
  fun (#pa: perm) (#sa: bytes) (a: byte_array) (la: US.t)
    (#pb: perm) (#sb: bytes) (b: byte_array) (lb: US.t)
    (pres: ref I16.t)
    ->
    (expects (byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * (exists res . pts_to pres full_perm res) * pure ((US.v la `eq2_prop` byte_length sa) `and_prop` (US.v lb `eq2_prop` byte_length sb))))
    (provides (fun _ -> byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * (exists res . pts_to pres full_perm res)))
    (
      pres := 0s;
      let pcont = local true in
      let ppos : ref (x: US.t {
        ((US.v x <= byte_length sa) `eq2_prop` true) `and_prop`
        ((US.v x <= byte_length sb) `eq2_prop` true) `and_prop`
        (lex_compare_bytes sa sb `eq2_prop` lex_compare_bytes (bytes_from sa (US.v x)) (bytes_from sb (US.v x)))
      }) = local sz_zero in
      while
        (invariant (fun cont ->
          pts_to pcont full_perm cont `star`
          (exists res . pts_to pres full_perm res) `star`
          (exists pos . pts_to ppos full_perm pos)
        ))
        (let cont = !pcont in return cont)
        (
          let pos = !ppos in
          if pos = la
          then begin
            pcont := false;
            write_if (pos = lb) pres (-1s)
          end else
          if pos = lb
          then begin
            pres := 1s;
            pcont := false
          end
          else begin
            ppos := (sz_add pos 1sz ())
          end
        )
    )
  )))
*) // FAIL: check_tot write_if ... elaborated to write_if ... Not typeable, probably because the contents of pres couldn't be inferred as a Ghost.erased

let if_then_else
  (#t: Type)
  (cond: bool)
  (x: t)
  (y: t)
: GTot t
= if cond then x else y

%splice_t[write_if_known] (check  (`(
   fun (#t: Type0)
     (y:t)
     (cond: bool)
     (p: ref t)
     (x: t)
      -> 
     (expects (
        pts_to p full_perm y
     ))
     (provides (fun (_: unit) ->
        pts_to p full_perm (if_then_else #t cond x y)
     ))
     (
       if cond
       then p := x
     )
   )))

(*
%splice_t[lex_check_FAIL_13] (check (`(
  fun (#pa: perm) (#sa: bytes) (a: byte_array) (la: US.t)
    (#pb: perm) (#sb: bytes) (b: byte_array) (lb: US.t)
    (pres: ref I16.t)
    ->
    (expects (byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * (exists res . pts_to pres full_perm res) * pure ((US.v la `eq2_prop` byte_length sa) `and_prop` (US.v lb `eq2_prop` byte_length sb))))
    (provides (fun _ -> byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * (exists res . pts_to pres full_perm res)))
    (
      pres := 0s;
      let pcont = local true in
      let ppos : ref (x: US.t {
        ((US.v x <= byte_length sa) `eq2_prop` true) `and_prop`
        ((US.v x <= byte_length sb) `eq2_prop` true) `and_prop`
        (lex_compare_bytes sa sb `eq2_prop` lex_compare_bytes (bytes_from sa (US.v x)) (bytes_from sb (US.v x)))
      }) = local sz_zero in
      while
        (invariant (fun cont ->
          pts_to pcont full_perm cont `star`
          (exists res . pts_to pres full_perm res) `star`
          (exists pos . pts_to ppos full_perm pos)
        ))
        (let cont = !pcont in return cont)
        (
          let pos = !ppos in
          if pos = la
          then begin
            pcont := false;
            write_if_known 0s (pos = lb) pres (-1s)
          end else
          if pos = lb
          then begin
            pres := 1s;
            pcont := false
          end
          else begin
            ppos := (sz_add pos 1sz ())
          end
        )
    )
  )))
*) // FAIL: cannot prove conditions. Probably because I need explicit intro exists

%splice_t[lex_check_SUCCESS_14] (check (`( // No functional correctness
  fun (#pa: perm) (#sa: bytes) (a: byte_array) (la: US.t)
    (#pb: perm) (#sb: bytes) (b: byte_array) (lb: US.t)
    (pres: ref I16.t)
    ->
    (expects (byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * (exists res . pts_to pres full_perm res)))
    (provides (fun _ -> byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * (exists res . pts_to pres full_perm res)))
    (
      pres := 0s;
      let pcont = local true in
      let ppos : ref (x: US.t {
        ((US.v x <= byte_length sa) `eq2_prop` true) `and_prop`
        ((US.v x <= byte_length sb) `eq2_prop` true) `and_prop`
        (lex_compare_bytes sa sb `eq2_prop` lex_compare_bytes (bytes_from sa (US.v x)) (bytes_from sb (US.v x)))
      }) = local sz_zero in
      while
        (invariant (fun cont ->
          pts_to pcont full_perm cont `star`
          (exists res . pts_to pres full_perm res) `star`
          (exists pos . pts_to ppos full_perm pos)
        ))
        (let cont = !pcont in return cont)
        (
          let pos = !ppos in
          if pos = la
          then begin
            pcont := false;
            pres := (-1s);
            intro (exists res . pts_to pres full_perm res) _;
            intro (exists pos . pts_to ppos full_perm pos) _;
            intro (exists cont .
              pts_to pcont full_perm cont `star`
              (exists res . pts_to pres full_perm res) `star`
              (exists pos . pts_to ppos full_perm pos)
            ) _
          end else
          if pos = lb
          then begin
            pres := 1s;
            pcont := false;
            intro (exists res . pts_to pres full_perm res) _;
            intro (exists pos . pts_to ppos full_perm pos) _;
            intro (exists cont .
              pts_to pcont full_perm cont `star`
              (exists res . pts_to pres full_perm res) `star`
              (exists pos . pts_to ppos full_perm pos)
            ) _
          end
          else begin
            ppos := (sz_add pos 1sz ());
            intro (exists res . pts_to pres full_perm res) _;
            intro (exists pos . pts_to ppos full_perm pos) _;
            intro (exists cont .
              pts_to pcont full_perm cont `star`
              (exists res . pts_to pres full_perm res) `star`
              (exists pos . pts_to ppos full_perm pos)
            ) _
          end
        );
        intro (exists cont . pts_to pcont full_perm cont) _;
        intro (exists pos . pts_to ppos full_perm pos) _;
        intro (exists res . pts_to pres full_perm res) _
    )
  )))

(*
%splice_t[lex_check_FAIL_15] (check (`(
  fun (#pa: perm) (#sa: bytes) (a: byte_array) (la: US.t)
    (#pb: perm) (#sb: bytes) (b: byte_array) (lb: US.t)
    (pres: ref I16.t)
    ->
    (expects (byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * (exists res . pts_to pres full_perm res) * pure ((US.v la `eq2_prop` byte_length sa) `and_prop` (US.v lb `eq2_prop` byte_length sb))))
    (provides (fun _ -> byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * pts_to pres full_perm (lex_compare_bytes sa sb)))
    (
      pres := 0s;
      let pcont = local true in
      let ppos : ref (x: US.t {
        ((US.v x <= byte_length sa) `eq2_prop` true) `and_prop`
        ((US.v x <= byte_length sb) `eq2_prop` true) `and_prop`
        (lex_compare_bytes sa sb `eq2_prop` lex_compare_bytes (bytes_from sa (US.v x)) (bytes_from sb (US.v x)))
      }) = local sz_zero in
      while
        (invariant (fun cont ->
          pts_to pcont full_perm cont `star`
          pts_to pres full_perm (if_then_else cont 0s (lex_compare_bytes sa sb)) `star`
          (exists pos . pts_to ppos full_perm pos)
        ))
        (let cont = !pcont in return cont)
        (
          let pos = !ppos in
          if pos = la
          then begin
            pcont := false;
            write_if_known 0s (pos <> lb) pres (-1s);
            intro (exists pos . pts_to ppos full_perm pos) _;
            intro (exists cont . 
              pts_to pcont full_perm cont `star`
              pts_to pres full_perm (if_then_else cont 0s (lex_compare_bytes sa sb)) `star`
              (exists pos . pts_to ppos full_perm pos)
            ) _
          end else
          if pos = lb
          then begin
            pres := 1s;
            pcont := false;
            intro (exists pos . pts_to ppos full_perm pos) _;
            intro (exists cont . 
              pts_to pcont full_perm cont `star`
              pts_to pres full_perm (if_then_else cont 0s (lex_compare_bytes sa sb)) `star`
              (exists pos . pts_to ppos full_perm pos)
            ) _
          end
          else begin
            let a = byte_array_read a pos in
            let b = byte_array_read b pos in
            if byte_compare a b <> 0sz
            then begin
              pres := byte_compare a b;
              pcont := false;
              intro (exists pos . pts_to ppos full_perm pos) _;
              intro (exists cont . 
                pts_to pcont full_perm cont `star`
                pts_to pres full_perm (if_then_else cont 0s (lex_compare_bytes sa sb)) `star`
                (exists pos . pts_to ppos full_perm pos)
              ) _
            end
            else begin
              ppos := (sz_add pos 1sz ());
              intro (exists pos . pts_to ppos full_perm pos) _;
              intro (exists cont . 
                pts_to pcont full_perm cont `star`
                pts_to pres full_perm (if_then_else cont 0s (lex_compare_bytes sa sb)) `star`
                (exists pos . pts_to ppos full_perm pos)
              ) _
            end
          end
        );
        intro (exists cont . pts_to pcont full_perm cont)
    )
  )))
*) // cannot prove conditions (probably failing to rewrite pts_to)

(*
%splice_t[lex_check_FAIL_16] (check (`(
  fun (#pa: perm) (#sa: bytes) (a: byte_array) (la: US.t)
    (#pb: perm) (#sb: bytes) (b: byte_array) (lb: US.t)
    (pres: ref I16.t)
    ->
    (expects (byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * (exists res . pts_to pres full_perm res) * pure ((US.v la `eq2_prop` byte_length sa) `and_prop` (US.v lb `eq2_prop` byte_length sb))))
    (provides (fun _ -> byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * pts_to pres full_perm (lex_compare_bytes sa sb)))
    (
      pres := 0s;
      let pcont = local true in
      let ppos : ref (x: US.t {
        ((US.v x <= byte_length sa) `eq2_prop` true) `and_prop`
        ((US.v x <= byte_length sb) `eq2_prop` true) `and_prop`
        (lex_compare_bytes sa sb `eq2_prop` lex_compare_bytes (bytes_from sa (US.v x)) (bytes_from sb (US.v x)))
      }) = local sz_zero in
      while
        (invariant (fun cont ->
          pts_to pcont full_perm cont `star`
          (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if cont then 0s else lex_compare_bytes sa sb))) `star`
          (exists pos . pts_to ppos full_perm pos)
        ))
        (let cont = !pcont in return cont)
        (
          let cont = !pcont in // FIXME: this should be a ghost read, only necessary for the intro_exists pres
          let pos = !ppos in
          if pos = la
          then begin
            pcont := false;
            if pos <> lb
            then begin
              pres := (-1s);
              intro (exists pos . pts_to ppos full_perm pos) _;
              intro (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if false then 0s else lex_compare_bytes sa sb))) _;
              intro (exists cont . 
                pts_to pcont full_perm cont `star`
                (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if cont then 0s else lex_compare_bytes sa sb))) `star`
                (exists pos . pts_to ppos full_perm pos)
              ) _
            end
            else begin
              intro (exists pos . pts_to ppos full_perm pos) _;
              intro (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if false then 0s else lex_compare_bytes sa sb))) _;
              intro (exists cont . 
                pts_to pcont full_perm cont `star`
                (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if cont then 0s else lex_compare_bytes sa sb))) `star`
                (exists pos . pts_to ppos full_perm pos)
              ) _
            end
          end else
          if pos = lb
          then begin
            pres := 1s;
            pcont := false;
            intro (exists pos . pts_to ppos full_perm pos) _;
            intro (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if false then 0s else lex_compare_bytes sa sb))) _;
            intro (exists cont . 
              pts_to pcont full_perm cont `star`
              (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if cont then 0s else lex_compare_bytes sa sb))) `star`
              (exists pos . pts_to ppos full_perm pos)
            ) _
          end
          else begin
            let a = byte_array_read a pos in
            let b = byte_array_read b pos in
            if byte_compare a b <> 0sz
            then begin
              pres := byte_compare a b;
              pcont := false;
              intro (exists pos . pts_to ppos full_perm pos) _;
              intro (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if false then 0s else lex_compare_bytes sa sb))) _;
              intro (exists cont . 
                pts_to pcont full_perm cont `star`
                (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if cont then 0s else lex_compare_bytes sa sb))) `star`
                (exists pos . pts_to ppos full_perm pos)
              ) _
            end
            else begin
              ppos := (sz_add pos 1sz ());
              intro (exists pos . pts_to ppos full_perm pos) _;
              intro (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if cont then 0s else lex_compare_bytes sa sb))) _;
              intro (exists cont . 
                pts_to pcont full_perm cont `star`
                (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if cont then 0s else lex_compare_bytes sa sb))) `star`
                (exists pos . pts_to ppos full_perm pos)
              ) _
            end
          end
        );
        intro (exists cont . pts_to pcont full_perm cont)
    )
  )))
*) // FAIL: Tv_Match not implemented. I cannot use `if ... then ... else ...` in specs

#push-options "--z3rlimit 16"

(*
%splice_t[lex_check_FAIL_17] (check (`(
  fun (#pa: perm) (#sa: bytes) (a: byte_array) (la: US.t)
    (#pb: perm) (#sb: bytes) (b: byte_array) (lb: US.t)
    (pres: ref I16.t)
    ->
    (expects (byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * (exists res . pts_to pres full_perm res) * pure ((US.v la `eq2_prop` byte_length sa) `and_prop` (US.v lb `eq2_prop` byte_length sb))))
    (provides (fun _ -> byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * pts_to pres full_perm (lex_compare_bytes sa sb)))
    (
      pres := 0s;
      let pcont = local true in
      let ppos : ref (x: US.t {
        ((US.v x <= byte_length sa) `eq2_prop` true) `and_prop`
        ((US.v x <= byte_length sb) `eq2_prop` true) `and_prop`
        (lex_compare_bytes sa sb `eq2_prop` lex_compare_bytes (bytes_from sa (US.v x)) (bytes_from sb (US.v x)))
      }) = local sz_zero in
      while
        (invariant (fun cont ->
          pts_to pcont full_perm cont `star`
          (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) `star`
          (exists pos . pts_to ppos full_perm pos)
        ))
        (let cont = !pcont in return cont)
        (
          let cont = !pcont in // FIXME: this should be a ghost read, only necessary for the intro_exists pres
          let pos = !ppos in
          if pos = la
          then begin
            pcont := false;
            if pos <> lb
            then begin
              pres := (-1s);
              intro (exists pos . pts_to ppos full_perm pos) _;
              intro (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else false 0s (lex_compare_bytes sa sb)))) _;
              intro (exists cont . 
                pts_to pcont full_perm cont `star`
                (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) `star`
                (exists pos . pts_to ppos full_perm pos)
              ) _
            end
            else begin
              intro (exists pos . pts_to ppos full_perm pos) _;
              intro (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else false 0s (lex_compare_bytes sa sb)))) _;
              intro (exists cont . 
                pts_to pcont full_perm cont `star`
                (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) `star`
                (exists pos . pts_to ppos full_perm pos)
              ) _
            end
          end else
          if pos = lb
          then begin
            pres := 1s;
            pcont := false;
            intro (exists pos . pts_to ppos full_perm pos) _;
            intro (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else false 0s (lex_compare_bytes sa sb)))) _;
            intro (exists cont . 
              pts_to pcont full_perm cont `star`
              (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) `star`
              (exists pos . pts_to ppos full_perm pos)
            ) _
          end
          else begin
            let a = byte_array_read a pos in
            let b = byte_array_read b pos in
            if byte_compare a b <> 0sz
            then begin
              pres := byte_compare a b;
              pcont := false;
              intro (exists pos . pts_to ppos full_perm pos) _;
              intro (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else false 0s (lex_compare_bytes sa sb)))) _;
              intro (exists cont . 
                pts_to pcont full_perm cont `star`
                (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) `star`
                (exists pos . pts_to ppos full_perm pos)
              ) _
            end
            else begin
              ppos := (sz_add pos 1sz ());
              intro (exists pos . pts_to ppos full_perm pos) _;
              intro (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) _;
              intro (exists cont . 
                pts_to pcont full_perm cont `star`
                (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) `star`
                (exists pos . pts_to ppos full_perm pos)
              ) _
            end
          end
        );
        intro (exists cont . pts_to pcont full_perm cont)
    )
  )))

*) // FAIL to prove some pure condition. Did the refinement disappear? How can I debug with pure asserts?

%splice_t[assert_pulse] (check (`(
    fun (p: prop) ->
      (expects (pure p))
      (provides (fun _ -> pure p))
    (return ())
  )))

(*
%splice_t[lex_check_FAIL_18] (check (`(
  fun (#pa: perm) (#sa: bytes) (a: byte_array) (la: US.t)
    (#pb: perm) (#sb: bytes) (b: byte_array) (lb: US.t)
    (pres: ref I16.t)
    ->
    (expects (byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * (exists res . pts_to pres full_perm res) * pure ((US.v la `eq2_prop` byte_length sa) `and_prop` (US.v lb `eq2_prop` byte_length sb))))
    (provides (fun _ -> byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * pts_to pres full_perm (lex_compare_bytes sa sb)))
    (
      pres := 0s;
      let pcont = local true in
      let ppos : ref (x: US.t {
        ((US.v x <= byte_length sa) `eq2_prop` true) `and_prop`
        ((US.v x <= byte_length sb) `eq2_prop` true) `and_prop`
        (lex_compare_bytes sa sb `eq2_prop` lex_compare_bytes (bytes_from sa (US.v x)) (bytes_from sb (US.v x)))
      }) = local sz_zero in
      while
        (invariant (fun cont ->
          pts_to pcont full_perm cont `star`
          (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) `star`
          (exists pos . pts_to ppos full_perm pos)
        ))
        (let cont = !pcont in return cont)
        (
          let cont = !pcont in // FIXME: this should be a ghost read, only necessary for the intro_exists pres
          let pos = !ppos in
          assert_pulse (
            ((US.v pos <= byte_length sa) `eq2_prop` true) `and_prop`
            ((US.v pos <= byte_length sb) `eq2_prop` true) `and_prop`
            (lex_compare_bytes sa sb `eq2_prop` lex_compare_bytes (bytes_from sa (US.v pos)) (bytes_from sb (US.v pos)))
          );
          if pos = la
          then begin
            pcont := false;
            if pos <> lb
            then begin
              pres := (-1s);
              intro (exists pos . pts_to ppos full_perm pos) _;
              intro (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else false 0s (lex_compare_bytes sa sb)))) _;
              intro (exists cont . 
                pts_to pcont full_perm cont `star`
                (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) `star`
                (exists pos . pts_to ppos full_perm pos)
              ) _
            end
            else begin
              intro (exists pos . pts_to ppos full_perm pos) _;
              intro (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else false 0s (lex_compare_bytes sa sb)))) _;
              intro (exists cont . 
                pts_to pcont full_perm cont `star`
                (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) `star`
                (exists pos . pts_to ppos full_perm pos)
              ) _
            end
          end else
          if pos = lb
          then begin
            pres := 1s;
            pcont := false;
            intro (exists pos . pts_to ppos full_perm pos) _;
            intro (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else false 0s (lex_compare_bytes sa sb)))) _;
            intro (exists cont . 
              pts_to pcont full_perm cont `star`
              (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) `star`
              (exists pos . pts_to ppos full_perm pos)
            ) _
          end
          else begin
            let a = byte_array_read a pos in
            let b = byte_array_read b pos in
            if byte_compare a b <> 0sz
            then begin
              pres := byte_compare a b;
              pcont := false;
              intro (exists pos . pts_to ppos full_perm pos) _;
              intro (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else false 0s (lex_compare_bytes sa sb)))) _;
              intro (exists cont . 
                pts_to pcont full_perm cont `star`
                (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) `star`
                (exists pos . pts_to ppos full_perm pos)
              ) _
            end
            else begin
              ppos := (sz_add pos 1sz ());
              intro (exists pos . pts_to ppos full_perm pos) _;
              intro (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) _;
              intro (exists cont . 
                pts_to pcont full_perm cont `star`
                (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) `star`
                (exists pos . pts_to ppos full_perm pos)
              ) _
            end
          end
        );
        intro (exists cont . pts_to pcont full_perm cont)
    )
  )))
*) // FAIL to prove the assert_pulse. Did the refinement disappear?

%splice_t[assert_squash] (check (`(
    fun (p: prop) (_: squash p) ->
      (expects emp)
      (provides (fun _ -> pure p))
    (return ())
  )))

(*
%splice_t[lex_check_FAIL_19] (check (`(
  fun (#pa: perm) (#sa: bytes) (a: byte_array) (la: US.t)
    (#pb: perm) (#sb: bytes) (b: byte_array) (lb: US.t)
    (pres: ref I16.t)
    ->
    (expects (byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * (exists res . pts_to pres full_perm res) * pure ((US.v la `eq2_prop` byte_length sa) `and_prop` (US.v lb `eq2_prop` byte_length sb))))
    (provides (fun _ -> byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * pts_to pres full_perm (lex_compare_bytes sa sb)))
    (
      pres := 0s;
      let pcont = local true in
      let ppos : ref (x: US.t {
        ((US.v x <= byte_length sa) `eq2_prop` true) `and_prop`
        ((US.v x <= byte_length sb) `eq2_prop` true) `and_prop`
        (lex_compare_bytes sa sb `eq2_prop` lex_compare_bytes (bytes_from sa (US.v x)) (bytes_from sb (US.v x)))
      }) = local sz_zero in
      while
        (invariant (fun cont ->
          pts_to pcont full_perm cont `star`
          (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) `star`
          (exists pos . pts_to ppos full_perm pos)
        ))
        (let cont = !pcont in return cont)
        (
          let cont = !pcont in // FIXME: this should be a ghost read, only necessary for the intro_exists pres
          let pos = !ppos in
          assert_squash (
            ((US.v pos <= byte_length sa) `eq2_prop` true) `and_prop`
            ((US.v pos <= byte_length sb) `eq2_prop` true) `and_prop`
            (lex_compare_bytes sa sb `eq2_prop` lex_compare_bytes (bytes_from sa (US.v pos)) (bytes_from sb (US.v pos)))
          ) ();
          if pos = la
          then begin
            pcont := false;
            if pos <> lb
            then begin
              pres := (-1s);
              intro (exists pos . pts_to ppos full_perm pos) _;
              intro (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else false 0s (lex_compare_bytes sa sb)))) _;
              intro (exists cont . 
                pts_to pcont full_perm cont `star`
                (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) `star`
                (exists pos . pts_to ppos full_perm pos)
              ) _
            end
            else begin
              intro (exists pos . pts_to ppos full_perm pos) _;
              intro (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else false 0s (lex_compare_bytes sa sb)))) _;
              intro (exists cont . 
                pts_to pcont full_perm cont `star`
                (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) `star`
                (exists pos . pts_to ppos full_perm pos)
              ) _
            end
          end else
          if pos = lb
          then begin
            pres := 1s;
            pcont := false;
            intro (exists pos . pts_to ppos full_perm pos) _;
            intro (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else false 0s (lex_compare_bytes sa sb)))) _;
            intro (exists cont . 
              pts_to pcont full_perm cont `star`
              (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) `star`
              (exists pos . pts_to ppos full_perm pos)
            ) _
          end
          else begin
            let a = byte_array_read a pos in
            let b = byte_array_read b pos in
            if byte_compare a b <> 0sz
            then begin
              pres := byte_compare a b;
              pcont := false;
              intro (exists pos . pts_to ppos full_perm pos) _;
              intro (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else false 0s (lex_compare_bytes sa sb)))) _;
              intro (exists cont . 
                pts_to pcont full_perm cont `star`
                (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) `star`
                (exists pos . pts_to ppos full_perm pos)
              ) _
            end
            else begin
              ppos := (sz_add pos 1sz ());
              intro (exists pos . pts_to ppos full_perm pos) _;
              intro (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) _;
              intro (exists cont . 
                pts_to pcont full_perm cont `star`
                (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) `star`
                (exists pos . pts_to ppos full_perm pos)
              ) _
            end
          end
        );
        intro (exists cont . pts_to pcont full_perm cont)
    )
  )))
*) // same thing here with assert_squash instead of assert_pure

let pos_refine_prop
  (sa: bytes)
  (sb: bytes)
  (x: US.t)
: GTot prop
=
        ((US.v x <= byte_length sa) `eq2_prop` true) `and_prop`
        ((US.v x <= byte_length sb) `eq2_prop` true) `and_prop`
        (lex_compare_bytes sa sb `eq2_prop` lex_compare_bytes (bytes_from sa (US.v x)) (bytes_from sb (US.v x)))

let pos_refine
  (sa: bytes)
  (sb: bytes)
: Tot Type0
= (x: US.t { pos_refine_prop sa sb x })

%splice_t[read_pos_refine] (check (`(
  fun (sa: bytes) (sb: bytes) (p: ref (pos_refine sa sb)) ->
    (expects (exists x . pts_to p full_perm x))
    (provides (fun (res: US.t) ->
      (exists x . pts_to p full_perm x) `star`
      pure (pos_refine_prop sa sb res)
    ))
    (
      let x = !p in
      return x
    )
  )))

%splice_t[write_pos_refine] (check (`(
  fun (sa: bytes) (sb: bytes) (p: ref (pos_refine sa sb)) (res: US.t) ->
    (expects (
      (exists x . pts_to p full_perm x) `star` pure (pos_refine_prop sa sb res)
    ))
    (provides (fun _ ->
      (exists x . pts_to p full_perm x)
    ))
    (
      p := res;
      intro (exists x . pts_to p full_perm x) _
    )
  )))

let zero_pos_refine
  (sa sb: bytes)
: Tot (pos_refine sa sb)
= sz_zero

(*
%splice_t[lex_check_FAIL_20] (check (`(
  fun (#pa: perm) (#sa: bytes) (a: byte_array) (la: US.t)
    (#pb: perm) (#sb: bytes) (b: byte_array) (lb: US.t)
    (pres: ref I16.t)
    ->
    (expects (byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * (exists res . pts_to pres full_perm res) * pure ((US.v la `eq2_prop` byte_length sa) `and_prop` (US.v lb `eq2_prop` byte_length sb))))
    (provides (fun _ -> byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * pts_to pres full_perm (lex_compare_bytes sa sb)))
    (
      pres := 0s;
      let pcont = local true in
      let ppos : ref (pos_refine sa sb) = local (zero_pos_refine sa sb) in
      while
        (invariant (fun cont ->
          pts_to pcont full_perm cont `star`
          (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) `star`
          (exists pos . pts_to ppos full_perm pos)
        ))
        (let cont = !pcont in return cont)
        (
          let cont = !pcont in // FIXME: this should be a ghost read, only necessary for the intro_exists pres
          let pos = read_pos_refine sa sb ppos in
          if pos = la
          then begin
            pcont := false;
            if pos <> lb
            then begin
              pres := (-1s);
              intro (exists pos . pts_to ppos full_perm pos) _;
              intro (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else false 0s (lex_compare_bytes sa sb)))) _;
              intro (exists cont . 
                pts_to pcont full_perm cont `star`
                (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) `star`
                (exists pos . pts_to ppos full_perm pos)
              ) _
            end
            else begin
              intro (exists pos . pts_to ppos full_perm pos) _;
              intro (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else false 0s (lex_compare_bytes sa sb)))) _;
              intro (exists cont . 
                pts_to pcont full_perm cont `star`
                (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) `star`
                (exists pos . pts_to ppos full_perm pos)
              ) _
            end
          end else
          if pos = lb
          then begin
            pres := 1s;
            pcont := false;
            intro (exists pos . pts_to ppos full_perm pos) _;
            intro (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else false 0s (lex_compare_bytes sa sb)))) _;
            intro (exists cont . 
              pts_to pcont full_perm cont `star`
              (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) `star`
              (exists pos . pts_to ppos full_perm pos)
            ) _
          end
          else begin
            let a = byte_array_read a pos in
            let b = byte_array_read b pos in
            if byte_compare a b <> 0sz
            then begin
              pres := byte_compare a b;
              pcont := false;
              intro (exists pos . pts_to ppos full_perm pos) _;
              intro (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else false 0s (lex_compare_bytes sa sb)))) _;
              intro (exists cont . 
                pts_to pcont full_perm cont `star`
                (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) `star`
                (exists pos . pts_to ppos full_perm pos)
              ) _
            end
            else begin
              write_pos_refine sa sb ppos (sz_add pos 1sz ());
              intro (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) _;
              intro (exists cont . 
                pts_to pcont full_perm cont `star`
                (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) `star`
                (exists pos . pts_to ppos full_perm pos)
              ) _
            end
          end
        );
        intro (exists cont . pts_to pcont full_perm cont)
    )
  )))

// *) // FAIL: op_Equality x#13 x#9 not typeable at Prims.bool. Subtyping with the pos_refine refinement type is not very well supported

let sz_eq (a b: US.t) : Tot bool = a = b

let sz_ne (a b: US.t) : Tot bool = a <> b

(*
%splice_t[lex_check_FAIL_21] (check (`(
  fun (#pa: perm) (#sa: bytes) (a: byte_array) (la: US.t)
    (#pb: perm) (#sb: bytes) (b: byte_array) (lb: US.t)
    (pres: ref I16.t)
    ->
    (expects (byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * (exists res . pts_to pres full_perm res) * pure ((US.v la `eq2_prop` byte_length sa) `and_prop` (US.v lb `eq2_prop` byte_length sb))))
    (provides (fun _ -> byte_array_pts_to a pa sa * byte_array_pts_to b pb sb * pts_to pres full_perm (lex_compare_bytes sa sb)))
    (
      pres := 0s;
      let pcont = local true in
      let ppos : ref (pos_refine sa sb) = local (zero_pos_refine sa sb) in
      while
        (invariant (fun cont ->
          pts_to pcont full_perm cont `star`
          (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) `star`
          (exists pos . pts_to ppos full_perm pos)
        ))
        (let cont = !pcont in return cont)
        (
          let cont = !pcont in // FIXME: this should be a ghost read, only necessary for the intro_exists pres
          let pos = read_pos_refine sa sb ppos in
          if pos `sz_eq` la
          then begin
            pcont := false;
            if pos `sz_ne` lb
            then begin
              pres := (-1s);
              intro (exists pos . pts_to ppos full_perm pos) _;
              intro (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else false 0s (lex_compare_bytes sa sb)))) _;
              intro (exists cont . 
                pts_to pcont full_perm cont `star`
                (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) `star`
                (exists pos . pts_to ppos full_perm pos)
              ) _
            end
            else begin
              intro (exists pos . pts_to ppos full_perm pos) _;
              intro (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else false 0s (lex_compare_bytes sa sb)))) _;
              intro (exists cont . 
                pts_to pcont full_perm cont `star`
                (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) `star`
                (exists pos . pts_to ppos full_perm pos)
              ) _
            end
          end else
          if pos `sz_eq` lb
          then begin
            pres := 1s;
            pcont := false;
            intro (exists pos . pts_to ppos full_perm pos) _;
            intro (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else false 0s (lex_compare_bytes sa sb)))) _;
            intro (exists cont . 
              pts_to pcont full_perm cont `star`
              (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) `star`
              (exists pos . pts_to ppos full_perm pos)
            ) _
          end
          else begin
            let a = byte_array_read a pos in
            let b = byte_array_read b pos in
            if byte_compare a b <> 0sz
            then begin
              pres := byte_compare a b;
              pcont := false;
              intro (exists pos . pts_to ppos full_perm pos) _;
              intro (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else false 0s (lex_compare_bytes sa sb)))) _;
              intro (exists cont . 
                pts_to pcont full_perm cont `star`
                (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) `star`
                (exists pos . pts_to ppos full_perm pos)
              ) _
            end
            else begin
              write_pos_refine sa sb ppos (sz_add pos 1sz ());
              intro (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) _;
              intro (exists cont . 
                pts_to pcont full_perm cont `star`
                (exists res . pts_to pres full_perm res `star` pure (res `eq2_prop` (if_then_else cont 0s (lex_compare_bytes sa sb)))) `star`
                (exists pos . pts_to ppos full_perm pos)
              ) _
            end
          end
        );
        intro (exists cont . pts_to pcont full_perm cont)
    )
  )))
*) // loops forever with IntroExists
