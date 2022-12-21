module Pulse.Steel.Wrapper

open Steel.ST.Effect
open Steel.Memory
open Steel.ST.Util

inline_for_extraction
let stt (a:Type u#a) (pre:vprop) (post:a -> vprop) = unit -> STT a pre post

inline_for_extraction
let return_stt (#a:Type u#a) (x:a) : stt a emp (fun r -> pure (r == x)) =
  fun _ -> return x

inline_for_extraction
let return_stt_noeq (#a:Type u#a) (x:a) : stt a emp (fun _ -> emp) = fun _ -> return x

inline_for_extraction
let bind_stt (#a:Type u#a) (#b:Type u#b) (#pre1:vprop) (#post1:a -> vprop) (#post2:b -> vprop)
  (e1:stt a pre1 post1)
  (e2:(x:a -> stt b (post1 x) post2))

  : stt b pre1 post2 =

  fun _ ->
  let x = e1 () in
  e2 x ()

inline_for_extraction
let frame_stt (#a:Type u#a) (#pre:vprop) (#post:a -> vprop) (frame:vprop) (e:stt a pre post)
  : stt a (pre `star` frame) (fun x -> post x `star` frame) =
  fun _ -> e ()

assume val admit__ (#a:Type u#a) (#p:vprop) (#q:a -> vprop) (_:unit) : ST a p q True (fun _ -> False)

let vprop_equiv (p q:vprop) = squash (equiv p q)
let vprop_post_equiv (#t:Type u#a) (p q: t -> vprop) = forall x. vprop_equiv (p x) (q x)

let intro_vprop_post_equiv
       (#t:Type u#a) 
       (p q: t -> vprop)
       (pf: (x:t -> vprop_equiv (p x) (q x)))
  : vprop_post_equiv p q
  = let pf = 
        introduce forall x. vprop_equiv (p x) (q x)
        with pf x
    in
    FStar.Squash.join_squash pf
       
let elim_vprop_post_equiv (#t:Type u#a)
                          (p q: t -> vprop) 
                          (pf:vprop_post_equiv p q)
                          (x:t) 
    : vprop_equiv (p x) (q x)
    = let pf : squash (vprop_equiv (p x) (q x))
             = eliminate forall x. vprop_equiv (p x) (q x) with x
      in
      FStar.Squash.join_squash pf

inline_for_extraction
let sub_stt (#a:Type u#a)
            (#pre1:vprop)
            (pre2:vprop)
            (#post1:a -> vprop)
            (post2:a -> vprop)
            (pf1 : vprop_equiv pre1 pre2)
            (pf2 : vprop_post_equiv post1 post2)
            (e:stt a pre1 post1)
  : stt a pre2 post2 =
  fun _ ->
    [@inline_let]
    let _ = unsquash_equiv pre1 pre2 () in
    rewrite_equiv pre2 pre1;
    let x = e () in
    [@inline_let]    
    let pf : vprop_equiv (post1 x) (post2 x) = 
      elim_vprop_post_equiv post1 post2 pf2 x
    in
    [@inline_let]    
    let _ = unsquash_equiv (post1 x) (post2 x) pf in
    rewrite_equiv (post1 x) (post2 x);
    return x

let vprop_equiv_refl (v0:vprop) 
  : vprop_equiv v0 v0
  = equiv_refl v0

let vprop_equiv_sym (v0 v1:vprop) (_:vprop_equiv v0 v1)
  : vprop_equiv v1 v0
  = equiv_sym v0 v1

let vprop_equiv_trans (v0 v1 v2:vprop) (_:vprop_equiv v0 v1) (_:vprop_equiv v1 v2)
  : vprop_equiv v0 v2
  = equiv_trans v0 v1 v2

let vprop_equiv_unit (x:vprop)
  : vprop_equiv (emp `star` x) x
  = cm_identity x

let vprop_equiv_comm (p1 p2:vprop)
  : vprop_equiv (p1 `star` p2) (p2 `star` p1)
  = star_commutative p1 p2

let vprop_equiv_assoc (p1 p2 p3:vprop)
  : vprop_equiv ((p1 `star` p2) `star` p3) (p1 `star` (p2 `star` p3))
  = star_associative p1 p2 p3

let vprop_equiv_cong (p1 p2 p3 p4:vprop)
                     (_: vprop_equiv p1 p3)
                     (_: vprop_equiv p2 p4)
  : vprop_equiv (p1 `star` p2) (p3 `star` p4)
  = star_congruence p1 p2 p3 p4

module G = FStar.Ghost
module U32 = FStar.UInt32
module R = Steel.ST.Reference

type erased = G.erased u32
let hide (x:u32) : erased = G.hide x
let reveal (x:erased) = G.reveal x

type ref = R.ref u32
[@@ __reduce__]
let pts_to (r:ref) (n:erased) = R.pts_to r full_perm n

let read (n:erased) (r:ref)
  = fun _ ->
    let x = R.read r in
    rewrite (pts_to r n) (pts_to r (hide x));
    return x

let write (n:erased) (r:ref) (x:u32)
  = fun _ ->
    let _ = R.write r x in
    rewrite _ (pts_to r (hide x))
