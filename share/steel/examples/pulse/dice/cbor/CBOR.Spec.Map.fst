module CBOR.Spec.Map
include CBOR.Spec.Type

let rec list_for_all_weaken
  (#t: Type)
  (p1: t -> bool)
  (p2: t -> bool { forall x . p1 x ==> p2 x })
  (l: list t)
: Lemma
  (requires (List.Tot.for_all p1 l))
  (ensures (List.Tot.for_all p2 l))
= match l with
  | [] -> ()
  | _ :: q -> list_for_all_weaken p1 p2 q

let rec list_sorted_cons_elim
  (#t1: Type)
  (key_order: t1 -> t1 -> bool {
    forall x y z . (key_order x y /\ key_order y z) ==> key_order x z
  })
  (a: t1)
  (q: list t1)
: Lemma
  (requires (List.Tot.sorted key_order (a :: q)))
  (ensures (List.Tot.for_all (key_order a) q))
  (decreases q)
= match q with
  | [] -> ()
  | b :: r ->
    list_sorted_cons_elim key_order b r;
    list_for_all_weaken (key_order b) (key_order a) r

let rec list_sorted_map_entry_order_lt_tail
  (#t1 #t2: Type)
  (key_order: t1 -> t1 -> bool {
    (forall x y z . (key_order x y /\ key_order y z) ==> key_order x z)
  })
  (a: (t1 & t2))
  (l: list (t1 & t2))
  (k: t1)
: Lemma
  (requires (List.Tot.sorted (map_entry_order key_order _) (a :: l) /\ List.Tot.memP k (List.Tot.map fst l)))
  (ensures (key_order (fst a) k))
  (decreases l)
= let b :: q = l in
  if FStar.StrongExcludedMiddle.strong_excluded_middle (k == fst b)
  then ()
  else list_sorted_map_entry_order_lt_tail key_order b q k

let list_sorted_map_entry_order_not_memP_tail
  (#t1 #t2: Type)
  (key_order: t1 -> t1 -> bool {
    (forall x . key_order x x == false) /\
    (forall x y z . (key_order x y /\ key_order y z) ==> key_order x z)
  })
  (a: (t1 & t2))
  (l: list (t1 & t2))
: Lemma
  (requires (List.Tot.sorted (map_entry_order key_order _) (a :: l)))
  (ensures (~ (List.Tot.memP (fst a) (List.Tot.map fst l))))
= Classical.move_requires (list_sorted_map_entry_order_lt_tail key_order a l) (fst a)

let rec list_sorted_map_entry_order_no_repeats
  (#t1 #t2: Type)
  (key_order: t1 -> t1 -> bool {
    (forall x . key_order x x == false) /\
    (forall x y z . (key_order x y /\ key_order y z) ==> key_order x z)
  })
  (l: list (t1 & t2))
: Lemma
  (requires (List.Tot.sorted (map_entry_order key_order _) l))
  (ensures (List.Tot.no_repeats_p (List.Tot.map fst l)))
= match l with
  | [] -> ()
  | a :: q ->
    list_sorted_map_entry_order_no_repeats key_order q;
    list_sorted_map_entry_order_not_memP_tail key_order a q

let rec list_tot_for_all_order_trans
    (#t1: Type)
    (order: t1 -> t1 -> bool {
      (forall x . order x x == false) /\
      (forall x y z . (order x y /\ order y z) ==> order x z)
    })
    (k1v1: _)
    (k2v2: _)
    (l1: list t1)
  : Lemma
  (requires (order k1v1 k2v2 /\
    List.Tot.for_all (order k2v2) l1
  ))
  (ensures (
    List.Tot.for_all (order k1v1) l1
  ))
  (decreases l1)
= match l1 with
  | [] -> ()
  | _ :: q -> list_tot_for_all_order_trans order k1v1 k2v2 q

let rec list_ghost_assoc
  (#key: Type)
  (#value: Type)
  (k: key)
  (m: list (key & value))
: GTot (option value)
  (decreases m)
= match m with
  | [] -> None
  | (k', v') :: m' ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (k == k')
    then Some v'
    else list_ghost_assoc k m'

let rec list_ghost_assoc_append
    (#tk #tv: Type)
    (k: tk)
    (l1 l2: list (tk & tv))
: Lemma
    (ensures (list_ghost_assoc k (l1 `List.Tot.append` l2) == (
        match list_ghost_assoc k l1 with
        | Some v -> Some v
        | None -> list_ghost_assoc k l2
    )))
    (decreases l1)
= match l1 with
| [] -> ()
| (k1, _ ) :: q1 ->
    if FStar.StrongExcludedMiddle.strong_excluded_middle (k == k1)
    then ()
    else list_ghost_assoc_append k q1 l2

[@@noextract_to "krml"] noextract
let rec map_sort_merge
  (#t1 #t2: Type)
  (key_compare: t1 -> t1 -> int)
  (accu: list (t1 & t2))
  (l1: list (t1 & t2))
  (l2: list (t1 & t2))
: Tot (bool & list (t1 & t2))
  (decreases (List.Tot.length l1 + List.Tot.length l2))
= match l1, l2 with
  |  (k1, v1) :: l1', (k2, v2) :: l2' ->
    begin let c = key_compare k1 k2 in
      if c = 0
      then (false, accu `List.Tot.append` (l1 `List.Tot.append` l2))
      else if c < 0
      then map_sort_merge key_compare (accu `List.Tot.append` [(k1, v1)]) l1' l2
      else map_sort_merge key_compare (accu `List.Tot.append` [(k2, v2)]) l1' ((k1, v1) :: l2') // this is not a stable sort
    end
  | [], _ -> (true, accu `List.Tot.append` l2)
  | _, [] -> (true, accu `List.Tot.append` l1)

let rec list_splitAt_length
  (#t: Type)
  (n: nat)
  (l: list t)
: Lemma
  (requires (List.Tot.length l >= n))
  (ensures (
    let (l1, l2) = List.Tot.splitAt n l in
    List.Tot.length l1 == n /\
    List.Tot.length l1 + List.Tot.length l2 == List.Tot.length l
  ))
  [SMTPat (List.Tot.splitAt n l)]
= if n = 0 then () else list_splitAt_length (n - 1) (List.Tot.tl l)

[@@noextract_to "krml"] noextract
let rec map_sort
  (#t1 #t2: Type)
  (key_compare: t1 -> t1 -> int)
  (l: list (t1 & t2))
: Tot (bool & list (t1 & t2))
  (decreases (List.Tot.length l))
= let len = List.Tot.length l in
  if len < 2
  then (true, l)
  else
    let (l1, l2) = List.Tot.splitAt (len / 2) l in
    let (res, l1') = map_sort key_compare l1 in
    if not res
    then (false, l1' `List.Tot.append` l2)
    else
      let (res, l2') = map_sort key_compare l2 in
      if not res
      then (false, l1' `List.Tot.append` l2')
      else map_sort_merge key_compare [] l1' l2'

let map_sort_correct
  (#t1 #t2: Type)
  (key_order: t1 -> t1 -> bool)
  (key_compare: t1 -> t1 -> int)
  (l: list (t1 & t2))
: Lemma
  (let (res, l') = map_sort key_compare l in
    (forall pre suff . List.Tot.no_repeats_p (pre `List.Tot.append` (List.Tot.map fst l' `List.Tot.append` suff)) <==> List.Tot.no_repeats_p (pre `List.Tot.append` (List.Tot.map fst l `List.Tot.append` suff))) /\
    (if res
    then (List.Tot.sorted (map_entry_order key_order _) l' /\ (forall k . list_ghost_assoc k l' == list_ghost_assoc k l))
    else ~ (List.Tot.no_repeats_p (List.Tot.map fst l)))
  )
= admit ()
