module Steel.ST.C.Rewrite

let rewrite_forall_from
  (#from #to: Type)
  (rewrite_from_to : (from -> Tot to))
  (rewrite_to_from: (to -> Tot from))
: GTot prop
= forall (x: from) . rewrite_to_from (rewrite_from_to x) == x

let rewrite_forall_from_intro
  (#from #to: Type)
  (rewrite_from_to : (from -> Tot to))
  (rewrite_to_from: (to -> Tot from))
  (f: (x: from) -> Lemma
    (rewrite_to_from (rewrite_from_to x) == x)
  )
: Lemma
  (rewrite_forall_from rewrite_from_to rewrite_to_from)
= Classical.forall_intro f

let rewrite_forall_to
  (#from #to: Type)
  (rewrite_from_to : (from -> Tot to))
  (rewrite_to_from: (to -> Tot from))
: GTot prop
= forall (y: to) . rewrite_from_to (rewrite_to_from y) == y

let rewrite_forall_to_intro
  (#from #to: Type)
  (rewrite_from_to : (from -> Tot to))
  (rewrite_to_from: (to -> Tot from))
  (f: (x: to) -> Lemma
    (rewrite_from_to (rewrite_to_from x) == x)
  )
: Lemma
  (rewrite_forall_to rewrite_from_to rewrite_to_from)
= Classical.forall_intro f

noeq
type rewrite_elts (from: Type) (to: Type) = {
  rewrite_from_to : (from -> Tot to);
  rewrite_to_from: (to -> Tot from);
  rewrite_equiv : squash (
    rewrite_forall_from rewrite_from_to rewrite_to_from /\
    rewrite_forall_to rewrite_from_to rewrite_to_from
  );
}
