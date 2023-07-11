module Steel.ST.C.Types.UserUnion
open Steel.ST.Util
open Steel.ST.C.Rewrite
open Steel.ST.C.Types.Scalar

module F = Steel.ST.C.Types.Fields

(* This library allows the user to define their own union type, with
a constructor from field values, and a destructor to field values for
each field. This may be necessary for recursive unions. *)

noextract
let union_item_refine
  ([@@@strictly_positive] t: Type) (one: Ghost.erased t) (p: Ghost.erased (option bool)) (x: t)
: GTot prop
= 
  match p with
  | None -> True
  | Some p -> not p == FStar.StrongExcludedMiddle.strong_excluded_middle (x == Ghost.reveal one)

inline_for_extraction
noextract
type union_item_t ([@@@strictly_positive] t: Type) (one: Ghost.erased t) (p: Ghost.erased (option bool)) = (x: t { union_item_refine t one p x })

inline_for_extraction
noextract
let union_item_intro
  (#t: Type)
  (one: Ghost.erased t)
  (p: Ghost.erased (option bool))
  (x: t)
: Pure (union_item_t t one p)
    (requires (union_item_refine t one p x))
    (ensures (fun _ -> True))
= x

[@@noextract_to "krml"; norm_field_attr]
inline_for_extraction // for field_desc.fd_type
noeq
type is_union_item (t: (Ghost.erased (option bool) -> Type)) (unkn: Ghost.erased (t None)) = {
  some_to_none: ((b: Ghost.erased bool) -> t (Some (Ghost.reveal b)) -> t None);
  none_to_some: (x: t None) -> t (Some (not (FStar.StrongExcludedMiddle.strong_excluded_middle (x == Ghost.reveal unkn))));
  none_to_some_inj: (x: t None) -> Lemma (some_to_none _ (none_to_some x) == x);
  some_to_none_inj: (b: Ghost.erased bool) -> (x: t (Some (Ghost.reveal b))) -> Lemma
    (Ghost.reveal b == not (FStar.StrongExcludedMiddle.strong_excluded_middle (some_to_none b x == Ghost.reveal unkn)) /\
      none_to_some (some_to_none _ x) == x
    );
}

[@@noextract_to "krml"]
let union_item_gen_some_to_none
  (#t: Type) (td: typedef t)
  (b: Ghost.erased bool)
  (x: union_item_t t (unknown td) (Some (Ghost.reveal b)))
: Tot (union_item_t t (unknown td) None)
= x

[@@noextract_to "krml"]
let union_item_gen_none_to_some
  (#t: Type) (td: typedef t)
  (x: union_item_t t (unknown td) None)
: Tot (union_item_t t (unknown td) (Some (not (FStar.StrongExcludedMiddle.strong_excluded_middle (x == Ghost.reveal (unknown td))))))
= x

[@@noextract_to "krml"]
let union_item_gen (#t: Type) (td: typedef t) : is_union_item (union_item_t t (unknown td)) (unknown td) = {
  some_to_none = union_item_gen_some_to_none td;
  none_to_some = union_item_gen_none_to_some td;
  none_to_some_inj = (fun _ -> ());
  some_to_none_inj = (fun _ _ -> ());
}

[@@noextract_to "krml"]
let union_item_rewrite
  (#t: Type)
  (one: Ghost.erased t)
: Tot (rewrite_elts t (union_item_t t one None))
= {
    rewrite_from_to = (fun (x: t) -> x <: union_item_t t one None);
    rewrite_to_from = (fun (x: union_item_t t one None) -> x <: t);
    rewrite_equiv = ();
  }

[@@noextract_to "krml"; norm_field_attr]
inline_for_extraction
noeq
type union_field_description_t (#t: Type0) (fd: F.field_description_t t) : Type u#1 = {
  fd_union_type: (F.field_t fd -> Ghost.erased (option bool) -> Type0);
  fd_union_type_rewrite: ((s: F.field_t fd) -> Tot (rewrite_elts (fd.fd_type s) (fd_union_type s None)));
  fd_union_item: ((s: F.field_t fd) -> Tot (is_union_item (fd_union_type s) ((fd_union_type_rewrite s).rewrite_from_to (unknown (fd.fd_typedef s)))));
}

[@@noextract_to "krml"]
type union_tag (fd_def: (string -> GTot bool)) : eqtype =
| TagKnown of (option (F.field_t' fd_def))
| TagUnknown

[@@noextract_to "krml"]
let known_union_tag (fd_def: (string -> GTot bool)) : eqtype = option (F.field_t' fd_def)

[@@noextract_to "krml"]
let union_field_type
  (#ft: Type0)
  (fields: F.field_description_t ft)
  (t: known_union_tag fields.fd_def)
: Tot Type
= match t with
  | None -> scalar_t (squash False)
  | Some s -> fields.fd_type s

[@@noextract_to "krml"]
let union_field_typedef
  (#ft: Type0)
  (fields: F.field_description_t ft)
  (t: known_union_tag fields.fd_def)
: Tot (typedef (union_field_type fields t))
= match t with
  | None -> scalar (squash False)
  | Some s -> fields.fd_typedef s

[@@noextract_to "krml"]
let union_field_union_type
  (#ft: Type0)
  (#fields: F.field_description_t ft)
  (fd: union_field_description_t fields)
  (t: known_union_tag fields.fd_def)
: Tot (Ghost.erased (option bool) -> Type)
= match t with
  | None -> union_item_t (scalar_t (squash False)) (unknown (scalar (squash False)))
  | Some s -> fd.fd_union_type s

[@@noextract_to "krml"]
let union_field_union_type_rewrite
  (#ft: Type0)
  (#fields: F.field_description_t ft)
  (fd: union_field_description_t fields)
  (t: known_union_tag fields.fd_def)
: Tot (rewrite_elts (union_field_type fields t) (union_field_union_type fd t None))
= match t with
  | None -> union_item_rewrite (unknown (scalar (squash False)))
  | Some s -> fd.fd_union_type_rewrite s

[@@noextract_to "krml"]
let union_field_union_item
  (#ft: Type0)
  (#fields: F.field_description_t ft)
  (fd: union_field_description_t fields)
  (s: known_union_tag fields.fd_def)
: Tot (is_union_item (union_field_union_type fd s) ((union_field_union_type_rewrite fd s).rewrite_from_to (unknown (union_field_typedef fields s))))
= match s with
  | None -> union_item_gen (scalar (squash False))
  | Some s -> fd.fd_union_item s

[@@noextract_to "krml"; norm_field_attr]
inline_for_extraction // for field_desc.fd_type
noeq
type union_def (t: Type) (ft: Type0) = {
  fields: F.field_description_t ft;
  field_desc: union_field_description_t fields;
  mk: ((tag: Ghost.erased (union_tag fields.fd_def)) -> ((tag': known_union_tag fields.fd_def) -> union_field_union_type field_desc tag' (Some (TagKnown tag' = Ghost.reveal tag))) -> t);
  get_tag: (t -> Ghost.erased (union_tag fields.fd_def));
  get: ((x: t) -> (tag': known_union_tag fields.fd_def) -> union_field_union_type field_desc tag' (Some (TagKnown tag' = Ghost.reveal (get_tag x))));
  get_tag_mk: (tag: Ghost.erased (union_tag fields.fd_def)) -> (phi: ((tag': known_union_tag fields.fd_def) -> union_field_union_type field_desc tag' (Some (TagKnown tag' = Ghost.reveal tag)))) ->
    Lemma
    (get_tag (mk tag phi) == tag)
  ;
  get_mk: (tag: Ghost.erased (union_tag fields.fd_def)) -> (phi: ((tag': known_union_tag fields.fd_def) -> union_field_union_type field_desc tag' (Some (TagKnown tag' = Ghost.reveal tag)))) ->
    (f: known_union_tag fields.fd_def) ->
    Lemma
    (get_tag (mk tag phi) == tag /\
      get (mk tag phi) f == phi f
    )
  ;
  extensionality: (x1: t) -> (x2: t) ->
    (prf_tag: squash (get_tag x1 == get_tag x2)) ->
    ((f: known_union_tag fields.fd_def) -> Lemma (get x1 f == get x2 f)) -> Lemma (x1 == x2);
}

val union_set_field
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
  (f: F.field_t sd.fields)
  (v: sd.fields.fd_type f)
: GTot t

let union_get_case
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
  (x: t)
: GTot (option (F.field_t sd.fields))
= match sd.get_tag x with
  | TagKnown f -> f
  | _ -> None

[@@noextract_to "krml"]
let union_get_field
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
  (u: t)
  (field: F.field_t sd.fields)
: Pure (sd.fields.fd_type field)
    (requires (union_get_case sd u == Some field))
    (ensures (fun _ -> True))
= (sd.field_desc.fd_union_type_rewrite field).rewrite_to_from ((sd.field_desc.fd_union_item field).some_to_none (Ghost.reveal (sd.get_tag u) = TagKnown (Some field)) (sd.get u (Some field)))

val union_get_field_same
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
  (field: F.field_t sd.fields)
  (v: sd.fields.fd_type field)
: Lemma
  (requires (~ (v == unknown (sd.fields.fd_typedef field))))
  (ensures (
    let u = union_set_field sd field v in
    union_get_case sd u == Some field /\
    union_get_field sd u field == v
  ))
  [SMTPatOr [
    [SMTPat (union_get_case sd (union_set_field sd field v))];
    [SMTPat (union_get_field sd (union_set_field sd field v) field)];
  ]]

val union_set_field_same
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
  (s: t)
  (field: F.field_t sd.fields)
: Lemma
  (requires (union_get_case sd s == Some field))
  (ensures (
    union_set_field sd field (union_get_field sd s field) == s
  ))
  [SMTPat (union_set_field sd field (union_get_field sd s field))]

[@@noextract_to "krml"]
val union_typedef
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
: Tot (typedef t)

val union_get_case_unknown
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
: Lemma
  (union_get_case sd (unknown (union_typedef sd)) == None)

val union_set_field_unknown
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
  (field: F.field_t sd.fields)
: Lemma
  (union_set_field sd field (unknown (sd.fields.fd_typedef field)) == unknown (union_typedef sd))

val union_get_case_uninitialized
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
: Lemma
  (union_get_case sd (uninitialized (union_typedef sd)) == None)
  [SMTPat (uninitialized (union_typedef sd))]

module P = Steel.FractionalPermission

val mk_fraction_union_get_case
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
  (s: t)
  (p: P.perm)
: Lemma
  (requires (fractionable (union_typedef sd) s))
  (ensures (
    union_get_case sd (mk_fraction (union_typedef sd) s p) == union_get_case sd s
  ))
  [SMTPat (union_get_case sd (mk_fraction (union_typedef sd) s p))]

val fractionable_union_get_field
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
  (s: t)
  (field: F.field_t sd.fields)
: Lemma
  (requires (union_get_case sd s == Some field))
  (ensures (
    fractionable (union_typedef sd) s <==> fractionable (sd.fields.fd_typedef field) (union_get_field sd s field)
  ))
  [SMTPat (fractionable (union_typedef sd) s); SMTPat (union_get_field sd s field)]

val mk_fraction_union_get_field
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
  (s: t)
  (p: P.perm)
  (field: F.field_t sd.fields)
: Lemma
  (requires (fractionable (union_typedef sd) s /\ union_get_case sd s == Some field))
  (ensures (union_get_field sd (mk_fraction (union_typedef sd) s p) field == mk_fraction (sd.fields.fd_typedef field) (union_get_field sd s field) p))
  [SMTPat (union_get_field sd (mk_fraction (union_typedef sd) s p) field)]

val mk_fraction_union_set_field
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
  (field: F.field_t sd.fields)
  (v: sd.fields.fd_type field)
  (p: P.perm)
: Lemma
  (requires (fractionable (sd.fields.fd_typedef field) v))
  (ensures (
    fractionable (union_typedef sd) (union_set_field sd field v) /\
    mk_fraction (union_typedef sd) (union_set_field sd field v) p == union_set_field sd field (mk_fraction (sd.fields.fd_typedef field) v p)
  ))

val full_union
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
  (s: t)
  (field: F.field_t sd.fields)
: Lemma
  (requires (union_get_case sd s == Some field))
  (ensures (
    full (union_typedef sd) s <==> full (sd.fields.fd_typedef field) (union_get_field sd s field)
  ))
  [SMTPat (full (union_typedef sd) s); SMTPat (union_get_field sd s field)]

val has_union_field
  (#t: Type)
  (#ft: Type0)
  (#sd: union_def t ft)
  (r: ref (union_typedef sd))
  (field: F.field_t sd.fields)
  (r': ref (sd.fields.fd_typedef field))
: Tot vprop

val has_union_field_dup
  (#t: Type)
  (#ft: Type0)
  (#opened: _)
  (#sd: union_def t ft)
  (r: ref (union_typedef sd))
  (field: F.field_t sd.fields)
  (r': ref (sd.fields.fd_typedef field))
: STGhostT unit opened
    (has_union_field r field r')
    (fun _ -> has_union_field r field r' `star` has_union_field r field r')

val has_union_field_inj
  (#opened: _)
  (#t: Type)
  (#ft: Type0)
  (#sd: union_def t ft)
  (r: ref (union_typedef sd))
  (field: F.field_t sd.fields)
  (r1 r2: ref (sd.fields.fd_typedef field))
: STGhostT unit opened
    (has_union_field r field r1 `star` has_union_field r field r2)
    (fun _ -> has_union_field r field r1 `star` has_union_field r field r2 `star` ref_equiv r1 r2)

val has_union_field_equiv_from
  (#opened: _)
  (#t: Type)
  (#ft: Type0)
  (#sd: union_def t ft)
  (r1 r2: ref (union_typedef sd))
  (field: F.field_t sd.fields)
  (r': ref (sd.fields.fd_typedef field))
: STGhostT unit opened
    (has_union_field r1 field r' `star` ref_equiv r1 r2)
    (fun _ -> has_union_field r2 field r' `star` ref_equiv r1 r2)

val has_union_field_equiv_to
  (#opened: _)
  (#t: Type)
  (#ft: Type0)
  (#sd: union_def t ft)
  (r: ref (union_typedef sd))
  (field: F.field_t sd.fields)
  (r1 r2: ref (sd.fields.fd_typedef field))
: STGhostT unit opened
    (has_union_field r field r1 `star` ref_equiv r1 r2)
    (fun _ -> has_union_field r field r2 `star` ref_equiv r1 r2)

val ghost_union_field
  (#opened: _)
  (#t: Type)
  (#ft: Type0)
  (#sd: union_def t ft)
  (#v: Ghost.erased t)
  (r: ref (union_typedef sd))
  (field: F.field_t sd.fields {union_get_case sd v == Some field})
: STGhostT (Ghost.erased (ref (sd.fields.fd_typedef field))) opened
    (pts_to r v)
    (fun r' -> has_union_field r field r' `star` pts_to r' (union_get_field sd v field))

let ghost_union_field_focus
  (#opened: _)
  (#t: Type)
  (#ft: Type0)
  (#sd: union_def t ft)
  (#v: Ghost.erased t)
  (r: ref (union_typedef sd))
  (field: F.field_t sd.fields {union_get_case sd v == Some field})
  (r': ref (sd.fields.fd_typedef field))
: STGhostT unit opened
    (has_union_field r field r' `star` pts_to r v)
    (fun _ -> has_union_field r field r' `star` pts_to r' (union_get_field sd v field))
= let r_ = ghost_union_field r field in
  has_union_field_inj r field r_ r';
  pts_to_equiv r_ r' _;
  drop (has_union_field r field r_);
  drop (ref_equiv r_ r')

[@@noextract_to "krml"] // primitive
val union_field0
  (#t: Type)
  (#t': Type0)
  (#ft: Type0)
  (#sd: union_def t ft)
  (#v: Ghost.erased t)
  (r: ref (union_typedef sd))
  (field: F.field_t sd.fields {union_get_case sd v == Some field})
  (td': typedef t' {
    t' ==  sd.fields.fd_type field /\
    td' == sd.fields.fd_typedef field
  })
: STT (ref td')
    (pts_to r v)
    (fun r' -> has_union_field r field (coerce_eq () r') `star` pts_to r' (Ghost.hide (coerce_eq () (union_get_field sd v field))))

val ununion_field
  (#opened: _)
  (#t: Type)
  (#ft: Type0)
  (#sd: union_def t ft)
  (#v: Ghost.erased t)
  (r: ref (union_typedef sd))
  (field: F.field_t sd.fields {union_get_case sd v == Some field})
  (#v': Ghost.erased (sd.fields.fd_type field))
  (r': ref (sd.fields.fd_typedef field))
: STGhostT unit opened
    (has_union_field r field r' `star` pts_to r' v')
    (fun _ -> has_union_field r field r' `star` pts_to r (union_set_field sd field v'))

// NOTE: we DO NOT support preservation of struct prefixes

[@@noextract_to "krml"] // primitive
val union_switch_field0
  (#t: Type)
  (t': Type0)
  (#ft: Type0)
  (#sd: union_def t ft)
  (#v: Ghost.erased t)
  (r: ref (union_typedef sd))
  (field: F.field_t sd.fields)
  (td': typedef t' {
    t' ==  sd.fields.fd_type field /\
    td' == sd.fields.fd_typedef field
  })
: ST (ref td') // need to write the pcm carrier value, so this cannot be Ghost or Atomic
    (pts_to r v)
    (fun r' -> has_union_field r field (coerce_eq () r') `star` pts_to r' (Ghost.hide (coerce_eq () (uninitialized (sd.fields.fd_typedef field)))))
    (full (union_typedef sd) v)
    (fun r' -> True)
