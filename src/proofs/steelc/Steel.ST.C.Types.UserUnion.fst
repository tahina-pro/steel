module Steel.ST.C.Types.UserUnion

friend Steel.ST.C.Types.Base
friend Steel.ST.C.Types.Union
friend Steel.ST.C.Types.Rewrite

module RW = Steel.ST.C.Model.Rewrite
module RWT = Steel.ST.C.Types.Rewrite
module U = Steel.ST.C.Types.Union
module Pcm = Steel.C.Model.PCM

// open Steel.ST.GenElim1 // I can't use Steel.ST.GenElim because of the "diamond" on init_resolve_tac
// open Steel.ST.C.Types.Base // for ref

let union_set_field_tag
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
  (f: F.field_t sd.fields)
  (v: sd.fields.fd_type f)
: Tot (Ghost.erased (union_tag sd.fields))
= if FStar.StrongExcludedMiddle.strong_excluded_middle (v == unknown (sd.fields.fd_typedef f)) then TagUnknown else TagKnown (Some f)

[@@noextract_to "krml"]
let union_set_field_payload
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
  (f: F.field_t sd.fields)
  (v: sd.fields.fd_type f)
  (tag': known_union_tag sd.fields)
: Tot (union_field_union_type sd.field_desc tag' (Some (TagKnown tag' = Ghost.reveal (union_set_field_tag sd f v))))
= if tag' = Some f
  then (union_field_union_item sd.field_desc tag').none_to_some ((union_field_union_type_rewrite sd.field_desc tag').rewrite_from_to v)
  else (union_field_union_item sd.field_desc tag').none_to_some ((union_field_union_type_rewrite sd.field_desc tag').rewrite_from_to (Pcm.one (union_field_typedef sd.fields tag').pcm))

[@@noextract_to "krml"]
let union_set_field'
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
  (f: F.field_t sd.fields)
  (v: sd.fields.fd_type f)
: Tot t
= sd.mk (union_set_field_tag sd f v) (union_set_field_payload sd f v)

let is_union_item_none_to_some_inj
  (t: (Ghost.erased (option bool) -> Type)) (unkn: Ghost.erased (t None))
  (ui: is_union_item t unkn)
  (x: t None)
: Lemma
    (ui.some_to_none _ (ui.none_to_some x) == x)
    [SMTPat (ui.none_to_some x)]
= ui.none_to_some_inj x

let is_union_item_some_to_none_inj
  (t: (Ghost.erased (option bool) -> Type)) (unkn: Ghost.erased (t None))
  (ui: is_union_item t unkn)
  (b: Ghost.erased bool)
  (x: t (Some (Ghost.reveal b)))
: Lemma
    (Ghost.reveal b == not (FStar.StrongExcludedMiddle.strong_excluded_middle (ui.some_to_none b x == Ghost.reveal unkn)) /\
      ui.none_to_some (ui.some_to_none _ x) == x
    )
    [SMTPat (has_type ui (is_union_item t unkn)); SMTPat (has_type x (t (Some (Ghost.reveal b))))]
= ui.some_to_none_inj b x

let union_def_get_tag_mk
  (#t: Type)
  (#ft: Type0)
  (ud: union_def t ft)
  (tag: Ghost.erased (union_tag ud.fields))
  (phi: ((tag': known_union_tag ud.fields) -> union_field_union_type ud.field_desc tag' (Some (TagKnown tag' = Ghost.reveal tag))))
: Lemma
    (ud.get_tag (ud.mk tag phi) == tag)
    [SMTPat (ud.get_tag (ud.mk tag phi))]
= ud.get_tag_mk tag phi

let union_def_get_mk
  (#t: Type)
  (#ft: Type0)
  (ud: union_def t ft)
  (tag: Ghost.erased (union_tag ud.fields))
  (phi: ((tag': known_union_tag ud.fields) -> union_field_union_type ud.field_desc tag' (Some (TagKnown tag' = Ghost.reveal tag))))
  (f: known_union_tag ud.fields)
: Lemma
    (ud.get_tag (ud.mk tag phi) == tag /\
      ud.get (ud.mk tag phi) f == phi f
    )
    [SMTPat (ud.get (ud.mk tag phi) f)]
= ud.get_mk tag phi f

let model_of_user_f
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
  (x: t)
  (f: U.union_field_t sd.fields)
: Tot (U.union_field_type sd.fields f)
= (union_field_union_type_rewrite sd.field_desc f).rewrite_to_from ((union_field_union_item sd.field_desc f).some_to_none _ (sd.get x f))

let dummy_string : string = ""

let model_of_user
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
  (x: t)
: Tot (U.union_t0 unit dummy_string sd.fields)
= FStar.FunctionalExtensionality.on_dom (U.union_field_t sd.fields) (model_of_user_f sd x)

let field_is_known
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
  (x: U.union_t0 unit dummy_string sd.fields)
  (f: U.union_field_t sd.fields)
: Tot prop
= ~ (x f == unknown (U.union_field_typedef sd.fields f))

let has_known_field
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
  (x: U.union_t0 unit dummy_string sd.fields)
: Tot prop
= (exists (f: U.union_field_t sd.fields) . field_is_known sd x f)

let user_of_model_tag
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
  (x: U.union_t0 unit dummy_string sd.fields)
: Pure (Ghost.erased (union_tag sd.fields))
    (requires True)
    (ensures (fun res -> 
      begin match Ghost.reveal res with
      | TagKnown f -> field_is_known sd x f /\ (forall (f': U.union_field_t sd.fields) . (~ (f == f')) ==> x f' == unknown (U.union_field_typedef sd.fields f'))
      | TagUnknown -> ~ (has_known_field sd x)
      end
    ))
= if FStar.StrongExcludedMiddle.strong_excluded_middle (has_known_field sd x)
  then
    TagKnown (FStar.IndefiniteDescription.indefinite_description_ghost (U.union_field_t sd.fields) (field_is_known sd x))
  else
    TagUnknown

let user_of_model_f
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
  (x: U.union_t0 unit dummy_string sd.fields)
  (tag': known_union_tag sd.fields)
: Tot (union_field_union_type sd.field_desc tag' (Some (TagKnown tag' = Ghost.reveal (user_of_model_tag sd x))))
= ((union_field_union_item sd.field_desc tag').none_to_some ((union_field_union_type_rewrite sd.field_desc tag').rewrite_from_to (x tag')))

let user_of_model
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
  (x: U.union_t0 unit dummy_string sd.fields)
: Tot t
= sd.mk (user_of_model_tag sd x) (user_of_model_f sd x)

#push-options "--z3rlimit 32"

#restart-solver
let user_of_model_rewrite_equiv
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
: Lemma
  (RW.rewrite_forall_from (user_of_model sd) (model_of_user sd) /\
    RW.rewrite_forall_to (user_of_model sd) (model_of_user sd)
  )
=
  rewrite_forall_from_intro (user_of_model sd) (model_of_user sd) (fun x ->
    assert (FStar.FunctionalExtensionality.feq (model_of_user sd (user_of_model sd x)) x)
  );
  rewrite_forall_to_intro (user_of_model sd) (model_of_user sd) (fun x ->
    let prf : squash (sd.get_tag (user_of_model sd (model_of_user sd x)) == sd.get_tag x) =
      assert (sd.get_tag (user_of_model sd (model_of_user sd x)) == user_of_model_tag sd (model_of_user sd x));
      match user_of_model_tag sd (model_of_user sd x) with
      | TagUnknown ->
        begin match sd.get_tag x with
        | TagUnknown -> ()
        | TagKnown f ->
          let f' : U.union_field_t sd.fields = f in
          assert_norm (model_of_user sd x f' == (union_field_union_type_rewrite sd.field_desc f).rewrite_to_from ((union_field_union_item sd.field_desc f).some_to_none _ (sd.get x f))); // FIXME: WHY WHY WHY?
          assert (field_is_known sd (model_of_user sd x) f');
          assert False
        end
      | TagKnown _ -> ()
    in
    sd.extensionality (user_of_model sd (model_of_user sd x)) x () (fun _ -> ())
  )

#pop-options

let user_of_model_rewrite
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
: Tot (RW.rewrite_elts (U.union_t0 unit dummy_string sd.fields) t)
= {
    rewrite_from_to = user_of_model sd;
    rewrite_to_from = model_of_user sd;
    rewrite_equiv = user_of_model_rewrite_equiv sd;
  }

let union_set_field = union_set_field'

let union_get_case_eq
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
  (s: t)
: Lemma
  (union_get_case sd s == U.union_get_case ((user_of_model_rewrite sd).rewrite_to_from s))
  [SMTPat (union_get_case sd s)]
= ()

let union_get_field_eq
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
  (s: t)
  (field: F.field_t sd.fields)
: Lemma
  (requires (union_get_case sd s == Some field))
  (ensures (union_get_field sd s field == U.union_get_field ((user_of_model_rewrite sd).rewrite_to_from s) field))
  [SMTPat (union_get_field sd s field)]
= ()

let union_set_field_eq
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
  (f: F.field_t sd.fields)
  (v: sd.fields.fd_type f)
: Lemma
  (union_set_field sd f v == (user_of_model_rewrite sd).rewrite_from_to (U.union_set_field unit dummy_string sd.fields f v))
  [SMTPat (union_set_field sd f v)]
= sd.extensionality
    (union_set_field sd f v)
    ((user_of_model_rewrite sd).rewrite_from_to (U.union_set_field unit dummy_string sd.fields f v))
    ()
    (fun _ -> ())

let union_get_field_same
  sd field v
= ()

let union_set_field_same
  sd s field
= U.union_set_field_same ((user_of_model_rewrite sd).rewrite_to_from s) field

let union_typedef
  #t sd
= RWT.rewrite_typedef (U.union0 unit dummy_string sd.fields) (user_of_model_rewrite sd)
    
let union_get_case_unknown
  #t sd
= ()

let union_set_field_unknown
  #t sd field
= ()

let union_get_case_uninitialized
  #t sd
= ()

let fractionable_union_eq
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
  (x: t)
: Lemma
  (fractionable (union_typedef sd) x <==> fractionable (U.union0 unit dummy_string sd.fields) ((user_of_model_rewrite sd).rewrite_to_from x))
  [SMTPat (fractionable (union_typedef sd) x)]
= ()

let mk_fraction_union_eq
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
  (x: t)
  (p: perm)
: Lemma
  (requires (fractionable (union_typedef sd) x))
  (ensures (mk_fraction (union_typedef sd) x p == ((user_of_model_rewrite sd).rewrite_from_to (mk_fraction (U.union0 unit dummy_string sd.fields) ((user_of_model_rewrite sd).rewrite_to_from x) p))))
  [SMTPat (mk_fraction (union_typedef sd) x p)]
= ()

#restart-solver
let mk_fraction_union_get_case
  #t sd s p
= ()

let fractionable_union_get_field
  sd s field
= ()

let mk_fraction_union_get_field
  sd s p field
= ()

#restart-solver
let mk_fraction_union_set_field
  sd field v p
= U.mk_fraction_union_set_field unit dummy_string sd.fields field v p

let full_union
  #t sd s field
= ()

let iso_user_to_model
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
: Tot (Steel.C.Model.Connection.isomorphism (union_typedef sd).pcm (U.union_pcm unit dummy_string sd.fields))
= Steel.C.Model.Connection.isomorphism_inverse (RW.rewrite_iso (U.union_pcm unit dummy_string sd.fields) (user_of_model_rewrite sd))

let conn_user_to_model
  (#t: Type)
  (#ft: Type0)
  (sd: union_def t ft)
: Tot (Steel.C.Model.Connection.connection (union_typedef sd).pcm (U.union_pcm unit dummy_string sd.fields))
= Steel.C.Model.Connection.connection_of_isomorphism (iso_user_to_model sd)

[@@__reduce__]
let has_union_field0
  (#t: Type)
  (#ft: Type0)
  (#sd: union_def t ft)
  (r: ref (union_typedef sd))
  (field: F.field_t sd.fields)
  (r': ref (sd.fields.fd_typedef field))
: Tot vprop
= exists_ (fun ru ->
    has_focus_ref r (conn_user_to_model sd) ru `star`
    U.has_union_field ru field r'
  )

let has_union_field
  #t #sd r field r'
= has_union_field0 r field r'

let has_union_field_elim
  (#opened: _)
  (#t: Type)
  (#ft: Type0)
  (#sd: union_def t ft)
  (r: ref (union_typedef sd))
  (field: F.field_t sd.fields)
  (r': ref (sd.fields.fd_typedef field))
: STGhostT (Ghost.erased (ref (U.union0 unit dummy_string sd.fields))) opened
    (has_union_field r field r')
    (fun ru -> has_focus_ref r (conn_user_to_model sd) ru `star`
      U.has_union_field ru field r'
    )
= elim_exists ()

let has_union_field_intro
  (#opened: _)
  (#t: Type)
  (#ft: Type0)
  (#sd: union_def t ft)
  (r: ref (union_typedef sd))
  (ru: ref (U.union0 unit dummy_string sd.fields))
  (field: F.field_t sd.fields)
  (r': ref (sd.fields.fd_typedef field))
: STGhostT unit opened
    (has_focus_ref r (conn_user_to_model sd) ru `star`
      U.has_union_field ru field r')
    (fun ru -> has_union_field r field r')
= noop ();
  rewrite (has_union_field0 r field r') (has_union_field r field r')

let has_union_field_dup
  #t #_ #_ #sd r field r'
= let ru = has_union_field_elim r field r' in
  has_focus_ref_dup r (conn_user_to_model sd) _;
  U.has_union_field_dup _ field r';
  has_union_field_intro r ru field r';
  has_union_field_intro r ru field r'

let has_union_field_inj
  #_ #t #_ #sd r field r1 r2
= let ru1 = has_union_field_elim r field r1 in
  let ru2 = has_union_field_elim r field r2 in
  has_focus_ref_inj r (conn_user_to_model sd) ru1 ru2;
  has_focus_ref_equiv_to r (conn_user_to_model sd) ru1 ru2;
  U.has_union_field_equiv_from ru1 ru2 field r1;
  drop (ref_equiv ru1 ru2);
  U.has_union_field_inj ru2 field r1 r2;
  has_union_field_intro r ru2 field r1;
  has_union_field_intro r ru2 field r2

let has_union_field_equiv_from
  #_ #t #_ #sd r1 r2 field r'
= let ru = has_union_field_elim r1 field r' in
  has_focus_ref_equiv_from r1 (conn_user_to_model sd) ru r2;
  has_union_field_intro r2 ru field r'

let has_union_field_equiv_to
  #_ #t #_ #sd r field r1 r2
= let ru = has_union_field_elim r field r1 in
  U.has_union_field_equiv_to ru field r1 r2;
  has_union_field_intro r ru field r2

let ghost_union_field
  #_ #t #_ #sd #v r field
= let ru = ghost_focus_ref r (U.union0 unit dummy_string sd.fields) (conn_user_to_model sd) in
  let _ = focus_ref_iso r ru (iso_user_to_model sd) in
  let res = U.ghost_union_field ru field in
  has_union_field_intro r ru field res;
  res

[@@noextract_to "krml"] // primitive
let model_union_field0
  (#tn: Type0)
  (#tf: Type0)
  (t': Type0)
  (#n: string)
  (#fields: F.field_description_t tf)
  (#v: Ghost.erased (U.union_t0 tn n fields))
  (r: ref (U.union0 tn n fields))
  (field: F.field_t fields {U.union_get_case v == Some field})
  (td': typedef t' {
    t' ==  fields.fd_type field /\
    td' == fields.fd_typedef field
  })
: STT (ref td')
    (pts_to r v)
    (fun r' -> U.has_union_field r field (coerce_eq () r') `star` pts_to r' (Ghost.hide (coerce_eq () (U.union_get_field v field))))
= U.union_field0 t' r field td'

let union_field0
  #t #t' #_ #sd #v r field td'
= let ru = focus_ref r (U.union0 unit dummy_string sd.fields) (conn_user_to_model sd) in
  let _ = focus_ref_iso r ru (iso_user_to_model sd) in
  let res = model_union_field0 t' ru field td' in
  has_union_field_intro r ru field (coerce_eq () res);
  return res

let ununion_field
  #_ #t #_ #sd #v r field #v' r'
= let ru = has_union_field_elim r field r' in
  U.ununion_field ru field r';
  let _ = unfocus_ref r ru (conn_user_to_model sd) in
  has_union_field_intro r ru field r'

[@@noextract_to "krml"] // primitive
let model_union_switch_field0
  (#tn: Type0)
  (#tf: Type0)
  (t': Type0)
  (#n: string)
  (#fields: F.field_description_t tf)
  (#v: Ghost.erased (U.union_t0 tn n fields))
  (r: ref (U.union0 tn n fields))
  (field: F.field_t fields)
  (td': typedef t' {
    t' ==  fields.fd_type field /\
    td' == fields.fd_typedef field
  })
: ST (ref td') // need to write the pcm carrier value, so this cannot be Ghost or Atomic
    (pts_to r v)
    (fun r' -> U.has_union_field r field (coerce_eq () r') `star` pts_to r' (Ghost.hide (coerce_eq () (uninitialized (fields.fd_typedef field)))))
    (full (U.union0 tn n fields) v)
    (fun r' -> True)
= U.union_switch_field0 t' r field td'

let union_switch_field0
  #_ t' #_ #sd #v r field td'
= let ru = focus_ref r (U.union0 unit dummy_string sd.fields) (conn_user_to_model sd) in
  let _ = focus_ref_iso r ru (iso_user_to_model sd) in
  let res = model_union_switch_field0 t' ru field td' in
  has_union_field_intro r ru field (coerce_eq () res);
  return res
