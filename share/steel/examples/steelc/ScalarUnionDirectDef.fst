module ScalarUnionDirectDef
open Steel.ST.Util
open Steel.ST.C.Types

module U32 = FStar.UInt32
module U16 = FStar.UInt16

noextract
inline_for_extraction
[@@ norm_field_attr]
let u32_or_u16_fields =
  field_description_cons "as_u32" (scalar U32.t) (
  field_description_cons "as_u16" (scalar U16.t) (
  field_description_nil))

(** The type of (union u32_or_u16) values. *)
let u32_or_u16_t = union_t "dummy" u32_or_u16_fields

noextract
let u32_or_u16 : typedef u32_or_u16_t = union0 _ _ _

#push-options "--fuel 0"

#push-options "--print_universes --print_implicits"
// --z3rlimit 30"

(** Switch a case of the union to the u16 case, by writing x to it. *)
val switch_to_u16
  (#v: Ghost.erased u32_or_u16_t)
  (p: ref u32_or_u16)
  (x: U16.t)
: ST unit
    (p `pts_to` v)
    (fun _ -> p `pts_to` union_set_field _ _ _ "as_u16" (mk_scalar x))
    (requires full u32_or_u16 v)
    (ensures fun _ -> True)

#push-options "--fuel 0 --print_bound_var_types"

let switch_to_u16 p x =
  let p16 = union_switch_field  p "as_u16" in
  write p16 x;
  ununion_field p "as_u16" _;
  drop (has_union_field _ _ _);
  return ()

(** Helper function that zeros the memory location pointed to by p. *)
let zero_u32_ref (#v: Ghost.erased (scalar_t U32.t)) (p:ref (scalar U32.t))
: ST unit
  (p `pts_to` v)
  (fun _ -> p `pts_to` mk_scalar 0ul)
  (requires full (scalar U32.t) v)
  (ensures fun _ -> True)
= write p 0ul;
  return ()

(** Given a union in the u32 case, set the u32 to zero. *)
val zero_u32_of_union (#v: Ghost.erased u32_or_u16_t) (p: ref u32_or_u16)
: ST unit
    (p `pts_to` v)
    (fun _ -> p `pts_to` union_set_field _ _ _ "as_u32" (mk_scalar 0ul))
    (requires exists (v0: scalar_t U32.t) . Ghost.reveal v == union_set_field _ _ _ "as_u32" v0 /\ full (scalar U32.t) v0)
    (ensures fun _ -> True)

let zero_u32_of_union #v p =
  let q = union_field p "as_u32" in
  zero_u32_ref q;
  ununion_field p "as_u32" _;
  drop (has_union_field _ _ _);
  return ()
