module MutualStruct

(* While I'm not testing anything really specific to Steel in this
   file, the Steel.ST ref type is marked strictly positive (contrary
   to F*/Low* ref types), which allows me to define mutually recursive
   struct types.  *)

module U64 = FStar.UInt64
module U8 = FStar.UInt8
module SZ = FStar.SizeT

let main () = C.EXIT_SUCCESS

// SUCCESS
noeq
type object1_tagged = {
  object1_tagged_tag: U64.t;
  object1_tagged_payload: Steel.ST.Reference.ref object1;
}
and object1 = {
  object1_type: U8.t;
  object1_payload: object1_tagged;
}

// FAIL to compile: struct types are generated in the wrong order, leading to the compiler complaining about `object2_tagged` being an incomplete type
noeq
type object2 = {
  object2_type: U8.t;
  object2_payload: object2_tagged;
}
and object2_tagged = {
  object2_tagged_tag: U64.t;
  object2_tagged_payload: Steel.ST.Reference.ref object2;
}

// FAIL to compile: same here
noeq
type object3 = {
  object3_type: U8.t;
  object3_map: object3_map;
}
and object3_pair = {
  object3_pair_key: object3;
  object3_pair_payload: object3;
}
and object3_map = {
  object3_map_entry_count: U64.t;
  object3_map_payload: Steel.ST.Reference.ref object3_pair;
}

// FAIL to compile: incomplete type, this time because the monomorphized type instance for `object6_map (ref object6_pair)` is not generated
noeq
type object6_map ([@@@strictly_positive] param: Type0) = {
  object6_map_entry_count: U64.t;
  object6_map_payload: param;
}
noeq
type object6 = {
  object6_type: U8.t;
  object6_map: object6_map (Steel.ST.Reference.ref object6_pair);
}
and object6_pair = {
  object6_pair_key: object6;
  object6_pair_payload: object6;
}
