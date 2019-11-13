module Memory
open FStar.Real
module F = FStar.FunctionalExtensionality
open FStar.FunctionalExtensionality

// In the future, we may have other cases of cells
// for arrays and structs
noeq
type cell =
  | Ref : a:Type u#0 ->
          perm:perm ->
          v:a ->
          cell

let addr = nat

/// This is just the core of a memory, about which one can write
/// assertions. At one level above, we'll encapsulate this memory
/// with a freshness counter, a lock store etc.
let mem = addr ^-> option cell

let contains_addr (m:mem) (a:addr)
  : bool
  = Some? (m a)

let select_addr (m:mem) (a:addr{contains_addr m a})
  : cell
  = Some?.v (m a)

let update_addr (m:mem) (a:addr) (c:cell)
  : mem
  = F.on _ (fun a' -> if a = a' then Some c else m a')

let disjoint_addr (m0 m1:mem) (a:addr)
  : prop
  = match m0 a, m1 a with
    | Some (Ref t0 p0 v0), Some (Ref t1 p1 v1) ->
      p0 +. p1 <=. 1.0R /\
      t0 == t1 /\
      v0 == v1

    | Some _, None
    | None, Some _
    | None, None ->
      True

    | _ ->
      False

let ref (a:Type) = addr

let disjoint (m0 m1:mem)
  : prop
  = forall a. disjoint_addr m0 m1 a

let disjoint_sym (m0 m1:mem)
  : Lemma (disjoint m0 m1 <==> disjoint m1 m0)
  = ()

let join (m0:mem) (m1:mem{disjoint m0 m1})
  : mem
  = F.on _ (fun a ->
      match m0 a, m1 a with
      | None, None -> None
      | None, Some x -> Some x
      | Some x, None -> Some x
      | Some (Ref a0 p0 v0), Some (Ref a1 p1 v1) ->
        Some (Ref a0 (p0 +. p1) v0))

let disjoint_join' (m0 m1 m2:mem)
  : Lemma (disjoint m1 m2 /\
           disjoint m0 (join m1 m2) ==>
           disjoint m0 m1 /\
           disjoint m0 m2 /\
           disjoint (join m0 m1) m2 /\
           disjoint (join m0 m2) m1)
          [SMTPat (disjoint m0 (join m1 m2))]
  = ()

let disjoint_join m0 m1 m2 = disjoint_join' m0 m1 m2

let mem_equiv (m0 m1:mem) =
  forall a. m0 a == m1 a

let mem_equiv_eq (m0 m1:mem)
  : Lemma
    (requires
      m0 `mem_equiv` m1)
    (ensures
      m0 == m1)
    [SMTPat (m0 `mem_equiv` m1)]
  = F.extensionality _ _ m0 m1

let join_commutative' (m0 m1:mem)
  : Lemma
    (requires
      disjoint m0 m1)
    (ensures
      join m0 m1 `mem_equiv` join m1 m0)
    [SMTPat (join m0 m1)]
  = ()

let join_commutative m0 m1 = ()

let join_associative' (m0 m1 m2:mem)
  : Lemma
    (requires
      disjoint m1 m2 /\
      disjoint m0 (join m1 m2))
    (ensures
      (disjoint_join m0 m1 m2;
       join m0 (join m1 m2) `mem_equiv` join (join m0 m1) m2))
    [SMTPatOr
      [[SMTPat (join m0 (join m1 m2))];
       [SMTPat (join (join m0 m1) m2)]]]
  = ()

let join_associative (m0 m1 m2:mem) = join_associative' m0 m1 m2

let join_associative2 (m0 m1 m2:mem)
  : Lemma
    (requires
      disjoint m0 m1 /\
      disjoint (join m0 m1) m2)
    (ensures
      disjoint m1 m2 /\
      disjoint m0 (join m1 m2) /\
      join m0 (join m1 m2) `mem_equiv` join (join m0 m1) m2)
    [SMTPat (join (join m0 m1) m2)]
  = ()

////////////////////////////////////////////////////////////////////////////////

module W = FStar.WellFounded

noeq
type hprop : Type u#1 =
  | Emp : hprop
  | Pts_to : #a:Type0 -> r:ref a -> perm:perm -> v:a -> hprop
  | And  : hprop -> hprop -> hprop
  | Or   : hprop -> hprop -> hprop
  | Star : hprop -> hprop -> hprop
  | Wand : hprop -> hprop -> hprop
  | Ex   : #a:Type0 -> (a -> hprop) -> hprop
  | All  : #a:Type0 -> (a -> hprop) -> hprop

let rec interp (p:hprop) (m:mem)
  : Tot prop (decreases p)
  = match p with
    | Emp -> True
    | Pts_to #a r perm v ->
      m `contains_addr` r /\
      (let Ref a' perm' v' = select_addr m r in
       a == a' /\
       v == v' /\
       perm <=. perm')

    | And p1 p2 ->
      interp p1 m /\
      interp p2 m

    | Or  p1 p2 ->
      interp p1 m \/
      interp p2 m

    | Star p1 p2 ->
      exists m1 m2.
        m1 `disjoint` m2 /\
        m == join m1 m2 /\
        interp p1 m1 /\
        interp p2 m2

    | Wand p1 p2 ->
      forall m1.
        m `disjoint` m1 /\
        interp p1 m1 ==>
        interp p2 (join m m1)

    | Ex f ->
      exists x. (W.axiom1 f x; interp (f x) m)

    | All f ->
      forall x. (W.axiom1 f x; interp (f x) m)

let emp = Emp
let pts_to = Pts_to
let h_and = And
let h_or = Or
let star = Star
let wand = Wand
let h_exists = Ex
let h_forall = All

let star_commutative (p1 p2:hprop) = ()

#push-options "--query_stats --z3rlimit_factor 4 --max_fuel 2 --initial_fuel 2 --max_ifuel 2 --initial_ifuel 2"
let star_associative (p1 p2 p3:hprop) = ()
#pop-options

let sel #a (r:ref a) (m:hmem (ptr r))
  : a
  = let Ref _ _ v = select_addr m r in
    v

let sel_lemma #a (r:ref a) (p:perm) (m:hmem (ptr_perm r p))
  = ()

/// The main caveat of this model is that because we're working
/// with proof-irrelevant propositions (squashed proofs), I end up
/// using the indefinite_description axiom to extract witnesses
/// of disjoint memories from squashed proofs of `star`
let split_mem_ghost (p1 p2:hprop) (m:hmem (p1 `Star` p2))
  : GTot (ms:(hmem p1 & hmem p2){
            let m1, m2 = ms in
            disjoint m1 m2 /\
            m == join m1 m2})
  = let open FStar.IndefiniteDescription in
    let (| m1, p |)
      : (m1:mem &
        (exists (m2:mem).
          m1 `disjoint` m2 /\
          m == join m1 m2 /\
          interp p1 m1 /\
          interp p2 m2))
        =
      indefinite_description
        mem
        (fun (m1:mem) ->
          exists (m2:mem).
            m1 `disjoint` m2 /\
            m == join m1 m2 /\
            interp p1 m1 /\
            interp p2 m2)
    in
    let p :
      (exists (m2:mem).
        m1 `disjoint` m2 /\
        m == join m1 m2 /\
        interp p1 m1 /\
        interp p2 m2) = p
    in
    let _ = FStar.Squash.return_squash p in
    let (| m2, _ |) =
      indefinite_description
        mem
        (fun (m2:mem) ->
           m1 `disjoint` m2 /\
           m == join m1 m2 /\
           interp p1 m1 /\
           interp p2 m2)
    in
    (m1, m2)

/// F*'s indefinite_description is only available in the Ghost effect
/// That's to prevent us from mistakenly extracting code that uses the
/// axiom, since, clearly, we can't execute code that invents witnesses
/// from squashed proofs of existentials.
///
/// Here, we're just building a logical model of heaps, so I don't really
/// care about enforcing the ghostiness of indefinite_description.
///
/// So, this axiom explicitly punches a hole in the ghost effect, allowing
/// me to coerce it to Tot
assume
val axiom_ghost_to_tot (#a:Type) (#b:a -> Type) ($f: (x:a -> GTot (b x))) (x:a)
  : Tot (b x)

let split_mem (p1 p2:hprop) (m:hmem (p1 `Star` p2))
  : Tot (ms:(hmem p1 & hmem p2){
            let m1, m2 = ms in
            disjoint m1 m2 /\
            m == join m1 m2})
  = axiom_ghost_to_tot (split_mem_ghost p1 p2) m

let upd #a (r:ref a) (v:a)
           (frame:hprop) (m:hmem (ptr_perm r 1.0R  `Star` frame))
  : Tot (m:hmem (Pts_to r 1.0R v `Star` frame))
  = let m0, m1 = split_mem (ptr_perm r 1.0R) frame m in
    let m0' = update_addr m0 r (Ref a 1.0R v) in
    join m0' m1

////////////////////////////////////////////////////////////////////////////////
// wand
////////////////////////////////////////////////////////////////////////////////
let intro_wand_alt (p1 p2:hprop) (m:mem)
  : Lemma
    (requires
      (forall (m0:hmem p1).
         disjoint m0 m ==>
         interp p2 (join m0 m)))
    (ensures
      interp (wand p1 p2) m)
  = ()

let intro_wand (p q r:hprop) (m:hmem q)
  : Lemma
    (requires
      (forall (m:hmem (p `star` q)). interp r m))
    (ensures
      interp (p `wand` r) m)
  = let aux (m0:hmem p)
      : Lemma
        (requires
          disjoint m0 m)
        (ensures
          interp r (join m0 m))
        [SMTPat (disjoint m0 m)]
      = ()
    in
    intro_wand_alt p r m

let elim_wand (p1 p2:hprop) (m:mem) = ()

////////////////////////////////////////////////////////////////////////////////
// or
////////////////////////////////////////////////////////////////////////////////

let intro_or_l (p1 p2:hprop) (m:hmem p1)
  : Lemma (interp (h_or p1 p2) m)
  = ()

let intro_or_r (p1 p2:hprop) (m:hmem p2)
  : Lemma (interp (h_or p1 p2) m)
  = ()

let or_star (p1 p2 p:hprop) (m:hmem ((p1 `star` p) `h_or` (p2 `star` p)))
  : Lemma (interp ((p1 `h_or` p2) `star` p) m)
  = ()

let elim_or (p1 p2 q:hprop) (m:hmem (p1 `h_or` p2))
  : Lemma (((forall (m:hmem p1). interp q m) /\
            (forall (m:hmem p2). interp q m)) ==> interp q m)
  = ()


////////////////////////////////////////////////////////////////////////////////
// and
////////////////////////////////////////////////////////////////////////////////

let intro_and (p1 p2:hprop) (m:mem)
  : Lemma (interp p1 m /\
           interp p2 m ==>
           interp (p1 `h_and` p2) m)
  = ()

let elim_and (p1 p2:hprop) (m:hmem (p1 `h_and` p2))
  : Lemma (interp p1 m /\
           interp p2 m)
  = ()


////////////////////////////////////////////////////////////////////////////////
// h_exists
////////////////////////////////////////////////////////////////////////////////

let intro_exists (#a:_) (x:a) (p : a -> hprop) (m:hmem (p x))
  : Lemma (interp (h_exists p) m)
  = ()

let elim_exists (#a:_) (p:a -> hprop) (q:hprop) (m:hmem (h_exists p))
  : Lemma
    ((forall (x:a). interp (p x) m ==> interp q m) ==>
     interp q m)
  = ()


////////////////////////////////////////////////////////////////////////////////
// h_forall
////////////////////////////////////////////////////////////////////////////////

let intro_forall (#a:_) (p : a -> hprop) (m:mem)
  : Lemma ((forall x. interp (p x) m) ==> interp (h_forall p) m)
  = ()

let elim_forall (#a:_) (p : a -> hprop) (m:hmem (h_forall p))
  : Lemma ((forall x. interp (p x) m) ==> interp (h_forall p) m)
  = ()


////////////////////////////////////////////////////////////////////////////////
// emp
////////////////////////////////////////////////////////////////////////////////

let intro_emp (m:mem)
  : Lemma (interp emp m)
  = ()

////////////////////////////////////////////////////////////////////////////////


let intro_pts_to (#a:_) (x:ref a) (p:perm) (v:a) (m:mem)
  : Lemma
    (requires
       m `contains_addr` x /\
       (let Ref a' perm' v' = select_addr m x in
        a == a' /\
        v == v' /\
        p <=. perm'))
     (ensures
       interp (pts_to x p v) m)
  = ()

let intro_star (p q:hprop) (mp:hmem p) (mq:hmem q)
  : Lemma
    (requires
      disjoint mp mq)
    (ensures
      interp (p `star` q) (join mp mq))
  = ()

#push-options "--z3rlimit_factor 4 --max_fuel 2 --max_ifuel 2  --initial_fuel 2 --initial_ifuel 2"
let rec affine_star_aux (p:hprop) (m:mem) (m':mem { disjoint m m' })
  : Lemma
    (ensures interp p m ==> interp p (join m m'))
    [SMTPat (interp p (join m m'))]
  = match p with
    | Emp -> ()

    | Pts_to _ _ _ -> ()

    | And p1 p2 -> affine_star_aux p1 m m'; affine_star_aux p2 m m'

    | Or p1 p2 -> affine_star_aux p1 m m'; affine_star_aux p2 m m'

    | Star p1 p2 ->
      let aux (m1 m2:mem) (m':mem {disjoint m m'})
        : Lemma
          (requires
            disjoint m1 m2 /\
            m == join m1 m2 /\
            interp p1 m1 /\
            interp p2 m2)
          (ensures interp (Star p1 p2) (join m m'))
          [SMTPat (interp (Star p1 p2) (join (join m1 m2) m'))]
        = affine_star_aux p2 m2 m';
          // assert (interp p2 (join m2 m'));
          affine_star_aux p1 m1 (join m2 m');
          // assert (interp p1 (join m1 (join m2 m')));
          join_associative m1 m2 m';
          // assert (disjoint m1 (join m2 m'));
          intro_star p1 p2 m1 (join m2 m')
      in
      ()

    | Wand p q ->
      let aux (mp:hmem p)
        : Lemma
          (requires
            disjoint mp (join m m') /\
            interp (wand p q) m)
          (ensures (interp q (join mp (join m m'))))
          [SMTPat  ()]
        = disjoint_join mp m m';
          assert (disjoint mp m);
          assert (interp q (join mp m));
          join_associative mp m m';
          affine_star_aux q (join mp m) m'
      in
      assert (interp (wand p q) m ==> interp (wand p q) (join m m'))

    | Ex #a f ->
      let aux (x:a)
        : Lemma (ensures interp (f x) m ==> interp (f x) (join m m'))
                [SMTPat ()]
        = W.axiom1 f x;
          affine_star_aux (f x) m m'
      in
      ()

    | All #a f ->
      let aux (x:a)
        : Lemma (ensures interp (f x) m ==> interp (f x) (join m m'))
                [SMTPat ()]
        = W.axiom1 f x;
          affine_star_aux (f x) m m'
      in
      ()
#pop-options

let affine_star (p q:hprop) (m:mem)
  : Lemma
    (ensures (interp (p `star` q) m ==> interp p m))
  = ()

////////////////////////////////////////////////////////////////////////////////
noeq
type t = {
  ctr: nat;
  mem: mem;
  properties: squash (
    forall i. i >= ctr ==> mem i == None
  )
}

let alloc (#a:_) (v:a) (frame:hprop) (m:t{interp frame m.mem})
  : (x:ref a &
     m:t { interp (pts_to x 1.0R v `star` frame) m.mem} )
  = let x : ref a = m.ctr in
    let cell = Ref a 1.0R v in
    let mem : mem = F.on _ (fun i -> if i = x then Some cell else None) in
    assert (disjoint mem m.mem);
    assert (mem `contains_addr` x);
    assert (select_addr mem x == cell);
    let mem' = join mem m.mem in
    intro_pts_to x 1.0R v mem;
    assert (interp (pts_to x 1.0R v) mem);
    assert (interp frame m.mem);
    intro_star (pts_to x 1.0R v) frame mem m.mem;
    assert (interp (pts_to x 1.0R v `star` frame) mem');
    let t = {
      ctr = x + 1;
      mem = mem';
      properties = ()
    } in
    (| x, t |)
