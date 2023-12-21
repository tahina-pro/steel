module ParallelIncrement
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32
module L = Pulse.Lib.SpinLock
module GR = Pulse.Lib.GhostReference
```pulse
fn increment (x: ref nat)
             (l:L.lock (exists* v. pts_to x #one_half v))
requires pts_to x #one_half 'i
ensures pts_to x #one_half ('i + 1)
 {
    let v = !x;
    L.acquire l;
    gather x;
    with p _v. rewrite (pts_to x #p _v) as (pts_to x _v);
    x := (v + 1);
    share x;
    with p _v. rewrite (pts_to x #p _v) as (pts_to x #one_half _v);
    L.release l;
    with p _v. rewrite (pts_to x #p _v) as (pts_to x #one_half _v);
}
```

#push-options "--print_implicits --ext 'pulse:env_on_err' --print_full_names"
```pulse
fn increment_f (x: ref nat)
               (#pred #qpred: nat -> vprop)
               (l:L.lock (exists* v. pts_to x #one_half v ** pred v))
               (f: (v:nat -> stt_ghost unit emp_inames 
                        (pred v ** qpred v ** pts_to x #one_half (v + 1))
                        (fun _ -> pred (v + 1) ** qpred (v + 1) ** pts_to x #one_half (v + 1))))
requires pts_to x #one_half 'i ** qpred 'i
ensures pts_to x #one_half ('i + 1) ** qpred ('i + 1)
 {
    let vx = !x;
    rewrite (qpred 'i) as (qpred vx);
    L.acquire l;
    gather x;
    with p v. rewrite (pts_to x #p v) as (pts_to x v);
    x := (vx + 1);
    share x;
    with p _v. rewrite (pts_to x #p _v) as (pts_to x #one_half _v);
    with _v. rewrite (pred _v) as (pred vx);
    f vx;
    L.release l;
    with p _v. rewrite (pts_to x #p _v) as (pts_to x #one_half _v);
    rewrite (qpred (vx + 1)) as (qpred ('i + 1));
}
```

```pulse
fn increment_f2 (x: ref int)
                (#pred #qpred: int -> vprop)
                (l:L.lock (exists* v. pts_to x v ** pred v))
                (f: (v:int -> vq:int -> stt_ghost unit emp_inames 
                        (pred v ** qpred vq ** pts_to x (v + 1))
                        (fun _ -> pred (v + 1) ** qpred (vq + 1) ** pts_to x (v + 1))))
requires qpred 'i
ensures qpred ('i + 1)
 {
    L.acquire l;
    let vx = !x;
    with _v. rewrite (pred _v) as (pred vx);
    x := vx + 1;
    f vx 'i;
    L.release l;
}
```

#push-options "--warn_error -249"
```pulse
fn parallel_increment
        (x: ref int)
requires pts_to x 'i
ensures pts_to x ('i + 2)
{
    let left = GR.alloc #int 0;
    let right = GR.alloc #int 0;
    GR.share left;
    GR.share right;
    let lock = L.new_lock (
      exists* (v:int).
        pts_to x v **
        (exists* (vl vr:int).
          GR.pts_to left #(half_perm full_perm) vl **
          GR.pts_to right #(half_perm full_perm) vr **
          pure (v == 'i + vl + vr))
    );
    ghost
    fn step
        (lr:GR.ref int)
        (b:bool { if b then lr == left else lr == right })
        (v vq:int)
      requires 
        (exists* (vl vr:int).
            GR.pts_to left #(half_perm full_perm) vl **
            GR.pts_to right #(half_perm full_perm) vr **
            pure (v == 'i + vl + vr)) **
        GR.pts_to lr #(half_perm full_perm) vq **
        pts_to x (v + 1)
      ensures
        (exists* (vl vr:int).
            GR.pts_to left #(half_perm full_perm) vl **
            GR.pts_to right #(half_perm full_perm) vr **
            pure (v + 1 == 'i + vl + vr)) **
        GR.pts_to lr #(half_perm full_perm) (vq + 1) **
        pts_to x (v + 1)
    { 
      if b
      {
        with _p _v. rewrite (GR.pts_to lr #_p _v) as (GR.pts_to left #_p _v);
        GR.gather left;
        with _p _v. rewrite (GR.pts_to left #_p _v) as (GR.pts_to left _v);
        GR.( left := vq + 1 );
        GR.share left;      
        with _p _v. rewrite (GR.pts_to left #_p _v) as (GR.pts_to lr #_p _v);
      }
      else
      {
        with _p _v. rewrite (GR.pts_to lr #_p _v) as (GR.pts_to right #_p _v);
        GR.gather right;
        with _p _v. rewrite (GR.pts_to right #_p _v) as (GR.pts_to right _v);
        GR.( right := vq + 1 );
        GR.share right;      
        with _p _v. rewrite (GR.pts_to right #_p _v) as (GR.pts_to lr #_p _v);
      }
    };

    parallel
    requires GR.pts_to left #(half_perm full_perm) 0
         and GR.pts_to right #(half_perm full_perm) 0
    ensures  GR.pts_to left #(half_perm full_perm) 1
         and GR.pts_to right #(half_perm full_perm) 1
    { increment_f2 x lock (step left true) }
    { increment_f2 x lock (step right false) };

    L.acquire lock;
    GR.gather left;
    GR.gather right;
    with _p _v. rewrite (GR.pts_to left #_p _v) as (GR.pts_to left _v);
    with _p _v. rewrite (GR.pts_to right #_p _v) as (GR.pts_to right _v);
    GR.free left;
    GR.free right;
}
```

assume
val atomic_increment (r:ref int) (#i:erased int)
  : stt_atomic unit emp_inames 
    (pts_to r i)
    (fun _ -> pts_to r (i + 1))
     
module F = Pulse.Lib.FlippableInv

```pulse
fn atomic_increment_f2
        (x: ref int)
        (#pred #qpred: int -> vprop)
        (l:inv (exists* v. pts_to x v ** pred v))
        (f: (v:int -> vq:int -> stt_ghost unit emp_inames 
                  (pred v ** qpred vq ** pts_to x (v + 1))
                  (fun _ -> pred (v + 1) ** qpred (vq + 1) ** pts_to x (v + 1))))
requires qpred 'i
ensures qpred ('i + 1)
{
  with_invariants l {
    with v. _;
    atomic_increment x;
    f v 'i;
  }
}
```

open Pulse.Lib.Stick.Util
module FA = Pulse.Lib.Forall.Util
module I = Pulse.Lib.Stick.Util
```pulse
fn atomic_increment_f3
        (x: ref int)
        (#pred #qpred: int -> vprop)
        (l:inv (exists* v. pts_to x v ** pred v))
requires
  qpred 'i **
  (forall* v vq.
     (pred v ** qpred vq ** pts_to x (v + 1)) @==>
     (pred (v + 1) ** qpred (vq + 1) ** pts_to x (v + 1)))
ensures qpred ('i + 1)
{
  with_invariants l {
    with v. _;
    atomic_increment x;
    FA.elim #_ #(fun v -> forall* vq. (pred v ** qpred vq ** pts_to x (v + 1)) @==>
                                      (pred (v + 1) ** qpred (vq + 1) ** pts_to x (v + 1))) v;

    FA.elim #_ #(fun vq -> (pred v ** qpred vq ** pts_to x (v + 1)) @==>
                           (pred (v + 1) ** qpred (vq + 1) ** pts_to x (v + 1))) 'i;
    I.elim _ _;
  }
}
```
#pop-options
```pulse
fn atomic_increment_f4
        (x: ref int)
        (#invp : vprop)
        (#pred #qpred: int -> vprop)
        (l:inv invp)
        (f: (v:int -> vq:int -> stt_ghost unit emp_inames 
                  (pred v ** qpred vq ** pts_to x (v + 1))
                  (fun _ -> pred (v + 1) ** qpred (vq + 1) ** pts_to x (v + 1))))
requires
  qpred 'i **
  (invp @==> (exists* v. pts_to x v ** pred v)) ** 
  ((exists* v. pts_to x v ** pred v) @==> invp)
ensures qpred ('i + 1)
{
  with_invariants l {
    I.elim invp _;
    atomic_increment x;
    f _ 'i;
    I.elim (exists* v. pts_to x v ** pred v) invp;
  }
}
```

assume
val atomic_read (r:ref int) (#i:erased int)
  : stt_atomic int emp_inames 
    (pts_to r #(half_perm full_perm) i)
    (fun v -> pts_to r #(half_perm full_perm) v ** pure (reveal i == v))

let cond b (p q:vprop) = if b then p else q
assume
val elim_cond_true (b:bool) (p q:vprop)
  : stt_ghost unit emp_inames 
    (cond b p q ** pure (b == true))
    (fun _ -> p)

assume
val elim_cond_false (b:bool) (p q:vprop)
  : stt_ghost unit emp_inames 
    (cond b p q ** pure (b == false))
    (fun _ -> q)

assume
val intro_cond_false (p q:vprop)
  : stt_ghost unit emp_inames 
    q (fun _ -> cond false p q)

assume
val cas (r:ref int) (u v:int) (#i:erased int)
  : stt_atomic bool emp_inames 
    (pts_to r i)
    (fun b ->
      cond b (pts_to r v ** pure (reveal i == u)) 
             (pts_to r i))

let trigger (x:'a) = emp

```pulse
fn atomic_increment_f5
        (x: ref int)
        (#invp #tok : vprop)
        (#pred #qpred: int -> vprop)
        (l:inv invp)
        (elim_inv: 
          (_:unit -> stt_ghost unit emp_inames invp (fun _ ->
                    ((exists* v. pts_to x v ** pred v) ** tok))))
        (intro_inv:
            (_:unit -> stt_ghost unit emp_inames 
                        ((exists* v. pts_to x v ** pred v) ** tok)
                         (fun _ -> invp)))
        (f: (v:int -> vq:int -> stt_ghost unit emp_inames 
                  (pred v ** qpred vq ** pts_to x (v + 1))
                  (fun _ -> pred (v + 1) ** qpred (vq + 1) ** pts_to x (v + 1))))
requires qpred 'i
ensures qpred ('i + 1)
{
  fn read ()
  requires emp
  returns v:int
  ensures emp
  {
    0
    //This doesn't work at the return type, complaining that it should be non-informative
    // with_invariants l {
        // elim_inv ();
        // with i. _;
        // share x;
        // let v = atomic_read x;
        // gather x;
        // with _p. rewrite (pts_to x #_p v) as (pts_to x i);
        // intro_inv ();
        // v
    // }
  };
  let mut continue = true;
  fold (cond true (qpred 'i) (qpred ('i + 1)));
  while (
    with _b. _;
    let b = !continue;
    rewrite each _b as b;
    b
  )
  invariant b.
    pts_to continue b **
    cond b (qpred 'i) (qpred ('i + 1))
  {
    let v = read ();
    with_invariants l {
        elim_inv ();
        let b = cas x v (v + 1);
        if b
        {
          elim_cond_true b _ _;
          elim_cond_true true _ _;
          f _ _;
          // continue := false; //local variable assignment is considered non-atomic
          intro_cond_false (qpred 'i) (qpred ('i + 1));
          intro_inv ();
          // show_proof_state; //the proof is done here, except for the assignment to continue
          admit()
        }
        else
        {
          with p q. rewrite (cond b p q) as q;
          intro_inv ();
        }
    }
  };
  with p q. unfold (cond false p q);
}
 
```


assume
val token : Type0

assume
val cancellable (t:token) (v:vprop) : vprop

assume
val active
     (p:perm) 
     (c:token)
 : vprop

assume
val take (#p #t:_) (v:vprop) :
  stt_ghost unit emp_inames
    (cancellable t v ** active p t)
    (fun _ -> v ** active p t)

assume
val restore (#p #t:_) (v:vprop) :
  stt_ghost unit emp_inames
    (v ** active p t)
    (fun _ -> cancellable t v ** active p t)
    

assume
val cancel (#t:_) (v:vprop) :
  stt_ghost unit emp_inames
    (cancellable t v ** active full_perm t)
    (fun _ -> cancellable t v ** v)

assume
val create (v:vprop) :
  stt_ghost (erased token) emp_inames v 
          (fun t -> cancellable t v ** active full_perm t)

assume
val share (#p:_) (t:_) :
  stt_ghost unit emp_inames
    (active p t)
    (fun _ -> active (half_perm p) t ** active (half_perm p) t)

assume
val gather (#p:_) (t:_) :
  stt_ghost unit emp_inames
    (active (half_perm p) t ** active (half_perm p) t)
    (fun _ -> active p t)
 
 assume
 val cancel_inv (#t #v:_) (i:inv (cancellable t v)) :
  stt_ghost unit emp_inames
    (active full_perm t)
    (fun _ -> v)


```pulse
fn atomic_increment_f6
        (x: ref int)
        (#p:_) (#t:erased token)
        (#pred #qpred: int -> vprop)
        (l:inv (cancellable t (exists* v. pts_to x v ** pred v)))
        (f: (v:int -> vq:int -> stt_ghost unit emp_inames 
                  (pred v ** qpred vq ** pts_to x (v + 1))
                  (fun _ -> pred (v + 1) ** qpred (vq + 1) ** pts_to x (v + 1))))
requires qpred 'i ** active p t
ensures qpred ('i + 1) ** active p t
{
  with_invariants l {
    take _;
    atomic_increment x;
    f _ 'i;
    restore (exists* v. pts_to x v ** pred v)
  }
}
```


```pulse
fn parallel_increment_inv
        (x: ref int)
requires pts_to x 'i
ensures pts_to x ('i + 2)
{
    let left = GR.alloc #int 0;
    let right = GR.alloc #int 0;
    GR.share left;
    GR.share right;
    let tok = create (
      exists* (v:int).
          pts_to x v **
          (exists* (vl vr:int).
            GR.pts_to left #(half_perm full_perm) vl **
            GR.pts_to right #(half_perm full_perm) vr **
            pure (v == 'i + vl + vr))

    );
    share tok; 
    let inv = new_invariant' (cancellable tok _);
    ghost
    fn step
        (lr:GR.ref int)
        (b:bool { if b then lr == left else lr == right })
        (v vq:int)
      requires 
        (exists* (vl vr:int).
            GR.pts_to left #(half_perm full_perm) vl **
            GR.pts_to right #(half_perm full_perm) vr **
            pure (v == 'i + vl + vr)) **
        GR.pts_to lr #(half_perm full_perm) vq **
        pts_to x (v + 1)
      ensures
        (exists* (vl vr:int).
            GR.pts_to left #(half_perm full_perm) vl **
            GR.pts_to right #(half_perm full_perm) vr **
            pure (v + 1 == 'i + vl + vr)) **
        GR.pts_to lr #(half_perm full_perm) (vq + 1) **
        pts_to x (v + 1)
    { 
      if b
      {
        with _p _v. rewrite (GR.pts_to lr #_p _v) as (GR.pts_to left #_p _v);
        GR.gather left;
        with _p _v. rewrite (GR.pts_to left #_p _v) as (GR.pts_to left _v);
        GR.( left := vq + 1 );
        GR.share left;      
        with _p _v. rewrite (GR.pts_to left #_p _v) as (GR.pts_to lr #_p _v);
      }
      else
      {
        with _p _v. rewrite (GR.pts_to lr #_p _v) as (GR.pts_to right #_p _v);
        GR.gather right;
        with _p _v. rewrite (GR.pts_to right #_p _v) as (GR.pts_to right _v);
        GR.( right := vq + 1 );
        GR.share right;      
        with _p _v. rewrite (GR.pts_to right #_p _v) as (GR.pts_to lr #_p _v);
      }
    };

    parallel
    requires GR.pts_to left #(half_perm full_perm) 0 **
             active (half_perm full_perm) tok
         and GR.pts_to right #(half_perm full_perm) 0 **
             active (half_perm full_perm) tok
    ensures  GR.pts_to left #(half_perm full_perm) 1 **
             active (half_perm full_perm) tok
         and GR.pts_to right #(half_perm full_perm) 1 **
             active (half_perm full_perm) tok
    { atomic_increment_f6 x inv (step left true) }
    { atomic_increment_f6 x inv (step right false) };

    gather tok;
    cancel_inv inv;
    GR.gather left;
    GR.gather right;
    with _p _v. rewrite (GR.pts_to left #_p _v) as (GR.pts_to left _v);
    with _p _v. rewrite (GR.pts_to right #_p _v) as (GR.pts_to right _v);
    GR.free left;
    GR.free right;

}
```
