module Example.ImplicitBinders
open Pulse.Lib.Pervasives
module U32 = FStar.UInt32
#push-options "--using_facts_from '* -FStar.Tactics -FStar.Reflection'"

module A = Pulse.Lib.Array
module AS = Pulse.Lib.ArraySwap

```pulse
fn swap (r1 r2:ref U32.t)
  requires 
      pts_to r1 'n1 **
      pts_to r2 'n2
  ensures
      pts_to r1 'n2 **
      pts_to r2 'n1
{
  let x = !r1;
  let y = !r2;
  r1 := y;
  r2 := x
}
```

```pulse
fn test_read (r:ref U32.t)
   requires pts_to r #p 'n
   returns x : U32.t
   ensures pts_to r #p x
{
  !r
}
```

```pulse
fn test_array_swap0
  (a: A.array U32.t)
  (#s: Ghost.erased (Seq.seq U32.t))
requires
  A.pts_to a s ** pure (A.length a == 2)
ensures exists s' .
  A.pts_to a s'
{
  A.pts_to_len a;
  A.pts_to_range_intro a full_perm s;
  A.pts_to_range_upd a 1sz 42ul #0 #(A.length a) #s; // HERE: cannot prove ... in the context (reveal (hide 0)) ...
  A.pts_to_range_elim a _ _;
  ()
}
```

```pulse
fn test_array_swap
  (a: A.array U32.t)
  (#s: Ghost.erased (Seq.seq U32.t))
requires
  A.pts_to a s ** pure (A.length a == 2)
ensures exists s' .
  A.pts_to a s'
{
  A.pts_to_len a;
  A.pts_to_range_intro a full_perm s;
  A.pts_to_range_upd a 1sz 42ul; // HERE: Cannot prove ... in the context (reveal _)
  A.pts_to_range_elim a _ _;
  ()
}
```
