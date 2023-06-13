module ArraySwap
module T = FStar.Tactics
module PM = Pulse.Main
open Steel.ST.Util 
open Steel.FractionalPermission
module U32 = FStar.UInt32
open Pulse.Steel.Wrapper
module A = Steel.ST.Array
module US = FStar.SizeT
module R = Steel.ST.Reference

#set-options "--ide_id_info_off"

#push-options "--query_stats"
#restart-solver

```pulse
fn array_swap_case_1(#t: Type0) (#s: Ghost.erased (Seq.seq t)) (a: A.array t) (n: US.t) (l: US.t)
  requires (
    A.pts_to a full_perm s `star`
    pure (
      US.v n == A.length a /\
      US.v l + US.v l <= US.v n
    )
  )
  ensures exists s' . (
    A.pts_to a full_perm s'
  )
{
  let mut pi = 0sz;
  while (let i = !pi; (i `US.lt` l))
  invariant b . exists i s' . (
    A.pts_to a full_perm s' `star`
    R.pts_to pi full_perm i `star`
    pure (eq2_prop #bool b ((i `US.lt` l)))
  ) {
    let i = !pi;
    let save = a.(i);
    let mut pj = i `US.add` l;
    while (let j = !pj; (j `US.lt` n))
    invariant b . exists i j s' . (
      A.pts_to a full_perm s' `star`
      R.pts_to pi full_perm i `star`
      R.pts_to pj full_perm j `star`
      pure (
        US.v j % US.v l == US.v i /\
        eq2_prop #bool b ((j `US.lt` n))
      )
    ) {
      let j = !pj;
      let x = a.(j);
      (a.(j `US.sub` l) <- x);
      pj := j `US.add` l;
      ()
    };
    let i' = (US.add (US.sub n l) i);
    (a.(i') <- save);
    pi := i `US.add` 1sz;
    ()
  };
  ()
}   
```
