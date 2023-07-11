module Steel.ST.C.Model.Rewrite
include Steel.ST.C.Rewrite

open Steel.C.Model.PCM
open Steel.C.Model.Connection

val rewrite_pcm
  (#from #to: Type)
  (p: pcm from)
  (rewrite: rewrite_elts from to)
: Tot (pcm to)

val rewrite_pcm_composable
  (#from #to: Type)
  (p: pcm from)
  (rewrite: rewrite_elts from to)
  (x1 x2: to)
: Lemma
  (composable (rewrite_pcm p rewrite) x1 x2 <==> composable p (rewrite.rewrite_to_from x1) (rewrite.rewrite_to_from x2))
  [SMTPat (composable (rewrite_pcm p rewrite) x1 x2)]

val rewrite_pcm_op
  (#from #to: Type)
  (p: pcm from)
  (rewrite: rewrite_elts from to)
  (x1 x2: to)
: Lemma
  (requires (composable (rewrite_pcm p rewrite) x1 x2))
  (ensures (op (rewrite_pcm p rewrite) x1 x2 == rewrite.rewrite_from_to (op p (rewrite.rewrite_to_from x1) (rewrite.rewrite_to_from x2))))
  [SMTPat (op (rewrite_pcm p rewrite) x1 x2)]

val rewrite_pcm_one
  (#from #to: Type)
  (p: pcm from)
  (rewrite: rewrite_elts from to)
: Lemma
  (one (rewrite_pcm p rewrite) == rewrite.rewrite_from_to (one p))
  [SMTPat (one (rewrite_pcm p rewrite))]

val rewrite_pcm_refine
  (#from #to: Type)
  (p: pcm from)
  (rewrite: rewrite_elts from to)
  (x: to)
: Lemma
  (p_refine (rewrite_pcm p rewrite) x <==> p_refine p (rewrite.rewrite_to_from x))
  [SMTPat (p_refine (rewrite_pcm p rewrite) x)]

let rewrite_iso
  (#from #to: Type)
  (p: pcm from)
  (rewrite: rewrite_elts from to)
: Tot (isomorphism p (rewrite_pcm p rewrite))
= mkisomorphism
    (mkmorphism
      rewrite.rewrite_from_to
      ()
      (fun _ _ -> ())
    )
    (mkmorphism
      rewrite.rewrite_to_from
      ()
      (fun _ _ -> ())
    )
    ()
    ()
    (fun _ -> ())
    (fun _ -> ())
