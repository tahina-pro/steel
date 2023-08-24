module Combinators

```pulse
fn validate_filter
  (v: validator)
  (cond: (U32.t -> bool))
  (r: ref U32.t)
  (#contents: Ghost.erased U32.t)
  requires (R.pts_to r contents)
  returns res : bool
  ensures (R.pts_to r contents)
{
  let test : bool = validate v r;
  if test {
    let x = !r;
    cond x;
  } else {
    false;
  }
}
```

```pulse
fn validate_always
  (r: ref U32.t)
  (#contents: Ghost.erased U32.t)
  requires (R.pts_to r contents)
  returns res : bool
  ensures (R.pts_to r contents)
{
  true;
}
```
