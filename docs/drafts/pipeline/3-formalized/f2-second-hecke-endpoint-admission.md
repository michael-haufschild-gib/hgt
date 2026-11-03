# The second Hecke step detects the window endpoint

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `MayerScattering/TheSecondHeckeStepSeesTheWindowEndpoint.lean`.
- **Statement:** For `A<log(4/3)`, a window lift has a compact second Hecke image at the upper cusp iff its original window vanishes near endpoint `0`. Every positive window contains one smooth test with compact first image and noncompact second image at every complex parameter.

## Exact admission law

If `f` vanishes above `1≤R<4/3`, then for `x>R/(2−R)`,

`T₂,s f(x)=2^(−2s)f(x/2)`.

The other three arguments exceed `R`. The first image has a finite upper cutoff because `R<2`. Applying the first-step cusp criterion to that image gives

`T₂,s² f has a finite upper cutoff`

iff `f` vanishes on a left germ at `1`.

For `f=windowPeriodLift s H`, inversion identifies `f(x)=0`, `0<x<1`, with `H(log x)=0`. Hence, for `H` supported in `[−A,0]`, `A<log(4/3)`,

`T₂,s² f has a finite upper cutoff ↔ ∃ε>0, H=0 on (−ε,0)`.

No resonance or sign assumption enters; `s` is any complex parameter.

## Universal two-step obstruction

For any `A>0`, choose `B=min(A,log(4/3))/2`. A smooth test with nonzero set exactly `(-B,0)` lies in stage `A`. Its first image has finite support at the upper cusp since `B<log2`. Its second image has no such cutoff, since the test is nonzero on every left neighbourhood of `0`. The same test works for every `s∈ℂ`.

The obstruction concerns compact support. It gives no assertion of divergent cusp energy. Its positive survivor is the exact endpoint-germ admission law.

## Lean audit

- `lewisHeckeT2_eq_half_near_two`
- `lewisHeckeT2_twice_upper_cutoff_iff`
- `hecke_windowPeriodLift_twice_upper_cutoff_iff`
- `exists_windowTest_hecke_cutoff_but_twice_no_cutoff`

Final individual `lake --old env lean` check passed without warnings. All three printed endpoint audits use only `propext`, `Classical.choice`, `Quot.sound`. Imported by `RenormalizedIntersectionTheory.lean`.
