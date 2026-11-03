# F2 — a stable decaying cusp carrier

- **Stage:** 3-formalized
- **Goal:** Replace failed compact-support admission with an actual Hecke-stable finite-energy carrier for window lifts.
- **Theorem [K]:** For `Re s>0`, every finite word in the actual `T₂,s,T₃,s`, applied to a smooth window lift, is measurable and satisfies `|f(a)|≤C(1+a)^(−2 Re s)`. Its upper Haar square energy and dyadic cusp energy are finite.
- **Source:** `MayerScattering/HeckeWordsPreserveFiniteCuspEnergy.lean`.

## Paper argument

Put `r=2 Re s≥0`. Suppose `|f(x)|≤C(1+x)^(−r)` for `x>0`, with `C≥0`. A branch with positive numerator `u` and denominator `v` satisfies

`|v^(−2s) f(u/v)| ≤ C v^(−r)(1+u/v)^(−r) = C(u+v)^(−r)`.

In every positive determinant-two or determinant-three branch, `u+v≥1+a`. Thus each branch preserves this bound; summation multiplies its constant by at most four or seven. Induction handles every finite word. All branch maps preserve positive arguments; composition, complex powers and finite sums preserve measurability.

A continuous window lift vanishes outside a compact interval contained in `(0,∞)`. Therefore `(1+a)^r|f(a)|` is bounded initially. No restriction on the window aperture is needed.

For `r>0`, the tail square divided by `a` is bounded by `C² a^(−2r−1)`, which is integrable on `(1,∞)`. The dyadic extractor is a fixed linear combination of `f(2a)` and `f(a)`, so the same bound applies to it.

## Remaining distinction

This is a carrier statement, not complete Weil positivity. The outgoing `a^(1−2s)` wave of completed source periods is annihilated by the dyadic extractor but does not satisfy the decay bound. Its role in a completion must be retained rather than removed through a stronger tail norm.

## Lean audit

- `lewisHeckeT2_decay_bound`, `lewisHeckeT3_decay_bound`
- `windowPeriodLift_decay_bound`
- `lewisHeckeWord_decay_bound`, `lewisHeckeWord_finite_cusp_energy`
- `lewisHeckeWord_windowPeriodLift_decay`
- `lewisHeckeWord_windowPeriodLift_finite_cusp_energy`

Final individual `lake --old env lean` check passed without warnings. Both actual-window endpoints have only `propext`, `Classical.choice`, `Quot.sound` in their transitive axiom audits. Wired into `RenormalizedIntersectionTheory.lean`.

This is the positive stable-carrier survivor of failed compact admission; it covers every finite ordered word in both source correspondences.
