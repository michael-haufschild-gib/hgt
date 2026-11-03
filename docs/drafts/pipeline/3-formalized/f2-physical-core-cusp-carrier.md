# F2 — physical cores in the stable cusp carrier

- **Stage:** 3-formalized
- **Goal:** Place the actual PM core functions and window lifts in the same parameter-dependent, source-Hecke-stable decay carrier.
- **Theorem [K]:** For `0<Re s<1/2`, `Im s>0`, the actual `mayerPeriodCore s` satisfies `|f(a)|≤C(1+a)^(−2 Re s)`. Every finite word in the actual prime-two and prime-three source operators then has finite upper Haar square and dyadic cusp energy.
- **Dependency:** [Window carrier and branch bounds](../3-formalized/f2-hecke-cusp-decay-carrier.md), individually Lean-audited [K].

## Source estimates

Put `w=2s`, `r=Re w∈(0,1)`. Existing `core_large_bound` gives

`|fieldCore_w(a)| ≤ |ζ(w)|a^(−r)+|scatteringCoefficient(w)|a^(−1)+tailCoefficient(w)a^(−r/2−1)`

for `a≥1`. Each exponent is at most `−r`. Existing `core_small_bound` gives a uniform bound on `0<a≤1`, since its two remaining exponents `1−r` and `1−r/2` are nonnegative. Therefore the field itself lies in the weighted decay carrier.

The actual period core is its Cauchy Mellin convolution. For `a,t>0`,

`1+a ≤ (1+t)(1+a/t)` and `(1+t)^r≤1+t`.

Hence a field bound `|f(x)|≤C(1+x)^(−r)` gives

`|f(a/t)| ≤ C(1+t)(1+a)^(−r)`.

The Cauchy kernel's absolute Mellin moments at `u=0,1` are finite by `cauchyKernel_hasMellin`: `−1<Re u<r+1`. The integral triangle inequality consequently bounds its convolution by

`C(1+a)^(−r) ∫₀∞ |K_w(t)|(1+t) dt/t`.

This uses the actual integral definition, without extending a disc-only period identity to the whole positive line.

## Formalization [K]

`RenormalizedIntersectionTheory/MayerScattering/PhysicalCoresHaveFiniteHeckeCuspEnergy.lean`:

- `mayerPeriodCore_decay_bound`: global weighted decay of the actual Cauchy integral.
- `mayerPeriodCore_measurable`: measurability of the actual joint integrand and its integral.
- `lewisHeckeWord_mayerPeriodCore_decay`: every finite ordered mixed source word retains decay.
- `lewisHeckeWord_mayerPeriodCore_finite_cusp_energy`: both upper Haar square and dyadic cusp energy are finite.

Final individual `lake --old env lean` audit passed without warnings. Both word endpoints depend only on `propext`, `Classical.choice`, `Quot.sound`. Module wired into the umbrella.

No new metric or positivity hypothesis is introduced. This is common-carrier admission, not an identification of the positive integral pairing with the PM Krein form. Constants depend on `s`; convergence of an infinite physical-core sum remains open.
