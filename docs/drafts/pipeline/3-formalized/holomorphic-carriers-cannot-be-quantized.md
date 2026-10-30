# Holomorphic carriers cannot be quantized

- **ID:** holomorphic-carrier-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** Let `Z` be a finite multiset in the open critical strip, invariant under `s ↦ 1 − s`.
  (1) If `h` is holomorphic on the strip and `h(½+it) + h(½−it) = 0` for all real `t`, then
  `Σ_{ρ∈Z} h(ρ) = 0`. (2) If `k` is holomorphic in each slot and `Σ_{a,b∈Z} k(a, b̄)` vanishes on
  every critical configuration, it vanishes on every `Z` also invariant under conjugation.
  (3) If `|h(s) + h(1−s)| ≤ ε` on `Re s = ½` and `≤ M` on `Re s = ½ + Δ` (bounded, continuous on the
  closed strip, holomorphic inside), the quartet `ρ, ρ̄, 1−ρ, 1−ρ̄` with `δ = Re ρ − ½ ∈ [0, Δ]`
  satisfies `|Σ h| ≤ 2 ε^{1−δ/Δ} M^{δ/Δ}`; if `2ε < q` every quartet close enough to the line carries
  less than `q`.

## Paper proof

(1) Put `Φ(s) = h(s) + h(1 − s)`, holomorphic on the strip, which is stable under `s ↦ 1 − s`. Since
`1 − (½ + it) = ½ − it`, the hypothesis says `Φ = 0` on the critical line, so `Φ ≡ 0` on the strip.
Reindexing `Z` by the involution gives `2 Σ_Z h = Σ_Z (h(ρ) + h(1 − ρ)) = Σ_Z Φ(ρ) = 0`.

(2) For critical `s, w` the pairs `P_s = {s, 1 − s}`, `P_w` are critical configurations and
`conj = 1 − ·` on the line. Bilinearity gives
`C(P_s + P_w) − C(P_s) − C(P_w) = K(s, w)`, where
`K(s,w) = Σ_{s'∈{s,1−s}, w'∈{w,1−w}} [k(s',w') + k(1−w', 1−s')]`. So `K = 0` on the product of lines.
For fixed critical `w`, `K(·, w)` is holomorphic on the strip and zero on the line, hence zero; then for
fixed `s` in the strip, `K(s, ·)` is zero on the line, hence on the strip. For general `Z`, conjugation
invariance turns `C(Z)` into `S(k) = Σ_{a,w∈Z} k(a, w)`, and the reflections in each slot and the slot
exchange show each of the eight terms of `K` has double sum `S(k)`. Hence `8 C(Z) = S(K) = 0`.

(3) The quartet sum is `Φ(ρ) + Φ(ρ̄)`, and both points have real part `½ + δ`. Hadamard's three lines
on `½ ≤ Re s ≤ ½ + Δ` bounds each by `ε^{1−δ/Δ} M^{δ/Δ}`. The map `θ ↦ 2ε^{1−θ}M^θ` is continuous
with value `2ε < q` at `0`, which gives the depth `δ₀`.

## Scope

The qualitative entire-weight case is `entire_vanishing_on_criticalLine_eq_zero`
(`RHTower/AnalyticityExcludesBetaSensitivity`). This theorem works on the strip, at configuration
level, covers sesquilinear carriers (Weil forms, squared explicit sums, Montgomery's unconditional
pair form), and quantifies the off-line signal. Families with an infimum over tests (Weil positivity)
are not single carriers and are not covered.

## Lean proof

`RHTower/HolomorphicCarriersCannotBeQuantized.lean` (namespace `RHTower`):

- `linearCarrier_eq_zero`
- `sesquilinearCarrier_eq_zero`
- `norm_quartet_le_interp`
- `exists_depth_without_quantum`

`lake --old env lean` check passes; all four use only `propext`, `Classical.choice`, `Quot.sound`.
Wired into `RHTower.lean`.
