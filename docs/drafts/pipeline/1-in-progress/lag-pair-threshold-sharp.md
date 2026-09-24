# The lag partner-pair positivity has an exact threshold

- **ID:** LAG-PT-001
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) + method no-go
- **Source:** MUST-268, `RHTower/WeilLagFunctionHerglotz.lean`
- **Statement:** for `X > 0`, `σ > 0`, the partner-pair numerator is nonnegative at every ordinate offset exactly when `4a⁴γ² ≤ X²(σ² − a²)`.

## Goal

`re_lagPoleSeries_nonneg` proves `Re G ≥ 0` on `Re s ≥ 13/25` unconditionally, and
`riemannHypothesis_iff_lagPoleSeries_re_nonneg` makes `Re G ≥ 0` on `Re s > 0` equivalent to RH.
The question this card settles is how far the termwise (partner-pair) argument can be pushed, and
what exact input would push it.

## What is proved

Module [`LagPairThresholdSharp`](../../../../formal/GaloisForLFunctions/RHTower/LagPairThresholdSharp.lean):

- `pairNumerator_eq` — the pair numerator is `2σ(X(σ² − a² + A²) + 4a²γA)`.
- `exists_pairNumerator_neg` — if `X²(σ² − a²) < 4a⁴γ²` then the numerator is negative at the vertex
  `A = −2a²γ/X`, where its value is `2σ(X²(σ²−a²) − 4a⁴γ²)/X`.
- `pairNumerator_nonneg_forall_iff` — hence the exact iff. **The termwise wall is exact.**
- `pairCondition_half_of_hyperbolic` — at `σ = 1/2` the condition follows from `β(1−β)γ² ≥ 1/4`,
  using `4(1/4 − b)² ≤ 1/4` and `(b + γ²)² b ≥ γ⁴ b = γ²(bγ²) ≥ γ²/4`.
- `HyperbolicZeroFree`, `hyperbolicZeroFree_of_riemannHypothesis` — the condition and the fact that
  RH implies it (with room: `b = 1/4` and `γ² > 41/2` give `41/8` against the required `1/4`).
- `re_lagPoleSeries_nonneg_half_of_hyperbolic` — under it, `Re G ≥ 0` on `Re s > 1/2`.

Axiom-clean; wired into `GaloisForLFunctions.RHTower`.

## What this says about the lane

The unconditional threshold is `sup_ρ √(a² + 4a⁴γ²/X²)`, and since `|a|` can be as large as `1/2` a
priori, that supremum is at least `1/2`. So `1/2` is the boundary of the method, and `13/25 = 0.52`
is currently `0.008` above it. The exact gap is the hyperbolic zero-free condition. Recorded as
CANNOT-323 / MUST-269.

Reaching `1/2` would **not** prove RH: `re_le_half_add_of_lagPoleSeries_re_nonneg` at `σ₀ = 1/2`
gives only `Re ρ ≤ 1`. The value of the exercise is that it identifies precisely which zero-free
input the Herglotz lane consumes, and confirms that the lane converts positivity into real-part
bounds one-for-one — which is why the memory records it as a receiver.

## Partial closure at large ordinate

[`HyperbolicZeroFreeHigh`](../../../../formal/GaloisForLFunctions/RHTower/HyperbolicZeroFreeHigh.lean)
proves `RHTower.exists_hyperbolic_zeroFree_high`:

```text
∃ T ≥ 3, ∀ β γ, T ≤ |γ| → 0 < β → β < 1 → ζ(β + iγ) = 0 → 1/4 ≤ β(1−β)γ².
```

Mechanism: `Sieve.exists_zero_free_region` gives `β ≤ 1 − c/log|γ|` for `|γ| ≥ T₀`; the functional
equation (`riemannZeta_one_sub_eq_zero_iff`) applied to the partner zero `1 − β − iγ` gives
`β ≥ c/log|γ|`; the two bounds force `c/log|γ| ≤ 1/2`, and `β(1−β) ≥ (c/L)(1 − c/L) ≥ c/(2L)` by the
identity `β(1−β) − a(1−a) = (β−a)(1−a−β)`. Finally `log|γ| ≤ |γ| − 1` turns the requirement
`cγ² ≥ log|γ|/2` into `|γ| ≥ 1/(2c)`.

## Open successor

Close `HyperbolicZeroFree` on the remaining bounded range of ordinates. The threshold `T` above is
existential because `Sieve.exists_zero_free_region` carries an existential `T₀`; with an explicit
zero-free constant valid from `|γ| ≈ 4.53` upward the whole condition would follow, since for
`γ² ≥ 41/2` it only asks `β(1−β) ≥ 1/82`, i.e. `0.0124 ≤ β ≤ 0.9876`.

## Log
- 2026-09-24 — created; exact threshold, sharpness witness, hyperbolic sufficient condition and the
  `1/2` reduction proved in Lean.
