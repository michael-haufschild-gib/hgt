# The finite-section dichotomy: invert ζ at the sample points, or be obstructed

Status: formalized (Lean, unconditional)
Date: 2026-08-09

## The step

`detector-duality-is-exact.md` established that the Báez-Duarte distance *is* the best annihilator pairing,
and named the next target: finite-section floors from detectors at points where `ζ` does **not** vanish.
Annihilating a whole family needs a zero of `ζ`; annihilating `N` generators needs only linear algebra. This
card carries that out and identifies what the resulting floor depends on.

## What is proved

`RHTower/FiniteSectionDetectorFloor.lean`:

* `detectorCombination ρ hρ a = ∑ⱼ aⱼ • bdDetector (1 − ρⱼ)` for sample points `½ < Re ρⱼ < 1`;
* `inner_detectorCombination_bdGen` — the pairing with a generator is
  `∑ⱼ conj(aⱼ)·(−(θ^{ρⱼ} − θ)·ζ(ρⱼ)/ρⱼ)`; `inner_detectorCombination_bdTarget` — with the target it is
  `∑ⱼ conj(aⱼ)/ρⱼ`; `inner_detectorCombination_self` — the squared norm is the Cauchy-kernel quadratic form
  `∑ⱼ∑ₖ conj(aⱼ)aₖ/((ρⱼ − ½) + conj(ρₖ − ½))`, i.e. the corpus's `rightHalfPlaneHardyCauchyGram`;
* `norm_inner_le_norm_mul_bdDist` — the duality bound in Báez-Duarte form;
* **`bdDist_ge_of_detectorCombination`, `bdDist_pos_of_detectorCombination`** — an annihilating combination
  with nonvanishing target pairing gives `‖∑ⱼ conj(aⱼ)/ρⱼ‖/‖w‖ ≤ d(θ)` and `0 < d(θ)`;
* `norm_bdDetector_of_re` — `‖bdDetector (1 − ρ)‖ = 1/√(2 Re ρ − 1)`; `norm_detectorCombination_le` — the
  triangle bound `∑ⱼ ‖aⱼ‖/√(2 Re ρⱼ − 1)`; `norm_sq_detectorCombination` — the exact squared norm as the
  real part of the Cauchy-kernel form; and **`bdDist_ge_triangle_of_detectorCombination`**, the floor with
  the triangle bound in the denominator, so that applying it needs only the coefficients and the real parts
  of the sample points — no Gram computation;
* `exists_ne_zero_mulVec_eq_zero`, `detectorCombination_ne_zero`,
  **`exists_ne_zero_annihilating_detectorCombination`** — with `M > N` sample points a nonzero annihilating
  coefficient vector always exists (rank), and at distinct points it gives a nonzero combination
  (`linearIndependent_bdDetector_zeros`). So annihilation is free; only separation is at stake.

`RHTower/FiniteSectionZetaInterpolation.lean`:

* `mem_span_range_of_forall_inner_eq_zero` — for a **finite** family the duality criterion of
  `DetectorDuality` upgrades from "in the closure" to "in the span": `FiniteDimensional.span_of_finite` plus
  `Submodule.closed_of_finiteDimensional`. General, any `RCLike` field;
* `exists_separating_or_mem_span_range` — the finite dichotomy: either something separates the target from
  the family, or the target is a finite combination of it;
* `sampledGenRow`, `sampledTargetVec`, `inner_sampledGenRow`, `inner_sampledTargetVec` — the sampled
  pairings as vectors of `EuclideanSpace ℂ (Fin M)`;
* **`interpolates_inv_zeta_or_exists_bdDist_floor`** — the capstone:

  > Either there are coefficients `d` with `(∑ᵢ dᵢ(θᵢ^{ρⱼ} − θᵢ))·ζ(ρⱼ) = 1` for **every** sample point,
  > or some detector combination has a nonvanishing target pairing and certifies the explicit floor
  > `‖∑ⱼ conj(aⱼ)/ρⱼ‖/‖w‖ ≤ d(θ)`.

  No hypothesis on `ζ` anywhere;
* `bdDist_pos_of_zeta_eq_zero_at_sample` — the classical zero-based obstruction as the degenerate case: if
  `ζ(ρⱼ₀) = 0` the interpolation equation reads `0 = 1`, so the floor alternative holds.

All 17 declarations are `#print axioms`-clean.

## Why it matters

The finite-section floor is **an interpolation obstruction for `1/ζ`**. Reading the first alternative as
`∑ᵢ dᵢ(θᵢ^{ρⱼ} − θᵢ) = 1/ζ(ρⱼ)` (legitimate wherever `ζ(ρⱼ) ≠ 0`, and the multiplied form above avoids
dividing), the section can escape a floor at a given set of sample points only by inverting `ζ` there. With
`M > N` points this is overdetermined: `M` equations for `N` unknowns.

That reframes the whole lane quantitatively. `d_N → 0` requires that for *every* finite set of sample points
in the strip the `N`-term Müntz system `{θ^s − θ}` inverts `ζ` at those points to within the corresponding
floor. So the rate at which `d_N` can decay is governed by the rate at which `{θᵢ^s − θᵢ}` can approximate
`1/ζ` along `½ < Re s < 1` — an approximation problem about `1/ζ` with no Hilbert space left in it, and the
first formulation in this corpus that makes the *size* of `d_N` (not merely its positivity) an arithmetic
question.

It also explains why the zero-based floors of `BaezDuarteL2Carrier` were never the general phenomenon: they
are the case where the interpolation problem is unsolvable for the trivial reason that its right-hand side
is infinite. Away from zeros the obstruction is quantitative rather than absolute.

## What is not proved

The dichotomy does not decide which alternative holds for any particular data. Producing an unconditional
decaying lower bound (the classical `1/√(log N)` target) requires choosing sample points and bounding the
Cauchy-kernel norm `‖detectorCombination ρ hρ a‖` against the target pairing — i.e. a quantitative
Müntz-inversion estimate. `inner_detectorCombination_self` supplies the norm in closed form and
`norm_detectorCombination_le` a coefficient-only upper bound for it, so that is now a computation with
explicit constants rather than a structural gap. The remaining choice is arithmetic: which sample points and
which kernel coefficients make `‖∑ⱼ conj(aⱼ)/ρⱼ‖` large against `∑ⱼ ‖aⱼ‖/√(2 Re ρⱼ − 1)` while the
annihilation equations hold.
