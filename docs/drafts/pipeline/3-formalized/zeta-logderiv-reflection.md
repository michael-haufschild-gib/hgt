# Reflection formula for the logarithmic derivative of zeta

- **ID:** zeta-logderiv-reflection
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** fallout of the archimedean off-poles layer (see `shift-divisor-value-reflection.md`)
- **Statement:** `ζ'/ζ(s) + ζ'/ζ(1−s) = log π − ψ(s/2)/2 − ψ((1−s)/2)/2`, off the poles and away from
  the zeros at `s` and `1−s`.

## Goal

The corpus had no reflection identity for `logDeriv riemannZeta` at all — checked by search before
building. It had the completed reciprocity `logDeriv ξ(1−s) = −logDeriv ξ(s)` and a strip-local
archimedean weld buried inside a curvature computation, but nothing joining them. This card records
the join and what it yields on the critical line.

## The chain

Each link is a specialization of the one above it; none re-proves the others.

| Theorem | Region |
|---|---|
| `seamFluxCochain_eq_infinitePrimeFlux_add_archimedean_off_poles` | plane minus `{1}` and the ladder `−2n` |
| `logDeriv_riemannZeta_add_reflect_off_poles` | same, plus the reflected ladder `1+2n` |
| `logDeriv_riemannZeta_add_reflect_of_strip` | open critical strip |
| `logDeriv_riemannZeta_add_reflect_criticalLine` | `s = 1/2 + it` |
| `re_logDeriv_riemannZeta_criticalLine` | real form on the line |
| `re_logDeriv_riemannZeta_criticalLine_le` | unconditional bound |
| `re_logDeriv_riemannZeta_add_mirror` / `_le` | mirror pairs `σ+it`, `(1−σ)+it` |
| `logDeriv_riemannZeta_add_reflect_of_one_lt_re` | `Re s > 1`, `s` not an odd integer |

All in `formal/GaloisForLFunctions/RHTower/CompletedSplitRightHalfPlane.lean`, resting on the
archimedean layer in `RHTower/ArchLadderRegular.lean`.

## The zero-locus half of the reflection

The value reflection has a companion that the corpus held only on the open strip
(`riemannZeta_one_sub_eq_gammaRatio_mul`, `riemannZeta_one_sub_eq_zero_iff` in
`RHTower/ReflectionCocycleClass.lean`). The strip was doing nothing there except keeping the two
`Γ_ℝ` factors nonzero, so both are now corollaries of

  `riemannZeta_one_sub_eq_gammaRatio_mul_of_Gammaℝ_ne_zero`
  `riemannZeta_one_sub_eq_zero_iff_of_Gammaℝ_ne_zero`

whose only hypotheses are `Γ_ℝ(s) ≠ 0` and `Γ_ℝ(1−s) ≠ 0` — which already force `s ≠ 0` and
`s ≠ 1`, since `Γ_ℝ` vanishes at every nonpositive even integer. Ladder-form corollaries
(`…_off_poles`) are stated for the calling convention used by the archimedean layer.

Two consequences that were absent from both mathlib and the corpus:

- `riemannZeta_ne_zero_of_re_lt_zero` — for `Re s < 0`, `ζ(s) ≠ 0` unless `s ∈ {−2, −4, −6, …}`.
- `riemannZeta_eq_zero_iff_of_re_lt_zero` — the zero locus left of the strip is *exactly* the
  trivial ladder.

mathlib has only the forward half (`riemannZeta_neg_two_mul_nat_add_one`: those points are zeros).
The converse follows from the zero-locus reflection plus Euler-product nonvanishing at `Re > 1`.

## Where the zeros are

Extending the left edge from `Re s < 0` to `Re s ≤ 0` (the point `s = 0` is settled by
`ζ(0) = -1/2`) closes the classification:

- `riemannZeta_ne_zero_of_re_le_zero`, `riemannZeta_eq_zero_iff_of_re_le_zero`
- `riemannZeta_zero_re_mem_Ioo` — **every nontrivial zero of `ζ` lies in the open critical strip**
- `riemannZeta_zero_trivial_or_mem_strip` — the global dichotomy
- `riemannZeta_zero_ne_one` — a nontrivial zero is never the pole

The corpus carries `0 < ρ.re` and `ρ.re < 1` as *hypotheses* on a `ζ` zero in a long list of
modules (`BurnolCoPoisson*`, `CCMBVMuntzSummation`, `ZeroDetectionEM`, `TentDivisorRecovery`, …).
`riemannZeta_zero_re_mem_Ioo` is the connector that turns those into consequences.

## The `ζ`/`ξ` zero-set bridge and the shape of RH

`formal/GaloisForLFunctions/RHTower/ZetaXiZeroCorrespondence.lean`:

- `xi_eq_zero_iff_riemannZeta_eq_zero_and_nontrivial` — `ξ(ρ) = 0` iff `ρ` is a nontrivial zero of
  `ζ`, with **no** strip hypothesis on either side. The corpus had this only as `xi_eq_zero_iff`,
  gated on `0 < Re s` and `s ≠ 1`.
- `riemannZeta_eq_zero_iff_xi_or_trivial` — `ζ`'s zero set is `ξ`'s plus the trivial ladder.
- `riemannHypothesis_iff_forall_nontrivial_zero` — mathlib's `RiemannHypothesis` carries a
  redundant `s ≠ 1` clause; this is the same statement without it.
- `riemannHypothesis_iff_xi_zero_re_eq_half` — RH is exactly "every `ξ` zero has real part `1/2`".
  The corpus's `rh_iff_xi_ne_zero_right` restricts to `Re s > 1/2`; the restriction is removable.

## Hypotheses discharged

- `logDeriv_riemannZeta_add_reflect_off_poles` lost `s ≠ 0` and `s ≠ 1`: the two ladder conditions
  at index `0` already say exactly that.
- Both mirror theorems lost their second nonvanishing hypothesis. `ζ` at the mirror point vanishes
  iff `ζ` at the original point does — reflection moves the zero to the conjugate height, and
  conjugation moves it back.
- `logDeriv_riemannZeta_add_reflect_of_one_lt_re` has **no** nonvanishing hypothesis at all. In the
  half-plane of absolute convergence the identity is unconditional away from the odd integers,
  where `ζ(1−s)` genuinely vanishes.

## What made it possible

Three ingredients, none of which existed in usable form before:

1. **`logDeriv_archFactor_add_reflect`** — the rational part `1/s + 1/(s−1)` of the completed
   archimedean factor cancels *exactly* against its reflection, so the polynomial factor `s(s−1)/2`
   contributes nothing and the entire reflection defect is the pure `Γ_ℝ` weld.
2. **`logDeriv_Gammaℝ_reflect_off_poles`** — that weld in closed form. The corpus had it only as an
   `EventuallyEq` near `s = 3/4`, inside `archReflCocycle_curvature_ne_zero`.
3. **`isOpen_setOf_offPoles`** — the pole-free set is open (mathlib has no such lemma). Without it
   every off-poles statement was stuck at a point; with it the neighbourhood arguments go through
   and the region becomes the whole plane minus the ladders.

## Consequences on the critical line

`Re ζ'/ζ(1/2+it) = (log π − Re ψ(1/4 + it/2))/2` — the real part is *entirely* archimedean, no
zeta-side information survives. Combining with the corpus's `re_logDeriv_Gammaℝ_real_le` (the
archimedean mode is minimised on the real axis) gives the unconditional
`2·Re ζ'/ζ(1/2+it) ≤ log π − Re ψ(1/4)`.

For mirror pairs the same holds with the bound depending only on the abscissa `σ`, uniformly in the
height.

## What this does not do

It does not decide RH. The bound is an *upper* bound, while `ζ'/ζ` blows up negatively near a zero,
so a hypothetical off-line zero pair is not contradicted by it. The honest description is that the
archimedean side of the explicit-formula domination is now available in ζ-form rather than only in
`Γ_ℝ`-form.

## Log

- 2026-08-07 — created in 3-formalized; all theorems axiom-clean
  (`propext, Classical.choice, Quot.sound`).
