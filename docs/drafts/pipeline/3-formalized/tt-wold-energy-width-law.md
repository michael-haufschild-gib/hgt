# Route TT: Wold energy and signed covariance are calibrated to the zero abscissa

- **ID:** tt-wold-energy-width-law
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** route-tt-loop-2026-10-13 rows 73, 74, 120
- **Statement:** For `0 ≤ α < ½`: every zero of `ξ` has `Re ρ ≤ ½+α` ⟺ the natural Wold square energy `E(t)=Σ_N N^{2t−1}R_N²` is finite for every `0<t<½−α` ⟺ the signed directed covariance `D_t(N)+Q_t(N)/2` of the literal Wold increments is bounded in `N` for every `0<t<½−α`.

## Goal
Route TT asks for a signed nonlocal covariance bound across rapidities. This card shows that the
need is exactly the zero-free half-plane of matching width. At `α=0` it is RH. The first non-trivial
TT milestone (finite `E(t)` for one `t>0`) is exactly quasi-RH `Θ ≤ 1−t`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (paper proof below)
- [x] 2 → 3  formalized: `lake build --old` green; `#print axioms` gives propext, Classical.choice, Quot.sound only
- [ ] 3 → 4  publication-ready

## Approach
- **Endpoint identity.** `D + Q/2 = ½(w₀(r_N−r_0)² + Σ(w_{n+1}−w_n)(r_N−r_{n+1})²)`, by
  summation by parts. The covariance therefore measures only the logarithmic energy plus a boundary
  term.
- **Concavity trap.** `2t(n+2)^{2t−1} ≤ (n+2)^{2t}−(n+1)^{2t} ≤ 2t(n+1)^{2t−1}`. The logarithmic
  energy is comparable to `E(t)`.
- **Energy ⟹ zero-free.** Finite `E(t)` makes the Abel current differentiable on `Re s > 1−t`, so
  the cleared continuation has no zero there.
- **Zero-free ⟹ energy.** Generalized von Koch gives the Chebyshev power spectrum, which transports
  to the Wold power spectrum `|R_N| ≤ B N^{−c}` for every `c < ½−α`. Choosing `t<c` makes the
  energy summable; choosing `c=t` bounds the boundary term.

## Lean
- `RHTower/XiHeatCassiniWoldNaturalSquareEnergySubhalf.lean`: `riemannHypothesis_iff_forall_woldNatResidualSquareEnergy_lt_half`, `riemannZeta_ne_zero_of_squareEnergy_subhalf`.
- `RHTower/PaperWoldDirectedCovarianceEnergy.lean`: `directedCovariance_add_half_diagonal`, `endpointEnergy_le`, `summable_woldEnergy_of_directedCovariance_bdd`.
- `RHTower/PaperWoldDirectedCovarianceRH.lean`: `riemannHypothesis_iff_forall_directedCovariance_bdd`, `exists_directedCovariance_bdd_of_squareEnergy`, `woldNatResidualSquareEnergy_of_directedCovariance_bdd`.
- `RHTower/PaperWoldDirectedCovarianceWidthSpectrum.lean`: `xiZeroHalfPlaneBound_iff_forall_woldNatResidualSquareEnergy`, `xiZeroHalfPlaneBound_iff_forall_directedCovariance_bdd`.
- Raw covariance (row 135): `exists_le_directedCovariance` (lower bound free), `xiZeroHalfPlaneBound_iff_forall_directedCovariance_bddAbove`, `riemannHypothesis_iff_forall_directedCovariance_bddAbove`.
- `RHTower/PaperWoldIncrementSignBlind.lean`: `paperWoldMaskedOperator_signBlind`. Masked Wold operators are sign-blind, so the TT operator layer carries no arithmetic sign.

## Log
- 2026-10-13: rows 73–74 proved (RH case).
- 2026-10-14: row 120 proved (every width); moved to 3-formalized.
- 2026-10-14: row 135 — raw signed covariance one-sided form.
