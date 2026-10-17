# PA: signed compact completions of the moment tower collapse to RH

- **ID:** pa-signed-completion-collapse
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — no-go closure of PA open item "nonpassive source-faithful completion"
- **Source:** route PA (docs/reports/rh-current-frontier-map.md), Stokes-carrier completion sub-lane
- **Statement:** If finite measures `μ, ν` on `[−B, B]` satisfy `m_n = ∫ x^n dμ − ∫ x^n dν` for every
  normalized prime–archimedean moment `m_n`, then RH holds. Hence a signed compact completion of the PA
  moment tower exists iff RH (the canonical compact Xi measure, with `ν = 0`, under RH).

## Goal
The frontier listed as open for PA a "nonpassive source-faithful completion with both added and
removed mass" of the critical Stokes carrier to the completed source. The corpus had killed passive
deletion, finite atom repair and positive supercarrier completions (all force RH through the compact
Markov capstone). The remaining loophole was a *signed* final carrier (added and removed mass) of
bounded support. This theorem closes it: any signed measure of bounded support representing the tower
already forces RH, for every support radius `B` (in particular beyond the endpoint radius, where the
Stokes nodes `p^{-1/2}` live). Positive survivor: a completion of the PA tower that is not RH-hard
must be a distribution of unbounded variation or unbounded support — the explicit-formula object,
not a measure. The completion programme is closed as a measure programme.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  paper proof (below)
- [x] 2 → 3  formalized: `RHTower/PrimeArchSignedCompactCompletionCollapse.lean` (812 lines),
  `lake env lean` green, wired into `GaloisForLFunctions/RHTower.lean`;
  `#print axioms`: `propext, Classical.choice, Quot.sound`.
  Main: `riemannHypothesis_of_signedCompactPrimeArchMoments`,
  `exists_signedCompactPrimeArchMoments_iff_riemannHypothesis`.
- [ ] 3 → 4  (no stage 4 by user directive)

## Approach (paper proof, as formalized)
1. Germ identity: `Σ_n m_n z^n = F(z) := Σ_q x_q/(1 − z x_q)` for `‖z‖ ≤ 41/4`
   (`xiAtomResolventSum_eq_tsum_moment`; double series, `‖x_q‖ ≤ 2/41`, power sums of the atoms are
   the moments via `xiCentralPolynomialMoment_eq_sourceMomentFunctional`).
2. `F` is holomorphic at every point where no `1 − z x_q` vanishes (finite head + uniformly bounded
   tail, `Complex.differentiableOn_tsum_of_summable_norm`).
3. For `μ` finite on `[−B, B]`, `H_μ(z) = ∫ dμ(x)/(1 − zx)` is holomorphic on `Im z > 0` (parametric
   differentiation; `‖1 − zx‖ ≥ |Im z|/‖z‖` for real `x`) and equals `Σ_n (∫x^n dμ) z^n` for
   `‖z‖B < 1`. Hence `F = H_μ − H_ν` near `0`.
4. If RH fails, critical-line reflection gives an atom with `Im x_q < 0`; take `x₀` of maximal
   modulus among them, `z₀ = 1/x₀` (`Im z₀ > 0`). On the half-disc `D = {Im z > 0} ∩ {‖z‖ < ‖z₀‖}`
   (convex, hence connected) `F` has no poles, so `F = H_μ − H_ν` on `D` by the identity theorem.
5. Along `t z₀`, `t ↑ 1`, `F` blows up like `M‖x₀‖/(1 − t)` (pole atoms; the other head atoms stay
   bounded since no atom is a real multiple `x₀/t`, `t ∈ [1/2,1)`, by maximality; the tail is bounded by
   twice the total atom mass), while `H_μ − H_ν` is continuous at `z₀`. Contradiction.

## Log
- 2026-10-17 — conjectured as the collapse of the PA "nonpassive completion" item; proved and
  formalized the same day; wired; axioms audited. Lint gate reports only other agents' unwired modules.
