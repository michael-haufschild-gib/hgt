# Periodic patterns cannot satisfy their last lag

- **ID:** zcg-periodic-patterns-last-lag
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** card `zcg-deep-hiding-at-ingham-scale` (5-failed), README §6 Q2
- **Statement:** Let `N ≥ 1`, `ω = e^{2πi/N}`, `x_r ≥ 0` and `C_r ∈ ℝ` for `r < N`. If
  `Σ_r C_r cosh(m x_r) ω^{rm} = 0` for `0 ≤ m ≤ N − 1`, then `C = 0`.

## Goal
A periodic pattern of period `Ng` (one FE orbit of depth `δ_r` per residue, `x_r = δ_r · 2π/(Ng)`)
has the image `ℓ Σ_m k(mℓ) D(m)` with symbol `D(m) = Σ_r C_r cosh(m x_r) ω^{rm}`, `ℓ = 2π/(Ng)`. A
window of aperture `a > (N − 1)ℓ/2` sees the lags `|m| ≤ N − 1`. So no two distinct periodic
patterns of period `Ng` are mimics above `(N − 1)π/(Ng)`. With `mixedDepth_mimics_to_five_sixths`
this makes `5π/(6g)` the exact hiding limit of period `6`.

## Proof
Write `a_r = e^{x_r}ω^r`, `b_r = e^{−x_r}ω^r`, `q_r = (X − a_r)(X − b_r)`, `P = Π_r q_r` (degree
`2N`), and `M_n = Σ_r (C_r/2)(a_r^n + b_r^n)` for `n ∈ ℤ`. Since `a_r^n + b_r^n = 2cosh(nx_r)ω^{rn}`
and `C, x` are real, the hypothesis gives `M_n = 0` for `|n| ≤ N − 1`.
1. **The numerator is a monomial.** Let `T = Σ_r (C_r/2)(P/(X − a_r) + P/(X − b_r))`. The
   coefficient of `X^k` in `P/(X − ζ)` is `Σ_{i>k} p_i ζ^{i−k−1}`, so `[X^k]T = Σ_{i>k} p_i M_{i−k−1}`,
   which vanishes for `k ≥ N`. Since `P(ζ) = 0` at every node it also equals
   `−Σ_{i≤k} p_i M_{i−k−1}`, which vanishes for `k ≤ N − 2`. So `T = κ X^{N−1}`.
2. **On the circle.** `T = Σ_r C_r (X − cosh(x_r)ω^r) Π_{s≠r} q_s`. At `z = e^{iφ}`,
   `q_s(z) = −2zω^s D_s(φ)` with `D_s(φ) = cosh x_s − cos(φ − θ_s)`, `θ_s = 2πs/N`, and
   `z − cosh(x_r)ω^r = ω^r(−D_r + i sin(φ − θ_r))`. With `Σ_r C_r = M_0 = 0`,
   `κ = (−2)^{N−1}(Π_s ω^s) · i · G(φ)`, `G(φ) = Σ_r C_r sin(φ − θ_r) Π_{s≠r} D_s(φ)`. So `G` is
   constant.
3. **The constant vanishes.** If some `x_{r₀} = 0`, then `D_{r₀}(θ_{r₀}) = 0`, so `G(θ_{r₀}) = 0`.
   Otherwise every `D_r > 0`, and `Ψ = Σ_r C_r log D_r` is `2π`-periodic with
   `Ψ' = Σ_r C_r sin(φ − θ_r)/D_r = G/Π_s D_s`. Rolle gives a zero of `Ψ'`, so `G = 0`. Hence
   `κ = 0` and `T = 0`.
4. **`T = 0` forces `C = 0`.** If `x_{r₀} > 0`, evaluate at `a_{r₀}`: only the term `r₀` survives,
   `C_{r₀} ω^{r₀} sinh(x_{r₀}) Π_{s≠r₀} q_s(a_{r₀}) = 0`, and `q_s(a_{r₀}) ≠ 0` since the nodes of
   different residues have different arguments. If `x_{r₀} = 0`, then `q_{r₀} = (X − ω^{r₀})²`
   divides every other term, and `T/(X − ω^{r₀})` at `ω^{r₀}` is `C_{r₀} Π_{s≠r₀} q_s(ω^{r₀})`. ∎

## Lean
`formal/GaloisForLFunctions/ZeroConfigurationGeometry/PeriodicPatternsCannotSatisfyTheirLastLag.lean`:
`lagRoot`, `lagOuter`, `lagInner`, `lagQuad`, `lagNodePoly`, `lagPosMoment`, `lagNegMoment`,
`lagNumerator`, `moments_eq_zero`, `coeff_divByMonic_of_root`, `coeff_lagNumerator_high`,
`coeff_lagNumerator_low`, `lagNumerator_eq_monomial`, `lagNumerator_eq_residue`,
`eval_lagQuad_circle`, `eval_lagNumerator_circle`, `lagNumerator_coeff_eq`, `lagWronskian_eq_zero`,
`eval_lagQuad_ne_zero`, `eq_zero_of_lagSymbol_eq_zero`. `#print axioms`: `propext`,
`Classical.choice`, `Quot.sound`. Configuration corollary:
`PeriodicMimicsAreResolvedAboveTheirLastLag.lean` (`weilTest_twoBump` for complex weight `τ`,
`W_twoBump_of_lagFormula`, `W_bump_of_lagFormula`, `lagSymbol_eq_of_mimic`,
`eq_zero_of_mimic_of_periodSymbol`): two configurations with lag formulas whose symbols differ by
a period-`N` pattern are resolved at every aperture above `(N − 1)ℓ/2`. Weights `−1` and `i` on
the tooth at `nℓ` separate `D(n)` from `D(−n)`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Log
- 2026-11-05 — created; formalized
