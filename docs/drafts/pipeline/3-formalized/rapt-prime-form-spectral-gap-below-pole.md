# The prime form has a spectral gap below its pole

- **ID:** rapt-prime-form-spectral-gap-below-pole
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** C4 of the connect-dots loop; ALG research direction "Trickle-down for ζ" (the gap of the
  Markov form on the complement of the pole vector); B3.30.
- **Statement:** There is `g > 0` such that for every `ε > 0`, eventually in `N`, every `x` with
  `Σ_{n ≤ N} x_n/√n = 0` satisfies `P_N(x) ≤ (log N − γ − g + ε)|x|²`.

## Goal

The top of the prime form is `log N − γ + o(1)`, attained near the pole `n^{−1/2}` (RP3). The
statement isolates it: the pole is the only direction within `g` of the top, uniformly in `N`.
Numerics: `λ₂ − log N → −(γ + 2 log 2)`, i.e. the optimal gap is `2 log 2`.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

## Approach (paper proof)

Pole gauge `x_n = y_n/√n`, harmonic measure `μ(n) = 1/n` on `[1, N]`, `|x|² = Σ y²/n`, pole
orthogonality = `μ`-mean zero.

1. **Ladder Poincaré.** `D_N(x) = Σ_{mt ≤ N} Λ(t)/(mt)(y_{mt} − y_m)² = Σ_p D_p`, `D_p` supported on
   `p`-ladders `{up^j ≤ N}`. On each ladder, pairwise: `w_i w_{i'}/W ≤ p^{−i'}/u`, so
   `D_p|_ladder ≥ log p · Var_ladder`. Hence `D_N ≥ log 2 · Σ_p G_p(y)`, `G_p = Σ_ladders Var`.
2. **Tensorization of the harmonic measure (Glauber).** `Var_μ(y) ≤ C Σ_p G_p(y)` uniformly in `N`.
   Proof by peeling the smallest prime from `R(Q, X)` = `Q`-rough numbers `≤ X` (weights `1/K`):
   `R(p, X) = ⊔_j p^j R(p⁺, X/p^j)`. Within-levels: induction. Between-levels: split
   `f = g(K) + h`, `g` the ladder mean; `h`-part `≤ (1 + η) G_p` (Jensen); `g`-part
   `≤ (1 + 1/η) τ(p, X) Var` with `τ(p, X) = Σ_{j≥1} p^{−j}(F_0 − F_j)/F_0`, `F_j = F_{p⁺}(X/p^j)`
   (nested-set mean bound `|E_A g − E g|² ≤ V (M − M_A)/(M M_A)`; `V_ρ(g) ≤ V_μ(f)`).
   So `C(p, X) ≤ max(sup_j C(p⁺, X/p^j), 1 + η)/(1 − (1 + 1/η)τ(p, X))`.
3. **Thin shells.** `F_{p⁺}(pY) − F_{p⁺}(Y) ≤ c` (Selberg sieve with `z = min(p, √x)` on dyadic
   blocks); `F_{p⁺}(X) ≥ log X · Π_{q ≤ p}(1 − 1/q) ≥ c′ log X/log p` (`H(X) ≤ F_{p⁺}(X) Σ_{p-smooth} 1/a`
   + Mertens). Hence `τ(p, X) ≤ c″ log p/(p log X)` and `τ ≤ τ* < 1`.
4. **Potential.** `Ψ(Q, X) = −A Σ_{q < Q}(log q/q)/log X` drops by `A log p/(p log X)` from `(p, X)`
   to `(p + 1, Y)` for every `Y ≤ X`, and lies in `[−3A, 0]` while `p ≤ X` (Mertens' first theorem).
   With `A = (1 + 1/η) c″/(1 − δ*)`, `1/(1 − δ) ≤ e^{δ/(1 − δ*)}` closes the induction
   `C(Q, X) ≤ (1 + η) e^{3A} e^{Ψ(Q, X)}`.
5. **Assembly.** Ground-state identity `P + D = Σ (A(⌊N/n⌋) + log n) x²`; rows `≤ log N − γ + ε`
   off the top `n > N/Y`; top mass `≤ (2D + 2(log Y + c)|x|²)/log(N/Y)`; `D ≥ (log 2/C)|x|²`.

Numerics: Glauber gap `0.786, 0.795, 0.800, 0.804` (N = 500…32000); `τ ≤ 0.19`,
`τ p log X/log p ≤ 3.7`, shells `≤ 0.69` (p ≤ 2741, X ≤ 2·10⁵).

## Status

Lean (RAPT, all axiom-clean `propext, Classical.choice, Quot.sound`, wired):
- `TheRoughHarmonicMeasureHasThinShells`: `sum_roughInterval_eq_levels`,
  `mertensPrimeProduct_mul_log_le_roughHarmonic`, `exists_mertensPrimeProduct_mul_log_ge`,
  `sum_roughInterval_block_le` (Selberg sieve, vendored `BrunTitchmarsh.siftedSum_le`),
  `exists_roughHarmonic_shell_le`, `exists_shellTau_le`.
- `TheHarmonicMeasureTensorizesOverPrimes`: `mul_sq_wMean_sub_le`, `glauberForm_eq_levels`, `peel`,
  `exists_harmonicVar_le_glauberForm`.
- `ThePrimeFormHasASpectralGapBelowItsPole`: `ladderVar_le_base_edges`,
  `log_two_mul_glauberForm_le_poleDefect`, `exists_poleDefect_ge`,
  `exists_atomicWeilForm_le_of_pole_orthogonal`.

Open: the optimal gap `2 log 2` (the `p = 2` valuation step); transfer to the Markov form at the
spacing (ALG's remaining content beyond `c★`).

## Log
- 2026-10-28 — paper proof; formalized in three modules.
