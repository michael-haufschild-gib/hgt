# The Route J scaling profile `Φ` as a Lean theorem

**Stage:** 3 (formalized), 2026-09-03.  Closes MUST-149.  Eight new modules (all wired into
`RHTower.lean`, axioms `[propext, Classical.choice, Quot.sound]`, lint clean), on top of the boost
programme of `semilocal-boost-diagonal-closed-form-lean.md`.

**Main theorem** (`RHTower.RouteJProfile.ScalingData.tendsto_residual_profile`,
`tendsto_residual_ratio_profile`).  For scaling data `p_j → ∞`, `2 k_j / p_j → X > 0`, with
`δ_j = log p_j`:

    residualJetOf (cosineModeDeterminantJet δ_j) k_j  →  Φ(X) := 4√(2/π) [√X cos 4X − 8 X^{3/2} sin 4X],

and the same limit holds for the relative deviation `J_k / R_k(0)` because `R_k(0) → 1`
(`tendsto_residualZero`).  `residualJetOf (cosineModeDeterminantJet δ) k` is the exact first-order
response (in the amplitude `ε`) of the Route J four-radius critical residual to the multiplier
`1 + 2ε cos(δ s)` of the archimedean Gamma measure (module `SemilocalCosineModeFirstOrderResponse`);
with `ε = p^{-1/2}` and `δ = log p` it is the first Euler mode of the semilocal measure of
Connes–Consani–Moscovici, and the numerics (report §3.6) show the first-order response is the whole
deviation to 0.1 %.  So the universal profile of the Route J scaling law `D_k(q) = √q Φ(qn) + O(q)`
is now a theorem, with the frequency `4` and the constants `4√(2/π)`, `−32√(2/π)` derived, not fitted.

| module | content |
|---|---|
| `ScaledTerminatingHypergeometricLimit` | terminating `₂F₁(−n, n+d; c; σ²)` as `hypSum`; Tannery's theorem gives the Mehler–Heine limit `→ Σ (−1)^l w^{2l}/((c)_l l!)` when `nσ → w`; `= cos 2w` (`c = ½`), `sin 2w/2w` (`c = 3/2`); Ring.choose ↔ rising factorials |
| `SemilocalDiagonalPfaffTransformation` | `Σ C(n,l)((−(n+½)) choose l) x^l = (−1)^n C_n ₂F₁(−n, n+½; ½; 1−x)` via Chu–Vandermonde (`Ring.add_choose_eq`); `m_n(δ) = (cosh δ)^{-1/2}(−1)^n C_n ₂F₁(−n, n+½; ½; sech² δ)` |
| `SemilocalBoostContiguousRelations` | `(2n+1)F_{n+1} + 2(n+1)F_n = (4n+3)(1−x)H_n`, `H_{n+1} − H_n = −(4n+5) x K_n` (coefficientwise) |
| `RouteJResidualFirstDifferenceForm` | `m_{n+1} − m_n = (cosh δ)^{-1/2}(−1)^{n+1} Q_n` with `Q_n = C_n(4n+3)(1−x)H_n/(2(n+1))` smooth; the residual jet `= (cosh δ)^{-1/2}[r r ΔQ + 2Δ(r²Q) + r r ΔQ]`; the differences in closed form through `H, K` |
| `RouteJScalingProfileLimits` | scaling data; `p σ → 2`, `(ck+d)σ → cX`, `H_{2k+a} → cos 4X`, `K_{2k+a} → sin 4X/4X`, Wallis `√n C_n → 1/√π`, `(cosh δ)^{-1/2}√p → √2`, `r_{2k+a}/2k → 1` |
| `RouteJScalingProfile` | the explicit residual, the normalization `N_j = (cosh δ)^{-1/2} C_{2k} 2k → √(2X/π)`, the rational prefactors, and the assembly to `Φ` |
| `RouteJResidualNormalizationLimit` | `R_k(0) = g(M) + g(M') + ½`, `g(M) = √(M(M+½)) − M → ¼`; `R_k(0) → 1`; the ratio limit |

**Why the alternating leading term does not obstruct the limit.**  The residual is a second
difference of the alternating `m_n`; written through `Q_n = (−1)^{n+1}(S_{n+1} − S_n)` it becomes a
combination of *first differences* of the smooth sequences `Q_n` and `r_n² Q_n`, and the second
contiguous relation evaluates those differences exactly with a factor `x = sech² δ ≈ 4/p²` in front
of `K_n`, which is why `x·(4n+1)(8n+7) → 32X²` produces the `x^{3/2} sin 4x` term.  Tannery's
theorem is applied only to sums whose terms are individually bounded (the `σ`-forms), never to the
cancelling `τ`-forms.

**Consequences.**  The odd Euler jets of the corpus (`c₁ = 4√(2/π)`, `c₃ = −160√(2/π)`) are the first
Taylor coefficients of `Φ`; the fifth is `384√(2/π)`; the order-one threshold of the Route J
deformation is `n* ~ p^{4/3}/8.66`.  Route J's boundary question "what happens at `n ≈ p`" has a
theorem: the Bessel-regime oscillation of the SU(1,1) boost elements at rapidity `log p`.

**Numerical pre-certification:** `2-fully-proven/computations/routej-semilocal-scale/mehler_heine_precert.py`
(Pfaff, both contiguous relations, the first-difference identity, and the scaling limit, all to
`10⁻³³` or better).
