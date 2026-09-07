# Unconditional Montgomery pair correlation in Lean

- **ID:** `unconditional-montgomery-pair-correlation-programme`
- **Stage:** 1-in-progress
- **Type:** FORMALIZATION PROGRAMME (literature theorem, corpus-missing foundation)
- **Source:** Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh, Acta Arith. 214 (2024), arXiv:2306.04799,
  Theorem 1; Montgomery (1973); Goldston–Montgomery (1987) Lemma 8; Aryan (2022).
- **Target statement.** With `F(x,T) := Σ_{ρ,ρ' : 0<γ,γ'≤T} x^{ρ+ρ̄'−1} w(ρ+ρ̄'−1)`, `w(u) = 4/(4−u²)`,
  over *all* nontrivial zeros (no hypothesis on their real parts),
  `F(T^α,T) = (T/2π) log T · (α + T^{−2α}(log T + O(1)) + O(1/√log T))` uniformly for `0 ≤ α ≤ 1`.

## Why this theorem

It is the single analytic input of the current critical-line-proportion frontier (Zeta-23 `2/3`,
Lamzouri, the `(L)`-constant `κ₀`), of the Maynard–Pratt-type isolation dichotomy (CANNOT-332), and
of every "what bandwidth-one statistics can and cannot see" law. The corpus owns Montgomery–Vaughan
(`RiemannGaussian/MontgomeryVaughan`, `MVHilbert 26`), the partial-fraction of `ξ'/ξ`, Littlewood
zero-free regions, the local zero count (`ZetaLocalZeroCount`), and the Guinand–Weil explicit formula on
the regularized Cauchy test algebra — but not this theorem.

## Bricks

| # | Brick | Corpus asset / status |
|---|---|---|
| 1 | **Mean-square identity** `F_Z(x) = ∫ e^{−2\|ξ\|} \|Σ_{ρ∈Z}(xe^{−ξ})^{ρ−1/2}\|² dξ` for every finite family in `0<Re ρ<1`; `F_Z ≥ 0` | **DONE** `RHTower/MontgomeryFormLogScaleMeanSquare.lean` (`montgomeryForm_eq_integral`, `montgomeryForm_re_nonneg`, pair integral `integral_exp_neg_two_abs_mul_cexp`); axiom-clean, wired |
| 2 | (superseded by 3) Landau's explicit formula `Σ_ρ x^{ρ−s}/(s−ρ) = Σ_{n≤x}Λ(n)n^{−s} + ζ'/ζ(s) − x^{1−s}/(1−s) − Σ_n x^{−2n−s}/(2n+s)` (BGSTB (2.3)) | search `lag_explicit_formula`, `xiGuinandWeilExplicitFormula`, Perron modules; not located as such |
| 3 | Montgomery's Lemma 1 as an **exact** identity: pair `−ζ'/ζ` on `Re s = 2` with `K_t(s) = x^{s}(−2)/((s−a)(s−b))`, `a = 3/2+it`, `b = −1/2+it` (`= 2x^{s}/(1−(s−s₀)²)`); Mittag-Leffler expansion termwise (the lag-formula route, no rectangle, no conditional convergence). **3a DONE** `RHTower/MontgomeryKernelPerron.lean`: poles, kernel, integrability, two-pole evaluation `(1/2π)∫K_t = −(x^a − x^b)`, three-pole evaluation `(1/2π)∫K_t/(s−c) = −((x^c−x^a)/(c−a) − (x^c−x^b)/(c−b))`, vanishing below the cutoff, and the Dirichlet side `(1/2π)∫ LSeries(Λ)·K_t = −Σ_{n≤x}Λ(n)((x/n)^a − (x/n)^b)` (`montgomery_dirichlet_side`). **3b DONE** `RHTower/MontgomeryLemmaOne.lean` (axiom-clean, wired): centred kernel bound `‖K_t(2+iτ)‖ ≤ 8x²/(1+(τ−t)²)`, digamma and zero terms against the kernel with majorants centred at `t`, integrability and summability (`summable_integral_norm_mkTerm`, `summable_integral_norm_mzTerm`), termwise integrals, the Mittag-Leffler side (`montgomery_mittagLeffler_side`), the rearranged values (`integral_mzTerm_eq`: `−Z_q − x^a P_a(ρ) + x^b P_b(ρ)`; `integral_mkTerm_eq`: `4T_k − x^a d_k(a) + x^b d_k(b)`), summabilities of the three families (`summable_montgomeryZeroTerm` through `‖ρ(1−ρ)‖ ≤ 16(1+t²)‖(ρ−a)(ρ−b)‖`, geometric `summable_montgomeryTrivialTerm`, `summable_digammaShiftTerm` for `Re s ≥ −1/2`), and **`montgomery_lemma_one`**: `Σ_ρ 2x^ρ/((ρ−a)(ρ−b)) = −Σ_{n≤x}Λ(n)((x/n)^a−(x/n)^b) + ((x−x^a)/(1−a) − (x−x^b)/(1−b)) + c₁(x^a−x^b) − 2Σ_k T_k + ½x^a S(a) − ½x^b S(b) − x^a ξ'/ξ(a) + x^b ξ'/ξ(b)`, exact for `x > 1` and every real `t`, over all zeros of `ξ` with multiplicity. Brick 2 (Landau) not needed. Cosmetic remainder: the `ζ'/ζ` form of the `x^a`, `x^b` coefficients (digamma series at `b/2`, `Re b/2 = −1/4`, via `digamma_apply_add_one`). |
| 4 | Lemma 3/4: `F(x,T) = (1/2π)∫_0^T \|zero side\|² + O(x^{1−2η}log³T) + O(x)`: the height mean square of the finite family, then truncation of far zeros and extension of the `t`-range | **4a DONE** `RHTower/LorentzianComplexShiftProduct.lean` (axiom-clean, wired): `∫_ℝ 1/(1+(t+a)²)·1/(1+(t+b)²) dt = 2π/(4+(a−b)²)` for complex shifts `\|Im a\|,\|Im b\| < 1` (`lorentzProduct_eq`), by the identity theorem on the unit strip twice from the corpus's real-shift identity, with Cauchy-dominated holomorphy of the parameter integral. **4b DONE** `RHTower/MontgomeryFormHeightMeanSquare.lean`: `montgomeryForm_eq_integral_height`: `F_Z(x) = (2/π)∫_ℝ \|Σ_{ρ∈Z} x^{ρ−1/2}/(1+(t+i(ρ−½))²)\|² dt` for every finite family in `0<Re ρ<1` (BGSTB Lemma 3, exact), real form `montgomeryForm_re_eq_integral_height`; and `montgomeryZeroTerm_eq_lorentz`: the Montgomery-lemma zero summand is `−2x^ρ·L_{i(ρ−½)}(t)`. **4c-i DONE** `RHTower/LorentzianZeroMass.lean`: `lorentzMass t := Σ_ρ 1/(1+(t−γ)²)` (all zeros, multiplicity) is summable and `≤ 8·Re ξ'/ξ(2+it)` (`lorentzMass_le_re_logDeriv_xi`: partial fraction + reflection `ρ↦1−ρ` kills the `(ρ−½)⁻¹` parts exactly), and `‖ξ'/ξ(2+it)‖ ≤ C + log(\|t\|+3)` with explicit `C` (`norm_logDeriv_xi_lineTwo_le`: polar terms, `Σ Λ(n)/n²`, digamma via two recurrence steps into the corpus Stirling bound); hence `lorentzMass t ≤ 8(C + log(\|t\|+3))` (`lorentzMass_le_log`). **4c-ii OPEN**: width-`w` mass `Σ_ρ 1/(w²+(t−γ)²) ≤ (8/w)Re ξ'/ξ(1+w+it)` (same mechanism at the point `1+w+it`) gives the one-sided tails `Σ_{γ>T}1/(1+(t−γ)²) ≪ log T/(1+T−t)` without window counting; then the crude Lemma 4 `∫_0^T\|S_all\|² = (π/2)F(x,T) + O(x log³T)` (bound `\|x^{ρ−½}\| ≤ x^{1/2}`; the `θ`-refinement only matters for `α→1`, where the corpus lacks Korobov–Vinogradov, so the target is uniformity on `[0,1−ε]`). |
| 5 | Mean square of the prime side `∫_0^T \|Σ_n Λ(n)n^{−1/2−it}min(n/x,x/n)\|²dt = T log x + O(x log x)` and, at `x = T`, the asymptotic with the Fejér structure (Aryan) | `MVHilbert 26` gives the `O(x log x)`; the `α = 1` asymptotic needs the near-diagonal prime-pair sieve bound `Σ_{n≤y}Λ(n)Λ(n+h) ≪ y` (corpus: check `Sieve` lane, Brun–Titchmarsh in `PNTPlus`) |
| 6 | Assembly: `F(α)` real, even, nonnegative, the asymptotic uniform on `[0,1]` | — |

## Disposition

Bricks 2–6 are unconditional analytic number theory of the classical kind; none is RH-bearing. The
programme is justified because every live statement about the Weil/pair-correlation complex on the
map now rests on it, and because the corpus's isolation dichotomy (CANNOT-332) is a two-line
corollary of bricks 1 and 6 combined.

## Log

- 2026-09-07 — programme opened; brick 1 built (the identity that the whole session's wall
  analysis rested on, and that was twice mis-applied on paper before being written down exactly).
- 2026-09-07 (later) — brick 3a built: Montgomery kernel, Perron evaluations, Dirichlet side. Landau's formula is bypassed: the combined kernel is absolutely convergent on the zero side, so the lag-formula route applies verbatim.
- 2026-09-07 (later) — brick 3b built: Montgomery's lemma is an exact Lean identity (`montgomery_lemma_one`). Next: brick 4 (finite-`T` truncation of the zero side against the mean square of brick 1) and brick 5 (prime-side mean square).
- 2026-09-07 (later) — bricks 4a, 4b, 4c-i built (complex-shift Lorentzian product; pair form as height mean square; Lorentzian zero mass `≤ 8 Re ξ'/ξ(2+it) ≤ 8(C+log(|t|+3))`). Zeta23 (lake dependency) audited for overlap: it owns Montgomery–Vaughan, Landau's formula, local zero counts and the explicit formula, but not the pair-correlation asymptotic; no duplication. Next: 4c-ii (width-`w` mass, tails, crude Lemma 4), brick 5 (BGSTB Lemma 1 form of `montgomery_lemma_one` + prime-side mean square via `MVHilbert`).
