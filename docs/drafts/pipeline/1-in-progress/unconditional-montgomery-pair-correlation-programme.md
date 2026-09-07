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
| 3 | Montgomery's Lemma 1 as an **exact** identity: pair `−ζ'/ζ` on `Re s = 2` with `K_t(s) = x^{s}(−2)/((s−a)(s−b))`, `a = 3/2+it`, `b = −1/2+it` (`= 2x^{s}/(1−(s−s₀)²)`); Mittag-Leffler expansion termwise (the lag-formula route, no rectangle, no conditional convergence). **3a DONE** `RHTower/MontgomeryKernelPerron.lean`: poles, kernel, integrability, two-pole evaluation `(1/2π)∫K_t = −(x^a − x^b)`, three-pole evaluation `(1/2π)∫K_t/(s−c) = −((x^c−x^a)/(c−a) − (x^c−x^b)/(c−b))`, vanishing below the cutoff, and the Dirichlet side `(1/2π)∫ LSeries(Λ)·K_t = −Σ_{n≤x}Λ(n)((x/n)^a − (x/n)^b)` (`montgomery_dirichlet_side`). **3b OPEN**: the Mittag-Leffler side (pole at 1, digamma series, paired zero terms) and the assembly; the kernel-pole residues re-sum to `x^a·(−ζ'/ζ)(a)` and `x^b·(−ζ'/ζ)(b)` through the paired partial fraction at `a` and at `b` (`logDeriv_xi_eq_partialFraction` holds at both since `ξ(b) = ξ(1−b) ≠ 0`). Brick 2 (Landau) is then not needed. |
| 4 | Lemma 3/4: `F(x,T) = (1/2π)∫_0^T \|zero side\|² + O(x^{1−2η}log³T) + O(x)`: truncation of far zeros (local count), extension of the `t`-range | brick 1 gives the exact infinite-line identity; the finite-`T` bookkeeping needs `card_le_of_ordinates_in_window` and the zero-free region `exists_littlewood_zero_free_region` (classical region suffices for `α ≥ ε`) |
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
