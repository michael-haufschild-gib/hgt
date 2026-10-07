# Weil-cone rigidity of dilation parts from the |ζ|²-weighted boundary inequality

- **ID:** weil-cone-zeta-square-boundary-rigidity
- **Stage:** 3-formalized (Lean, unconditional, standard axioms)
- **Type:** THEOREM
- **Source:** Opus loop row 531; extends MUST-801 (`WeilConeInfiniteDilationRigidity`) and the finite-type card
  (`3-formalized/11-rh-zero-divisor-geometry/weil-cone-finite-type-uniqueness.md`); frontier-map open item
  "mixed infinite-type zero-singular perturbations".
- **Statement (Step 1).** Let `a, f, v : ℕ → ℝ`, `δ > 0`, with `Σ (|a(n)| + |f(n)| + |v(n)|) n^{−1/2+δ} < ∞`,
  `f(1) = 0`, `v(0) = v(1) = 0`. If `lam = Λ ⋆ a + μ ⋆ f + v` is full-cone Weil-positive, then `a = δ₁`.
- **Corollary.** If moreover `f` is finitely supported, then `f = 0` and `v = 0` (finite-type theorem applied after
  `a = δ₁`). Within the class {`Λ⋆a + μ⋆f + v`: `a`, `v` absolutely convergent past ½, `f` finite} a Weil-positive
  completion exists iff RH.

## Why it is new
- MUST-801 needs `f = 0`; the finite-type theorem needs `a` finitely supported (its Step 1 uses the largest support index).
- The notch lane (MUST-570–576) pairs `|ζ|²` with the Weil form through the explicit formula. That needs the deviation's
  twisted sums to converge (absolute abscissa `< 1`). Dilation deviations `Λ ⋆ (a − δ₁)` have abscissa exactly 1
  ("Λ-comparable"), where that route hits long twisted moments.
- Here the long prime sum is never expanded. The FE identity `Re(ζ′ ζ̄) = −θ′ |ζ|²` on the critical line evaluates it
  exactly, and only fixed-twist second moments of `ζ` are needed.

## Paper proof of Step 1
Notation: `A, F, E` the Dirichlet series of `a, f, v`; `G(s) = ½ψ(s/2) − ½log π + 1/s`; `Φ` the Herglotz continuation of
the Weil function of `lam` (`Re Φ ≥ 0` on `Re s > ½`); `g(t) = Re(G + 1/(s−1))(½+it) = ½ Re ψ(¼ + it/2) − ½ log π`
(= `gammaHardyPhaseRate`, `θ′`).

1. **Master identity.** On `Re s > ½`: `ζ(Φ − G − 1/(s−1) + E) = A ζ′ − F`, and `A(1) = 1` (residue at `s = 1`).
   So `H := Φζ = (G + 1/(s−1) − E)ζ + Aζ′ − F`, holomorphic on a neighbourhood of the critical line.
2. **Boundary inequality.** On `Re s > ½`, `Re(H ζ̄) = |ζ|² Re Φ ≥ 0`. Both factors extend continuously to the line, so
   `Re(H(½+it) ζ(½−it)) ≥ 0` for every real `t`. No measure theory and no residues are used: `|ζ|²` vanishes at
   every critical zero.
3. **Functional equation.** `Re ξ′/ξ = 0` on the line off zeros, and `ξ′/ξ = G + 1/(s−1) + ζ′/ζ`. So
   `Re[(G + 1/(s−1))|ζ|² + ζ′ζ̄] = 0` on the line (both sides vanish at zeros). Hence
   `Re[(A − 1) ζ′ ζ̄] ≥ Re E |ζ|² + Re(F ζ̄)`.
4. **Decomposition.** `Re(ζ′ζ̄) = −g|ζ|²` and `Im(ζ′ζ̄) = −½ d/dt |ζ(½+it)|²`. So, pointwise,
   `(P)  g (1 − Re A) Z + ½ Im A · Z′ ≥ Re E · Z + Re(F ζ̄)`, with `Z(t) = |ζ(½+it)|²`.
5. **Averaging.** Let `ω_L` be the notch window (`= 1` on `[L, 2L]`, supported in `[L/2, 5L/2]`), `m ≥ 1`, `c = ±1`,
   `W(t) = 1 + c² + 2c cos(t log m) ≥ 0`. Multiply (P) by `ω_L W / log t` and integrate. Integrate the `Z′` term by
   parts. With `|g − ½log(t/2π)| ≤ 33/(16t²) + π/(2t)`, `∫ω_L Z = O(L log L)` and Cauchy–Schwarz for `∫ω_L|ζ|`:
   `½ ∫ ω_L W (1 − Re A) Z ≥ −C L`.
6. **Twisted moments.** For coprime `h, k`: `∫ ω_L Z (h/k)^{it} = (hk)^{−1/2} ∫ω_L log t + O(L)` (corpus
   `exists_norm_twistedMoment_hk_sub_le`). Expanding `W (1 − Re A)` (truncating `A` at `N`, tail `≤ ε_N ∫ω_L Z`):
   `∫ ω_L W (1 − Re A) Z = (∫ω_L log t)·[(1 + c²)(1 − A(1)) + c m^{−1/2}(2 − Σ_n a(n)(1 + gcd(m,n))/n)] + o(L log L)`.
   With `A(1) = Σ a(n)/n = 1` the bracket is `c m^{−1/2}(1 − Σ_n a(n) gcd(m,n)/n)`.
7. **Both signs of `c`.** Step 5 gives the bracket `≥ 0` for `c = ±1`, so `Σ_n a(n) gcd(m,n)/n = 1` for every `m ≥ 1`.
8. **Inversion.** With `b = a − δ₁`: `Σ_n b(n) gcd(m,n)/n = 0`. Since `gcd(m,n) = Σ_{d | m, d | n} φ(d)`,
   `Σ_{d | m} φ(d) β(d) = 0` for all `m`, where `β(d) = Σ_k b(dk)/(dk)`. Induction on `m` gives `β ≡ 0`, and
   `b(n)/n = Σ_k μ(k) β(nk) = 0` (absolutely convergent since `Σ|b(n)| d(n)/n < ∞`). So `a = δ₁`. ∎

## Structural reading
- The leading-order functional `(h/k)^{it} ↦ (hk)^{−1/2}` is integration against the Kakutani product of Poisson kernels
  `⊗_p P_{p^{−1/2}}` on the Bohr torus (singular with respect to Haar). The Weil normalization `A(1) = 1` is exactly
  the mean of `Re A` under this measure. Positivity then forces `Re A ≤ 1` on the whole torus, with mean 1, so `A ≡ 1`.
  Steps 7–8 are the algebraic shadow of this: only the two-point weights `|1 ± m^{it}|²` are needed.

## Lean plan
- [x] L1 master identity for series `A`, `F` (absolutely convergent past ½ − δ) and regular `v`; `A(1) = 1`
- [x] L2 boundary inequality (P) on the critical line
- [x] L3 averaged inequality: `½∫ω_L W(1 − Re A)Z ≥ −C L`
- [x] L4 twisted-moment main term of `∫ω_L W (1 − Re A) Z` with truncation
- [x] L5 algebra: gcd identity, inversion, `a = δ₁`; corollaries with finite `f`

## Log
- 2026-10-06: created (loop row 531). Inputs located in the corpus: `exists_norm_twistedMoment_hk_sub_le`
  (ZetaNotchTwistMainTerm), `gammaHardyPhaseRate_sub_log_conductor_bound` (HardyZPhaseAsymptotic),
  `re_logDeriv_xi_criticalLine`, `logDeriv_xi_eq_datum_add` (finite-type uniqueness module).
- 2026-10-07 00:10, status of this card's Lean (Opus loop):
  - L1 + L2 DONE, built: `RHTower/WeilZetaSquareBoundaryInequality.lean`. It contains the master identity with a Möbius part `F` and regular `v`, `A(1) = 1`, the boundary inequality `re_boundary_ge`, `Re(ζ′ζ̄) = −θ′|ζ|²` and `d/dt|ζ|² = −2 Im(ζ′ζ̄)`.
  - Moments DONE, built: `RHTower/WeilZetaSquareMoments.lean`. It contains `momentRe`, the main term with an `O(hk·L)` error, `∫ω_L Z = O(L log L)` and `∫_{L/2}^{5L/2} Z = O(L log L)`.
  - L3 in progress: `RHTower/WeilZetaSquareAveraging.lean`. The pointwise window bound and integration by parts are done; the integrated inequality `exists_averaged_ge` is being finished.
  - A parallel session's `RHTower/WeilConeBoundaryDilationInequality.lean` (case `f = v = 0`, abscissa ½) overlaps L1–L2. Please build on the modules above rather than re-deriving L3–L5.
- 2026-10-07: FORMALIZED, standard axioms, `lake --old build` green, wired, lint clean.
  - Theorem `RHTower.WeilZetaSquare.eq_delta_of_weilPositiveFull`: `a = δ₁` for `Λ⋆a + μ⋆f + v` with `a`, `f` absolutely convergent past ½ (`f(1) = 0`) and `v` regular with continuation bounded on the line.
  - `eq_delta_and_eq_zero_of_weilPositiveFull`: when `f` is finitely supported, also `f = 0` and `v = 0` (via the finite-type theorem).
  - `exists_weilPositive_iff`: within that class, existence of a Weil-positive completion ⟺ RH.
  - Modules:
    - `RHTower/WeilZetaSquareBoundaryInequality` (L1, L2);
    - `RHTower/WeilZetaSquareMoments` (twisted moments `momentRe`, main term with `O(hk·L)` error, window and interval mean squares);
    - `RHTower/WeilZetaSquareAveraging` (L3: `exists_averaged_ge`);
    - `RHTower/WeilZetaSquareDilationRigidity` (L4 and the theorem: `exists_abs_momentRe_log_sub_le`, `integral_truncated_eq`, `coeffB_nonneg`, `coeffB_eq`, `tsum_a_gcd_div_eq_one`);
    - `HTGeometry/GcdWeightedSeriesInversion` (L5: `eq_zero_of_tsum_gcd_mul_div_eq_zero`, sieve recurrence `S_{P∪p}(n) = S_P(n) − S_P(np)`, no divisor bound).
  - The parallel session's `WeilConeBoundaryDilationRigidity` proves the pure-dilation case `f = v = 0` at the boundary class `Σ|a(n)|n^{−1/2}(1+log n) < ∞`, by log averaging with Littlewood's floor and Phragmén–Lindelöf. It complements this card, which covers the Möbius and regular parts and needs a δ-margin.
