# Boundary-class rigidity with infinite Möbius part via |ζ|²-weighting and twisted moments

- **ID:** weil-cone-boundary-mobius-part-twisted-moments (conjecture C539)
- **Stage:** 3-formalized (MUST-810)
- **Type:** THEOREM (formalized with the log moment also on `f`)
- **Source:** Opus loop row 538; extends MUST-804 (`WeilConeBoundaryDilation*`, `Λ ⋆ a + v`)
- **Statement (as formalized):** Let `a, f, v : ℕ → ℝ` with `Σ (|a(n)| + |f(n)|) n^{−½}(1+log n) < ∞`, `Σ |v(n)| n^{−½} < ∞`, `f(1) = 0`, `v(0) = v(1) = 0`. If `λ = Λ ⋆ a + μ ⋆ f + v` is full-cone Weil-positive, then `a = δ₁`, `f = 0`, `v = 0`. Hence RH.

## Why the MUST-804 route stops at `f = 0`
- With a Möbius part, `Φ = G + 1/(s−1) − V + Aζ'/ζ − F/ζ`, and the line term `Re(F/ζ)` is singular at the zeros.
- The softened weight `Z²/(Z²+η²)` turns it into `Re(F ζ̄)/(Z²+η²)`. Its integral is `≍ log(1/η)·Σ_γ 1/|ζ'(ρ)|`, a discrete negative moment that is not available unconditionally.

## Reduction (paper)
1. **Unsoftened weighting.** Multiply the boundary inequality by `Z² = |ζ|²`:
   `(Re A − 1)θ'Z² ≤ Im A·ZZ' − Re V·Z² − Re(F ζ̄)`. Every term is now regular, since `(F/ζ)|ζ|² = F ζ̄`.
2. **Right side `O(T log T)`.**
   - Integrate by parts: `ZZ' = ½(Z²)'`.
   - Take the endpoint `T₂ ∈ [2T, 2T+1]` where `Z(T₂)² ≤ ∫_{2T}^{2T+1} Z² ≤ C T log T`.
   - Bound the rest by the mean square, plus Cauchy–Schwarz for `∫|F||ζ| = O(T√log T)`.
3. **Left side `≥ c T log² T`.** For `f = (Re A − 1)w ≥ 0`, which is AP and `≥ ε` on windows, it suffices that `∫_T^{2T} f|ζ|² ≥ c(f) T log T` with `c(f) > 0`. Cauchy–Schwarz against `Q = Σ_{n≤T^{1/20}} n^{−½−it}`:
   `∫ f|ζ|² ≥ |∫ f ζ Q̄|² / ∫ f|Q|²`.
   - Numerator: the twisted first moment.
   - Denominator: the mean value theorem for Dirichlet polynomials.
   - Both are `T log M · M_ζ(f)(1+o(1))`. Here `M_ζ(f) = ∫ f dν_ζ`, and `ν_ζ` is the product of Poisson kernels `P_{p^{−½}}(θ_p)` on the Bohr torus `T^{primes}` (Fourier coefficients `(hk)^{−½}` at `h/k`). `ν_ζ` has full support, so `M_ζ(f) > 0`. Then `Re A ≤ 1` on the line, and MUST-804 Steps 5–6 give `A ≡ 1`.
4. **`v = 0`:** with `A ≡ 1`, averaging `−Re V Z² − Re(F ζ̄) ≥ 0` against `w` gives `M_ζ(Re V·w) ≤ 0` for all AP `w ≥ 0`. So `Re V ≤ 0` on the line; it has mean `v(1) = 0`, hence `V ≡ 0`.
5. **`f = 0` [OPEN CORE].** What remains is `Re(F(½+it) conj ζ(½+it)) ≤ 0` for all `t`.
   - Twisted first moments with weights `w` depending on the primes `≤ P` give `Re(H_P(θ)·conj ζ_{B,P}(θ)) ≤ 0` on `T^P`. Here `ζ_{B,P} = Π_{p≤P}(1−p^{−½}e^{iθ_p})^{−1}`, `H_P = Σ_{n₂ P-rough} F_{n₂}/n₂` and `F_{n₂} = Σ_{n₁ P-smooth} f(n₁n₂) n₁^{−½} χ_{n₁}^{−1}`.
   - If `F(1) = Σ f(n)/n = 0`: the negative measure `Re(F ζ̄_B)` has mass 0, so all its coefficients vanish. Then `Σ_j f(hj)/j = 0` for every `h`, and inclusion–exclusion gives `f = 0`.
   - If `F(1) < 0`: one needs equidistribution of `arg ζ_{B,P}` given the small primes (variance `½ Σ_{P₀<p≤P} 1/p → ∞`), independent of `H_P` up to `L²` tails. This is a finite-torus CLT, with no further analytic input on ζ.

## Analytic inputs in the corpus
- Twisted first moment `ZetaTwistedFirstMomentContour.norm_integral_twistedZeta_sub_diag_le`.
- First-moment-plus-Cauchy–Schwarz floor technique `MollifiedMeanSquareUnmollifiedPrimeFloor`.
- Mean square `ZetaVerticalMeanSquare`.
- Missing: a Dirichlet-polynomial mean value with an AP weight, and the Poisson-product positivity of `ν_ζ` on finite tori.

## Lean (MUST-810, standard axioms, wired after `ZetaLineTwistedSeriesMoment`)
- `RHTower/WeilConeBoundaryMobiusAveraging.lean` (Steps 1–2 at `δ = 0`):
  - `master_identity_boundary`, `zeta_mul_eq_boundary`, `dilSeries_one_eq_one_boundary`;
  - `re_boundaryNumerator_mul_conj_line_nonneg_boundary`: the numerator `H = Φζ` is continuous on the closed half-plane, so `Re(Hζ̄) ≥ 0` reaches the line by a one-sided limit;
  - `re_boundary_ge_boundary`, `pointwise_ge_boundary`;
  - `exists_averaged_ge_boundary`: integration by parts uses the line derivative `−iΣa(n)log n·n^{−½−it}`, bounded by the log moment, in place of the Cauchy estimate for `A′`.
- `RHTower/WeilConeBoundaryMobiusRigidity.lean` (Step 3 and the assembly):
  - `coeffB_nonneg_boundary`, `tsum_a_gcd_div_eq_one_boundary`, `eq_delta_of_weilPositiveFull_boundary` (`a = δ₁`);
  - `moebiusPart_regularPart_eq_zero_boundary`: Steps 4–5 through `WeilZetaSquare.eq_zero_of_re_regular_le_of_summable` and `ZetaUniformMoment.eq_zero_of_re_mul_conj_zeta_nonpos`;
  - `eq_vonMangoldt_of_weilPositiveFull_mobius_boundary`, `riemannHypothesis_of_weilPositiveFull_mobius_boundary`, `exists_mobiusBoundary_weilPositive_iff`.
- Side module: `RHTower/ZetaLineTwistedSeriesMoment.lean`, `ZetaLineTwist.tendsto_twistMean`. For every `h, k ≥ 1`, `(1/T)∫_T^{2T}(h/k)^{it}F(½+it)conj ζ(½+it)dt → Σ_n f(n)n^{−½}[h∣kn]√h/√(kn)`.

## Scope
- Like MUST-804/806/807/808, this is a uniqueness theorem (U). Existence in the class is equivalent to RH.
- The log moment on `f` is used only in Step 5. The `|ζ|²` Steps 1–4 need just `Σ|f|n^{−½} < ∞`.
- Not covered: dilations without the log moment, and non-multiplicative full-scale deviations. For the former, smoothing `A(½+it)` at scale `δ(T) → 0` reduces the extension to the sharp mean square `∫_T^{2T}|ζ′(½+it)|² ≪ T log³ T`, which is not yet in the corpus.

## Log
- 2026-10-07: created (Opus loop row 538) after MUST-804's `Λ ⋆ a + v` extension. Steps 1–4 reduce to classical mean values; Step 5 is the open core.
- 2026-10-07 (other Opus session, loop row 539): **Step 5 (open core) is closed in Lean**, under the log moment `Σ |f(n)| n^{−½}(1 + log n) < ∞`, with no CLT.
  - Theorem: `RHTower.ZetaUniformMoment.eq_zero_of_re_mul_conj_zeta_nonpos` (module `RHTower/AbsolutelyConvergentZetaSignRigidity`, standard axioms). If `Re(F(½+iy)·conj ζ(½+iy)) ≤ 0` for `y ≥ 8` and `f(1) = 0`, then `f(n) = 0` for all `n ≥ 1`.
  - The case `F(1) < 0` needs nothing extra. The Cesàro weight is `|M_{K!}(y)(1 + f(a)a^{−iy})|²`, with `M_D` the Möbius polynomial, and `M_{K!}` removes the diagonal: the limit is `f(a)²a^{−½} + O(Σ_{n>K}|f(n)|/n)` (`norm_tsum_weightLimit_sub_le`). Then `K → ∞`.
  - The limit and the infinite sum are exchanged via the uniform twisted first moment `‖∫_8^T ζ(½+iy)(p/q)^{iy}dy‖ ≤ C T √(1+log pq)` (`RHTower/ZetaTwistedFirstMomentUniform`). This is where the log moment enters.
  - For `δ > 0` the corollary `WeilZetaSquare.eq_delta_and_eq_zero_of_weilPositiveFull_mobius` (`RHTower/WeilZetaSquareMobiusRigidity`) gives `Λ⋆a + μ⋆f ∈ W ⇒ a = δ₁, f = 0`.
- 2026-10-07 (other Opus session, loop rows 540–541): **Step 4 (`v = 0`) is also closed in Lean, at `δ = 0`.**
  - Theorem: `RHTower.WeilZetaSquare.eq_zero_of_re_regular_le_of_summable` (module `RHTower/WeilZetaSquareRegularPartRigidity`, standard axioms). Hypotheses: `Σ|v(n)|/√n < ∞`, `Σ|f(n)|/√n < ∞`, `v(1) = 0`, and `Re V(½+it)|ζ|² + Re(F conj ζ) ≤ 0` for `t ≥ 8`. Conclusion: `v(n) = 0` for all `n ≥ 1`.
  - Mechanism: Möbius de-tilting `RHTower.WeilZetaSquare.exists_abs_momentP_sub_le`, which averages against `ω_L Π_{p≤K}|1−p^{−½−it}|²|1+v(a)a^{−it}|²`. It needs no Kakutani–Poisson full-support argument.
  - With the earlier Step 5 note (`ZetaUniformMoment.eq_zero_of_re_mul_conj_zeta_nonpos`, log moment on `f`), C539 now reduces in Lean to Steps 1–3: getting `A ≡ 1`, i.e. `a = δ₁`, in the boundary class with `f`, `v` present.
- 2026-10-07 (loop row 545): **Steps 1–3 closed in Lean at `δ = 0`**, so C539 is formalized in full (MUST-810), with the log moment also on `f`. The `δ > 0` chain (`WeilZetaSquare*`) used `δ` only for Cauchy estimates of `A′` and continuation of `E`. At `δ = 0` the line derivative of `A` and continuity on the closed half-plane replace them. Moved to 3-formalized.
