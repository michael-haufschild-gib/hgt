# HB: Maass–Selberg relation for the Eisenstein line model (E4 brick)

- **ID:** HB-MS-001
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper; classical) → Lean
- **Source:** docs/notes.md rows 36, 37, 40; card `3-formalized/hb-modular-laplacian-spectral-assembly.md` (input E4); frontier map HB "on-line spectral comparison"
- **Statement:** For `Y ≥ 1` and parameters `u, v` in the quarter-plane `Ω = {−½ < Re u, 0 < Im u}`, with `E_u := E*(·, ½+u)` the completed Eisenstein Fourier model (`eisensteinLineModel u`), `A(u) := Λ(1+2u)`, `B(u) := Λ(2u)`, and `Λ^Y E_u := E_u − 1_{y>Y}(A(u)y^{½+u} + B(u)y^{½−u})` on `fd`:
  `(u−v)(u+v)·∫_fd Λ^Y E_u · Λ^Y E_v dμ = (u−v)A(u)A(v)Y^{u+v} + (u+v)[A(u)B(v)Y^{u−v} − B(u)A(v)Y^{v−u}] − (u−v)B(u)B(v)Y^{−u−v}`
  (bilinear pairing, no conjugation). Diagonal on the line (`u = it`, `E_u` real): `‖Λ^Y E*(·,½+it)‖² = 2‖Λ‖²·log Y + 4‖Λ‖²·Re(Λ'/Λ)(1+2it) + Im(Λ(1+2it)²Y^{2it})/t`.

## Goal
The relation is the Maass–Selberg value `⟨F,1⟩ = ‖Λ¹E*‖²` for the literal on-line comparison source
`F = (Λ¹E*)²` (frontier map HB, "on-line spectral comparison"), the truncated-domain input of row 36
for the line family (the corpus's truncated Stokes theorem covers only `Re s > 1`), and the `c₀`
consistency of row 37. It also certifies the resonant-state receivers (`u = ρ/2 − ½ ∈ Ω`): the exact
cutoff-exponent receiver and the Cauchy–Schwarz invariant `cos² = 4σ(1−σ)`. Receiver-side by
CANNOT-366; no RH content.

## Gates
- [x] 0 → 1  in-progress: well-posed; unfolding route fixed (below)
- [x] 1 → 2  fully-proven: paper proof below is classical (Maass 1949, Selberg 1956; Iwaniec *Spectral methods* Prop. 6.8 by Green; unfolding form as in Zagier 1981)
- [x] 2 → 3  formalized: `RHTower.maassSelberg_lineModel` (Ω × Ω), `RHTower.truncatedPairing_diag`, `RHTower.integral_norm_sq_truncatedLineModel_line` (line norm); axioms standard; wired into `RHTower.lean` (2026-09-18)
- [ ] 3 → 4  not applicable

## Approach (unfolding, no arc integration)
Region `R = {Re u > Re v > ½}`. There `E_u` is the completed Poincaré series (corpus
`d4BM_actualCompletedPoincare_eq_canonicalCuspLeg`).
1. Zero mean above `Y`: `∫_fd Λ^Y E_u · Λ^Y E_v = ∫_fd Λ^Y E_u · E_v` (the `x`-mean of `Λ^Y E_u` vanishes for `y > Y ≥ 1`).
2. Horoball lemma: for `z ∈ fd` and a primitive pair `(c,d)` with `c ≠ 0`, `Im(γ z) = y/|cz+d|² ≤ 1`; hence on `fd`, `Λ^Y E_u = A(u)·½Σ_p Im(γ_p z)^{½+u}·1_{Im γ_p z ≤ Y} − B(u)y^{½−u}1_{y>Y}`.
3. Unfold the first sum (`tsum_setIntegral_fd_eq_two_mul_setIntegral_modularStrip`, `φ = y^{½+u}1_{y≤Y}E_v`): `= A(u)∫_0^Y y^{u−3/2}c_v(y)dy = A(u)[A(v)Y^{u+v}/(u+v) + B(v)Y^{u−v}/(u−v)]`.
4. Second term: `−B(u)∫_Y^∞ y^{−u−3/2}c_v(y)dy = B(u)A(v)Y^{v−u}/(v−u) − B(u)B(v)Y^{−u−v}/(u+v)`.
5. Integrability on `R`: truncated real Poincaré sum `≤ C(y^{½−a}1_{y>Y} + 1_{y≤Y})`, `|E_v| ≤ C(y^{½+Re v} + y^{½−Re v} + 1)` on `fd`; product integrable against `dμ` iff `Re v < Re u`.
6. Continuation: both sides of the cleared identity are holomorphic in `u ∈ Ω` (parametric integral over `fd ∩ {y ≤ Y}` with the corpus majorants, plus the cusp tail) and in `v`; identity theorem on `Ω` (convex) in `u`, then in `v`.
7. Diagonal: divide by `(u−v)`, let `v → u`; on the line use `B(it) = conj A(it)`, `Λ'(2it) = −conj Λ'(1+2it)`.

## Lean plan
- MS-1 `EisensteinHoroballBound`: horoball lemma on mathlib's `fd` (elementary, `nlinarith`).
- MS-2 `EisensteinMaassSelbergAlgebra`: the explicit right-hand side, its removable-singularity form, the `v`-derivative at `v = u`, the line specialisation.
- MS-3 `EisensteinLineZeroMean`: `∫_0^1 tail_u(x,y)dx = 0` for every `u`, `y > 0` (general-`u` version of `EisensteinLineTailParseval`).
- MS-4 `EisensteinTruncatedPoincareOnDomain`: identity of step 2 on `fd` for `Re u > ½`.
- MS-5 `EisensteinMaassSelbergRegion`: steps 3–5 (unfolding, power integrals, integrability).
- MS-6 `EisensteinTruncatedPairingHolomorphic`: step 6 holomorphy.
- MS-7 `EisensteinMaassSelbergLineModel`: identity theorem; `EisensteinTruncatedNormLine`: step 7.
- MS-8 application: sign law for `(Λ¹E*)²` (fourth-moment bound as in `EisensteinLineSourceMeanSquare`).

## Log
- 2026-09-18 — created in 1-in-progress after the HB route audit (CANNOT-366); unfolding route chosen over arc integration because the corpus's Stokes chains cover only the cubic and Bochner currents of the Poincaré family.
- 2026-09-18 — MS-1–MS-5 CLOSED IN LEAN (region identity). Modules (namespace `RHTower`, all `lake build` green, axioms `propext, Classical.choice, Quot.sound`): `EisensteinHoroballBound` (`im_smul_le_one_of_mem_fd`), `EisensteinLineZeroMean` (`setIntegral_Ioc_cuspLeg`: period mean = Weyl constant part, every `u`), `EisensteinMaassSelbergAlgebra` (`msRight`, `msDiag`, `hasDerivAt_msRight`, the limit lemma `eq_neg_msDiag_div_of_cleared`, the derivative functional equation `deriv_reflectedCompletedLambda_one_sub`, `msLineValue`), `EisensteinTruncatedRowSum` (`eisensteinLineModel_eq_rowSum`, `truncatedLineModel_eq_truncatedRowSum`), `EisensteinHyperbolicChart` (coordinate formula, cusp rectangle, strip slab, product Fubini), `EisensteinLineModelBounds` (`‖tail‖ ≤ tailConst u e^{−2πY}`, joint continuity, `continuous_eisensteinLineModel`), `EisensteinRowSumMajorant`, `EisensteinFundamentalDomainIntegrability` (`integrableOn_fd_rpow`, `integrableOn_coord_iff`), `EisensteinUnfoldedRowSum` (`integrableOn_unfoldedIntegrand_strip`, `setIntegral_truncatedRowSum_mul_eq`), `EisensteinMaassSelbergCuspIntegrals` (`setIntegral_cusp_eq`, `setIntegral_slab_eq`), `EisensteinMaassSelbergRegion`:
  `maassSelberg_region : 1/2 < v.re → v.re < u.re → v ∈ Ω → 1 ≤ Y → (u−v)(u+v) ∫_fd Λ^Y E_u · Λ^Y E_v = msRight u v Y`.
  Not yet in the umbrella (wired after MS-7). Remaining: MS-6 (holomorphy of the truncated pairing in each parameter on `Ω`: dominated differentiation with a Cauchy-estimate bound; measurability of the parameter derivative as an a.e. limit of difference quotients), MS-7 (identity theorem in `u` then `v`; diagonal by the limit lemma; line value), MS-8.
  Note: the corpus module `ThetaCuspHawkingBMEisensteinLineEigenEquation` (in the umbrella) does not compile against the current `…ModeJetMajorants` (`WindowDominatedX` renamed); not needed here (the unfolding route uses `…LineInvariance`, which builds).
- 2026-09-18 — MS-6, MS-7 CLOSED IN LEAN. `EisensteinTruncatedPairingHolomorphic` (uniform bound `truncBound'` for every parameter, `tailConstBound`, measurability of the parameter derivative as a limit of difference quotients, `hasDerivAt_truncatedPairing` by `hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the Cauchy estimate `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`), `EisensteinMaassSelbergLineModel` (`clearedDefect` analytic in each variable, identity theorem in `u` at `z₀ = v + 1`, then in `v` at `z₀ = 1 + i`; `maassSelberg_lineModel`, `truncatedPairing_diag`, `truncatedPairing_line`), `EisensteinLineRealness` (conjugation symmetry `cuspLeg_conj`, reflection from the corpus (`ThetaCuspHawkingBMLiteralSourceReflection`, built: 3 modules), realness on the line, `deriv_reflectedCompletedLambda_conj`, `msLineValue_conj`, `integral_norm_sq_truncatedLineModel_line`). All wired into the umbrella; lint gate unchanged. STATUS MUST-352. Next: MS-7b (resonant-state corollaries: `A(u) = Λ(ρ) = 0` gives `‖Λ^Y E*(·,ρ/2)‖² = |Λ(ρ−1)|² Y^{1−Re ρ}/(1−Re ρ)`, the certified cutoff-exponent receiver), MS-8 (sign law for `(Λ¹E*)²`).
- 2026-09-18 — MS-7b CLOSED IN LEAN: `EisensteinResonantStateNorm` (`truncatedLineModel_conj/_neg`, `integral_norm_sq_eq_truncatedPairing` (sesquilinear = bilinear with `−conj u`), `integral_norm_sq_of_msA_eq_zero`, `integral_norm_sq_resonantState`, `resonant_norm_const_pos`); wired; STATUS MUST-353.
- 2026-09-18 — MS-8 CLOSED IN LEAN at height `e²`: `EisensteinArthurSource` (slices, `vMajorant` domination of the Arthur mean square, mean `≥ (5/2)‖Λ‖²`, integrability), `HBOnLineSignLawArthurSource` (`arthurL2`, mean = `Re msLineValue(t,e²)`, `hb_online_sign_law_arthur_source`). Height `1` blocked by the strength of the certified lower bound for `Re(ξ'/ξ)(1+2it)` (`c log log t / t`); see STATUS MUST-354. Wired; lint clean.

- 2026-09-18 — MS-8 CLOSED IN LEAN at height `1`. `XiLogDerivLineOneWindowLower` (`exists_xiZeroCount_window_ge_log`: one width `h`, `N(T+h) − N(T−h) ≥ log T`, from the corpus's `O(log T)` Riemann–von Mangoldt remainder `exists_xiZeroCount_routeKSmoothRVMCount_log_remainder`; `exists_re_logDeriv_xi_lineOne_loglog_lower'`: `Re(ξ'/ξ)(1+2it) ≥ c₁ log log t`; constant and `≥ A` corollaries), `EisensteinLineHeightOneMean` (`logDeriv_xi_eq_of_ne`, `msLineValue_one`, `msLineValue_one_re`, `conj_eisLineLambda_mul_deriv_re`, `exists_msLineValue_one_re_ge`: mean `≥ 3‖Λ‖²`), `EisensteinArthurSourceHeightOne` (`arthurOneCoord`, slices, `slice_gt_bound_div_le_vMajorant` generalized to every `y ≥ arcFloor`, `arthurOneL2`, `hb_online_sign_law_arthur_source_height_one`). The `O(log T)` count was already certified in the corpus; the missing brick was the bounded-window lower count. Wired; axioms standard; lint unchanged. STATUS MUST-355, MUST-356.
- 2026-09-19 — MS-9 (Hecke layer) CLOSED IN LEAN: `EisensteinHeckeCoefficient` (complex divisor power sum as `ζ ∗ n^{s}`, multiplicativity, geometric `p`-part, `whittakerCoeff_hecke`), `EisensteinHeckeOperator` (`heckeOp`, `sum_fourierPhase_div`, frequency reindexing through `heckeShift N = p(N+1)−1` with `Function.Injective.tsum_eq`, `heckeOp_tail`, `heckeOp_constantTerm`, `heckeOp_cuspLeg : T_p E_u = (p^u+p^{−u})E_u`). STATUS MUST-364. MS-10 (next): `T_p` on `Λ^Y E_u` and the Hecke–Maass–Selberg relation (mixed-height pairings reduce to the lower height by the zero-mean lemma; remainder supported in `(Y/p, pY]`), then the exact Hecke moments of the on-line source and of the resonant states (the memory's paper "Hecke-positivity test").
- 2026-09-19 — MS-10 CLOSED IN LEAN: `EisensteinHeckeMaassSelberg` (`truncatedLeg`, `heckeOp_truncatedLeg` with explicit `heckeRemainder`, `weyl_scalar_identity`, vanishing outside `(Y/p, pY]`, `lowerBandRemainder`/`upperBandRemainder`, `bandRect` + `setIntegral_fd_band_eq` + `setIntegral_bandRect_eq_iterated`, `setIntegral_band_mul_line`, `setIntegral_band_mul_tail_eq_zero`, `setIntegral_heckeRemainder_mul_trunc`, `heckeMaassSelberg`). STATUS MUST-365. MS-11 (next): closed-form band integral and the line/resonant specialisations (exact Hecke moments `⟨T_pΛ^Y u, Λ^Y u⟩` of the resonant state), then the positivity analysis of those moments.
- 2026-09-19 — MS-11 CLOSED IN LEAN: `EisensteinHeckeResonantMoment` (`heckeHermitianMoment`, `resonant_band_integral` via `integral_cpow`, `heckeHermitianMoment_resonant : ⟨T_pΛ^Yu,Λ^Yu⟩ = (p^u+p^{ū})‖Λ^Yu‖²`, real form `2Re(p^u)`). STATUS MUST-368. MS-12 (next): second moment / variance and two-prime moments of the Hecke-algebra state of the truncated resonant state.
- 2026-09-19 — MS-12 CLOSED IN LEAN: `EisensteinHeckeSecondMoment` (`setIntegral_fd_height`, resonant band remainders `lowerBandRemainder_resonant = −Λ(2u)y^{½−u}p^{−u}`, `upperBandRemainder_resonant = Λ(2u)y^{½−u}p^{u}`, their squared norms, `setIntegral_fd_normSq_heckeRemainder`, `heckeSecondMoment_resonant`, `_re`). STATUS MUST-369. The Hecke lane of HB is now exact through second order and identified with the Breit–Wigner profile (paper); no producer in it.
- 2026-09-19 — MS-13 CLOSED IN LEAN: `EisensteinResonantSpectralKernel.truncatedPairing_resonant_line` (Cauchy-kernel form of the resonant state's Eisenstein transform; STATUS MUST-370). The line-model card's Lean programme (MS-1–MS-13) is complete: Maass–Selberg, resonant norm, height-1 sign law, Hecke eigen-equation, Hecke–Maass–Selberg, exact Hecke moments, spectral kernel.
