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

