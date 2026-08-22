# Wasserstein barycenter of positive definite operators (Kim–Mer–Pálfia, arXiv:2607.29142)

- **ID:** kmp-2026-wass-barycenter
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** arXiv:2607.29142v1 (31 Jul 2026), `W_M_of_positive_operators_V16.tex`
- **Statement:** Formalize, unconditionally and closed, every lemma/theorem/provable proposition of
  the paper that mathlib and the hgt corpus do not already own.

## Goal
Full Lean 4 formalization of the operator-level Bures–Wasserstein barycenter theory:
existence/uniqueness of the Wasserstein mean of positive definite operators, its ODE/no-dice/SLLN
approximation theory, and its order/norm inequalities.  Along the way the corpus gains a reusable
C*-algebraic **operator geometric mean** layer (`#`, `#_t`, Riccati, congruence, self-duality,
joint concavity, AM–GM–HM), which mathlib does not have.

## Corpus/mathlib audit (2026-08-22)
- mathlib v4.32.2 **has**: `CFC.sqrt`, `CFC.rpow`, `CFC.nnrpow`, `CFC.conjSqrt`,
  `CFC.monotone_sqrt`, `CFC.monotone_rpow` (p∈[0,1]), `CFC.concaveOn_sqrt`, `CFC.concaveOn_rpow`,
  `CStarAlgebra.ringInverse_le_ringInverse` (antitone inverse), `IsStrictlyPositive`.
- mathlib **lacks**: operator geometric mean `A # B`, weighted `A #_t B`, Riccati characterization,
  congruence invariance, self-duality, AM/GM/HM chain, joint concavity, Kubo–Ando means,
  Wasserstein/Karcher/power means, Bures–Wasserstein distance of operators.
- hgt corpus **has**: `positiveMatrixGeometricMean` (matrices only, `HTGeometry/
  ConstitutivePositiveConeMidpointRecovery.lean`), Bures *reporter/minimax* laws (unrelated),
  `kantorovichRubinstein` (W1 dual, unrelated).
- hgt corpus **lacks**: everything operator-geometric-mean and Wasserstein-mean related.

## Paper inventory (target list)
Sec 2: Thm 2.1 (Gelbrich/MPZ), Def 2.2, Thm 2.3 (Minh) — *cited literature, not proved in paper*.
Sec 3: Thm 3.1 (min problem), **Thm 3.2** (strict concavity of `tr_ex ∘ sqrt`), **Lem 3.3** (order
bounds on fixed points), **Lem 3.4** (homogeneity), Thm 3.5 (IFT, cited), Thm 3.6, Cor 3.7, Thm 3.8,
Cor 3.9, **Lem 3.10** (`‖AYB‖²` two-sided spectral bounds), **Lem 3.11** (`⟨DΦ(X)Y,Y⟩ ≥ α³/2β⁴‖Y‖²`),
Thm 3.12, Rmk 3.13, **Lem 3.14** (iso ↔ adjoint iso), **Thm 3.15** (`AYA+BYB+CYC` iso), Thm 3.16.
Sec 4: Rmk 4.1, Thm 4.2 (cited OP), **Lem 4.3** (renorming / logarithmic norm), Prop 4.4,
Thm 4.5 (Banach–Finsler contraction), **Lem 4.6**, **Lem 4.7** (flow invariance of `[αI,βI]`),
Cor 4.8, **Lem 4.9/4.10** (Taylor), **Lem 4.11/4.12**, Cor 4.13, **Prop 4.14**, **Prop 4.15**,
**Thm 4.16** (No-dice).
Sec 5: Thm 5.1, **Lem 5.2** (Etemadi weight recursion), Thm 5.3 (SLLN).
Sec 6: **Prop 6.1** (1)–(5)+fixed point, **Thm 6.2** (Loewner bounds), **Cor 6.3**, Cor 6.4
(Lie–Trotter), **Thm 6.5** (norm bounds), Rmk 6.6, **Thm 6.7**, **Thm 6.8** (power mean),
**Thm 6.9** (block-matrix minimum), **Lem 6.10** (`A◇_t B = B◇_{1-t} A`), **Thm 6.11**,
**Thm 6.12**, **Thm 6.13**, **Cor 6.14**, **Prop 6.15**, **Lem 6.16** (Kantorovich converse AM–GM),
**Thm 6.17** (near-order two-sided comparison with dual).

## Module plan (`formal/GaloisForLFunctions/HTGeometry/BuresWasserstein/`)
1. `OperatorGeometricMean.lean` — `CFC.wgm t a b`, `CFC.gm`, Riccati + uniqueness, symmetry,
   congruence invariance, self-duality, monotonicity, max characterization, AM/GM/HM,
   joint concavity, `X A⁻¹ X` joint operator convexity.
2. `WassersteinEquation.lean` — `IsWassersteinPoint`, equivalence of the two forms of (gradF),
   Lem 3.3, Lem 3.4.
3. `SqrtStrictConcavity.lean` — Thm 3.2 operator core (equality case of operator concavity of sqrt).
4. …further modules per section.

## Log
- 2026-08-22 — created; paper downloaded to `scratchpad/paper/`; corpus + mathlib audit done.

## Lean progress ledger

Directory: `formal/GaloisForLFunctions/HTGeometry/BuresWasserstein/`
(all wired into `GaloisForLFunctions.HTGeometry`; all `lake build` green, no `sorry`).

### `OperatorGeometricMean.lean` — new mathlib-gap layer (C*-algebraic geometric mean)
`wgm`, `gm` (`#ᴳ`), `gm_riccati`, `gm_unique`, `riccati_symm`, `gm_comm`, `ringInverse_sandwich`,
`gm_ringInverse` (self-duality), `gm_conjugate` (congruence), `gm_one_left/right`,
`gm_mono_right/left/mono`, `le_gm_of_conj_le` (maximality), `le_sqrt_of_mul_self_le`,
`conj_sqrt_le_sqrt_conj` (**Hansen inequality for √, proved by the maximality characterisation**),
`mul_self_le_of_le_smul_one`, `smul_one_le_mul_self_of_le`, `sqrt_add_sqrt_le_one_add`,
`gm_add_gm_le`, `gm_le_arith` (AM–GM), `harm_le_gm` (GM–HM), `ringInverse_smul`,
`rpow_half_ringInverse`, `gm_ringInverse_left`, `gm_smul` (joint homogeneity), `gm_smul_self`,
`wgm_half/zero/one`, `wgm_mono_right`, `conj_ringInverse_sub_eq`, `le_conj_ringInverse`,
`conj_ringInverse_eq_at`, `isStrictlyPositive_sum_smul`, `conj_ringInverse_convex`
(**joint operator convexity of `(x,a) ↦ x a⁻¹ x`, no weight normalisation needed**),
`gm_concave` (**joint operator concavity of `#`**), `gm_ringInverse_self`, `sum_smul_conjugate`.

### `WassersteinEquation.lean`
`IsWassersteinPoint`, `isWassersteinPoint_iff_sqrt` (the two forms of (gradF) agree),
`IsWassersteinPoint.mem_Icc` (**Lemma 3.3**), `isWassersteinPoint_smul` (**Lemma 3.4**),
`isWassersteinPoint_reindex` (**Prop 6.1(3)**), `isWassersteinPoint_repeat` (**Prop 6.1(4)**),
`IsWassersteinPoint.unitary_conjugate` (**Prop 6.1(5)**),
`isWassersteinPoint_insert_self` (**Prop 6.1 "furthermore"**).

### `WassersteinBounds.lean`
`sq_sum_smul_le_sum_smul_sq` (operator convexity of `t²`),
`ringInverse_sum_le_sum_ringInverse` (harmonic–arithmetic),
`IsWassersteinPoint.le_arithMean` + `two_sub_harm_le` (**Theorem 6.2**),
`two_sub_arithMean_le_ringInverse` (**Corollary 6.3, second inequality, operator form**),
`le_sqrtMean_ringInverse` / `sqrtMean_ringInverse_le` (**Theorem 6.7 (i),(ii)**).

### `SqrtOperatorConcavity.lean`
`smul_sqrt_add_smul_sqrt_le`, `eq_of_sqrt_smul_add_eq` (**Theorem 3.2, operator core**),
`eq_zero_of_isSelfAdjoint_of_mul_self_eq_zero`.

### `EtemadiWeightRecursion.lean`
`etemadiProd`, `etemadiWeight`, `etemadiTotal`, `etemadi_recursion`, `etemadiTotal_eq`,
`etemadiWeight_antitone`, `etemadiTotal_tendsto_atTop` (**Lemma 5.2**).

## No-go recorded
`X ↦ (X^{1/2} A X^{1/2})^{1/2}` is **not** operator monotone, so the Thompson-metric
contraction route to existence/uniqueness (the commented-out Lemma in the source `.tex`) is dead.
Counterexample mechanism: for `A = P + ε` with `P = |e⟩⟨e|` rank one, `f(X) → ⟨e,Xe⟩^{1/2}·P_{X^{1/2}e}`,
and two rank-one positive operators are comparable only when their ranges coincide; take
`X = 1 ≤ Y = 1 + tQ` with `Y^{1/2}e ∦ e` and test against `z ⊥ Y^{1/2}e`, `⟨e,z⟩ ≠ 0`.
Hence existence/uniqueness needs the paper's Fréchet-derivative + homotopy (or ODE) machinery.

## Log
- 2026-08-22 — created; paper downloaded; corpus + mathlib audit done.
- 2026-08-22 — five modules landed (list above); no-go on the Thompson route recorded.

### `TwoVariableWassersteinMean.lean` (complete two-variable theory)
`wassParam` (`1 ∇_t (a⁻¹#b)`), `wass2` (`a ◇[t] b`), `gmInv_riccati`, `wassParam_isSelfAdjoint`,
`commute_wassParam_gmInv`, `wassParam_isStrictlyPositive_of_mem_Icc`, `wass2_isStrictlyPositive`,
`wass2_ringInverse`, `gm_left_wass2`, `gm_right_wass2`, **`wass2_solves`** (existence for the
two-point Wasserstein equation), `conj_mul_self_mul_conj`, `wass2_eq_conj` (Bhatia–Jain–Lim closed
form), `wass2_expansion`, **`wass2_symm`** (Lemma 6.10), **`wass2_unique`** (Theorem 6.11 —
uniqueness for all real `t`), `conj_ringInverse_cancel`, `ringInverse_conj_cancel`,
`wass2_conj_ringInverse`, **`wass2_le_of_conj_ringInverse_le`** (Theorem 6.9, Schur form),
`NearLE` (`⪯ᴳ`), `two_le_add_ringInverse`, **`wass2_ringInverse_nearLE`** (Proposition 6.15).

### `WassersteinNormBounds.lean`
`norm_cfcSqrt_mul_self`, `norm_cfcSqrt`, `cfcSqrt_smul`, `le_smul_one_norm`,
`norm_le_of_le_smul_one`, **`IsWassersteinPoint.norm_le`** and
**`IsWassersteinPoint.norm_sqrtMean_le`** (Theorem 6.5, both halves).

### `WassersteinDual.lean`
`IsDualWassersteinPoint`, `isDualWassersteinPoint_iff`, `ringInverse_conj_rpow_half`,
`rpow_half_mul_ringInverse_mul_rpow_half`, `isDualWassersteinPoint_iff_sqrtInv`,
**`IsDualWassersteinPoint.one_le_sqrtInvMean`** and **`quasiArith_le_one`** (Theorem 6.13).

### `WassersteinBounds.lean` (added)
`IsWassersteinPoint.map_two_sub_harm_le`, `map_two_sub_arithMean_le_ringInverse` (Corollary 6.3).

## Corpus assets found for the analytic core
`formal/GaloisForLFunctions/HTGeometry/HilbertSchmidtOperator.lean` already builds a full
coordinate-free Hilbert–Schmidt layer that mathlib lacks: `ContinuousLinearMap.IsHilbertSchmidt`,
`hsNormSq`, `hsNorm`, `hsInner` with the complete inner-product API (sesquilinearity,
conjugate symmetry, positive definiteness, Cauchy–Schwarz, triangle inequality), the two-sided
ideal property `IsHilbertSchmidt.comp_left/comp_right`, and `IsHilbertSchmidt.adjoint`.
This is the layer Lemma 3.10/3.11 need.

### `KantorovichConverse.lean`
`kantorovich` (`K(h) = (1+h)/(2√h)`), `kantorovich_inv`, `one_add_div_two_le_mul_sqrt`
(convexity of `t² - 2κt + 1` propagates endpoint inequalities), `smul_one_add_le_smul_cfcSqrt`
(the CFC transfer), `ringInverse_le_of_smul_one_le`, `smul_one_le_ringInverse_of_le_smul_one`,
**`arith_le_smul_gm`** (Lemma 6.16).

### `WassersteinNearOrder.lean`
`wassKappa`, `one_le_kantorovich`, `one_le_wassKappa`, `wassKappa_pos`, `kappa_eq_max`,
`mem_Icc_ringInverse`, `mem_Icc_of_ringInverse`, **`gm_dual_primalInv_bounds`**
(`κ⁻² ≤ D # P⁻¹ ≤ 2κ-1`), **`nearLE_smul_primal_dual`** and **`nearLE_dual_smul_primal`**
(Theorem 6.17, both halves).

### `WassersteinDual.lean` (added)
`isDualWassersteinPoint_smul`, **`IsDualWassersteinPoint.norm_quasiArith_le`** (Corollary 6.14).

### `HTGeometry/OperatorLyapunovEquation.lean` (new general asset)
`lyapunov` (`Λ_x : y ↦ xy + yx` as `A →L[ℝ] A`), `lyapunov_apply/add/smul_one`,
`norm_lyapunov_le`, `norm_sub_midpoint_le`, **`isUnit_lyapunov`** (Neumann-series proof from a
Loewner interval), **`isUnit_lyapunov_of_isStrictlyPositive`**.
This replaces the integral representation `∫₀^∞ e^{-tx} · e^{-tx} dt` used by the paper: the
Lyapunov operator is a Neumann perturbation of `2c·id` around the midpoint of `[α,β]`, with
`‖Λ_{x-c}‖ ≤ β - α < α + β = 2c`.

## Analytic-core plan (Sections 3–5)
Established route, replacing the paper's semigroup-integral machinery where possible:
1. **Lyapunov invertibility** ✅ (`OperatorLyapunovEquation.lean`).
2. **Fréchet derivative of `CFC.sqrt`**: apply the inverse-function theorem to `y ↦ y*y`
   (a bounded bilinear map, so strictly differentiable with derivative `Λ_y`); step 1 gives
   invertibility at `y = √a`, so `D(√)(a) = Λ_{√a}⁻¹`.
3. **Derivative of `X ↦ Aᵢ # X⁻¹`** by the chain rule with mathlib's derivative of `Ring.inverse`.
4. **Lemma 3.10** (two-sided HS bounds) on top of the corpus HS layer.
5. **Lemma 3.11**: positivity of `⟨DΦ(X)Y, Y⟩_HS`.  Key discovery: the paper's
   `∫ B(t) Y B(t) dt ≥ 0` can be replaced by the Lyapunov identity — if `u y + y u = v` then
   `⟨y, u⁻²-weighted v⟩` reduces to `tr(y a y b) = ‖√a y √b‖²_HS ≥ 0` by trace cyclicity alone.
6. **Theorem 3.12** (`Σ₂` case) by the implicit function theorem in the Hilbert space
   `SL²_ex(H)`, where coercivity gives invertibility directly (Lax–Milgram).
7. **Theorem 3.16** (general `ℙ`) additionally needs Lemma 3.14 (duality `S¹* = S`) and
   Theorem 3.15 (spectral permanence `σ(L|_{S¹}) ⊆ σ(L|_{S²})`, Drivaliaris–Yannakakis).
8. Sections 4–5 (renorming, Banach–Finsler contraction, no-dice, SLLN) sit on top of 6–7.

## Log
- 2026-08-22 — Section 6 essentially complete (6.1–6.3, 6.5, 6.7, 6.9–6.11, 6.13–6.17);
  Section 3 partial (3.2, 3.3, 3.4); Section 5 Lemma 5.2.  Analytic core started with the
  Lyapunov layer.

### `HTGeometry/CFCSqrtDerivative.lean` (new mathlib gap: differentiability of `CFC.sqrt`)
`saProj` (self-adjoint projection `x ↦ (x+x⋆)/2`, as `A →L[ℝ] A`) with `saProj_apply`,
`isSelfAdjoint_saProj`, `saProj_of_isSelfAdjoint`, `saProj_saProj`, `saProj_mul_saProj`,
`norm_saProj_le`, `commute_lyapunov_saProj`;
`saSquare` / `saSqrt` (the twist that makes both maps globally defined on `A`),
`saProj_saSqrt`, `saSquare_saSqrt`, `saSqrt_of_isSelfAdjoint`, `saProj_saSquare`,
`saSqrt_saSquare`, `saSquare_of_isSelfAdjoint`;
`hasStrictFDerivAt_saSquare` (derivative `Λ_{Py} ∘ P + (1 - P)`);
`Units.val_inv_commute`, `isUnit_mul_idem_add_compl` (general ring lemma: `L P + (1-P)` is a unit
when `P` is idempotent, commutes with `L`, and `L` is a unit), `isUnit_saSquare_fderiv`;
`unitsToEquiv` (a unit of `E →L[ℝ] E` as a `ContinuousLinearEquiv`);
`isStrictlyPositive_saProj_of_norm_lt`;
**`hasStrictFDerivAt_saSqrt`** — the CFC square root is strictly Fréchet differentiable at every
strictly positive element, the derivative being the inverse of `Λ_{√a} ∘ P + (1-P)`;
**`lyapunov_fderiv_saSqrt`** — the derivative solves `√a · (D√(a)h) + (D√(a)h) · √a = h`
on self-adjoint directions.
Plus `exists_pos_smul_one_le` in `OperatorLyapunovEquation.lean`.

The subtype `selfAdjoint A` is avoided entirely: `saSquare` and `saSqrt` are globally defined
mutually inverse maps near a strictly positive point, and the derivative of `saSquare` is block
diagonal for the decomposition `A = A_sa ⊕ A_asa`, so its invertibility is exactly the
invertibility of the Lyapunov operator.

### `HTGeometry/HilbertSchmidtSandwichBounds.lean` (**Lemma 3.10**)
`ContinuousLinearMap.hsNormSq_comp_left_le`, `le_hsNormSq_comp_left`,
`hsNormSq_comp_right_le`, `le_hsNormSq_comp_right`, **`hsNormSq_sandwich_bounds`**.
Stated vector-wise (`c‖y‖² ≤ ‖S y‖² ≤ C‖y‖²`) so no trace theory is needed; the right factor is
handled by adjoints, using `IsHilbertSchmidt.hsNormSq_adjoint` from the corpus HS layer.

## Next concrete steps
1. HS inner-product adjunctions `⟨A∘S, T⟩_HS = ⟨S, A†∘T⟩_HS` and `⟨S∘B, T⟩_HS = ⟨S, T∘B†⟩_HS`
   (the second from `hsInner_adjoint_adjoint` + conjugate symmetry).
2. Positivity `⟨a Y b, Y⟩_HS = ‖√a Y √b‖²_HS ≥ 0` for `a, b ≥ 0` and `Y` self-adjoint — this is
   the replacement for the paper's `∫ B(t) Y B(t) dt` computation.
3. Chain rule for `Z ↦ a # Z` (conjugation maps as CLMs + `hasStrictFDerivAt_saSqrt`) and for
   `X ↦ Aᵢ # X⁻¹` (mathlib's derivative of `Ring.inverse`).
4. Lemma 3.11 from 2 + 3 + Lemma 3.10.
5. Implicit function theorem + homotopy continuation ⇒ Theorems 3.6, 3.8, 3.12, 3.16.

### `HTGeometry/HilbertSchmidtSandwichPositivity.lean` (**core of Lemma 3.11**)
`ContinuousLinearMap.hsInner_comp_left` (`⟨A∘S, T⟩_HS = ⟨S, A†∘T⟩_HS`, termwise),
`hsInner_comp_right` (`⟨S∘B, T⟩_HS = ⟨S, T∘B†⟩_HS`, via `hsInner_adjoint_adjoint` and conjugate
symmetry), **`hsInner_sandwich_eq`** (`⟨(s†s) Y (t t†), Y⟩_HS = ⟨sYt, sYt⟩_HS`),
**`re_hsInner_sandwich_nonneg`**, **`re_hsInner_sandwich_eq_hsNormSq`**.
This is the trace-free replacement for the paper's `∫₀^∞ B(t) Y B(t) dt ≥ 0`: no trace, no
semigroup integral, only the two adjunctions of the Hilbert–Schmidt inner product.

## Log
- 2026-08-22 (cont.) — analytic core layers 1–2 and the HS positivity landed:
  `OperatorLyapunovEquation`, `CFCSqrtDerivative`, `HilbertSchmidtSandwichBounds` (Lemma 3.10),
  `HilbertSchmidtSandwichPositivity` (core of Lemma 3.11).

## mathlib inputs verified available for step 3
* `NormedRing.hasFDerivAt_ringInverse (x : Rˣ) : HasFDerivAt Ring.inverse (-mulLeftRight 𝕜 R ↑x⁻¹ ↑x⁻¹) x`
  (needs `[HasSummableGeomSeries R]`, automatic for a complete normed ring);
* `contDiffAt_ringInverse 𝕜 (x : Rˣ) : ContDiffAt 𝕜 n Ring.inverse x`, hence
  `ContDiffAt.hasStrictFDerivAt` gives the **strict** derivative needed by the inverse function
  theorem;
* `HasStrictFDerivAt.mul'` (noncommutative product rule), `HasStrictFDerivAt.comp`,
  `HasStrictFDerivAt.to_local_left_inverse`, `ContinuousLinearEquiv.equivOfInverse`;
* `CFC.continuousOn_sqrt`, `CFC.sqrt_mul_self`, `CFC.sqrt_mul_sqrt_self`;
* `CStarAlgebra (E →L[ℂ] E)` from `Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap`
  (the order instances `PartialOrder`/`StarOrderedRing` are *not* global — carry them as
  instance-implicit variables, as the BuresWasserstein modules do).

### `BuresWasserstein/GeometricMeanDerivative.lean`
`conjMap` (`x ↦ b x b` as `A →L[ℝ] A`), `conjMap_apply`, `conjMap_apply'`,
`isSelfAdjoint_conjMap`, `gmMap` (the geometric mean in its second argument, extended to all of
`A`), `gmMap_eq_gm`, **`hasStrictFDerivAt_gmMap`** (strict differentiability of `Z ↦ a # Z` at
strictly positive `Z`, derivative `h ↦ a^{1/2} Λ_{√c}⁻¹(a^{-1/2} h a^{-1/2}) a^{1/2}`),
`isStrictlyPositive_conjMap_rpow`.

Note for reuse: `HasStrictFDerivAt.comp` needs `(f := …) (g := …)` supplied explicitly here —
higher-order unification picks `f := id` otherwise.

### `BuresWasserstein/WassersteinFieldDerivative.lean`
`hasStrictFDerivAt_ringInverse` (strict version, via `contDiffAt_ringInverse`), `gmInvMap`
(`X ↦ a # X⁻¹`), `gmInvMap_eq_gm`, **`hasStrictFDerivAt_gmInvMap`**, `wassField`
(the paper's `Φ(X) = ∑ wᵢ (1 - Aᵢ # X⁻¹)`), **`wassField_eq_zero_iff`** (zeros = Wasserstein
points), **`hasStrictFDerivAt_wassField`**.

### `HTGeometry/OperatorLoewnerVectorBounds.lean`
`re_inner_nonneg_of_nonneg`, `smul_one_le_re_inner`, `sq_mul_norm_sq_le_norm_apply_sq`
(`m ≤ T ⟹ m²‖v‖² ≤ ‖Tv‖²`), the bridge that feeds the Hilbert–Schmidt sandwich estimates.

### `BuresWasserstein/LyapunovFormPositivity.lean` (**Lemma 3.11 core, quantitative**)
`lyapunov_solution` (`u²(u⁻¹yu⁻² + u⁻²yu⁻¹)u² = uy + yu`),
**`re_hsInner_lyapunovSolution`** (`Re⟨q, y⟩_HS = ‖u^{-1/2}yu⁻¹‖²_HS + ‖u⁻¹yu^{-1/2}‖²_HS`),
`re_hsInner_lyapunovSolution_nonneg`, `smul_one_le_rpow_neg_half`,
**`re_hsInner_lyapunovSolution_lower`** (`2β⁻³‖y‖²_HS ≤ Re⟨q, y⟩_HS` when `u ≤ β`).
Plus `le_hsNormSq_sandwich` added to `HilbertSchmidtSandwichBounds.lean`.
