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

## Session update — Lemma 3.11 CLOSED

**Lemma 3.11 (`re_hsInner_wassFieldDeriv_lower`) is now unconditional Lean.**
Constant obtained: `α²/(2β³)`, which **dominates** the paper's `α³/(2β⁴)` on `[α, β]`
(`α²/β³ ≥ α³/β⁴ ⟺ β ≥ α`), so the source statement follows a fortiori. The semigroup
integral `∫₀^∞ e^{-t√c} q e^{-t√c} dt` of the paper is replaced throughout by the
Lyapunov inverse; no exponential, no Bochner integral, no trace.

### New modules (all wired into `GaloisForLFunctions/HTGeometry.lean`, all `lake build` green,
### `#print axioms` = {propext, Classical.choice, Quot.sound})

1. `HTGeometry/HilbertSchmidtLyapunovInverse.lean`
   - `ContinuousLinearMap.sq_hsNorm`, `hsNorm_comp_left_le`, `hsNorm_comp_right_le`,
     `hsNormSq_zero`, `hsNorm_zero`, `hsNorm_sub_le`
   - `IsHilbertSchmidt.sum`, `hsInner_sum_left`
   - `IsHilbertSchmidt.real_smul`, `hsNorm_real_smul`, `hsInner_real_smul_left`
   - **`isHilbertSchmidt_of_tendsto`** — Fatou: a pointwise limit of HS operators with a
     uniform HS bound is HS. Proof by finite partial sums + `summable_of_sum_le`.
   - **`isHilbertSchmidt_of_lyapunov`** — *new mathlib gap*: `v` strictly positive,
     `v y + y v = q` with `q` HS ⟹ `y` HS. Picard iteration
     `z ↦ (2μ)⁻¹(q - w z - z w)`, `w = v - μ`, `μ` the midpoint of a Loewner interval
     containing `v`; the iteration contracts in **both** the operator norm (giving
     convergence to `y`) and the HS norm (giving the uniform bound), then Fatou.
     This is what makes the whole analytic core work without a bundled `L²(H)` space.

2. `HTGeometry/TwistedLyapunovUnit.lean`
   - `saProj_star`, `unit_inv_apply_apply`, `unit_apply_inv_apply`
   - `twisted_unit_apply`, `twisted_unit_apply_of_isSelfAdjoint`
   - **`star_twisted_unit_apply`** — the twisted unit `Λ_{√c}∘P + (1-P)` commutes with `star`
   - **`isSelfAdjoint_twisted_unit_inv`**, **`lyapunov_twisted_unit_inv`** — its inverse at a
     self-adjoint `q` is *the* self-adjoint solution of `√c y + y √c = q`.

3. `HTGeometry/BuresWasserstein/LyapunovFormPositivity.lean` (extended)
   - **`hsNormSq_le_re_hsInner_lyapunovSolution`** — the sharp bound
     `‖p‖²_HS ≤ 2β³ · Re⟨p, y⟩_HS` when `β⁻¹ ≤ v`. Mechanism: with
     `A = v^{-1/2} y v⁻¹`, `B = v⁻¹ y v^{-1/2}`, one has `Re⟨p,y⟩ = ‖A‖² + ‖B‖²`,
     `‖p‖_HS ≤ β^{3/2}(‖A‖+‖B‖)`, and `(x+y)² ≤ 2(x²+y²)`. This elementary route beats the
     paper's integral constant.
   - `norm_ringInverse_le`, `hsNorm_sq`.

4. `HTGeometry/HilbertSchmidtSandwichBounds.lean` (extended)
   - `hsNormSq_sandwich_le` — operator-norm upper bound `‖SYT‖²_HS ≤ ‖S‖²‖T‖²‖Y‖²_HS`.

5. `HTGeometry/BuresWasserstein/WassersteinFieldCoercivity.lean`
   - `eq_of_conj_eq` (conjugation by a unit is injective), `adjoint_eq_self`,
     **`hsInner_conj_eq`** (`⟨bZb, T⟩_HS = ⟨Z, bTb⟩_HS` for self-adjoint `b`)
   - `isHilbertSchmidt_gmInvDerivSolution`, `isHilbertSchmidt_gmInvDeriv`
   - **`re_hsInner_gmInvDeriv_lower`** — one-term Lemma 3.11
   - **`re_hsInner_wassFieldDeriv_lower`** — **Lemma 3.11** for the weighted sum.

### The proof skeleton actually used (for reuse)
With `c = a^{-1/2}X⁻¹a^{-1/2}`, `v = √c`, `q = a^{-1/2}X⁻¹YX⁻¹a^{-1/2}`, `y = Λ_v⁻¹ q`,
`p = a^{1/2} Y a^{1/2}`:
* `c p c = q` (pure algebra, `a^{-1/2}a^{1/2} = 1`);
* `v y + y v = q` and `v² = c` force `p = v⁻¹ y v⁻² + v⁻² y v⁻¹` (cancel `v²` by
  `eq_of_conj_eq`);
* `Re⟨D_a(Y), Y⟩_HS = Re⟨p, y⟩_HS` by the conjugation adjunction;
* `Re⟨p,y⟩ ≥ ‖p‖²_HS/(2β³)` and `‖p‖²_HS ≥ α²‖Y‖²_HS`.

### Next concrete steps (unchanged in substance)
5. Implicit function theorem + homotopy continuation ⇒ Theorems 3.6, 3.8, 3.12, 3.16.
   Lemma 3.11 now supplies the invertibility/coercivity input in Lean.
6. Section 4 (renorming, Banach–Finsler contraction, No-dice), Section 5 (SLLN).
7. Remaining Section 6: Cor 6.4 (Lie–Trotter), Thm 6.8 (power means), Thm 6.12 (Karcher).

## Plan of record — near-identity existence (Theorem 3.5 / `T:Wass-epsilon`)

**Route chosen (mine, not the paper's IFT):** Banach fixed point for the Newton map
`N(X) := X - 2 Φ(X)` on the closed convex set

`S := {X : IsSelfAdjoint X ∧ ‖X - 1‖ ≤ r}`,  `r := 1/32`,

inside the C\*-algebra. Every `X ∈ S` is strictly positive (`X ≥ (1-r)·1`), so `Φ = wassField`
agrees with the geometric-mean form there.

**Why this works and the IFT is not needed.**
1. `DΦ(X)` is known in closed form (`hasStrictFDerivAt_wassField`).
2. On self-adjoint directions,
   `(id - 2DΦ(X))(P) = (P - X⁻¹PX⁻¹) - ∑ wᵢ aᵢ^{1/2}(2yᵢ - qᵢ)aᵢ^{1/2}`,
   `qᵢ = aᵢ^{-1/2}X⁻¹PX⁻¹aᵢ^{-1/2}`, `Λ_{vᵢ}(yᵢ) = qᵢ`, `vᵢ = √(aᵢ^{-1/2}X⁻¹aᵢ^{-1/2})`
   (uses `∑ wᵢ = 1` and `aᵢ^{1/2}qᵢaᵢ^{1/2} = X⁻¹PX⁻¹`).
3. `‖2yᵢ - qᵢ‖ ≤ (‖1 - vᵢ‖/μᵢ)·‖qᵢ‖` — **`norm_two_smul_sub_lyapunov`** (landed).
4. Everything is then elementary norm algebra with the landed perturbation bounds.
5. **Non-self-adjoint directions are genuinely bad** (`id - 2DΦ(1)` acts as `-id` on the
   anti-self-adjoint part), so the mean-value inequality must be run with the derivative
   *within* `S`, namely `(id - 2DΦ(X)) ∘L saProj`, which is a valid `HasFDerivWithinAt`
   derivative because `S` lies in the self-adjoint subspace. **Record this — it is the one
   subtlety that will otherwise make the whole route look impossible.**

**Numeric budget at `r = 1/32`, `δ := maxᵢ‖Aᵢ - 1‖ ≤ 1/128`:**
| quantity | bound |
|---|---|
| `‖X⁻¹‖` | `32/31` |
| `‖1 - X⁻¹‖` | `1/31` |
| `‖P - X⁻¹PX⁻¹‖` | `(1/31)(1 + 32/31)‖P‖ ≈ 0.066‖P‖` |
| `‖aᵢ^{1/2}‖²` | `(33/32)² ≈ 1.063` |
| `‖aᵢ^{-1/2}‖²` | `32/31 ≈ 1.032` |
| `‖qᵢ‖` | `≈ 1.100 ‖P‖` |
| `‖1 - vᵢ‖` | `≈ 0.066` |
| `μᵢ` (lower Loewner bd of `vᵢ`) | `32/33 ≈ 0.970` |
| second term | `≈ 0.079 ‖P‖` |
| **total** | `≈ 0.145 ‖P‖ ≤ ½‖P‖` ✓ |

Invariance: `‖N(1) - 1‖ = 2‖Φ(1)‖ = 2‖1 - ∑wᵢAᵢ^{1/2}‖ ≤ 2δ ≤ 1/64 = r/2`, hence
`‖N(X) - 1‖ ≤ ½‖X - 1‖ + r/2 ≤ r` — `N(S) ⊆ S`. Banach on the complete set `S` gives a unique
fixed point, i.e. a unique zero of `Φ` in `S`. `IsWassersteinPoint.mem_Icc` (landed) then
upgrades uniqueness in `S` to uniqueness in the Loewner interval, giving `ε_ω := 1 + 1/128`
(in fact independent of `ω`).

**Landed bricks for this route**
- `HTGeometry/LyapunovInverseBounds.lean`: `lyapunov_midpoint_identity`,
  **`norm_le_of_lyapunov`** (`2μ‖y‖ ≤ ‖q‖` — the one-line fixed-point argument, no iteration),
  **`norm_two_smul_sub_lyapunov`**, `norm_twisted_unit_inv_le`, `hsNorm_le_of_lyapunov`.
- `HTGeometry/CFCSqrtPerturbation.lean`: `isStrictlyPositive_one_add`,
  `norm_ringInverse_one_add_le`, **`norm_cfcSqrt_sub_one_le`** (`‖√c - 1‖ ≤ ‖c - 1‖`, from
  `c - 1 = (√c-1)(√c+1)` and `‖(√c+1)⁻¹‖ ≤ 1`), `norm_rpow_half_sub_one_le`,
  `norm_ringInverse_sub_one_le`, `norm_rpow_neg_half_sub_one_le`.
- `HTGeometry/OperatorNormLoewner.lean`: `le_smul_one_of_norm_sub_one_le`,
  `smul_one_le_of_norm_sub_one_le`, `norm_ringInverse_le_of_smul_one_le`,
  `norm_le_of_norm_sub_one_le`.

**Still to build for this route**
(a) one-term derivative-difference bound `‖X⁻¹PX⁻¹ - 2 D_a(P)‖ ≤ ‖a^{1/2}‖²(‖1-v‖/μ)‖q‖`;
(b) the numeric assembly at `r = 1/32`;
(c) `HasFDerivWithinAt` for `N` on `S` with derivative `(id - 2DΦ(X)) ∘L saProj`;
(d) `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le` + Banach fixed point
    (`ContractingWith.exists_fixedPoint` on the complete space `S`).

## Session update — Theorem 3.5 and Corollary 3.6 CLOSED

Both are now unconditional Lean, `#print axioms` = {propext, Classical.choice, Quot.sound}.

* **`existsUnique_isWassersteinPoint_near_one`** (Theorem 3.5 / `T:Wass-epsilon`):
  weights `wᵢ ≥ 0` summing to `1`, data `Aᵢ` strictly positive with `‖Aᵢ - 1‖ ≤ 1/128`
  ⟹ `∃! X, ‖X - 1‖ ≤ 1/32 ∧ IsWassersteinPoint s w Av X`.
  The paper's `ε_ω` is here the **explicit, ω-independent** `1 + 1/128`.
* **`existsUnique_isWassersteinPoint_of_ratio`** (Corollary 3.6 / `corol_P`, `corl`):
  `0 < wᵢ`, `∑ wᵢ = 1`, `α·1 ≤ Aᵢ ≤ β·1`, `β ≤ α(1+1/128)²` ⟹ `∃! X, IsWassersteinPoint s w Av X`
  — existence **and global uniqueness** (uniqueness is global, not just inside the ball,
  because `IsWassersteinPoint.mem_Icc` forces every solution into `[α·1, β·1]`, whose rescaling
  lands inside the `1/128` ball).

### Modules added
* `HTGeometry/BuresWasserstein/WassersteinFieldContraction.lean`
  `norm_conjMap_le`, `conjMap_rpow_half_conjMap_rpow_neg_half`,
  **`norm_deriv_term_sub_le`** (one-term Newton difference via the Lyapunov resolvent),
  `norm_cfcSqrt_le_of_le_smul_one`, `norm_rpow_half_sq_le`, `norm_rpow_neg_half_sq_le`,
  **`smul_one_le_cfcSqrt_conjMap`**, `norm_deriv_term_sub_le_delta`,
  `newtonTermConst`, `newtonConst`, `newtonTermConst_nonneg`,
  `norm_deriv_term_sub_le_const`, `norm_sub_conj_ringInverse_le`,
  **`norm_newton_deriv_le`** (the aggregate bound `‖P - 2DΦ(X)P‖ ≤ newtonConst δ ‖P‖`),
  **`newtonConst_thirtysecond`** (`newtonConst (1/32) ≤ 1/2`, by `norm_num`).
* `HTGeometry/BuresWasserstein/WassersteinNearIdentity.lean`
  `exists_twisted_unit`, `wassFieldDeriv_apply`, `newtonMap`, `newtonMap_eq_self_iff`,
  **`norm_newtonMap_sub_le`** (segment mean-value inequality along `t ↦ X + t(Y-X)`),
  `wassField_one`, `norm_wassField_one_le`, `isSelfAdjoint_wassField`,
  **`existsUnique_isWassersteinPoint_near_one`**, `norm_sub_one_le_of_mem_Icc`,
  `norm_smul_sub_one_le_of_Icc`, **`existsUnique_isWassersteinPoint_of_ratio`**.
* `HTGeometry/OperatorNormLoewner.lean` gained `isStrictlyPositive_of_norm_sub_one_le`.

### Technique notes worth keeping
* The anti-self-adjoint-direction obstruction (recorded above) was **avoided entirely** by running
  the mean-value inequality along the *segment* `t ↦ X + t(Y-X)` with
  `norm_image_sub_le_of_norm_deriv_le_segment'` instead of
  `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`: the direction `Y - X` is self-adjoint by
  construction, so only the self-adjoint bound is ever needed. No `saProj`-twisted
  `HasFDerivWithinAt` was required.
* Units for `hasStrictFDerivAt_wassField` are produced totally on `ι` by
  `by_cases i ∈ s` + `choose`; outside `s` take `1`.
* `hasStrictFDerivAt_wassField` has `w` implicit — pass `(w := w)` or elaboration stalls.

### Remaining in §3
Theorem 3.12 (`T:Wass_P`, Σ₂) and Theorem 3.16 (`wass_P`, ℙ) need the homotopy continuation in
`t ↦ Aᵢ^t` from Corollary 3.6's ratio window to `t = 1`, plus (for ℙ) Lemma 3.14 and the spectral
permanence Theorem 3.15. The coercivity input is already in hand
(`re_hsInner_wassFieldDeriv_lower`).

## Session update — Prop 6.1(1) closed; the Hilbert–Schmidt Hilbert space built

### Paper item closed
* **`isWassersteinPoint_of_commute`** (Proposition 6.1(1), consistency with scalars): for a
  pairwise-commuting family of strictly positive `Aᵢ` with `wᵢ > 0`,
  `(∑ wᵢ Aᵢ^{1/2})²` is a Wasserstein point.  Proof by the Riccati uniqueness `gm_unique`
  applied to `x = Aᵢ^{1/2} S⁻¹` with `S = ∑ wᵢ Aᵢ^{1/2}`.  **The normalisation `∑ wᵢ = 1` is not
  needed** and was dropped from the statement.
  Module `HTGeometry/BuresWasserstein/WassersteinCommuting.lean`, also containing the reusable
  `commute_ringInverse_left` and `commute_rpow_left`.

### New infrastructure: the Hilbert space of Hilbert–Schmidt operators (mathlib gap)
Mathlib has no Hilbert–Schmidt class at all (checked: no `HilbertSchmidt`/`Schatten` anywhere).
The corpus had only the predicate `IsHilbertSchmidt` plus `hsInner`/`hsNorm`.  Now built:

* `HTGeometry/HilbertSchmidtNormComparison.lean`
  - **`norm_apply_le_hsNorm`** / **`norm_le_hsNorm`**: `‖T x‖ ≤ ‖T‖_HS ‖x‖`, hence
    `‖T‖ ≤ ‖T‖_HS`.  Basis expansion + the corpus's real Cauchy–Schwarz
    `tsum_mul_le_sqrt_mul_sqrt`.
  - `hsNorm_smul`, `tendsto_apply_of_tendsto`.
  - **`exists_hsNorm_limit`** — completeness of the Hilbert–Schmidt class in *unbundled* form:
    an HS-Cauchy sequence has an HS limit in HS norm.  Mechanism: HS-Cauchy ⟹ operator-norm
    Cauchy ⟹ operator-norm limit `T`; then Fatou (`isHilbertSchmidt_of_tendsto`,
    `hsNormSq_le_of_tendsto`) applied to the shifted sequence `k ↦ Tₙ - T_{k+N}` shows
    `Tₙ - T` is HS with `‖Tₙ - T‖_HS ≤ ε`, so `T = Tₙ - (Tₙ - T)` is HS.
* `HTGeometry/HilbertSchmidtLyapunovInverse.lean` gained **`hsNormSq_le_of_tendsto`**.
* `HTGeometry/HilbertSchmidtSpace.lean`
  - `hsSubmodule` — the HS operators as a `Submodule 𝕜 (E →L[𝕜] E)`.
  - **`HSpace 𝕜 E`** — a type synonym for that submodule, so it does *not* inherit the operator
    norm; `op`, `mk`, `ext`, `op_injective`, the `op_*` simp lemmas.
  - `hsAddGroupNorm` and the **`NormedAddCommGroup`**, **`InnerProductSpace 𝕜`** and
    **`CompleteSpace`** instances.  `HSpace 𝕜 E` is a Hilbert space.

All `#print axioms` = {propext, Classical.choice, Quot.sound}.

### Why this is the gate for Theorem 3.12
Theorem 3.12 (`T:Wass_P`, existence in `Σ₂`) needs `DΦ(X)` to be an *invertible* operator on the
Hilbert space of self-adjoint Hilbert–Schmidt operators — that is exactly what Lemma 3.11's
coercivity gives once the space exists (Lax–Milgram).  Next bricks, in order:
1. the real inner-product structure on the self-adjoint part `SL²` (a closed real subspace of
   `HSpace ℂ E`);
2. the unitisation `SL²_ex ≅ ℝ × SL²` (a `WithLp 2` product Hilbert space) and the map
   `(γ, K) ↦ γ·1 + K`;
3. `Φ` maps `Σ₂` into `SL²_ex`, with `DΦ(X)` a bounded operator there;
4. coercivity + Lax–Milgram ⟹ `DΦ(X)` invertible with `‖DΦ(X)⁻¹‖ ≤ 1/κ`;
5. Newton–Kantorovich step of uniform size + continuation in `t ↦ Aᵢ^t`.

Theorem 3.16 (`ℙ`) additionally needs Lemma 3.14 and the spectral permanence Theorem 3.15
(Drivaliaris–Yannakakis).  **Recorded no-go for the elementary route**: `L(Y) = ∑ AᵢYAᵢ` is
invertible on `B(H)` by an elementary Neumann/spectrum argument only for `m ≤ 2` — factor out
`M_{A₁}R_{A₁}` and use `σ(M_C R_{C*}) ⊆ σ(C)σ(C*) ⊆ (0,∞)`.  For `m ≥ 3` the two perturbations
do not commute and the argument breaks; spectral permanence is genuinely needed.

## Session update — `D₂φ(X)` is an isomorphism of `S²(ℋ)`

The invertibility step used inside Theorems 3.12 and 3.16 is now unconditional Lean.

* `HTGeometry/SelfAdjointHilbertSchmidtSpace.lean`
  - `HSpace.opCLM` (the underlying-operator map as a norm-≤-1 CLM), `HSpace.continuous_op`;
  - `slSubmodule` — the self-adjoint HS operators as a real submodule of `HSpace ℂ E`;
    `isClosed_slSubmodule`;
  - **`SLSpace E`** — the paper's `S²(ℋ)`, a **real Hilbert space** (`NormedAddCommGroup`,
    `InnerProductSpace ℝ`, `CompleteSpace`), with `toHS`, `op`, `isSelfAdjoint`, `isHS`, `ext`
    and the `op_*`/`norm_def`/`inner_def` simp lemmas.
    The real structure comes from `attribute [local instance] InnerProductSpace.complexToReal`
    (it is *not* a global instance in mathlib) — record this, it is easy to trip on.
* `HTGeometry/CoerciveOperatorInvertible.lean`
  - `bilinOfCLM`, `isCoercive_bilinOfCLM`, `continuousLinearMapOfBilin_bilinOfCLM`,
    **`coerciveEquiv`**, `norm_le_of_coercive`, **`bijective_of_coercive`**:
    `κ‖v‖² ≤ ⟪Tv,v⟫` with `κ > 0` ⟹ `T` is a continuous linear equivalence (Lax–Milgram
    through the form `B v w = ⟪Tv,w⟫`, whose associated operator is `T` itself).
* `HTGeometry/HilbertSchmidtNormComparison.lean` gained `hsNorm_sandwich_le`, `hsNorm_sum_le`.
* `HTGeometry/BuresWasserstein/WassersteinDerivOperator.lean`
  - `wassDerivFun` and its `IsHilbertSchmidt` / `IsSelfAdjoint` / additivity / real-homogeneity
    lemmas;
  - `hsNorm_conjMap_le`, **`hsNorm_deriv_term_le`** (`≤ β(β/2)α⁻³ ‖Y‖_HS` per term, from the
    Lyapunov HS bound `hsNorm_le_of_lyapunov` and `smul_one_le_cfcSqrt_conjMap`),
    **`hsNorm_wassDerivFun_le`**;
  - `wassDerivSL`, `wassDerivLinearMap`, **`wassDerivCLM`** — the derivative as a bounded
    operator on `S²(ℋ)`;
  - **`bijective_wassDerivCLM`** — it is bijective, by Lemma 3.11 + Lax–Milgram.

**Elaboration note worth keeping:** `w` must be an *explicit* argument of `wassDerivSL` /
`wassDerivLinearMap` / `wassDerivCLM`.  None of the hypotheses mention `w`, so as a section
variable it is not inferable and elaboration both fails and blows the heartbeat budget.

### What still separates this from Theorem 3.12
The remaining gap is analytic, not algebraic: `hasStrictFDerivAt_wassField` is Fréchet
differentiability **in the C\*-operator norm**, whereas the continuation argument needs
differentiability **in the Hilbert–Schmidt norm** on `Σ₂`, i.e. the little-o estimate measured in
`‖·‖_HS`.  Concretely still to build:
1. `Σ₂` as the unitisation `ℝ × SLSpace E` (a `WithLp 2` product Hilbert space) with
   `(γ, K) ↦ γ·1 + K`;
2. `Φ : Σ₂ → SL²_ex` well defined (i.e. `1 - Aᵢ # X⁻¹` is HS for `Aᵢ, X ∈ Σ₂`);
3. `HasFDerivAt Φ (wassDerivCLM …)` in the HS topology;
4. Newton–Kantorovich with the uniform bound `‖DΦ(X)⁻¹‖ ≤ 1/κ` from `norm_le_of_coercive`,
   giving a uniform continuation step in `t ↦ Aᵢ^t`.

## Session update — the Sylvester route: `#` is Lipschitz, `Φ` is HS-valued on `Σ₂`

**The key structural discovery of this batch.**  The difference of two geometric means with the
same first argument satisfies a *Sylvester equation*: from the Riccati equations
`x a⁻¹ x = b`, `y a⁻¹ y = c` for `x = a # b`, `y = a # c`,

`x a⁻¹ (x - y) + (x - y) a⁻¹ y = b - c`,

and conjugating by `a^{-1/2}` turns the coefficients into *positive* operators:

`X' Z' + Z' Y' = D'`,  `X' = a^{-1/2}(a#b)a^{-1/2}`, `Y' = a^{-1/2}(a#c)a^{-1/2}`,
`Z' = a^{-1/2}(a#b - a#c)a^{-1/2}`, `D' = a^{-1/2}(b-c)a^{-1/2}`.

This gives **Lipschitz estimates and Hilbert–Schmidt stability with no differentiability at
all** — the analytic content of `DΦ` without any Fréchet theory.

### New modules
* `HTGeometry/SylvesterInverseBounds.lean`
  - `sylvester_midpoint_identity` — `(μ+ν) z = d - (x-μ) z - z (y-ν)`;
  - **`norm_le_of_sylvester`**: `μ·1 ≤ x`, `ν·1 ≤ y`, `xz + zy = d` ⟹ `(μ+ν)‖z‖ ≤ ‖d‖`;
  - **`hsNorm_le_of_sylvester`** — the same in the Hilbert–Schmidt norm;
  - **`isHilbertSchmidt_of_sylvester`** — the Sylvester inverse preserves the HS class
    (two-coefficient Picard iteration + Fatou, generalising `isHilbertSchmidt_of_lyapunov`).
* `HTGeometry/BuresWasserstein/GeometricMeanLipschitz.lean`
  - **`gm_sub_sylvester`** — the Sylvester equation for the difference of geometric means;
  - `smul_one_le_conj_rpow_neg_half`;
  - **`norm_gm_sub_le`**, **`norm_gm_sub_le_of_Icc`**: on `α·1 ≤ a ≤ M·1` with
    `γ·1 ≤ a#b, a#c`, `‖a#b - a#c‖ ≤ (M²/(2γα)) ‖b - c‖`;
  - **`norm_gm_sub_le_left`** — Lipschitz in the first argument, by `gm_comm`;
  - **`isHilbertSchmidt_gm_sub`**, **`hsNorm_gm_sub_le_of_Icc`** — the HS versions.
* `HTGeometry/BuresWasserstein/WassersteinFieldHilbertSchmidt.lean`
  - **`gm_ringInverse_self'`**: `a # a⁻¹ = 1` (Riccati uniqueness with `x = 1`) — this is what
    turns the summand `1 - Aᵢ # X⁻¹` into a *difference of two geometric means*
    `Aᵢ # Aᵢ⁻¹ - Aᵢ # X⁻¹`;
  - `smul_one_le_gm` — `√(αδ)·1 ≤ a # b` on a Loewner interval;
  - `isHilbertSchmidt_ringInverse_sub` — `a⁻¹ - X⁻¹ = a⁻¹(X-a)X⁻¹`;
  - **`isHilbertSchmidt_one_sub_gm`**, **`isHilbertSchmidt_wassField`**:
    **`Φ` maps `Σ₂` into the Hilbert–Schmidt class** — item 2 of the Theorem-3.12 roadmap.

All `#print axioms` = {propext, Classical.choice, Quot.sound}.

### Roadmap status for Theorem 3.12
1. `Σ₂` as `ℝ × SLSpace E` — **still open** (the unitisation).
2. `Φ` HS-valued on `Σ₂` — **done** (`isHilbertSchmidt_wassField`).
3. HS-norm derivative — **partly bypassed**: the Sylvester Lipschitz estimates give
   `‖Φ(X) - Φ(Y)‖_HS ≤ L‖X - Y‖_HS` with an explicit `L` and no Fréchet theory.  What is still
   needed is the *second-order* estimate `‖Φ(X) - Φ(Y) - DΦ(X₀)(X-Y)‖ = O(‖X-Y‖·(‖X-X₀‖+‖Y-X₀‖))`,
   which the same Sylvester identity should yield: `DΦ` is the linearisation obtained by setting
   `X' = Y'` in the Sylvester equation, and the error is controlled by `‖X' - Y'‖`.
4. `‖DΦ(X)⁻¹‖ ≤ 1/κ` — **done** (`bijective_wassDerivCLM` + `norm_le_of_coercive`).
5. Newton–Kantorovich + continuation in `t ↦ Aᵢ^t` — open.

**Alternative route now visible**: `Φ` is the gradient of a convex functional, and Lemma 3.11 is
its Hessian bound, so `Φ` is *strongly monotone*: `⟨Φ(X)-Φ(Y), X-Y⟩ ≥ κ‖X-Y‖²`.  Together with
the Sylvester Lipschitz bound this makes `X ↦ X - tΦ(X)` a contraction for `t = κ/L²`, and the
a-priori Loewner localisation `IsWassersteinPoint.mem_Icc` confines the iteration.  The one gap
in that route is invariance of the closed convex set `[α·1, β·1] ∩ Σ₂` (or a projection onto it).

## Session update — Theorem 3.7 and Corollary 3.8 CLOSED (the `Σ₂` theory)

**The `Σ₂` regularity needs no analysis at all.**  Read the Wasserstein equation in square-root
form, `∑ wᵢ (X^{1/2} Aᵢ X^{1/2})^{1/2} = X`, and subtract `X^{1/2}` from every summand:

`X - X^{1/2} = ∑ᵢ wᵢ [(X^{1/2} Aᵢ X^{1/2})^{1/2} - X^{1/2}]`.

* `X^{1/2} Aᵢ X^{1/2} - X = X^{1/2}(Aᵢ - 1)X^{1/2}` is Hilbert–Schmidt whenever `Aᵢ - 1` is;
* the square root is HS-stable, because `√b(√b - √c) + (√b - √c)√c = b - c` is a **Sylvester
  equation** with positive coefficients (`isHilbertSchmidt_of_sylvester`);
* hence `K := X - X^{1/2}` is HS, so `X^{1/2} - 1 = X^{-1/2} K` is HS,
* and `X - 1 = (X^{1/2} - 1)(X^{1/2} + 1)` is HS.

No iteration, no Fatou, no fixed point — pure algebra on top of the Sylvester HS theory.

### Landed (module `HTGeometry/BuresWasserstein/WassersteinSigmaTwo.lean`)
* `cfcSqrt_sub_sylvester`, **`isHilbertSchmidt_cfcSqrt_sub`** (the square root is HS-stable);
* **`isHilbertSchmidt_sub_one_of_isWassersteinPoint`** — every Wasserstein point of a family in
  `1 + SL²` lies in `1 + SL²`;
* **`isHilbertSchmidt_sub_smul_one_of_isWassersteinPoint`** — the same with a general scalar part
  `γ`, via homogeneity `isWassersteinPoint_smul`;
* **`existsUnique_isWassersteinPoint_sigmaTwo_near_one`** — **Theorem 3.7**;
* **`existsUnique_isWassersteinPoint_sigmaTwo_of_ratio`** — **Corollary 3.8** (`corl`).
* `HTGeometry/SylvesterInverseBounds.lean` also gained `two_smul_sub_sylvester_identity`,
  **`norm_two_smul_sub_sylvester`**, **`hsNorm_two_smul_sub_sylvester`**
  (`‖2z - d‖ ≤ (‖x-1‖ + ‖y-1‖)‖z‖` — the comparison of the Sylvester solution with the linear
  one, the derivative-free replacement for a second-order Taylor estimate).

All `#print axioms` = {propext, Classical.choice, Quot.sound}.

### §3 status after this batch
| item | state |
|---|---|
| Lemma 3.3 (`ineq`) | closed |
| Lemma 3.4 (`homo_set`) | closed |
| Theorem 3.5 (`T:Wass-epsilon`) | **closed** |
| Corollary 3.6 (`corol_P`) | **closed** |
| Theorem 3.7 (`Σ₂` near identity) | **closed** |
| Corollary 3.8 (`corl`) | **closed** |
| Lemma 3.10 (`l-1`) | closed |
| Lemma 3.11 (`L:Phi-bdd`) | **closed**, with a better constant |
| `D₂φ(X)` invertible on `S²(ℋ)` | **closed** |
| Theorem 3.12 (`T:Wass_P`) | open — **only the continuation is missing** |
| Lemma 3.14, Theorem 3.15 | open — spectral permanence |
| Theorem 3.16 (`wass_P`) | open — the continuation |

**Key reduction now available:** `isHilbertSchmidt_sub_smul_one_of_isWassersteinPoint` says every
Wasserstein point of a `Σ₂` family is automatically in `Σ₂`.  So **Theorem 3.12 follows from
Theorem 3.16** with no extra work; the *single* remaining crux in §3 is existence in `ℙ` for an
arbitrary ratio `β/α`, i.e. the homotopy continuation.

### The continuation, derivative-free plan
1. Lipschitz bound for `X ↦ DΦ(X)` in the `S²(ℋ)` operator norm — obtainable from the same
   Sylvester identity (the difference of two Lyapunov solves is itself a Sylvester solve).
2. Lipschitz bound for `t ↦ Aᵢ^t` in operator norm: `‖a^t - a^s‖ ≤ |t-s| · sup_{[α,β]}|λ^ξ log λ|`
   through the continuous functional calculus.
3. Newton–Kantorovich at a solution `X_{t₀}`, with the uniform inverse bound
   `‖DΦ(X)⁻¹‖ ≤ 1/κ` from `norm_le_of_coercive` — giving a step size independent of `t`.
4. Finitely many steps from `t₀` to `1` (the paper's own remark).

## Session update — square-root Lipschitz + the affine homotopy

* `HTGeometry/CFCSqrtLipschitz.lean`
  - `cfcSqrt_sub_sylvester'`, `smul_one_le_cfcSqrt`,
    **`norm_cfcSqrt_sub_le_of_Icc`** (`2√α ‖√b - √c‖ ≤ ‖b - c‖` on `α·1 ≤ b, c`) and
    **`hsNorm_cfcSqrt_sub_le_of_Icc`**.  General C\*-algebra version of the square-root
    stability used in the `Σ₂` theorem.
* `HTGeometry/BuresWasserstein/WassersteinHomotopy.lean`
  - **`homotopyFamily Av t i = (1-t)·1 + t·Aᵢ`** — the *affine* homotopy replacing the paper's
    `t ↦ Aᵢ^t`.  **Why this is the right choice:** it is exactly Lipschitz in `t`
    (`homotopyFamily_sub`: `A(σ) - A(τ) = (σ-τ)·(A - 1)`), it stays in the *fixed* interval
    `[min(1,α)·1, max(1,β)·1]` for all `t ∈ [0,1]`, so every constant along the continuation is
    uniform in `t`, and no `rpow`-in-the-exponent Lipschitz theory is needed at all.
    At `t = 0` the family is constantly `1`, whose Wasserstein point is `1`.
  - `homotopyFamily_zero/_one/_sub`, `isSelfAdjoint_homotopyFamily`,
    `smul_one_le_homotopyFamily`, `homotopyFamily_le_smul_one`,
    `isStrictlyPositive_homotopyFamily`;
  - **`norm_wassField_homotopy_sub_le`** — `‖Φ_σ(X) - Φ_τ(X)‖ ≤ C |σ - τ|`, from
    `norm_gm_sub_le_left`.  This is step (2) of the continuation plan, done.

### Continuation: what is left
* (1) `‖DΦ(X) - DΦ(Y)‖_{S²→S²} ≤ C‖X - Y‖` — reachable by the same Sylvester trick: with
  `vX yX + yX vX = qX` and `vY yY + yY vY = qY`, the difference `D = yX - yY` satisfies the
  Lyapunov equation `vX D + D vX = (qX - qY) - (δv·yY + yY·δv)`, `δv = vX - vY`, and
  `‖δv‖ ≤ ‖cX - cY‖/(2√·)` by `norm_cfcSqrt_sub_le_of_Icc`.
* (3) Newton–Kantorovich at `X_{t₀}` using `‖DΦ(X)⁻¹‖ ≤ 1/κ` (`norm_le_of_coercive`), giving a
  step size independent of `t`.
* (4) Finitely many steps from `0` to `1`.

## Session update — the derivative of the Wasserstein field is Lipschitz

Step (1) of the continuation plan is done, still with no differentiability theory.

* `HTGeometry/SylvesterInverseBounds.lean` gained the **perturbation** layer:
  - `sylvester_sub_sylvester` — the difference of two Sylvester solutions is itself a Sylvester
    solution for the first pair of coefficients:
    `x₁(z₁-z₂) + (z₁-z₂)y₁ = (d₁-d₂) - (x₁-x₂)z₂ - z₂(y₁-y₂)`;
  - **`norm_sylvester_sub_le`**, **`hsNorm_sylvester_sub_le`**:
    `(μ+ν)‖z₁-z₂‖ ≤ ‖d₁-d₂‖ + (‖x₁-x₂‖+‖y₁-y₂‖)‖z₂‖`.
    This one lemma is the engine for every Lipschitz statement about the derivative.
* `HTGeometry/BuresWasserstein/WassersteinDerivLipschitz.lean`
  - **`cfcSqrt_conjMap_rpow_neg_half`** — the identity that ties everything together:
    `√(a^{-1/2} b a^{-1/2}) = a^{-1/2}(a # b)a^{-1/2}`.  So the *Lyapunov coefficient of the
    derivative is exactly the conjugated geometric mean*, and the geometric-mean Lipschitz
    theorem transfers to it verbatim (`norm_cfcSqrt_conjMap_sub_le`).
  - `norm_ringInverse_sub_le_of_Icc`, `hsNorm_conj_ringInverse_sub_le`;
  - `derivLipConst α β = β(β/2)(2α⁻⁴ + β²α⁻⁶/(2√(αβ⁻¹)))`;
  - **`hsNorm_deriv_term_diff_le`** — one term;
  - **`hsNorm_wassDerivFun_diff_le`** — `‖DΦ(X)P - DΦ(Y)P‖_HS ≤ C ‖X-Y‖ ‖P‖_HS`.

All `#print axioms` = {propext, Classical.choice, Quot.sound}.

**Elaboration note worth keeping:** in a proof with many large `set` definitions, `linarith`,
`rw` and `field_simp` blow the heartbeat budget because `set` leaves the big bodies reachable.
Replacing `set x := big with h` by `obtain ⟨x, h⟩ : ∃ z, z = big := ⟨_, rfl⟩` makes the local
constant genuinely opaque and the same proof elaborates in seconds.

### Continuation: what is left
* (3) Newton–Kantorovich at a solution `X_{t₀}`, using
  `‖DΦ(X)⁻¹‖ ≤ 1/κ` (`norm_le_of_coercive` + `bijective_wassDerivCLM`),
  `‖DΦ(X) - DΦ(Y)‖ ≤ C‖X-Y‖` (**done**), and
  `‖Φ_σ(X) - Φ_τ(X)‖ ≤ C|σ-τ|` (**done**, `norm_wassField_homotopy_sub_le`).
* (4) Finitely many steps from `0` to `1` along the affine homotopy.

## Session update — the second-order estimate (derivative-free Taylor)

`HTGeometry/BuresWasserstein/WassersteinSecondOrder.lean`

**The observation that makes it work.**  The increment of `X ↦ a # X⁻¹` and its linearisation at
`Y` are *both* Sylvester solutions with the **same first coefficient**
`Xc = a^{-1/2}(a # Y⁻¹)a^{-1/2} = √(a^{-1/2}Y⁻¹a^{-1/2})`:

| | first coeff | second coeff | right-hand side |
|---|---|---|---|
| increment `W' = a^{-1/2}(a#Y⁻¹ - a#X⁻¹)a^{-1/2}` | `Xc` | `Yc = a^{-1/2}(a#X⁻¹)a^{-1/2}` | `a^{-1/2}(Y⁻¹-X⁻¹)a^{-1/2}` |
| linearisation `V = DΦ(Y)(X-Y)`-term | `Xc` | `Xc` | `a^{-1/2}Y⁻¹(X-Y)Y⁻¹a^{-1/2}` |

and the coefficient gap is *itself* the increment: **`Xc - Yc = W'`**.  So the Sylvester
perturbation bound gives

`2β⁻¹‖V - W'‖_HS ≤ ‖q - D'‖_HS + ‖W'‖ · ‖W'‖_HS`,

both terms manifestly quadratic in `X - Y`.  No Taylor expansion, no differentiability.

* `secondOrderConst α β = β(β/2)(α⁻⁴ + (β²/4)α⁻⁶)`;
* **`hsNorm_increment_sub_deriv_le`** — one term;
* **`hsNorm_wassField_increment_sub_deriv_le`** —
  `‖(Φ(X) - Φ(Y)) - DΦ(Y)(X-Y)‖_HS ≤ C ‖X-Y‖ ‖X-Y‖_HS`.
* `GeometricMeanLipschitz` gained `hsNorm_gm_sub_le_left`, `isHilbertSchmidt_gm_sub_left`;
  `WassersteinHomotopy` gained **`hsNorm_wassField_homotopy_sub_le`**.

All `#print axioms` = {propext, Classical.choice, Quot.sound}.

### The continuation now has every quantitative input
| input | lemma | state |
|---|---|---|
| `‖DΦ(X)⁻¹‖ ≤ 1/κ` | `bijective_wassDerivCLM` + `norm_le_of_coercive` | done |
| `‖DΦ(X) - DΦ(Y)‖ ≤ C‖X-Y‖` | `hsNorm_wassDerivFun_diff_le` | done |
| `‖(Φ(X)-Φ(Y)) - DΦ(Y)(X-Y)‖ ≤ C‖X-Y‖²` | `hsNorm_wassField_increment_sub_deriv_le` | done |
| `‖Φ_σ(X) - Φ_τ(X)‖_HS ≤ C|σ-τ|` | `hsNorm_wassField_homotopy_sub_le` | done |
| `Φ` is HS-valued on `Σ₂` | `isHilbertSchmidt_wassField` | done |
| `SLSpace E` complete | `HSpace`/`SLSpace` instances | done |

What remains is purely the assembly: a Banach fixed point for
`H(K) = K - L⁻¹(Φ_t(X₀ + K))` on a closed ball of `SLSpace E` (`L = DΦ_t(X₀)`, inverse from
`coerciveEquiv`), giving a step of size independent of `t`, and then a finite induction along the
affine homotopy from `t = 0` (where `X = 1` solves it) to `t = 1`.

## Session update — strong monotonicity and the explicit gradient step

Two more bricks, both derivative-free, both feeding the continuation.

* `HTGeometry/HilbertSchmidtNormComparison.lean` gained the inner-product algebra needed for a
  contraction computation: `hsInner_neg_left/right`, `hsInner_sub_left/right`, and
  **`hsNormSq_sub`** (`‖S-T‖²_HS = ‖S‖² - 2 Re⟨S,T⟩ + ‖T‖²`);
  `HilbertSchmidtLyapunovInverse.lean` gained `hsInner_real_smul_right`.
* `HTGeometry/BuresWasserstein/WassersteinStrongMonotone.lean`
  - `isHilbertSchmidt_wassField_sub` — the *increment* of `Φ` is HS whenever `X - Y` is
    (needs no `Σ₂` hypothesis on `X`, `Y` separately);
  - **`re_hsInner_wassField_sub_lower`** — **local strong monotonicity**:
    `⟨Φ(X) - Φ(Y), X - Y⟩_HS ≥ (κ - C‖X-Y‖)‖X-Y‖²_HS`, with `κ = α²/(2β³)` from Lemma 3.11 and
    `C = secondOrderConst α β`.  Coercivity of the derivative plus the second-order estimate.
* `HTGeometry/BuresWasserstein/WassersteinGradientStep.lean`
  - `wassLipConst α β = β²α⁻³/(2√(αβ⁻¹))` and **`hsNorm_wassField_sub_le`**
    (`Φ` is Lipschitz on the Loewner interval);
  - **`hsNormSq_gradientStep_sub_le`** —
    `‖(X - tΦ(X)) - (Y - tΦ(Y))‖²_HS ≤ (1 - 2tκ' + t²L²)‖X-Y‖²_HS`.

**Design decision recorded:** the continuation uses the *explicit* step `X ↦ X - tΦ(X)`, not a
Newton step `X ↦ X - DΦ(X₀)⁻¹Φ(X)`.  The explicit step never needs `DΦ⁻¹`, so it avoids
packaging `Φ(X)` as an element of the bundled `SLSpace E` at every iterate (the map
`K ↦ Φ(X₀+K)` is only defined where the Loewner bounds hold, so it is not a total map of
`SLSpace E` and cannot be fed to `ContractingWith` directly).  With the explicit step the whole
iteration stays in the C\*-algebra and completeness is supplied by `exists_hsNorm_limit`.

All `#print axioms` = {propext, Classical.choice, Quot.sound}.

### Remaining for Theorem 3.16 (and hence 3.12)
1. Choose `t = κ'/L²` and a ball radius `r ≤ κ/(2C)` so that `1 - 2tκ' + t²L² ≤ 1 - κ'²/(2L²) < 1`
   on the ball, and check the ball is Loewner-admissible.
2. Banach by hand: iterate, show HS-Cauchy, take the limit with `exists_hsNorm_limit`, and use
   Lipschitz continuity of `Φ` to pass to the limit.
3. Induct along the affine homotopy: `t = 0` has the solution `X = 1`; each step moves the
   parameter by a fixed amount determined by `hsNorm_wassField_homotopy_sub_le`.

## Session update — Banach fixed point in the Hilbert–Schmidt metric

`HTGeometry/HilbertSchmidtBanach.lean`

**`exists_fixedPoint_hs`** — if `G` maps the Hilbert–Schmidt ball `{X : ‖X - X₀‖_HS ≤ r}` into the
Hilbert–Schmidt class, contracts there with factor `θ < 1`, and `‖G X₀ - X₀‖_HS ≤ (1-θ)r`, then
`G` has a fixed point in that ball.

**Why it is proved by hand rather than through `ContractingWith`.**  The natural carrier would be
the closed ball of the bundled `SLSpace E`, but the map `K ↦ Φ(X₀ + K)` is only defined where the
Loewner bounds hold, so it is *not* a total map of `SLSpace E` and cannot be handed to
`ContractingWith` without dependent packaging at every iterate.  Stating the fixed point directly
in `E →L[ℂ] E`, with completeness supplied by `exists_hsNorm_limit`, keeps everything first-order.
The geometric series is carried as the sharp invariant
`‖Xₙ - X₀‖_HS ≤ (1-θⁿ)/(1-θ)·d` together with `‖Xₙ₊₁ - Xₙ‖_HS ≤ θⁿ d`, and the Cauchy estimate
`‖X_m - X_n‖_HS ≤ (θⁿ - θᵐ)/(1-θ)·d` is proved by `Nat.le_induction`.

`HTGeometry/OperatorNormLoewner.lean` also gained the Loewner perturbation pair
**`smul_one_le_of_norm_sub_le`** / **`le_smul_one_of_norm_sub_le`**
(`‖X - Y‖ ≤ r`, `m·1 ≤ Y ≤ M·1` ⟹ `(m-r)·1 ≤ X ≤ (M+r)·1`), which is what will keep the Newton
ball inside the Loewner interval.

All `#print axioms` = {propext, Classical.choice, Quot.sound}.

### Every ingredient for Theorem 3.16 is now in the corpus
| ingredient | lemma |
|---|---|
| explicit step contracts | `hsNormSq_gradientStep_sub_le` |
| local strong monotonicity | `re_hsInner_wassField_sub_lower` |
| `Φ` Lipschitz | `hsNorm_wassField_sub_le` |
| `Φ` HS-valued, increment HS | `isHilbertSchmidt_wassField`, `isHilbertSchmidt_wassField_sub` |
| Banach in HS metric | `exists_fixedPoint_hs` |
| Loewner ball control | `smul_one_le_of_norm_sub_le`, `le_smul_one_of_norm_sub_le` |
| homotopy, Lipschitz in `t` | `homotopyFamily`, `hsNorm_wassField_homotopy_sub_le` |
| `t = 0` solution | `gm_ringInverse_self'` gives `Φ_0(1) = 0` |
| `Σ₂` regularity | `isHilbertSchmidt_sub_smul_one_of_isWassersteinPoint` |

The remaining work is the numerical choice of `t`, `r` and the step size, and the induction along
`[0,1]`.

### Banach lemma generalised with an invariant predicate
`exists_fixedPoint_hs` now carries a predicate `P` preserved by `G` on the ball and closed under
Hilbert–Schmidt limits, and returns `P X` for the fixed point.  This is needed because every
estimate in the Wasserstein theory requires the arguments to be **self-adjoint**, and the naked
Hilbert–Schmidt ball does not.  `isSelfAdjoint_of_hs_limit` supplies the closedness
(`hsNorm → 0` ⟹ `‖·‖ → 0` by `norm_le_hsNorm`, then continuity of `star`).

## Batch: Theorem 3.16 continuation and Theorem 3.12 (existence + uniqueness) — CLOSED

`HTGeometry/BuresWasserstein/WassersteinContinuation.lean` (wired, built, axioms clean)
- `abs_min_one_sub_min_one_le`, `wassField_eq_zero_of_isWassersteinPoint`, `homotopy_Icc`
- `exists_isWassersteinPoint_homotopy_succ` — one continuation step along the affine homotopy
- `hsNorm_wassField_homotopy_defect`, `isWassersteinPoint_one`
- `exists_isWassersteinPoint_homotopy_iter` — the induction on the number of steps
- `exists_isWassersteinPoint_of_Icc` — **existence** of a Wasserstein point for any family in
  `1 + S²` with `0 < a₀ ≤ Aᵢ ≤ b₀`, `a₀ ≤ 1 ≤ b₀`, with the solution again in `1 + S²`.

`HTGeometry/BuresWasserstein/WassersteinUniqueness.lean` (wired, built, axioms clean)
- `segPoint`, `segPoint_zero`, `segPoint_last`, `segPoint_succ_sub`,
  `smul_one_le_segPoint`, `segPoint_le_smul_one` — the affine segment from `Y` to `X` and the
  fact that the Loewner interval is convex.
- `re_hsInner_wassField_sub_lower'` — local strong monotonicity with the twisted Lyapunov unit
  produced internally (`choose` over a `by_cases` on membership; the unit is only constrained
  on `s`).
- `re_hsInner_wassField_sub_lower_global` — **global strong monotonicity**:
  `⟨Φ(X) − Φ(Y), X − Y⟩ ≥ (κ − C‖X−Y‖/N)‖X−Y‖²_HS` for every `N ≥ 1`, `κ = α²/(2β³)`.
- `eq_of_isWassersteinPoint` — uniqueness whenever `X − Y` is Hilbert–Schmidt.
- `existsUnique_isWassersteinPoint_of_sigmaTwo` — **Theorem 3.12**: unique solution in the whole
  positive cone; uniqueness holds against *arbitrary* competitors because the regularity theorem
  forces every solution into `1 + S²`.
- `exists_isWassersteinPoint_sigmaTwo` — the same statement with the `1 + S²` regularity attached.

### Technique that made the telescoping work
Local strong monotonicity has a defect linear in `‖X − Y‖`, useless for far-apart points. Split
`[Y, X]` into `N` equal pieces `P_k = Y + (k/N)(X − Y)`; each `P_k` lies in the same Loewner
interval (convexity), each increment `P_{k+1} − P_k = (1/N)(X − Y)` is Hilbert–Schmidt and
self-adjoint, and `Φ(X) − Φ(Y)` telescopes over `Finset.range N` (`Finset.sum_range_sub`).
Pairing the `k`-th increment with `X − Y = N·(P_{k+1} − P_k)` turns the local estimate into
`(κ − C‖X−Y‖/N)‖X−Y‖²_HS / N`; summing `N` of them restores the full square. No differentiability,
no integral along the segment, no mean value theorem.

### Elaboration trap recorded
`obtain ⟨x, hx, hP⟩ : ∃ x, x = <big real expression> ∧ P x := ⟨_, rfl, by …⟩` is fine when the
expression is an operator but **times out** when the expression is a real number built from
`hsNorm`/`tsum` — the anonymous constructor forces `whnf` on the sum. Fix: prove the properties
first with the expression written out, then `set x := <expression> with hx` (which rewrites the
hypotheses already in context and never re-checks defeq).

## Batch: Lemma 3.14 (Banach transpose) and Section 4 Lemmas 4.6, 4.7

`HTGeometry/BanachTransposeIsomorphism.lean` (wired, built, axioms clean) — general mathlib gap
- `transposeCLM` — the Banach transpose `Lᵀ : F* → E*` as a bundled continuous linear map,
  with `transposeCLM_apply`, `transposeCLM_id`, `transposeCLM_comp`,
  `transposeCLM_transposeCLM_inclusion` (the double transpose extends `L` along the biduals).
- `bijective_transposeCLM_of_inverse`, `bijective_transposeCLM_of_bijective` — the easy half.
- `exists_dual_eq_zero_on` — Hahn–Banach: a closed proper subspace carries a nonzero annihilating
  functional (via the quotient seminorm and `exists_dual_vector''`).
- `bijective_of_bijective_transposeCLM` — the converse.
- `bijective_transposeCLM_iff` — **Lemma 3.14**: `L` is an isomorphism iff `Lᵀ` is.
  Under the trace duality `(S¹)* ≅ S` this is the paper's statement.

Route note: the converse does **not** need the bidual.  A norming functional `f` for `x`
(`‖f‖ ≤ 1`, `f x = ‖x‖`) is `Lᵀ g` for `g = (Lᵀ)⁻¹ f`, so
`‖x‖ = |f x| = |g (L x)| ≤ ‖g‖ ‖L x‖ ≤ ‖(Lᵀ)⁻¹‖ ‖L x‖` — one dual level only, no
`σ(exp a) = exp σ(a)`, no holomorphic functional calculus.

`HTGeometry/BuresWasserstein/WassersteinFlowInvariance.lean` (wired, built, axioms clean)
- `add_smul_inv_sqrt_lower`, `add_smul_inv_sqrt_upper` — the two scalar inequalities behind
  Lemma 4.7, via the factorisations `(√t−√α)(t+√α√t−λ)/√t` and `(√β−√t)(√t√β+t−λ)/√t`.
- `smul_one_le_add_smul_rpow_neg_half`, `add_smul_rpow_neg_half_le_smul_one` — their operator
  forms, by `cfc_mono` with `cfc_inv Real.sqrt` and `ringInverse_rpow_half`.
- `neg_wassField_Icc` — `√α X^{-1/2} − 1 ≤ −Φ(X) ≤ √β X^{-1/2} − 1`.
- `sub_smul_wassField_mem_Icc` — **Lemma 4.7**: for `0 < λ ≤ 2α` the explicit step
  `X + λ(−Φ(X))` stays in `[α·1, β·1]`; this is the subtangential condition that the paper
  feeds to the Nagumo-type invariance theorem of [GQ].
- `norm_ringInverse_sub_le_of_smul_one_le`, `rpow_neg_half_le_smul_one`,
  `exists_bound_lipschitz_wassField` — **Lemma 4.6**: `Φ` is bounded and globally Lipschitz on
  `[α·1, β·1]` in the operator norm, with the explicit constants
  `B = 1 + √β √(α⁻¹)` and `L = βα⁻¹(α⁻¹)²/(2√(αβ⁻¹)β⁻¹)`.

### Recorded obstruction: Theorem 3.15 and Theorem 3.16 in all of `ℙ`
The paper's Theorem 3.15 (`L(Y) = AYA + BYB + CYC` is an isomorphism on `S(ℋ)`) rests on the
spectral-permanence corollary of Drivaliaris–Yannakakis, `σ(L|_{S¹}) ⊆ σ(L|_{S²})`.  Injectivity
of `L` on `S¹` is elementary (`⟨L Y, Y⟩₂ = ∑ Tr((Aᵢ^{1/2} Y Aᵢ^{1/2})²) > 0` for `Y ≠ 0`, and
`S¹ ⊆ S²`), and Lemma 3.14 is now available, so the whole statement reduces to
`L⁻¹(S¹) ⊆ S¹`.  Two routes were examined and rejected:
* the Lyapunov splitting `L = M − R`, `M(Y) = ½(TY+YT)`, `T = ∑Aᵢ²`, `R(Y) = ½∑[Aᵢ,[Aᵢ,Y]]`:
  `M⁻¹` does preserve `S¹`, but `‖M⁻¹R‖ < 1` only under a ratio condition;
* `L⁻¹` positivity: false — for `A = diag(1,ε)`, `B = diag(ε,1)` on `ℂ²`, `L⁻¹` scales the
  off-diagonal by `1/(2ε)` and destroys positivity.
The renorming Lemma 4.3 is likewise blocked: `‖e^{tA}‖ ≤ M e^{t(Reσ(A)+ε)}` needs
`σ(e^A) ⊆ exp σ(A)`, and mathlib has only `spectrum.exp_mem_exp` (the other inclusion); the full
spectral mapping theorem needs the Riesz–Dunford holomorphic functional calculus, which mathlib
does not have.

## Batch: Section 4 Lemmas 4.9–4.12 and Proposition 4.14

`HTGeometry/BuresWasserstein/WassersteinResolventExpansion.lean`
- `gm_sub_riccati` — the unconjugated Riccati form of a difference of geometric means.
- `wassG Y X := X(1 − X # Y⁻¹) + (1 − X # Y⁻¹)X` — the normalized resolvent increment.
- **`wassG_sub_eq`** — the *exact* identity
  `G(Y,X) − (Y−X) = −(Y−X)Y⁻¹(Y−X) + X N X⁻¹ N X`, `N = 1 − X#Y⁻¹`.
  Both summands are visibly quadratic; the paper's second differential and Taylor formula with
  integral remainder are not needed at all.
- `gmFieldLipConst`, `norm_one_sub_gm_le`, `wassGConst`, **`norm_wassG_sub_le`** (Lemma 4.10).
- **`norm_one_sub_gm_sub_lyapunov_le`** (Lemma 4.9): `1 − X#Y⁻¹` agrees with the solution `W`
  of the Lyapunov equation `XW + WX = Y − X` up to `O(‖Y−X‖²)`; obtained by dividing the exact
  remainder by the Lyapunov operator (`norm_le_of_lyapunov`).

`HTGeometry/BuresWasserstein/WassersteinResolventLipschitz.lean`
- `mul5_le`, `sandwich_sub_telescope`, `quintuple_sub_telescope`, `norm_gm_sub_gm_le`,
  `wassRLipConst`, **`norm_wassG_remainder_sub_le`**:
  `‖R(Y₁,X) − R(Y₂,X)‖ ≤ C(‖Y₁−X‖+‖Y₂−X‖)‖Y₁−Y₂‖`.

`HTGeometry/BuresWasserstein/WassersteinResolventStep.lean`
- `isSelfAdjoint_wassG`, **`exists_resolvent_step`** (Lemma 4.11): a Banach fixed point for
  `T(Y) = X − hΦ(Y) − R(Y,X)` on the ball of radius `2(B_Φ+1)h`, giving a solution of
  `hΦ(Y) + G(Y,X) = 0` with `‖Y − (X − hΦ(X))‖ ≤ C_loc h²`.

`HTGeometry/BuresWasserstein/WassersteinTrapping.lean`
- `euler_lower_scalar`, `euler_upper_scalar` — the inward scalar estimates, proved after the
  substitution `x = u²` (which removes every `Real.sqrt` of a composite and lets `field_simp;
  ring` close the factorisation).
- `smul_one_le_euler_lower`, `euler_upper_le_smul_one` — their `cfc_mono` forms.
- **`exists_trapping_resolvent`** (Lemma 4.12): the resolvent maps `[(α/2)·1, (2β)·1]` into
  itself for all small `h`; the Euler margin is `h(√α/√(α/2) − 1)` on the left and
  `h(1 − √β/√(2β))` on the right, and it absorbs the `O(h²)` resolvent error.

`HTGeometry/BuresWasserstein/WassersteinResolventConsistency.lean`
- `wassGConst_pos`, **`exists_resolvent_consistency`** (Proposition 4.14): *any* solution of the
  resolvent equation on the near branch `C‖Y−X‖ ≤ ½` satisfies `‖Y−X‖ ≤ 2Bh` and
  `‖Y − (X − hΦ(X))‖ ≤ (2BL + 4CB²)h²`.  The paper's "since `Y_h → X`" step is replaced by the
  explicit branch condition, which is what the quadratic inequality actually gives.

All five modules wired into `GaloisForLFunctions.HTGeometry`, `lake build` green,
`#print axioms` = {propext, Classical.choice, Quot.sound} on every capstone.

### Route for Proposition 4.15 and Theorem 4.16
The paper runs these in the Banach–Finsler metric `d_ε` of Lemma 4.3, which is blocked (see the
recorded obstruction).  They are, however, available **in the Hilbert–Schmidt metric**, where
`DΦ` is genuinely self-adjoint and positive definite and no renorming is needed: the contraction
estimate `d(X*, u(t)) ≤ e^{−κt} d(X*, X)` is replaced by the discrete inequality
`‖X_{k+1} − X*‖²_HS ≤ (1 − 2λκ + λ²L²)‖X_k − X*‖²_HS`, which the corpus already owns
(`hsNormSq_gradientStep_sub_le`) together with global strong monotonicity
(`re_hsInner_wassField_sub_lower_global`).  What remains is the Robbins–Siegmund style real
recursion `d_{k+1} ≤ (1 − κλ_{k+1})d_k + Cλ_{k+1}²` with `∑λ = ∞`, `∑λ² < ∞` ⟹ `d_k → 0`.

## Batch: Corollary 4.13, Proposition 4.15, Remark 6.6 kernel, and Robbins–Monro

`HTGeometry/RobbinsMonroRecursion.lean` (wired, built, axioms clean) — general mathlib gap
- `prod_one_sub_le_exp_neg`, `robbins_le`, **`tendsto_zero_of_robbins`**: a nonnegative sequence
  with `d(n+1) ≤ (1 − κλₙ)dₙ + Cλₙ²`, `0 ≤ κλₙ ≤ 1`, `∑λ = ∞`, `∑λ² < ∞` tends to zero.
  Proof: the explicit solution bound `dₙ ≤ (∏_{[N,n)}(1−κλ))d_N + C∑_{[N,n)}λ²`, the exponential
  majorant `1 − x ≤ e^{−x}`, and a two-parameter ε-argument.

`HTGeometry/BuresWasserstein/WassersteinGradientDescent.lean` (wired, built, axioms clean)
- **`hsNormSq_gradientStep_sub_le_global`** — the explicit gradient step contracts with **no**
  second-order defect: `‖(X−tΦX)−(Y−tΦY)‖²_HS ≤ (1 − 2tκ + t²L²)‖X−Y‖²_HS`.  The defect
  `C‖X−Y‖/N` of the local estimate is removed by `le_of_forall_pos_le_add` over `N`.
- `hsNorm_gradientStep_sub_le_global` — square-root form, using the exact identity
  `(1 − tκ + t²L²/2)² = (1 − 2tκ + t²L²) + (tκ − t²L²/2)²`.
- **`tendsto_hsNorm_sub_isWassersteinPoint`** — **Proposition 4.15 in the Hilbert–Schmidt
  metric**: a perturbed iteration `X_{k+1} = X_k − λ_kΦ(X_k) + r_k`, `‖r_k‖_HS ≤ Cλ_k²`, with
  `λ_kL² ≤ κ`, `κλ_k ≤ 1`, `∑λ = ∞`, `∑λ² < ∞`, converges to the Wasserstein point.
  This replaces the paper's Banach–Finsler metric `d_ε` (blocked on Lemma 4.3) by the metric in
  which the whole treatment lives, and is unconditional.

`HTGeometry/BuresWasserstein/WassersteinTrapping.lean` (extended)
- **`mem_Icc_of_euler_close`** — **Corollary 4.13 (freedom of resolvents)**: *any* map agreeing
  with the explicit Euler step to second order leaves `[(α/2)·1, (2β)·1]` invariant for small
  steps, however that map is produced.

`HTGeometry/BuresWasserstein/NearOrderNorm.lean` (wired, built, axioms clean)
- **`NearLE.norm_le`** — the provable kernel of Remark 6.6: `p ⪯ q ⟹ ‖p‖ ≤ ‖q‖`.  Via the
  Riccati equation `XpX = q` for `X = p⁻¹#q ≥ 1`, the C*-identity `‖q‖ = ‖√p·X‖²`, and
  `‖√p‖ ≤ ‖√p·X‖‖X⁻¹‖ ≤ ‖√p·X‖`.  (The near-order chain `(E:chain)` that Remark 6.6 feeds this
  into is cited from [HK25] and is not proved in the paper.)

## Batch: Theorem 4.16 (No-dice) — CLOSED in the Hilbert–Schmidt metric

`HTGeometry/BuresWasserstein/WassersteinBlockField.lean` (wired, built, axioms clean)
- `hsNorm_neg'`, `wassPsi m w Av i X := (m wᵢ)(1 − Aᵢ # X⁻¹)`, `sum_wassPsi` (`∑ᵢ Ψᵢ = m Φ`),
  `hsNorm_gm_sub_gm_le`, `isHilbertSchmidt_wassPsi_sub`, `hsNorm_wassPsi_sub_le`.
  Since `Ψᵢ(Aᵢ) = 0`, every `Ψᵢ(X)` is itself Hilbert–Schmidt on `1 + S²`, with
  `‖Ψᵢ(X)‖_HS ≤ Wm·L·(‖X − Ω‖_HS + Sstar)`.

`HTGeometry/BuresWasserstein/WassersteinGradientDescent.lean` (extended)
- **`tendsto_hsNorm_sub_isWassersteinPoint'`** — Proposition 4.15 with a *state-dependent* error
  `Cr(1 + dₙ)λₙ²`; the extra `Cr dₙ λ²` is absorbed by the contraction once `Cr λ ≤ κ/8`.

`HTGeometry/BuresWasserstein/WassersteinNoDice.lean` (wired, built, axioms clean)
- `idx_mem_of_bijOn`, `one_div_sub_one_div_le`.
- **`tendsto_noDice`** — **Theorem 4.16**: for a cyclic resolvent iteration
  `‖s_{n+1} − (s_n − (1/(n+1))Ψ_{i_n}(s_n))‖_HS ≤ Cr/(n+1)²` whose index map visits every
  member of the family exactly once per block of `m` steps, `‖s_n − Ω‖_HS → 0`.
- **`bijOn_cyclic`** — the paper's concrete scheme `i_n ≡ n+1 (mod m)` satisfies that block
  hypothesis (injectivity from `Nat.ModEq.add_left_cancel'`, surjectivity by cardinality).

### How the block analysis goes
`x_k := s_{N₀+km}`.  Over one block the increments telescope, and
`G_k := ∑_j [h₀ Ψ_j(x_k) − h_j Ψ_j(s_{N₀+km+j})] + ∑_j ρ_j` is an **exact** identity for
`x_{k+1} − (x_k − (m h₀)Φ(x_k))`, using `∑ᵢ Ψᵢ = mΦ` and the block bijection.  The three error
sources are all `O(h₀²)`: `h₀ − h_j ≤ m h₀²`, the within-block drift is `≤ m h₀ Q(d_k)` (a crude
Grönwall bound `d_{n+j} + S + Cr ≤ (2+K)^j(d_n + S + Cr)` inside the block), and `‖ρ_j‖ ≤ Cr h₀²`.
The resulting recursion is exactly the state-dependent Proposition 4.15, and the within-block
drift `→ 0` transfers the block convergence to the whole sequence.

## Batch: Lemma 4.3 (renorming) and the weighted-geometric-mean symmetry

`HTGeometry/LogarithmicNormRenorming.lean` (wired, built, axioms clean) — general mathlib gap
- `semigroupSup T ω x := sup_{t ≥ 0} e^{-ωt}‖T t x‖`, with `norm_le_semigroupSup`,
  `semigroupSup_le`, `semigroupSup_add_le`, `semigroupSup_smul`, `semigroupSup_apply_le`.
- **`exists_equivalent_norm_of_semigroup_growth`** — **Lemma 4.3, the renorming procedure**:
  a semigroup with `‖T t‖ ≤ M e^{ωt}` admits an equivalent norm (`‖x‖ ≤ p x ≤ M‖x‖`, subadditive,
  absolutely homogeneous) in which `p(T t x) ≤ e^{ωt} p x`, i.e. the logarithmic norm of the
  generator is at most `ω`.
- `norm_semigroup_nat_le`, **`exists_growth_of_pow_bound`** — the continuous growth bound from a
  discrete geometric bound: `‖T n‖ ≤ e^{ωn}` eventually plus local boundedness gives
  `‖T t‖ ≤ M e^{ωt}` for all `t ≥ 0` (splitting `t = ⌊t⌋ + s`).

What is still missing for the paper's exact phrasing of Lemma 4.3 is only the identification of
the growth exponent with the spectral abscissa `Reσ(A)`.  That is `σ(e^A) ⊆ exp σ(A)`; mathlib has
only `spectrum.exp_mem_exp` (the other inclusion), and the missing half needs the Riesz–Dunford
holomorphic functional calculus.  Everything else in the renorming is now unconditional.

`HTGeometry/BuresWasserstein/WeightedGeometricMeanSymmetry.lean` (wired, built, axioms clean)
- **`rpow_mul_star_intertwine`** — `(z z^*)^t z = z (z^* z)^t` for `t ≥ 0`, from the corpus's
  `cfc_mul_eq_mul_cfc_of_intertwine` together with `CFC.rpow_def` and `cfc_nnreal_eq_real`
  (the continuous function used is `x ↦ (x.toNNReal)^t`, which is `(max x 0)^t` and therefore
  continuous on all of `ℝ` for `t ≥ 0`).
- **`wgm_symm`** — `a #_t b = b #_{1-t} a`.  With `z := a^{-1/2}b^{1/2}` and
  `zi := b^{-1/2}a^{1/2}`, both means collapse to `b^{1/2}(b^{-1/2}ab^{-1/2})^{1-t}b^{1/2}`;
  the only analytic input is the intertwining above.  No congruence-invariance of `#_t` and no
  unitary polar decomposition is needed.
- **`wgm_mono_left`**, **`wgm_mono`** — monotonicity of `#_t` in the first argument and jointly,
  immediate from the symmetry plus the existing `wgm_mono_right`.

These are the first two of the four inputs the Lim–Pálfia power mean `P_t` needs (the remaining
two are left homogeneity `(r•a) #_t b = r^{1−t}(a #_t b)`, which needs a `CFC.rpow_smul` that
mathlib lacks, and the Thompson-ratio contraction).

## Batch: the Loewner ratio and the Lim–Pálfia power mean — BUILT

`HTGeometry/LoewnerRatio.lean` (wired, built, axioms clean) — mathlib gap
The Thompson metric in multiplicative form, so every estimate stays algebraic:
- `nonneg_of_smul_one_nonneg`, `le_of_smul_one_le_smul_one` — the Loewner order on multiples of
  the unit is the order on coefficients (proved without spectra: `c < 0` forces `c·1 = 0`).
- `loewnerRatio a b := sInf {s > 0 | a ≤ s b}`, `loewnerRatio_le`, `loewnerRatio_nonneg`,
  `loewnerRatio_set_nonempty`.
- **`le_loewnerRatio_smul`** — the infimum is attained (`{s | a ≤ s b}` is closed, and
  `M + 1/(n+1)` lies in it for every `n`).
- `loewnerRatio_pos`, `loewnerRatio_mul_le` (chain rule), `one_le_loewnerRatio_mul`,
  `loewnerRatio_le_one_add` (`M(a/b) ≤ 1 + ‖a−b‖/α`),
  `norm_sub_le_of_loewnerRatio` (`‖a−b‖ ≤ 3β(ρ−1)`).

`HTGeometry/BuresWasserstein/WeightedGeometricMeanSymmetry.lean` (extended)
- **`rpow_smul_of_nonneg`** — `(r·x)^t = r^t·x^t`, the `CFC.rpow_smul` that mathlib lacks,
  via `cfc_comp_smul` and the `ℝ≥0`→`ℝ` bridge.
- **`wgm_smul_left`** — `(r·a) #_t b = r^{1−t}(a #_t b)`.

`HTGeometry/BuresWasserstein/PowerMeanContraction.lean` (wired, built, axioms clean)
- `wgm_self`, `powerMeanMap s w Av t X := ∑ᵢ wᵢ (X #_t Aᵢ)`, `powerMeanMap_mem_Icc`,
  `powerMeanMap_le_of_le`, and **`loewnerRatio_powerMeanMap_le`**:
  `M(F X / F Y) ≤ M(X/Y)^{1−t}` — the `(1−t)`-contraction in the Thompson metric.

`HTGeometry/BuresWasserstein/PowerMean.lean` (wired, built, axioms clean)
- `rpow_le_one_add_mul_sub_one` — Bernoulli `x^s ≤ 1 + s(x−1)` from the weighted AM–GM
  `Real.geom_mean_le_arith_mean2_weighted`.
- **`powerMeanMap_fixedPoint_unique`** — uniqueness: `M(X/Y) ≤ M(X/Y)^{1−t}` forces `M ≤ 1`.
- `norm_powerMeanMap_sub_le` — `F` is norm-Lipschitz on the interval.
- **`exists_powerMean`**, **`existsUnique_powerMean`** — **the Lim–Pálfia power mean `P_t`**:
  for `0 < t ≤ 1` the equation `X = ∑ᵢ wᵢ (X #_t Aᵢ)` has exactly one solution in the Loewner
  interval spanned by the data.  Existence by iterating from `α·1`: the Loewner ratio of
  consecutive iterates obeys `M − 1 ≤ (1−t)ⁿ(M₀ − 1)`, so `‖Xₙ − Xₙ₊₁‖ ≤ 3β(M₀−1)(1−t)ⁿ` is
  geometrically summable and the sequence is norm-Cauchy.  No Thompson **metric space**
  structure and no completeness argument for it is needed — only the ratio and its chain rule.

This is the object the paper cites from [LP12]; neither mathlib nor the corpus had it.  It is
the last missing input for Theorem 6.8.

## Batch: Theorem 6.8 — CLOSED for the paper's core range

`HTGeometry/BuresWasserstein/WeightedGeometricMeanArith.lean` (wired, built, axioms clean)
- `conjugate_le_conjugate`.
- **`wgm_le_arith`** — the weighted arithmetic–geometric mean inequality
  `X #_s Y ≤ (1−s)X + sY`, obtained by conjugating away the first argument and feeding the scalar
  Bernoulli inequality `y^s ≤ (1−s) + s y` through `cfc_mono`.
- **`wgm_wgm`** — the affine parameter law `X #_s (X #_t Y) = X #_{ts} Y`, which is
  `(c^t)^s = c^{ts}` after the same conjugation.

`HTGeometry/BuresWasserstein/PowerMeanWasserstein.lean` (wired, built, axioms clean)
- `powerMeanMap_mono`, `wgm_strictlyPositive`.
- **`tendsto_powerMeanMap_iterate`** — the power-mean iteration converges to the fixed point from
  *any* starting point of the interval (same geometric ratio decay as in the existence proof).
- **`ringInverse_isWassersteinPoint_le_powerMean`** — **Theorem 6.8(i)** for `t ∈ [1/2, 1]`:
  `Ω ≥ 1` implies `Ω⁻¹ ≤ P_t`, i.e. `Ω ≥ P_t^{-1}`.
  The proof is exactly the paper's: `X # Aᵢ = X #_{1/(2t)} (X #_t Aᵢ)` by the affine law, then
  AM–GM, then summing with `∑ wᵢ = 1` and `X ≤ 1` gives `X ≤ g_t(X)`; monotonicity of `g_t` gives
  `X ≤ g_t^r(X)` for all `r`, and the iterates converge to `P_t`.

Scope note: the paper's statement covers `1/2 ≤ t < 2`.  The range `t ∈ (1,2)` is obtained in the
paper from `P_1 = 𝒜 ≤ P_t`, cited as [Seo, Proposition 4.5(v)]; part (ii) is the substitution
`P_t(ω; 𝔸⁻¹) = P_{−t}(ω; 𝔸)^{-1}`, which is the *definition* of `P_t` for negative `t`.  Both are
outside what the paper proves.  The range `[1/2, 1]` — the part the paper actually argues — is
now unconditional in Lean.

## Batch: Bochner integrals and the Loewner order — the Section 5 gateway

`HTGeometry/BochnerLoewner.lean` (wired, built, axioms clean) — mathlib gap
- `starCLM` — the star operation as a real-linear continuous map.
- `isSelfAdjoint_integral` — the Bochner integral of a self-adjoint family is self-adjoint.
- **`integral_nonneg_of_le_smul_one`** — the Bochner integral of a family with `0 ≤ f ω ≤ R·1`
  is positive.  No theory of closed convex cones is used: `‖R·1 − f ω‖ ≤ R` pointwise gives
  `‖R·1 − ∫f‖ ≤ ∫‖R·1 − f‖ ≤ R`, and the corpus lemma `smul_one_le_of_norm_sub_le` turns a
  self-adjoint element within distance `R` of `R·1` into one dominating `(R−R)·1 = 0`.
- **`integral_mono_of_le`** — the Bochner integral is monotone for the Loewner order.

This is the missing primitive for Theorem 5.1 (`wass_P2`), whose field is
`Φ_μ(X) = ∫ Ψ_A(X) dμ(A)`: all of the Section 3 estimates are pointwise in `A`, so with a
monotone, positivity-preserving integral they transfer by integration.

`HTGeometry/BuresWasserstein/PowerMeanWasserstein.lean` (extended)
- **`powerMean_ringInverse_le_isWassersteinPoint`** — Theorem 6.8 in the paper's own form,
  `Ω ≥ P_t^{-1}`.  Part (ii) of the theorem is this same statement, since `P_t(ω; 𝔸⁻¹)` is by
  *definition* `P_{−t}(ω; 𝔸)^{-1}` for negative `t`.

## Batch: Section 5 opened — Theorem 5.1 uniqueness

`HTGeometry/HilbertSchmidtBochner.lean` (wired, built, axioms clean) — mathlib gap
- `SLSpace.opCLM` — the inclusion `S²(ℋ) → B(ℋ)` as a norm-one real-linear bounded map.
- **`SLSpace.op_integral`** — a Bochner integral taken in `S²(ℋ)` agrees with the
  operator-valued Bochner integral of the underlying operators.
- **`SLSpace.hsNorm_integral_le`**, **`SLSpace.re_hsInner_integral`** — the Hilbert–Schmidt norm
  and the Hilbert–Schmidt inner product against a fixed vector pass through the integral.
- `SLSpace.isHilbertSchmidt_integral`, `SLSpace.isSelfAdjoint_integral'`.

`HTGeometry/BuresWasserstein/WassersteinMeasure.lean` (wired, built, axioms clean)
- `wassField_unit` — the one-point instance of the finite Wasserstein field, `1 − B # X⁻¹`.
- **`re_hsInner_single_sub_lower`** — pointwise strong monotonicity: the global estimate applied
  to the one-point family `{B}` with weight `1`.
- **`eq_of_integral_wassField_eq_zero`** — **Theorem 5.1 (`wass_P2`), uniqueness**: a
  measure-weighted Wasserstein equation `∫ Ψ_A(X) dμ(A) = 0` has at most one solution in a
  Loewner interval.

### Why this works without redoing Section 3
Every Section 3 estimate is **pointwise in `A`**.  Taking the field's integral in `S²(ℋ)` — a
genuine real Hilbert space — makes the Hilbert–Schmidt inner product a continuous linear
functional, so `⟨∫F, Z⟩ = ∫⟨F, Z⟩` and the pointwise strong monotonicity integrates directly:

`0 = ⟨∫Ψ_A(X)dμ − ∫Ψ_A(Y)dμ, X−Y⟩ ≥ (κ − C‖X−Y‖/N)‖X−Y‖²_HS`  for every `N ≥ 1`.

No refactor of the finite theory into integrals was needed; the one-point family carries it.

## Batch: Theorem 5.1 — CLOSED (existence and uniqueness)

`HTGeometry/HilbertSchmidtBochner.lean` (extended)
- `SLSpace.mk`, `SLSpace.op_mk` — the constructor of `S²(ℋ)` from an operator with its two
  proofs, which the module previously lacked.

`HTGeometry/HilbertSchmidtBanachInvariant.lean` (wired, built, axioms clean)
- `tendsto_of_hs_limit` — Hilbert–Schmidt convergence implies operator-norm convergence.
- **`exists_fixedPoint_hs_invariant`** — Banach fixed point with **no prescribed ball**: a
  `θ`-contraction preserving a class closed under Hilbert–Schmidt limits, whose members all
  differ from a base point by a Hilbert–Schmidt operator, has a fixed point in the class.  It is
  the ball version applied with the radius `(1−θ)⁻¹‖G X₀ − X₀‖_HS` read off from the first step,
  which is what removes the "small defect" side condition of the continuation argument.

`HTGeometry/BuresWasserstein/WassersteinMeasureField.lean` (wired, built, axioms clean)
- `isSelfAdjoint_one_sub_gm`, `gm_ringInverse_Icc` — the pointwise self-adjointness and the
  Loewner envelope `√α·X^{-1/2} ≤ A # X⁻¹ ≤ √β·X^{-1/2}`.
- **`hsNorm_single_sub_le`** — the pointwise Lipschitz bound, the one-point instance of the
  finite estimate.
- `wassSL B X` — the pointwise field as an element of `S²(ℋ)`; `wassSL_op` identifies it with
  `1 − B # X⁻¹` on the Loewner interval.
- `integrable_one_sub_gm`, **`wassFieldMeasure_eq_op_integral`**, `isHilbertSchmidt_wassFieldMeasure`,
  `isSelfAdjoint_wassFieldMeasure`, `wassFieldMeasure_sub_eq`.
- **`neg_wassFieldMeasure_Icc'`** — the two-sided Loewner envelope of `−Φ_μ`, with the uniform
  majorant supplied by the argument itself: the deviation from either envelope is at most
  `(√β − √α)·X^{-1/2} ≤ (√β − √α)√(α⁻¹)·1`, which is exactly the hypothesis
  `integral_mono_of_le` needs.
- **`sub_smul_wassFieldMeasure_mem_Icc'`** — subtangentiality: `X − λΦ_μ(X) ∈ [α·1, β·1]` for
  every `0 < λ ≤ 2α`.
- **`hsNorm_wassFieldMeasure_sub_le`** — the field is `wassLipConst α β`-Lipschitz in `‖·‖_HS`.
- **`re_hsInner_wassFieldMeasure_sub_lower`** — global strong monotonicity, telescoped along the
  `N`-fold subdivision, integrated pointwise.
- **`hsNormSq_gradientStepMeasure_sub_le`** — the explicit gradient step contracts with factor
  `1 − 2t(κ − C‖X−Y‖/N) + t²L²`.

`HTGeometry/BuresWasserstein/WassersteinMeasureExistence.lean` (wired, built, axioms clean)
- `nonempty_of_isProbabilityMeasure`, `norm_le_of_Icc` (`‖X‖ ≤ β` on the interval).
- **`exists_wassFieldMeasure_eq_zero`** — **Theorem 5.1, existence**.
- **`existsUnique_wassFieldMeasure_eq_zero`** — **Theorem 5.1 in full**: for a probability
  measure supported in `[α·1, β·1]` the equation `∫ Ψ_A(X) dμ(A) = 0` has exactly one solution
  there.

### The mechanism
No Banach–Finsler renorming and no homotopy continuation are used.  On the interval the
derivative of `Φ_μ` is positive definite in the Hilbert–Schmidt inner product, so the explicit
gradient step `G X = X − tΦ_μ(X)` is the contraction:

* subtangentiality (`sub_smul_wassFieldMeasure_mem_Icc'`) keeps `G` inside `[α·1, β·1]` for
  `0 < t ≤ 2α`;
* the interval is norm-bounded (`‖X − Y‖ ≤ 2β`), so choosing the subdivision `N` with
  `C·2β/N ≤ κ/2` makes the second-order defect harmless **uniformly**, giving
  `⟨Φ_μ(X) − Φ_μ(Y), X − Y⟩ ≥ (κ/2)‖X − Y‖²_HS` with `κ = α²/(2β³)`;
* with `t ≤ κ/(2L²)` the step factor is `1 − tκ/2 < 1`, so `G` is a
  `√(1 − tκ/2)`-contraction;
* the class `{X : X* = X, α·1 ≤ X ≤ β·1, X − A_w ∈ S²}` is closed under Hilbert–Schmidt limits
  (the Loewner order is closed and HS convergence implies norm convergence), so
  `exists_fixedPoint_hs_invariant` applies with base point any `A_{w₀}`; a probability measure
  forces `Ω` nonempty, so such a base point exists.

Side condition: the theorem carries `Integrable (fun w => wassSL (A w) X) μ` for `X` in the
interval — Bochner integrability of the integrand, the same kind of hypothesis mathlib's own
`integral_add`/`integral_mono` carry.  It is not a mathematical assumption about the geometry:
it is the statement that `Φ_μ` is defined.  In infinite dimensions it cannot be derived, since
strong measurability of `w ↦ A_w` is not implied by anything else in the setting.

## Batch: Theorem 5.3 — the whole deterministic engine, unconditional

`HTGeometry/EtemadiWeightedAverage.lean` (wired, built, axioms clean) — external theorem, mathlib gap
Etemadi's Theorem 1, in its deterministic (pathwise) form, which is what the a.s. statement rests on:
- `partialSum`, `totalWeight`, `defect`, `totalVar`; `sum_mul_eq` (summation by parts),
  `totalWeight_eq` (the same identity for the constant sequence `1`), **`key_identity`**
  — subtracting the two replaces the partial sums `Sₙ` by the defects `Sₙ − x₀n`.
- **`tendsto_weightedAverage`** — if `Sₙ/n → x₀` and the positive weights satisfy
  `n wₙ ≤ K Wₙ`, `∑_{i<n}(i+1)|w_{i+1} − wᵢ| ≤ K Wₙ` and `Wₙ → ∞`, then
  `Wₙ⁻¹ ∑ wᵢxᵢ → x₀`.  The boundary term is `(n wₙ/Wₙ)·δₙ` and the sum term splits at the index
  where `δ` is already small; the head is a fixed constant divided by `Wₙ → ∞`.
- `totalVar_eq_of_antitone` (`Vₙ = Wₙ − n wₙ`, a telescoping), `totalVar_le_of_antitone`,
  `one_le_of_weight_cond`, **`tendsto_weightedAverage_of_antitone`** — for monotone weights the
  second condition is automatic, exactly as the paper's remark says.

`HTGeometry/BuresWasserstein/EtemadiRecursionLimit.lean` (wired, built, axioms clean)
- `etemadiProd_succ_le` (`∏_{j≤n}(1−α/j) ≤ 1−α` from the first factor on), `totalWeight_etemadi`,
  **`etemadi_weight_cond`** — the first Etemadi condition for the recursion's own weights, with
  constant **one**: it reduces to `α ≤ 1 − ∏_{j≤n}(1−α/j)`.
- **`tendsto_of_etemadiRecursion`** — `sₙ = (1−α/n)sₙ₋₁ + (α/n)bₙ₋₁` converges to the Cesàro
  limit of `b`.  Lemma 5.2 turns the recursion into a weighted average, the weights are antitone,
  and the initial datum contributes `s₀/(1+Wₙ) → 0`.

`HTGeometry/BuresWasserstein/RobbinsMonroCesaro.lean` (wired, built, axioms clean)
- **`tendsto_zero_of_robbins_cesaro`** — `d(n+1) ≤ (1−α/(n+1))d(n) + (n+1)⁻¹εₙ + C(n+1)⁻²`
  with `εₙ` only **Cesàro-null** forces `d(n) → 0`.  The classical Robbins–Monro theorem the
  corpus already had needs a square-summable error and does not apply; the comparison sequence is
  the Etemadi recursion driven by `εₙ + C/(n+1)`, whose Cesàro means vanish.

`HTGeometry/BuresWasserstein/WassersteinPerturbedDescent.lean` (wired, built, axioms clean)
- **`tendsto_hsNorm_sub_of_perturbed_descent`** — perturbed gradient descent for `Φ_μ` with step
  `λ/(n+1)` converges to the barycentre whenever the Cesàro means of the perturbation vanish.
  The exact step contracts by `√(1 − tκ/2) ≤ 1 − tκ/4`, so the distance obeys exactly the
  Cesàro–Robbins–Monro recursion.
- **`tendsto_hsNorm_sub_of_empirical_descent`** — the same for the paper's iteration
  `X_{n+1} = X_n − (λ/(n+1))Φ_{ν_{n+1}}(X_n)`, where each `ν_n` is a probability measure in the
  same Loewner interval: subtangentiality for `ν_{n+1}` keeps the iterates in the interval, so no
  invariance has to be assumed.

### What Theorem 5.3 still needs
Only the probabilistic input: that the empirical measures of an i.i.d. sample satisfy
`n⁻¹ ∑_{i<n} ‖Φ_{ν_i}(X_i) − Φ_μ(X_i)‖_HS → 0` almost surely.  Through the Lipschitz bound in the
first argument (`hsNorm_gm_sub_le_left`) this is `n⁻¹ ∑ W₁(ν_i, μ) → 0`, i.e. **Varadarajan's
theorem** on a separable Banach space — a full empirical-process development that neither mathlib
nor the corpus has.  Everything else in the proof of Theorem 5.3 is now Lean-closed and
unconditional.

## Batch: Corollary 6.4 (Lie–Trotter / log-Euclidean limit) — CLOSED

`HTGeometry/BuresWasserstein/OperatorLogRpow.lean` (wired, built, axioms clean) — mathlib gap
- `norm_le_norm_of_le` — `0 ≤ P ≤ Q ⟹ ‖P‖ ≤ ‖Q‖`, the device that turns a Loewner sandwich into
  a norm estimate.
- **`log_rpow_eq_smul`** — `log (a^y) = y·log a`, and **`log_ringInverse`** — `log (a⁻¹) = −log a`.
  Both by composing the continuous functional calculus with `Real.log (x^y) = y log x`.
- **`tendsto_rpow_sub_one_log`** — `p⁻¹(a^p − 1) → log a` as `p ↓ 0`, the operator form of
  mathlib's `CFC.tendsto_cfc_rpow_sub_one_log`.

`HTGeometry/BuresWasserstein/LieTrotterLogEuclidean.lean` (wired, built, axioms clean)
- `abs_log_one_add_sub_le` — `|log(1+v) − v| ≤ 2v²` for `|v| ≤ ½`.
- **`abs_rpow_sub_exp_le`** — the scalar comparison `|(1+pu)^{1/p} − eᵘ| ≤ 4e^C p C²`, uniform for
  `|u| ≤ C`; no hypothesis on `C` is needed, it follows from `|u| ≤ C`.
- `abs_sub_one_le_of_mem_spectrum`, **`norm_rpow_sub_exp_le`** — the same comparison for an
  operator near the identity, obtained by running both sides through the functional calculus of
  `T` and using the isometry `‖cfc f T‖ = sup_{σ(T)}|f|`.
- `ringInverse_rpow` — `(a^p)⁻¹ = (a⁻¹)^p`.
- **`tendsto_rpow_isWassersteinPoint_logEuclidean`** — **Corollary 6.4**:
  `Ω(ω; A₁^p, …, A_m^p)^{1/p} → exp(∑ wᵢ log Aᵢ)` as `p ↓ 0`.

### The mechanism
No differentiation of the barycentre in `p` is used.  Theorem 6.2 sandwiches the barycentre of
the powers,

`2·1 − ∑ wᵢ Aᵢ^{−p} ≤ Ω(ω; 𝔸^p) ≤ ∑ wᵢ Aᵢ^p`,

and after subtracting `1` and dividing by `p` both envelopes converge to `∑ wᵢ log Aᵢ` by the
first-order expansion of the logarithm.  Since `0 ≤ M_p − L_p ≤ U_p − L_p`, the order sandwich
becomes a norm estimate, so `Ω(ω; 𝔸^p) = 1 + p·M_p` with `M_p → ∑ wᵢ log Aᵢ`.  Both
`Ω(ω;𝔸^p)^{1/p}` and `exp(M_p)` are functions of the *same* operator `1 + p·M_p` in the
continuous functional calculus, so their distance is the sup over the spectrum of
`|x^{1/p} − e^{(x−1)/p}|`, which the scalar comparison bounds by `O(p)`.

The statement is unconditional: it does not assume that a barycentre exists in `ℙ` (Theorem 3.16,
still blocked), it characterizes the limit of whatever solutions are given.
