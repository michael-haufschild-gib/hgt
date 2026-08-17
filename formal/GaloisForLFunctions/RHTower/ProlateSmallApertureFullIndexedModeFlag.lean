import GaloisForLFunctions.RHTower.ProlateSmallApertureIndexedModeFlag

open MeasureTheory Filter Topology Set Complex

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry
open _root_.RHTower

/-- Taylor truncation through degree `n-1` for the full aperture synthesis. -/
noncomputable def apertureMomentTaylorHead (n : ℕ) (c : ℝ) :
    UnitPhysicalScalarL2 →L[ℂ] UnitApertureL2 :=
  ∑ j ∈ Finset.range n,
    ((c : ℂ) ^ j • apertureMomentPowerSynthesisCoeff j)

theorem hasRectRankLE_apertureMomentTaylorHead (n : ℕ) (c : ℝ) :
    HasRectRankLE (apertureMomentTaylorHead n c) n := by
  classical
  let q : Fin n → UnitApertureL2 := fun i =>
    fourierGroundVector 1 (apertureMomentResidual 0) (i : ℕ)
  let V : Submodule ℂ UnitApertureL2 := Submodule.span ℂ (Set.range q)
  have hdim : Module.finrank ℂ V ≤ n := by
    change Module.finrank ℂ (Submodule.span ℂ (Set.range q)) ≤ n
    refine (finrank_span_le_card (R := ℂ) (Set.range q)).trans ?_
    rw [Set.toFinset_range]
    exact Finset.card_image_le.trans (by simp)
  refine ⟨V, FiniteDimensional.span_of_finite ℂ (Set.finite_range q), hdim, ?_⟩
  intro f
  rw [apertureMomentTaylorHead, sum_apply]
  exact Submodule.sum_mem V fun j hj => by
    simp only [Finset.mem_range] at hj
    rw [smul_apply, apertureMomentPowerSynthesisCoeff_apply]
    have hq : fourierGroundVector 1 (apertureMomentResidual 0) j ∈ V :=
      Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩
    exact V.smul_mem _ (V.smul_mem _ hq)

/-- Full aperture synthesis is compact as an operator-norm limit of its finite-rank
Taylor heads. -/
theorem isCompactOperator_apertureMomentFourierSynthesis_zero (c : ℝ) :
    IsCompactOperator (apertureMomentFourierSynthesis 0 c) := by
  have hlim : Tendsto (fun n : ℕ => apertureMomentTaylorHead n c) atTop
      (𝓝 (apertureMomentFourierSynthesis 0 c)) := by
    simpa [apertureMomentTaylorHead] using
      (hasSum_apertureMomentFourierSynthesis_coeff c).tendsto_sum_nat
  apply isClosed_setOf_isCompactOperator.mem_of_tendsto hlim
  exact Filter.Eventually.of_forall fun n =>
    (hasRectRankLE_apertureMomentTaylorHead n c).isCompactOperator

/-- Ordered full fixed-unit Slepian spectrum. -/
noncomputable def complexUnitBandValue (c : ℝ) (k : ℕ) : ℝ :=
  approxNumber (complexBandOperatorL2 c) k

/-- Canonical greedy input vector of the full fixed-unit Slepian operator. -/
noncomputable def indexedFullSlepianInputMode (c : ℝ) (k : ℕ) :
    ComplexUnitIntervalL2 :=
  ContinuousLinearMap.sgVec (complexBandOperatorL2 c) k

/-- Rectangular singular value of the full aperture synthesis. -/
noncomputable def indexedFullSlepianSingularValue (c : ℝ) (k : ℕ) : ℝ :=
  rectApproxNumber (apertureMomentFourierSynthesis 0 c) k

theorem complexUnitBandValue_eq_sgVal {c : ℝ} (hc : 0 < c) (k : ℕ) :
    complexUnitBandValue c k =
      ContinuousLinearMap.sgVal (complexBandOperatorL2 c) k := by
  rw [complexUnitBandValue,
    approxNumber_eq_singVal (isCompactOperator_complexBandOperatorL2 c),
    ← abs_sgVal_eq_singVal (isCompactOperator_complexBandOperatorL2 c)
      (complexBandOperatorL2_isPositive hc).isSymmetric,
    abs_of_nonneg (sgVal_nonneg_of_isPositive
      (complexBandOperatorL2_isPositive hc) k)]

/-- Exact indexed Gram transfer for the full fixed-unit Slepian operator. -/
theorem rectApproxNumber_apertureMomentSynthesis_sq_eq_scaled_bandValue
    {c : ℝ} (hc : 0 < c) (k : ℕ) :
    indexedFullSlepianSingularValue c k ^ 2 =
      (2 * Real.pi / c) * complexUnitBandValue c k := by
  rw [indexedFullSlepianSingularValue, complexUnitBandValue,
    rectApproxNumber_sq_eq_approxNumber_adjoint_comp_self
      (apertureMomentFourierSynthesis 0 c)
      (isCompactOperator_apertureMomentFourierSynthesis_zero c) k,
    adjoint_comp_apertureMomentFourierSynthesis_eq_bandOperator hc.ne',
    approxNumber_smul]
  change _ = _ * approxNumber (complexBandOperatorL2 c) k
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (div_pos (mul_pos (by norm_num) Real.pi_pos) hc)]

theorem indexedFullSlepianInputMode_norm_of_singularValue_pos
    {c : ℝ} (hc : 0 < c) {k : ℕ}
    (hs : 0 < indexedFullSlepianSingularValue c k) :
    ‖indexedFullSlepianInputMode c k‖ = 1 := by
  let S := complexBandOperatorL2 c
  have hsq := rectApproxNumber_apertureMomentSynthesis_sq_eq_scaled_bandValue hc k
  have hscale : 0 < 2 * Real.pi / c := div_pos (by positivity) hc
  have hval : 0 < complexUnitBandValue c k := by nlinarith
  rcases ContinuousLinearMap.norm_sgVec_zero_or_one S k with hzero | hone
  · have hdead := ContinuousLinearMap.sgVal_zero_of_dead (S := S) (n := k) hzero
    have heq := complexUnitBandValue_eq_sgVal hc k
    linarith
  · exact hone

theorem indexedFullSlepianInputMode_eigen
    {c : ℝ} (hc : 0 < c) (k : ℕ) :
    complexBandOperatorL2 c (indexedFullSlepianInputMode c k) =
      (complexUnitBandValue c k : ℂ) • indexedFullSlepianInputMode c k := by
  unfold indexedFullSlepianInputMode
  rw [ContinuousLinearMap.apply_sgVec, ← complexUnitBandValue_eq_sgVal hc k]

/-- Normalized full output singular mode.  Positivity is supplied eventually by
the sharp full singular-value lower bound. -/
noncomputable def indexedFullSlepianOutputMode (c : ℝ) (k : ℕ) :
    UnitApertureL2 :=
  ((indexedFullSlepianSingularValue c k : ℝ) : ℂ)⁻¹ •
    apertureMomentFourierSynthesis 0 c (indexedFullSlepianInputMode c k)

theorem norm_apertureMomentFourierSynthesis_inputMode_sq
    {c : ℝ} (hc : 0 < c) {k : ℕ}
    (hs : 0 < indexedFullSlepianSingularValue c k) :
    ‖apertureMomentFourierSynthesis 0 c (indexedFullSlepianInputMode c k)‖ ^ 2 =
      indexedFullSlepianSingularValue c k ^ 2 := by
  let T := apertureMomentFourierSynthesis 0 c
  let x := indexedFullSlepianInputMode c k
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right]
  have hgram := adjoint_comp_apertureMomentFourierSynthesis_eq_bandOperator hc.ne'
  have heig := indexedFullSlepianInputMode_eigen hc k
  have hxnorm := indexedFullSlepianInputMode_norm_of_singularValue_pos hc hs
  have hsq := rectApproxNumber_apertureMomentSynthesis_sq_eq_scaled_bandValue hc k
  change Complex.re (inner ℂ x ((ContinuousLinearMap.adjoint T ∘L T) x)) = _
  rw [hgram, smul_apply, heig, smul_smul,
    inner_smul_right, inner_self_eq_norm_sq_to_K, hxnorm]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  norm_num
  simpa only [x, T] using hsq.symm

theorem indexedFullSlepianOutputMode_norm
    {c : ℝ} (hc : 0 < c) {k : ℕ}
    (hs : 0 < indexedFullSlepianSingularValue c k) :
    ‖indexedFullSlepianOutputMode c k‖ = 1 := by
  have hsne := ne_of_gt hs
  have hsq := norm_apertureMomentFourierSynthesis_inputMode_sq hc hs
  have hnorm :
      ‖apertureMomentFourierSynthesis 0 c (indexedFullSlepianInputMode c k)‖ =
        indexedFullSlepianSingularValue c k := by
    nlinarith [norm_nonneg
      (apertureMomentFourierSynthesis 0 c (indexedFullSlepianInputMode c k))]
  rw [indexedFullSlepianOutputMode, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hs, hnorm, inv_mul_cancel₀ hsne]

theorem indexedFullSlepianOutputMode_orthogonal_of_ne
    {c : ℝ} (hc : 0 < c) {j k : ℕ} (hjk : j ≠ k) :
    inner ℂ (indexedFullSlepianOutputMode c j)
      (indexedFullSlepianOutputMode c k) = 0 := by
  let T := apertureMomentFourierSynthesis 0 c
  let S := complexBandOperatorL2 c
  let xj := indexedFullSlepianInputMode c j
  let xk := indexedFullSlepianInputMode c k
  have horth : inner ℂ xj xk = 0 := by
    exact ContinuousLinearMap.inner_sgVec_sgVec_of_ne S hjk
  have hgram := adjoint_comp_apertureMomentFourierSynthesis_eq_bandOperator hc.ne'
  have heig := indexedFullSlepianInputMode_eigen hc k
  have hTorth : inner ℂ (T xj) (T xk) = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ xj ((ContinuousLinearMap.adjoint T ∘L T) xk) = 0
    rw [hgram, smul_apply, heig, smul_smul, inner_smul_right, horth, mul_zero]
  rw [indexedFullSlepianOutputMode, indexedFullSlepianOutputMode,
    inner_smul_left, inner_smul_right]
  change _ * (_ * inner ℂ (T xj) (T xk)) = 0
  rw [hTorth, mul_zero, mul_zero]

/-- Scalar comparing the full indexed output with its degree-`k` moment residual. -/
noncomputable def indexedFullMomentAlignmentCoeff (c : ℝ) (k : ℕ) : ℂ :=
  ((c ^ k / indexedFullSlepianSingularValue c k : ℝ) : ℂ) *
    inner ℂ (physicalComplexMonomialL2 k) (indexedFullSlepianInputMode c k)

theorem apertureMomentResidual_fullOutputMode_sub_alignmentCoeff
    {c : ℝ} (hc : 0 < c) {k : ℕ}
    (hs : 0 < indexedFullSlepianSingularValue c k) :
    apertureMomentResidual k (indexedFullSlepianOutputMode c k) -
        indexedFullMomentAlignmentCoeff c k •
          fourierGroundVector 1 (apertureMomentResidual k) k =
      ((c ^ k / indexedFullSlepianSingularValue c k : ℝ) : ℂ) •
        ((normalizedApertureMomentSynthesis k c -
            apertureMomentLeadingSynthesis k)
          (indexedFullSlepianInputMode c k)) := by
  let s := indexedFullSlepianSingularValue c k
  let x := indexedFullSlepianInputMode c k
  let q := fourierGroundVector 1 (apertureMomentResidual k) k
  have hs0 : s ≠ 0 := ne_of_gt hs
  have hc0 : c ^ k ≠ 0 := pow_ne_zero k hc.ne'
  have hPT : apertureMomentResidual k
      (apertureMomentFourierSynthesis 0 c x) =
        apertureMomentFourierSynthesis k c x := by
    exact congrArg
      (fun A : UnitPhysicalScalarL2 →L[ℂ] UnitApertureL2 => A x)
      (apertureMomentFourierSynthesis_eq_residual_comp k c).symm
  have hlead : apertureMomentLeadingSynthesis k x =
      inner ℂ (physicalComplexMonomialL2 k) x • q := by
    exact apertureMomentLeadingSynthesis_apply k _
  rw [indexedFullSlepianOutputMode, map_smul, hPT]
  change ((s : ℂ)⁻¹ • apertureMomentFourierSynthesis k c x) -
    ((((c ^ k / s : ℝ) : ℂ) * inner ℂ (physicalComplexMonomialL2 k) x) • q) = _
  rw [sub_apply, normalizedApertureMomentSynthesis, smul_apply, hlead]
  change ((s : ℂ)⁻¹ • apertureMomentFourierSynthesis k c x) -
    ((((c ^ k / s : ℝ) : ℂ) * inner ℂ (physicalComplexMonomialL2 k) x) • q) =
    ((c ^ k / s : ℝ) : ℂ) •
      ((((c ^ k)⁻¹ : ℝ) : ℂ) • apertureMomentFourierSynthesis k c x -
        inner ℂ (physicalComplexMonomialL2 k) x • q)
  rw [smul_sub, smul_smul, smul_smul]
  have hcast : (((c ^ k)⁻¹ : ℝ) : ℂ) = ((c ^ k : ℂ)⁻¹) := by norm_cast
  rw [hcast]
  apply sub_left_inj.mpr
  congr 1
  field_simp [hs0, hc.ne']
  norm_cast
  field_simp [hs0]

/-- Deflated full indexed output line converges to exact degree-`k` orthogonal
moment line. -/
theorem tendsto_indexedFullSlepianOutputMode_deflated_projective (k : ℕ) :
    Tendsto (fun c : ℝ =>
      ‖apertureMomentResidual k (indexedFullSlepianOutputMode c k) -
        indexedFullMomentAlignmentCoeff c k •
          fourierGroundVector 1 (apertureMomentResidual k) k‖)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
  let L := nhdsWithin (0 : ℝ) (Ioi 0)
  have hLpunct : L ≤ 𝓝[≠] (0 : ℝ) := by
    exact nhdsWithin_mono 0 (by intro c hc; exact ne_of_gt hc)
  have hop : Tendsto (fun c : ℝ =>
      ‖normalizedApertureMomentSynthesis k c -
        apertureMomentLeadingSynthesis k‖) L (nhds 0) :=
    ((tendsto_iff_norm_sub_tendsto_zero).mp
      (tendsto_normalizedApertureMomentSynthesis k)).mono_left hLpunct
  obtain ⟨C, hC, hlower⟩ :=
    exists_pos_eventually_rectApproxNumber_full_lower k
  have hlowerL : ∀ᶠ c : ℝ in L,
      C * c ^ k ≤ indexedFullSlepianSingularValue c k := by
    filter_upwards [hlower.filter_mono hLpunct, self_mem_nhdsWithin]
      with c hclower hc
    have hcpos : 0 < c := hc
    have habs : |c| = c := abs_of_pos hcpos
    simpa only [indexedFullSlepianSingularValue, habs] using hclower
  have hsposL : ∀ᶠ c : ℝ in L, 0 < indexedFullSlepianSingularValue c k := by
    filter_upwards [hlowerL, self_mem_nhdsWithin] with c hclower hc
    have hpow : 0 < c ^ k := pow_pos hc k
    exact lt_of_lt_of_le (mul_pos hC hpow) hclower
  have herr : Tendsto (fun c : ℝ =>
      ‖(normalizedApertureMomentSynthesis k c -
          apertureMomentLeadingSynthesis k)
        (indexedFullSlepianInputMode c k)‖) L (nhds 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hop
    filter_upwards [self_mem_nhdsWithin, hsposL] with c hc hspos
    have hcpos : 0 < c := hc
    calc
      ‖(normalizedApertureMomentSynthesis k c -
          apertureMomentLeadingSynthesis k)
        (indexedFullSlepianInputMode c k)‖ ≤
          ‖normalizedApertureMomentSynthesis k c -
            apertureMomentLeadingSynthesis k‖ *
            ‖indexedFullSlepianInputMode c k‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖normalizedApertureMomentSynthesis k c -
            apertureMomentLeadingSynthesis k‖ := by
        rw [indexedFullSlepianInputMode_norm_of_singularValue_pos hcpos hspos,
          mul_one]
  have hratio : ∀ᶠ c : ℝ in L,
      |c ^ k / indexedFullSlepianSingularValue c k| ≤ C⁻¹ := by
    filter_upwards [hlowerL, self_mem_nhdsWithin, hsposL]
      with c hclower hc hspos
    have hpow : 0 ≤ c ^ k := pow_nonneg hc.le k
    rw [abs_of_nonneg (div_nonneg hpow hspos.le), div_le_iff₀ hspos]
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hC).2 (by simpa [mul_comm] using hclower)
  have hbound : ∀ᶠ c : ℝ in L,
      ‖apertureMomentResidual k (indexedFullSlepianOutputMode c k) -
        indexedFullMomentAlignmentCoeff c k •
          fourierGroundVector 1 (apertureMomentResidual k) k‖ ≤
        C⁻¹ * ‖(normalizedApertureMomentSynthesis k c -
          apertureMomentLeadingSynthesis k)
        (indexedFullSlepianInputMode c k)‖ := by
    filter_upwards [hratio, self_mem_nhdsWithin, hsposL]
      with c hratio hc hspos
    have hcpos : 0 < c := hc
    rw [apertureMomentResidual_fullOutputMode_sub_alignmentCoeff hcpos hspos,
      norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hratio (norm_nonneg _)
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound ?_
  have hlast : Tendsto (fun c : ℝ => C⁻¹ *
      ‖(normalizedApertureMomentSynthesis k c -
          apertureMomentLeadingSynthesis k)
        (indexedFullSlepianInputMode c k)‖) L (nhds (C⁻¹ * 0)) :=
    tendsto_const_nhds.mul herr
  simpa [L] using hlast

/-- Fixed orthogonal-moment flag vector at degree `k`. -/
noncomputable def apertureMomentFlagVector (k : ℕ) : UnitApertureL2 :=
  fourierGroundVector 1 (apertureMomentResidual k) k

/-- Unit normalization of the fixed orthogonal-moment flag. -/
noncomputable def apertureMomentFlagUnit (k : ℕ) : UnitApertureL2 :=
  ((‖apertureMomentFlagVector k‖ : ℝ) : ℂ)⁻¹ • apertureMomentFlagVector k

theorem apertureMomentSpan_mono {j k : ℕ} (hjk : j ≤ k) :
    apertureMomentSpan j ≤ apertureMomentSpan k := by
  intro x hx
  refine Submodule.span_mono ?_ hx
  rintro _ ⟨i, rfl⟩
  exact ⟨(⟨(i : ℕ), lt_of_lt_of_le i.2 hjk⟩ : Fin k), rfl⟩

theorem apertureMomentFlagVector_ne_zero (k : ℕ) :
    apertureMomentFlagVector k ≠ 0 :=
  fourierGroundVector_apertureMomentResidual_ne_zero k

theorem apertureMomentFlagUnit_norm (k : ℕ) :
    ‖apertureMomentFlagUnit k‖ = 1 := by
  have hnorm : ‖apertureMomentFlagVector k‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (apertureMomentFlagVector_ne_zero k)
  rw [apertureMomentFlagUnit, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), inv_mul_cancel₀ hnorm]

theorem apertureMomentResidual_monomial_mem_span_succ (k : ℕ) :
    apertureMomentResidual k (apertureComplexMonomialL2 1 k) ∈
      apertureMomentSpan (k + 1) := by
  rw [apertureMomentResidual_apply]
  apply Submodule.sub_mem
  · exact apertureComplexMonomial_mem_momentSpan (by omega)
  · exact apertureMomentSpan_mono (Nat.le_succ k)
      ((apertureMomentSpan k).starProjection_apply_mem _)

theorem apertureMomentFlagVector_mem_span_succ (k : ℕ) :
    apertureMomentFlagVector k ∈ apertureMomentSpan (k + 1) := by
  rw [apertureMomentFlagVector, fourierGroundVector]
  exact Submodule.smul_mem _ _ (apertureMomentResidual_monomial_mem_span_succ k)

theorem apertureMomentFlagUnit_mem_span_succ (k : ℕ) :
    apertureMomentFlagUnit k ∈ apertureMomentSpan (k + 1) := by
  exact Submodule.smul_mem _ _ (apertureMomentFlagVector_mem_span_succ k)

theorem inner_apertureMomentFlagVector_eq_zero_of_lt {j k : ℕ} (hjk : j < k) :
    inner ℂ (apertureMomentFlagVector k) (apertureMomentFlagVector j) = 0 := by
  have hjmem : apertureMomentFlagVector j ∈ apertureMomentSpan k :=
    apertureMomentSpan_mono (by omega) (apertureMomentFlagVector_mem_span_succ j)
  have horth : inner ℂ
      (apertureMomentResidual k (apertureComplexMonomialL2 1 k))
      (apertureMomentFlagVector j) = 0 := by
    exact (apertureMomentSpan k).starProjection_inner_eq_zero _ _ hjmem
  rw [apertureMomentFlagVector, fourierGroundVector, inner_smul_left,
    horth, mul_zero]

theorem inner_apertureMomentFlagUnit_eq_zero_of_ne {j k : ℕ} (hjk : j ≠ k) :
    inner ℂ (apertureMomentFlagUnit j) (apertureMomentFlagUnit k) = 0 := by
  rcases lt_or_gt_of_ne hjk with hjklt | hkjlt
  · have h := inner_apertureMomentFlagVector_eq_zero_of_lt hjklt
    have h' : inner ℂ (apertureMomentFlagVector j)
        (apertureMomentFlagVector k) = 0 := by
      rw [← inner_conj_symm, h, map_zero]
    rw [apertureMomentFlagUnit, apertureMomentFlagUnit,
      inner_smul_left, inner_smul_right]
    change _ * (_ * inner ℂ (apertureMomentFlagVector j)
      (apertureMomentFlagVector k)) = 0
    rw [h', mul_zero, mul_zero]
  · have h := inner_apertureMomentFlagVector_eq_zero_of_lt hkjlt
    rw [apertureMomentFlagUnit, apertureMomentFlagUnit,
      inner_smul_left, inner_smul_right]
    change _ * (_ * inner ℂ (apertureMomentFlagVector j)
      (apertureMomentFlagVector k)) = 0
    rw [h, mul_zero, mul_zero]

theorem orthonormal_apertureMomentFlagUnit :
    Orthonormal ℂ apertureMomentFlagUnit := by
  rw [orthonormal_iff_ite]
  intro j k
  by_cases hjk : j = k
  · subst k
    rw [if_pos rfl, inner_self_eq_norm_sq_to_K, apertureMomentFlagUnit_norm]
    norm_num
  · rw [if_neg hjk, inner_apertureMomentFlagUnit_eq_zero_of_ne hjk]

/-- The first `k` normalized moment residuals form exactly the polynomial
moment subspace of degrees below `k`. -/
theorem span_apertureMomentFlagUnit_range_fin_eq_momentSpan (k : ℕ) :
    Submodule.span ℂ
        (Set.range fun i : Fin k => apertureMomentFlagUnit (i : ℕ)) =
      apertureMomentSpan k := by
  let U := Submodule.span ℂ
    (Set.range fun i : Fin k => apertureMomentFlagUnit (i : ℕ))
  have hle : U ≤ apertureMomentSpan k := by
    intro x hx
    refine Submodule.span_induction
      (p := fun x _ => x ∈ apertureMomentSpan k) ?_ (Submodule.zero_mem _) ?_ ?_ hx
    · rintro _ ⟨i, rfl⟩
      exact apertureMomentSpan_mono (by omega)
        (apertureMomentFlagUnit_mem_span_succ (i : ℕ))
    · intro x y _ _ hxM hyM
      exact Submodule.add_mem _ hxM hyM
    · intro a x _ hxM
      exact Submodule.smul_mem _ a hxM
  letI : FiniteDimensional ℂ (apertureMomentSpan k) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range
      (fun i : Fin k => apertureComplexMonomialL2 1 (i : ℕ)))
  have hUdim : Module.finrank ℂ U = k := by
    have horth : Orthonormal ℂ
        (fun i : Fin k => apertureMomentFlagUnit (i : ℕ)) :=
      orthonormal_apertureMomentFlagUnit.comp ((↑) : Fin k → ℕ)
        Fin.val_injective
    simpa only [U, Fintype.card_fin] using
      finrank_span_eq_card horth.linearIndependent
  have hMdim : Module.finrank ℂ (apertureMomentSpan k) = k := by
    have hli : LinearIndependent ℂ
        (fun i : Fin k => apertureComplexMonomialL2 1 (i : ℕ)) :=
      linearIndependent_apertureComplexMonomialL2_one.comp
        ((↑) : Fin k → ℕ) Fin.val_injective
    change Module.finrank ℂ (Submodule.span ℂ
      (Set.range fun i : Fin k => apertureComplexMonomialL2 1 (i : ℕ))) = k
    simpa only [Fintype.card_fin] using
      finrank_span_eq_card hli
  change U = apertureMomentSpan k
  exact Submodule.eq_of_le_of_finrank_eq hle (hUdim.trans hMdim.symm)

/-- Canonical orthonormal basis of the degree-below-`k` aperture moment span. -/
noncomputable def apertureMomentFlagBasis (k : ℕ) :
    OrthonormalBasis {i // i ∈ Finset.range k} ℂ (apertureMomentSpan k) := by
  classical
  let U := Submodule.span ℂ
    (((Finset.range k).image apertureMomentFlagUnit : Finset UnitApertureL2) :
      Set UnitApertureL2)
  have hEq : U = apertureMomentSpan k := by
    have hspan := span_apertureMomentFlagUnit_range_fin_eq_momentSpan k
    change Submodule.span ℂ
      ((↑((Finset.range k).image apertureMomentFlagUnit) :
        Set UnitApertureL2)) = apertureMomentSpan k
    rw [Finset.coe_image, Set.image_eq_range]
    have hset : Set.range
          (fun i : {i // i ∈ Finset.range k} => apertureMomentFlagUnit (i : ℕ)) =
        Set.range (fun i : Fin k => apertureMomentFlagUnit (i : ℕ)) := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨⟨(i : ℕ), Finset.mem_range.mp i.2⟩, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨⟨(i : ℕ), Finset.mem_range.mpr i.2⟩, rfl⟩
    exact (congrArg (Submodule.span ℂ) hset).trans hspan
  let bU : OrthonormalBasis {i // i ∈ Finset.range k} ℂ U :=
    OrthonormalBasis.span orthonormal_apertureMomentFlagUnit (Finset.range k)
  exact bU.map (LinearIsometryEquiv.ofEq U (apertureMomentSpan k) hEq)

theorem coe_apertureMomentFlagBasis_apply (k : ℕ)
    (i : {i // i ∈ Finset.range k}) :
    ((apertureMomentFlagBasis k i : apertureMomentSpan k) : UnitApertureL2) =
      apertureMomentFlagUnit (i : ℕ) := by
  simp [apertureMomentFlagBasis]

theorem apertureMomentSpan_starProjection_eq_sum_flag
    (k : ℕ) (x : UnitApertureL2) :
    (apertureMomentSpan k).starProjection x =
      ∑ i : {i // i ∈ Finset.range k},
        inner ℂ (apertureMomentFlagUnit (i : ℕ)) x •
          apertureMomentFlagUnit (i : ℕ) := by
  have h := congrArg
    (fun T : UnitApertureL2 →L[ℂ] UnitApertureL2 => T x)
    (OrthonormalBasis.starProjection_eq_sum_rankOne
      (apertureMomentFlagBasis k))
  simpa [sum_apply, InnerProductSpace.rankOne_apply,
    coe_apertureMomentFlagBasis_apply] using h

theorem eventually_indexedFullSlepianSingularValue_pos (k : ℕ) :
    ∀ᶠ c : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
      0 < indexedFullSlepianSingularValue c k := by
  let L := nhdsWithin (0 : ℝ) (Ioi 0)
  have hLpunct : L ≤ 𝓝[≠] (0 : ℝ) := by
    exact nhdsWithin_mono 0 (by intro c hc; exact ne_of_gt hc)
  obtain ⟨C, hC, hlower⟩ :=
    exists_pos_eventually_rectApproxNumber_full_lower k
  filter_upwards [hlower.filter_mono hLpunct, self_mem_nhdsWithin]
    with c hclower hc
  have habs : |c| = c := abs_of_pos hc
  have hpow : 0 < c ^ k := pow_pos hc k
  have hbound : C * c ^ k ≤ indexedFullSlepianSingularValue c k := by
    simpa only [indexedFullSlepianSingularValue, habs] using hclower
  exact lt_of_lt_of_le (mul_pos hC hpow) hbound

/-- Projective convergence of a unit indexed output forces its alignment
coefficient to converge in norm to the unique noncollapse scale. -/
theorem tendsto_norm_indexedFullMomentAlignmentCoeff_of_projective
    (k : ℕ)
    (hproj : Tendsto (fun c : ℝ =>
      ‖indexedFullSlepianOutputMode c k -
        indexedFullMomentAlignmentCoeff c k • apertureMomentFlagVector k‖)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0)) :
    Tendsto (fun c : ℝ => ‖indexedFullMomentAlignmentCoeff c k‖)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds ‖apertureMomentFlagVector k‖⁻¹) := by
  let L := nhdsWithin (0 : ℝ) (Ioi 0)
  let q := apertureMomentFlagVector k
  have hq : q ≠ 0 := apertureMomentFlagVector_ne_zero k
  have hspos := eventually_indexedFullSlepianSingularValue_pos k
  have habs : Tendsto (fun c : ℝ =>
      |‖indexedFullMomentAlignmentCoeff c k • q‖ - 1|) L (nhds 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ hproj
    filter_upwards [self_mem_nhdsWithin, hspos] with c hc hs
    calc
      |‖indexedFullMomentAlignmentCoeff c k • q‖ - 1| =
          |‖indexedFullMomentAlignmentCoeff c k • q‖ -
            ‖indexedFullSlepianOutputMode c k‖| := by
        rw [indexedFullSlepianOutputMode_norm hc hs]
      _ ≤ ‖indexedFullMomentAlignmentCoeff c k • q -
          indexedFullSlepianOutputMode c k‖ :=
        abs_norm_sub_norm_le _ _
      _ = ‖indexedFullSlepianOutputMode c k -
          indexedFullMomentAlignmentCoeff c k • q‖ := norm_sub_rev _ _
  have hnorm : Tendsto (fun c : ℝ =>
      ‖indexedFullMomentAlignmentCoeff c k • q‖) L (nhds 1) := by
    apply (tendsto_iff_norm_sub_tendsto_zero).2
    simpa only [Real.norm_eq_abs] using habs
  have hdiv := hnorm.div_const ‖q‖
  have hqnorm : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  simpa only [L, q, norm_smul, div_eq_mul_inv, mul_assoc,
    mul_inv_cancel₀ hqnorm, mul_one, one_mul] using hdiv

/-- Once lower indexed line `j` is identified and noncollapsed, exact singular
orthogonality forces the `k`th line to lose its `j`th moment coordinate. -/
theorem tendsto_inner_apertureMomentFlagUnit_indexedFull_of_lower
    {j k : ℕ} (hjk : j < k)
    (hproj : Tendsto (fun c : ℝ =>
      ‖indexedFullSlepianOutputMode c j -
        indexedFullMomentAlignmentCoeff c j • apertureMomentFlagVector j‖)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0))
    (hcoeff : Tendsto (fun c : ℝ =>
      ‖indexedFullMomentAlignmentCoeff c j‖)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds ‖apertureMomentFlagVector j‖⁻¹)) :
    Tendsto (fun c : ℝ => inner ℂ (apertureMomentFlagUnit j)
      (indexedFullSlepianOutputMode c k))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
  let L := nhdsWithin (0 : ℝ) (Ioi 0)
  let q := apertureMomentFlagVector j
  let a : ℝ := ‖q‖⁻¹
  have hq : q ≠ 0 := apertureMomentFlagVector_ne_zero j
  have hqnorm : 0 < ‖q‖ := norm_pos_iff.mpr hq
  have ha : 0 < a := inv_pos.mpr hqnorm
  have hzlower : ∀ᶠ c : ℝ in L,
      a / 2 < ‖indexedFullMomentAlignmentCoeff c j‖ :=
    (tendsto_order.1 hcoeff).1 (a / 2) (by linarith)
  have hspos := eventually_indexedFullSlepianSingularValue_pos k
  have hbound : ∀ᶠ c : ℝ in L,
      ‖inner ℂ (apertureMomentFlagUnit j)
        (indexedFullSlepianOutputMode c k)‖ ≤
      2 * ‖indexedFullSlepianOutputMode c j -
        indexedFullMomentAlignmentCoeff c j • apertureMomentFlagVector j‖ := by
    filter_upwards [self_mem_nhdsWithin, hzlower, hspos]
      with c hc hzlower hspos
    let z := indexedFullMomentAlignmentCoeff c j
    let yj := indexedFullSlepianOutputMode c j
    let yk := indexedFullSlepianOutputMode c k
    have hyknorm : ‖yk‖ = 1 := indexedFullSlepianOutputMode_norm hc hspos
    have horth : inner ℂ yj yk = 0 :=
      indexedFullSlepianOutputMode_orthogonal_of_ne hc (Nat.ne_of_lt hjk)
    have hinnerEq : inner ℂ (z • q) yk = inner ℂ (z • q - yj) yk := by
      rw [inner_sub_left, horth, sub_zero]
    have hinnerBound : ‖inner ℂ (z • q) yk‖ ≤ ‖z • q - yj‖ := by
      rw [hinnerEq]
      calc
        ‖inner ℂ (z • q - yj) yk‖ ≤ ‖z • q - yj‖ * ‖yk‖ :=
          norm_inner_le_norm _ _
        _ = ‖z • q - yj‖ := by rw [hyknorm, mul_one]
    have hzNorm : ‖inner ℂ (z • q) yk‖ =
        ‖z‖ * ‖inner ℂ q yk‖ := by
      rw [inner_smul_left, norm_mul, Complex.norm_conj]
    have huNorm : ‖inner ℂ (apertureMomentFlagUnit j) yk‖ =
        a * ‖inner ℂ q yk‖ := by
      simp only [apertureMomentFlagUnit, inner_smul_left, norm_mul,
        Complex.norm_conj, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg _)]
      rfl
    have hinnerNonneg : 0 ≤ ‖inner ℂ q yk‖ := norm_nonneg _
    rw [huNorm]
    change a * ‖inner ℂ q yk‖ ≤ 2 * ‖yj - z • q‖
    rw [norm_sub_rev]
    rw [hzNorm] at hinnerBound
    have hscale : a * ‖inner ℂ q yk‖ ≤
        2 * (‖z‖ * ‖inner ℂ q yk‖) := by
      nlinarith
    exact hscale.trans (mul_le_mul_of_nonneg_left hinnerBound (by norm_num))
  apply (tendsto_iff_norm_sub_tendsto_zero).2
  simpa only [sub_zero, mul_zero] using squeeze_zero'
    (Eventually.of_forall fun _ => norm_nonneg _) hbound
    (show Tendsto (fun c : ℝ => 2 *
        ‖indexedFullSlepianOutputMode c j -
          indexedFullMomentAlignmentCoeff c j • apertureMomentFlagVector j‖)
      L (nhds 0) by simpa using tendsto_const_nhds.mul hproj)

/-- **All-rung full indexed moment-flag theorem.** Every fixed indexed singular
output line converges projectively to the matching orthogonal polynomial moment
line, and its alignment coefficient has the exact nonzero limiting norm. -/
theorem indexedFullSlepianOutputMode_projective_flag (k : ℕ) :
    Tendsto (fun c : ℝ =>
      ‖indexedFullSlepianOutputMode c k -
        indexedFullMomentAlignmentCoeff c k • apertureMomentFlagVector k‖)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) ∧
    Tendsto (fun c : ℝ => ‖indexedFullMomentAlignmentCoeff c k‖)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds ‖apertureMomentFlagVector k‖⁻¹) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
      let L := nhdsWithin (0 : ℝ) (Ioi 0)
      have hprojSpan : Tendsto (fun c : ℝ =>
          (apertureMomentSpan k).starProjection
            (indexedFullSlepianOutputMode c k)) L (nhds 0) := by
        have hsum : Tendsto (fun c : ℝ =>
            ∑ i : {i // i ∈ Finset.range k},
              inner ℂ (apertureMomentFlagUnit (i : ℕ))
                  (indexedFullSlepianOutputMode c k) •
                apertureMomentFlagUnit (i : ℕ)) L (nhds 0) := by
          simpa only [zero_smul, Finset.sum_const_zero] using
            (tendsto_finsetSum
              (Finset.univ : Finset {i // i ∈ Finset.range k}) fun i _ =>
              (tendsto_inner_apertureMomentFlagUnit_indexedFull_of_lower
                (Finset.mem_range.mp i.2) (ih (i : ℕ) (Finset.mem_range.mp i.2)).1
                (ih (i : ℕ) (Finset.mem_range.mp i.2)).2).smul_const
                  (apertureMomentFlagUnit (i : ℕ)))
        simpa only [apertureMomentSpan_starProjection_eq_sum_flag] using hsum
      have hprojSpanNorm : Tendsto (fun c : ℝ =>
          ‖(apertureMomentSpan k).starProjection
            (indexedFullSlepianOutputMode c k)‖) L (nhds 0) := by
        simpa using hprojSpan.norm
      have hdeflated : Tendsto (fun c : ℝ =>
          ‖apertureMomentResidual k (indexedFullSlepianOutputMode c k) -
            indexedFullMomentAlignmentCoeff c k • apertureMomentFlagVector k‖)
          L (nhds 0) := by
        simpa only [apertureMomentFlagVector] using
          tendsto_indexedFullSlepianOutputMode_deflated_projective k
      have hbound : ∀ c : ℝ,
          ‖indexedFullSlepianOutputMode c k -
            indexedFullMomentAlignmentCoeff c k • apertureMomentFlagVector k‖ ≤
          ‖(apertureMomentSpan k).starProjection
            (indexedFullSlepianOutputMode c k)‖ +
          ‖apertureMomentResidual k (indexedFullSlepianOutputMode c k) -
            indexedFullMomentAlignmentCoeff c k • apertureMomentFlagVector k‖ := by
        intro c
        have hdecomp : indexedFullSlepianOutputMode c k -
              indexedFullMomentAlignmentCoeff c k • apertureMomentFlagVector k =
            (apertureMomentSpan k).starProjection
                (indexedFullSlepianOutputMode c k) +
              (apertureMomentResidual k (indexedFullSlepianOutputMode c k) -
                indexedFullMomentAlignmentCoeff c k • apertureMomentFlagVector k) := by
          rw [apertureMomentResidual_apply]
          abel
        rw [hdecomp]
        exact norm_add_le _ _
      have hfull : Tendsto (fun c : ℝ =>
          ‖indexedFullSlepianOutputMode c k -
            indexedFullMomentAlignmentCoeff c k • apertureMomentFlagVector k‖)
          L (nhds 0) := by
        refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
          (Eventually.of_forall hbound) ?_
        simpa only [zero_add] using hprojSpanNorm.add hdeflated
      exact ⟨hfull,
        tendsto_norm_indexedFullMomentAlignmentCoeff_of_projective k hfull⟩

end GaloisForLFunctions.RHTower
