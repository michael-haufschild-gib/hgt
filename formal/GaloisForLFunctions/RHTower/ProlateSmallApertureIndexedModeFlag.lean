import GaloisForLFunctions.RHTower.ProlateSmallApertureIndexedSpectrum
import GaloisForLFunctions.RHTower.ProlateSmallApertureSpectralLowerBound

/-!
# Indexed small-aperture Slepian mode flag

The sharp indexed birth law is upgraded from eigenvalues to actual singular
lines.  Canonical greedy input modes produce unit, mutually orthogonal output
modes of the rectangular aperture synthesis.  After deleting all moments below
degree `2n`, the actual `n`th output mode converges projectively to the nonzero
orthogonal residual of `x^(2n)`.  The lower singular-value birth bound is the
essential noncollapse input; no compactness choice or spectral relabelling is
assumed.

This is the first operator-level identification of the indexed Slepian branch
with its small-aperture moment flag.  It is the induction seed for the missing
all-rung Legendre/separation anchor.
-/

open MeasureTheory Filter Topology Set Complex

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry
open _root_.RHTower

/-- Positivity of every indexed even Slepian value at arbitrary positive bandwidth. -/
theorem complexUnitBandEvenValue_pos_of_pos
    {c : ℝ} (hc : 0 < c) (n : ℕ) :
    0 < complexUnitBandEvenValue c n := by
  let a : ℝ := Real.sqrt (c / (2 * Real.pi))
  have hden : 0 < 2 * Real.pi := by positivity
  have hquot : 0 < c / (2 * Real.pi) := div_pos hc hden
  have ha : 0 < a := Real.sqrt_pos.2 hquot
  have haSq : a ^ 2 = c / (2 * Real.pi) := by
    dsimp only [a]
    exact Real.sq_sqrt hquot.le
  have hband : 2 * Real.pi * a ^ 2 = c := by
    rw [haSq]
    field_simp
  simpa only [hband] using complexUnitBandEvenValue_pos ha n

/-- Canonical greedy input vector of the indexed even Slepian block. -/
noncomputable def indexedEvenSlepianInputMode (c : ℝ) (n : ℕ) :
    complexUnitBandEvenSubspace :=
  ContinuousLinearMap.sgVec (complexUnitBandEvenBlock c) n

/-- Rectangular singular value of the even aperture synthesis. -/
noncomputable def indexedEvenSlepianSingularValue (c : ℝ) (n : ℕ) : ℝ :=
  rectApproxNumber (complexEvenApertureMomentSynthesis c) n

theorem indexedEvenSlepianInputMode_norm
    {c : ℝ} (hc : 0 < c) (n : ℕ) :
    ‖indexedEvenSlepianInputMode c n‖ = 1 := by
  let S := complexUnitBandEvenBlock c
  have hval : 0 < complexUnitBandEvenValue c n :=
    complexUnitBandEvenValue_pos_of_pos hc n
  rcases ContinuousLinearMap.norm_sgVec_zero_or_one S n with hzero | hone
  · have hdead := ContinuousLinearMap.sgVal_zero_of_dead (S := S) (n := n) hzero
    have heq := complexUnitBandEvenValue_eq_sgVal hc n
    linarith
  · exact hone

theorem indexedEvenSlepianSingularValue_pos
    {c : ℝ} (hc : 0 < c) (n : ℕ) :
    0 < indexedEvenSlepianSingularValue c n := by
  have hsq := rectApproxNumber_complexEven_sq_eq_scaled_evenValue hc n
  have hval := complexUnitBandEvenValue_pos_of_pos hc n
  have hscale : 0 < 2 * Real.pi / c := div_pos (by positivity) hc
  have hnonneg : 0 ≤ indexedEvenSlepianSingularValue c n :=
    rectApproxNumber_nonneg _ _
  dsimp only [indexedEvenSlepianSingularValue] at hnonneg ⊢
  nlinarith

theorem indexedEvenSlepianInputMode_eigen
    {c : ℝ} (hc : 0 < c) (n : ℕ) :
    complexUnitBandEvenBlock c (indexedEvenSlepianInputMode c n) =
      (complexUnitBandEvenValue c n : ℂ) • indexedEvenSlepianInputMode c n := by
  unfold indexedEvenSlepianInputMode
  rw [ContinuousLinearMap.apply_sgVec,
    ← complexUnitBandEvenValue_eq_sgVal hc n]

/-- Unit output singular mode of the rectangular even synthesis. -/
noncomputable def indexedEvenSlepianOutputMode (c : ℝ) (n : ℕ) :
    UnitApertureL2 :=
  ((indexedEvenSlepianSingularValue c n : ℝ) : ℂ)⁻¹ •
    complexEvenApertureMomentSynthesis c (indexedEvenSlepianInputMode c n)

theorem norm_complexEvenApertureMomentSynthesis_inputMode_sq
    {c : ℝ} (hc : 0 < c) (n : ℕ) :
    ‖complexEvenApertureMomentSynthesis c (indexedEvenSlepianInputMode c n)‖ ^ 2 =
      indexedEvenSlepianSingularValue c n ^ 2 := by
  let T := complexEvenApertureMomentSynthesis c
  let x := indexedEvenSlepianInputMode c n
  rw [ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right]
  have hgram := adjoint_comp_complexEvenApertureMomentSynthesis_eq_evenBlock hc.ne'
  have heig := indexedEvenSlepianInputMode_eigen hc n
  have hxnorm := indexedEvenSlepianInputMode_norm hc n
  have hsq := rectApproxNumber_complexEven_sq_eq_scaled_evenValue hc n
  change Complex.re (inner ℂ x ((ContinuousLinearMap.adjoint T ∘L T) x)) = _
  rw [hgram, smul_apply, heig, smul_smul,
    inner_smul_right, inner_self_eq_norm_sq_to_K, hxnorm]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero]
  norm_num
  simpa only [x, T, indexedEvenSlepianSingularValue] using hsq.symm

theorem indexedEvenSlepianOutputMode_norm
    {c : ℝ} (hc : 0 < c) (n : ℕ) :
    ‖indexedEvenSlepianOutputMode c n‖ = 1 := by
  have hspos := indexedEvenSlepianSingularValue_pos hc n
  have hsne := ne_of_gt hspos
  have hsq := norm_complexEvenApertureMomentSynthesis_inputMode_sq hc n
  have hnorm :
      ‖complexEvenApertureMomentSynthesis c (indexedEvenSlepianInputMode c n)‖ =
        indexedEvenSlepianSingularValue c n := by
    nlinarith [norm_nonneg
      (complexEvenApertureMomentSynthesis c (indexedEvenSlepianInputMode c n))]
  rw [indexedEvenSlepianOutputMode, norm_smul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hspos, hnorm, inv_mul_cancel₀ hsne]

theorem complexEvenApertureMomentSynthesis_inputMode_eq_smul_output
    {c : ℝ} (hc : 0 < c) (n : ℕ) :
    complexEvenApertureMomentSynthesis c (indexedEvenSlepianInputMode c n) =
      (indexedEvenSlepianSingularValue c n : ℂ) •
        indexedEvenSlepianOutputMode c n := by
  rw [indexedEvenSlepianOutputMode, smul_smul]
  have hsne : (indexedEvenSlepianSingularValue c n : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (indexedEvenSlepianSingularValue_pos hc n)
  rw [mul_inv_cancel₀ hsne, one_smul]

theorem indexedEvenSlepianOutputMode_orthogonal_of_ne
    {c : ℝ} (hc : 0 < c) {m n : ℕ} (hmn : m ≠ n) :
    inner ℂ (indexedEvenSlepianOutputMode c m)
      (indexedEvenSlepianOutputMode c n) = 0 := by
  let T := complexEvenApertureMomentSynthesis c
  let S := complexUnitBandEvenBlock c
  let xm := indexedEvenSlepianInputMode c m
  let xn := indexedEvenSlepianInputMode c n
  have horth : inner ℂ xm xn = 0 := by
    exact ContinuousLinearMap.inner_sgVec_sgVec_of_ne S hmn
  have hgram := adjoint_comp_complexEvenApertureMomentSynthesis_eq_evenBlock hc.ne'
  have heig := indexedEvenSlepianInputMode_eigen hc n
  have hTorth : inner ℂ (T xm) (T xn) = 0 := by
    rw [← ContinuousLinearMap.adjoint_inner_right]
    change inner ℂ xm ((ContinuousLinearMap.adjoint T ∘L T) xn) = 0
    rw [hgram, smul_apply, heig, smul_smul, inner_smul_right, horth, mul_zero]
  rw [indexedEvenSlepianOutputMode, indexedEvenSlepianOutputMode,
    inner_smul_left, inner_smul_right]
  change _ * (_ * inner ℂ (T xm) (T xn)) = 0
  rw [hTorth, mul_zero, mul_zero]

/-- Scalar comparing the indexed output mode with the leading orthogonal
moment residual at its birth order. -/
noncomputable def indexedEvenMomentAlignmentCoeff (c : ℝ) (n : ℕ) : ℂ :=
  ((c ^ (2 * n) / indexedEvenSlepianSingularValue c n : ℝ) : ℂ) *
    inner ℂ (physicalComplexMonomialL2 (2 * n))
      ((indexedEvenSlepianInputMode c n : complexUnitBandEvenSubspace) :
        UnitPhysicalScalarL2)

theorem apertureMomentResidual_outputMode_sub_alignmentCoeff
    {c : ℝ} (hc : 0 < c) (n : ℕ) :
    apertureMomentResidual (2 * n) (indexedEvenSlepianOutputMode c n) -
        indexedEvenMomentAlignmentCoeff c n •
          fourierGroundVector 1 (apertureMomentResidual (2 * n)) (2 * n) =
      ((c ^ (2 * n) / indexedEvenSlepianSingularValue c n : ℝ) : ℂ) •
        ((normalizedApertureMomentSynthesis (2 * n) c -
            apertureMomentLeadingSynthesis (2 * n))
          ((indexedEvenSlepianInputMode c n : complexUnitBandEvenSubspace) :
            UnitPhysicalScalarL2)) := by
  let k := 2 * n
  let s := indexedEvenSlepianSingularValue c n
  let x := indexedEvenSlepianInputMode c n
  let q := fourierGroundVector 1 (apertureMomentResidual k) k
  have hs : s ≠ 0 := ne_of_gt (indexedEvenSlepianSingularValue_pos hc n)
  have hc0 : c ^ k ≠ 0 := pow_ne_zero k hc.ne'
  have hPT : apertureMomentResidual k
      (complexEvenApertureMomentSynthesis c x) =
        apertureMomentFourierSynthesis k c
          ((x : complexUnitBandEvenSubspace) : UnitPhysicalScalarL2) := by
    rw [complexEvenApertureMomentSynthesis, ContinuousLinearMap.comp_apply]
    exact congrArg
      (fun A : UnitPhysicalScalarL2 →L[ℂ] UnitApertureL2 =>
        A ((x : complexUnitBandEvenSubspace) : UnitPhysicalScalarL2))
      (apertureMomentFourierSynthesis_eq_residual_comp k c).symm
  have hlead : apertureMomentLeadingSynthesis k
      ((x : complexUnitBandEvenSubspace) : UnitPhysicalScalarL2) =
        inner ℂ (physicalComplexMonomialL2 k)
          ((x : complexUnitBandEvenSubspace) : UnitPhysicalScalarL2) • q := by
    exact apertureMomentLeadingSynthesis_apply k _
  rw [indexedEvenSlepianOutputMode, map_smul, hPT]
  change ((s : ℂ)⁻¹ • apertureMomentFourierSynthesis k c
      ((x : complexUnitBandEvenSubspace) : UnitPhysicalScalarL2)) -
    ((((c ^ k / s : ℝ) : ℂ) * inner ℂ (physicalComplexMonomialL2 k)
      ((x : complexUnitBandEvenSubspace) : UnitPhysicalScalarL2)) • q) = _
  rw [sub_apply, normalizedApertureMomentSynthesis, smul_apply, hlead]
  change ((s : ℂ)⁻¹ • apertureMomentFourierSynthesis k c
      ((x : complexUnitBandEvenSubspace) : UnitPhysicalScalarL2)) -
    ((((c ^ k / s : ℝ) : ℂ) * inner ℂ (physicalComplexMonomialL2 k)
      ((x : complexUnitBandEvenSubspace) : UnitPhysicalScalarL2)) • q) =
    ((c ^ k / s : ℝ) : ℂ) •
      ((((c ^ k)⁻¹ : ℝ) : ℂ) • apertureMomentFourierSynthesis k c
          ((x : complexUnitBandEvenSubspace) : UnitPhysicalScalarL2) -
        inner ℂ (physicalComplexMonomialL2 k)
          ((x : complexUnitBandEvenSubspace) : UnitPhysicalScalarL2) • q)
  rw [smul_sub, smul_smul, smul_smul]
  have hcast : (((c ^ k)⁻¹ : ℝ) : ℂ) = ((c ^ k : ℂ)⁻¹) := by norm_cast
  rw [hcast]
  apply sub_left_inj.mpr
  congr 1
  field_simp [hs, hc.ne']
  norm_cast
  field_simp [hs]

/-- The deflated actual `n`th output line converges to the nonzero degree-`2n`
orthogonal moment line.  No compactness or eigenline identification is assumed:
the sharp indexed singular-value lower birth law prevents projective collapse. -/
theorem tendsto_indexedEvenSlepianOutputMode_deflated_projective (n : ℕ) :
    Tendsto (fun c : ℝ =>
      ‖apertureMomentResidual (2 * n) (indexedEvenSlepianOutputMode c n) -
        indexedEvenMomentAlignmentCoeff c n •
          fourierGroundVector 1 (apertureMomentResidual (2 * n)) (2 * n)‖)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
  let k := 2 * n
  let L := nhdsWithin (0 : ℝ) (Ioi 0)
  have hLpunct : L ≤ 𝓝[≠] (0 : ℝ) := by
    exact nhdsWithin_mono 0 (by intro c hc; exact ne_of_gt hc)
  have hop : Tendsto (fun c : ℝ =>
      ‖normalizedApertureMomentSynthesis k c -
        apertureMomentLeadingSynthesis k‖) L (nhds 0) :=
    ((tendsto_iff_norm_sub_tendsto_zero).mp
      (tendsto_normalizedApertureMomentSynthesis k)).mono_left hLpunct
  have herr : Tendsto (fun c : ℝ =>
      ‖(normalizedApertureMomentSynthesis k c -
          apertureMomentLeadingSynthesis k)
        ((indexedEvenSlepianInputMode c n : complexUnitBandEvenSubspace) :
          UnitPhysicalScalarL2)‖) L (nhds 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hop
    filter_upwards [self_mem_nhdsWithin] with c hc
    have hcpos : 0 < c := hc
    calc
      ‖(normalizedApertureMomentSynthesis k c -
          apertureMomentLeadingSynthesis k)
        ((indexedEvenSlepianInputMode c n : complexUnitBandEvenSubspace) :
          UnitPhysicalScalarL2)‖ ≤
          ‖normalizedApertureMomentSynthesis k c -
            apertureMomentLeadingSynthesis k‖ *
            ‖indexedEvenSlepianInputMode c n‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ = ‖normalizedApertureMomentSynthesis k c -
            apertureMomentLeadingSynthesis k‖ := by
        rw [indexedEvenSlepianInputMode_norm hcpos n, mul_one]
  obtain ⟨C, hC, hlower⟩ :=
    exists_pos_eventually_rectApproxNumber_complexEven_lower n
  have hlowerL : ∀ᶠ c : ℝ in L,
      C * c ^ k ≤ indexedEvenSlepianSingularValue c n := by
    filter_upwards [hlower.filter_mono hLpunct, self_mem_nhdsWithin]
      with c hclower hc
    have hcpos : 0 < c := hc
    have habs : |c| = c := abs_of_pos hcpos
    simpa only [k, indexedEvenSlepianSingularValue, habs] using hclower
  have hratio : ∀ᶠ c : ℝ in L,
      |c ^ k / indexedEvenSlepianSingularValue c n| ≤ C⁻¹ := by
    filter_upwards [hlowerL, self_mem_nhdsWithin] with c hclower hc
    have hcpos : 0 < c := hc
    have hspos := indexedEvenSlepianSingularValue_pos hcpos n
    have hpow : 0 ≤ c ^ k := pow_nonneg hcpos.le k
    rw [abs_of_nonneg (div_nonneg hpow hspos.le), div_le_iff₀ hspos]
    rw [inv_mul_eq_div]
    exact (le_div_iff₀ hC).2 (by simpa [mul_comm] using hclower)
  have hbound : ∀ᶠ c : ℝ in L,
      ‖apertureMomentResidual (2 * n) (indexedEvenSlepianOutputMode c n) -
        indexedEvenMomentAlignmentCoeff c n •
          fourierGroundVector 1 (apertureMomentResidual (2 * n)) (2 * n)‖ ≤
        C⁻¹ * ‖(normalizedApertureMomentSynthesis k c -
          apertureMomentLeadingSynthesis k)
        ((indexedEvenSlepianInputMode c n : complexUnitBandEvenSubspace) :
          UnitPhysicalScalarL2)‖ := by
    filter_upwards [hratio, self_mem_nhdsWithin] with c hratio hc
    have hcpos : 0 < c := hc
    rw [apertureMomentResidual_outputMode_sub_alignmentCoeff hcpos n,
      norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hratio (norm_nonneg _)
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) hbound ?_
  have hlast : Tendsto (fun c : ℝ => C⁻¹ *
      ‖(normalizedApertureMomentSynthesis k c -
          apertureMomentLeadingSynthesis k)
        ((indexedEvenSlepianInputMode c n : complexUnitBandEvenSubspace) :
          UnitPhysicalScalarL2)‖) L (nhds (C⁻¹ * 0)) :=
    tendsto_const_nhds.mul herr
  simpa [L] using hlast

/-- Ground indexed output line converges projectively to the constant moment
line.  This is the base case for hierarchical removal of lower moment lines. -/
theorem tendsto_indexedEvenSlepianOutputMode_zero_projective :
    Tendsto (fun c : ℝ =>
      ‖indexedEvenSlepianOutputMode c 0 -
        indexedEvenMomentAlignmentCoeff c 0 •
          fourierGroundVector 1 (apertureMomentResidual 0) 0‖)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds 0) := by
  simpa only [Nat.mul_zero, apertureMomentResidual_zero,
    ContinuousLinearMap.id_apply] using
    tendsto_indexedEvenSlepianOutputMode_deflated_projective 0

/-- Ground alignment coefficient cannot collapse: its norm converges to the
inverse norm of the constant residual. -/
theorem tendsto_norm_indexedEvenMomentAlignmentCoeff_zero :
    Tendsto (fun c : ℝ => ‖indexedEvenMomentAlignmentCoeff c 0‖)
      (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds ‖fourierGroundVector 1 (apertureMomentResidual 0) 0‖⁻¹) := by
  let L := nhdsWithin (0 : ℝ) (Ioi 0)
  let q := fourierGroundVector 1 (apertureMomentResidual 0) 0
  have hq : q ≠ 0 := fourierGroundVector_apertureMomentResidual_ne_zero 0
  have hdiff := tendsto_indexedEvenSlepianOutputMode_zero_projective
  have habs : Tendsto (fun c : ℝ =>
      |‖indexedEvenMomentAlignmentCoeff c 0 • q‖ - 1|) L (nhds 0) := by
    refine squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _) ?_ hdiff
    filter_upwards [self_mem_nhdsWithin] with c hc
    have hcpos : 0 < c := hc
    calc
      |‖indexedEvenMomentAlignmentCoeff c 0 • q‖ - 1| =
          |‖indexedEvenMomentAlignmentCoeff c 0 • q‖ -
            ‖indexedEvenSlepianOutputMode c 0‖| := by
        rw [indexedEvenSlepianOutputMode_norm hcpos 0]
      _ ≤ ‖indexedEvenMomentAlignmentCoeff c 0 • q -
          indexedEvenSlepianOutputMode c 0‖ :=
        abs_norm_sub_norm_le _ _
      _ = ‖indexedEvenSlepianOutputMode c 0 -
          indexedEvenMomentAlignmentCoeff c 0 • q‖ := norm_sub_rev _ _
  have hnorm : Tendsto (fun c : ℝ =>
      ‖indexedEvenMomentAlignmentCoeff c 0 • q‖) L (nhds 1) := by
    apply (tendsto_iff_norm_sub_tendsto_zero).2
    simpa only [Real.norm_eq_abs] using habs
  have hdiv := hnorm.div_const ‖q‖
  have hqnorm : ‖q‖ ≠ 0 := norm_ne_zero_iff.mpr hq
  simpa only [L, q, norm_smul, div_eq_mul_inv, mul_assoc,
    mul_inv_cancel₀ hqnorm, mul_one, one_mul] using hdiv

end GaloisForLFunctions.RHTower
