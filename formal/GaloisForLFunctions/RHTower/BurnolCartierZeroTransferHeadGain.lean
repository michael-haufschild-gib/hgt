import GaloisForLFunctions.RHTower.BurnolReflectedCoShiftCartierContinuation

/-!
# Burnol Cartier zero-transfer and fixed-head gain

Constructs canonical isometric zero-transfer for Burnol divided shift. At right-half Xi divisors,
its value on fixed co-Poisson atom lands in literal extended Sonin source. Both aperture heads are
computed exactly. Their gains are reciprocal, and forward gain has norm one exactly on critical
line. This reduces prior global sewing producer to conservation of one explicit local source
coefficient. No such conservation law is assumed or proved here.
-/

open Complex Real MeasureTheory Set Filter Topology
open scoped ENNReal InnerProductSpace ComplexConjugate

noncomputable section

namespace RHTower


theorem norm_sub_centered_burnolMellinDividedShift
    {rho : ℂ} (h : 1 / 2 < rho.re) (f : evenSubspace) :
    ‖f - (((2 * (rho.re - 1 / 2) : ℝ) : ℂ) •
      burnolMellinDividedShift h f)‖ = ‖f‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  rw [norm_sub_sq (𝕜 := ℂ), norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by linarith : 0 ≤ 2 * (rho.re - 1 / 2))]
  have hinner :
      RCLike.re (inner ℂ f (((2 * (rho.re - 1 / 2) : ℝ) : ℂ) •
        burnolMellinDividedShift h f)) =
        (2 * (rho.re - 1 / 2)) *
          (inner ℂ f (burnolMellinDividedShift h f)).re := by
    change (inner ℂ f (((2 * (rho.re - 1 / 2) : ℝ) : ℂ) •
        burnolMellinDividedShift h f)).re = _
    rw [inner_smul_right f (burnolMellinDividedShift h f)
      (((2 * (rho.re - 1 / 2) : ℝ) : ℂ))]
    simp
  rw [hinner]
  have hacc := re_inner_burnolMellinDividedShift_eq h f
  nlinarith

def BurnolSoninHeadEquals (a : ℝ) (f : evenSubspace) (c : ℂ) : Prop :=
  ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) a)),
    (((f : evenSubspace) : SoninL2) : ℝ → ℂ) t = c

theorem BurnolSoninHeadEquals.sub {a : ℝ} {f g : evenSubspace} {c d : ℂ}
    (hf : BurnolSoninHeadEquals a f c) (hg : BurnolSoninHeadEquals a g d) :
    BurnolSoninHeadEquals a (f - g) (c - d) := by
  filter_upwards [hf, hg, ae_restrict_of_ae (Lp.coeFn_sub
    ((f : evenSubspace) : SoninL2) ((g : evenSubspace) : SoninL2))] with t hft hgt hsub
  change ((((((f : evenSubspace) : SoninL2) - ((g : evenSubspace) : SoninL2)) :
    SoninL2) : ℝ → ℂ) t) = c - d
  rw [hsub, Pi.sub_apply, hft, hgt]

theorem BurnolSoninHeadEquals.smul {a : ℝ} {f : evenSubspace} {c lambda : ℂ}
    (hf : BurnolSoninHeadEquals a f c) : BurnolSoninHeadEquals a (lambda • f) (lambda * c) := by
  filter_upwards [hf, ae_restrict_of_ae
    (Lp.coeFn_smul lambda ((f : evenSubspace) : SoninL2))] with t hft hsmul
  change (((((lambda • ((f : evenSubspace) : SoninL2) : SoninL2)) :
    SoninL2) : ℝ → ℂ) t) = lambda * c
  rw [hsmul, Pi.smul_apply, hft, smul_eq_mul]

/-- The canonical Blaschke zero-transfer attached to the right-half Cauchy shift. -/
def burnolCartierZeroTransfer {rho : ℂ} (h : 1 / 2 < rho.re) :
    evenSubspace →ₗᵢ[ℂ] evenSubspace where
  toLinearMap :=
    LinearMap.id - (((2 * (rho.re - 1 / 2) : ℝ) : ℂ) •
      (burnolMellinDividedShift h).toLinearMap)
  norm_map' f := by
    change ‖f - (((2 * (rho.re - 1 / 2) : ℝ) : ℂ) •
      burnolMellinDividedShift h f)‖ = ‖f‖
    exact norm_sub_centered_burnolMellinDividedShift h f

@[simp] theorem burnolCartierZeroTransfer_apply {rho : ℂ} (h : 1 / 2 < rho.re)
    (f : evenSubspace) :
    burnolCartierZeroTransfer h f =
      f - (((2 * (rho.re - 1 / 2) : ℝ) : ℂ) • burnolMellinDividedShift h f) := rfl

theorem burnolFixedSubWindowSourceAtom_head :
    BurnolSoninHeadEquals (1 / 2) burnolFixedSubWindowSourceAtom (-1) := by
  filter_upwards [ae_restrict_of_ae
      (coPoissonSubWindowEven_coeFn (c := (1 / 2 : ℝ)) (d := 1)
        (by norm_num) (by norm_num)),
    ae_restrict_mem measurableSet_Ioo] with t hcoe ht
  have hcoe' :
      (((burnolFixedSubWindowSourceAtom : evenSubspace) : SoninL2) : ℝ → ℂ) t =
        burnolCoPoissonRightSum (coPoissonSubWindowSeed (1 / 2 : ℝ) 1) t := by
    simpa [burnolFixedSubWindowSourceAtom] using hcoe
  rw [hcoe',
    burnolCoPoissonRightSum_coPoissonSubWindowSeed_eq_const
      (c := (1 / 2 : ℝ)) (d := 1) (by norm_num) (by norm_num) ht.1 ht.2]
  norm_num

theorem coPoissonReciprocal_fixedSubWindow_correction :
    coPoissonCorrectionConstant
        (coPoissonReciprocalSeed (coPoissonSubWindowSeed (1 / 2 : ℝ) 1)) =
      (Real.log 2 : ℂ) := by
  rw [coPoissonReciprocalSeed_subWindow_eq (c := (1 / 2 : ℝ)) (d := 1)
    (by norm_num) (by norm_num)]
  norm_num only [inv_one, one_div]
  rw [
    coPoissonCorrectionConstant_coPoissonWindowIndicatorSeed
      (c := (1 : ℝ)) (d := 2) (by norm_num) (by norm_num),
    Real.log_one, sub_zero]

theorem soninCosineUnitary_burnolFixedSubWindowSourceAtom_head :
    BurnolSoninHeadEquals (1 / 2)
      (soninCosineUnitary burnolFixedSubWindowSourceAtom) (-(Real.log 2 : ℂ)) := by
  filter_upwards [ae_restrict_of_ae
      (coeFn_soninCosineUnitary_coPoissonSubWindowEven
        (c := (1 / 2 : ℝ)) (d := 1) (by norm_num) (by norm_num)),
    ae_restrict_mem measurableSet_Ioo] with t hcoe ht
  have hcoe' :
      (((soninCosineUnitary burnolFixedSubWindowSourceAtom : evenSubspace) : SoninL2) :
        ℝ → ℂ) t =
        burnolCoPoissonRightSum
          (coPoissonReciprocalSeed (coPoissonSubWindowSeed (1 / 2 : ℝ) 1)) t := by
    simpa [burnolFixedSubWindowSourceAtom] using hcoe
  rw [hcoe']
  have hconst := burnolCoPoissonRightSum_eq_const
    (support_reciprocal_subWindow_symmetric
      (c := (1 / 2 : ℝ)) (d := 1) (by norm_num) (by norm_num))
    (t := t) (by
      rw [abs_of_pos ht.1, subWindowAperture]
      have ht1 : t < 1 := lt_trans ht.2 (by norm_num)
      exact lt_min ht.2 (by simpa using ht1))
  rw [hconst]
  change -coPoissonCorrectionConstant
      (coPoissonReciprocalSeed (coPoissonSubWindowSeed (1 / 2 : ℝ) 1)) = _
  rw [coPoissonReciprocal_fixedSubWindow_correction]

theorem xiDivisor_re_lt_one_of_half_lt (rho : XiDivisorSupport)
    (h : 1 / 2 < (rho : ℂ).re) : (rho : ℂ).re < 1 := by
  have hxi : xi (rho : ℂ) = 0 := xi_eq_zero_of_mem_divisor_support rho
  have hrhoOne : (rho : ℂ) ≠ 1 := by
    intro hrho
    rw [hrho, xi_one] at hxi
    norm_num at hxi
  have hzeta : riemannZeta (rho : ℂ) = 0 :=
    (xi_eq_zero_iff (by linarith) hrhoOne).mp hxi
  exact riemannZeta_zero_re_lt_one hzeta

theorem xiDivisor_fixedSubWindowSourceAtom_mellin_eq_zero
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    (∫ s in Ioi (0 : ℝ),
      (((burnolFixedSubWindowSourceAtom : evenSubspace) : SoninL2) : ℝ → ℂ) s *
        soninMellinKernel (rho : ℂ) s) = 0 := by
  have hxi : xi (rho : ℂ) = 0 := xi_eq_zero_of_mem_divisor_support rho
  have hrhoOne : (rho : ℂ) ≠ 1 := by
    intro hrho
    rw [hrho, xi_one] at hxi
    norm_num at hxi
  have hzeta : riemannZeta (rho : ℂ) = 0 :=
    (xi_eq_zero_iff (by linarith) hrhoOne).mp hxi
  have hvalue := soninMellinEvaluation_coPoissonSubWindowSonin_eq_zero
    (c := (1 / 2 : ℝ)) (d := 1) (by norm_num) (by norm_num)
    (by linarith) hzeta
  rw [soninMellinEvaluation] at hvalue
  exact (mul_eq_zero.mp hvalue).resolve_left
    (mellinCompletionFactor_ne_zero (by linarith))

theorem xiDivisor_burnolMellinDividedShift_fixed_head
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    BurnolSoninHeadEquals (1 / 2)
      (burnolMellinDividedShift h burnolFixedSubWindowSourceAtom)
      ((1 - (rho : ℂ))⁻¹) := by
  have hhead : ∀ᵐ s ∂volume, s ∈ Ioo (0 : ℝ) (1 / 2) →
      (((burnolFixedSubWindowSourceAtom : evenSubspace) : SoninL2) : ℝ → ℂ) s = -1 := by
    rw [← ae_restrict_iff' measurableSet_Ioo]
    exact burnolFixedSubWindowSourceAtom_head
  have hint : IntegrableOn (fun s : ℝ =>
      (((burnolFixedSubWindowSourceAtom : evenSubspace) : SoninL2) : ℝ → ℂ) s *
        ((s : ℂ) ^ (-(rho : ℂ)))) (Ioi (0 : ℝ)) volume :=
    integrableOn_extendedSonin_mul_mellinKernel h (xiDivisor_re_lt_one_of_half_lt rho h)
      (by norm_num [subWindowAperture])
      (coPoissonSubWindowSonin (c := (1 / 2 : ℝ)) (d := 1)
        (by norm_num) (by norm_num))
  have hraw := xiDivisor_fixedSubWindowSourceAtom_mellin_eq_zero rho h
  change (∫ s in Ioi (0 : ℝ),
      (((burnolFixedSubWindowSourceAtom : evenSubspace) : SoninL2) : ℝ → ℂ) s *
        ((s : ℂ) ^ (-(rho : ℂ)))) = 0 at hraw
  have hshift : BurnolSoninHeadEquals (1 / 2)
      (burnolShift (rho : ℂ) burnolFixedSubWindowSourceAtom) ((1 - (rho : ℂ))⁻¹) := by
    filter_upwards [ae_restrict_of_ae
        (coe_burnolShift_ae h burnolFixedSubWindowSourceAtom),
      ae_restrict_mem measurableSet_Ioo] with t hcoe ht
    rw [hcoe, burnolShiftFun_head_eq h (xiDivisor_re_lt_one_of_half_lt rho h) (by norm_num)
      burnolFixedSubWindowSourceAtom hhead hint hraw ht.1 ht.2]
    ring
  rwa [burnolShift_eq_burnolMellinDividedShift h] at hshift

theorem xiDivisor_burnolMellinDividedShift_fixed_cosine_head
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    BurnolSoninHeadEquals (1 / 2)
      (soninCosineUnitary
        (burnolMellinDividedShift h burnolFixedSubWindowSourceAtom))
      (-(Real.log 2 : ℂ) / (rho : ℂ)) := by
  have hhead : ∀ᵐ s ∂volume, s ∈ Ioo (0 : ℝ) (1 / 2) →
      (((soninCosineUnitary burnolFixedSubWindowSourceAtom : evenSubspace) : SoninL2) :
        ℝ → ℂ) s = -(Real.log 2 : ℂ) := by
    rw [← ae_restrict_iff' measurableSet_Ioo]
    exact soninCosineUnitary_burnolFixedSubWindowSourceAtom_head
  have hcoshift : BurnolSoninHeadEquals (1 / 2)
      (soninCosineUnitary (burnolShift (rho : ℂ) burnolFixedSubWindowSourceAtom))
      (-(Real.log 2 : ℂ) / (rho : ℂ)) := by
    rw [soninCosineUnitary_burnolShift h]
    filter_upwards [ae_restrict_of_ae
        (coe_burnolCoShift_ae h (soninCosineUnitary burnolFixedSubWindowSourceAtom)),
      ae_restrict_mem measurableSet_Ioo] with t hcoe ht
    rw [hcoe, burnolCoShiftFun_head_eq h (by norm_num)
      (soninCosineUnitary burnolFixedSubWindowSourceAtom) hhead ht.1 ht.2]
  rwa [burnolShift_eq_burnolMellinDividedShift h] at hcoshift

def burnolCartierForwardHeadGain (rho : ℂ) : ℂ := conj rho / (1 - rho)

def burnolCartierCosineHeadGain (rho : ℂ) : ℂ := (1 - conj rho) / rho

theorem burnol_cartier_center_eq (rho : ℂ) :
    (((2 * (rho.re - 1 / 2) : ℝ) : ℂ)) = rho + conj rho - 1 := by
  apply Complex.ext
  · simp
    ring
  · simp

theorem xiDivisor_burnolCartierZeroTransfer_fixed_head
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    BurnolSoninHeadEquals (1 / 2)
      (burnolCartierZeroTransfer h burnolFixedSubWindowSourceAtom)
      (-burnolCartierForwardHeadGain (rho : ℂ)) := by
  rw [burnolCartierZeroTransfer_apply]
  have hhead := burnolFixedSubWindowSourceAtom_head.sub
    ((xiDivisor_burnolMellinDividedShift_fixed_head rho h).smul
      (lambda := (((2 * ((rho : ℂ).re - 1 / 2) : ℝ) : ℂ))))
  convert hhead using 1
  rw [burnol_cartier_center_eq]
  unfold burnolCartierForwardHeadGain
  have hne : (1 : ℂ) - (rho : ℂ) ≠ 0 := by
    intro hzero
    have hrho : (rho : ℂ) = 1 := by linear_combination -hzero
    have hlt := xiDivisor_re_lt_one_of_half_lt rho h
    rw [hrho] at hlt
    norm_num at hlt
  field_simp
  ring

theorem xiDivisor_burnolCartierZeroTransfer_fixed_cosine_head
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    BurnolSoninHeadEquals (1 / 2)
      (soninCosineUnitary (burnolCartierZeroTransfer h burnolFixedSubWindowSourceAtom))
      (-(Real.log 2 : ℂ) * burnolCartierCosineHeadGain (rho : ℂ)) := by
  rw [burnolCartierZeroTransfer_apply, map_sub, map_smul]
  have hhead := soninCosineUnitary_burnolFixedSubWindowSourceAtom_head.sub
    ((xiDivisor_burnolMellinDividedShift_fixed_cosine_head rho h).smul
      (lambda := (((2 * ((rho : ℂ).re - 1 / 2) : ℝ) : ℂ))))
  convert hhead using 1
  rw [burnol_cartier_center_eq]
  unfold burnolCartierCosineHeadGain
  have hne : (rho : ℂ) ≠ 0 := by
    intro hzero
    rw [hzero] at h
    norm_num at h
  field_simp
  ring

theorem norm_burnolCartierForwardHeadGain_eq_one_iff
    {rho : ℂ} (hlt : rho.re < 1) :
    ‖burnolCartierForwardHeadGain rho‖ = 1 ↔ rho.re = 1 / 2 := by
  have hrhoOne : rho ≠ 1 := by
    intro hrho
    rw [hrho] at hlt
    norm_num at hlt
  have hden : ‖(1 : ℂ) - rho‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hrhoOne.symm)
  unfold burnolCartierForwardHeadGain
  rw [norm_div, norm_conj]
  constructor
  · intro hnorm
    rw [div_eq_iff hden] at hnorm
    simp only [one_mul] at hnorm
    have hsq := congrArg (fun x : ℝ => x ^ 2) hnorm
    rw [Complex.sq_norm, Complex.sq_norm] at hsq
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im] at hsq
    nlinarith
  · intro hre
    field_simp
    rw [← sq_eq_sq₀ (norm_nonneg rho) (norm_nonneg ((1 : ℂ) - rho)),
      Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im]
    nlinarith

theorem burnolCartierCosineHeadGain_eq_inv_conj_forwardHeadGain
    {rho : ℂ} (hzero : rho ≠ 0) :
    burnolCartierCosineHeadGain rho = (conj (burnolCartierForwardHeadGain rho))⁻¹ := by
  unfold burnolCartierCosineHeadGain burnolCartierForwardHeadGain
  rw [map_div₀]
  simp only [map_sub, map_one, Complex.conj_conj]
  field_simp [hzero]

theorem xiDivisor_burnolCartierZeroTransfer_mem_soninExtendedSpace
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    burnolCartierZeroTransfer h burnolFixedSubWindowSourceAtom ∈
      soninExtendedSpace (subWindowAperture (1 / 2) 1) := by
  have hfixed : burnolFixedSubWindowSourceAtom ∈
      soninExtendedSpace (subWindowAperture (1 / 2) 1) := by
    simpa [burnolFixedSubWindowSourceAtom, coPoissonSubWindowSonin] using
      (coPoissonSubWindowSonin (c := (1 / 2 : ℝ)) (d := 1)
        (by norm_num) (by norm_num)).property
  have hshift : burnolMellinDividedShift h burnolFixedSubWindowSourceAtom ∈
      soninExtendedSpace (subWindowAperture (1 / 2) 1) := by
    rw [← burnolShift_eq_burnolMellinDividedShift h]
    exact burnolShift_mem_soninExtendedSpace h (xiDivisor_re_lt_one_of_half_lt rho h)
      (by norm_num [subWindowAperture]) hfixed
      (xiDivisor_fixedSubWindowSourceAtom_mellin_eq_zero rho h)
  rw [burnolCartierZeroTransfer_apply]
  exact (soninExtendedSpace (subWindowAperture (1 / 2) 1)).sub_mem hfixed
    ((soninExtendedSpace (subWindowAperture (1 / 2) 1)).smul_mem _ hshift)

def burnolXiCartierZeroTransferSourceLift
    (rho : XiDivisorSupport) (h : 1 / 2 < (rho : ℂ).re) :
    soninExtendedSpace (subWindowAperture (1 / 2) 1) :=
  ⟨burnolCartierZeroTransfer h burnolFixedSubWindowSourceAtom,
    xiDivisor_burnolCartierZeroTransfer_mem_soninExtendedSpace rho h⟩

theorem one_lt_norm_burnolCartierForwardHeadGain
    {rho : ℂ} (hright : 1 / 2 < rho.re) (hlt : rho.re < 1) :
    1 < ‖burnolCartierForwardHeadGain rho‖ := by
  have hrhoOne : rho ≠ 1 := by
    intro hrho
    rw [hrho] at hlt
    norm_num at hlt
  have hdenpos : 0 < ‖(1 : ℂ) - rho‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr hrhoOne.symm)
  unfold burnolCartierForwardHeadGain
  rw [norm_div, norm_conj]
  rw [one_lt_div hdenpos]
  have hsq : ‖(1 : ℂ) - rho‖ ^ 2 < ‖rho‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im, Complex.one_im]
    nlinarith
  nlinarith [norm_nonneg rho, norm_nonneg ((1 : ℂ) - rho)]

/-- Off the critical line the cosine-side Cartier head gain is strictly contractive.  Thus the
global isometry cannot identify the two aperture heads; it must move the missing mass into the
cosine tail. -/
theorem norm_burnolCartierCosineHeadGain_lt_one
    {rho : ℂ} (hright : 1 / 2 < rho.re) (hlt : rho.re < 1) :
    ‖burnolCartierCosineHeadGain rho‖ < 1 := by
  have hrho : rho ≠ 0 := by
    intro hzero
    rw [hzero] at hright
    norm_num at hright
  rw [burnolCartierCosineHeadGain_eq_inv_conj_forwardHeadGain hrho,
    norm_inv, norm_conj]
  exact inv_lt_one_of_one_lt₀
    (one_lt_norm_burnolCartierForwardHeadGain hright hlt)

/-- The forward and cosine Cartier head gains have exactly reciprocal norms throughout the
open right half of the critical strip. -/
theorem norm_burnolCartierCosineHeadGain_mul_forward_eq_one
    {rho : ℂ} (hright : 1 / 2 < rho.re) (hlt : rho.re < 1) :
    ‖burnolCartierCosineHeadGain rho‖ *
        ‖burnolCartierForwardHeadGain rho‖ = 1 := by
  have hrho : rho ≠ 0 := by
    intro hzero
    rw [hzero] at hright
    norm_num at hright
  rw [burnolCartierCosineHeadGain_eq_inv_conj_forwardHeadGain hrho,
    norm_inv, norm_conj, inv_mul_cancel₀]
  exact (zero_lt_one.trans
    (one_lt_norm_burnolCartierForwardHeadGain hright hlt)).ne'

/-- The oriented head-mass defect is strictly positive off the critical line. -/
theorem burnolCartierHeadGain_sq_defect_pos
    {rho : ℂ} (hright : 1 / 2 < rho.re) (hlt : rho.re < 1) :
    0 < ‖burnolCartierForwardHeadGain rho‖ ^ 2 -
      ‖burnolCartierCosineHeadGain rho‖ ^ 2 := by
  have hf := one_lt_norm_burnolCartierForwardHeadGain hright hlt
  have hc := norm_burnolCartierCosineHeadGain_lt_one hright hlt
  nlinarith [norm_nonneg (burnolCartierForwardHeadGain rho),
    norm_nonneg (burnolCartierCosineHeadGain rho)]

/-- Every hypothetical right-half Xi divisor carries strict reciprocal aperture-head asymmetry.
Any successful forward/reflected sewing must therefore transfer a nonzero head defect through the
tails rather than identify the two heads. -/
theorem xiDivisor_burnolCartierHeadGain_strict_reciprocal_asymmetry
    (rho : XiDivisorSupport) (hright : 1 / 2 < (rho : ℂ).re) :
    1 < ‖burnolCartierForwardHeadGain (rho : ℂ)‖ ∧
      ‖burnolCartierCosineHeadGain (rho : ℂ)‖ < 1 ∧
      ‖burnolCartierCosineHeadGain (rho : ℂ)‖ *
        ‖burnolCartierForwardHeadGain (rho : ℂ)‖ = 1 := by
  have hlt := xiDivisor_re_lt_one_of_half_lt rho hright
  exact ⟨one_lt_norm_burnolCartierForwardHeadGain hright hlt,
    norm_burnolCartierCosineHeadGain_lt_one hright hlt,
    norm_burnolCartierCosineHeadGain_mul_forward_eq_one hright hlt⟩

/-- Source-side producer reduced to conservation of the single explicit fixed forward head. -/
def BurnolXiCartierZeroTransferForwardHeadNormConservation : Prop :=
  ∀ (rho : XiDivisorSupport) (_h : 1 / 2 < (rho : ℂ).re),
    ‖burnolCartierForwardHeadGain (rho : ℂ)‖ = 1

theorem burnolXiForwardReflectedCartierStokesSewing_of_cartierZeroTransferForwardHeadNorm
    (hhead : BurnolXiCartierZeroTransferForwardHeadNormConservation) :
    BurnolXiForwardReflectedCartierStokesSewing := by
  intro rho h
  have hline : (rho : ℂ).re = 1 / 2 :=
    (norm_burnolCartierForwardHeadGain_eq_one_iff (xiDivisor_re_lt_one_of_half_lt rho h)).mp
      (hhead rho h)
  exfalso
  linarith

theorem riemannHypothesis_of_burnolXiCartierZeroTransferForwardHeadNormConservation
    (hhead : BurnolXiCartierZeroTransferForwardHeadNormConservation) : RiemannHypothesis :=
  riemannHypothesis_of_burnolXiForwardReflectedCartierStokesSewing
    (burnolXiForwardReflectedCartierStokesSewing_of_cartierZeroTransferForwardHeadNorm hhead)

theorem burnolXiCartierZeroTransferForwardHeadNorm_of_forwardReflectedSewing
    (hsew : BurnolXiForwardReflectedCartierStokesSewing) :
    BurnolXiCartierZeroTransferForwardHeadNormConservation := by
  have hRH := riemannHypothesis_of_burnolXiForwardReflectedCartierStokesSewing hsew
  intro rho h
  have hline := xi_divisor_support_re_eq_half_of_rh hRH rho
  exact (norm_burnolCartierForwardHeadGain_eq_one_iff (xiDivisor_re_lt_one_of_half_lt rho h)).mpr hline

theorem burnolXiForwardReflectedCartierStokesSewing_iff_cartierZeroTransferForwardHeadNorm :
    BurnolXiForwardReflectedCartierStokesSewing ↔
      BurnolXiCartierZeroTransferForwardHeadNormConservation :=
  ⟨burnolXiCartierZeroTransferForwardHeadNorm_of_forwardReflectedSewing,
    burnolXiForwardReflectedCartierStokesSewing_of_cartierZeroTransferForwardHeadNorm⟩

end RHTower
