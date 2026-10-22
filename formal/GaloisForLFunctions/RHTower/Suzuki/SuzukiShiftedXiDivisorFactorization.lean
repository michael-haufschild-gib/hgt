import GaloisForLFunctions.RHTower.GammaSewnMobiusXiTrueWienerHopfFactorization
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalShiftRatio

open Complex Set

namespace RHTower

noncomputable section

/-- Multiplicity copies of Xi zeros strictly beyond the shifted line. -/
abbrev XiShiftRightZeroCopy (omega : ℝ) :=
  {q : XiZeroCopy // omega < (I * xiSpectralPoint q).re}

/-- Canonical product over the Xi divisor strictly beyond the shifted line. -/
def xiShiftRightCanonicalProduct (omega : ℝ) : ℂ → ℂ :=
  canonicalProductE1IndexedSelected xiSpectralPoint
    (fun q => omega < (I * xiSpectralPoint q).re)

/-- Canonical product over the complementary shifted Xi divisor. -/
def xiShiftRightComplementCanonicalProduct (omega : ℝ) : ℂ → ℂ :=
  canonicalProductE1IndexedComplement xiSpectralPoint
    (fun q => omega < (I * xiSpectralPoint q).re)

theorem xiShiftRightCanonicalProduct_analytic (omega : ℝ) :
    AnalyticOnNhd ℂ (xiShiftRightCanonicalProduct omega) Set.univ := by
  exact canonicalProductE1IndexedSelected_analytic
    xiSpectralPoint
    (fun q => omega < (I * xiSpectralPoint q).re)
    xiSpectralPoint_ne_zero
    xiSpectralPoint_inv_sq_summable

theorem xiShiftRightComplementCanonicalProduct_analytic (omega : ℝ) :
    AnalyticOnNhd ℂ (xiShiftRightComplementCanonicalProduct omega) Set.univ := by
  exact canonicalProductE1IndexedComplement_analytic
    xiSpectralPoint
    (fun q => omega < (I * xiSpectralPoint q).re)
    xiSpectralPoint_ne_zero
    xiSpectralPoint_inv_sq_summable

theorem xiCanonicalProduct_eq_shiftRight_mul_complement (omega : ℝ) (z : ℂ) :
    xiCanonicalProduct z =
      xiShiftRightCanonicalProduct omega z *
        xiShiftRightComplementCanonicalProduct omega z := by
  simpa [xiCanonicalProduct, xiShiftRightCanonicalProduct,
    xiShiftRightComplementCanonicalProduct] using
    canonicalProductE1Indexed_eq_selected_mul_complement
      xiSpectralPoint
      (fun q => omega < (I * xiSpectralPoint q).re)
      xiSpectralPoint_ne_zero
      xiSpectralPoint_inv_sq_summable z

/-- Entire complementary Xi source factor at a shifted divisor cutoff. -/
def xiShiftRightComplementSourceFactor (omega : ℝ) (z : ℂ) : ℂ :=
  xiHadamardQuotient z * xiShiftRightComplementCanonicalProduct omega z

theorem xiShiftRightComplementSourceFactor_analytic (omega : ℝ) :
    AnalyticOnNhd ℂ (xiShiftRightComplementSourceFactor omega) Set.univ :=
  xiHadamardQuotient_analytic.mul
    (xiShiftRightComplementCanonicalProduct_analytic omega)

theorem xiShiftRightCanonicalProduct_mul_complementSourceFactor
    (omega : ℝ) (z : ℂ) :
    xiShiftRightCanonicalProduct omega z *
        xiShiftRightComplementSourceFactor omega z = XiC z := by
  have hsource := congrFun xiHadamardQuotient_mul_canonicalProduct z
  rw [Pi.mul_apply] at hsource
  calc
    xiShiftRightCanonicalProduct omega z *
        xiShiftRightComplementSourceFactor omega z =
      xiHadamardQuotient z *
        (xiShiftRightCanonicalProduct omega z *
          xiShiftRightComplementCanonicalProduct omega z) := by
        rw [xiShiftRightComplementSourceFactor]
        ring_nf
    _ = xiHadamardQuotient z * xiCanonicalProduct z := by
      rw [← xiCanonicalProduct_eq_shiftRight_mul_complement omega z]
    _ = XiC z := hsource

theorem xiShiftRightCanonicalProduct_eq_zero
    (omega : ℝ) (q : XiShiftRightZeroCopy omega) :
    xiShiftRightCanonicalProduct omega (xiSpectralPoint q.1) = 0 := by
  rw [xiShiftRightCanonicalProduct, canonicalProductE1IndexedSelected,
    canonicalProductE1Indexed]
  apply tprod_of_exists_eq_zero
  refine ⟨q, ?_⟩
  rw [div_self (xiSpectralPoint_ne_zero q.1), weierstrassE1_one]

theorem xiShiftRightCanonicalProduct_eq_zero_iff_exists
    (omega : ℝ) (z : ℂ) :
    xiShiftRightCanonicalProduct omega z = 0 ↔
      ∃ q : XiShiftRightZeroCopy omega, xiSpectralPoint q.1 = z := by
  constructor
  · intro hz
    by_contra hnone
    have haway : ∀ q : XiShiftRightZeroCopy omega,
        z ≠ xiSpectralPoint q.1 := by
      intro q heq
      exact hnone ⟨q, heq.symm⟩
    exact (canonicalProductE1IndexedSelected_ne_zero
      xiSpectralPoint
      (fun q => omega < (I * xiSpectralPoint q).re)
      xiSpectralPoint_ne_zero xiSpectralPoint_inv_sq_summable z haway) hz
  · rintro ⟨q, rfl⟩
    exact xiShiftRightCanonicalProduct_eq_zero omega q

theorem xiShiftRightComplementCanonicalProduct_ne_zero_at_selected
    (omega : ℝ) (q : XiShiftRightZeroCopy omega) :
    xiShiftRightComplementCanonicalProduct omega (xiSpectralPoint q.1) ≠ 0 := by
  apply canonicalProductE1IndexedComplement_ne_zero
    xiSpectralPoint
    (fun r => omega < (I * xiSpectralPoint r).re)
    xiSpectralPoint_ne_zero xiSpectralPoint_inv_sq_summable
  intro r heq
  apply r.2
  rw [← heq]
  exact q.2

theorem xiShiftRightComplementSourceFactor_ne_zero_at_selected
    (omega : ℝ) (q : XiShiftRightZeroCopy omega) :
    xiShiftRightComplementSourceFactor omega (xiSpectralPoint q.1) ≠ 0 :=
  mul_ne_zero (xiHadamardQuotient_ne_zero _)
    (xiShiftRightComplementCanonicalProduct_ne_zero_at_selected omega q)

/-- Selected shifted factor retains the full analytic multiplicity of Xi. -/
theorem analyticOrderAt_XiC_eq_xiShiftRightCanonicalProduct_at_selected
    (omega : ℝ) (q : XiShiftRightZeroCopy omega) :
    analyticOrderAt XiC (xiSpectralPoint q.1) =
      analyticOrderAt (xiShiftRightCanonicalProduct omega)
        (xiSpectralPoint q.1) := by
  have hfun :
      (fun z => xiShiftRightCanonicalProduct omega z *
        xiShiftRightComplementSourceFactor omega z) = XiC := by
    funext z
    exact xiShiftRightCanonicalProduct_mul_complementSourceFactor omega z
  have hselected :=
    xiShiftRightCanonicalProduct_analytic omega
      (xiSpectralPoint q.1) (Set.mem_univ _)
  have hcomplement :=
    xiShiftRightComplementSourceFactor_analytic omega
      (xiSpectralPoint q.1) (Set.mem_univ _)
  have hord :
      analyticOrderAt
          (fun z => xiShiftRightCanonicalProduct omega z *
            xiShiftRightComplementSourceFactor omega z)
          (xiSpectralPoint q.1) =
        analyticOrderAt (xiShiftRightCanonicalProduct omega)
            (xiSpectralPoint q.1) +
          analyticOrderAt (xiShiftRightComplementSourceFactor omega)
            (xiSpectralPoint q.1) := by
    simpa only [Pi.mul_apply] using!
      analyticOrderAt_mul hselected hcomplement
  rw [← hfun, hord,
    hcomplement.analyticOrderAt_eq_zero.mpr
      (xiShiftRightComplementSourceFactor_ne_zero_at_selected omega q),
    add_zero]

/-- Upper-half-plane pole coordinate of the shifted Xi quotient. -/
def xiShiftPoleCoordinate (omega : ℝ)
    (q : XiShiftRightZeroCopy omega) : ℂ :=
  -xiSpectralPoint q.1 - (omega : ℂ) * I

theorem xiShiftPoleCoordinate_im_pos (omega : ℝ)
    (q : XiShiftRightZeroCopy omega) :
    0 < (xiShiftPoleCoordinate omega q).im := by
  change 0 < (-xiSpectralPoint q.1 - (omega : ℂ) * I).im
  simp only [sub_im, neg_im, mul_im, ofReal_re, ofReal_im, I_re, I_im,
    mul_zero, mul_one, add_zero]
  have h := q.2
  norm_num [mul_re] at h
  linarith

theorem suzukiCanonicalE_xiShiftPoleCoordinate_eq_zero
    (omega : ℝ) (q : XiShiftRightZeroCopy omega) :
    suzukiCanonicalE omega (xiShiftPoleCoordinate omega q) = 0 := by
  rw [suzukiCanonicalE_eq_XiC_shift, xiShiftPoleCoordinate]
  convert XiC_xiSpectralPoint_eq_zero q.1 using 1
  ring_nf

theorem exists_xiShiftRightZeroCopy_of_suzukiCanonicalE_eq_zero
    (omega : ℝ) {z : ℂ} (hz : suzukiCanonicalE omega z = 0)
    (hzUpper : 0 < z.im) :
    ∃ q : XiShiftRightZeroCopy omega, xiShiftPoleCoordinate omega q = z := by
  rw [suzukiCanonicalE_eq_XiC_shift] at hz
  obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy _).mp hz
  have hselected : omega < (I * xiSpectralPoint q).re := by
    rw [hq]
    norm_num [mul_re, sub_re, sub_im, neg_re, neg_im]
    linarith
  refine ⟨⟨q, hselected⟩, ?_⟩
  rw [xiShiftPoleCoordinate, hq]
  ring_nf

theorem suzukiCanonicalE_eq_zero_iff_exists_shiftRight
    (omega : ℝ) {z : ℂ} (hzUpper : 0 < z.im) :
    suzukiCanonicalE omega z = 0 ↔
      ∃ q : XiShiftRightZeroCopy omega, xiShiftPoleCoordinate omega q = z := by
  constructor
  · exact fun hz =>
      exists_xiShiftRightZeroCopy_of_suzukiCanonicalE_eq_zero omega hz hzUpper
  · rintro ⟨q, rfl⟩
    exact suzukiCanonicalE_xiShiftPoleCoordinate_eq_zero omega q

theorem suzukiCanonicalE_shift_factorization (omega : ℝ) (z : ℂ) :
    xiShiftRightCanonicalProduct omega
          (-z - (omega : ℂ) * I) *
        xiShiftRightComplementSourceFactor omega
          (-z - (omega : ℂ) * I) =
      suzukiCanonicalE omega z := by
  rw [suzukiCanonicalE_eq_XiC_shift]
  exact xiShiftRightCanonicalProduct_mul_complementSourceFactor omega _

/-- A shift is nonexceptional when no selected denominator zero is also a numerator zero. -/
def SuzukiShiftNonexceptional (omega : ℝ) : Prop :=
  ∀ q : XiShiftRightZeroCopy omega,
    suzukiCanonicalE omega (-xiShiftPoleCoordinate omega q) ≠ 0

theorem suzukiCanonicalTheta_denominator_zero_numerator_ne_zero
    {omega : ℝ} (h : SuzukiShiftNonexceptional omega)
    (q : XiShiftRightZeroCopy omega) :
    suzukiCanonicalE omega (xiShiftPoleCoordinate omega q) = 0 ∧
      suzukiCanonicalE omega (-xiShiftPoleCoordinate omega q) ≠ 0 :=
  ⟨suzukiCanonicalE_xiShiftPoleCoordinate_eq_zero omega q, h q⟩

end

end RHTower
