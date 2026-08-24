import GaloisForLFunctions.RHTower.SuzukiShiftedXiExtremeEquiv

open Complex Set

namespace RHTower

noncomputable section

/-- Reflection-paired finite tail factor. -/
def xiShiftRightReflectionPairFactor (z : ℂ) (q : XiZeroCopy) : ℂ :=
  weierstrassE1 (z / xiSpectralPoint q) *
    weierstrassE1 (z / -xiSpectralPoint q)

/-- A reflection pair of genus-one factors is the corresponding quadratic factor. -/
theorem xiShiftRightReflectionPairFactor_eq (z : ℂ) (q : XiZeroCopy) :
    xiShiftRightReflectionPairFactor z q =
      (1 - z / xiSpectralPoint q) *
        (1 + z / xiSpectralPoint q) := by
  rw [xiShiftRightReflectionPairFactor, weierstrassE1, weierstrassE1]
  have hneg : z / -xiSpectralPoint q = -(z / xiSpectralPoint q) := by
    rw [div_neg]
  rw [hneg, Complex.exp_neg]
  field_simp [Complex.exp_ne_zero]
  ring

/-- With finitely many selected right zeros, the two-tailed canonical product is the finite
product of its reflection-paired quadratic factors. -/
theorem xiShiftExtremeCanonicalProduct_eq_right_pair_prod
    (omega : ℝ) (homega : 0 ≤ omega)
    [Fintype (XiShiftRightZeroCopy omega)] (z : ℂ) :
    xiShiftExtremeCanonicalProduct omega z =
      ∏ q : XiShiftRightZeroCopy omega,
        xiShiftRightReflectionPairFactor z q.1 := by
  letI : Fintype (XiShiftExtremeZeroCopy omega) :=
    xiShiftExtremeFintype omega homega
  rw [xiShiftExtremeCanonicalProduct, canonicalProductE1IndexedSelected,
    canonicalProductE1Indexed, tprod_fintype]
  let e := xiShiftExtremeSumEquiv omega homega
  calc
    (∏ q : XiShiftExtremeZeroCopy omega,
        weierstrassE1 (z / xiSpectralPoint q.1)) =
      ∏ s : XiShiftRightZeroCopy omega ⊕ XiShiftRightZeroCopy omega,
        weierstrassE1 (z / xiSpectralPoint (e.symm s).1) := by
          exact (e.symm.prod_comp (fun q : XiShiftExtremeZeroCopy omega =>
            weierstrassE1 (z / xiSpectralPoint q.1))).symm
    _ = (∏ q : XiShiftRightZeroCopy omega,
          weierstrassE1 (z / xiSpectralPoint q.1)) *
        ∏ q : XiShiftRightZeroCopy omega,
          weierstrassE1
            (z / xiSpectralPoint (xiZeroCopyReflectEquiv q.1)) := by
      rw [Fintype.prod_sum_type]
      rfl
    _ = ∏ q : XiShiftRightZeroCopy omega,
        xiShiftRightReflectionPairFactor z q.1 := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro q _
      rw [xiShiftRightReflectionPairFactor, xiSpectralPoint_reflect]

/-- Upper-half-plane zero coordinate of the finite transverse-tail numerator. -/
def xiShiftNumeratorCoordinate (omega : ℝ)
    (q : XiShiftRightZeroCopy omega) : ℂ :=
  -xiSpectralPoint q.1 + (omega : ℂ) * I

theorem xiShiftNumeratorCoordinate_im_pos {omega : ℝ} (homega : 0 ≤ omega)
    (q : XiShiftRightZeroCopy omega) :
    0 < (xiShiftNumeratorCoordinate omega q).im := by
  rw [xiShiftNumeratorCoordinate]
  simp only [add_im, neg_im, mul_im, ofReal_re, I_im, ofReal_im, I_re,
    mul_one, mul_zero]
  have hq := q.2
  norm_num [mul_re] at hq
  linarith

/-- Schwarz conjugation preserves the selected right shifted tail. -/
def xiShiftRightCopyConjEquiv (omega : ℝ) :
    XiShiftRightZeroCopy omega ≃ XiShiftRightZeroCopy omega :=
  Equiv.subtypeEquiv xiZeroCopyConjEquiv (fun q => by
    rw [xiSpectralPoint_copyConj]
    have h : (I * -(starRingEnd ℂ) (xiSpectralPoint q)).re =
        (I * xiSpectralPoint q).re := by
      norm_num [mul_re]
    rw [h])

theorem conj_xiShiftPoleCoordinate_copyConj (omega : ℝ)
    (q : XiShiftRightZeroCopy omega) :
    (starRingEnd ℂ)
        (xiShiftPoleCoordinate omega (xiShiftRightCopyConjEquiv omega q)) =
      xiSpectralPoint q.1 + (omega : ℂ) * I := by
  have hspec :
      xiSpectralPoint (xiShiftRightCopyConjEquiv omega q).1 =
        -(starRingEnd ℂ) (xiSpectralPoint q.1) :=
    xiSpectralPoint_copyConj q.1
  rw [xiShiftPoleCoordinate, hspec]
  simp [mul_comm, add_comm]

theorem conj_xiShiftNumeratorCoordinate_copyConj (omega : ℝ)
    (q : XiShiftRightZeroCopy omega) :
    (starRingEnd ℂ)
        (xiShiftNumeratorCoordinate omega
          (xiShiftRightCopyConjEquiv omega q)) =
      xiSpectralPoint q.1 - (omega : ℂ) * I := by
  have hspec :
      xiSpectralPoint (xiShiftRightCopyConjEquiv omega q).1 =
        -(starRingEnd ℂ) (xiSpectralPoint q.1) :=
    xiSpectralPoint_copyConj q.1
  rw [xiShiftNumeratorCoordinate, hspec]
  simp [mul_comm, add_comm, sub_eq_add_neg]

theorem xiShiftRightReflectionPairFactor_numerator_shift
    (omega : ℝ) (z : ℂ) (q : XiShiftRightZeroCopy omega) :
    xiShiftRightReflectionPairFactor (z - (omega : ℂ) * I) q.1 =
      -((z - (xiSpectralPoint q.1 + (omega : ℂ) * I)) *
        (z - xiShiftNumeratorCoordinate omega q)) /
          xiSpectralPoint q.1 ^ 2 := by
  rw [xiShiftRightReflectionPairFactor_eq, xiShiftNumeratorCoordinate]
  field_simp [xiSpectralPoint_ne_zero q.1]
  ring

theorem xiShiftRightReflectionPairFactor_denominator_shift
    (omega : ℝ) (z : ℂ) (q : XiShiftRightZeroCopy omega) :
    xiShiftRightReflectionPairFactor (-z - (omega : ℂ) * I) q.1 =
      -((z - xiShiftPoleCoordinate omega q) *
        (z - (xiSpectralPoint q.1 - (omega : ℂ) * I))) /
          xiSpectralPoint q.1 ^ 2 := by
  rw [xiShiftRightReflectionPairFactor_eq, xiShiftPoleCoordinate]
  field_simp [xiSpectralPoint_ne_zero q.1]
  ring

/-- Common nonzero scale in the two finite shifted tail products. -/
def xiShiftFiniteTailScale (omega : ℝ)
    [Fintype (XiShiftRightZeroCopy omega)] : ℂ :=
  ∏ q : XiShiftRightZeroCopy omega,
    -(xiSpectralPoint q.1 ^ 2)⁻¹

theorem xiShiftFiniteTailScale_ne_zero (omega : ℝ)
    [Fintype (XiShiftRightZeroCopy omega)] :
    xiShiftFiniteTailScale omega ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro q _
  exact neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 (xiSpectralPoint_ne_zero q.1)))

def xiShiftFiniteNumeratorProduct (omega : ℝ)
    [Fintype (XiShiftRightZeroCopy omega)] (z : ℂ) : ℂ :=
  ∏ q : XiShiftRightZeroCopy omega,
    (z - xiShiftNumeratorCoordinate omega q)

def xiShiftFiniteConjNumeratorProduct (omega : ℝ)
    [Fintype (XiShiftRightZeroCopy omega)] (z : ℂ) : ℂ :=
  ∏ q : XiShiftRightZeroCopy omega,
    (z - (starRingEnd ℂ) (xiShiftNumeratorCoordinate omega q))

def xiShiftFinitePoleProduct (omega : ℝ)
    [Fintype (XiShiftRightZeroCopy omega)] (z : ℂ) : ℂ :=
  ∏ q : XiShiftRightZeroCopy omega,
    (z - xiShiftPoleCoordinate omega q)

def xiShiftFiniteConjPoleProduct (omega : ℝ)
    [Fintype (XiShiftRightZeroCopy omega)] (z : ℂ) : ℂ :=
  ∏ q : XiShiftRightZeroCopy omega,
    (z - (starRingEnd ℂ) (xiShiftPoleCoordinate omega q))

theorem prod_lowerNumerator_eq_conjPoleProduct (omega : ℝ)
    [Fintype (XiShiftRightZeroCopy omega)] (z : ℂ) :
    (∏ q : XiShiftRightZeroCopy omega,
        (z - (xiSpectralPoint q.1 + (omega : ℂ) * I))) =
      xiShiftFiniteConjPoleProduct omega z := by
  let e := xiShiftRightCopyConjEquiv omega
  calc
    (∏ q : XiShiftRightZeroCopy omega,
        (z - (xiSpectralPoint q.1 + (omega : ℂ) * I))) =
      ∏ q : XiShiftRightZeroCopy omega,
        (z - (starRingEnd ℂ) (xiShiftPoleCoordinate omega (e q))) := by
      apply Finset.prod_congr rfl
      intro q _
      rw [conj_xiShiftPoleCoordinate_copyConj]
    _ = ∏ q : XiShiftRightZeroCopy omega,
        (z - (starRingEnd ℂ) (xiShiftPoleCoordinate omega q)) :=
      e.prod_comp (fun q : XiShiftRightZeroCopy omega =>
        z - (starRingEnd ℂ) (xiShiftPoleCoordinate omega q))
    _ = xiShiftFiniteConjPoleProduct omega z := rfl

theorem prod_lowerPole_eq_conjNumeratorProduct (omega : ℝ)
    [Fintype (XiShiftRightZeroCopy omega)] (z : ℂ) :
    (∏ q : XiShiftRightZeroCopy omega,
        (z - (xiSpectralPoint q.1 - (omega : ℂ) * I))) =
      xiShiftFiniteConjNumeratorProduct omega z := by
  let e := xiShiftRightCopyConjEquiv omega
  calc
    (∏ q : XiShiftRightZeroCopy omega,
        (z - (xiSpectralPoint q.1 - (omega : ℂ) * I))) =
      ∏ q : XiShiftRightZeroCopy omega,
        (z - (starRingEnd ℂ) (xiShiftNumeratorCoordinate omega (e q))) := by
      apply Finset.prod_congr rfl
      intro q _
      rw [conj_xiShiftNumeratorCoordinate_copyConj]
    _ = ∏ q : XiShiftRightZeroCopy omega,
        (z - (starRingEnd ℂ) (xiShiftNumeratorCoordinate omega q)) :=
      e.prod_comp (fun q : XiShiftRightZeroCopy omega =>
        z - (starRingEnd ℂ) (xiShiftNumeratorCoordinate omega q))
    _ = xiShiftFiniteConjNumeratorProduct omega z := rfl

theorem xiShiftExtremeCanonicalProduct_numerator_shift_factorization
    (omega : ℝ) (homega : 0 ≤ omega)
    [Fintype (XiShiftRightZeroCopy omega)] (z : ℂ) :
    xiShiftExtremeCanonicalProduct omega (z - (omega : ℂ) * I) =
      xiShiftFiniteTailScale omega *
        xiShiftFiniteConjPoleProduct omega z *
        xiShiftFiniteNumeratorProduct omega z := by
  rw [xiShiftExtremeCanonicalProduct_eq_right_pair_prod omega homega]
  calc
    (∏ q : XiShiftRightZeroCopy omega,
        xiShiftRightReflectionPairFactor
          (z - (omega : ℂ) * I) q.1) =
      ∏ q : XiShiftRightZeroCopy omega,
        (-(xiSpectralPoint q.1 ^ 2)⁻¹ *
          (z - (xiSpectralPoint q.1 + (omega : ℂ) * I)) *
          (z - xiShiftNumeratorCoordinate omega q)) := by
      apply Finset.prod_congr rfl
      intro q _
      rw [xiShiftRightReflectionPairFactor_numerator_shift]
      field_simp [xiSpectralPoint_ne_zero q.1]
    _ = xiShiftFiniteTailScale omega *
        (∏ q : XiShiftRightZeroCopy omega,
          (z - (xiSpectralPoint q.1 + (omega : ℂ) * I))) *
        xiShiftFiniteNumeratorProduct omega z := by
      rw [xiShiftFiniteTailScale, xiShiftFiniteNumeratorProduct,
        ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    _ = _ := by rw [prod_lowerNumerator_eq_conjPoleProduct]

theorem xiShiftExtremeCanonicalProduct_denominator_shift_factorization
    (omega : ℝ) (homega : 0 ≤ omega)
    [Fintype (XiShiftRightZeroCopy omega)] (z : ℂ) :
    xiShiftExtremeCanonicalProduct omega (-z - (omega : ℂ) * I) =
      xiShiftFiniteTailScale omega *
        xiShiftFinitePoleProduct omega z *
        xiShiftFiniteConjNumeratorProduct omega z := by
  rw [xiShiftExtremeCanonicalProduct_eq_right_pair_prod omega homega]
  calc
    (∏ q : XiShiftRightZeroCopy omega,
        xiShiftRightReflectionPairFactor
          (-z - (omega : ℂ) * I) q.1) =
      ∏ q : XiShiftRightZeroCopy omega,
        (-(xiSpectralPoint q.1 ^ 2)⁻¹ *
          (z - xiShiftPoleCoordinate omega q) *
          (z - (xiSpectralPoint q.1 - (omega : ℂ) * I))) := by
      apply Finset.prod_congr rfl
      intro q _
      rw [xiShiftRightReflectionPairFactor_denominator_shift]
      field_simp [xiSpectralPoint_ne_zero q.1]
    _ = xiShiftFiniteTailScale omega *
        xiShiftFinitePoleProduct omega z *
        (∏ q : XiShiftRightZeroCopy omega,
          (z - (xiSpectralPoint q.1 - (omega : ℂ) * I))) := by
      rw [xiShiftFiniteTailScale, xiShiftFinitePoleProduct,
        ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    _ = _ := by rw [prod_lowerPole_eq_conjNumeratorProduct]

/-- Finite upper-half-plane Blaschke quotient before Cayley transport. -/
def xiShiftFiniteNumeratorHalfPlaneBlaschke (omega : ℝ)
    [Fintype (XiShiftRightZeroCopy omega)] (z : ℂ) : ℂ :=
  xiShiftFiniteNumeratorProduct omega z /
    xiShiftFiniteConjNumeratorProduct omega z

def xiShiftFinitePoleHalfPlaneBlaschke (omega : ℝ)
    [Fintype (XiShiftRightZeroCopy omega)] (z : ℂ) : ℂ :=
  xiShiftFinitePoleProduct omega z /
    xiShiftFiniteConjPoleProduct omega z

/-- The finite transverse-tail quotient is exactly numerator Blaschke divided by pole Blaschke. -/
theorem xiShiftExtremeTheta_eq_finiteHalfPlaneBlaschke_div
    {omega : ℝ} (homega : 0 ≤ omega)
    [Fintype (XiShiftRightZeroCopy omega)] {z : ℂ}
    (hext : xiShiftExtremeE omega z ≠ 0) :
    xiShiftExtremeTheta omega z =
      xiShiftFiniteNumeratorHalfPlaneBlaschke omega z /
        xiShiftFinitePoleHalfPlaneBlaschke omega z := by
  have hscale := xiShiftFiniteTailScale_ne_zero omega
  have hden := xiShiftExtremeCanonicalProduct_denominator_shift_factorization
    omega homega z
  have hdenProduct :
      xiShiftFinitePoleProduct omega z *
        xiShiftFiniteConjNumeratorProduct omega z ≠ 0 := by
    intro hzero
    apply hext
    rw [xiShiftExtremeE, hden]
    simpa only [mul_assoc, mul_zero] using
      congrArg (fun u => xiShiftFiniteTailScale omega * u) hzero
  have hpole : xiShiftFinitePoleProduct omega z ≠ 0 :=
    (mul_ne_zero_iff.mp hdenProduct).1
  have hconjNum : xiShiftFiniteConjNumeratorProduct omega z ≠ 0 :=
    (mul_ne_zero_iff.mp hdenProduct).2
  rw [xiShiftExtremeTheta, xiShiftExtremeE, xiShiftExtremeE,
    xiShiftExtremeCanonicalProduct_numerator_shift_factorization omega homega,
    xiShiftExtremeCanonicalProduct_denominator_shift_factorization omega homega,
    xiShiftFiniteNumeratorHalfPlaneBlaschke,
    xiShiftFinitePoleHalfPlaneBlaschke]
  field_simp

end

end RHTower
