import GaloisForLFunctions.RHTower.CCM.CCMFinitePhaseNoether
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCCMMixedScrewWeilBridge

/-!
# Complex coefficient energies on actual real source families

Real physical sources have a real mixed Weil matrix. Consequently complex
coefficient energy splits into the two real coefficient energies, and the
finite phase potential is exactly the energy of one complex phase source.
-/

noncomputable section

open scoped BigOperators

namespace RHTower

theorem ccmRestrictedWeilForm_smul_left (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) (z : ℂ) :
    ccmRestrictedWeilForm a (z • u) v = starRingEnd ℂ z * ccmRestrictedWeilForm a u v := by
  simp only [ccmRestrictedWeilForm, map_smul,
    inner_smul_left (E := CCMArchimedeanFormDomain a),
    inner_smul_left (E := suzukiApertureHilbert a), mul_add]

theorem ccmRestrictedWeilForm_smul_right (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) (z : ℂ) :
    ccmRestrictedWeilForm a u (z • v) = z * ccmRestrictedWeilForm a u v := by
  simp only [ccmRestrictedWeilForm, map_smul,
    inner_smul_right (E := CCMArchimedeanFormDomain a),
    inner_smul_right (E := suzukiApertureHilbert a), mul_add]

theorem ccmRestrictedWeilForm_sum_left {ι : Type*} (a : SuzukiPositiveAperture)
    (s : Finset ι) (u : ι → CCMArchimedeanFormDomain a) (v : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilForm a (∑ i ∈ s, u i) v = ∑ i ∈ s, ccmRestrictedWeilForm a (u i) v := by
  simp only [ccmRestrictedWeilForm, map_sum, sum_inner, Finset.sum_add_distrib]

theorem ccmRestrictedWeilForm_sum_right {ι : Type*} (a : SuzukiPositiveAperture)
    (s : Finset ι) (u : CCMArchimedeanFormDomain a) (v : ι → CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilForm a u (∑ i ∈ s, v i) = ∑ i ∈ s, ccmRestrictedWeilForm a u (v i) := by
  simp only [ccmRestrictedWeilForm, map_sum, inner_sum, Finset.sum_add_distrib]

theorem ccmRestrictedWeilForm_neg_left (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilForm a (-u) v = -ccmRestrictedWeilForm a u v := by
  simp only [ccmRestrictedWeilForm, map_neg, inner_neg_left, neg_add]

theorem ccmRestrictedWeilForm_neg_right (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilForm a u (-v) = -ccmRestrictedWeilForm a u v := by
  simp only [ccmRestrictedWeilForm, map_neg, inner_neg_right, neg_add]

theorem ccmRestrictedWeilForm_complex_sum {ι : Type*} [Fintype ι]
    (a : SuzukiPositiveAperture) (u : ι → CCMArchimedeanFormDomain a) (z w : ι → ℂ) :
    ccmRestrictedWeilForm a (∑ i, z i • u i) (∑ i, w i • u i) =
      ∑ i, ∑ j, starRingEnd ℂ (z i) * (w j * ccmRestrictedWeilForm a (u i) (u j)) := by
  simp_rw [ccmRestrictedWeilForm_sum_left, ccmRestrictedWeilForm_sum_right,
    ccmRestrictedWeilForm_smul_left, ccmRestrictedWeilForm_smul_right]

theorem ccmRestrictedWeilForm_real_source_im_zero (a : SuzukiPositiveAperture)
    (u v : CCMComplexSmoothInteriorSource a)
    (hu : ∀ x : ℝ, (u x).im = 0) (hv : ∀ x : ℝ, (v x).im = 0) :
    (ccmRestrictedWeilForm a u.toCCMFormVector v.toCCMFormVector).im = 0 := by
  have he (w : CCMComplexSmoothInteriorSource a) (hw : ∀ x : ℝ, (w x).im = 0) :
      ccmComplexSmoothInteriorSourceOfRealCore a w.realCore = w := by
    apply CCMComplexSmoothInteriorSource.eq_of_coe_eq
    funext x
    change ((w x).re : ℂ) = w x
    apply Complex.ext
    · rfl
    · exact (hw x).symm
  conv_lhs => rw [← he u hu, ← he v hv]
  rw [ccmComplexSmoothInteriorSourceOfRealCore_toCCMFormVector,
    ccmComplexSmoothInteriorSourceOfRealCore_toCCMFormVector]
  exact ccmRestrictedWeilForm_realCore_mixed_im_eq_zero a u.realCore v.realCore

theorem ccmRestrictedWeilSourceQuadratic_complex_sum_realImag {ι : Type*} [Fintype ι]
    (a : SuzukiPositiveAperture) (u : ι → CCMArchimedeanFormDomain a)
    (hreal : ∀ i j, (ccmRestrictedWeilForm a (u i) (u j)).im = 0) (z : ι → ℂ) :
    ccmRestrictedWeilSourceQuadratic a (∑ i, z i • u i) =
      ccmRestrictedWeilSourceQuadratic a (∑ i, ((z i).re : ℂ) • u i) +
      ccmRestrictedWeilSourceQuadratic a (∑ i, ((z i).im : ℂ) • u i) := by
  simp_rw [← ccmRestrictedWeilForm_self_re_eq_source, ccmRestrictedWeilForm_complex_sum,
    Complex.re_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, hreal, mul_zero, zero_mul, sub_zero, add_zero]
  ring

theorem ccmWeilFinitePhaseEnergy_eq_complex_phase {ι : Type*} [Fintype ι]
    (a : SuzukiPositiveAperture) (u : ι → CCMArchimedeanFormDomain a)
    (hreal : ∀ i j, (ccmRestrictedWeilForm a (u i) (u j)).im = 0) (theta : ι → ℝ) :
    ccmWeilFinitePhaseEnergy a u theta =
      ccmRestrictedWeilSourceQuadratic a (∑ i, Complex.exp ((theta i : ℂ) * Complex.I) • u i) := by
  rw [ccmRestrictedWeilSourceQuadratic_complex_sum_realImag a u hreal]
  simp only [Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    ccmWeilFinitePhaseEnergy]

end RHTower
