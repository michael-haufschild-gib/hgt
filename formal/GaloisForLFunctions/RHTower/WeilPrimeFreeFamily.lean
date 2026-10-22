import GaloisForLFunctions.RHTower.WeilDeletionZeroCrossing
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarConstrainedRightContinuity

/-!
# The prime-free restricted Weil family

Removing the whole finite prime block from the restricted Weil remainder leaves the archimedean
scalar and the polar rank-two operator.  This *prime-free* remainder is an aperture-compatible
family in the sense of `CCMRemainderFamily`, its quadratic form on the archimedean form domain is
the archimedean multiplier integral plus the polar term, and on pole-vanishing sources it reduces
to the archimedean multiplier integral alone.  Below the aperture `½ log 2` no prime is visible,
so the prime-free family coincides with the literal one there.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.WeilDeletion

/-! ## The prime-free remainder -/

/-- The literal remainder with the finite prime block added back: the archimedean scalar plus the
polar operator. -/
def ccmPrimeFreeRemainder (a : SuzukiPositiveAperture) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  ccmRestrictedWeilBoundedRemainder a + ccmFinitePrimeOperator a

theorem ccmPrimeFreeRemainder_isSelfAdjoint (a : SuzukiPositiveAperture) :
    IsSelfAdjoint (ccmPrimeFreeRemainder a) := by
  unfold ccmPrimeFreeRemainder
  have h1 := ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a
  have h2 := ccmFinitePrimeOperator_isSelfAdjoint a
  rw [ContinuousLinearMap.isSelfAdjoint_iff'] at h1 h2 ⊢
  rw [ContinuousLinearMap.adjoint.map_add, h1, h2]

/-- The real diagonal of the finite prime block is the source-formula prime sum. -/
theorem re_inner_ccmFinitePrimeOperator_eq (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) :
    (inner ℂ (ccmFinitePrimeOperator a f) f).re =
      ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
        (ArithmeticFunction.vonMangoldt n : ℝ) * (1 / Real.sqrt n) *
          (inner ℂ (logTranslationCLM (Real.log n) f.1) f.1 +
            inner ℂ (logTranslationCLM (-Real.log n) f.1) f.1).re := by
  rw [inner_ccmFinitePrimeOperator, Complex.re_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [inner_ccmPrimeTransportOperator, ← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]

theorem primeFree_diagonal_eq_of_val_eq {a b : SuzukiPositiveAperture} (hab : a.1 ≤ b.1)
    {u : CCMArchimedeanFormDomain a} {v : CCMArchimedeanFormDomain b} (hvu : v.1 = u.1) :
    (inner ℂ (ccmPrimeFreeRemainder b (ccmArchimedeanFormToAperture b v))
        (ccmArchimedeanFormToAperture b v)).re =
      (inner ℂ (ccmPrimeFreeRemainder a (ccmArchimedeanFormToAperture a u))
        (ccmArchimedeanFormToAperture a u)).re := by
  unfold ccmPrimeFreeRemainder
  rw [add_apply, add_apply, inner_add_left, inner_add_left, Complex.add_re, Complex.add_re,
    literal_diagonal_eq_of_val_eq hab hvu, re_inner_ccmFinitePrimeOperator_eq,
    re_inner_ccmFinitePrimeOperator_eq]
  congr 1
  have hcoe : ((ccmArchimedeanFormToAperture b v : suzukiApertureHilbert b) : SoninL2) =
      ((ccmArchimedeanFormToAperture a u : suzukiApertureHilbert a) : SoninL2) :=
    ccmArchimedeanFormToAperture_coe_eq_of_val_eq hvu
  rw [hcoe]
  exact ccmFinitePrimeQuadraticSum_eq_of_le hab (ccmArchimedeanFormToAperture a u)

/-- The prime-free remainders form an aperture-compatible family. -/
def primeFreeFamily : CCMRemainderFamily where
  B a := ccmPrimeFreeRemainder a
  selfAdjoint a := ccmPrimeFreeRemainder_isSelfAdjoint a
  compat := by
    intro a b hab u v hvu
    exact primeFree_diagonal_eq_of_val_eq hab hvu

/-! ## Below the first prime the family is the literal one -/

theorem ccmFinitePrimeOperator_eq_zero_of_small {a : SuzukiPositiveAperture}
    (ha : a.1 < Real.log 2 / 2) : ccmFinitePrimeOperator a = 0 := by
  unfold ccmFinitePrimeOperator
  have hfl : Nat.floor (Real.exp (2 * a.1)) < 2 := by
    rw [Nat.floor_lt (Real.exp_pos _).le]
    have h2 : 2 * a.1 < Real.log 2 := by linarith
    rw [Real.lt_log_iff_exp_lt (by norm_num)] at h2
    exact_mod_cast h2
  have hempty : Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))) = ∅ := by
    rw [Finset.Icc_eq_empty_iff]
    omega
  rw [hempty, Finset.sum_empty]

theorem primeFreeFamily_energy_eq_literal_of_small {a : SuzukiPositiveAperture}
    (ha : a.1 < Real.log 2 / 2) :
    primeFreeFamily.energy a = ccmRestrictedWeilGroundEnergy a := by
  have he : ccmPrimeFreeRemainder a = ccmRestrictedWeilBoundedRemainder a := by
    unfold ccmPrimeFreeRemainder
    rw [ccmFinitePrimeOperator_eq_zero_of_small ha, add_zero]
  unfold CCMRemainderFamily.energy ccmRestrictedWeilGroundEnergy ccmRestrictedWeilCovariance
  change ‖boundedPerturbedFormCovariance (ccmArchimedeanFormToAperture a) (ccmPrimeFreeRemainder a)
      (ccmPrimeFreeRemainder_isSelfAdjoint a)‖⁻¹ -
    boundedPerturbedFormShift (ccmPrimeFreeRemainder a) = _
  rw [boundedPerturbedFormCovariance_congr (ccmArchimedeanFormToAperture a) he _
    (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a), he]

theorem exists_small_aperture_primeFree_energy_pos :
    ∃ δ : ℝ, 0 < δ ∧ ∀ a : SuzukiPositiveAperture, a.1 < δ → 0 < primeFreeFamily.energy a := by
  obtain ⟨δ₀, hδ₀, hpos⟩ := exists_suzukiSmallAperture_ccmGroundEnergy_pos
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨min δ₀ (Real.log 2 / 2), lt_min hδ₀ (by linarith), fun a ha => ?_⟩
  rw [primeFreeFamily_energy_eq_literal_of_small (lt_of_lt_of_le ha (min_le_right _ _))]
  exact hpos a (lt_of_lt_of_le ha (min_le_left _ _))

/-! ## The quadratic form of the prime-free family -/

/-- The archimedean multiplier integral of a form vector. -/
def archPart (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) : ℝ :=
  ∫ xi : ℝ, 2 * gammaHardyPhaseRate (2 * Real.pi * xi) * ‖(u.1 : ℝ → ℂ) xi‖ ^ 2

/-- The polar rank-two term of a form vector. -/
def polarPart (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) : ℝ :=
  let f := ccmArchimedeanFormToAperture a u
  ((starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector a (-1 / 2)) f) *
        inner ℂ (ccmPolarApertureVector a (1 / 2)) f +
      (starRingEnd ℂ) (inner ℂ (ccmPolarApertureVector a (1 / 2)) f) *
        inner ℂ (ccmPolarApertureVector a (-1 / 2)) f).re

theorem primeFreeFamily_Q_eq (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    primeFreeFamily.Q a u = archPart a u + polarPart a u := by
  have hQ : primeFreeFamily.Q a u = ccmRestrictedWeilSourceQuadratic a u +
      (inner ℂ (ccmFinitePrimeOperator a (ccmArchimedeanFormToAperture a u))
        (ccmArchimedeanFormToAperture a u)).re := by
    rw [CCMRemainderFamily.Q_eq_form_re, ← ccmRestrictedWeilForm_self_re_eq_source]
    show (inner ℂ u u + inner ℂ (ccmRestrictedWeilBoundedRemainder a (ccmArchimedeanFormToAperture a u) +
      ccmFinitePrimeOperator a (ccmArchimedeanFormToAperture a u))
      (ccmArchimedeanFormToAperture a u)).re = _
    rw [inner_add_left, ← add_assoc, Complex.add_re]
    rfl
  rw [hQ, re_inner_ccmFinitePrimeOperator_eq]
  unfold ccmRestrictedWeilSourceQuadratic archPart polarPart
  dsimp only
  ring

theorem polarPart_eq_zero_of_polarConstrained {a : SuzukiPositiveAperture}
    {u : CCMArchimedeanFormDomain a} (hu : IsPolarConstrained a u) : polarPart a u = 0 := by
  unfold polarPart
  dsimp only
  rw [hu.1, hu.2]
  simp

theorem primeFreeFamily_Q_eq_archPart {a : SuzukiPositiveAperture}
    {u : CCMArchimedeanFormDomain a} (hu : IsPolarConstrained a u) :
    primeFreeFamily.Q a u = archPart a u := by
  rw [primeFreeFamily_Q_eq, polarPart_eq_zero_of_polarConstrained hu, add_zero]

end RHTower.WeilDeletion

end
