import GaloisForLFunctions.AdelicKreinGeometry.Haar.PeriodDefects
import GaloisForLFunctions.HeckeKreinToeplitz.Index.FiniteColumns
import GaloisForLFunctions.BiarithmeticGeometry.Affine.PolynomialAntidifferences
import GaloisForLFunctions.BiarithmeticGeometry.Affine.PolynomialFibres
import GaloisForLFunctions.HeckeKreinToeplitz.Index.FiniteRankPerturbations

/-!
# Canonical polynomial corrections with zero axis readings

A Hermitian finite-index affine kernel with periodic translation reading has a finite-dimensional
period-defect representation. Its normalized polynomial primitive has finite column rank.
Commensurable rational periods force this primitive to be Hermitian, and its two axis readings
vanish. Subtraction gives a finite-index kernel invariant under integer translations on both sides.
-/

open Module
open GaloisForLFunctions.HeckeKreinToeplitz GaloisForLFunctions.BiarithmeticGeometry
open GaloisForLFunctions.ArithmeticPositiveDuality
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

/-- The right integer-period difference of an affine kernel. -/
def translationPeriodKernel (k : AffineGroupQ → ℂ) (g : AffineGroupQ) : ℂ :=
  k (g * translation 1) - k g

/-- The affine action on the full period-defect orbit. -/
def periodDefectRepresentation (k : AffineGroupQ → ℂ) :
    AffineGroupQ →* End ℂ (affinePeriodSpace k) where
  toFun g := (kernelColumnRepresentation k g).restrict (affinePeriodSpace_invariant k g)
  map_one' := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (map_one (kernelColumnRepresentation k)) x
  map_mul' g h := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (map_mul (kernelColumnRepresentation k) g h) x

def periodDefectVector (k : AffineGroupQ → ℂ) : affinePeriodSpace k :=
  ⟨translationPeriodDefect k 0,
    translationPeriodSpace_le_affinePeriodSpace k (Submodule.subset_span ⟨0, rfl⟩)⟩

def periodDefectObservation (k : AffineGroupQ → ℂ) : affinePeriodSpace k →ₗ[ℂ] ℂ :=
  (kernelColumnObservation k).comp (affinePeriodSpace k).subtype

/-- The period difference is a coefficient of its affine defect representation. -/
theorem periodDefect_coefficient (k : AffineGroupQ → ℂ) (g : AffineGroupQ) :
    periodDefectObservation k (periodDefectRepresentation k g (periodDefectVector k)) =
      translationPeriodKernel k g := by
  change k (((g⁻¹ * 1)⁻¹) * translation (0 + 1)) -
      k (((g⁻¹ * 1)⁻¹) * translation 0) = k (g * translation 1) - k g
  rw [mul_one, inv_inv, zero_add, translation_zero, mul_one]

/-- The complete right-period difference has finite column rank. -/
theorem finite_columnSpan_translationPeriodKernel {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r)
    (hper : ∀ b : ℚ, k (translation (b + 1)) = k (translation b)) :
    Module.Finite ℂ (kernelColumnSpan (translationPeriodKernel k)) := by
  letI := (finite_affinePeriodSpace hk hi hper).1
  have he : (fun g => periodDefectObservation k
      (periodDefectRepresentation k g (periodDefectVector k))) = translationPeriodKernel k :=
    funext (periodDefect_coefficient k)
  rw [← he]
  exact finite_columnSpan_of_representation (periodDefectRepresentation k)
    (periodDefectObservation k) (periodDefectVector k)

#print axioms periodDefect_coefficient
#print axioms finite_columnSpan_translationPeriodKernel

/-- Normalized polynomial corrections of a Hermitian kernel are Hermitian. -/
theorem isHermKernel_of_polynomial_correction {k q : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) (hq : HasPolynomialTranslationFibres q)
    (hd : ∀ u : ℚˣ, q (dilation u) = 0)
    (hp : ∀ g, k (g * translation 1) - q (g * translation 1) = k g - q g) :
    IsHermKernel q := by
  let h : AffineGroupQ → ℂ := fun g => k g - q g
  let hstar : AffineGroupQ → ℂ := fun g => starRingEnd ℂ (h g⁻¹)
  have hinv (g : AffineGroupQ) : h (g * (translation 1)⁻¹) = h g := by
    have he := hp (g * (translation 1)⁻¹)
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using he.symm
  have hsym (g : AffineGroupQ) :
      h g - hstar g = starRingEnd ℂ (q g⁻¹) - q g := by
    simp only [h, hstar, map_sub]
    rw [hk g, starRingEnd_self_apply]
    ring
  have hzero (g : AffineGroupQ) : starRingEnd ℂ (q g⁻¹) - q g = 0 := by
    -- On a rational slope, the Hermitian defect is a polynomial with a nonzero common period.
    let u := Units.mk0 (affSlope g) (affSlope_ne_zero g)
    obtain ⟨P, hP⟩ := (hq.adjoint.sub hq) u
    let f : ℚ → ℂ := fun b => h (translation b * dilation u)
    let fstar : ℚ → ℂ := fun b => hstar (translation b * dilation u)
    have hf : Function.Periodic f (u : ℚ) := by
      intro b
      change h (translation (b + u) * dilation u) = h (translation b * dilation u)
      rw [translation_fibre_shift_right]
      exact hp _
    have hfstar : Function.Periodic fstar 1 := by
      intro b
      change starRingEnd ℂ (h (translation (b + 1) * dilation u)⁻¹) =
        starRingEnd ℂ (h (translation b * dilation u)⁻¹)
      have he : translation (b + 1) * dilation u =
          translation 1 * (translation b * dilation u) := by
        rw [← mul_assoc, ← translation_add, add_comm b 1]
      rw [he, _root_.mul_inv_rev, hinv]
    have hpoly (b : ℚ) : P.eval (b : ℂ) = f b - fstar b := by
      rw [← hP]
      exact (hsym _).symm
    have he := polynomial_difference_of_rational_periods P f fstar u.ne_zero hf hfstar
      hpoly (affShift g)
    change h (translation (affShift g) * dilation u) -
      hstar (translation (affShift g) * dilation u) =
      h (translation 0 * dilation u) - hstar (translation 0 * dilation u) at he
    rw [← eq_translation_mul_dilation g, translation_zero, one_mul, hsym, hsym] at he
    rw [← map_inv, hd, hd, map_zero, sub_self] at he
    exact he
  intro g
  have he := congrArg (starRingEnd ℂ) (sub_eq_zero.mp (hzero g))
  simpa only [starRingEnd_self_apply] using he

#print axioms isHermKernel_of_polynomial_correction

/-- The full period difference has a finite-rank polynomial primitive, normalized on dilations. -/
theorem exists_finite_rank_period_antidifference {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r)
    (hper : ∀ b : ℚ, k (translation (b + 1)) = k (translation b)) :
    ∃ q : AffineGroupQ → ℂ, Module.Finite ℂ (kernelColumnSpan q) ∧
      HasPolynomialTranslationFibres q ∧ (∀ u : ℚˣ, q (dilation u) = 0) ∧
      ∀ g, q (g * translation 1) - q g = k (g * translation 1) - k g := by
  letI := (finite_affinePeriodSpace hk hi hper).1
  let q := affineCoefficientPrimitive (periodDefectRepresentation k)
    (periodDefectObservation k) (periodDefectVector k)
  letI : Module.Finite ℂ (kernelColumnSpan q) :=
    finite_columnSpan_affineCoefficientPrimitive (periodDefectRepresentation k)
      (periodDefectObservation k) (periodDefectVector k)
  refine ⟨q, inferInstance, hasPolynomialTranslationFibres_of_finite_columns q,
    affineCoefficientPrimitive_dilation (periodDefectRepresentation k)
      (periodDefectObservation k) (periodDefectVector k), fun g => ?_⟩
  rw [affineCoefficientPrimitive_difference, periodDefect_coefficient]
  rfl

/-- A polynomial correction is uniquely determined by its difference and dilation normalization. -/
theorem polynomial_period_correction_unique {q q' : AffineGroupQ → ℂ}
    (hq : HasPolynomialTranslationFibres q) (hq' : HasPolynomialTranslationFibres q')
    (hd : ∀ u : ℚˣ, q (dilation u) = 0) (hd' : ∀ u : ℚˣ, q' (dilation u) = 0)
    (he : ∀ g, q (g * translation 1) - q g = q' (g * translation 1) - q' g) : q = q' := by
  have hz := eq_zero_of_polynomial_fibres_right_period (hq.sub hq')
    (fun u => by rw [hd, hd', sub_self]) (fun g => by linear_combination he g)
  funext g
  exact sub_eq_zero.mp (congrFun hz g)

/-- Periodicity on the translation axis forces its normalized polynomial primitive to vanish. -/
theorem polynomial_period_correction_translation {k q : AffineGroupQ → ℂ}
    (hq : HasPolynomialTranslationFibres q) (hd : ∀ u : ℚˣ, q (dilation u) = 0)
    (he : ∀ g, q (g * translation 1) - q g = k (g * translation 1) - k g)
    (hper : ∀ b : ℚ, k (translation (b + 1)) = k (translation b)) (b : ℚ) :
    q (translation b) = 0 := by
  obtain ⟨P, hP⟩ := hq 1
  have hP' (b : ℚ) : q (translation b) = P.eval (b : ℂ) := by
    simpa only [map_one, mul_one] using hP b
  have hp : Function.Periodic (fun b : ℚ => P.eval (b : ℂ)) 1 := by
    intro t
    change P.eval ((t + 1 : ℚ) : ℂ) = P.eval (t : ℂ)
    rw [← hP', ← hP']
    have h := he (translation t)
    simp only [← translation_add, hper, sub_self] at h
    exact sub_eq_zero.mp h
  have hc := eq_C_of_rational_period one_ne_zero P hp
  rw [hP', hc, Polynomial.eval_C]
  have h0 := hP' 0
  rw [translation_zero, ← map_one dilation, hd, Rat.cast_zero] at h0
  exact h0.symm

#print axioms exists_finite_rank_period_antidifference
#print axioms polynomial_period_correction_unique
#print axioms polynomial_period_correction_translation

/-- Remove the unique zero-axis polynomial part to obtain a finite-index bi-periodic kernel. -/
theorem exists_zero_axis_polynomial_correction {k : AffineGroupQ → ℂ}
    (hk : IsHermKernel k) {r : ℕ} (hi : negIndex k ≤ r)
    (hper : ∀ b : ℚ, k (translation (b + 1)) = k (translation b)) :
    ∃ q : AffineGroupQ → ℂ, Module.Finite ℂ (kernelColumnSpan q) ∧
      HasPolynomialTranslationFibres q ∧ IsHermKernel q ∧
      (∀ b : ℚ, q (translation b) = 0) ∧ (∀ u : ℚˣ, q (dilation u) = 0) ∧
      IsHermKernel (fun g => k g - q g) ∧
      negIndex (fun g => k g - q g) ≤ (r : ℕ∞) + finrank ℂ (kernelColumnSpan q) ∧
      (∀ g, k (g * translation 1) - q (g * translation 1) = k g - q g) ∧
      (∀ g, k (translation 1 * g) - q (translation 1 * g) = k g - q g) := by
  obtain ⟨q, hfinite, hq, hd, he⟩ := exists_finite_rank_period_antidifference hk hi hper
  letI := hfinite
  have hp (g : AffineGroupQ) :
      k (g * translation 1) - q (g * translation 1) = k g - q g := by
    linear_combination -(he g)
  have hqHerm := isHermKernel_of_polynomial_correction hk hq hd hp
  have hh : IsHermKernel (fun g => k g - q g) := by
    intro g
    change k g⁻¹ - q g⁻¹ = starRingEnd ℂ (k g - q g)
    rw [hk, hqHerm, map_sub]
  refine ⟨q, hfinite, hq, hqHerm, polynomial_period_correction_translation hq hd he hper,
    hd, hh, (negIndex_sub_le_add_finrank k q).trans (_root_.add_le_add hi le_rfl), hp, ?_⟩
  intro g
  have hm (a : AffineGroupQ) :
      k (a * (translation 1)⁻¹) - q (a * (translation 1)⁻¹) = k a - q a := by
    have h := hp (a * (translation 1)⁻¹)
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using h.symm
  have h := hh (translation 1 * g)
  change k (translation 1 * g)⁻¹ - q (translation 1 * g)⁻¹ =
    starRingEnd ℂ (k (translation 1 * g) - q (translation 1 * g)) at h
  have hg : k g⁻¹ - q g⁻¹ = starRingEnd ℂ (k g - q g) := hh g
  rw [_root_.mul_inv_rev, hm, hg] at h
  have hc := congrArg (starRingEnd ℂ) h.symm
  simpa only [starRingEnd_self_apply] using hc

#print axioms exists_zero_axis_polynomial_correction
end GaloisForLFunctions.AdelicKreinGeometry
