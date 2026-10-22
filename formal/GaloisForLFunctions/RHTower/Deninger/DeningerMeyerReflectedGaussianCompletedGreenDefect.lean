import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerReflectedGaussianResolvedAdmission
import GaloisForLFunctions.RHTower.Deninger.DeningerCompletedXiHellingerGammaGreenResolvedProvenance
import GaloisForLFunctions.RHTower.Deninger.DeningerMultiplier

/-!
# Completed Green defect of the reflected Meyer Gaussian horizon

The internal Green covariance fracture is a diagonal multiplier by
`2 Re(rho) - 1`.  Every actual Xi-divisor point lies in the open critical
strip, so this multiplier has norm at most one.  Consequently the algebraic
resolved Green defect extends to the full completed Xi carrier as a bounded
operator, with exact agreement on the finite graded source core.

We apply that completion to the fixed Paugam-reflection-invariant Meyer
Gaussian horizon vector.  Because the source grade is nonzero on every
divisor copy, the resulting single global completed Green-provenance vector
vanishes exactly when every Xi zero lies on the critical line.  Its actual
Calderon--Witt incidence image and resolved Hellinger--Gamma quotient class
therefore vanish exactly under RH.

These statements are unconditional identifications.  They construct the
global source object and close its completed comparison; they do not prove
the missing source-side transversality or Hermitian Gram domination that
would force the class to vanish.
-/

open Complex
open GaloisForLFunctions.HTGeometry

namespace RHTower
namespace DeningerMeyerGaussianGreen

noncomputable section

/-- The Green fracture is a contraction multiplier on the actual Xi divisor. -/
theorem norm_xiNearbyPoleDualityAdjunctionFracture_le_one
    (q : XiZeroCopy) :
    ‖xiNearbyPoleDualityAdjunctionFracture (q.1 : ℂ)‖ ≤ 1 := by
  rw [xiNearbyPoleDualityAdjunctionFracture_eq_two_re]
  simp only [norm_real, Real.norm_eq_abs]
  rw [abs_le]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  constructor <;> linarith

/-- Coefficientwise completed Riesz conjugation. -/
def deningerArithmeticCompletedRieszConjugation
    (a : XiDivisorL2) : XiDivisorL2 :=
  star a

@[simp]
theorem deningerArithmeticCompletedRieszConjugation_apply
    (a : XiDivisorL2) (q : XiZeroCopy) :
    deningerArithmeticCompletedRieszConjugation a q =
      (starRingEnd ℂ) (a q) := by
  rfl

/-- Bounded completion of the algebraic Hodge covariance defect. -/
def deningerArithmeticCompletedHodgeCovarianceDefect
    (a : XiDivisorL2) : XiDivisorL2 :=
  deningerMultiplier norm_xiNearbyPoleDualityAdjunctionFracture_le_one
    (deningerArithmeticOrientedHodgeLp a)

@[simp]
theorem deningerArithmeticCompletedHodgeCovarianceDefect_apply
    (a : XiDivisorL2) (q : XiZeroCopy) :
    deningerArithmeticCompletedHodgeCovarianceDefect a q =
      xiNearbyPoleDualityAdjunctionFracture (q.1 : ℂ) *
        deningerArithmeticOrientedHodgeLp a q := by
  exact deningerMultiplier_apply
    norm_xiNearbyPoleDualityAdjunctionFracture_le_one
    (deningerArithmeticOrientedHodgeLp a) q

/-- Uniform capacity: the completed Hodge fracture has operator bound one. -/
theorem norm_deningerArithmeticCompletedHodgeCovarianceDefect_le
    (a : XiDivisorL2) :
    ‖deningerArithmeticCompletedHodgeCovarianceDefect a‖ ≤ ‖a‖ := by
  change ‖deningerMultiplierMap
      norm_xiNearbyPoleDualityAdjunctionFracture_le_one
      (deningerArithmeticOrientedHodgeLp a)‖ ≤ ‖a‖
  calc
    _ ≤ 1 * ‖deningerArithmeticOrientedHodgeLp a‖ :=
      deningerMultiplierMap_norm_le
        norm_xiNearbyPoleDualityAdjunctionFracture_le_one _
    _ = ‖a‖ := by
      rw [one_mul, norm_deningerArithmeticOrientedHodgeLp]

/-- Completed first Green defect: Hodge covariance after Riesz conjugation. -/
def deningerArithmeticCompletedGreenProvenance
    (a : XiDivisorL2) : XiDivisorL2 :=
  deningerArithmeticCompletedHodgeCovarianceDefect
    (deningerArithmeticCompletedRieszConjugation a)

@[simp]
theorem deningerArithmeticCompletedGreenProvenance_apply
    (a : XiDivisorL2) (q : XiZeroCopy) :
    deningerArithmeticCompletedGreenProvenance a q =
      xiNearbyPoleDualityAdjunctionFracture (q.1 : ℂ) *
        deningerArithmeticOrientedHodgeLp
          (deningerArithmeticCompletedRieszConjugation a) q := by
  rw [deningerArithmeticCompletedGreenProvenance,
    deningerArithmeticCompletedHodgeCovarianceDefect_apply]

/-- The completed Green provenance also has uniform capacity one. -/
theorem norm_deningerArithmeticCompletedGreenProvenance_le
    (a : XiDivisorL2) :
    ‖deningerArithmeticCompletedGreenProvenance a‖ ≤ ‖a‖ := by
  calc
    _ ≤ ‖deningerArithmeticCompletedRieszConjugation a‖ :=
      norm_deningerArithmeticCompletedHodgeCovarianceDefect_le _
    _ = ‖a‖ := by
      rw [deningerArithmeticCompletedRieszConjugation]
      exact norm_star a

/-- Canonical coefficient-preserving inclusion of finite graded Xi classes. -/
def deningerArithmeticGradedH1ToCompleted :
    DeningerArithmeticGradedH1 →ₗ[ℂ] XiDivisorL2 :=
  Finsupp.lsum ℂ fun q =>
    lp.lsingle (E := fun _ : XiZeroCopy => ℂ) 2 q

@[simp]
theorem deningerArithmeticGradedH1ToCompleted_single
    (q : XiZeroCopy) (c : ℂ) :
    deningerArithmeticGradedH1ToCompleted (Finsupp.single q c) =
      lp.single 2 q c := by
  simp [deningerArithmeticGradedH1ToCompleted]

@[simp]
theorem deningerArithmeticGradedH1ToCompleted_apply
    (a : DeningerArithmeticGradedH1) (q : XiZeroCopy) :
    deningerArithmeticGradedH1ToCompleted a q = a q := by
  classical
  induction a using Finsupp.induction with
  | zero =>
      change (0 : ℂ) = 0
      rfl
  | single_add r c a hr _hc ih =>
      rw [map_add, lp.coeFn_add, Pi.add_apply,
        deningerArithmeticGradedH1ToCompleted_single, ih]
      by_cases hrq : r = q
      · subst r
        simp
      · simp [lp.single_apply, hrq]

theorem deningerArithmeticGradedH1ToCompleted_injective :
    Function.Injective deningerArithmeticGradedH1ToCompleted := by
  intro a b hab
  ext q
  have hq := congrArg (fun x : XiDivisorL2 => x q) hab
  simpa using hq

/-- Completed Green provenance agrees exactly with the algebraic Green defect on finite jets. -/
theorem deningerArithmeticCompletedGreenProvenance_finite
    (a : DeningerArithmeticGradedH1) :
    deningerArithmeticCompletedGreenProvenance
        (deningerArithmeticGradedH1ToCompleted a) =
      deningerArithmeticGradedH1ToCompleted
        (deningerArithmeticGradedHodgeCovarianceDefect
          (deningerArithmeticGradedRieszConjugation a)) := by
  ext q
  rw [deningerArithmeticCompletedGreenProvenance_apply,
    deningerArithmeticOrientedHodgeLp_apply,
    deningerArithmeticCompletedRieszConjugation_apply,
    deningerArithmeticGradedH1ToCompleted_apply,
    starRingEnd_self_apply,
    deningerArithmeticGradedH1ToCompleted_apply,
    deningerArithmeticGradedHodgeCovarianceDefect_apply,
    deningerArithmeticGradedOrientedHodge_apply,
    deningerArithmeticGradedRieszConjugation_apply,
    starRingEnd_self_apply]

/-- Completed two-channel resolved Green defect. -/
def deningerArithmeticCompletedGreenResolvedDefect
    (a : XiDivisorL2) : XiDivisorL2 × XiDivisorL2 :=
  resolvedDefectAntidiagonal (R := ℂ)
    (deningerArithmeticCompletedGreenProvenance a)

/-- The bounded completion restricts to the exact algebraic two-channel Green defect. -/
theorem deningerArithmeticCompletedGreenResolvedDefect_finite
    (a : DeningerArithmeticGradedH1) :
    deningerArithmeticCompletedGreenResolvedDefect
        (deningerArithmeticGradedH1ToCompleted a) =
      (deningerArithmeticGradedH1ToCompleted
          (deningerArithmeticGreenResolvedDefect a).1,
        deningerArithmeticGradedH1ToCompleted
          (deningerArithmeticGreenResolvedDefect a).2) := by
  rw [deningerArithmeticCompletedGreenResolvedDefect,
    deningerArithmeticGreenResolvedDefect_eq_antidiagonal,
    deningerArithmeticCompletedGreenProvenance_finite]
  apply Prod.ext
  · rfl
  · exact (map_neg deningerArithmeticGradedH1ToCompleted _).symm

/-- Completed resolved defect remains antidiagonal and is lost by codiagonalization. -/
theorem deningerArithmeticCompletedGreenResolvedDefect_codiagonal
    (a : XiDivisorL2) :
    resolvedDefectCodiagonal (R := ℂ)
      (deningerArithmeticCompletedGreenResolvedDefect a) = 0 := by
  simp [deningerArithmeticCompletedGreenResolvedDefect,
    resolvedDefectCodiagonal, resolvedDefectAntidiagonal]

/-- Fixed source-horizon Green provenance vector. -/
def reflectedGaussianHorizonGreenProvenance : XiDivisorL2 :=
  deningerArithmeticCompletedGreenProvenance
    reflectedGaussianHorizonGradeL2

/-- One source-defined completed vector detects every horizontal Xi displacement. -/
theorem reflectedGaussianHorizonGreenProvenance_eq_zero_iff_riemannHypothesis :
    reflectedGaussianHorizonGreenProvenance = 0 ↔
      RiemannHypothesis := by
  constructor
  · intro hzero
    apply deningerArithmeticGreenResolvedDefect_vanishes_iff_riemannHypothesis.mp
    intro a
    rw [deningerArithmeticGreenResolvedDefect_eq_antidiagonal]
    have hfracture : ∀ q : XiZeroCopy,
        xiNearbyPoleDualityAdjunctionFracture (q.1 : ℂ) = 0 := by
      intro q
      have hq := congrArg (fun x : XiDivisorL2 => x q) hzero
      rw [reflectedGaussianHorizonGreenProvenance,
        deningerArithmeticCompletedGreenProvenance_apply] at hq
      apply (mul_eq_zero.mp hq).resolve_right
      rw [deningerArithmeticOrientedHodgeLp_apply,
        deningerArithmeticCompletedRieszConjugation_apply]
      apply mul_ne_zero
      · exact neg_ne_zero.mpr (deningerArithmeticFEOrientation_ne_zero q)
      · rw [starRingEnd_self_apply]
        exact reflectedGaussianHorizonGrade_ne_zero
          (xiZeroCopyReflectEquiv q)
    have hfirst :
        deningerArithmeticGradedHodgeCovarianceDefect
          (deningerArithmeticGradedRieszConjugation a) = 0 := by
      ext q
      rw [deningerArithmeticGradedHodgeCovarianceDefect_apply,
        hfracture q, zero_mul]
      rfl
    rw [hfirst]
    simp [resolvedDefectAntidiagonal]
  · intro hRH
    ext q
    rw [reflectedGaussianHorizonGreenProvenance,
      deningerArithmeticCompletedGreenProvenance_apply]
    have hline := xi_divisor_support_re_eq_half_of_rh hRH q.1
    rw [(xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
      (q.1 : ℂ)).2 hline, zero_mul]
    rfl

theorem reflectedGaussianHorizonGreenProvenance_ne_zero_iff_not_riemannHypothesis :
    reflectedGaussianHorizonGreenProvenance ≠ 0 ↔
      ¬ RiemannHypothesis := by
  exact not_congr
    reflectedGaussianHorizonGreenProvenance_eq_zero_iff_riemannHypothesis

/-- Actual completed incidence image of the fixed source-horizon Green defect. -/
def reflectedGaussianHorizonGreenIncidence
    (p q : Nat.Primes) (hpq : p ≠ q) :
    DeningerCalderonWittCrossPrimeXiIncidenceCompletion p q hpq :=
  deningerCompletedXiToCrossPrimeIncidenceCompletion p q hpq
    reflectedGaussianHorizonGreenProvenance

theorem reflectedGaussianHorizonGreenIncidence_eq_zero_iff_riemannHypothesis
    (p q : Nat.Primes) (hpq : p ≠ q) :
    reflectedGaussianHorizonGreenIncidence p q hpq = 0 ↔
      RiemannHypothesis := by
  constructor
  · intro hzero
    apply reflectedGaussianHorizonGreenProvenance_eq_zero_iff_riemannHypothesis.mp
    apply (deningerCompletedXiToCrossPrimeIncidenceCompletion p q hpq).injective
    simpa [reflectedGaussianHorizonGreenIncidence] using hzero
  · intro hRH
    rw [reflectedGaussianHorizonGreenIncidence,
      reflectedGaussianHorizonGreenProvenance_eq_zero_iff_riemannHypothesis.mpr hRH]
    exact map_zero _

/-- Resolved Hellinger--Gamma class of the actual fixed source-horizon Green defect. -/
def reflectedGaussianHorizonGreenResolvedClass
    (p q : Nat.Primes) (hpq : p ≠ q) (a : ℝ) :=
  hellingerGammaResolvedProvenanceQuotientSource hpq a
    (reflectedGaussianHorizonGreenIncidence p q hpq)

/-- One global source-derived quotient class vanishes exactly under RH. -/
theorem reflectedGaussianHorizonGreenResolvedClass_eq_zero_iff_riemannHypothesis
    (p q : Nat.Primes) (hpq : p ≠ q) (a : ℝ) :
    reflectedGaussianHorizonGreenResolvedClass p q hpq a = 0 ↔
      RiemannHypothesis := by
  rw [← reflectedGaussianHorizonGreenIncidence_eq_zero_iff_riemannHypothesis
    p q hpq]
  constructor
  · intro hzero
    apply hellingerGammaResolvedProvenanceQuotientSource_injective hpq a
    simpa [reflectedGaussianHorizonGreenResolvedClass] using hzero
  · intro hzero
    rw [reflectedGaussianHorizonGreenResolvedClass, hzero]
    exact map_zero _

end

end DeningerMeyerGaussianGreen
end RHTower
