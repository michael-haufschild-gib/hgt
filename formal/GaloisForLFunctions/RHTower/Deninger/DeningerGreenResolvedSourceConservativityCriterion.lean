import GaloisForLFunctions.RHTower.Deninger.DeningerGreenResolvedDefectLaw
import GaloisForLFunctions.HTGeometry.ResolvedDefectConservationLaw

/-!
# Resolved source conservativity criterion for the Riemann divisor

The finite arithmetic Green map is already Frobenius-covariant because its two transported factor
defects cancel.  This file retains those defects as a resolved pair and proves the exact logical
frontier: RH is componentwise vanishing of the resolved pair, and follows from source support in
any sector on which codiagonal augmentation is conservative.
-/

open Complex

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Total Green covariance is the zero codiagonal of the resolved defect, unconditionally. -/
@[simp]
theorem resolvedDefectCodiagonal_deningerArithmeticGreenResolvedDefect
    (a : DeningerArithmeticGradedH1) :
    resolvedDefectCodiagonal (R := ℂ)
        (deningerArithmeticGreenResolvedDefect a) = 0 := by
  exact deningerArithmeticGreen_internalDefects_cancel a

/-- **Resolved Green criterion.**  RH is exactly componentwise vanishing of the resolved Green
defect.  This is strictly stronger than its unconditional zero codiagonal. -/
theorem deningerArithmeticGreenResolvedDefect_eq_zero_iff_riemannHypothesis :
    (∀ a, deningerArithmeticGreenResolvedDefect a = 0) ↔ RiemannHypothesis := by
  constructor
  · intro hresolved
    rw [← deningerArithmeticGradedTheta_orientedHodge_iff_riemannHypothesis]
    intro b
    obtain ⟨a, rfl⟩ := deningerArithmeticGradedRieszConjugation.surjective b
    have hfst := congrArg Prod.fst (hresolved a)
    change deningerArithmeticGradedHodgeCovarianceDefect
        (deningerArithmeticGradedRieszConjugation a) = 0 at hfst
    exact sub_eq_zero.mp hfst
  · intro hRH a
    rw [← deningerArithmeticGradedTheta_orientedHodge_iff_riemannHypothesis] at hRH
    apply Prod.ext
    · change deningerArithmeticGradedHodgeCovarianceDefect
        (deningerArithmeticGradedRieszConjugation a) = 0
      exact sub_eq_zero.mpr (hRH _)
    · have hcancel := deningerArithmeticGreen_internalDefects_cancel a
      have hfirst : deningerArithmeticGradedHodgeCovarianceDefect
          (deningerArithmeticGradedRieszConjugation a) = 0 :=
        sub_eq_zero.mpr (hRH _)
      rw [hfirst, zero_add] at hcancel
      exact hcancel

/-- **Resolved source-support criterion for RH.**  If every actual Green defect belongs to a
source-selected sector on which codiagonal augmentation is conservative, then RH follows. -/
theorem riemannHypothesis_of_greenResolvedDefect_supported_in_conservativeSector
    (S : Set (DeningerArithmeticGradedH1 × DeningerArithmeticGradedH1))
    (hsupport : ∀ a, deningerArithmeticGreenResolvedDefect a ∈ S)
    (hconservative : ∀ z ∈ S,
      resolvedDefectCodiagonal (R := ℂ) z = 0 → z = 0) :
    RiemannHypothesis := by
  rw [← deningerArithmeticGreenResolvedDefect_eq_zero_iff_riemannHypothesis]
  intro a
  exact hconservative _ (hsupport a)
    (resolvedDefectCodiagonal_deningerArithmeticGreenResolvedDefect a)

end

end RHTower
