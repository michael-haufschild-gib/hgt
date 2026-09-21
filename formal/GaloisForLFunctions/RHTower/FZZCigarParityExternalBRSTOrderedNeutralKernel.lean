import GaloisForLFunctions.RHTower.FZZCigarParityExternalBRSTOrderedBranchPrimitive

/-!
# FZZ external-BRST ordered neutral branch kernel

The literal `W⁺` and `W⁻` external branch factors carry opposite compact
charges. At distinct cyclic positions their neutral product is not the
same-point product: its inner cyclic-arc integral retains the branch
primitive. This is the first source-faithful ordered object left after the
single-branch and same-point neutral-pair no-gos.
-/

open Complex MeasureTheory

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Distinct-angle neutral external-BRST branch kernel in cyclic order. -/
def fzzCigarExternalBRSTOrderedNeutralAngularKernel
    (k : ℝ) (j : ℂ) (p ν : ℤ) (s t : ℝ) : ℂ :=
  fzzCigarExternalBRSTPlusAngularBranchKernel k j p ν s *
    fzzCigarExternalBRSTMinusAngularBranchKernel k j p ν t

/-- The ordered neutral kernel is exactly the product of the two literal
opposite-charge compact holonomy characters. -/
theorem fzzCigarExternalBRSTOrderedNeutralAngularKernel_eq
    (k : ℝ) (j : ℂ) (p ν : ℤ) (s t : ℝ) :
    fzzCigarExternalBRSTOrderedNeutralAngularKernel k j p ν s t =
      RHTower.fzzTorusHolonomyCharacter p s *
        RHTower.fzzTorusHolonomyCharacter (-p) t := by
  rfl

/-- Integrating the first literal branch along the cyclic arc ending at the
second retains the nontrivial branch primitive. -/
theorem intervalIntegral_fzzCigarExternalBRSTOrderedNeutralAngularKernel_inner
    (k : ℝ) (j : ℂ) (p ν : ℤ) (t : ℝ) (hp : p ≠ 0) :
    (∫ s in (0 : ℝ)..t,
      fzzCigarExternalBRSTOrderedNeutralAngularKernel k j p ν s t) =
      ((RHTower.fzzTorusHolonomyCharacter p t - 1) /
        fzzCigarExternalBRSTAngularFrequency p) *
          RHTower.fzzTorusHolonomyCharacter (-p) t := by
  change (∫ s in (0 : ℝ)..t,
    RHTower.fzzTorusHolonomyCharacter p s *
      RHTower.fzzTorusHolonomyCharacter (-p) t) = _
  rw [intervalIntegral.integral_mul_const,
    intervalIntegral_fzzCigarExternalBRSTAngularBranch_to p t hp]

end

end GaloisForLFunctions.RHTower
