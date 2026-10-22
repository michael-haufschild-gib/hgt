import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaEigenODE
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaEigenTransform
import GaloisForLFunctions.RHTower.XiQuotientRealDecay
import GaloisForLFunctions.RHTower.XiThetaEigenGramLaw
import GaloisForLFunctions.RHTower.XiWeilHilbertCore
import GaloisForLFunctions.RHTower.XiWeilPositivityCriterion
import GaloisForLFunctions.RHTower.XiWeilResolventSource

/-!
# Canonical Weil polarization of the Hedenmalm theta pair

This capstone assembles the unconditional algebraic theorem: the multiplicity-exact centered Weil
form is Hermitian, kills the theta constraint on both sides, and makes centered differentiation
formally symmetric.  Its nonnegativity is equivalent to RH, while positive definiteness on every
finite theta-eigenfunction span is equivalent to RH plus simplicity.  Imported source modules give
the exact prime--Gamma Cauchy-core realization, Hilbert evaluation carrier, time-side ODE, decay,
and removable-quotient transform.
-/

open MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- Positive definiteness of the Weil form on every nonzero finite combination of actual theta
eigenfunction quotients. -/
def HedenmalmThetaEigenSpanPositiveDefinite : Prop :=
  ∀ (A : Finset ℂ) (c : ℂ → ℂ),
    (∀ alpha ∈ A, XiC alpha = 0) →
    (∃ alpha ∈ A, c alpha ≠ 0) →
      0 < (xiWeilPolarization
        (fun z ↦ ∑ alpha ∈ A, c alpha * xiThetaEigenFourier alpha z)
        (fun z ↦ ∑ beta ∈ A, c beta * xiThetaEigenFourier beta z)).re

/-- **Canonical Hedenmalm--Weil polarization law.**  Every clause is unconditional and the two
terminal equivalences expose, rather than assume, the exact RH and RH-plus-simplicity content. -/
theorem hedenmalmPairWeilPolarizationLaw :
    (∀ F G : ℂ → ℂ,
      xiWeilPolarization G F = (starRingEnd ℂ) (xiWeilPolarization F G)) ∧
    (∀ F G : ℂ → ℂ,
      xiWeilPolarization (fun z ↦ -z * F z) G =
        xiWeilPolarization F (fun z ↦ -z * G z)) ∧
    (∀ F : ℂ → ℂ,
      xiWeilPolarization XiC F = 0 ∧ xiWeilPolarization F XiC = 0) ∧
    (RiemannHypothesis ↔
      ∀ F : ℂ → ℂ, XiWeilSquareSummable F →
        0 ≤ (xiWeilPolarization F F).re) ∧
    (HedenmalmThetaEigenSpanPositiveDefinite ↔
      RiemannHypothesis ∧ ∀ alpha : ℂ, XiC alpha = 0 → deriv XiC alpha ≠ 0) := by
  refine ⟨xiWeilPolarization_conj_symm,
    xiWeilPolarization_spectralMultiply, ?_,
    riemannHypothesis_iff_xiWeilPolarization_nonneg, ?_⟩
  · intro F
    exact ⟨xiWeilPolarization_XiC_left F, xiWeilPolarization_XiC_right F⟩
  · exact forall_finsetSum_thetaEigen_re_pos_iff

/-- Quotient independence through the theta constraint, in both preimage variables. -/
theorem hedenmalmPairWeil_quotient_independence :
    ∀ (F G : ℂ → ℂ) (c d : ℂ),
      xiWeilPolarization (fun z ↦ F z + c * XiC z)
          (fun z ↦ G z + d * XiC z) = xiWeilPolarization F G := by
  intro F G c d
  rw [xiWeilPolarization_add_XiC_left,
    xiWeilPolarization_add_XiC_right]

/-- Under RH, the completed square-summable form is literally the Hilbert inner product on its
`ell²` evaluation carrier. -/
theorem hedenmalmPairWeil_hilbertCarrier_of_riemannHypothesis
    (hRH : RiemannHypothesis) (F G : ℂ → ℂ)
    (hF : XiWeilSquareSummable F) (hG : XiWeilSquareSummable G) :
    inner ℂ (xiWeilEvaluationLp G hG) (xiWeilEvaluationLp F hF) =
      xiWeilPolarization F G :=
  inner_xiWeilEvaluationLp_eq_polarization_of_riemannHypothesis hRH F G hF hG

end

end RHTower
