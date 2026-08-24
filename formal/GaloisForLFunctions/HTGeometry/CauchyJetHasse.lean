import GaloisForLFunctions.HTGeometry.HasseFamily
import GaloisForLFunctions.HTGeometry.MomentFiberPickSchurPhase

/-!
# Hasse principle for complete Cauchy jets

At any fixed nonreal node, the complete derivative profile of the resolvent transform determines a
real probability measure.  Consequently distinct probability laws differ at one finite derivative
order at every such node.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

noncomputable section

/-- Resolvent derivatives at one nonreal node form a Hasse family for real probability laws. -/
noncomputable def completeCauchyJetHasseFamily (a : ℂ) (ha : a.im ≠ 0) :
    HasseFamily (ProbabilityMeasure ℝ) ℕ where
  Local _ := ℂ
  profile mu k := iteratedDeriv k (resolventTransform (mu : Measure ℝ)) a
  profile_injective := by
    intro mu nu h
    apply Subtype.ext
    exact momentBoundary_completeResolvent_separates
      (mu := (mu : Measure ℝ)) (nu := (nu : Measure ℝ)) a ha (congrFun h)

/-- Probability laws agree exactly when their complete Cauchy jets agree at one nonreal node. -/
theorem probabilityMeasure_congr_completeCauchyJet_hasse_iff
    (a : ℂ) (ha : a.im ≠ 0) (mu nu : ProbabilityMeasure ℝ) :
    (∀ k : ℕ,
      iteratedDeriv k (resolventTransform (mu : Measure ℝ)) a =
        iteratedDeriv k (resolventTransform (nu : Measure ℝ)) a) ↔ mu = nu :=
  (completeCauchyJetHasseFamily a ha).pointwise_eq_iff mu nu

/-- Unequal probability laws differ at one finite Cauchy-derivative order at the chosen node. -/
theorem probabilityMeasure_ne_iff_exists_completeCauchyJet_ne
    (a : ℂ) (ha : a.im ≠ 0) (mu nu : ProbabilityMeasure ℝ) :
    mu ≠ nu ↔ ∃ k : ℕ,
      iteratedDeriv k (resolventTransform (mu : Measure ℝ)) a ≠
        iteratedDeriv k (resolventTransform (nu : Measure ℝ)) a :=
  (completeCauchyJetHasseFamily a ha).ne_iff_exists_local_ne mu nu

end


end GaloisForLFunctions.HTGeometry
