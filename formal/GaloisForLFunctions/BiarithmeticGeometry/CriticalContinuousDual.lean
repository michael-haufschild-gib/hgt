import GaloisForLFunctions.BiarithmeticGeometry.CriticalCoefficientDomain
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

/-!
# The continuous dual of the unreduced critical quotient is one-dimensional

The quotient retains its actual topology even though payment is not closed.
Pullback along its continuous quotient map turns each continuous functional
into an annihilator of the payment domain. The exact annihilator theorem
then expresses it as a unique scalar total evaluation. This gives an
explicit complex-linear equivalence of the continuous dual with the field.
-/

noncomputable section
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- The continuous dual of the actual unreduced coefficient quotient. -/
abbrev CriticalUnreducedContinuousDual :=
  (CriticalCoefficientSpace ⧸ criticalCoefficientDomain) →L[ℂ] ℂ

/-- Total evaluation descends continuously to the unreduced quotient itself. -/
def criticalQuotientTotalEvaluation : CriticalUnreducedContinuousDual :=
  criticalCoefficientDomain.liftQL criticalTotalEvaluation
    (fun _ hg => criticalTotalEvaluation_eq_zero_of_mem hg)

theorem criticalQuotientTotalEvaluation_mk (g : CriticalCoefficientSpace) :
    criticalQuotientTotalEvaluation (criticalCoefficientDomain.mkQ g) = criticalTotalEvaluation g := rfl

private theorem criticalQuotientTotalEvaluation_unit :
    criticalQuotientTotalEvaluation (criticalCoefficientDomain.mkQ (lp.single 1 0 (1 : ℂ))) = 1 := by
  rw [criticalQuotientTotalEvaluation_mk, criticalTotalEvaluation_single]

/-- Every continuous functional on the non-Hausdorff quotient is a scalar total evaluation. -/
theorem criticalUnreducedContinuousDual_classification (L : CriticalUnreducedContinuousDual)
    (q : CriticalCoefficientSpace ⧸ criticalCoefficientDomain) :
    L q = L (criticalCoefficientDomain.mkQ (lp.single 1 0 (1 : ℂ))) *
      criticalQuotientTotalEvaluation q := by
  let A := L.comp criticalCoefficientDomain.mkQL
  have hA : ∀ g ∈ criticalCoefficientDomain, A g = 0 := by
    intro g hg
    have hzero : criticalCoefficientDomain.mkQ g = 0 :=
      (Submodule.Quotient.mk_eq_zero criticalCoefficientDomain).mpr hg
    change L (criticalCoefficientDomain.mkQ g) = 0
    rw [hzero, map_zero]
  obtain ⟨g, rfl⟩ := criticalCoefficientDomain.mkQ_surjective q
  exact criticalCoefficientDomain_continuous_annihilator A hA g

/-- Evaluation on the unit coefficient class identifies the entire continuous dual with `ℂ`. -/
def criticalUnreducedContinuousDualEquiv : CriticalUnreducedContinuousDual ≃ₗ[ℂ] ℂ where
  toFun L := L (criticalCoefficientDomain.mkQ (lp.single 1 0 (1 : ℂ)))
  invFun z := z • criticalQuotientTotalEvaluation
  left_inv L := by
    ext q
    change L (criticalCoefficientDomain.mkQ (lp.single 1 0 (1 : ℂ))) *
      criticalQuotientTotalEvaluation q = L q
    exact (criticalUnreducedContinuousDual_classification L q).symm
  right_inv z := by
    change z * criticalQuotientTotalEvaluation
      (criticalCoefficientDomain.mkQ (lp.single 1 0 (1 : ℂ))) = z
    rw [criticalQuotientTotalEvaluation_unit, mul_one]
  map_add' L R := rfl
  map_smul' z L := rfl

instance : FiniteDimensional ℂ CriticalUnreducedContinuousDual :=
  FiniteDimensional.of_injective criticalUnreducedContinuousDualEquiv.toLinearMap
    criticalUnreducedContinuousDualEquiv.injective

/-- Continuity sees exactly one complex dimension despite the continuum algebraic defect. -/
theorem finrank_criticalUnreducedContinuousDual : Module.finrank ℂ CriticalUnreducedContinuousDual = 1 := by
  simpa only [Module.finrank_self] using criticalUnreducedContinuousDualEquiv.finrank_eq

/-- Every continuous quotient functional vanishes on every zero-total coefficient class. -/
theorem criticalUnreducedContinuousDual_vanishes_on_closure (L : CriticalUnreducedContinuousDual)
    (g : CriticalCoefficientSpace) (hg : g ∈ criticalCoefficientDomain.topologicalClosure) :
    L (criticalCoefficientDomain.mkQ g) = 0 := by
  have hz : criticalTotalEvaluation g = 0 := by
    change g ∈ closure (criticalCoefficientDomain : Set CriticalCoefficientSpace) at hg
    rwa [closure_criticalCoefficientDomain] at hg
  rw [criticalUnreducedContinuousDual_classification, criticalQuotientTotalEvaluation_mk, hz, mul_zero]

end GaloisForLFunctions.BiarithmeticGeometry

