import GaloisForLFunctions.ArithmeticDefectRigidity.PositiveOriginMixturesAreFaithful
import GaloisForLFunctions.ArithmeticDefectRigidity.TheClosedCofactorAnnihilatorHasNoCountableIndex
import GaloisForLFunctions.ArithmeticOrientationTheory.WienerCoefficientEvaluation

/-!
# Positive origin boundaries have continuum index

Injective continuous Wiener cyclic maps force the step module and every
positive origin mixture to have infinite Hilbert dimension and continuum
annihilator-quotient rank.
-/
section

noncomputable section
set_option autoImplicit false
open scoped NNReal
open GaloisForLFunctions.ArithmeticOrientationTheory
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticDefectRigidity

private theorem faithful_wiener_orbit_rank
    {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (q : WienerAlgebraAt (1 / 2) →L[ℂ] H) (hq : Function.Injective q)
    (I : Ideal (WienerAlgebraAt (1 / 2))) (hI : I = ⊥) :
    Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸ I) = Cardinal.continuum := by
  have hrange : ¬ FiniteDimensional ℂ q.range := by
    intro h
    letI := h
    let e := LinearEquiv.ofInjective q.toLinearMap hq
    exact WienerAlgebraAt.not_finiteDimensional (1 / 2)
      (FiniteDimensional.of_injective e.toLinearMap e.injective)
  have hker : q.ker = I.restrictScalars ℂ := by
    rw [LinearMap.ker_eq_bot.mpr hq, hI]
    rfl
  have e := q.toLinearMap.quotKerEquivRange
  change (WienerAlgebraAt (1 / 2) ⧸ q.ker) ≃ₗ[ℂ] q.range at e
  rw [hker] at e
  have e' : (WienerAlgebraAt (1 / 2) ⧸ I) ≃ₗ[ℂ] q.range := e
  rw [e'.rank_eq]
  exact rank_hilbert_image_eq_continuum q (WienerAlgebraAt.cardinal_le_continuum (1 / 2)) hrange

namespace OriginStepModule

/-- The continuous cyclic orbit map of the origin-step module. -/
def cyclicLinear : WienerAlgebraAt (1 / 2) →L[ℂ] Hilbert :=
  (ContinuousLinearMap.apply ℂ Hilbert (KernelHilbert.vector complexKernel 1)).comp
    (CriticalKernelAction.representationLinear complexKernel complex_packet_dilation)

/-- The faithful step module is necessarily infinite-dimensional. -/
theorem not_finiteDimensional : ¬ FiniteDimensional ℂ Hilbert := by
  intro h
  letI := h
  exact WienerAlgebraAt.not_finiteDimensional (1 / 2)
    (FiniteDimensional.of_injective cyclicLinear.toLinearMap cyclic_map_injective)

/-- Its zero-annihilator quotient has exactly continuum Hamel rank. -/
theorem annihilator_quotient_rank :
    Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸ annihilator) = Cardinal.continuum :=
  faithful_wiener_orbit_rank cyclicLinear cyclic_map_injective annihilator annihilator_eq_bot

end OriginStepModule

namespace MixedOriginModule

/-- The continuous cyclic orbit map of a reset-origin mixture. -/
def cyclicLinear {ε : SubcriticalDamping} (L : ActualCofactorLimit ε) (c : ℝ≥0) :
    WienerAlgebraAt (1 / 2) →L[ℂ] Hilbert L c :=
  (ContinuousLinearMap.apply ℂ (Hilbert L c) (KernelHilbert.vector (complexKernel L c) 1)).comp
    (CriticalKernelAction.representationLinear (complexKernel L c) (complex_packet_dilation L c))

/-- Every positive retained origin mass produces an infinite-dimensional cyclic module. -/
theorem not_finiteDimensional {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (c : ℝ≥0) (hc : 0 < (c : ℝ)) : ¬ FiniteDimensional ℂ (Hilbert L c) := by
  intro h
  letI := h
  exact WienerAlgebraAt.not_finiteDimensional (1 / 2)
    (FiniteDimensional.of_injective (cyclicLinear L c).toLinearMap (cyclic_map_injective L c hc))

/-- Positive origin mixtures have continuum annihilator-quotient index. -/
theorem annihilator_quotient_rank {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (c : ℝ≥0) (hc : 0 < (c : ℝ)) :
    Module.rank ℂ (WienerAlgebraAt (1 / 2) ⧸ annihilator L c) = Cardinal.continuum :=
  faithful_wiener_orbit_rank (cyclicLinear L c) (cyclic_map_injective L c hc)
    (annihilator L c) (annihilator_eq_bot L c hc)

end MixedOriginModule
end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.OriginStepModule.not_finiteDimensional
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.OriginStepModule.annihilator_quotient_rank
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.MixedOriginModule.not_finiteDimensional
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.MixedOriginModule.annihilator_quotient_rank
end
end

