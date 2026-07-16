import GaloisForLFunctions.HTGeometry.FiniteDifferentialCircuitBoundary
import GaloisForLFunctions.HTGeometry.SourceLogarithmicBoundary

/-!
# Differential-algebraic variable-coefficient observation filters

A finite jet-linear observation may use coefficients from a derivation-closed intermediate field
rather than from the constant field.  If that coefficient reservoir has finite transcendence
degree over the base, every nonzero such observation preserves hypertranscendence.  Equivalently,
the filtered value escapes the reservoir that supplied its coefficients.

This is a static observability theorem.  It assumes no solution flow for the differential equation
represented by the filter.  The proof treats a hypothetical differentially algebraic output as one
more coefficient, obtains a nonzero affine relation on the source jet, and descends differential
algebraicity through the finite reservoir.

Systems-biology and ML provenance: A. Ovchinnikov, G. Pogudin, and P. Thompson,
*Input-output equations and identifiability of linear ODE models*, arXiv:1910.03960, identify
model information through coefficients of differential input-output equations; T. E. Loman,
A. P. Browning, and R. E. Baker, *Structural functional identifiability and model discovery in
differential equation models*, arXiv:2606.30289, extend this viewpoint to unknown functional
components and neural-ODE model discovery.  Physics provenance: Picard--Fuchs and D-module
equations supply variable-coefficient differential observations of Feynman periods.  These are
parent interfaces; the result below is a bridge formalization, not a novelty claim.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- A finite variable-coefficient linear observation of the complete differential jet. -/
def finsuppLinearDifferentialObservation
    (C : Type*) {E : Type*} [Field C] [Field E] [Algebra C E] [Differential E]
    (c : (Unit × ℕ) →₀ C) (y : E) : E :=
  Finsupp.linearCombination E (fun p => differentialJet p.2 y)
    (Finsupp.mapRange (algebraMap C E) (map_zero (algebraMap C E)) c)

/-- **Finite-reservoir variable-filter preservation.**  Let `S` be a derivation-closed
coefficient field of finite transcendence degree over `F`.  Every nonzero finite `S`-linear
combination of the jets of an `F`-hypertranscendental element is again hypertranscendental over
`F`.

Unlike the constant-coefficient Toeplitz theorem, the derivatives of the coefficients may be
nonzero.  Finite differential-algebraic complexity of the complete coefficient reservoir is the
relevant hypothesis. -/
theorem hypertranscendentalOver_finsuppLinearDifferentialObservation_of_finiteTrdeg
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {y : E} (S : IntermediateField F E) (hSclosed : DerivationClosed S)
    (hSfinite : Algebra.trdeg F S < Cardinal.aleph0)
    (c : (Unit × ℕ) →₀ S) (hc : c ≠ 0)
    (hy : HypertranscendentalOver F y) :
    HypertranscendentalOver F (finsuppLinearDifferentialObservation S c y) := by
  letI : Differential S := derivationClosedDifferential S hSclosed
  letI : DifferentialAlgebra S E :=
    ⟨fun a => derivationClosedDifferential_apply S hSclosed a⟩
  let z : E := finsuppLinearDifferentialObservation S c y
  change HypertranscendentalOver F z
  intro hz
  have hzS : DifferentialAlgebraicOver S z :=
    differentialAlgebraicOver_mono hz
  let T := differentialAdjoin S ({z} : Set E)
  letI : Differential T := derivationClosedDifferential T
    (derivationClosed_differentialAdjoin S ({z} : Set E))
  letI : DifferentialAlgebra T E :=
    ⟨fun a => derivationClosedDifferential_apply T
      (derivationClosed_differentialAdjoin S ({z} : Set E)) a⟩
  let zT : T := ⟨z, subset_differentialAdjoin S ({z} : Set E) rfl⟩
  let cT : (Unit × ℕ) →₀ T :=
    Finsupp.mapRange (algebraMap S T) (map_zero (algebraMap S T)) c
  have hcT : cT ≠ 0 := by
    intro hzero
    apply hc
    apply Finsupp.mapRange_injective (algebraMap S T)
      (map_zero (algebraMap S T)) (algebraMap S T).injective
    simpa only [cT, Finsupp.mapRange_zero] using hzero
  have hcmap :
      Finsupp.mapRange (algebraMap T E) (map_zero (algebraMap T E)) cT =
        Finsupp.mapRange (algebraMap S E) (map_zero (algebraMap S E)) c := by
    ext p
    change algebraMap T E (algebraMap S T (c p)) = algebraMap S E (c p)
    exact IsScalarTower.algebraMap_apply S T E (c p)
  have hrel :
      Finsupp.linearCombination E (fun p => differentialJet p.2 y)
          (Finsupp.mapRange (algebraMap T E) (map_zero (algebraMap T E)) cT) =
        algebraMap T E zT := by
    rw [hcmap]
    rfl
  have hyT : DifferentialAlgebraicOver T y :=
    differentialAlgebraicOver_of_finsupp_jet_linear_eq y cT hcT zT hrel
  have hyS : DifferentialAlgebraicOver S y :=
    differentialAlgebraicOver_trans hzS hyT
  exact hy (differentialAlgebraicOver_of_intermediate_trdeg_lt_aleph0
    S hSclosed hSfinite hyS)

/-- **Finite-state escape law.**  A nonzero variable-coefficient differential observation of an
HT source cannot lie in the finite-transcendence derivation-closed field that supplied its
coefficients. -/
theorem finsuppLinearDifferentialObservation_not_mem_finiteTrdeg_reservoir
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {y : E} (hy : HypertranscendentalOver F y)
    (S : IntermediateField F E) (hSclosed : DerivationClosed S)
    (hSfinite : Algebra.trdeg F S < Cardinal.aleph0)
    (c : (Unit × ℕ) →₀ S) (hc : c ≠ 0) :
    finsuppLinearDifferentialObservation S c y ∉ S := by
  intro hmem
  have houtDA : DifferentialAlgebraicOver F
      (finsuppLinearDifferentialObservation S c y) :=
    differentialAlgebraicOver_of_mem_derivationClosed_finiteTrdeg
      S hSclosed hSfinite hmem
  exact (hypertranscendentalOver_finsuppLinearDifferentialObservation_of_finiteTrdeg
    S hSclosed hSfinite c hc hy) houtDA

end

end GaloisForLFunctions.HTGeometry
