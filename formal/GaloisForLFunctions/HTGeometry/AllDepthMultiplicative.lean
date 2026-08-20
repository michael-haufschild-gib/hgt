import GaloisForLFunctions.HTGeometry.AllDepthCompleteness
import GaloisForLFunctions.HTGeometry.AffineFirstOrderDifferentialAlgebraicity
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicTransitivity
import GaloisForLFunctions.HTGeometry.FiniteDifferentialCircuitBoundary

/-!
# The multiplicative all-depth theorem

A nonzero germ is differentially algebraic exactly when its logarithmic derivative is: one direction
is closure of the generated differential field, the other is the first-order equation
`y′ = (y′/y)·y`.  Combined with the additive completeness theorem this classifies every
multiplicative solution of the all-depth constraint by the pair-face residues of its logarithmic
derivative.

* **`differentialAlgebraicOver_of_deriv_eq_mul`**;
* **`differentialAlgebraicOver_iff_logDeriv`**;
* **`differentialAlgebraicOver_iff_pairFace_logDeriv`**.
-/

open Filter Set Topology
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

/-- **A homogeneous first-order equation over a differentially algebraic coefficient.** -/
theorem differentialAlgebraicOver_of_deriv_eq_mul
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {u y : E} (hu : DifferentialAlgebraicOver F u) (hrel : y′ = u * y) :
    DifferentialAlgebraicOver F y := by
  letI : DifferentialAlgebra (differentialAdjoin F ({u} : Set E)) E :=
    ⟨fun c => derivationClosedDifferential_apply _
      (derivationClosed_differentialAdjoin F ({u} : Set E)) c⟩
  have humem : u ∈ differentialAdjoin F ({u} : Set E) :=
    subset_differentialAdjoin F ({u} : Set E) rfl
  have hyS : DifferentialAlgebraicOver (differentialAdjoin F ({u} : Set E)) y :=
    differentialAlgebraicOver_of_deriv_eq_base_mul
      (F := differentialAdjoin F ({u} : Set E)) (E := E) ⟨u, humem⟩ hrel
  exact differentialAlgebraicOver_trans hu hyS

/-- **A nonzero germ is differentially algebraic exactly when its logarithmic derivative is.** -/
theorem differentialAlgebraicOver_iff_logDeriv
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {y : E} (hy : y ≠ 0) :
    DifferentialAlgebraicOver F y ↔ DifferentialAlgebraicOver F (y′ / y) := by
  constructor
  · intro hDA
    refine differentialAlgebraicOver_of_mem_differentialAdjoin_singleton hDA ?_
    have hymem : y ∈ differentialAdjoin F ({y} : Set E) :=
      subset_differentialAdjoin F ({y} : Set E) rfl
    have hy'mem : y′ ∈ differentialAdjoin F ({y} : Set E) :=
      derivationClosed_differentialAdjoin F ({y} : Set E) hymem
    exact div_mem hy'mem hymem
  · intro hDA
    refine differentialAlgebraicOver_of_deriv_eq_mul hDA ?_
    field_simp

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **The multiplicative all-depth theorem.**  A nonzero multiplicative solution of the all-depth
constraint is differentially algebraic exactly when every pair-face residue of its logarithmic
derivative vanishes. -/
theorem differentialAlgebraicOver_iff_pairFace_logDeriv
    (τ : ι → ℂ) (hτ : ∀ m, 0 < (τ m).im) (hQ : PeriodsIntegrallyIndependent τ)
    (s : Finset ι) (hs : 2 ≤ s.card)
    {y : meroField (Set.univ : Set ℂ)} (hy : y ≠ 0) {F : ℂ → ℂ} {Cst : ℂ}
    (hF : RealizesMero (y′ / y) F) (hper : PeriodicOneGerm F)
    (hmixed : MixedConstGermSet τ s F Cst) :
    DifferentialAlgebraicOver ℂ y ↔
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ (p : ℂ) (ℓ : ℤ), ℓ < 0 →
        additiveOrbitalDivisorAt (pairFaceWitnessFun τ s i j F) (τ i) p ℓ = 0 := by
  rw [differentialAlgebraicOver_iff_logDeriv hy]
  exact differentialAlgebraicOver_iff_pairFace_eq_zero τ hτ hQ s hs hF hper hmixed

end

end GaloisForLFunctions
