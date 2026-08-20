import GaloisForLFunctions.HTGeometry.AllDepthUniversalCarrier
import GaloisForLFunctions.HTGeometry.AllDepthBottomRealization
import GaloisForLFunctions.HTGeometry.MeromorphicTranslationDifferentialOperator
import GaloisForLFunctions.HTGeometry.MeromorphicRealizationDerivative

/-!
# Jets of the universal carrier realize every prescribed bottom charge

The bottom witness of the universal carrier is a translated theta logarithmic derivative, so the
bottom witness of a finite combination of jets of translates of the carrier is the corresponding
finite combination of line-atom jets.  Since an atom sum realizes an arbitrary finite divisor of
bounded order on the elliptic quotient, the bottom-charge map is surjective.

* `realizesMero_thetaLogDerivMero`;
* `diffCubeMero_add`, `diffCubeMero_finsetSum`, `diffCubeMero_algebraMap_mul`,
  `diffCubeMero_differentialJet` — the cube is a constant-coefficient differential operator;
* `carrierAtomCombination` and its cube and bottom laws;
* **`exists_class_member_with_prescribed_bottomCharge`**.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra

/-! ## The theta coordinate is realized by the theta source -/

theorem realizesMero_thetaLogDerivMero (σ : ℂ) (hσ : 0 < σ.im) :
    RealizesMero (thetaLogDerivMero σ hσ) (thetaSource σ) := by
  refine realizesMero_fraction (A := fun z => jacobiTheta₂' z σ) (B := fun z => jacobiTheta₂ z σ)
    (jacobiTheta₂'_analyticOnNhd_fst σ hσ) (jacobiTheta₂_analyticOnNhd_fst σ hσ)
    (thetaAnalytic_ne_zero σ hσ) ?_
  intro z hz
  rw [thetaSource, logDeriv_apply]
  congr 1
  exact (hasDerivAt_jacobiTheta₂_fst z hσ).deriv

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## The difference cube is a constant-coefficient operator -/

omit [Fintype ι] [DecidableEq ι] in
theorem diffCubeMero_add (τ : ι → ℂ) (t : Finset ι) (x y : meroField (Set.univ : Set ℂ)) :
    diffCubeMero τ t (x + y) = diffCubeMero τ t x + diffCubeMero τ t y := by
  classical
  rw [diffCubeMero, diffCubeMero, diffCubeMero, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun E _ => by rw [map_add, smul_add]

omit [Fintype ι] [DecidableEq ι] in
theorem diffCubeMero_finsetSum (τ : ι → ℂ) (t : Finset ι) {κ : Type*} (s : Finset κ)
    (x : κ → meroField (Set.univ : Set ℂ)) :
    diffCubeMero τ t (∑ i ∈ s, x i) = ∑ i ∈ s, diffCubeMero τ t (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [diffCubeMero]
  | @insert a s' ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, diffCubeMero_add, ih]

omit [Fintype ι] [DecidableEq ι] in
theorem diffCubeMero_algebraMap_mul (τ : ι → ℂ) (t : Finset ι) (α : ℂ)
    (x : meroField (Set.univ : Set ℂ)) :
    diffCubeMero τ t (algebraMap ℂ (meroField (Set.univ : Set ℂ)) α * x)
      = algebraMap ℂ (meroField (Set.univ : Set ℂ)) α * diffCubeMero τ t x := by
  classical
  rw [diffCubeMero, diffCubeMero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun E _ => ?_
  rw [map_mul, addTranslationMeroEquiv_algebraMap_complex, Algebra.smul_def, Algebra.smul_def]
  ring

omit [Fintype ι] in
theorem diffCubeMero_differentialJet (τ : ι → ℂ) (j : ℕ) :
    ∀ (t : Finset ι) (x : meroField (Set.univ : Set ℂ)),
      diffCubeMero τ t (differentialJet j x) = differentialJet j (diffCubeMero τ t x) := by
  classical
  intro t
  induction t using Finset.induction_on with
  | empty => intro x; simp
  | @insert q t' hq ih =>
      intro x
      rw [diffCubeMero_insert τ hq, ih x, diffCubeMero_insert τ hq,
        addTranslationMeroEquiv_differentialJet]
      exact (differentialJet_sub j _ _).symm

end

end GaloisForLFunctions
