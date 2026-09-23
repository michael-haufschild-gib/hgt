import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullSeedCapRadialMemory

/-! Literal physical angular action in the combined cyclic Peierls cap normal trace.

The established cap theorem displays the full Goursat coefficient as
`parameter * (H + Q)`.  This file identifies it with the actual inverse-metric
scalar action of the full field in physical `(X,Y)` coordinates.  Both the seed
and source-cap terms, their coefficients, and the unrenormalized cap scale are
retained.  No derivative/cap-limit interchange is asserted here.
-/

open Filter Topology
namespace RHTower.D4BMFullSeedCapPhysicalAction
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open D4BMFutureSeedHorizon D4BMFutureHorizon D4BMFullSeedCapRadialMemory
open D4BMHorizon D4BMModularCore D4BMGlobalAngularResponse D4BMCapRadialMemory
  D4BMCapNormalTrace
noncomputable section
set_option autoImplicit false

/-- Physical scalar action in the original upper-half-plane chart. -/
def physicalScalarAction (S : Point → ℂ) (z : Point) : ℂ :=
  (z 1 : ℂ)^(2 : ℕ) *
    (coordDeriv 0 (coordDeriv 0 S) z + coordDeriv 1 (coordDeriv 1 S) z)

/-- Coordinate expansion of the actual inverse-metric scalar action. -/
theorem physicalScalarAction_eq (S : Point → ℂ) (z : Point) (hz : 0 < z 1) :
    physicalScalarAction S z = scalarLaplacian S z := by
  unfold physicalScalarAction
  rw [scalarLaplacian_eq S z hz]

/-- The full Goursat coefficient is the literal physical scalar action. -/
theorem full_physicalScalarAction (q : XiZeroCopy) (branch : Bool) (X k : ℝ) :
    physicalScalarAction (fullAngularField q branch) ![X, Real.exp k] =
      parameter q branch *
        (fullAngularField q branch ![X, Real.exp k] +
          fullSquarePotential q ![X, Real.exp k]) := by
  rw [physicalScalarAction_eq _ _ (Real.exp_pos k)]
  rw [fullAngularField_equation q branch _ (Real.exp_pos k)]
  simp only [fullSquarePotential]
  ring

/-- The full seed and source cap normal coefficients in literal physical action form. -/
def combinedCapPhysicalNormalCoefficient (q : XiZeroCopy) (branch : Bool)
    (amp : ℂ) (v X k : ℝ) : ℂ :=
  seedTraceCoefficient q branch amp *
      physicalScalarAction (fullAngularField q branch) ![X, Real.exp k] *
        sourceMemory q branch v -
    parameter q branch * liftTraceCoefficient q branch amp *
      physicalScalarAction (fullSquarePotential q) ![X, Real.exp k] *
        sourceMemory q branch v

/-- Exact unrenormalized normal trace of literal cyclic Peierls cap.

This is the existing two-arm, seed-minus-source cap limit rewritten only through
the physical `(X,Y)` scalar action. -/
theorem combinedCap_ingoing_normal_div_scale_physical_action
    (q : XiZeroCopy) (branch : Bool) (amp : ℂ) (v X k : ℝ) :
    Tendsto (fun x => deriv (fun y =>
      seedCapField q branch amp (v-y) y X k -
        parameter q branch * capBoundaryField q branch amp (v-y) y X k) x /
          (capScale x : ℂ)) atBot
      (𝓝 (combinedCapPhysicalNormalCoefficient q branch amp v X k)) := by
  have h := combinedCap_ingoing_normal_div_scale q branch amp v X k
  have hH := physicalScalarAction_eq (fullAngularField q branch) ![X, Real.exp k]
    (Real.exp_pos k)
  have hQ := physicalScalarAction_eq (fullSquarePotential q) ![X, Real.exp k]
    (Real.exp_pos k)
  rw [combinedCapPhysicalNormalCoefficient, hH, hQ,
    fullAngularField_equation q branch _ (Real.exp_pos k)]
  simp only [fullSquarePotential] at h ⊢
  convert h using 1 <;> ring

end
end RHTower.D4BMFullSeedCapPhysicalAction
