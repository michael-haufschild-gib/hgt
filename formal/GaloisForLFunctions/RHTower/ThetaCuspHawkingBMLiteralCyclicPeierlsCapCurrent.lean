import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCapAngularFluxCusp
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedQuadraticCurrent
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralCyclicPeierlsCapDefect

/-!
# Literal cyclic Peierls cap current

The cap action cannot be compared to a reader through only the full-response
Green current: its retained square term contributes its own source flux.  This
leaf constructs their exact same-branch combination.  The result is the
literal Green current of `H - c Q`, whose coefficient of the reader derivative
is the physical cyclic Peierls action, including the full gradient energy.

Proof-chain role:
`two-arm cap action + full Green current + square-source cap flux -> literal
same-branch angular cap current -> noncompact metric-current/left-QNM contact
transport -> HB B2`.
-/

namespace RHTower.D4BMLiteralCyclicPeierlsCapCurrent

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open D4BMHorizon D4BMModularCore D4BMGlobalAngularResponse D4BMJointSource
open D4BMMixedQuadraticCurrent D4BMCapAngularFluxCusp
open D4BMLiteralCyclicPeierlsCapDefect

noncomputable section
set_option autoImplicit false

/-- The literal angular potential carried by the two-leg cyclic Peierls
metric before its physical scalar action is taken. -/
def cyclicPeierlsAngularPotential (q : XiZeroCopy) (branch : Bool) : Point → ℂ :=
  fullAngularField q branch -
    (physicalRate q branch * (physicalRate q branch - 1) / 4) • fullSquarePotential q

/-- The physical scalar action of the literal angular potential at an
arbitrary upper-half-plane point. -/
def cyclicPeierlsAngularAction (q : XiZeroCopy) (branch : Bool) (z : Point) : ℂ :=
  scalarLaplacian (fullAngularField q branch) z -
    (physicalRate q branch * (physicalRate q branch - 1) / 4) *
      scalarLaplacian (fullSquarePotential q) z

/-- Same-branch cap current: full-response Green current minus exactly the
retained square-source flux, with the coefficient forced by the physical
two-leg metric. -/
def cyclicPeierlsAngularCurrent (q reader : XiZeroCopy) (branch : Bool)
    (j : Fin 2) (z : Point) : ℂ :=
  angularGreenCurrent q branch reader j z -
    (physicalRate q branch * (physicalRate q branch - 1) / 4) *
      angularFlux q reader j z

/-- The first coordinate jets of the literal potential retain the full and
square covectors with their forced physical coefficient. -/
theorem cyclicPeierlsAngularPotential_coordDeriv (q : XiZeroCopy) (branch : Bool)
    (z : {z : Point // 0 < z 1}) (j : Fin 2) :
    coordDeriv j (cyclicPeierlsAngularPotential q branch) z.val =
      coordDeriv j (fullAngularField q branch) z.val -
        (physicalRate q branch * (physicalRate q branch - 1) / 4) *
          coordDeriv j (fullSquarePotential q) z.val := by
  have hH : DifferentiableAt ℝ (fullAngularField q branch) z.val :=
    (fullAngularField_smooth q branch z.val z.property).differentiableAt (by norm_num)
  have hQ : DifferentiableAt ℝ (fullSquarePotential q) z.val :=
    (fullSquarePotential_smooth q z.val z.property 1).differentiableAt (by norm_num)
  have hmul : coordDeriv j (fun y =>
      (physicalRate q branch * (physicalRate q branch - 1) / 4) *
        fullSquarePotential q y) z.val =
      (physicalRate q branch * (physicalRate q branch - 1) / 4) *
        coordDeriv j (fullSquarePotential q) z.val := by
    have h := hQ.hasFDerivAt.const_mul
      (physicalRate q branch * (physicalRate q branch - 1) / 4)
    simpa only [coordDeriv, smul_apply, smul_eq_mul] using
      congrArg (fun L => L (Pi.single j 1)) h.fderiv
  change coordDeriv j (fun y => fullAngularField q branch y -
      (physicalRate q branch * (physicalRate q branch - 1) / 4) *
        fullSquarePotential q y) z.val = _
  rw [coordDeriv_sub hH (hQ.const_mul _), hmul]

/-- The completed cap current is exactly the scalar Green current of the
literal potential.  In particular, its reader-derivative coefficient is the
full cyclic Peierls action, rather than a homogeneous full-minus-square
surrogate. -/
theorem cyclicPeierlsAngularCurrent_eq_green (q reader : XiZeroCopy) (branch : Bool)
    (z : {z : Point // 0 < z 1}) (j : Fin 2) :
    cyclicPeierlsAngularCurrent q reader branch j z.val =
      D4BMLeftModeRadialEquation.eigenvalue reader *
        D4BMLiteralCusp.scalar (physicalAngularParameter reader) z.val *
          (coordDeriv j (fullAngularField q branch) z.val -
            (physicalRate q branch * (physicalRate q branch - 1) / 4) *
              coordDeriv j (fullSquarePotential q) z.val) -
        cyclicPeierlsAngularAction q branch z.val *
          coordDeriv j (D4BMLiteralCusp.scalar (physicalAngularParameter reader)) z.val := by
  unfold cyclicPeierlsAngularCurrent cyclicPeierlsAngularAction
  rw [fullAngularField_equation q branch z.val z.property,
    angularFlux_eq q reader j z.val]
  simp only [angularGreenCurrent, D4BMAngularTwoTensor.source,
    D4BMLeftModeRadialEquation.eigenvalue]
  ring

/-- Equivalent potential form of the same current.  This identifies an
actual literal potential and its physical scalar action, not merely an
algebraic coefficient list. -/
theorem cyclicPeierlsAngularCurrent_eq_potential_green (q reader : XiZeroCopy)
    (branch : Bool) (z : {z : Point // 0 < z 1}) (j : Fin 2) :
    cyclicPeierlsAngularCurrent q reader branch j z.val =
      D4BMLeftModeRadialEquation.eigenvalue reader *
        D4BMLiteralCusp.scalar (physicalAngularParameter reader) z.val *
          coordDeriv j (cyclicPeierlsAngularPotential q branch) z.val -
        cyclicPeierlsAngularAction q branch z.val *
          coordDeriv j (D4BMLiteralCusp.scalar (physicalAngularParameter reader)) z.val := by
  rw [cyclicPeierlsAngularPotential_coordDeriv]
  exact cyclicPeierlsAngularCurrent_eq_green q reader branch z j

/-- On the physical `(X, exp k)` chart, the arbitrary-point action is exactly
the cap action selected by the literal cyclic Peierls metric. -/
theorem cyclicPeierlsAngularAction_physical (q : XiZeroCopy) (branch : Bool)
    (X k : ℝ) :
    cyclicPeierlsAngularAction q branch ![X, Real.exp k] =
      cyclicPeierlsPhysicalAction q branch X k := by
  unfold cyclicPeierlsAngularAction cyclicPeierlsPhysicalAction
  rw [physicalScalarAction_eq _ _ (Real.exp_pos k),
    physicalScalarAction_eq _ _ (Real.exp_pos k)]

/-- Physical-chart form of the literal cap current.  This is the exact
reader current whose coefficient is the normal cap action transported by the
late-clock realization; no full/square or gradient contribution is omitted. -/
theorem cyclicPeierlsAngularCurrent_eq_physical_green (q reader : XiZeroCopy)
    (branch : Bool) (X k : ℝ) (j : Fin 2) :
    cyclicPeierlsAngularCurrent q reader branch j ![X, Real.exp k] =
      D4BMLeftModeRadialEquation.eigenvalue reader *
        D4BMLiteralCusp.scalar (physicalAngularParameter reader) ![X, Real.exp k] *
          (coordDeriv j (fullAngularField q branch) ![X, Real.exp k] -
            (physicalRate q branch * (physicalRate q branch - 1) / 4) *
              coordDeriv j (fullSquarePotential q) ![X, Real.exp k]) -
        cyclicPeierlsPhysicalAction q branch X k *
          coordDeriv j (D4BMLiteralCusp.scalar (physicalAngularParameter reader))
            ![X, Real.exp k] := by
  have h := cyclicPeierlsAngularCurrent_eq_green q reader branch
    ⟨![X, Real.exp k], Real.exp_pos k⟩ j
  rw [cyclicPeierlsAngularAction_physical] at h
  exact h

end

end RHTower.D4BMLiteralCyclicPeierlsCapCurrent
