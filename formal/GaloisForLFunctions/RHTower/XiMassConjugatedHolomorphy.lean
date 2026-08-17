import GaloisForLFunctions.RHTower.XiMassCausticSymbolComplex
import GaloisForLFunctions.HTGeometry.CauchySecondOrderIterate

/-!
# Holomorphy of the conjugated carrier and of the caustic coefficients

The Cauchy iteration is run on the open region

`U(τ) = { w : Re(τ² + w²) > 0 }`,

where the propagation radius `Z` is holomorphic and nonvanishing and `Re(aZ) > 0`, so the Schläfli
integral is holomorphic at `aZ`.  Everything the iteration touches — the conjugated carrier, the
transport rate, the caustic symbol — is holomorphic there, and holomorphy is inherited by every
iterate because a function holomorphic on an open set has holomorphic derivatives of all orders.
-/

open Complex Metric

namespace RHTower

noncomputable section

/-- The open region on which the propagation radius is a genuine principal square root. -/
def xiMassHeightRegion (τ : ℂ) : Set ℂ := {w : ℂ | 0 < (τ ^ 2 + w ^ 2).re}

theorem isOpen_xiMassHeightRegion (τ : ℂ) : IsOpen (xiMassHeightRegion τ) := by
  have hcont : Continuous fun w : ℂ => (τ ^ 2 + w ^ 2).re := by fun_prop
  exact isOpen_lt continuous_const hcont

theorem mem_xiMassHeightRegion {τ w : ℂ} : w ∈ xiMassHeightRegion τ ↔ 0 < (τ ^ 2 + w ^ 2).re :=
  Iff.rfl

/-- The propagation radius is holomorphic on the region. -/
theorem differentiableOn_xiMassHeightRadius (τ : ℂ) :
    DifferentiableOn ℂ (xiMassHeightRadius τ) (xiMassHeightRegion τ) := fun _ hw =>
  ((hasDerivAt_xiMassHeightRadius hw).differentiableAt).differentiableWithinAt

/-- The conjugated carrier is holomorphic on the region. -/
theorem differentiableAt_xiMassConjugatedCarrier {a : ℝ} {τ w : ℂ} (ha : 0 < a)
    (hw : 0 < (τ ^ 2 + w ^ 2).re) :
    DifferentiableAt ℂ (xiMassConjugatedCarrier a τ) w := by
  have hZ := (hasDerivAt_xiMassHeightRadius hw).differentiableAt
  have hexp : DifferentiableAt ℂ
      (fun v : ℂ => Complex.exp ((a : ℂ) * xiMassHeightRadius τ v)) w :=
    (hZ.const_mul (a : ℂ)).cexp
  have hside : DifferentiableAt ℂ (xiMassBesselHeightSide a τ) w :=
    (hasDerivAt_xiMassBesselHeightSide ha hw).differentiableAt
  exact hexp.mul hside

theorem differentiableOn_xiMassConjugatedCarrier {a : ℝ} (ha : 0 < a) (τ : ℂ) :
    DifferentiableOn ℂ (xiMassConjugatedCarrier a τ) (xiMassHeightRegion τ) := fun _ hw =>
  (differentiableAt_xiMassConjugatedCarrier ha hw).differentiableWithinAt

/-! ## The caustic coefficients -/

/-- The zeroth-order coefficient of the caustic operator on the conjugated carrier. -/
def xiCausticCoeffZero (a : ℝ) (τ w : ℂ) : ℂ :=
  xiMassCausticSymbolC a τ w
    + (a : ℂ) * (1 / xiMassHeightRadius τ w - w ^ 2 / xiMassHeightRadius τ w ^ 3)

/-- The first-order coefficient of the caustic operator on the conjugated carrier. -/
def xiCausticCoeffOne (a : ℝ) (τ w : ℂ) : ℂ :=
  2 * (a : ℂ) * xiMassRadiusRate τ w

theorem differentiableAt_xiCausticCoeffZero {a : ℝ} {τ w : ℂ} (hw : 0 < (τ ^ 2 + w ^ 2).re) :
    DifferentiableAt ℂ (xiCausticCoeffZero a τ) w := by
  have hZne : xiMassHeightRadius τ w ≠ 0 := xiMassHeightRadius_ne_zero hw
  have hRne : (τ ^ 2 + w ^ 2) ≠ 0 := by
    intro hcon
    rw [hcon] at hw
    simp at hw
  have hZ := (hasDerivAt_xiMassHeightRadius hw).differentiableAt
  have hquad : DifferentiableAt ℂ (fun v : ℂ => τ ^ 2 + v ^ 2) w := by fun_prop
  have hsym : DifferentiableAt ℂ (fun v : ℂ => xiMassCausticSymbolC a τ v) w := by
    have hnum : DifferentiableAt ℂ (fun v : ℂ => (a : ℂ) ^ 2 * v ^ 2) w := by fun_prop
    exact (differentiableAt_const _).sub (hnum.div hquad hRne)
  have hone : DifferentiableAt ℂ (fun v : ℂ => 1 / xiMassHeightRadius τ v) w :=
    (differentiableAt_const _).div hZ hZne
  have hcube : DifferentiableAt ℂ (fun v : ℂ => v ^ 2 / xiMassHeightRadius τ v ^ 3) w :=
    (by fun_prop : DifferentiableAt ℂ (fun v : ℂ => v ^ 2) w).div (hZ.pow 3)
      (pow_ne_zero _ hZne)
  exact hsym.add ((hone.sub hcube).const_mul _)

theorem differentiableAt_xiCausticCoeffOne {a : ℝ} {τ w : ℂ} (hw : 0 < (τ ^ 2 + w ^ 2).re) :
    DifferentiableAt ℂ (xiCausticCoeffOne a τ) w := by
  have hrate := (hasDerivAt_xiMassRadiusRate hw).differentiableAt
  exact hrate.const_mul _

end

end RHTower
