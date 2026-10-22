import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMMixedQuadraticCurrent
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMLiteralCyclicPeierlsContactBilinear

/-!
# Literal polarized contact current

The B2 boundary comparison must use two independent physical source legs.
This leaf takes the polarization of the *actual* contact/left-QNM Einstein
current, rather than polarizing a scalar cap trace.  Its radial coefficient is
therefore exactly the product of the two source amplitudes and retains the
original left QNM and every angular covector.

Proof-chain role:
`literal two-leg metric contact + actual left QNM -> polarized contact current
-> finite/noncompact residual-face comparison -> HB B2`.
-/

namespace RHTower.D4BMLiteralCyclicPeierlsPolarizedContactCurrent

open Set
open GaloisForLFunctions.HTGeometry
open D4BMHorizon D4BMModularCore D4BMJointWave D4BMFundamentalScalarMetric
open D4BMLeftModeRadialEquation D4BMMixedQuadraticClosure
open D4BMMixedQuadraticCurrent D4BMMixedActionCurrent D4BMMetricReconstruction D4BMPhysicalModeAction

noncomputable section
set_option autoImplicit false

/-- Polarization in two independent source amplitudes of the literal contact
paired with the original left QNM.  Both summands are actual Einstein currents
of actual contact metrics; this definition performs no boundary replacement. -/
def polarizedContactRadialCurrent (q : XiZeroCopy) (branch : Bool) (a d : ℂ)
    (reader : XiZeroCopy) (side outer : Bool) (t : Iio (0 : ℝ))
    (z : {z : Point // 0 < z 1}) : ℂ :=
  let p := modePoint t z.val z.property
  (4 : ℂ)⁻¹ *
    ((p.val 1 : ℂ) ^ (2 : ℕ) / (p.val 3 : ℂ) ^ (2 : ℕ) * actionSymplectic
        (D4BMBackground.jet (p.val 1) (p.val 3))
        (ofMetricField (contactField q branch (a + d)) p.val)
        (ofMetricField (metricField reader side outer) p.val) 1 -
      (p.val 1 : ℂ) ^ (2 : ℕ) / (p.val 3 : ℂ) ^ (2 : ℕ) * actionSymplectic
        (D4BMBackground.jet (p.val 1) (p.val 3))
        (ofMetricField (contactField q branch (a - d)) p.val)
        (ofMetricField (metricField reader side outer) p.val) 1)

/-- Exact two-leg radial contact current.  This is the metric-side carrier
needed by B2: its coefficient is bilinear in the independent amplitudes, with
the same original left QNM and square covector as the diagonal current. -/
theorem polarizedContactRadialCurrent_eq (q : XiZeroCopy) (branch : Bool)
    (a d : ℂ) (reader : XiZeroCopy) (side outer : Bool) (t : Iio (0 : ℝ))
    (z : {z : Point // 0 < z 1}) :
    let p := modePoint t z.val z.property
    let s := physicalRate q branch
    let r := (p.val 1 : ℂ)
    let E := envelope (2 * s) (a * d) p.val
    polarizedContactRadialCurrent q branch a d reader side outer t z =
      contactRadialCoefficient s r E (eigenvalue reader)
        (profile reader side outer t) (profileFirst reader side outer t) *
      ∑ k : Fin 2, fullSquareCovector q k (angularPoint p.val) *
        D4BMLiteralCusp.vector (D4BMJointSource.physicalAngularParameter reader) k z.val := by
  dsimp only
  unfold polarizedContactRadialCurrent
  simp only []
  rw [contact_radial_current, contact_radial_current]
  simp only [envelope, contactRadialCoefficient]
  ring

end

end RHTower.D4BMLiteralCyclicPeierlsPolarizedContactCurrent
