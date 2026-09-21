import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralCyclicPeierlsCrossBranchSource
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMStreamMetricEinstein

/-!
# Literal complementary-rate cyclic Peierls bidegree carrier

The literal source pairing has no same-rate component.  Its complementary
legs have total radial rate `-6`, but their angular product is not an
eigenfield at the corresponding clock parameter.  This leaf constructs the
honest replacement: a divergence-free cross-branch covector and its stream
metric, with the forced cross-gradient kept as an explicit covector source.

Proof-chain role:
`complementary causal legs -> bidegree covector at rate -6 + explicit forcing
 -> cross-branch metric/contact realization -> causal noncompact B2 transport
 -> RBH/PW-B/FZZ-P current -> RH`.
-/

namespace RHTower.D4BMLiteralCyclicPeierlsCrossBranchBidegree

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped ContDiff
open Filter Topology
open D4BMHorizon D4BMFundamentalScalarMetric D4BMMetricReconstruction D4BMModularCore
open D4BMLiteralCyclicPeierlsCrossBranchSource

noncomputable section
set_option autoImplicit false

/-- Angular field carried by the two distinct literal causal source branches. -/
def crossBranchField (q : XiZeroCopy) : Field := fun z =>
  fullAngularField q true z * fullAngularField q false z

/-- The complementary-rate carrier remains a genuine divergence-free stream
covector, since it is the coexact derivative of the literal product field. -/
def crossBranchCovector (q : XiZeroCopy) : Covector := coexact (crossBranchField q)

/-- Exact inhomogeneity after the two causal rates are combined at their
physical total clock.  The first summand is the literal cross-gradient source;
the second is the irreducible angular/clock parameter mismatch. -/
def crossBranchClockForcing (q : XiZeroCopy) : Field := fun z =>
  crossBranchAngularForcing q z +
    (crossBranchAngularParameter q - crossBranchClockParameter q) * crossBranchField q z

/-- Covector-level forcing of the literal complementary carrier.  This is
defined from the actual scalar defect, rather than postulating a homogeneous
cross-branch mode or discarding the cross-gradient. -/
def crossBranchForcingCovector (q : XiZeroCopy) : Covector := fun k z =>
  coexact (scalarLaplacian (crossBranchField q)) k z -
    crossBranchClockParameter q * crossBranchCovector q k z

theorem crossBranchField_c3 (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) :
    ContDiffAt ℝ 3 (crossBranchField q) z := by
  unfold crossBranchField
  exact
    ((contDiffAt_infty.mp (fullAngularField_smooth q true z hz)) 3).mul
      ((contDiffAt_infty.mp (fullAngularField_smooth q false z hz)) 3)

/-- The literal cross product obeys the exact forced equation at its total
complementary clock.  The inhomogeneity is retained in full. -/
theorem crossBranchField_clock_equation (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) :
    scalarLaplacian (crossBranchField q) z =
      crossBranchClockParameter q * crossBranchField q z + crossBranchClockForcing q z := by
  change scalarLaplacian (fun w => fullAngularField q true w * fullAngularField q false w) z =
    crossBranchClockParameter q * (fullAngularField q true z * fullAngularField q false z) +
      (crossBranchAngularForcing q z +
        (crossBranchAngularParameter q - crossBranchClockParameter q) *
          (fullAngularField q true z * fullAngularField q false z))
  rw [crossBranchAngular_product_equation q z hz]
  change crossBranchAngularParameter q *
      (fullAngularField q true z * fullAngularField q false z) +
      crossBranchAngularForcing q z = _
  ring

/-- The scalar defect defining the forced covector is exactly the literal
cross-gradient and angular-clock mismatch, not an auxiliary residual. -/
theorem crossBranchClockForcing_eq_scalar_defect (q : XiZeroCopy) (z : Point)
    (hz : 0 < z 1) :
    crossBranchClockForcing q z =
      scalarLaplacian (crossBranchField q) z -
        crossBranchClockParameter q * crossBranchField q z := by
  rw [crossBranchField_clock_equation q z hz]
  ring

theorem crossBranchCovector_smooth (q : XiZeroCopy) (z : Point) (hz : 0 < z 1)
    (k : Fin 2) :
    ContDiffAt ℝ 2 (crossBranchCovector q k) z := by
  unfold crossBranchCovector
  exact coexact_contDiffAt (m := (2 : WithTop ℕ∞)) (crossBranchField_c3 q z hz) k

theorem crossBranchCovector_divergence (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) :
    divergence (crossBranchCovector q) z = 0 := by
  unfold crossBranchCovector
  apply coexact_divergence _ z hz
  exact (crossBranchField_c3 q z hz).of_le (by norm_num)

/-- The complementary carrier satisfies the exact forced stream equation at
clock `-6`.  In particular the curvature shift and every literal source term
survive passage from scalar product to divergence-free covector. -/
theorem crossBranchCovector_rough_forced (q : XiZeroCopy) (z : Point)
    (hz : 0 < z 1) (k : Fin 2) :
    roughLaplacian (crossBranchCovector q) k z + crossBranchCovector q k z =
      crossBranchClockParameter q * crossBranchCovector q k z +
        crossBranchForcingCovector q k z := by
  unfold crossBranchCovector crossBranchForcingCovector
  rw [coexact_roughLaplacian _ z hz (crossBranchField_c3 q z hz) k]
  simp only [crossBranchCovector]
  ring

/-- The angular slot used by the actual Einstein stream is exactly the
complementary clock term plus the literal cross forcing.  Thus the forcing
survives into the reconstructed metric tensor rather than only its auxiliary
covector equation. -/
theorem crossBranch_streamAngularOperator_forced (q : XiZeroCopy) (z : Point)
    (hz : 0 < z 1) (k : Fin 2) :
    streamAngularOperator (crossBranchCovector q) k z =
      crossBranchClockParameter q * crossBranchCovector q k z +
        crossBranchForcingCovector q k z := by
  rw [streamAngularOperator_actual _ z hz _ (crossBranchCovector_divergence q),
    crossBranchCovector_rough_forced q z hz k]
  intro j
  exact crossBranchCovector_smooth q z hz j

/-- Actual cross-branch stream metric at the complementary physical clock.
Its amplitude `a² b² / 64` is the literal full-incoming-horizon normalization,
so it is fixed before any Peierls incidence is attempted. -/
def crossBranchMetric (q : XiZeroCopy) (a b : ℂ) (x : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  streamMetricField (crossBranchClock q) (a ^ 2 * b ^ 2 / 64) false
    (crossBranchCovector q) x

/-- The reconstructed complementary metric has actual second coordinate
derivatives throughout the exterior. -/
theorem crossBranchMetric_smooth (q : XiZeroCopy) (a b : ℂ)
    (p : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    ContDiffAt ℝ 2 (fun x => crossBranchMetric q a b x i j) p.val := by
  unfold crossBranchMetric
  apply streamMetricField_smooth
  intro k
  exact crossBranchCovector_smooth q (angularPoint p.val) p.property.2 k

/-- Every linearized Einstein component of the literal complementary metric
is its explicit stream current tensor.  This is a bulk realization theorem,
not an assertion of a causal cap/contact equality. -/
theorem crossBranchMetric_einstein (q : XiZeroCopy) (a b : ℂ)
    (p : D4BMBackground.ExteriorPoint) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological
        (D4BMBackground.jet (p.val 1) (p.val 3))
        (ofMetricField (crossBranchMetric q a b) p.val) (-3) i j =
      streamMetricTensor (crossBranchClock q) (p.val 1)
        (envelope (crossBranchClock q) (a ^ 2 * b ^ 2 / 64) p.val) false
        (crossBranchCovector q) (angularPoint p.val) i j := by
  unfold crossBranchMetric
  apply streamMetricField_einstein
  · intro k
    exact crossBranchCovector_smooth q (angularPoint p.val) p.property.2 k
  · exact crossBranchCovector_divergence q

/-- The realized metric has exactly the complementary total clock, never a
one-branch rate. -/
theorem crossBranchMetric_clock (q : XiZeroCopy) (a b : ℂ) (x : Fin 4 → ℝ) :
    crossBranchMetric q a b x =
      streamMetricField (-6 : ℂ) (a ^ 2 * b ^ 2 / 64) false
        (crossBranchCovector q) x := by
  rw [crossBranchMetric, crossBranchClock_eq_neg_six]

end

end RHTower.D4BMLiteralCyclicPeierlsCrossBranchBidegree
