import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralCyclicPeierlsCapRadialDefect
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspMeanDerivative

/-!
# Finite-cusp Stokes for the literal cyclic Peierls residual

The residual left after the literal cap-current substitution is a genuine
two-component angular current.  This leaf proves its finite-height cusp
Stokes law: the full metric/left-QNM radial defect has only the two literal
vertical faces on every finite cusp strip.  It retains both terms of the
current and asserts neither a noncompact limit nor cancellation of either
face.

Proof-chain role:
`actual radial defect = residual divergence -> finite periodic cusp Stokes
-> explicit upper/lower residual faces -> noncompact finite-part/cancellation
or B2 obstruction -> HB B2`.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane
open scoped BigOperators ContDiff

namespace RHTower.D4BMLiteralCyclicPeierlsCapResidualCusp

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open D4BMHorizon D4BMModularCore D4BMJointSource D4BMJointWave
open D4BMGlobalAngularResponse D4BMLeftModeRadialEquation D4BMAngularSeries
open D4BMMixedQuadraticCurrent D4BMMixedRadialOverlap D4BMCapAngularFluxCusp
open D4BMCuspResponse D4BMLiteralCyclicPeierlsCapRadialDefect

noncomputable section
set_option autoImplicit false

private def planarCurrent (q reader : XiZeroCopy) (branch side outer : Bool)
    (a : ℂ) (t : Iio (0 : ℝ)) (base : {z : Point // 0 < z 1})
    (j : Fin 2) : ℂ → ℂ :=
  cyclicPeierlsResidualCurrent q reader branch side outer a t base j ∘ angularCoordinates

private theorem planarCurrent_smooth (q reader : XiZeroCopy) (branch side outer : Bool)
    (a : ℂ) (t : Iio (0 : ℝ)) (base : {z : Point // 0 < z 1})
    (j : Fin 2) :
    ContDiffOn ℝ ∞ (planarCurrent q reader branch side outer a t base j)
      {w : ℂ | 0 < w.im} := by
  intro w hw
  exact ((cyclicPeierlsResidualCurrent_contDiffAt q reader branch side outer a t base j
    (angularCoordinates w) hw).comp w angularCoordinates.contDiff.contDiffAt).contDiffWithinAt

private theorem periodic_coordDeriv {F : Point → ℂ}
    (hF : Function.Periodic F ![1, 0]) (j : Fin 2) :
    Function.Periodic (coordDeriv j F) ![1, 0] := by
  intro z
  have he : (fun w => F (w + ![1, 0])) = F := funext hF
  have hd := fderiv_comp_add_right (𝕜 := ℝ) (f := F) (x := z) ![1, 0]
  rw [he] at hd
  exact congrArg (fun L => L (Pi.single j 1)) hd.symm

private theorem scalar_periodic (u : ℂ) :
    Function.Periodic (D4BMLiteralCusp.scalar u) ![1, 0] := by
  intro z
  simpa [D4BMLiteralCusp.scalar, Pi.add_apply] using
    d4BM_completedEisensteinCuspLeg_scalar_periodic u (z 1) (z 0)

private theorem square_periodic (q : XiZeroCopy) :
    Function.Periodic (fullSquarePotential q) ![1, 0] := by
  intro z
  have h := scalar_periodic (center q) z
  simp only [D4BMLiteralCusp.scalar] at h
  simp only [fullSquarePotential, D4BMGlobalAngularResponse.scalar, h]

private theorem squareReaderCurrent_periodic (q reader : XiZeroCopy) (j : Fin 2) :
    Function.Periodic (squareReaderCurrent q reader j) ![1, 0] := by
  let S := D4BMAngularTwoTensor.source q
  let R := D4BMLiteralCusp.scalar (physicalAngularParameter reader)
  have hS : Function.Periodic S ![1, 0] := scalar_periodic (center q)
  have hR : Function.Periodic R ![1, 0] := scalar_periodic (physicalAngularParameter reader)
  intro z
  change S (z + ![1, 0]) ^ (2 : ℕ) / 2 * coordDeriv j R (z + ![1, 0]) =
    S z ^ (2 : ℕ) / 2 * coordDeriv j R z
  rw [hS z, periodic_coordDeriv hR j z]

private theorem scalarLaplacian_square_periodic (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) :
    scalarLaplacian (fullSquarePotential q) (z + ![1, 0]) =
      scalarLaplacian (fullSquarePotential q) z := by
  have hz' : 0 < (z + ![1, 0] : Point) 1 := by
    simpa only [Pi.add_apply, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one, add_zero] using hz
  have hQ := square_periodic q
  have h00 := periodic_coordDeriv (periodic_coordDeriv hQ 0) 0
  have h11 := periodic_coordDeriv (periodic_coordDeriv hQ 1) 1
  rw [scalarLaplacian_eq _ (z + ![1, 0]) hz', scalarLaplacian_eq _ z hz,
    h00 z, h11 z]
  simp only [Pi.add_apply, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_fin_one, add_zero]

private theorem angularFlux_periodic_at (q reader : XiZeroCopy) (j : Fin 2)
    (z : Point) (hz : 0 < z 1) :
    angularFlux q reader j (z + ![1, 0]) = angularFlux q reader j z := by
  have hQ : Function.Periodic (fullSquarePotential q) ![1, 0] := square_periodic q
  have hR : Function.Periodic
      (D4BMLiteralCusp.scalar (physicalAngularParameter reader)) ![1, 0] :=
    scalar_periodic (physicalAngularParameter reader)
  have hQj := periodic_coordDeriv hQ j
  have hRj := periodic_coordDeriv hR j
  rw [angularFlux_eq, angularFlux_eq, hR z, hQj z, hRj z,
    scalarLaplacian_square_periodic q z hz]

private theorem residualCurrent_periodic_at (q reader : XiZeroCopy)
    (branch side outer : Bool) (a : ℂ) (t : Iio (0 : ℝ))
    (base : {z : Point // 0 < z 1}) (j : Fin 2)
    (z : Point) (hz : 0 < z 1) :
    cyclicPeierlsResidualCurrent q reader branch side outer a t base j (z + ![1, 0]) =
      cyclicPeierlsResidualCurrent q reader branch side outer a t base j z := by
  unfold cyclicPeierlsResidualCurrent
  rw [squareReaderCurrent_periodic q reader j z, angularFlux_periodic_at q reader j z hz]

private theorem planarCurrent_periodic (q reader : XiZeroCopy) (branch side outer : Bool)
    (a : ℂ) (t : Iio (0 : ℝ)) (base : {z : Point // 0 < z 1})
    (j : Fin 2) (y : ℝ) (hy : 0 < y) :
    Function.Periodic (fun x => planarCurrent q reader branch side outer a t base j
      (D4BMCuspResponse.point x y)) 1 := by
  intro x
  have hc : angularCoordinates (D4BMCuspResponse.point (x + 1) y) =
      angularCoordinates (D4BMCuspResponse.point x y) + ![1, 0] := by
    ext i
    fin_cases i <;> norm_num [angularCoordinates, D4BMCuspResponse.point, Pi.add_apply]
  change cyclicPeierlsResidualCurrent q reader branch side outer a t base j
      (angularCoordinates (D4BMCuspResponse.point (x + 1) y)) = _
  rw [hc]
  exact residualCurrent_periodic_at q reader branch side outer a t base j
    (angularCoordinates (D4BMCuspResponse.point x y))
    (by simpa [angularCoordinates, D4BMCuspResponse.point] using hy)

private def planarDivergence (q reader : XiZeroCopy) (branch side outer : Bool)
    (a : ℂ) (t : Iio (0 : ℝ)) (base : {z : Point // 0 < z 1}) (w : ℂ) : ℂ :=
  horizontal (planarCurrent q reader branch side outer a t base 0) w +
    vertical (planarCurrent q reader branch side outer a t base 1) w

private theorem planarDivergence_eq (q reader : XiZeroCopy) (branch side outer : Bool)
    (a : ℂ) (t : Iio (0 : ℝ)) (base : {z : Point // 0 < z 1}) (w : ℂ) :
    planarDivergence q reader branch side outer a t base w =
      ∑ j : Fin 2, coordDeriv j
        (cyclicPeierlsResidualCurrent q reader branch side outer a t base j)
        (angularCoordinates w) := by
  have h0 := angularCoordinates_derivative
    (cyclicPeierlsResidualCurrent q reader branch side outer a t base 0) 0 w
  have h1 := angularCoordinates_derivative
    (cyclicPeierlsResidualCurrent q reader branch side outer a t base 1) 1 w
  rw [Fin.sum_univ_two]
  exact congrArg₂ (· + ·) h0 h1

private theorem planarDivergence_smooth (q reader : XiZeroCopy) (branch side outer : Bool)
    (a : ℂ) (t : Iio (0 : ℝ)) (base : {z : Point // 0 < z 1}) :
    ContDiffOn ℝ ∞ (planarDivergence q reader branch side outer a t base)
      {w : ℂ | 0 < w.im} :=
  (planar_derivative_contDiffOn
    (planarCurrent_smooth q reader branch side outer a t base 0) (1 : ℂ)).add
      (planar_derivative_contDiffOn
        (planarCurrent_smooth q reader branch side outer a t base 1) Complex.I)

/-- Literal vertical residual-current face on one width-one cusp section. -/
def cyclicPeierlsResidualCuspBoundary (q reader : XiZeroCopy) (branch side outer : Bool)
    (a : ℂ) (t : Iio (0 : ℝ)) (base : {z : Point // 0 < z 1}) (y : ℝ) : ℂ :=
  D4BMCuspResponse.average (planarCurrent q reader branch side outer a t base 1) y

/-- The actual metric-current radial defect density on a cusp section,
represented by its equal literal residual divergence. -/
def cyclicPeierlsResidualCuspDensity (q reader : XiZeroCopy) (branch side outer : Bool)
    (a : ℂ) (t : Iio (0 : ℝ)) (base : {z : Point // 0 < z 1}) (y : ℝ) : ℂ :=
  D4BMCuspResponse.average (planarDivergence q reader branch side outer a t base) y

private theorem horizontal_current_mean_zero (q reader : XiZeroCopy) (branch side outer : Bool)
    (a : ℂ) (t : Iio (0 : ℝ)) (base : {z : Point // 0 < z 1}) {y : ℝ} (hy : 0 < y) :
    D4BMCuspResponse.average
      (horizontal (planarCurrent q reader branch side outer a t base 0)) y = 0 := by
  have hs := planarCurrent_smooth q reader branch side outer a t base 0
  have hd := planar_derivative_contDiffOn hs (1 : ℂ)
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
    (fun x _ => slice_horizontal_derivative
      (planarCurrent q reader branch side outer a t base 0) hs y hy x)
    ((slice_continuous (horizontal (planarCurrent q reader branch side outer a t base 0)) hd hy).intervalIntegrable _ _)
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 / 2 : ℝ) ≤ 1 / 2)] at he
  change D4BMCuspResponse.average
    (horizontal (planarCurrent q reader branch side outer a t base 0)) y = _
  simp only [D4BMCuspResponse.average, D4BMCuspProjection.mean]
  rw [he]
  have hp := planarCurrent_periodic q reader branch side outer a t base 0 y hy (-1 / 2)
  exact sub_eq_zero.mpr (by
    convert hp using 1 <;> norm_num)

/-- Differentiating the vertical residual face gives the full metric-current
radial defect density; periodic horizontal faces cancel exactly. -/
theorem cyclicPeierlsResidualCuspBoundary_hasDerivAt (q reader : XiZeroCopy)
    (branch side outer : Bool) (a : ℂ) (t : Iio (0 : ℝ))
    (base : {z : Point // 0 < z 1}) (y : Ioi (0 : ℝ)) :
    HasDerivAt (cyclicPeierlsResidualCuspBoundary q reader branch side outer a t base)
      (cyclicPeierlsResidualCuspDensity q reader branch side outer a t base y) y := by
  have hv := D4BMCuspResponse.average_hasDerivAt
    (planarCurrent q reader branch side outer a t base 1)
    (planarCurrent_smooth q reader branch side outer a t base 1) y.property
  have h0 := (slice_continuous
    (horizontal (planarCurrent q reader branch side outer a t base 0))
    (planar_derivative_contDiffOn
      (planarCurrent_smooth q reader branch side outer a t base 0) (1 : ℂ)) y.property).integrableOn_Ioc (μ := (volume : Measure ℝ))
          (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
  have h1 := (slice_continuous
    (vertical (planarCurrent q reader branch side outer a t base 1))
    (planar_derivative_contDiffOn
      (planarCurrent_smooth q reader branch side outer a t base 1) Complex.I) y.property).integrableOn_Ioc (μ := (volume : Measure ℝ))
          (a := (-1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
  have he : cyclicPeierlsResidualCuspDensity q reader branch side outer a t base y =
      D4BMCuspResponse.average
        (vertical (planarCurrent q reader branch side outer a t base 1)) y := by
    change (∫ x in Ioc (-1 / 2 : ℝ) (1 / 2 : ℝ),
      horizontal (planarCurrent q reader branch side outer a t base 0)
        (D4BMCuspResponse.point x y) +
      vertical (planarCurrent q reader branch side outer a t base 1)
        (D4BMCuspResponse.point x y)) = _
    rw [integral_add h0 h1]
    change D4BMCuspResponse.average
      (horizontal (planarCurrent q reader branch side outer a t base 0)) y + _ = _
    rw [horizontal_current_mean_zero q reader branch side outer a t base y.property, zero_add]
    rfl
  exact hv.congr_deriv he.symm

private theorem residualDensity_intervalIntegrable (q reader : XiZeroCopy)
    (branch side outer : Bool) (a : ℂ) (t : Iio (0 : ℝ))
    (base : {z : Point // 0 < z 1}) (u v : Ioi (0 : ℝ)) :
    IntervalIntegrable (cyclicPeierlsResidualCuspDensity q reader branch side outer a t base)
      volume (u : ℝ) v := by
  apply ContinuousOn.intervalIntegrable
  intro y hy
  exact (D4BMCuspResponse.average_hasDerivAt
    (planarDivergence q reader branch side outer a t base)
    (planarDivergence_smooth q reader branch side outer a t base)
    ((lt_min u.property v.property).trans_le hy.1)).continuousAt.continuousWithinAt

/-- Finite-height literal cyclic Peierls Stokes law.  Every finite strip of
the actual radial defect is exactly its upper residual face minus its lower
residual face.  This creates no claim about the limit as the upper height
diverges. -/
theorem cyclicPeierlsResidual_finite_cusp_stokes (q reader : XiZeroCopy)
    (branch side outer : Bool) (a : ℂ) (t : Iio (0 : ℝ))
    (base : {z : Point // 0 < z 1}) (u v : Ioi (0 : ℝ)) :
    (∫ y in (u : ℝ)..v,
      cyclicPeierlsResidualCuspDensity q reader branch side outer a t base y) =
      cyclicPeierlsResidualCuspBoundary q reader branch side outer a t base v -
        cyclicPeierlsResidualCuspBoundary q reader branch side outer a t base u := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y hy => cyclicPeierlsResidualCuspBoundary_hasDerivAt q reader branch side outer a t
      base ⟨y, (lt_min u.property v.property).trans_le hy.1⟩)
    (residualDensity_intervalIntegrable q reader branch side outer a t base u v)

/-- On the physical cusp, the finite-Stokes density is the actual original
metric/left-QNM radial defect, not a proxy current. -/
theorem planarDivergence_eq_cyclicPeierlsRadialDefect (q reader : XiZeroCopy)
    (branch side outer : Bool) (a : ℂ) (t : Iio (0 : ℝ))
    (base : {z : Point // 0 < z 1}) (w : ℂ) (hw : 0 < w.im) :
    planarDivergence q reader branch side outer a t base w =
      cyclicPeierlsRadialDefect q reader branch side outer a t
        ⟨angularCoordinates w, hw⟩ := by
  rw [planarDivergence_eq]
  symm
  exact cyclicPeierlsRadialDefect_eq_residualCurrent_divergence_at
    q reader branch side outer a t ⟨angularCoordinates w, hw⟩ base

end

end RHTower.D4BMLiteralCyclicPeierlsCapResidualCusp
