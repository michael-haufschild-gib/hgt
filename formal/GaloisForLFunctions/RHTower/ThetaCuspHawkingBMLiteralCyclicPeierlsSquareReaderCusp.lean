import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralCyclicPeierlsCapResidualCusp
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedParticularCuspFlux

/-!
# Literal square-reader cusp face

The first survivor in the cyclic Peierls radial defect has an exact cusp
decomposition.  Its full integrated face is its two-Weyl principal reader
face plus one half of the already retained full Fourier forcing tail.  Thus
this survivor has no unanalysed noncompact remainder; no assertion is made
about the independent cap angular-flux survivor.

Proof-chain role:
`residual current -> square-reader cusp face = principal face + decaying tail
-> isolate cap angular-flux finite part as sole remaining B2 cusp analysis
-> contact boundary comparison -> HB B2`.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane
open scoped BigOperators ContDiff

namespace RHTower.D4BMLiteralCyclicPeierlsSquareReaderCusp

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open GaloisForLFunctions.RHTower.SelbergMaassMean
open D4BMHorizon D4BMModularCore D4BMGlobalAngularResponse D4BMJointSource
open D4BMMixedRadialOverlap D4BMMixedParticularCuspFlux D4BMQuarticTestedNativeCurrent
open D4BMLiteralCyclicPeierlsCapRadialDefect

noncomputable section
set_option autoImplicit false

/-- Full literal square-reader vertical face on one width-one cusp section. -/
def squareReaderCuspFlux (q reader : XiZeroCopy) (y : ℝ) : ℂ :=
  ∫ x in Ioc (-1 / 2 : ℝ) (1 / 2 : ℝ), squareReaderCurrent q reader 1 ![x, y]

/-- The exact two-Weyl principal part of the square-reader face. -/
def squareReaderPrincipalCuspFlux (q reader : XiZeroCopy) (y : ℝ) : ℂ :=
  principal (center q) ![0, y] ^ (2 : ℕ) / 2 *
    readerCoefficient reader * readerPower reader * (y : ℂ) ^ (readerPower reader - 1)

private theorem physicalTest_smooth (r : XiZeroCopy) :
    ContDiffOn ℝ ∞ (physicalTest r) {z : ℂ | 0 < z.im} := by
  intro z hz
  have h := (D4BMAngularSeries.cuspLeg_contDiffOn .scalar (physicalAngularParameter r)).contDiffAt
    ((isOpen_lt continuous_const (continuous_apply 1)).mem_nhds
      (show 0 < angularCoordinates z 1 from hz))
  exact (h.comp z angularCoordinates.contDiff.contDiffAt).contDiffWithinAt

private theorem physicalTest_mean (r : XiZeroCopy) (y : Ioi (0 : ℝ)) :
    D4BMCuspResponse.average (physicalTest r) y =
      readerCoefficient r * (y : ℂ) ^ readerPower r := by
  let u := physicalAngularParameter r
  have he (x : ℝ) : physicalTest r (D4BMCuspResponse.point x y) =
      principal u ![0, y.val] + tail u ![x, y.val] := by
    simp [physicalTest, scalar, D4BMGlobalAngularResponse.principal, tail,
      d4BMCompletedEisensteinCuspLeg,
      angularCoordinates, D4BMCuspResponse.point, u]
  have ht : Continuous (fun x : ℝ => tail u ![x, y.val]) := by
    have hh : (fun x : ℝ => tail u ![x, y.val]) =
        fun x => physicalTest r (D4BMCuspResponse.point x y) - principal u ![0, y.val] := by
      funext x
      rw [he]
      ring
    rw [hh]
    exact (GaloisForLFunctions.RHTower.SelbergMaassMean.slice_continuous
      (physicalTest_smooth r).continuousOn y.property).sub continuous_const
  change (∫ x in Ioc (-1 / 2 : ℝ) (1 / 2 : ℝ),
    physicalTest r (D4BMCuspResponse.point x y)) = _
  simp_rw [he]
  rw [integral_add (integrable_const _) ht.integrableOn_Ioc]
  have hm := D4BMCuspProjection.mean_tail u y.property
  change (∫ x in Ioc (-1 / 2 : ℝ) (1 / 2), tail u ![x, y.val]) = 0 at hm
  rw [hm, add_zero]
  norm_num
  exact physicalScalar_principal r ![0, y.val]

private theorem physicalTest_vertical_mean (r : XiZeroCopy) (y : Ioi (0 : ℝ)) :
    D4BMCuspResponse.average (directional Complex.I (physicalTest r)) y =
      readerCoefficient r * readerPower r * (y : ℂ) ^ (readerPower r - 1) := by
  have h := D4BMCuspResponse.average_hasDerivAt (physicalTest r) (physicalTest_smooth r) y.property
  have hm : HasDerivAt (fun t : ℝ => readerCoefficient r * (t : ℂ) ^ readerPower r)
      (D4BMCuspResponse.average (directional Complex.I (physicalTest r)) y) y := by
    apply h.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds y.property] with t ht
    exact (physicalTest_mean r ⟨t, ht⟩).symm
  have hp := (GaloisForLFunctions.RHTower.hasDerivAt_cpow_ofReal
    (w := readerPower r) y.property).const_mul (readerCoefficient r)
  simpa only [mul_assoc] using hm.unique hp

private theorem reader_vertical (r : XiZeroCopy) (x y : ℝ) :
    coordDeriv 1 (D4BMLiteralCusp.scalar (physicalAngularParameter r)) ![x, y] =
      directional Complex.I (physicalTest r) (D4BMCuspResponse.point x y) := by
  change coordDeriv 1 (D4BMLiteralCusp.scalar (physicalAngularParameter r)) ![x, y] =
    fderiv ℝ ((D4BMLiteralCusp.scalar (physicalAngularParameter r)) ∘ angularCoordinates)
      (D4BMCuspResponse.point x y) Complex.I
  have h := angularCoordinates_derivative
    (D4BMLiteralCusp.scalar (physicalAngularParameter r)) 1 (D4BMCuspResponse.point x y)
  simpa only [direction, Matrix.cons_val_one, Matrix.cons_val_zero,
    show angularCoordinates (D4BMCuspResponse.point x y) = ![x, y] by
      simp [angularCoordinates, D4BMCuspResponse.point]] using h.symm

/-- Exact decomposition of the full square-reader face.  The complete
Fourier remainder is retained in `forcingTail`; no mode is deleted. -/
theorem squareReaderCuspFlux_eq_principal_add_forcingTail (q reader : XiZeroCopy)
    (y : Ioi (0 : ℝ)) :
    squareReaderCuspFlux q reader y =
      squareReaderPrincipalCuspFlux q reader y + (1 / 2 : ℂ) * forcingTail q reader y := by
  let P : ℂ := principal (center q) ![0, y.val]
  let F : ℝ → ℂ := fun x => squareReaderCurrent q reader 1 ![x, y.val]
  let A : ℝ → ℂ := fun x => P ^ (2 : ℕ) / 2 *
    directional Complex.I (physicalTest reader) (D4BMCuspResponse.point x y.val)
  let B : ℝ → ℂ := fun x => (1 / 2 : ℂ) * squareRemainder (center q) ![x, y.val] *
    directional Complex.I (physicalTest reader) (D4BMCuspResponse.point x y.val)
  have hFA (x : ℝ) : F x = A x + B x := by
    dsimp only [F, A, B, P]
    change D4BMAngularTwoTensor.source q ![x, y.val] ^ (2 : ℕ) / 2 *
        coordDeriv 1 (D4BMLiteralCusp.scalar (physicalAngularParameter reader)) ![x, y.val] = _
    rw [reader_vertical]
    change D4BMLiteralCusp.scalar (center q) ![x, y.val] ^ (2 : ℕ) / 2 *
        directional Complex.I (physicalTest reader) (D4BMCuspResponse.point x y.val) = _
    have hp : principal (center q) ![x, y.val] = principal (center q) ![0, y.val] := rfl
    rw [show squareRemainder (center q) ![x, y.val] =
      D4BMLiteralCusp.scalar (center q) ![x, y.val] ^ (2 : ℕ) -
        principal (center q) ![x, y.val] ^ (2 : ℕ) by rfl, hp]
    ring
  have hFsmooth : ContDiffOn ℝ ∞ (squareReaderCurrent q reader 1)
      {z : Point | 0 < z 1} := by
    intro z hz
    exact (squareReaderCurrent_contDiffAt q reader ⟨z, hz⟩ 1).contDiffWithinAt
  have hmap : Continuous (fun x : ℝ => (![x, y.val] : Point)) := by fun_prop
  have cF : Continuous F := by
    dsimp only [F]
    refine hFsmooth.continuousOn.comp_continuous hmap ?_
    intro x
    show (0 : ℝ) < (![x, y.val] : Point) 1
    simp only [Matrix.cons_val_one]
    exact y.property
  have cV : Continuous (fun x : ℝ =>
      directional Complex.I (physicalTest reader) (D4BMCuspResponse.point x y.val)) :=
    GaloisForLFunctions.RHTower.SelbergMaassMean.slice_continuous
      (planar_derivative_contDiffOn (physicalTest_smooth reader) Complex.I).continuousOn
      y.property
  have cA : Continuous A := cV.const_mul _
  have cB : Continuous B := by
    have hB : B = fun x => F x - A x := by
      funext x
      rw [hFA]
      ring
    rw [hB]
    exact cF.sub cA
  have hsplit : (∫ x in Ioc (-1 / 2 : ℝ) (1 / 2 : ℝ), F x) =
      (∫ x in Ioc (-1 / 2 : ℝ) (1 / 2 : ℝ), A x) +
        ∫ x in Ioc (-1 / 2 : ℝ) (1 / 2 : ℝ), B x := by
    calc
      _ = ∫ x in Ioc (-1 / 2 : ℝ) (1 / 2 : ℝ), A x + B x := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x _
        exact hFA x
      _ = _ := integral_add cA.integrableOn_Ioc cB.integrableOn_Ioc
  have hV : (∫ x in Ioc (-1 / 2 : ℝ) (1 / 2 : ℝ),
      directional Complex.I (physicalTest reader) (D4BMCuspResponse.point x y.val)) =
      readerCoefficient reader * readerPower reader *
        (y.val : ℂ) ^ (readerPower reader - 1) := by
    change D4BMCuspResponse.average (directional Complex.I (physicalTest reader)) y = _
    exact physicalTest_vertical_mean reader y
  have hA : (∫ x in Ioc (-1 / 2 : ℝ) (1 / 2 : ℝ), A x) =
      P ^ (2 : ℕ) / 2 * readerCoefficient reader * readerPower reader *
        (y.val : ℂ) ^ (readerPower reader - 1) := by
    dsimp only [A]
    rw [integral_const_mul, hV]
    ring
  have hB : (∫ x in Ioc (-1 / 2 : ℝ) (1 / 2 : ℝ), B x) =
      (1 / 2 : ℂ) * forcingTail q reader y := by
    dsimp only [B, forcingTail]
    simp_rw [mul_assoc]
    rw [integral_const_mul]
    rfl
  unfold squareReaderCuspFlux squareReaderPrincipalCuspFlux
  change (∫ x in Ioc (-1 / 2 : ℝ) (1 / 2 : ℝ), F x) = _
  rw [hsplit, hA, hB]

/-- The full Fourier remainder of the square-reader face vanishes at the
cusp.  This fully discharges the first survivor's noncompact tail. -/
theorem squareReaderCuspFlux_sub_principal_tendsto_zero (q reader : XiZeroCopy) :
    Tendsto (fun y : ℝ =>
      squareReaderCuspFlux q reader y - squareReaderPrincipalCuspFlux q reader y)
      atTop (𝓝 0) := by
  have h := (forcingTail_weighted_tendsto_zero q reader 0).const_mul (1 / 2 : ℂ)
  simp only [Complex.cpow_zero, one_mul, mul_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  rw [squareReaderCuspFlux_eq_principal_add_forcingTail q reader ⟨y, hy⟩]
  ring

end

end RHTower.D4BMLiteralCyclicPeierlsSquareReaderCusp
