import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralCyclicPeierlsCapCurrent
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMMixedRadialOverlap

/-!
# Literal cyclic Peierls radial defect

This leaf identifies the exact residual left after replacing the full angular
Green divergence in the actual mixed metric current by the literal cyclic cap
current.  It retains, rather than discards, both surviving terms: the
square-reader divergence and the square-source cap flux.

Proof-chain role:
`actual mixed metric/left-QNM radial balance - literal cyclic cap divergence
-> explicit two-term residual -> noncompact cancellation or route obstruction
-> HB B2`.
-/

namespace RHTower.D4BMLiteralCyclicPeierlsCapRadialDefect

open Set Filter Topology
open scoped ContDiff
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open D4BMHorizon D4BMModularCore D4BMJointSource D4BMJointWave
open D4BMGlobalAngularResponse D4BMLeftModeRadialEquation
open D4BMMixedQuadraticCurrent D4BMMixedRadialOverlap
open D4BMCapAngularFluxCusp D4BMLiteralCyclicPeierlsCapCurrent

noncomputable section
set_option autoImplicit false

/-- Divergence of the literal cyclic cap current, expanded before any
noncompact integration. -/
def cyclicPeierlsAngularDivergence (q reader : XiZeroCopy) (branch : Bool)
    (z : {z : Point // 0 < z 1}) : ℂ :=
  ∑ j : Fin 2,
    coordDeriv j (angularGreenCurrent q branch reader j) z.val -
      (physicalRate q branch * (physicalRate q branch - 1) / 4) *
        coordDeriv j (angularFlux q reader j) z.val

/-- Residual between the actual mixed metric radial current and the literal
cyclic cap-current divergence.  Every coefficient is the original physical
one; no radial weight is normalized away. -/
def cyclicPeierlsRadialDefect (q reader : XiZeroCopy) (branch side outer : Bool)
    (a : ℂ) (t : Iio (0 : ℝ)) (z : {z : Point // 0 < z 1}) : ℂ :=
  let p := modePoint t z.val z.property
  let s := physicalRate q branch
  let r := (p.val 1 : ℂ)
  let E := envelope (2 * s) (a ^ 2) p.val
  let g := profile reader side outer t
  let dg := profileFirst reader side outer t
  let lam := eigenvalue reader
  let mu := parameter q branch
  let C := radialPairCoefficient s r E lam g dg 1 0
  let Omega := bulkOverlapCoefficient q reader branch side outer a t z
  (lam - mu) * current q branch a reader side outer t z 1 +
      Omega * lam * (D4BMAngularTwoTensor.source q z.val) ^ 2 *
        D4BMLiteralCusp.scalar (physicalAngularParameter reader) z.val /
          (2 * (z.val 1 : ℂ) ^ 2) -
    C * cyclicPeierlsAngularDivergence q reader branch z

/-- The physical radial coefficient of the retained source-square/reader
boundary current.  It is frozen on one radial fibre before angular
differentiation; no angular coefficient derivative is introduced. -/
def cyclicPeierlsSquareCoefficient (q reader : XiZeroCopy) (branch side outer : Bool)
    (a : ℂ) (t : Iio (0 : ℝ)) (z : {z : Point // 0 < z 1}) : ℂ :=
  bulkOverlapCoefficient q reader branch side outer a t z

/-- The physical radial coefficient of the retained cap source current. -/
def cyclicPeierlsCapFluxCoefficient (q reader : XiZeroCopy) (branch side outer : Bool)
    (a : ℂ) (t : Iio (0 : ℝ)) (z : {z : Point // 0 < z 1}) : ℂ :=
  (physicalRate q branch * (physicalRate q branch - 1) / 4) *
    radialPairCoefficient (physicalRate q branch)
      ((modePoint t z.val z.property).val 1 : ℂ)
      (envelope (2 * physicalRate q branch) (a ^ 2)
        (modePoint t z.val z.property).val)
      (eigenvalue reader) (profile reader side outer t)
      (profileFirst reader side outer t) 1 0

/-- The retained square-current coefficient has no angular dependence: the
mode point fixes time and radius before inserting the cusp point. -/
theorem cyclicPeierlsSquareCoefficient_angular_independent (q reader : XiZeroCopy)
    (branch side outer : Bool) (a : ℂ) (t : Iio (0 : ℝ))
    (z w : {z : Point // 0 < z 1}) :
    cyclicPeierlsSquareCoefficient q reader branch side outer a t z =
      cyclicPeierlsSquareCoefficient q reader branch side outer a t w := by
  rfl

/-- The retained cap-source coefficient has the same literal angular
independence. -/
theorem cyclicPeierlsCapFluxCoefficient_angular_independent (q reader : XiZeroCopy)
    (branch side outer : Bool) (a : ℂ) (t : Iio (0 : ℝ))
    (z w : {z : Point // 0 < z 1}) :
    cyclicPeierlsCapFluxCoefficient q reader branch side outer a t z =
      cyclicPeierlsCapFluxCoefficient q reader branch side outer a t w := by
  rfl

/-- The two surviving terms are one literal angular residual current.  Its
coefficients are the unchanged physical radial ones, frozen before the
angular divergence is taken. -/
def cyclicPeierlsResidualCurrent (q reader : XiZeroCopy) (branch side outer : Bool)
    (a : ℂ) (t : Iio (0 : ℝ)) (z : {z : Point // 0 < z 1})
    (j : Fin 2) : Point → ℂ := fun w =>
  cyclicPeierlsSquareCoefficient q reader branch side outer a t z *
      squareReaderCurrent q reader j w +
    cyclicPeierlsCapFluxCoefficient q reader branch side outer a t z *
      angularFlux q reader j w

private theorem scalarLaplacian_differentiableAt (S : Field) (z : Point) (hz : 0 < z 1)
    (hS : ContDiffAt ℝ 3 S z) :
    DifferentiableAt ℝ (scalarLaplacian S) z := by
  have hY : DifferentiableAt ℝ (fun w : Point => (w 1 : ℂ) ^ 2) z :=
    ((Complex.ofRealCLM.hasFDerivAt.comp z
      ((ContinuousLinearMap.proj 1 : Point →L[ℝ] ℝ).hasFDerivAt)).pow 2).differentiableAt
  have h00 :=
    (coordDeriv_hasFDerivAt (coordDeriv_contDiffAt (m := 2) hS 0) 0).differentiableAt
  have h11 :=
    (coordDeriv_hasFDerivAt (coordDeriv_contDiffAt (m := 2) hS 1) 1).differentiableAt
  have hbase : DifferentiableAt ℝ (fun w : Point => (w 1 : ℂ) ^ 2 *
      (coordDeriv 0 (coordDeriv 0 S) w + coordDeriv 1 (coordDeriv 1 S) w)) z :=
    hY.mul (h00.add h11)
  have he : scalarLaplacian S =ᶠ[𝓝 z] (fun w => (w 1 : ℂ) ^ 2 *
      (coordDeriv 0 (coordDeriv 0 S) w + coordDeriv 1 (coordDeriv 1 S) w)) := by
    have hpos : ∀ᶠ w : Point in 𝓝 z, 0 < w 1 :=
      (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz
    filter_upwards [hpos] with w hw
    exact scalarLaplacian_eq S w hw
  exact hbase.congr_of_eventuallyEq he

private theorem scalarLaplacian_contDiffAt (S : Field) (z : Point) (hz : 0 < z 1)
    (hS : ContDiffAt ℝ ∞ S z) :
    ContDiffAt ℝ ∞ (scalarLaplacian S) z := by
  have hY : ContDiffAt ℝ ∞ (fun w : Point => (w 1 : ℂ) ^ 2) z :=
    ((Complex.ofRealCLM.contDiff.comp
      ((ContinuousLinearMap.proj 1 : Point →L[ℝ] ℝ).contDiff)).pow 2).contDiffAt
  have h00 : ContDiffAt ℝ ∞ (fun w => coordDeriv 0 (coordDeriv 0 S) w) z :=
    coordDeriv_contDiffAt (m := ∞) (coordDeriv_contDiffAt (m := ∞) hS 0) 0
  have h11 : ContDiffAt ℝ ∞ (fun w => coordDeriv 1 (coordDeriv 1 S) w) z :=
    coordDeriv_contDiffAt (m := ∞) (coordDeriv_contDiffAt (m := ∞) hS 1) 1
  have hbase : ContDiffAt ℝ ∞ (fun w : Point => (w 1 : ℂ) ^ 2 *
      (coordDeriv 0 (coordDeriv 0 S) w + coordDeriv 1 (coordDeriv 1 S) w)) z :=
    hY.mul (h00.add h11)
  have he : scalarLaplacian S =ᶠ[𝓝 z] (fun w => (w 1 : ℂ) ^ 2 *
      (coordDeriv 0 (coordDeriv 0 S) w + coordDeriv 1 (coordDeriv 1 S) w)) := by
    have hpos : ∀ᶠ w : Point in 𝓝 z, 0 < w 1 :=
      (isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz
    filter_upwards [hpos] with w hw
    exact scalarLaplacian_eq S w hw
  exact hbase.congr_of_eventuallyEq he

private theorem squareReaderCurrent_differentiableAt (q reader : XiZeroCopy)
    (z : {z : Point // 0 < z 1}) (j : Fin 2) :
    DifferentiableAt ℝ (squareReaderCurrent q reader j) z.val := by
  let S := D4BMAngularTwoTensor.source q
  let R := D4BMLiteralCusp.scalar (physicalAngularParameter reader)
  have hS : ContDiffAt ℝ 2 S z.val :=
    D4BMLiteralCusp.scalar_contDiffAt (center q) 2 z.val z.property
  have hR : ContDiffAt ℝ 2 R z.val :=
    D4BMLiteralCusp.scalar_contDiffAt (physicalAngularParameter reader) 2 z.val z.property
  have hRj : DifferentiableAt ℝ (fun w => coordDeriv j R w) z.val :=
    (coordDeriv_hasFDerivAt hR j).differentiableAt
  have hSq : DifferentiableAt ℝ (fun w => S w * S w * (2 : ℂ)⁻¹) z.val :=
    ((hS.differentiableAt (by norm_num)).mul
      (hS.differentiableAt (by norm_num))).mul_const _
  have hfun : squareReaderCurrent q reader j =
      (fun w => (S w * S w * (2 : ℂ)⁻¹) * coordDeriv j R w) := by
    funext w
    simp only [squareReaderCurrent, S, R, div_eq_mul_inv]
  rw [hfun]
  exact hSq.mul hRj

/-- The retained square/reader current is smooth at every physical cusp point. -/
theorem squareReaderCurrent_contDiffAt (q reader : XiZeroCopy)
    (z : {z : Point // 0 < z 1}) (j : Fin 2) :
    ContDiffAt ℝ ∞ (squareReaderCurrent q reader j) z.val := by
  let S := D4BMAngularTwoTensor.source q
  let R := D4BMLiteralCusp.scalar (physicalAngularParameter reader)
  have hS : ContDiffAt ℝ ∞ S z.val := by
    apply contDiffAt_infty.mpr
    intro n
    exact D4BMLiteralCusp.scalar_contDiffAt (center q) n z.val z.property
  have hR : ContDiffAt ℝ ∞ R z.val := by
    apply contDiffAt_infty.mpr
    intro n
    exact D4BMLiteralCusp.scalar_contDiffAt (physicalAngularParameter reader) n z.val z.property
  have hRj : ContDiffAt ℝ ∞ (fun w => coordDeriv j R w) z.val := by
    apply coordDeriv_contDiffAt
    simpa using hR
  have hSq : ContDiffAt ℝ ∞ (fun w => S w * S w * (2 : ℂ)⁻¹) z.val :=
    ((hS.mul hS).mul_const _)
  have hfun : squareReaderCurrent q reader j =
      (fun w => (S w * S w * (2 : ℂ)⁻¹) * coordDeriv j R w) := by
    funext w
    simp only [squareReaderCurrent, S, R, div_eq_mul_inv]
  rw [hfun]
  exact hSq.mul hRj

private theorem angularFlux_differentiableAt (q reader : XiZeroCopy)
    (z : {z : Point // 0 < z 1}) (j : Fin 2) :
    DifferentiableAt ℝ (angularFlux q reader j) z.val := by
  let Q := fullSquarePotential q
  let R := D4BMLiteralCusp.scalar (physicalAngularParameter reader)
  have hQ : ContDiffAt ℝ 3 Q z.val :=
    fullSquarePotential_smooth q z.val z.property 3
  have hR : ContDiffAt ℝ 3 R z.val :=
    D4BMLiteralCusp.scalar_contDiffAt (physicalAngularParameter reader) 3 z.val z.property
  have hQj : DifferentiableAt ℝ (fun w => coordDeriv j Q w) z.val :=
    (coordDeriv_hasFDerivAt (hQ.of_le (by norm_num)) j).differentiableAt
  have hRj : DifferentiableAt ℝ (fun w => coordDeriv j R w) z.val :=
    (coordDeriv_hasFDerivAt (hR.of_le (by norm_num)) j).differentiableAt
  have hL : DifferentiableAt ℝ (scalarLaplacian Q) z.val :=
    scalarLaplacian_differentiableAt Q z.val z.property hQ
  have hfun : angularFlux q reader j = fun w =>
      (physicalAngularParameter reader ^ 2 - 1 / 4) * R w * coordDeriv j Q w -
        scalarLaplacian Q w * coordDeriv j R w := by
    funext w
    exact angularFlux_eq q reader j w
  rw [hfun]
  exact (((hR.differentiableAt (by norm_num)).const_mul _).mul hQj).sub (hL.mul hRj)

private theorem angularFlux_contDiffAt (q reader : XiZeroCopy)
    (z : {z : Point // 0 < z 1}) (j : Fin 2) :
    ContDiffAt ℝ ∞ (angularFlux q reader j) z.val := by
  let Q := fullSquarePotential q
  let R := D4BMLiteralCusp.scalar (physicalAngularParameter reader)
  have hS : ContDiffAt ℝ ∞ (D4BMLiteralCusp.scalar (center q)) z.val := by
    apply contDiffAt_infty.mpr
    intro n
    exact D4BMLiteralCusp.scalar_contDiffAt (center q) n z.val z.property
  have hQ : ContDiffAt ℝ ∞ Q z.val := by
    change ContDiffAt ℝ ∞ (fun w =>
      (1 / 2 : ℂ) * (D4BMLiteralCusp.scalar (center q) w *
        D4BMLiteralCusp.scalar (center q) w)) z.val
    exact contDiffAt_const.mul (hS.mul hS)
  have hR : ContDiffAt ℝ ∞ R z.val := by
    apply contDiffAt_infty.mpr
    intro n
    exact D4BMLiteralCusp.scalar_contDiffAt (physicalAngularParameter reader) n z.val z.property
  have hQj : ContDiffAt ℝ ∞ (fun w => coordDeriv j Q w) z.val := by
    apply coordDeriv_contDiffAt
    simpa using hQ
  have hRj : ContDiffAt ℝ ∞ (fun w => coordDeriv j R w) z.val := by
    apply coordDeriv_contDiffAt
    simpa using hR
  have hL : ContDiffAt ℝ ∞ (scalarLaplacian Q) z.val :=
    scalarLaplacian_contDiffAt Q z.val z.property hQ
  have hfun : angularFlux q reader j = fun w =>
      (physicalAngularParameter reader ^ 2 - 1 / 4) * R w * coordDeriv j Q w -
        scalarLaplacian Q w * coordDeriv j R w := by
    funext w
    exact angularFlux_eq q reader j w
  rw [hfun]
  exact ((hR.const_mul _).mul hQj).sub (hL.mul hRj)

/-- The literal residual current is smooth throughout the physical upper
half-plane.  This is the regularity input for finite-cusp Stokes, not a
claim about its noncompact limit. -/
theorem cyclicPeierlsResidualCurrent_contDiffAt (q reader : XiZeroCopy)
    (branch side outer : Bool) (a : ℂ) (t : Iio (0 : ℝ))
    (base : {z : Point // 0 < z 1}) (j : Fin 2)
    (z : Point) (hz : 0 < z 1) :
    ContDiffAt ℝ ∞ (cyclicPeierlsResidualCurrent q reader branch side outer a t base j) z := by
  unfold cyclicPeierlsResidualCurrent
  exact (contDiffAt_const.mul
    (squareReaderCurrent_contDiffAt q reader ⟨z, hz⟩ j)).add
      (contDiffAt_const.mul (angularFlux_contDiffAt q reader ⟨z, hz⟩ j))

/-- Exact divergence law for the one residual current.  This is the positive
survivor of the cap-current substitution: after angular integration it has
only literal boundary faces, not an unexplained bulk error. -/
theorem cyclicPeierlsResidualCurrent_divergence (q reader : XiZeroCopy)
    (branch side outer : Bool) (a : ℂ) (t : Iio (0 : ℝ))
    (base z : {z : Point // 0 < z 1}) :
    (∑ j : Fin 2, coordDeriv j
      (cyclicPeierlsResidualCurrent q reader branch side outer a t base j) z.val) =
      cyclicPeierlsSquareCoefficient q reader branch side outer a t base *
        (∑ j : Fin 2, coordDeriv j (squareReaderCurrent q reader j) z.val) +
      cyclicPeierlsCapFluxCoefficient q reader branch side outer a t base *
        (∑ j : Fin 2, coordDeriv j (angularFlux q reader j) z.val) := by
  let A := cyclicPeierlsSquareCoefficient q reader branch side outer a t base
  let B := cyclicPeierlsCapFluxCoefficient q reader branch side outer a t base
  change (∑ j : Fin 2, coordDeriv j (fun w =>
      A * squareReaderCurrent q reader j w + B * angularFlux q reader j w) z.val) =
    A * (∑ j : Fin 2, coordDeriv j (squareReaderCurrent q reader j) z.val) +
      B * (∑ j : Fin 2, coordDeriv j (angularFlux q reader j) z.val)
  have hA (j : Fin 2) : coordDeriv j (fun w => A * squareReaderCurrent q reader j w) z.val =
      A * coordDeriv j (squareReaderCurrent q reader j) z.val := by
    have h := (squareReaderCurrent_differentiableAt q reader z j).hasFDerivAt.const_mul A
    simpa only [coordDeriv, smul_apply, smul_eq_mul] using
      congrArg (fun L => L (Pi.single j 1)) h.fderiv
  have hB (j : Fin 2) : coordDeriv j (fun w => B * angularFlux q reader j w) z.val =
      B * coordDeriv j (angularFlux q reader j) z.val := by
    have h := (angularFlux_differentiableAt q reader z j).hasFDerivAt.const_mul B
    simpa only [coordDeriv, smul_apply, smul_eq_mul] using
      congrArg (fun L => L (Pi.single j 1)) h.fderiv
  calc
    _ = ∑ j : Fin 2,
        A * coordDeriv j (squareReaderCurrent q reader j) z.val +
          B * coordDeriv j (angularFlux q reader j) z.val := by
      apply Finset.sum_congr rfl
      intro j _
      rw [coordDeriv_add
        ((squareReaderCurrent_differentiableAt q reader z j).const_mul A)
        ((angularFlux_differentiableAt q reader z j).const_mul B), hA, hB]
    _ = _ := by
      simp only [Fin.sum_univ_two]
      ring

/-- Exact positive survivor of the cap-current replacement.  A literal B2
cap/contact equality must cancel this displayed pair, or prove that it cannot
cancel; neither term may be silently absorbed into a scalar Green boundary. -/
theorem cyclicPeierlsRadialDefect_eq (q reader : XiZeroCopy) (branch side outer : Bool)
    (a : ℂ) (t : Iio (0 : ℝ)) (z : {z : Point // 0 < z 1}) :
    cyclicPeierlsRadialDefect q reader branch side outer a t z =
      bulkOverlapCoefficient q reader branch side outer a t z *
        (∑ j : Fin 2, coordDeriv j (squareReaderCurrent q reader j) z.val) +
      (physicalRate q branch * (physicalRate q branch - 1) / 4) *
        radialPairCoefficient (physicalRate q branch)
          ((modePoint t z.val z.property).val 1 : ℂ)
          (envelope (2 * physicalRate q branch) (a ^ 2)
            (modePoint t z.val z.property).val)
          (eigenvalue reader) (profile reader side outer t)
          (profileFirst reader side outer t) 1 0 *
        (∑ j : Fin 2, coordDeriv j (angularFlux q reader j) z.val) := by
  unfold cyclicPeierlsRadialDefect cyclicPeierlsAngularDivergence
  rw [original_radial_triple_balance q reader branch side outer a t z]
  ring

/-- The actual radial defect is exactly the divergence of the literal
residual current.  Therefore a B2 noncompact argument must analyze its cusp
boundary faces; it cannot leave a separate angular bulk term. -/
theorem cyclicPeierlsRadialDefect_eq_residualCurrent_divergence
    (q reader : XiZeroCopy) (branch side outer : Bool) (a : ℂ)
    (t : Iio (0 : ℝ)) (z : {z : Point // 0 < z 1}) :
    cyclicPeierlsRadialDefect q reader branch side outer a t z =
      ∑ j : Fin 2, coordDeriv j
        (cyclicPeierlsResidualCurrent q reader branch side outer a t z j) z.val := by
  rw [cyclicPeierlsRadialDefect_eq]
  symm
  simpa only [cyclicPeierlsSquareCoefficient, cyclicPeierlsCapFluxCoefficient] using
    cyclicPeierlsResidualCurrent_divergence q reader branch side outer a t z z

/-- The radial defect equals the divergence of any one frozen fibre current
at every positive angular point.  This is the literal local law needed before
finite-cusp Stokes can turn the defect into boundary faces. -/
theorem cyclicPeierlsRadialDefect_eq_residualCurrent_divergence_at
    (q reader : XiZeroCopy) (branch side outer : Bool) (a : ℂ)
    (t : Iio (0 : ℝ)) (z base : {z : Point // 0 < z 1}) :
    cyclicPeierlsRadialDefect q reader branch side outer a t z =
      ∑ j : Fin 2, coordDeriv j
        (cyclicPeierlsResidualCurrent q reader branch side outer a t base j) z.val := by
  rw [cyclicPeierlsRadialDefect_eq]
  symm
  rw [cyclicPeierlsResidualCurrent_divergence]
  rw [cyclicPeierlsSquareCoefficient_angular_independent q reader branch side outer a t base z,
    cyclicPeierlsCapFluxCoefficient_angular_independent q reader branch side outer a t base z]

end

end RHTower.D4BMLiteralCyclicPeierlsCapRadialDefect
