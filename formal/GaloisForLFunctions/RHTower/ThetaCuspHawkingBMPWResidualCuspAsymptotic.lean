import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralCyclicPeierlsSquareReaderCusp
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLiteralCyclicPeierlsCapAngularFluxIntegral

/-!
The literal cyclic-Peierls radial residual current has a source-faithful outer cusp face.
Its two frozen-coefficient summands reduce to explicit principal channels, with the
complete angular and square-reader remainders vanishing under every fixed complex
height weight. This is a cusp-face theorem, not a CTP/current incidence theorem.
-/

open MeasureTheory Set Filter Topology
open RHTower
open RHTower.D4BMModularCore RHTower.D4BMGlobalAngularResponse
open RHTower.D4BMJointSource RHTower.D4BMMixedRadialOverlap
open RHTower.D4BMCapAngularFluxCusp
open RHTower.D4BMLiteralCyclicPeierlsCapRadialDefect
open RHTower.D4BMLiteralCyclicPeierlsCapResidualCusp
open RHTower.D4BMLiteralCyclicPeierlsSquareReaderCusp
open RHTower.D4BMLiteralCyclicPeierlsCapAngularFluxIntegral
open RHTower.D4BMMixedParticularCuspFlux

namespace RHTower.D4BMPWResidualCuspAsymptotic
noncomputable section
set_option autoImplicit false

def capRemainder (q reader : XiZeroCopy) (y : ℝ) : ℂ :=
  ∫ x in Ioc (-1/2 : ℝ) (1/2 : ℝ),
    angularFlux q reader 1 ![x,y] -
      constantVerticalFlux (center q) (physicalAngularParameter reader) y

def residualPrincipal (q reader : XiZeroCopy) (branch side outer : Bool)
    (a : ℂ) (t : Iio (0 : ℝ)) (base : {z : D4BMHorizon.Point // 0 < z 1})
    (y : ℝ) : ℂ :=
  cyclicPeierlsSquareCoefficient q reader branch side outer a t base *
    squareReaderPrincipalCuspFlux q reader y +
  cyclicPeierlsCapFluxCoefficient q reader branch side outer a t base *
    constantVerticalFlux (center q) (physicalAngularParameter reader) y

private theorem boundary_split (q reader : XiZeroCopy) (branch side outer : Bool)
    (a : ℂ) (t : Iio (0 : ℝ)) (base : {z : D4BMHorizon.Point // 0 < z 1})
    {y : ℝ} (hy : 0 < y) :
    cyclicPeierlsResidualCuspBoundary q reader branch side outer a t base y =
      cyclicPeierlsSquareCoefficient q reader branch side outer a t base *
        squareReaderCuspFlux q reader y +
      cyclicPeierlsCapFluxCoefficient q reader branch side outer a t base *
        (constantVerticalFlux (center q) (physicalAngularParameter reader) y +
          capRemainder q reader y) := by
  let A := cyclicPeierlsSquareCoefficient q reader branch side outer a t base
  let B := cyclicPeierlsCapFluxCoefficient q reader branch side outer a t base
  let S : ℝ → ℂ := fun x => squareReaderCurrent q reader 1 ![x,y]
  let G : ℝ → ℂ := fun x => angularFlux q reader 1 ![x,y]
  let F : ℝ → ℂ := fun x => cyclicPeierlsResidualCurrent q reader branch side outer a t base 1 ![x,y]
  let C := constantVerticalFlux (center q) (physicalAngularParameter reader) y
  have hF : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hc : ContinuousAt (fun u : ℝ => (![u,y] : D4BMHorizon.Point)) x := by fun_prop
    simpa only [Function.comp_def] using
      (ContinuousAt.comp (f := fun u : ℝ => (![u,y] : D4BMHorizon.Point))
        (cyclicPeierlsResidualCurrent_contDiffAt q reader branch side outer a t
          base 1 ![x,y] (by simpa using hy)).continuousAt hc)
  have hS : Continuous S := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hc : ContinuousAt (fun u : ℝ => (![u,y] : D4BMHorizon.Point)) x := by fun_prop
    simpa only [Function.comp_def] using
      (ContinuousAt.comp (f := fun u : ℝ => (![u,y] : D4BMHorizon.Point))
        (squareReaderCurrent_contDiffAt q reader ⟨![x,y], by simpa using hy⟩
          1).continuousAt hc)
  have hBG : Continuous (fun x => B * G x) := by
    have he : (fun x => B * G x) = F - (fun x => A * S x) := by
      funext x
      dsimp [F,S,G,A,B]
      simp only [cyclicPeierlsResidualCurrent]
      ring
    rw [he]
    exact hF.sub (hS.const_mul A)
  have hSint : IntegrableOn (fun x => A*S x) (Ioc (-1/2 : ℝ) (1/2 : ℝ)) :=
    (hS.const_mul A).integrableOn_Ioc
  have hGint : IntegrableOn (fun x => B*G x) (Ioc (-1/2 : ℝ) (1/2 : ℝ)) :=
    hBG.integrableOn_Ioc
  have heF (x : ℝ) : F x = A*S x+B*G x := by
    dsimp [F,S,G,A,B,cyclicPeierlsResidualCurrent]
  have hcoord (x : ℝ) :
      angularCoordinates (RHTower.D4BMCuspResponse.point x y) = ![x,y] := by
    ext j
    fin_cases j <;> simp [angularCoordinates,RHTower.D4BMCuspResponse.point]
  have hJ : cyclicPeierlsResidualCuspBoundary q reader branch side outer a t base y =
      ∫ x in Ioc (-1/2 : ℝ) (1/2 : ℝ), F x := by
    unfold cyclicPeierlsResidualCuspBoundary RHTower.D4BMCuspResponse.average
      RHTower.D4BMCuspProjection.mean
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x _
    exact congrArg (cyclicPeierlsResidualCurrent q reader branch side outer a t base 1)
      (hcoord x)
  have hsplit : (∫ x in Ioc (-1/2 : ℝ) (1/2 : ℝ), F x) =
      A * squareReaderCuspFlux q reader y +
        ∫ x in Ioc (-1/2 : ℝ) (1/2 : ℝ), B*G x := by
    calc
      _ = ∫ x in Ioc (-1/2 : ℝ) (1/2 : ℝ), A*S x+B*G x := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x _
        exact heF x
      _ = _ := by
        rw [integral_add hSint hGint, integral_const_mul]
        rfl
  have hrem : (∫ x in Ioc (-1/2 : ℝ) (1/2 : ℝ), B*G x) =
      B*(C+capRemainder q reader y) := by
    have hconst : IntegrableOn (fun _ : ℝ => B*C) (Ioc (-1/2 : ℝ) (1/2 : ℝ)) :=
      integrable_const _
    have hdiff : IntegrableOn (fun x => B*G x-B*C) (Ioc (-1/2 : ℝ) (1/2 : ℝ)) :=
      hGint.sub hconst
    calc
      _ = (∫ x in Ioc (-1/2 : ℝ) (1/2 : ℝ), (B*C)+(B*G x-B*C)) := by
        apply setIntegral_congr_fun measurableSet_Ioc
        intro x _
        ring
      _ = B*C + ∫ x in Ioc (-1/2 : ℝ) (1/2 : ℝ), B*(G x-C) := by
        rw [integral_add hconst hdiff]
        norm_num
        congr 1
        funext x
        ring
      _ = _ := by
        rw [integral_const_mul]
        dsimp [capRemainder,G,C]
        ring
  rw [hJ, hsplit, hrem]

/-- The full literal residual cusp face has no unweighted tail beyond its two
explicit principal channels. -/
theorem residualCuspBoundary_sub_principal_tendsto_zero
    (q reader : XiZeroCopy) (branch side outer : Bool) (a : ℂ)
    (t : Iio (0 : ℝ)) (base : {z : D4BMHorizon.Point // 0 < z 1}) :
    Tendsto (fun y : ℝ =>
      cyclicPeierlsResidualCuspBoundary q reader branch side outer a t base y -
        residualPrincipal q reader branch side outer a t base y)
      atTop (𝓝 0) := by
  have hSq := squareReaderCuspFlux_sub_principal_tendsto_zero q reader
  have hCap : Tendsto (capRemainder q reader) atTop (𝓝 0) := by
    have h := angularFlux_remainder_integral_tendsto_zero q reader 0
    simp only [Complex.cpow_zero,one_mul] at h
    apply h.congr'
    filter_upwards with y
    dsimp [capRemainder]
    rw [← intervalIntegral.integral_of_le (by norm_num : (-1/2 : ℝ) ≤ 1/2)]
  let A := cyclicPeierlsSquareCoefficient q reader branch side outer a t base
  let B := cyclicPeierlsCapFluxCoefficient q reader branch side outer a t base
  have h := (hSq.const_mul A).add (hCap.const_mul B)
  simp only [mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  rw [boundary_split q reader branch side outer a t base hy]
  dsimp [residualPrincipal, A, B]
  ring

/-- Both complete Fourier remainders vanish after any fixed complex height power;
neither physical current summand nor its frozen radial coefficient is discarded. -/
theorem residualCuspBoundary_weighted_sub_principal_tendsto_zero
    (q reader : XiZeroCopy) (branch side outer : Bool) (a w : ℂ)
    (t : Iio (0 : ℝ)) (base : {z : D4BMHorizon.Point // 0 < z 1}) :
    Tendsto (fun y : ℝ => (y : ℂ) ^ w *
      (cyclicPeierlsResidualCuspBoundary q reader branch side outer a t base y -
        residualPrincipal q reader branch side outer a t base y))
      atTop (𝓝 0) := by
  have hSq : Tendsto (fun y : ℝ => (y : ℂ) ^ w *
      (squareReaderCuspFlux q reader y - squareReaderPrincipalCuspFlux q reader y))
      atTop (𝓝 0) := by
    have h := (forcingTail_weighted_tendsto_zero q reader w).const_mul (1 / 2 : ℂ)
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    rw [squareReaderCuspFlux_eq_principal_add_forcingTail q reader ⟨y,hy⟩]
    ring
  have hCap : Tendsto (fun y : ℝ => (y : ℂ) ^ w * capRemainder q reader y)
      atTop (𝓝 0) := by
    have h := angularFlux_remainder_integral_tendsto_zero q reader w
    apply h.congr'
    filter_upwards with y
    dsimp [capRemainder]
    rw [← intervalIntegral.integral_of_le (by norm_num : (-1/2 : ℝ) ≤ 1/2)]
    rw [intervalIntegral.integral_const_mul]
  let A := cyclicPeierlsSquareCoefficient q reader branch side outer a t base
  let B := cyclicPeierlsCapFluxCoefficient q reader branch side outer a t base
  have h := (hSq.const_mul A).add (hCap.const_mul B)
  simp only [mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  rw [boundary_split q reader branch side outer a t base hy]
  dsimp [residualPrincipal, A, B]
  ring

end
end RHTower.D4BMPWResidualCuspAsymptotic
