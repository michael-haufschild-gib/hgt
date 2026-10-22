import GaloisForLFunctions.RHTower.Suzuki.SuzukiProjectedContinuousDeficiency
import GaloisForLFunctions.RHTower.Suzuki.SuzukiSecondDefectParityCommutator
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

/-!
# Compact Suzuki response: exact parity endpoint jets

For a real compact-interval deficiency response `u`, the four quantities

* `E = ∫ u(x) cosh(x) dx`,
* `O = ∫ u(x) sinh(x) dx`,
* `alpha = ∫ x u(x) sinh(x) dx`,
* `beta = ∫ x u(x) cosh(x) dx`

are the even energy, odd energy, even tilt, and odd tilt channels.  Symmetry of the interval makes
the displayed weights parity selectors; no parity assumption on `u` is needed.

This file proves, rather than assumes, the endpoint data used by the second-defect theorem:

`F(i)=E-O`, `F(-i)=E+O`,

`F'(i)=i(beta-alpha)`, `F'(-i)=i(alpha+beta)`,

where `F(z)=∫_{-a}^a u(x)e^{ixz}dx`.  Consequently the second disk jet of every real Suzuki
compact response is exactly its parity curvature.  The result removes the last abstract endpoint
hypotheses from the source-side second-jet law.

No RH assumption, asymptotic replacement, or numerical computation occurs.
-/

open Complex Filter MeasureTheory Set

namespace RHTower

noncomputable section

/-! ## The four compact parity channels -/

/-- Cosh-weighted even channel of a real compact Suzuki response. -/
def suzukiCompactEvenEnergy (u : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ x in -a..a, u x * Real.cosh x

/-- Sinh-weighted odd channel of a real compact Suzuki response. -/
def suzukiCompactOddEnergy (u : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ x in -a..a, u x * Real.sinh x

/-- Exponential-tilt moment of the even response channel. -/
def suzukiCompactEvenTilt (u : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ x in -a..a, x * u x * Real.sinh x

/-- Exponential-tilt moment of the odd response channel. -/
def suzukiCompactOddTilt (u : ℝ → ℝ) (a : ℝ) : ℝ :=
  ∫ x in -a..a, x * u x * Real.cosh x

/-! ## Holomorphic spectral differentiation -/

/-- A continuous real compact response may be differentiated under Suzuki's Fourier integral.
The derivative is its exact first spectral moment. -/
theorem hasDerivAt_suzukiProjectedIntervalFourier_ofReal
    (u : ℝ → ℝ) (a : ℝ) (z : ℂ) (hu : Continuous u) :
    HasDerivAt
      (suzukiProjectedIntervalFourier (fun x => (u x : ℂ)) a)
      (∫ x in -a..a,
        (u x : ℂ) * ((x : ℂ) * I) * suzukiOscillatoryKernel z x) z := by
  let F : ℂ → ℝ → ℂ := fun w x =>
    (u x : ℂ) * suzukiOscillatoryKernel w x
  let F' : ℂ → ℝ → ℂ := fun w x =>
    (u x : ℂ) * ((x : ℂ) * I) * suzukiOscillatoryKernel w x
  let K : Set (ℂ × ℝ) := Metric.closedBall z 1 ×ˢ Set.uIcc (-a) a
  have hFcont : ∀ w : ℂ, ContinuousOn (F w) (Set.uIcc (-a) a) := by
    intro w
    dsimp only [F, suzukiOscillatoryKernel]
    fun_prop
  have hF'cont : ∀ w : ℂ, ContinuousOn (F' w) (Set.uIcc (-a) a) := by
    intro w
    dsimp only [F', suzukiOscillatoryKernel]
    fun_prop
  have hKcompact : IsCompact K :=
    IsCompact.prod (isCompact_closedBall z 1) isCompact_uIcc
  have hderivCont : ContinuousOn
      (fun p : ℂ × ℝ => ‖F' p.1 p.2‖) K := by
    dsimp only [F', suzukiOscillatoryKernel]
    fun_prop
  obtain ⟨R, hR⟩ := hKcompact.exists_bound_of_continuousOn hderivCont
  have hresult :=
    intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := volume) (a := -a) (b := a) (F := F) (F' := F')
      (x₀ := z) (s := Metric.ball z 1) (bound := fun _ => R)
      (Metric.ball_mem_nhds z (by norm_num))
      (Filter.Eventually.of_forall fun w =>
        ((hFcont w).mono Set.uIoc_subset_uIcc).aestronglyMeasurable
          measurableSet_uIoc)
      ((hFcont z).intervalIntegrable)
      (((hF'cont z).mono Set.uIoc_subset_uIcc).aestronglyMeasurable
        measurableSet_uIoc)
      (by
        filter_upwards with x
        intro hx w hw
        simpa only [Prod.fst, Prod.snd, Real.norm_of_nonneg (norm_nonneg _)] using
          hR (w, x) ⟨Metric.mem_closedBall.mpr
            (le_of_lt (Metric.mem_ball.mp hw)), Set.uIoc_subset_uIcc hx⟩)
      _root_.intervalIntegrable_const
      (by
        filter_upwards with x
        intro _hx w _hw
        have hlin : HasDerivAt
            (fun y : ℂ => (x : ℂ) * (I * y)) ((x : ℂ) * I) w := by
          simpa only [Function.id_def, mul_one, mul_assoc] using
            ((hasDerivAt_id w).const_mul I).const_mul (x : ℂ)
        dsimp only [F, F', suzukiOscillatoryKernel]
        simpa only [mul_assoc, mul_comm, mul_left_comm] using
          hlin.cexp.const_mul (u x : ℂ))
  change HasDerivAt
    (fun w => ∫ x in -a..a,
      (u x : ℂ) * suzukiOscillatoryKernel w x)
    (∫ x in -a..a,
      (u x : ℂ) * ((x : ℂ) * I) * suzukiOscillatoryKernel z x) z
  exact hresult.2

@[simp] theorem suzukiOscillatoryKernel_at_I (x : ℝ) :
    suzukiOscillatoryKernel I x = (Real.exp (-x) : ℂ) := by
  simp [suzukiOscillatoryKernel]

@[simp] theorem suzukiOscillatoryKernel_at_neg_I (x : ℝ) :
    suzukiOscillatoryKernel (-I) x = (Real.exp x : ℂ) := by
  simp [suzukiOscillatoryKernel]

/-! ## Endpoint values -/

theorem suzukiProjectedIntervalFourier_at_I_eq_parity
    (u : ℝ → ℝ) (a : ℝ) (hu : Continuous u) :
    suzukiProjectedIntervalFourier (fun x => (u x : ℂ)) a I =
      ((suzukiCompactEvenEnergy u a - suzukiCompactOddEnergy u a : ℝ) : ℂ) := by
  have hcosh : IntervalIntegrable (fun x => u x * Real.cosh x) volume (-a) a := by
    exact (hu.mul Real.continuous_cosh).intervalIntegrable _ _
  have hsinh : IntervalIntegrable (fun x => u x * Real.sinh x) volume (-a) a := by
    exact (hu.mul Real.continuous_sinh).intervalIntegrable _ _
  have hreal :
      (∫ x in -a..a, u x * Real.exp (-x)) =
        ∫ x in -a..a, (u x * Real.cosh x - u x * Real.sinh x) := by
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp
    rw [← Real.cosh_sub_sinh]
    ring
  calc
    suzukiProjectedIntervalFourier (fun x => (u x : ℂ)) a I =
        ∫ x in -a..a, ((u x * Real.exp (-x) : ℝ) : ℂ) := by
          apply intervalIntegral.integral_congr
          intro x _hx
          simp
    _ = ((∫ x in -a..a, u x * Real.exp (-x) : ℝ) : ℂ) :=
      intervalIntegral.integral_ofReal
    _ = ((∫ x in -a..a,
          (u x * Real.cosh x - u x * Real.sinh x) : ℝ) : ℂ) :=
      congrArg Complex.ofReal hreal
    _ = ((suzukiCompactEvenEnergy u a -
          suzukiCompactOddEnergy u a : ℝ) : ℂ) := by
      rw [intervalIntegral.integral_sub hcosh hsinh]
      rfl

theorem suzukiProjectedIntervalFourier_at_neg_I_eq_parity
    (u : ℝ → ℝ) (a : ℝ) (hu : Continuous u) :
    suzukiProjectedIntervalFourier (fun x => (u x : ℂ)) a (-I) =
      ((suzukiCompactEvenEnergy u a + suzukiCompactOddEnergy u a : ℝ) : ℂ) := by
  have hcosh : IntervalIntegrable (fun x => u x * Real.cosh x) volume (-a) a := by
    exact (hu.mul Real.continuous_cosh).intervalIntegrable _ _
  have hsinh : IntervalIntegrable (fun x => u x * Real.sinh x) volume (-a) a := by
    exact (hu.mul Real.continuous_sinh).intervalIntegrable _ _
  have hreal :
      (∫ x in -a..a, u x * Real.exp x) =
        ∫ x in -a..a, (u x * Real.cosh x + u x * Real.sinh x) := by
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp
    rw [← Real.cosh_add_sinh]
    ring
  calc
    suzukiProjectedIntervalFourier (fun x => (u x : ℂ)) a (-I) =
        ∫ x in -a..a, ((u x * Real.exp x : ℝ) : ℂ) := by
          apply intervalIntegral.integral_congr
          intro x _hx
          simp
    _ = ((∫ x in -a..a, u x * Real.exp x : ℝ) : ℂ) :=
      intervalIntegral.integral_ofReal
    _ = ((∫ x in -a..a,
          (u x * Real.cosh x + u x * Real.sinh x) : ℝ) : ℂ) :=
      congrArg Complex.ofReal hreal
    _ = ((suzukiCompactEvenEnergy u a +
          suzukiCompactOddEnergy u a : ℝ) : ℂ) := by
      rw [intervalIntegral.integral_add hcosh hsinh]
      rfl

/-! ## Endpoint spectral derivatives -/

theorem deriv_suzukiProjectedIntervalFourier_at_I_eq_parity
    (u : ℝ → ℝ) (a : ℝ) (hu : Continuous u) :
    deriv (suzukiProjectedIntervalFourier (fun x => (u x : ℂ)) a) I =
      I * ((suzukiCompactOddTilt u a - suzukiCompactEvenTilt u a : ℝ) : ℂ) := by
  have hbeta : IntervalIntegrable
      (fun x => x * u x * Real.cosh x) volume (-a) a := by
    exact ((continuous_id.mul hu).mul Real.continuous_cosh).intervalIntegrable _ _
  have halpha : IntervalIntegrable
      (fun x => x * u x * Real.sinh x) volume (-a) a := by
    exact ((continuous_id.mul hu).mul Real.continuous_sinh).intervalIntegrable _ _
  have hreal :
      (∫ x in -a..a, x * u x * Real.exp (-x)) =
        ∫ x in -a..a,
          (x * u x * Real.cosh x - x * u x * Real.sinh x) := by
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp
    rw [← Real.cosh_sub_sinh]
    ring
  rw [(hasDerivAt_suzukiProjectedIntervalFourier_ofReal u a I hu).deriv]
  calc
    (∫ x in -a..a,
        (u x : ℂ) * ((x : ℂ) * I) * suzukiOscillatoryKernel I x) =
        ∫ x in -a..a, I * (((x * u x * Real.exp (-x) : ℝ) : ℂ)) := by
          apply intervalIntegral.integral_congr
          intro x _hx
          simp only [suzukiOscillatoryKernel_at_I]
          push_cast
          ring
    _ = I * (∫ x in -a..a, (((x * u x * Real.exp (-x) : ℝ) : ℂ))) := by
      rw [intervalIntegral.integral_const_mul]
    _ = I * ((∫ x in -a..a, x * u x * Real.exp (-x) : ℝ) : ℂ) := by
      rw [intervalIntegral.integral_ofReal]
    _ = I * ((∫ x in -a..a,
          (x * u x * Real.cosh x - x * u x * Real.sinh x) : ℝ) : ℂ) := by
      rw [hreal]
    _ = I * ((suzukiCompactOddTilt u a -
          suzukiCompactEvenTilt u a : ℝ) : ℂ) := by
      rw [intervalIntegral.integral_sub hbeta halpha]
      rfl

theorem deriv_suzukiProjectedIntervalFourier_at_neg_I_eq_parity
    (u : ℝ → ℝ) (a : ℝ) (hu : Continuous u) :
    deriv (suzukiProjectedIntervalFourier (fun x => (u x : ℂ)) a) (-I) =
      I * ((suzukiCompactEvenTilt u a + suzukiCompactOddTilt u a : ℝ) : ℂ) := by
  have hbeta : IntervalIntegrable
      (fun x => x * u x * Real.cosh x) volume (-a) a := by
    exact ((continuous_id.mul hu).mul Real.continuous_cosh).intervalIntegrable _ _
  have halpha : IntervalIntegrable
      (fun x => x * u x * Real.sinh x) volume (-a) a := by
    exact ((continuous_id.mul hu).mul Real.continuous_sinh).intervalIntegrable _ _
  have hreal :
      (∫ x in -a..a, x * u x * Real.exp x) =
        ∫ x in -a..a,
          (x * u x * Real.sinh x + x * u x * Real.cosh x) := by
    apply intervalIntegral.integral_congr
    intro x _hx
    dsimp
    rw [← Real.sinh_add_cosh]
    ring
  rw [(hasDerivAt_suzukiProjectedIntervalFourier_ofReal u a (-I) hu).deriv]
  calc
    (∫ x in -a..a,
        (u x : ℂ) * ((x : ℂ) * I) * suzukiOscillatoryKernel (-I) x) =
        ∫ x in -a..a, I * (((x * u x * Real.exp x : ℝ) : ℂ)) := by
          apply intervalIntegral.integral_congr
          intro x _hx
          simp only [suzukiOscillatoryKernel_at_neg_I]
          push_cast
          ring
    _ = I * (∫ x in -a..a, (((x * u x * Real.exp x : ℝ) : ℂ))) := by
      rw [intervalIntegral.integral_const_mul]
    _ = I * ((∫ x in -a..a, x * u x * Real.exp x : ℝ) : ℂ) := by
      rw [intervalIntegral.integral_ofReal]
    _ = I * ((∫ x in -a..a,
          (x * u x * Real.sinh x + x * u x * Real.cosh x) : ℝ) : ℂ) := by
      rw [hreal]
    _ = I * ((suzukiCompactEvenTilt u a +
          suzukiCompactOddTilt u a : ℝ) : ℂ) := by
      rw [intervalIntegral.integral_add halpha hbeta]
      rfl

/-! ## Source-side second defect -/

/-- The endpoint second defect of an actual real compact Suzuki response is exactly the parity
curvature of its four source integrals.  No endpoint identities remain as hypotheses. -/
theorem suzukiProjectedIntervalFourier_secondDefect_eq_parityCurvature
    (u : ℝ → ℝ) (a : ℝ) (hu : Continuous u)
    (hsum : suzukiCompactEvenEnergy u a + suzukiCompactOddEnergy u a ≠ 0) :
    4 * I *
        (deriv (suzukiProjectedIntervalFourier (fun x => (u x : ℂ)) a) I *
            suzukiProjectedIntervalFourier (fun x => (u x : ℂ)) a (-I) +
          suzukiProjectedIntervalFourier (fun x => (u x : ℂ)) a I *
            deriv (suzukiProjectedIntervalFourier (fun x => (u x : ℂ)) a) (-I)) /
          suzukiProjectedIntervalFourier (fun x => (u x : ℂ)) a (-I) ^ (2 : ℕ) =
      (suzukiSecondDefectParityCurvature
        (suzukiCompactEvenEnergy u a) (suzukiCompactOddEnergy u a)
        (suzukiCompactEvenTilt u a) (suzukiCompactOddTilt u a) : ℂ) := by
  exact suzukiFourier_endpointSecondDefect_eq_parityCurvature hsum
    (suzukiProjectedIntervalFourier_at_I_eq_parity u a hu)
    (suzukiProjectedIntervalFourier_at_neg_I_eq_parity u a hu)
    (deriv_suzukiProjectedIntervalFourier_at_I_eq_parity u a hu)
    (deriv_suzukiProjectedIntervalFourier_at_neg_I_eq_parity u a hu)

/-! ## Xi-identifying compact source families -/

/-- Locally uniform Xi identification forces the parity curvature of the actual compact real
responses—not an abstract endpoint surrogate—to converge to the negative prime--Gamma
calibration. -/
theorem suzukiCompactParityCurvature_tendsto_primeArch
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (u : ι → ℝ → ℝ) (a : ι → ℝ)
    (hu : ∀ j, Continuous (u j))
    (hconv : TendstoLocallyUniformlyOn
      (fun j w =>
        GaloisForLFunctions.RHTower.suzukiLivsicQuotient
          (GaloisForLFunctions.RHTower.suzukiFourierNumerator
            (suzukiProjectedIntervalFourier
              (fun x => (u j x : ℂ)) (a j)))
          (GaloisForLFunctions.RHTower.suzukiFourierDenominator
            (suzukiProjectedIntervalFourier
              (fun x => (u j x : ℂ)) (a j)))
          (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w))
      (xiHedenmalmLivsicTarget ∘
        GaloisForLFunctions.RHTower.suzukiUpperCayleyInv)
      l (Metric.ball 0 1))
    (hcont : ∀ᶠ j in l, ContDiffOn ℂ 2
      (fun w =>
        GaloisForLFunctions.RHTower.suzukiLivsicQuotient
          (GaloisForLFunctions.RHTower.suzukiFourierNumerator
            (suzukiProjectedIntervalFourier
              (fun x => (u j x : ℂ)) (a j)))
          (GaloisForLFunctions.RHTower.suzukiFourierDenominator
            (suzukiProjectedIntervalFourier
              (fun x => (u j x : ℂ)) (a j)))
          (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w))
      (Metric.ball 0 1))
    (hsource : ∀ᶠ j in l,
      ContDiffAt ℂ 2
          (suzukiProjectedIntervalFourier
            (fun x => (u j x : ℂ)) (a j)) I ∧
        ContDiffAt ℂ 2
          (suzukiProjectedIntervalFourier
            (fun x => (u j x : ℂ)) (a j)) (-I) ∧
        suzukiProjectedIntervalFourier
            (fun x => (u j x : ℂ)) (a j) (-I) ≠ 0) :
    Tendsto
      (fun j => suzukiSecondDefectParityCurvature
        (suzukiCompactEvenEnergy (u j) (a j))
        (suzukiCompactOddEnergy (u j) (a j))
        (suzukiCompactEvenTilt (u j) (a j))
        (suzukiCompactOddTilt (u j) (a j))) l
      (nhds primeArchSuzukiSecondDefectCalibration) := by
  let F : ι → ℂ → ℂ := fun j =>
    suzukiProjectedIntervalFourier (fun x => (u j x : ℂ)) (a j)
  have hendpoint :=
    suzukiFourier_endpointSecondDefect_tendsto_primeArch F hconv hcont hsource
  apply tendsto_suzukiSecondDefectParityCurvature_of_endpoint
    F
    (fun j => suzukiCompactEvenEnergy (u j) (a j))
    (fun j => suzukiCompactOddEnergy (u j) (a j))
    (fun j => suzukiCompactEvenTilt (u j) (a j))
    (fun j => suzukiCompactOddTilt (u j) (a j))
    hendpoint
  filter_upwards [hsource] with j hj
  have hFi := suzukiProjectedIntervalFourier_at_I_eq_parity
    (u j) (a j) (hu j)
  have hFni := suzukiProjectedIntervalFourier_at_neg_I_eq_parity
    (u j) (a j) (hu j)
  have hsum :
      suzukiCompactEvenEnergy (u j) (a j) +
          suzukiCompactOddEnergy (u j) (a j) ≠ 0 := by
    intro hzero
    apply hj.2.2
    rw [hFni, hzero]
    norm_num
  exact ⟨hsum, hFi, hFni,
    deriv_suzukiProjectedIntervalFourier_at_I_eq_parity
      (u j) (a j) (hu j),
    deriv_suzukiProjectedIntervalFourier_at_neg_I_eq_parity
      (u j) (a j) (hu j)⟩

/-- **Strict source consequence.**  If the compact even and odd energies are positive, every
Xi-identifying Suzuki family eventually has larger relative exponential-tilt growth in the odd
channel:

`alpha/E < beta/O`.

This is a genuine source selection law.  It is not implied by the first defect angle alone. -/
theorem eventually_suzukiCompact_evenRelativeTilt_lt_oddRelativeTilt
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (u : ι → ℝ → ℝ) (a : ι → ℝ)
    (hcurvature : Tendsto
      (fun j => suzukiSecondDefectParityCurvature
        (suzukiCompactEvenEnergy (u j) (a j))
        (suzukiCompactOddEnergy (u j) (a j))
        (suzukiCompactEvenTilt (u j) (a j))
        (suzukiCompactOddTilt (u j) (a j))) l
      (nhds primeArchSuzukiSecondDefectCalibration))
    (hpositive : ∀ᶠ j in l,
      0 < suzukiCompactEvenEnergy (u j) (a j) ∧
      0 < suzukiCompactOddEnergy (u j) (a j)) :
    ∀ᶠ j in l,
      suzukiCompactEvenTilt (u j) (a j) /
          suzukiCompactEvenEnergy (u j) (a j) <
        suzukiCompactOddTilt (u j) (a j) /
          suzukiCompactOddEnergy (u j) (a j) := by
  have hnegative : ∀ᶠ j in l,
      suzukiSecondDefectParityCurvature
        (suzukiCompactEvenEnergy (u j) (a j))
        (suzukiCompactOddEnergy (u j) (a j))
        (suzukiCompactEvenTilt (u j) (a j))
        (suzukiCompactOddTilt (u j) (a j)) < 0 :=
    (tendsto_order.1 hcurvature).2 0
      primeArchSuzukiSecondDefectCalibration_neg
  filter_upwards [hnegative, hpositive] with j hneg hpos
  exact (suzukiSecondDefectParityCurvature_neg_iff hpos.1 hpos.2).mp hneg

end

end RHTower
