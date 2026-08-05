import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian spectral-packet action law

For an arbitrary finite spectral packet observed through one standard
Gaussian clock, every packet character is multiplied exactly by the Gaussian
kernel at its dimensionless action `time * detuning`.  As time tends to
infinity, precisely the zero-detuning sector survives.

The theorem is independent of any Hamiltonian realization.  A finite-replica
Hamiltonian reporter becomes an instance after spectral expansion: its
detunings are sums of forward energy labels minus backward energy labels.
-/

open Filter MeasureTheory Topology
open scoped BigOperators ENNReal NNReal
open ProbabilityTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Universal multiplier of a spectral character under a standard Gaussian
clock. -/
def gaussianObserverActionKernel (action : ℝ) : ℂ :=
  Complex.exp (-((action : ℂ) ^ 2) / 2)

/-- The action kernel is exactly the characteristic function of the standard
real Gaussian. -/
theorem gaussianObserverActionKernel_eq_charFun (action : ℝ) :
    gaussianObserverActionKernel action =
      charFun (gaussianReal 0 1) action := by
  rw [charFun_gaussianReal]
  unfold gaussianObserverActionKernel
  congr 1
  push_cast
  ring

/-- Exact Gaussian integral of one observer--spectral character. -/
theorem integral_gaussian_observer_character (action : ℝ) :
    (∫ x : ℝ,
        Complex.exp (((action * x : ℝ) : ℂ) * Complex.I)
        ∂gaussianReal 0 1) =
      gaussianObserverActionKernel action := by
  rw [show (∫ x : ℝ,
      Complex.exp (((action * x : ℝ) : ℂ) * Complex.I)
        ∂gaussianReal 0 1) =
      charFun (gaussianReal 0 1) action by
    rw [charFun_apply_real]
    apply integral_congr_ae
    filter_upwards with x
    congr 1
    push_cast
    ring]
  exact (gaussianObserverActionKernel_eq_charFun action).symm

/-- Zero action is perfectly locked. -/
theorem gaussianObserverActionKernel_zero :
    gaussianObserverActionKernel 0 = 1 := by
  simp [gaussianObserverActionKernel]

/-- Every fixed nonzero detuning is dephased by an unbounded Gaussian
observation clock. -/
theorem tendsto_gaussianObserverActionKernel_atTop_zero
    {detuning : ℝ} (hdetuning : detuning ≠ 0) :
    Tendsto
      (fun time : ℝ =>
        gaussianObserverActionKernel (time * detuning))
      atTop (𝓝 0) := by
  have hcoefficient : 0 < detuning ^ 2 / 2 :=
    div_pos (sq_pos_of_ne_zero hdetuning) two_pos
  have hsquare :
      Tendsto (fun time : ℝ => time ^ (2 : ℕ)) atTop atTop :=
    Filter.tendsto_pow_atTop two_ne_zero
  have hactionSquare :
      Tendsto
        (fun time : ℝ => (time * detuning) ^ 2 / 2)
        atTop atTop := by
    apply (hsquare.const_mul_atTop hcoefficient).congr'
    filter_upwards [] with time
    ring
  have hreal :
      Tendsto
        (fun time : ℝ =>
          Real.exp (-((time * detuning) ^ 2 / 2)))
        atTop (𝓝 0) := by
    apply
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        hactionSquare).congr'
    filter_upwards [] with time
    rfl
  have hcomplex :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  apply hcomplex.congr'
  filter_upwards [] with time
  unfold gaussianObserverActionKernel
  simp only [Function.comp_apply, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

variable {ι : Type*}

/-- Finite spectral packet sampled at time `time` by a scalar Gaussian
clock `x`. -/
def gaussianSpectralPacket
    (support : Finset ι) (coefficient : ι → ℂ)
    (detuning : ι → ℝ) (time x : ℝ) : ℂ :=
  ∑ i ∈ support, coefficient i *
    Complex.exp
      (((time * detuning i * x : ℝ) : ℂ) * Complex.I)

/-- **Exact Gaussian observer--spectral action law.**  Gaussian averaging of
an arbitrary finite packet evaluates the universal action kernel at every
dimensionless action `time * detuning`. -/
theorem integral_gaussianSpectralPacket
    (support : Finset ι) (coefficient : ι → ℂ)
    (detuning : ι → ℝ) (time : ℝ) :
    (∫ x : ℝ,
        gaussianSpectralPacket support coefficient detuning time x
        ∂gaussianReal 0 1) =
      ∑ i ∈ support, coefficient i *
        gaussianObserverActionKernel (time * detuning i) := by
  classical
  have hintegrable (action : ℝ) :
      Integrable
        (fun x : ℝ =>
          Complex.exp (((action * x : ℝ) : ℂ) * Complex.I))
        (gaussianReal 0 1) := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) ?_
    filter_upwards with x
    rw [Complex.norm_exp]
    simp
  unfold gaussianSpectralPacket
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_const_mul]
    rw [show
      (fun x : ℝ =>
        Complex.exp
          (↑(time * detuning i * x) * Complex.I)) =
      fun x : ℝ =>
        Complex.exp
          (↑((time * detuning i) * x) * Complex.I) by
      funext x
      congr 2]
    rw [integral_gaussian_observer_character]
  · intro i hi
    exact
      (hintegrable (time * detuning i)).const_mul
        (coefficient i)

/-- Sum of exactly those packet coefficients whose spectral action is zero. -/
def zeroActionSpectralPacket
    (support : Finset ι) (coefficient : ι → ℂ)
    (detuning : ι → ℝ) : ℂ :=
  ∑ i ∈ support.filter (fun i => detuning i = 0), coefficient i

/-- **Zero-action completion law.**  At unbounded Gaussian observation time,
an arbitrary finite spectral packet converges exactly to its zero-action
sector. -/
theorem tendsto_integral_gaussianSpectralPacket_atTop
    (support : Finset ι) (coefficient : ι → ℂ)
    (detuning : ι → ℝ) :
    Tendsto
      (fun time : ℝ =>
        ∫ x : ℝ,
          gaussianSpectralPacket support coefficient detuning time x
          ∂gaussianReal 0 1)
      atTop
      (𝓝 (zeroActionSpectralPacket support coefficient detuning)) := by
  classical
  have hcharacter (i : ι) :
      Tendsto
        (fun time : ℝ =>
          coefficient i *
            gaussianObserverActionKernel (time * detuning i))
        atTop
        (𝓝 (if detuning i = 0 then coefficient i else 0)) := by
    by_cases hzero : detuning i = 0
    · simp [hzero, gaussianObserverActionKernel_zero]
    · simpa [hzero] using
        (tendsto_gaussianObserverActionKernel_atTop_zero hzero).const_mul
          (coefficient i)
  have hsum :=
    tendsto_finsetSum support (fun i _ => hcharacter i)
  rw [show
    zeroActionSpectralPacket support coefficient detuning =
      ∑ i ∈ support,
        if detuning i = 0 then coefficient i else 0 by
    unfold zeroActionSpectralPacket
    rw [Finset.sum_filter]]
  apply hsum.congr'
  filter_upwards [] with time
  rw [integral_gaussianSpectralPacket]

end

end GaloisForLFunctions.HTGeometry
