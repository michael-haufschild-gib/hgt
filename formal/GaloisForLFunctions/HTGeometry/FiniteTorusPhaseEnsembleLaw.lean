import Mathlib

/-!
# Exact finite-torus phase ensemble

Uniformly sample a centered observation time and map it into the phase
torus of an arbitrary finite real frequency vector. Every Fourier
coefficient of the resulting probability law is exactly a sinc of the
corresponding integer spectral detuning.
-/

open Filter MeasureTheory Set Topology
open scoped BigOperators Interval

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Normalized Lebesgue probability measure on the unit interval. -/
def unitIntervalProbabilityMeasure : ProbabilityMeasure ℝ :=
  ⟨volume.restrict (Ioc 0 1), by
    constructor
    rw [Measure.restrict_apply_univ, Real.volume_Ioc]
    norm_num⟩

/-- Centered uniform-time phase point on a finite unit torus. The
`2π` normalization matches Mathlib's additive-circle Fourier convention. -/
def finiteTorusPhasePoint
    {d : Type*} [Fintype d]
    (omega : d → ℝ) (A u : ℝ) : UnitAddTorus d :=
  fun i =>
    ((A * (2 * u - 1) * omega i / (2 * Real.pi) : ℝ) :
      UnitAddCircle)

/-- The finite-torus phase point depends continuously on sampled time. -/
theorem finiteTorusPhasePoint_continuous
    {d : Type*} [Fintype d]
    (omega : d → ℝ) (A : ℝ) :
    Continuous (finiteTorusPhasePoint omega A) := by
  unfold finiteTorusPhasePoint
  apply continuous_pi
  intro i
  exact (AddCircle.continuous_mk' (1 : ℝ)).comp (by fun_prop)

/-- Pushforward law of uniformly sampled centered observation time. -/
def finiteTorusPhaseProbabilityMeasure
    {d : Type*} [Fintype d]
    (omega : d → ℝ) (A : ℝ) :
    ProbabilityMeasure (UnitAddTorus d) :=
  ProbabilityMeasure.map unitIntervalProbabilityMeasure
    (f := finiteTorusPhasePoint omega A)
    (finiteTorusPhasePoint_continuous omega A).aemeasurable

/-- Real detuning selected by an integer torus character. -/
def finiteTorusCharacterDetuning
    {d : Type*} [Fintype d]
    (n : d → ℤ) (omega : d → ℝ) : ℝ :=
  ∑ i, (n i : ℝ) * omega i

/-- Evaluation of a torus Fourier monomial on a sampled phase point. -/
theorem mFourier_finiteTorusPhasePoint
    {d : Type*} [Fintype d]
    (n : d → ℤ) (omega : d → ℝ) (A u : ℝ) :
    UnitAddTorus.mFourier n (finiteTorusPhasePoint omega A u) =
      Complex.exp
        (((A * (2 * u - 1) *
          finiteTorusCharacterDetuning n omega : ℝ) : ℂ) *
            Complex.I) := by
  rw [UnitAddTorus.mFourier]
  simp only [ContinuousMap.coe_mk, finiteTorusPhasePoint,
    fourier_coe_apply]
  rw [← Complex.exp_sum]
  congr 1
  simp only [finiteTorusCharacterDetuning]
  push_cast
  field_simp [Real.pi_ne_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Centering the unit interval converts its exponential average into the
standard sinc kernel. -/
theorem interval_exp_centered_eq_sinc (A : ℝ) :
    ∫ u in (0 : ℝ)..1,
        Complex.exp (((A * (2 * u - 1) : ℝ) : ℂ) * Complex.I) =
      Real.sinc A := by
  by_cases hA : A = 0
  · subst A
    simp
  have hfun :
      (fun u : ℝ =>
        Complex.exp
          (((A * (2 * u - 1) : ℝ) : ℂ) * Complex.I)) =
      fun u : ℝ =>
        Complex.exp
          ((((2 * A) * u + (-A) : ℝ) : ℂ) * Complex.I) := by
    funext u
    congr 2
    push_cast
    ring
  rw [hfun]
  rw [intervalIntegral.integral_comp_mul_add
    (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
    (mul_ne_zero (by norm_num) hA) (-A)]
  rw [show 2 * A * 0 + -A = -A by ring,
    show 2 * A * 1 + -A = A by ring]
  rw [integral_exp_mul_I_eq_sinc]
  simp only [Complex.real_smul]
  push_cast
  field_simp [hA]

/-- **Exact phase-ensemble character law.** Every Fourier coefficient of
the actual uniformly sampled phase probability measure is the sinc of its
integer spectral detuning. -/
theorem finiteTorusPhaseProbabilityMeasure_mFourier_integral
    {d : Type*} [Fintype d]
    (n : d → ℤ) (omega : d → ℝ) (A : ℝ) :
    (∫ x, UnitAddTorus.mFourier n x
        ∂(finiteTorusPhaseProbabilityMeasure omega A :
          Measure (UnitAddTorus d))) =
      Real.sinc (A * finiteTorusCharacterDetuning n omega) := by
  rw [finiteTorusPhaseProbabilityMeasure,
    ProbabilityMeasure.toMeasure_map]
  rw [integral_map
    (finiteTorusPhasePoint_continuous omega A).aemeasurable
    (by fun_prop)]
  simp_rw [mFourier_finiteTorusPhasePoint]
  rw [show
    (unitIntervalProbabilityMeasure : Measure ℝ) =
      volume.restrict (Ioc 0 1) by rfl]
  rw [← intervalIntegral.integral_of_le
    (by norm_num : (0 : ℝ) ≤ 1)]
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    interval_exp_centered_eq_sinc
      (A * finiteTorusCharacterDetuning n omega)

end

end GaloisForLFunctions.HTGeometry
