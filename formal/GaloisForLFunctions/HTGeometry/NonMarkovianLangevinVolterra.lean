import GaloisForLFunctions.HTGeometry.NonMarkovianLangevinKernel
import GaloisForLFunctions.HTGeometry.VolterraLinearIntegralEquation
import Mathlib.Tactic

open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Closed antiderivative law for a nonzero real Fourier mode. -/
theorem hasDerivAt_realFourierCharacterUnitPrimitive
    (frequency : ℝˣ) (t : ℝ) :
    HasDerivAt
      (fun s : ℝ =>
        (realFourierCharacter (frequency : ℝ) s - 1) /
          (Complex.I * (((frequency : ℝ) : ℝ) : ℂ)))
      (realFourierCharacter (frequency : ℝ) t) t := by
  have hlinear : HasDerivAt
      (fun s : ℝ => (((frequency : ℝ) * s : ℝ) : ℂ))
      (((frequency : ℝ) : ℝ) : ℂ) t := by
    simpa only [id_eq, mul_one] using
      (((hasDerivAt_id t).const_mul (frequency : ℝ)).ofReal_comp)
  have hexp := (hlinear.const_mul Complex.I).cexp
  have hquotient := (hexp.sub_const 1).div_const
    (Complex.I * (((frequency : ℝ) : ℝ) : ℂ))
  have hden : Complex.I * (((frequency : ℝ) : ℝ) : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (Units.ne_zero frequency))
  simpa only [realFourierCharacter, mul_div_cancel_right₀ _ hden] using hquotient

theorem intervalIntegral_realFourierCharacterUnit
    (frequency : ℝˣ) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, realFourierCharacter (frequency : ℝ) s) =
      (realFourierCharacter (frequency : ℝ) t - 1) /
        (Complex.I * (((frequency : ℝ) : ℝ) : ℂ)) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hasDerivAt_realFourierCharacterUnitPrimitive frequency s)
    ((by
      unfold realFourierCharacter
      fun_prop : Continuous fun s : ℝ => realFourierCharacter (frequency : ℝ) s).intervalIntegrable
      0 t)
  simpa [realFourierCharacter] using h

/-- Finite bath kernel with every detuning nonzero by construction. -/
def finiteNonresonantBathMemoryKernel {ι : Type*} [Fintype ι]
    (detuning : ι → ℝˣ) (coupling : ι → ℂ) (t : ℝ) : ℂ :=
  finitePositiveMemoryKernel (finiteBathMemoryWeight coupling)
    (fun i => (detuning i : ℝ)) t

theorem finiteNonresonantBathMemoryKernel_neg
    {ι : Type*} [Fintype ι]
    (detuning : ι → ℝˣ) (coupling : ι → ℂ) (t : ℝ) :
    finiteNonresonantBathMemoryKernel detuning coupling (-t) =
      star (finiteNonresonantBathMemoryKernel detuning coupling t) :=
  finitePositiveMemoryKernel_neg _ _ _

theorem norm_finiteNonresonantBathMemoryKernel_le_zero
    {ι : Type*} [Fintype ι]
    (detuning : ι → ℝˣ) (coupling : ι → ℂ) (t : ℝ) :
    ‖finiteNonresonantBathMemoryKernel detuning coupling t‖ ≤
      ∑ i, Complex.normSq (coupling i) := by
  change ‖finitePositiveMemoryKernel (finiteBathMemoryWeight coupling)
      (fun i => (detuning i : ℝ)) t‖ ≤
    ∑ i, (finiteBathMemoryWeight coupling i : ℝ)
  exact norm_finitePositiveMemoryKernel_le_zero
    (finiteBathMemoryWeight coupling) (fun i => (detuning i : ℝ)) t

theorem positiveDefiniteOnReal_finiteNonresonantBathMemoryKernel
    {ι : Type*} [Fintype ι]
    (detuning : ι → ℝˣ) (coupling : ι → ℂ) :
    PositiveDefiniteOnReal (finiteNonresonantBathMemoryKernel detuning coupling) :=
  positiveDefiniteOnReal_finitePositiveMemoryKernel _ _

/-- Time primitive of a finite bath kernel with nonzero detunings encoded as units. -/
def finiteNonresonantBathMemoryPrimitive {ι : Type*} [Fintype ι]
    (detuning : ι → ℝˣ) (coupling : ι → ℂ) (t : ℝ) : ℂ :=
  ∑ i, ((Complex.normSq (coupling i) : ℝ) : ℂ) *
    (realFourierCharacter (detuning i : ℝ) t - 1) /
      (Complex.I * (((detuning i : ℝ) : ℝ) : ℂ))

def finiteNonresonantBathMemoryBound {ι : Type*} [Fintype ι]
    (detuning : ι → ℝˣ) (coupling : ι → ℂ) : ℝ :=
  ∑ i, 2 * Complex.normSq (coupling i) / |(detuning i : ℝ)|

theorem intervalIntegral_finiteNonresonantBathMemoryKernel_eq_primitive
    {ι : Type*} [Fintype ι]
    (detuning : ι → ℝˣ) (coupling : ι → ℂ) (t : ℝ) :
    (∫ s in (0 : ℝ)..t, finiteNonresonantBathMemoryKernel detuning coupling s) =
      finiteNonresonantBathMemoryPrimitive detuning coupling t := by
  classical
  unfold finiteNonresonantBathMemoryKernel finitePositiveMemoryKernel
    finiteBathMemoryWeight finiteNonresonantBathMemoryPrimitive
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral_realFourierCharacterUnit]
    change (((Complex.normSq (coupling i) : ℝ) : ℂ) *
        ((realFourierCharacter (detuning i : ℝ) t - 1) /
          (Complex.I * (((detuning i : ℝ) : ℝ) : ℂ)))) =
      (((Complex.normSq (coupling i) : ℝ) : ℂ) *
        (realFourierCharacter (detuning i : ℝ) t - 1)) /
          (Complex.I * (((detuning i : ℝ) : ℝ) : ℂ))
    ring
  · intro i _
    exact ((by
      unfold realFourierCharacter
      fun_prop : Continuous fun s : ℝ =>
        (((Complex.normSq (coupling i) : ℝ) : ℂ) *
          realFourierCharacter (detuning i : ℝ) s)).intervalIntegrable 0 t)

theorem finiteNonresonantBathMemoryBound_nonneg {ι : Type*} [Fintype ι]
    (detuning : ι → ℝˣ) (coupling : ι → ℂ) :
    0 ≤ finiteNonresonantBathMemoryBound detuning coupling := by
  unfold finiteNonresonantBathMemoryBound
  exact Finset.sum_nonneg fun i _ =>
    div_nonneg (mul_nonneg (by norm_num) (Complex.normSq_nonneg _)) (abs_nonneg _)

theorem norm_finiteNonresonantBathMemoryPrimitive_le
    {ι : Type*} [Fintype ι]
    (detuning : ι → ℝˣ) (coupling : ι → ℂ) (t : ℝ) :
    ‖finiteNonresonantBathMemoryPrimitive detuning coupling t‖ ≤
      finiteNonresonantBathMemoryBound detuning coupling := by
  classical
  unfold finiteNonresonantBathMemoryPrimitive finiteNonresonantBathMemoryBound
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
  have hdet : (detuning i : ℝ) ≠ 0 := Units.ne_zero (detuning i)
  have hden : 0 < |(detuning i : ℝ)| := abs_pos.mpr hdet
  have hosc : ‖realFourierCharacter (detuning i : ℝ) t - 1‖ ≤ 2 := by
    calc
      ‖realFourierCharacter (detuning i : ℝ) t - 1‖
          ≤ ‖realFourierCharacter (detuning i : ℝ) t‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num
  rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Complex.normSq_nonneg _), norm_mul, Complex.norm_I,
    Complex.norm_real, Real.norm_eq_abs, one_mul]
  exact div_le_div_of_nonneg_right
    (by nlinarith [Complex.normSq_nonneg (coupling i)]) hden.le

theorem continuous_finiteNonresonantBathMemoryPrimitive
    {ι : Type*} [Fintype ι]
    (detuning : ι → ℝˣ) (coupling : ι → ℂ) :
    Continuous (finiteNonresonantBathMemoryPrimitive detuning coupling) := by
  classical
  unfold finiteNonresonantBathMemoryPrimitive realFourierCharacter
  fun_prop

/-- Initial-environment driving for the same nonresonant bath. -/
def finiteNonresonantBathInitialDrive {ι : Type*} [Fintype ι]
    (detuning : ι → ℝˣ) (coupling initialAmplitude : ι → ℂ) (t : ℝ) : ℂ :=
  -Complex.I * ∑ i, coupling i * initialAmplitude i *
    realFourierCharacter (detuning i : ℝ) t

@[simp]
theorem finiteNonresonantBathInitialDrive_vacuum
    {ι : Type*} [Fintype ι]
    (detuning : ι → ℝˣ) (coupling : ι → ℂ) (t : ℝ) :
    finiteNonresonantBathInitialDrive detuning coupling (fun _ => 0) t = 0 := by
  simp [finiteNonresonantBathInitialDrive]

theorem continuous_finiteNonresonantBathInitialDrive
    {ι : Type*} [Fintype ι]
    (detuning : ι → ℝˣ) (coupling initialAmplitude : ι → ℂ) :
    Continuous (finiteNonresonantBathInitialDrive detuning coupling initialAmplitude) := by
  classical
  unfold finiteNonresonantBathInitialDrive realFourierCharacter
  fun_prop

/-- Mild source: initial system amplitude plus integrated initial-environment drive. -/
def finiteNonresonantBathMildSource {ι : Type*} [Fintype ι]
    (initialSystem : ℂ) (detuning : ι → ℝˣ)
    (coupling initialAmplitude : ι → ℂ) (t : ℝ) : ℂ :=
  initialSystem + ∑ i, (-Complex.I * coupling i * initialAmplitude i) *
    ((realFourierCharacter (detuning i : ℝ) t - 1) /
      (Complex.I * (((detuning i : ℝ) : ℝ) : ℂ)))

def finiteNonresonantBathSourceBound {ι : Type*} [Fintype ι]
    (initialSystem : ℂ) (detuning : ι → ℝˣ)
    (coupling initialAmplitude : ι → ℂ) : ℝ :=
  ‖initialSystem‖ +
    ∑ i, 2 * ‖coupling i * initialAmplitude i‖ / |(detuning i : ℝ)|

theorem finiteNonresonantBathMildSource_eq_initial_add_integral_drive
    {ι : Type*} [Fintype ι]
    (initialSystem : ℂ) (detuning : ι → ℝˣ)
    (coupling initialAmplitude : ι → ℂ) (t : ℝ) :
    finiteNonresonantBathMildSource initialSystem detuning coupling initialAmplitude t =
      initialSystem + ∫ s in (0 : ℝ)..t,
        finiteNonresonantBathInitialDrive detuning coupling initialAmplitude s := by
  classical
  unfold finiteNonresonantBathMildSource finiteNonresonantBathInitialDrive
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul,
      intervalIntegral_realFourierCharacterUnit]
    rw [Finset.mul_sum]
    apply congrArg (initialSystem + ·)
    apply Finset.sum_congr rfl
    intro i _
    ring
  · intro i _
    exact ((by
      unfold realFourierCharacter
      fun_prop : Continuous fun s : ℝ =>
        coupling i * initialAmplitude i *
          realFourierCharacter (detuning i : ℝ) s).intervalIntegrable 0 t)

theorem finiteNonresonantBathSourceBound_nonneg {ι : Type*} [Fintype ι]
    (initialSystem : ℂ) (detuning : ι → ℝˣ)
    (coupling initialAmplitude : ι → ℂ) :
    0 ≤ finiteNonresonantBathSourceBound initialSystem detuning coupling initialAmplitude := by
  unfold finiteNonresonantBathSourceBound
  positivity

theorem norm_finiteNonresonantBathMildSource_le
    {ι : Type*} [Fintype ι]
    (initialSystem : ℂ) (detuning : ι → ℝˣ)
    (coupling initialAmplitude : ι → ℂ) (t : ℝ) :
    ‖finiteNonresonantBathMildSource initialSystem detuning coupling initialAmplitude t‖ ≤
      finiteNonresonantBathSourceBound initialSystem detuning coupling initialAmplitude := by
  classical
  unfold finiteNonresonantBathMildSource finiteNonresonantBathSourceBound
  refine (norm_add_le _ _).trans ?_
  refine add_le_add (le_refl _) ?_
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
  have hdet : (detuning i : ℝ) ≠ 0 := Units.ne_zero (detuning i)
  have hden : 0 < |(detuning i : ℝ)| := abs_pos.mpr hdet
  have hosc : ‖realFourierCharacter (detuning i : ℝ) t - 1‖ ≤ 2 := by
    calc
      ‖realFourierCharacter (detuning i : ℝ) t - 1‖
          ≤ ‖realFourierCharacter (detuning i : ℝ) t‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by norm_num
  simp only [norm_mul, norm_neg, Complex.norm_I, one_mul, norm_div,
    Complex.norm_real, Real.norm_eq_abs]
  calc
    ‖coupling i‖ * ‖initialAmplitude i‖ *
        (‖realFourierCharacter (detuning i : ℝ) t - 1‖ / |(detuning i : ℝ)|)
        ≤ ‖coupling i‖ * ‖initialAmplitude i‖ * (2 / |(detuning i : ℝ)|) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hosc hden.le)
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = 2 * (‖coupling i‖ * ‖initialAmplitude i‖) / |(detuning i : ℝ)| := by ring

theorem continuous_finiteNonresonantBathMildSource
    {ι : Type*} [Fintype ι]
    (initialSystem : ℂ) (detuning : ι → ℝˣ)
    (coupling initialAmplitude : ι → ℂ) :
    Continuous
      (finiteNonresonantBathMildSource initialSystem detuning coupling initialAmplitude) := by
  classical
  unfold finiteNonresonantBathMildSource realFourierCharacter
  fun_prop

/-- Volterra operator in the mild form of the finite-bath Langevin equation. -/
def finiteNonresonantBathVolterraKernel {ι : Type*} [Fintype ι]
    (detuning : ι → ℝˣ) (coupling : ι → ℂ) (t s : ℝ) : ℂ →L[ℝ] ℂ :=
  ((ContinuousLinearMap.mul ℂ ℂ)
    (-finiteNonresonantBathMemoryPrimitive detuning coupling (t - s))).restrictScalars ℝ

theorem continuous_finiteNonresonantBathVolterraKernel
    {ι : Type*} [Fintype ι]
    (detuning : ι → ℝˣ) (coupling : ι → ℂ) :
    Continuous fun p : ℝ × ℝ =>
      finiteNonresonantBathVolterraKernel detuning coupling p.1 p.2 := by
  unfold finiteNonresonantBathVolterraKernel
  have hcoefficient : Continuous fun p : ℝ × ℝ =>
      -finiteNonresonantBathMemoryPrimitive detuning coupling (p.1 - p.2) :=
    (continuous_finiteNonresonantBathMemoryPrimitive detuning coupling).comp
      (continuous_fst.sub continuous_snd) |>.neg
  exact (ContinuousLinearMap.restrictScalarsIsometry ℂ ℂ ℂ ℝ ℝ).continuous.comp
    ((ContinuousLinearMap.mul ℂ ℂ).continuous.comp hcoefficient)

theorem norm_finiteNonresonantBathVolterraKernel_le
    {ι : Type*} [Fintype ι]
    (detuning : ι → ℝˣ) (coupling : ι → ℂ) (t s : ℝ) :
    ‖finiteNonresonantBathVolterraKernel detuning coupling t s‖ ≤
      finiteNonresonantBathMemoryBound detuning coupling := by
  rw [finiteNonresonantBathVolterraKernel, ContinuousLinearMap.norm_restrictScalars]
  simpa using norm_finiteNonresonantBathMemoryPrimitive_le detuning coupling (t - s)

/-- Exact all-time solution selected by the finite-bath mild Volterra equation. -/
def finiteNonresonantBathVolterraSolution {ι : Type*} [Fintype ι]
    (initialSystem : ℂ) (detuning : ι → ℝˣ)
    (coupling initialAmplitude : ι → ℂ) : ℝ → ℂ :=
  volterraSolution
    (finiteNonresonantBathMildSource initialSystem detuning coupling initialAmplitude)
    (finiteNonresonantBathVolterraKernel detuning coupling)

theorem continuous_finiteNonresonantBathVolterraSolution
    {ι : Type*} [Fintype ι]
    (initialSystem : ℂ) (detuning : ι → ℝˣ)
    (coupling initialAmplitude : ι → ℂ) :
    Continuous
      (finiteNonresonantBathVolterraSolution initialSystem detuning coupling initialAmplitude) := by
  exact continuous_volterraSolution
    (continuous_finiteNonresonantBathMildSource initialSystem detuning coupling initialAmplitude)
    (continuous_finiteNonresonantBathVolterraKernel detuning coupling)
    (finiteNonresonantBathMemoryBound_nonneg detuning coupling)
    (finiteNonresonantBathSourceBound_nonneg initialSystem detuning coupling initialAmplitude)
    (norm_finiteNonresonantBathVolterraKernel_le detuning coupling)
    (norm_finiteNonresonantBathMildSource_le initialSystem detuning coupling initialAmplitude)

/-- Unconditional closed mild Langevin law for every finite nonresonant bath. -/
theorem finiteNonresonantBathVolterraSolution_eq
    {ι : Type*} [Fintype ι]
    (initialSystem : ℂ) (detuning : ι → ℝˣ)
    (coupling initialAmplitude : ι → ℂ) (t : ℝ) :
    finiteNonresonantBathVolterraSolution initialSystem detuning coupling initialAmplitude t =
      finiteNonresonantBathMildSource initialSystem detuning coupling initialAmplitude t +
        ∫ s in (0 : ℝ)..t,
          finiteNonresonantBathVolterraKernel detuning coupling t s
            (finiteNonresonantBathVolterraSolution
              initialSystem detuning coupling initialAmplitude s) := by
  exact volterraSolution_eq
    (continuous_finiteNonresonantBathMildSource initialSystem detuning coupling initialAmplitude)
    (continuous_finiteNonresonantBathVolterraKernel detuning coupling)
    (finiteNonresonantBathMemoryBound_nonneg detuning coupling)
    (finiteNonresonantBathSourceBound_nonneg initialSystem detuning coupling initialAmplitude)
    (norm_finiteNonresonantBathVolterraKernel_le detuning coupling)
    (norm_finiteNonresonantBathMildSource_le initialSystem detuning coupling initialAmplitude) t

/-- Paper's finite-bath Langevin equation in exact integrated-memory form. -/
theorem finiteNonresonantBathVolterraSolution_eq_integratedMemory
    {ι : Type*} [Fintype ι]
    (initialSystem : ℂ) (detuning : ι → ℝˣ)
    (coupling initialAmplitude : ι → ℂ) (t : ℝ) :
    finiteNonresonantBathVolterraSolution initialSystem detuning coupling initialAmplitude t =
      initialSystem +
        (∫ r in (0 : ℝ)..t,
          finiteNonresonantBathInitialDrive detuning coupling initialAmplitude r) -
        ∫ s in (0 : ℝ)..t,
          finiteNonresonantBathMemoryPrimitive detuning coupling (t - s) *
            finiteNonresonantBathVolterraSolution
              initialSystem detuning coupling initialAmplitude s := by
  rw [finiteNonresonantBathVolterraSolution_eq,
    finiteNonresonantBathMildSource_eq_initial_add_integral_drive]
  change initialSystem +
      (∫ r in (0 : ℝ)..t,
        finiteNonresonantBathInitialDrive detuning coupling initialAmplitude r) +
      (∫ s in (0 : ℝ)..t,
        (-finiteNonresonantBathMemoryPrimitive detuning coupling (t - s)) *
          finiteNonresonantBathVolterraSolution
            initialSystem detuning coupling initialAmplitude s) = _
  rw [sub_eq_add_neg, ← intervalIntegral.integral_neg]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  ring

theorem finiteNonresonantBathVolterraSolution_vacuum_eq_integratedMemory
    {ι : Type*} [Fintype ι]
    (initialSystem : ℂ) (detuning : ι → ℝˣ)
    (coupling : ι → ℂ) (t : ℝ) :
    finiteNonresonantBathVolterraSolution
        initialSystem detuning coupling (fun _ => 0) t =
      initialSystem -
        ∫ s in (0 : ℝ)..t,
          finiteNonresonantBathMemoryPrimitive detuning coupling (t - s) *
            finiteNonresonantBathVolterraSolution
              initialSystem detuning coupling (fun _ => 0) s := by
  simpa using finiteNonresonantBathVolterraSolution_eq_integratedMemory
    initialSystem detuning coupling (fun _ => 0) t

@[simp]
theorem finiteNonresonantBathVolterraSolution_zero_coupling
    {ι : Type*} [Fintype ι]
    (initialSystem : ℂ) (detuning : ι → ℝˣ)
    (initialAmplitude : ι → ℂ) (t : ℝ) :
    finiteNonresonantBathVolterraSolution
      initialSystem detuning (fun _ => 0) initialAmplitude t = initialSystem := by
  simpa [finiteNonresonantBathMemoryPrimitive,
    finiteNonresonantBathInitialDrive] using
      finiteNonresonantBathVolterraSolution_eq_integratedMemory
        initialSystem detuning (fun _ => 0) initialAmplitude t

end

end GaloisForLFunctions.HTGeometry

