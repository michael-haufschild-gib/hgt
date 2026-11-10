import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.WeightedTraceFloors
import GaloisForLFunctions.HTGeometry.FiniteAmplifierFrame
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# A weighted floor needs more than coefficient one

The trace `cos t + cos(2t)` has floor `−9/8`. At the three cubic roots
its absolute values sum to four, while both Fourier samples vanish.
Normalized interval densities approximate these three point masses,
giving integrable nonnegative weights with the same strict obstruction.
-/

open MeasureTheory Set Filter Topology
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- Unit-mass interval density when `ε>0`. -/
def intervalDensity (x ε t : ℝ) : ℝ := (Ioc x (x + ε)).indicator (fun _ => ε⁻¹) t

theorem intervalDensity_nonneg (x : ℝ) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    0 ≤ intervalDensity x ε t := by
  by_cases ht : t ∈ Ioc x (x + ε)
  · simpa only [intervalDensity, indicator_of_mem ht] using (inv_pos.mpr hε).le
  · simp only [intervalDensity, indicator_of_notMem ht, le_refl]

theorem integrable_intervalDensity (x ε : ℝ) : Integrable (intervalDensity x ε) :=
  (integrable_indicator_iff measurableSet_Ioc).mpr continuous_const.integrableOn_Ioc

private theorem intervalDensity_smul_eq {E : Type*} [Zero E] [SMulWithZero ℝ E]
    (x ε : ℝ) (f : ℝ → E) :
    (fun t => intervalDensity x ε t • f t) =
      (Ioc x (x + ε)).indicator (fun t => ε⁻¹ • f t) := by
  funext t
  by_cases ht : t ∈ Ioc x (x + ε)
  · simp only [intervalDensity, indicator_of_mem ht]
  · simp only [intervalDensity, indicator_of_notMem ht, zero_smul]

theorem integrable_intervalDensity_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x ε : ℝ) {f : ℝ → E} (hf : Continuous f) :
    Integrable (fun t => intervalDensity x ε t • f t) := by
  rw [intervalDensity_smul_eq]
  exact (integrable_indicator_iff measurableSet_Ioc).mpr
    (continuous_const.smul hf).integrableOn_Ioc

theorem intervalDensity_average {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (x : ℝ) {ε : ℝ} (hε : 0 < ε) (f : ℝ → E) :
    (∫ t, intervalDensity x ε t • f t) = ε⁻¹ • ∫ t in x..(x + ε), f t := by
  rw [intervalDensity_smul_eq, integral_indicator measurableSet_Ioc, integral_smul,
    intervalIntegral.integral_of_le (by linarith only [hε])]

/-- Continuity turns narrow interval averages into evaluation, by the fundamental theorem. -/
theorem tendsto_intervalDensity_average {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (x : ℝ) {f : ℝ → E} (hf : Continuous f) :
    Tendsto (fun ε => ∫ t, intervalDensity x ε t • f t) (𝓝[>] (0 : ℝ)) (𝓝 (f x)) := by
  have hd := intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable x x) hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have ht := hd.tendsto_slope_zero_right
  simp only [intervalIntegral.integral_same, sub_zero] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (intervalDensity_average x hε f).symm

/-- The sum of equal narrow interval densities at finitely many sampling sites. -/
def finiteSamplingWeight {n : ℕ} (x : Fin n → ℝ) (ε t : ℝ) : ℝ :=
  ∑ j, intervalDensity (x j) ε t

theorem finiteSamplingWeight_nonneg {n : ℕ} (x : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε)
    (t : ℝ) : 0 ≤ finiteSamplingWeight x ε t :=
  Finset.sum_nonneg fun j _ => intervalDensity_nonneg (x j) hε t

theorem integrable_finiteSamplingWeight {n : ℕ} (x : Fin n → ℝ) (ε : ℝ) :
    Integrable (finiteSamplingWeight x ε) :=
  integrable_finsetSum Finset.univ fun j _ => integrable_intervalDensity (x j) ε

theorem integral_finiteSamplingWeight_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {n : ℕ} (x : Fin n → ℝ) (ε : ℝ) {f : ℝ → E} (hf : Continuous f) :
    (∫ t, finiteSamplingWeight x ε t • f t) =
      ∑ j, ∫ t, intervalDensity (x j) ε t • f t := by
  simp only [finiteSamplingWeight, Finset.sum_smul]
  exact integral_finsetSum Finset.univ fun j _ => integrable_intervalDensity_smul (x j) ε hf

theorem tendsto_finiteSamplingWeight_integral {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {n : ℕ} (x : Fin n → ℝ) {f : ℝ → E}
    (hf : Continuous f) :
    Tendsto (fun ε => ∫ t, finiteSamplingWeight x ε t • f t)
      (𝓝[>] (0 : ℝ)) (𝓝 (∑ j, f (x j))) := by
  simp_rw [integral_finiteSamplingWeight_smul x _ hf]
  exact tendsto_finsetSum Finset.univ fun j _ => tendsto_intervalDensity_average (x j) hf

/-- Two positive-frequency modes with a sharp floor of `−9/8`. -/
def twoModeTrace (t : ℝ) : ℝ := Real.cos t + Real.cos (2 * t)

theorem twoModeTrace_floor (t : ℝ) : -(9 / 8 : ℝ) ≤ twoModeTrace t := by
  rw [twoModeTrace, Real.cos_two_mul]
  nlinarith only [sq_nonneg (Real.cos t + 1 / 4)]

theorem twoModeTrace_eq_finiteExpSum (t : ℝ) :
    twoModeTrace t = (finiteExpSum ![1, 1] ![1, 2] t).re := by
  simp only [finiteExpSum, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, one_mul, Complex.add_re, Complex.exp_ofReal_mul_I_re, twoModeTrace]

def cubicSampleSites (j : Fin 3) : ℝ := 2 * Real.pi * j / 3

theorem cubicSampleSites_abs_trace : (∑ j, |twoModeTrace (cubicSampleSites j)|) = 4 := by
  have h2 : Real.cos (2 * Real.pi / 3) = -(1 / 2 : ℝ) := by
    have h := Real.cos_two_mul (Real.pi / 3)
    rw [show 2 * (Real.pi / 3) = 2 * Real.pi / 3 by ring, Real.cos_pi_div_three] at h
    norm_num at h ⊢
    exact h
  have h4 : Real.cos (4 * Real.pi / 3) = -(1 / 2 : ℝ) := by
    have h := Real.cos_two_mul (2 * Real.pi / 3)
    rw [show 2 * (2 * Real.pi / 3) = 4 * Real.pi / 3 by ring, h2] at h
    norm_num at h ⊢
    exact h
  have h8 : Real.cos (8 * Real.pi / 3) = -(1 / 2 : ℝ) := by
    have h := Real.cos_two_mul (4 * Real.pi / 3)
    rw [show 2 * (4 * Real.pi / 3) = 8 * Real.pi / 3 by ring, h4] at h
    norm_num at h ⊢
    exact h
  rw [Fin.sum_univ_three]
  norm_num [twoModeTrace, cubicSampleSites, show 2 * Real.pi * 2 / 3 = 4 * Real.pi / 3 by ring,
    show 2 * (2 * Real.pi / 3) = 4 * Real.pi / 3 by ring,
    show 2 * (4 * Real.pi / 3) = 8 * Real.pi / 3 by ring, h2, h4, h8]

theorem cubicSampleSites_character {r : ℕ} (hr : 0 < r) (hr3 : r < 3) :
    (∑ j, Complex.exp ((((r : ℝ) * cubicSampleSites j : ℝ) : ℂ) * Complex.I)) = 0 := by
  have he : (fun j : ℕ => Complex.exp ((((r : ℝ) * (2 * Real.pi * j / 3) : ℝ) : ℂ) * Complex.I)) =
      fun j => Complex.exp (2 * Real.pi * Complex.I * r * j / 3) := by
    funext j
    congr 1
    push_cast
    ring
  change (∑ j : Fin 3, Complex.exp ((((r : ℝ) * (2 * Real.pi * (j : ℕ) / 3) : ℝ) : ℂ) * Complex.I)) = 0
  rw [Fin.sum_univ_eq_sum_range, he]
  exact _root_.HTGeometry.exp_unit_sum_zero 3 r hr hr3

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
