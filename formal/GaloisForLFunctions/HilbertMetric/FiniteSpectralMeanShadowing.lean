import GaloisForLFunctions.RHTower.FiniteExponentialPencilMeanSquare
import Mathlib.Analysis.Complex.Circle

/-!
# Mean shadowing determines a finite unitary spectrum

Soma--Tomizawa, arXiv:2608.22784, use vanishing Cesàro mean distance
to express strong orbit shadowing. For the finite exponential pencils of
the corpus, that condition is rigid: it identifies every mode coefficient.
The mean-square identity and the uniform coefficient bound convert mean
distance into an exact spectral classification.
-/

noncomputable section
open Filter Topology RHTower
open scoped BigOperators
namespace GaloisForLFunctions.HilbertMetric

/-- A finite spectral signal, indexed by its distinct unit-circle modes. -/
def circleSignal (s : Finset Circle) (c : Circle → ℂ) (n : ℕ) : ℂ :=
  finiteExponentialPencil s c (fun z => (z : ℂ)) n

/-- Mean orbit distance between two finite spectral signals. -/
def spectralMeanDistance (s : Finset Circle) (a b : Circle → ℂ) (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖circleSignal s a n-circleSignal s b n‖

theorem circleSignal_sub (s : Finset Circle) (a b : Circle → ℂ) (n : ℕ) :
    circleSignal s a n-circleSignal s b n = circleSignal s (fun z => a z-b z) n := by
  simp only [circleSignal, finiteExponentialPencil, sub_mul, Finset.sum_sub_distrib]

/-- A finite unitary signal is bounded by the total absolute spectral mass. -/
theorem norm_circleSignal_le (s : Finset Circle) (c : Circle → ℂ) (n : ℕ) :
    ‖circleSignal s c n‖ ≤ ∑ z ∈ s, ‖c z‖ := by
  calc
    ‖circleSignal s c n‖ ≤ ∑ z ∈ s, ‖c z * (z : ℂ)^n‖ := norm_sum_le _ _
    _ = ∑ z ∈ s, ‖c z‖ := by
      simp only [norm_mul, norm_pow, Circle.norm_coe, one_pow, mul_one]

/-- The coefficient mass converts mean distance into mean-square distance. -/
theorem spectralMeanSquare_le_mass_mul_mean (s : Finset Circle)
    (a b : Circle → ℂ) (N : ℕ) :
    (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, ‖circleSignal s a n-circleSignal s b n‖^2 ≤
      (∑ z ∈ s, ‖a z-b z‖) * spectralMeanDistance s a b N := by
  rw [spectralMeanDistance, mul_left_comm, Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg N))
  apply Finset.sum_le_sum
  intro n _
  rw [circleSignal_sub, pow_two]
  exact mul_le_mul_of_nonneg_right (norm_circleSignal_le s (fun z => a z-b z) n)
    (norm_nonneg _)

/-- Exact mean-square separation of every pair of finite unitary signals. -/
theorem tendsto_spectralMeanSquare (s : Finset Circle) (a b : Circle → ℂ) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ *
      ∑ n ∈ Finset.range N, ‖circleSignal s a n-circleSignal s b n‖^2)
      atTop (𝓝 (∑ z ∈ s, ‖a z-b z‖^2)) := by
  classical
  simp_rw [circleSignal_sub]
  exact tendsto_finiteExponentialPencil_cesaro_norm_sq s (fun z => a z-b z)
    (fun z => (z : ℂ)) (fun z _ => Circle.norm_coe z)
    (fun _ _ _ _ h => Subtype.ext h)

/-- Mean shadowing is equivalent to equality of every spectral coefficient. -/
theorem spectralMeanDistance_tendsto_zero_iff (s : Finset Circle) (a b : Circle → ℂ) :
    Tendsto (spectralMeanDistance s a b) atTop (𝓝 0) ↔ ∀ z ∈ s, a z = b z := by
  constructor
  · intro h
    have hu : Tendsto (fun N => (∑ z ∈ s, ‖a z-b z‖) * spectralMeanDistance s a b N)
        atTop (𝓝 0) := by simpa only [mul_zero] using h.const_mul (∑ z ∈ s, ‖a z-b z‖)
    have hle : (∑ z ∈ s, ‖a z-b z‖^2) ≤ 0 :=
      le_of_tendsto_of_tendsto' (tendsto_spectralMeanSquare s a b) hu
        (spectralMeanSquare_le_mass_mul_mean s a b)
    have hz : (∑ z ∈ s, ‖a z-b z‖^2) = 0 :=
      le_antisymm hle (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    intro z hzs
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun z (_ : z ∈ s) =>
      sq_nonneg ‖a z-b z‖)).mp hz z hzs
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hterm))
  · intro h
    have he : ∀ n, circleSignal s a n = circleSignal s b n := by
      intro n
      apply Finset.sum_congr rfl
      intro z hz
      rw [h z hz]
    have hz : spectralMeanDistance s a b = fun _ => 0 := by
      funext N
      simp only [spectralMeanDistance, he, sub_self, norm_zero, Finset.sum_const_zero, mul_zero]
    rw [hz]
    exact tendsto_const_nhds

/-- Statistical agreement of finite spectral signals is exact agreement at every time. -/
theorem spectralMeanDistance_tendsto_zero_iff_signal_eq
    (s : Finset Circle) (a b : Circle → ℂ) :
    Tendsto (spectralMeanDistance s a b) atTop (𝓝 0) ↔
      circleSignal s a = circleSignal s b := by
  constructor
  · intro h
    have hc := (spectralMeanDistance_tendsto_zero_iff s a b).mp h
    funext n
    apply Finset.sum_congr rfl
    intro z hz
    rw [hc z hz]
  · intro h
    have hz : spectralMeanDistance s a b = fun _ => 0 := by
      funext N
      simp only [spectralMeanDistance, h, sub_self, norm_zero, Finset.sum_const_zero, mul_zero]
    rw [hz]
    exact tendsto_const_nhds

/-- Proportion of sampling times at which the two signals differ. -/
def spectralDisagreementDensity (s : Finset Circle) (a b : Circle → ℂ) (N : ℕ) : ℝ := by
  classical
  exact (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N,
    if circleSignal s a n = circleSignal s b n then 0 else 1

/-- Bounded spectral mass controls mean distance by the disagreement density. -/
theorem spectralMeanDistance_le_mass_mul_density (s : Finset Circle)
    (a b : Circle → ℂ) (N : ℕ) :
    spectralMeanDistance s a b N ≤
      (∑ z ∈ s, ‖a z-b z‖) * spectralDisagreementDensity s a b N := by
  classical
  rw [spectralMeanDistance, spectralDisagreementDensity, mul_left_comm, Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg N))
  apply Finset.sum_le_sum
  intro n _
  by_cases h : circleSignal s a n = circleSignal s b n
  · simp only [h, sub_self, norm_zero, if_pos, mul_zero, le_refl]
  · rw [if_neg h, mul_one, circleSignal_sub]
    exact norm_circleSignal_le s (fun z => a z-b z) n

/-- Agreement on a set of density one identifies every finite spectral coefficient. -/
theorem spectralDisagreementDensity_tendsto_zero_iff
    (s : Finset Circle) (a b : Circle → ℂ) :
    Tendsto (spectralDisagreementDensity s a b) atTop (𝓝 0) ↔
      ∀ z ∈ s, a z = b z := by
  classical
  constructor
  · intro h
    apply (spectralMeanDistance_tendsto_zero_iff s a b).mp
    apply squeeze_zero
      (fun N => mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))
        (Finset.sum_nonneg fun _ _ => norm_nonneg _))
      (spectralMeanDistance_le_mass_mul_density s a b)
    simpa only [mul_zero] using h.const_mul (∑ z ∈ s, ‖a z-b z‖)
  · intro h
    have hs := (spectralMeanDistance_tendsto_zero_iff_signal_eq s a b).mp
      ((spectralMeanDistance_tendsto_zero_iff s a b).mpr h)
    have hz : spectralDisagreementDensity s a b = fun _ => 0 := by
      funext N
      simp [spectralDisagreementDensity, hs]
    rw [hz]
    exact tendsto_const_nhds

end GaloisForLFunctions.HilbertMetric
