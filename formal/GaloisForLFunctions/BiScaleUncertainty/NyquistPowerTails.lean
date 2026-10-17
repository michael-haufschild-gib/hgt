import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Explicit positive power-tail bounds for Nyquist residuals -/

open Set Filter Topology MeasureTheory
open scoped BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section
set_option autoImplicit false

def nyquistPowerTail (p : ℝ) (N : ℕ) : ℝ :=
  ∑' k : ℕ, ((N + k + 1 : ℕ) : ℝ) ^ p

theorem summable_nyquistPowerTail {p : ℝ} (hp : p < -1) (N : ℕ) :
    Summable (fun k : ℕ => ((N + k + 1 : ℕ) : ℝ) ^ p) := by
  simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    (summable_nat_add_iff (f := fun k : ℕ => (k : ℝ) ^ p) (N + 1)).mpr
      (Real.summable_nat_rpow.mpr hp)

theorem nyquistPowerTail_integral_bounds {p : ℝ} (hp : p < -1) (N : ℕ) :
    ((N + 1 : ℕ) : ℝ) ^ (p + 1) / (-p - 1) ≤ nyquistPowerTail p N ∧
      nyquistPowerTail p N ≤ ((N + 1 : ℕ) : ℝ) ^ p +
        ((N + 1 : ℕ) : ℝ) ^ (p + 1) / (-p - 1) := by
  have hn : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hanti : AntitoneOn (fun x : ℝ => x ^ p) (Ici ((N + 1 : ℕ) : ℝ)) :=
    (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith : p ≤ 0)).mono
      (fun _ hx => hn.trans_le hx)
  have hnonneg : ∀ x ∈ Ioi ((N + 1 : ℕ) : ℝ), 0 ≤ x ^ p :=
    fun x hx => Real.rpow_nonneg (hn.trans hx).le _
  have hi : (∫ x in Ioi ((N + 1 : ℕ) : ℝ), x ^ p) =
      ((N + 1 : ℕ) : ℝ) ^ (p + 1) / (-p - 1) := by
    rw [integral_Ioi_rpow_of_lt hp hn]
    have hq : p + 1 ≠ 0 := by linarith
    have hq' : -p - 1 ≠ 0 := by linarith
    field_simp
    ring
  constructor
  · have h := hanti.integral_le_tsum_comp_add (N + 1)
      (Real.summable_nat_rpow.mpr hp) hnonneg
    rw [hi] at h
    simpa only [nyquistPowerTail, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h
  · have h := hanti.tsum_comp_add_le_integral (N + 1)
      (integrableOn_Ioi_rpow_of_lt hp hn) hnonneg
    rw [hi] at h
    have hs : nyquistPowerTail p N = ((N + 1 : ℕ) : ℝ) ^ p +
        ∑' k : ℕ, ((k + (N + 1) + 1 : ℕ) : ℝ) ^ p := by
      simpa only [nyquistPowerTail, Finset.sum_range_one, Nat.add_zero,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        (Summable.sum_add_tsum_nat_add 1 (summable_nyquistPowerTail hp N)).symm
    rw [hs]
    exact add_le_add le_rfl h

theorem nyquistPowerTail_le {p : ℝ} (hp : p < -1) (N : ℕ) :
    nyquistPowerTail p N ≤ (1 + 1 / (-p - 1)) * ((N + 1 : ℕ) : ℝ) ^ (p + 1) := by
  have hn : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hbase : (1 : ℝ) ≤ (N + 1 : ℕ) := by exact_mod_cast (show 1 ≤ N + 1 by omega)
  have hstep : ((N + 1 : ℕ) : ℝ) ^ p ≤ ((N + 1 : ℕ) : ℝ) ^ (p + 1) := by
    rw [Real.rpow_add hn, Real.rpow_one]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hbase (Real.rpow_pos_of_pos hn p).le
  calc
    _ ≤ ((N + 1 : ℕ) : ℝ) ^ p + ((N + 1 : ℕ) : ℝ) ^ (p + 1) / (-p - 1) :=
      (nyquistPowerTail_integral_bounds hp N).2
    _ ≤ ((N + 1 : ℕ) : ℝ) ^ (p + 1) +
        ((N + 1 : ℕ) : ℝ) ^ (p + 1) / (-p - 1) := add_le_add hstep le_rfl
    _ = _ := by ring

theorem nyquistPowerTail_normalized_bounds {p : ℝ} (hp : p < -1) (N : ℕ) :
    1 / (-p - 1) ≤ nyquistPowerTail p N / ((N + 1 : ℕ) : ℝ) ^ (p + 1) ∧
      nyquistPowerTail p N / ((N + 1 : ℕ) : ℝ) ^ (p + 1) ≤
        1 / (-p - 1) + 1 / ((N + 1 : ℕ) : ℝ) := by
  have hn : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hpow := Real.rpow_pos_of_pos hn (p + 1)
  have he : ((N + 1 : ℕ) : ℝ) ^ p / ((N + 1 : ℕ) : ℝ) ^ (p + 1) =
      1 / ((N + 1 : ℕ) : ℝ) := by
    rw [Real.rpow_add hn, Real.rpow_one]
    have hpn := (Real.rpow_pos_of_pos hn p).ne'
    field_simp
  have hc : (((N + 1 : ℕ) : ℝ) ^ (p + 1) / (-p - 1)) /
      ((N + 1 : ℕ) : ℝ) ^ (p + 1) = 1 / (-p - 1) := by
    field_simp
  constructor
  · have h := div_le_div_of_nonneg_right (nyquistPowerTail_integral_bounds hp N).1 hpow.le
    rwa [hc] at h
  · have h := div_le_div_of_nonneg_right (nyquistPowerTail_integral_bounds hp N).2 hpow.le
    simpa only [add_div, he, hc, add_comm] using h

theorem tendsto_nyquistPowerTail_normalized {p : ℝ} (hp : p < -1) :
    Tendsto (fun N => nyquistPowerTail p N / ((N + 1 : ℕ) : ℝ) ^ (p + 1)) atTop
      (𝓝 (1 / (-p - 1))) := by
  have hu : Tendsto (fun N : ℕ => 1 / (-p - 1) + 1 / ((N + 1 : ℕ) : ℝ))
      atTop (𝓝 (1 / (-p - 1))) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_zero] using
      (tendsto_const_nhds (x := 1 / (-p - 1))).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
    (fun N => (nyquistPowerTail_normalized_bounds hp N).1)
    (fun N => (nyquistPowerTail_normalized_bounds hp N).2)

end
end GaloisForLFunctions.BiScaleUncertainty
