import GaloisForLFunctions.RHTower.ZetaChiDualSmoothedInteriorMean
import Mathlib.Order.Interval.Finset.Nat

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators
noncomputable section
namespace RHTower

/-- A literal growing integer block strictly inside the unique integer-saddle range. -/
def zetaChiDualCoherentBlock (m : ℕ) : Finset ℕ :=
  Finset.Icc (5 ^ 9 * m ^ 10) (6 * 5 ^ 8 * m ^ 10)

theorem card_zetaChiDualCoherentBlock (m : ℕ) :
    (zetaChiDualCoherentBlock m).card = 5 ^ 8 * m ^ 10 + 1 := by
  rw [zetaChiDualCoherentBlock, Nat.card_Icc]
  have he : 6 * 5 ^ 8 * m ^ 10 + 1 = 5 ^ 9 * m ^ 10 + (5 ^ 8 * m ^ 10 + 1) := by ring
  rw [he, Nat.add_sub_cancel_left]

/-- Every term in the concrete block has the full polynomial saddle margin. -/
theorem zetaChiDualCoherentBlock_saddle {m : ℕ} (hm : 1 ≤ m)
    {n : ℕ} (hn : n ∈ zetaChiDualCoherentBlock m) :
    (5 * (m : ℝ)) ^ 10 + (5 * (m : ℝ)) ^ 6 ≤ 2 * Real.pi * n ∧
      2 * Real.pi * n + (5 * (m : ℝ)) ^ 6 ≤ 2 * (5 * (m : ℝ)) ^ 10 := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hloN := (Finset.mem_Icc.mp hn).1
  have hupN := (Finset.mem_Icc.mp hn).2
  have hlo : (5 : ℝ) ^ 9 * (m : ℝ) ^ 10 ≤ n := by exact_mod_cast hloN
  have hup : (n : ℝ) ≤ 6 * (5 : ℝ) ^ 8 * (m : ℝ) ^ 10 := by exact_mod_cast hupN
  have hpow : (m : ℝ) ^ 6 ≤ (m : ℝ) ^ 10 := by
    have h4 : (1 : ℝ) ≤ (m : ℝ) ^ 4 := one_le_pow₀ hmR
    nlinarith only [mul_nonneg (sub_nonneg.mpr h4) (show 0 ≤ (m : ℝ) ^ 6 by positivity)]
  have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hml : 6 * (n : ℝ) ≤ 2 * Real.pi * n :=
    mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three]) hnn
  have hmu : 2 * Real.pi * (n : ℝ) ≤ 8 * n :=
    mul_le_mul_of_nonneg_right (by linarith [Real.pi_lt_four]) hnn
  constructor <;> nlinarith only [hlo, hup, hpow, hml, hmu,
    show 0 ≤ (m : ℝ) ^ 6 by positivity]

/-- The selected literal Gaussian-smoothed carrier has a physical first mean
of order the window length, uniformly on the whole fixed compact disc. -/
theorem exists_zetaChi_dual_coherent_block_mean_lower
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ m : ℕ in atTop, ∀ s ∈ Metric.closedBall c r,
      κ * (5 * (m : ℝ)) ^ 10 ≤
        (∫ t in (5 * (m : ℝ)) ^ 10..(2 * (5 * (m : ℝ)) ^ 10),
          ∑ n ∈ zetaChiDualCoherentBlock m,
            smoothAFECutoff ((n : ℝ) / (5 * (m : ℝ)) ^ 10) * zetaChiDualInteriorAtom s n t).re := by
  have hv : 0 < (smoothAFECutoff 1).re := smoothAFECutoff_re_pos (by norm_num)
  refine ⟨Real.pi * (smoothAFECutoff 1).re / 25, by positivity, ?_⟩
  obtain ⟨M, hM⟩ := eventually_atTop.mp (eventually_zetaChi_dual_smoothed_interior_mean_ge c hr hc0 hc1)
  filter_upwards [eventually_ge_atTop M, eventually_ge_atTop (1 : ℕ)] with m hmM hm1
  intro s hs
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hm0 : (0 : ℝ) < m := by linarith
  have hbound := hM (5 * m) (by omega) s hs (zetaChiDualCoherentBlock m)
    (fun n hn => by simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      zetaChiDualCoherentBlock_saddle hm1 hn)
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hbound
  have hweight (n : ℕ) (hn : n ∈ zetaChiDualCoherentBlock m) :
      (smoothAFECutoff 1).re ≤ (smoothAFECutoff ((n : ℝ) / (5 * (m : ℝ)) ^ 10)).re := by
    have hloN := (Finset.mem_Icc.mp hn).1
    have hupN := (Finset.mem_Icc.mp hn).2
    have hlo : (5 : ℝ) ^ 9 * (m : ℝ) ^ 10 ≤ n := by exact_mod_cast hloN
    have hup : (n : ℝ) ≤ 6 * (5 : ℝ) ^ 8 * (m : ℝ) ^ 10 := by exact_mod_cast hupN
    have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hlo
    have hnN : (n : ℝ) ≤ (5 * (m : ℝ)) ^ 10 := by nlinarith only [hup, show 0 ≤ (m : ℝ) ^ 10 by positivity]
    exact smoothAFECutoff_re_antitoneOn (div_pos hn0 (by positivity)) (by norm_num)
      ((div_le_one (by positivity : 0 < (5 * (m : ℝ)) ^ 10)).mpr hnN)
  have hcard : (5 * (m : ℝ)) ^ 10 / 25 ≤ ((zetaChiDualCoherentBlock m).card : ℝ) := by
    rw [card_zetaChiDualCoherentBlock]
    push_cast
    nlinarith only [show 0 ≤ (m : ℝ) ^ 10 by positivity]
  have hsum : (smoothAFECutoff 1).re * ((zetaChiDualCoherentBlock m).card : ℝ) ≤
      ∑ n ∈ zetaChiDualCoherentBlock m,
        (smoothAFECutoff ((n : ℝ) / (5 * (m : ℝ)) ^ 10)).re := by
    calc
      _ = ∑ _n ∈ zetaChiDualCoherentBlock m, (smoothAFECutoff 1).re := by simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum hweight
  have hmass := (mul_le_mul_of_nonneg_left hcard hv.le).trans hsum
  calc
    _ = Real.pi * ((smoothAFECutoff 1).re * ((5 * (m : ℝ)) ^ 10 / 25)) := by ring
    _ ≤ Real.pi * ∑ n ∈ zetaChiDualCoherentBlock m,
        (smoothAFECutoff ((n : ℝ) / (5 * (m : ℝ)) ^ 10)).re :=
      mul_le_mul_of_nonneg_left hmass Real.pi_pos.le
    _ ≤ _ := hbound

end RHTower
