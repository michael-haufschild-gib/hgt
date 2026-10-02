import GaloisForLFunctions.RHTower.ZetaChiDualCoherentBlock

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators
noncomputable section
namespace RHTower


/-- The coherent block lies in the positive integer support below the literal cutoff. -/
theorem zetaChiDualCoherentBlock_pos_le {m : ℕ} (hm : 1 ≤ m)
    {n : ℕ} (hn : n ∈ zetaChiDualCoherentBlock m) : 0 < n ∧ n ≤ (5 * m) ^ 10 := by
  have hlo := (Finset.mem_Icc.mp hn).1
  have hup := (Finset.mem_Icc.mp hn).2
  have hm0 : 0 < m := by omega
  constructor
  · exact lt_of_lt_of_le (by positivity) hlo
  · nlinarith only [hup, show 0 ≤ m ^ 10 by omega]

/-- Every complete subset of the actual smoothed block retains both a positive
real first mean and a uniform norm bound proportional to its cardinality. -/
theorem eventually_zetaChi_dual_block_subset_mean_bounds
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∀ᶠ m : ℕ in atTop, ∀ s ∈ Metric.closedBall c r, ∀ S : Finset ℕ,
      S ⊆ zetaChiDualCoherentBlock m →
      Real.pi * (smoothAFECutoff 1).re * S.card ≤
        (∫ t in (5 * (m : ℝ)) ^ 10..(2 * (5 * (m : ℝ)) ^ 10),
          ∑ n ∈ S, smoothAFECutoff ((n : ℝ) / (5 * (m : ℝ)) ^ 10) *
            zetaChiDualInteriorAtom s n t).re ∧
      ‖∫ t in (5 * (m : ℝ)) ^ 10..(2 * (5 * (m : ℝ)) ^ 10),
          ∑ n ∈ S, smoothAFECutoff ((n : ℝ) / (5 * (m : ℝ)) ^ 10) *
            zetaChiDualInteriorAtom s n t‖ ≤ (2 * Real.pi + 1) * S.card := by
  obtain ⟨D, hD, hb⟩ := exists_zetaChi_dual_weighted_interior_mean c hr hc0 hc1
  obtain ⟨M, hM⟩ := eventually_atTop.mp hb
  obtain ⟨L, hL⟩ := eventually_atTop.mp
    (eventually_zetaChi_dual_smoothed_interior_mean_ge c hr hc0 hc1)
  obtain ⟨K, hK⟩ := exists_nat_gt D
  filter_upwards [eventually_ge_atTop M, eventually_ge_atTop L,
    eventually_ge_atTop K, eventually_ge_atTop (1 : ℕ)] with m hmM hmL hmK hm1
  intro s hs S hS
  have hmR : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hN : 0 < (5 * (m : ℝ)) ^ 10 := by positivity
  have hgeom (n : ℕ) (hn : n ∈ S) := zetaChiDualCoherentBlock_saddle hm1 (hS hn)
  have hnR (n : ℕ) (hn : n ∈ S) : 0 < (n : ℝ) ∧ (n : ℝ) ≤ (5 * (m : ℝ)) ^ 10 := by
    have hh := zetaChiDualCoherentBlock_pos_le hm1 (hS hn)
    exact_mod_cast hh
  let w : ℕ → ℝ := fun n => (smoothAFECutoff ((n : ℝ) / (5 * (m : ℝ)) ^ 10)).re
  have hw : ∀ n ∈ S, 0 ≤ w n := fun n hn =>
    (smoothAFECutoff_re_pos (div_pos (hnR n hn).1 hN)).le
  have hw1 : ∀ n ∈ S, w n ≤ 1 := fun n hn =>
    smoothAFECutoff_re_le_one (div_pos (hnR n hn).1 hN)
  have hwlo : ∀ n ∈ S, (smoothAFECutoff 1).re ≤ w n := by
    intro n hn
    exact smoothAFECutoff_re_antitoneOn (div_pos (hnR n hn).1 hN) (by norm_num)
      ((div_le_one hN).mpr (hnR n hn).2)
  have heq (n : ℕ) (hn : n ∈ S) :
      smoothAFECutoff ((n : ℝ) / (5 * (m : ℝ)) ^ 10) = (w n : ℂ) := by
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using smoothAFECutoff_im_eq_zero (div_pos (hnR n hn).1 hN)
  have hsum : 0 ≤ ∑ n ∈ S, w n := Finset.sum_nonneg hw
  have hsum1 : ∑ n ∈ S, w n ≤ S.card := by
    simpa using (Finset.sum_le_sum hw1)
  have hsumlo : (smoothAFECutoff 1).re * S.card ≤ ∑ n ∈ S, w n := by
    simpa [mul_comm] using (Finset.sum_le_sum hwlo)
  have hbnd := hM (5 * m) (by omega) s hs S w hw
    (fun n hn => by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hgeom n hn)
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hbnd
  have hlow := hL (5 * m) (by omega) s hs S
    (fun n hn => by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hgeom n hn)
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hlow
  constructor
  · calc
      _ = Real.pi * ((smoothAFECutoff 1).re * S.card) := by ring
      _ ≤ Real.pi * ∑ n ∈ S, w n := mul_le_mul_of_nonneg_left hsumlo Real.pi_pos.le
      _ ≤ _ := hlow
  · have herr : D / (5 * (m : ℝ)) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      have hKR : (K : ℝ) ≤ m := by exact_mod_cast hmK
      linarith
    let Z : ℂ := ∫ t in (5 * (m : ℝ)) ^ 10..(2 * (5 * (m : ℝ)) ^ 10),
      ∑ n ∈ S, (w n : ℂ) * zetaChiDualInteriorAtom s n t
    have hnorm : ‖Z‖ ≤ (2 * Real.pi + 1) * S.card := by
      have htriangle : ‖Z‖ ≤ ‖Z - ((2 * Real.pi * ∑ n ∈ S, w n : ℝ) : ℂ)‖ +
          ‖((2 * Real.pi * ∑ n ∈ S, w n : ℝ) : ℂ)‖ := by
        simpa only [sub_add_cancel] using norm_add_le
          (Z - ((2 * Real.pi * ∑ n ∈ S, w n : ℝ) : ℂ))
          (((2 * Real.pi * ∑ n ∈ S, w n : ℝ) : ℂ))
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ 2 * Real.pi * ∑ n ∈ S, w n by positivity)] at htriangle
      have he := mul_le_mul_of_nonneg_right herr hsum
      have hc := mul_le_mul_of_nonneg_left hsum1 (show 0 ≤ 2 * Real.pi + 1 by positivity)
      change ‖Z - ((2 * Real.pi * ∑ n ∈ S, w n : ℝ) : ℂ)‖ ≤ _ at hbnd
      linarith
    have hint : (∫ t in (5 * (m : ℝ)) ^ 10..(2 * (5 * (m : ℝ)) ^ 10),
        ∑ n ∈ S, smoothAFECutoff ((n : ℝ) / (5 * (m : ℝ)) ^ 10) *
          zetaChiDualInteriorAtom s n t) = Z := by
      apply intervalIntegral.integral_congr
      intro t _
      apply Finset.sum_congr rfl
      intro n hn
      rw [heq n hn]
    rw [hint]
    exact hnorm

end RHTower
