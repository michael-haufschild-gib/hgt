import GaloisForLFunctions.RHTower.ZetaChiDualSaddleRemainder
import Mathlib.Order.Filter.AtTopBot.Ring

open Complex Set Filter Topology MeasureTheory
noncomputable section
namespace RHTower


private theorem exists_zetaChi_real_dual_atom_disc_stationary
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ s ∈ Metric.closedBall c r,
      ∀ (n : ℝ) (h : ℝ), 0 < n → 8 ≤ 2 * Real.pi * (n : ℝ) →
      0 < h → h ≤ (2 * Real.pi * n) / 2 →
      (2 * Real.pi * n) / 2 ≤ (N : ℝ) →
      (N : ℝ) ≤ 2 * Real.pi * n - h →
      2 * Real.pi * n + h ≤ 2 * N → 2 * (N : ℝ) ≤ 2 * (2 * Real.pi * n) →
      2 * |s.im| ≤ 2 * Real.pi * n →
      26 * ‖s - (1 / 2 : ℂ)‖ + 10 * ‖s - (1 / 2 : ℂ)‖ ^ 2 ≤ 2 * Real.pi * n →
      ‖(∫ t in (N : ℝ)..(2 * N),
          zetaChi (s + (t : ℂ) * I) * (n : ℂ) ^ (s - 1) *
            bourgainOscillation (t * Real.log n)) - ((2 * Real.pi : ℝ) : ℂ) * bourgainOscillation (2 * Real.pi * n)‖ ≤
        ‖zetaChiDualRowCoefficient s N n‖ *
          (C * (78 + 2 * h ^ 2 / N + 40 * (2 * Real.pi * n) ^ 2 / ((N : ℝ) * h) +
            4 * h ^ 4 / (2 * Real.pi * n) ^ 2 + 40 * (2 * Real.pi * n) / h)) +
          (52 * ‖s - (1 / 2 : ℂ)‖ + 20 * ‖s - (1 / 2 : ℂ)‖ ^ 2) / n := by
  obtain ⟨C, hC, hbound⟩ := exists_compactGaussianRow_disc_stationary c hr hc0 hc1
  refine ⟨C, hC, ?_⟩
  filter_upwards [hbound, eventually_ge_atTop (1 : ℕ)] with N hN hN1
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  intro s hs n h hn ha hh hha hl hlh hhu hu him hsize
  have hre : |s.re - c.re| ≤ r := (by
    simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (s - c) :
      |s.re - c.re| ≤ dist s c).trans hs
  have hs0 : 0 < s.re := by linarith [(abs_le.mp hre).1]
  have hs1 : s.re < 1 := by linarith [(abs_le.mp hre).2]
  have hb := hN s hs (2 * Real.pi * n) h ha hh hha hl hlh hhu hu
  have he : (2 * Real.pi * (n : ℝ)) / (2 * Real.pi) = n := by field_simp
  rw [he] at hb
  have hscaled := mul_le_mul_of_nonneg_left hb
    (norm_nonneg (zetaChiDualRowCoefficient s N n))
  rw [← norm_mul, mul_sub, ← intervalIntegral.integral_const_mul,
    zetaChiDualRowCoefficient_mul_saddle s hNR] at hscaled
  have heq (t : ℝ) : zetaChiDualRowCoefficient s N n *
      (reflectedCompactGaussianRow s N t * bourgainOscillation (t * Real.log n)) =
      zetaChi (s + (t : ℂ) * I) * (n : ℂ) ^ (s - 1) *
        bourgainOscillation (t * Real.log n) := by
    rw [← mul_assoc, zetaChiDualRowCoefficient_mul_row s hNR]
  rw [intervalIntegral.integral_congr (fun t _ => heq t)] at hscaled
  have htri (x y z : ℂ) : ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := by
    calc
      _ = ‖(x - y) + (y - z)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  exact (htri _ (zetaChiCanonicalSaddleCoefficient s n) _).trans
    (add_le_add hscaled
      (norm_zetaChiCanonicalSaddleCoefficient_sub_phase_le hs0 hs1 hn
        (by linarith) him hsize))

/-- Every eligible real-frequency dual atom has its full signed phase
`2*pi*exp(2*pi*i*x)`, with a uniform reciprocal-polynomial error on the disc. -/
theorem exists_zetaChi_real_dual_atom_disc_uniform
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∃ D : ℝ, 0 < D ∧ ∀ᶠ m : ℕ in atTop, ∀ s ∈ Metric.closedBall c r,
      ∀ n : ℝ, (m : ℝ) ^ 10 + (m : ℝ) ^ 6 ≤ 2 * Real.pi * n →
      2 * Real.pi * n + (m : ℝ) ^ 6 ≤ 2 * (m : ℝ) ^ 10 →
      ‖(∫ t in (m : ℝ) ^ 10..(2 * (m : ℝ) ^ 10),
          zetaChi (s + (t : ℂ) * I) * (n : ℂ) ^ (s - 1) *
            bourgainOscillation (t * Real.log n)) - ((2 * Real.pi : ℝ) : ℂ) * bourgainOscillation (2 * Real.pi * n)‖ ≤ D / m := by
  obtain ⟨C, hC, hbound⟩ := exists_zetaChi_real_dual_atom_disc_stationary c hr hc0 hc1
  let R : ℝ := ‖c - (1 / 2 : ℂ)‖ + r
  let J : ℝ := |c.im| + r
  let K : ℝ := 52 * R + 20 * R ^ 2
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  obtain ⟨M, hM⟩ := exists_nat_gt (8 + 2 * J + 26 * R + 10 * R ^ 2)
  refine ⟨648 * Real.pi * C + 2 * Real.pi * K, by positivity, ?_⟩
  have hp : Tendsto (fun m : ℕ => m ^ 10) atTop atTop := tendsto_pow_atTop (by decide)
  filter_upwards [hp.eventually hbound, eventually_ge_atTop M,
    eventually_ge_atTop (1 : ℕ)] with m hboundm hmM hm1
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hm0 : (0 : ℝ) < m := by linarith
  have hMR : (M : ℝ) ≤ m := by exact_mod_cast hmM
  have hmN : (m : ℝ) ≤ (m : ℝ) ^ 10 := by
    have h9 : (1 : ℝ) ≤ (m : ℝ) ^ 9 := one_le_pow₀ hmR
    nlinarith [mul_nonneg (sub_nonneg.mpr h9) hm0.le]
  have hhN : (m : ℝ) ^ 6 ≤ (m : ℝ) ^ 10 := by
    have h4 : (1 : ℝ) ≤ (m : ℝ) ^ 4 := one_le_pow₀ hmR
    nlinarith [mul_nonneg (sub_nonneg.mpr h4) (show 0 ≤ (m : ℝ) ^ 6 by positivity)]
  norm_num only [Nat.cast_pow] at hboundm
  intro s hs n hl hu
  have hre : |s.re - c.re| ≤ r := (by
    simpa only [Complex.sub_re, dist_eq_norm] using Complex.abs_re_le_norm (s - c) :
      |s.re - c.re| ≤ dist s c).trans hs
  have hs0 : 0 < s.re := by linarith [(abs_le.mp hre).1]
  have hsc : ‖s - c‖ ≤ r := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hs
  have hd : ‖s - (1 / 2 : ℂ)‖ ≤ R := by
    calc
      _ = ‖(s - c) + (c - (1 / 2 : ℂ))‖ := by congr 1; ring
      _ ≤ ‖s - c‖ + ‖c - (1 / 2 : ℂ)‖ := norm_add_le _ _
      _ ≤ R := by dsimp [R]; linarith
  have him : |s.im| ≤ J := by
    have he : s.im = (s - c).im + c.im := by simp
    rw [he]
    apply (abs_add_le _ _).trans
    calc
      _ ≤ r + |c.im| := add_le_add ((Complex.abs_im_le_norm (s - c)).trans hsc) le_rfl
      _ = J := by dsimp [J]; ring
  have hNpos : 0 < (m : ℝ) ^ 10 := by positivity
  have hm6 : 0 ≤ (m : ℝ) ^ 6 := by positivity
  have hnR : (0 : ℝ) < n := by nlinarith [Real.pi_pos]
  have hn : 0 < n := by exact_mod_cast hnR
  have hAlo : (m : ℝ) ^ 10 ≤ 2 * Real.pi * n := by linarith
  have hAup : 2 * Real.pi * n ≤ 2 * (m : ℝ) ^ 10 := by linarith
  have ha : 8 ≤ 2 * Real.pi * (n : ℝ) := by nlinarith
  have hsize : 26 * ‖s - (1 / 2 : ℂ)‖ + 10 * ‖s - (1 / 2 : ℂ)‖ ^ 2 ≤
      2 * Real.pi * n := by nlinarith [norm_nonneg (s - (1 / 2 : ℂ))]
  have hima : 2 * |s.im| ≤ 2 * Real.pi * n := by nlinarith
  have hb := hboundm s hs n ((m : ℝ) ^ 6) hn ha (by positivity)
    (by linarith) (by linarith) (by linarith) hu (by linarith) hima hsize
  have hcoef := norm_zetaChiDualRowCoefficient_saddle_le hs0.le
    (by positivity : 0 < (m : ℝ) ^ 10) hnR hAlo hAup
  have hmain : ‖zetaChiDualRowCoefficient s ((m : ℝ) ^ 10) n‖ *
      (C * (78 + 2 * ((m : ℝ) ^ 6) ^ 2 / (m : ℝ) ^ 10 +
        40 * (2 * Real.pi * n) ^ 2 / ((m : ℝ) ^ 10 * (m : ℝ) ^ 6) +
        4 * ((m : ℝ) ^ 6) ^ 4 / (2 * Real.pi * n) ^ 2 +
        40 * (2 * Real.pi * n) / (m : ℝ) ^ 6)) ≤ 648 * Real.pi * C / m :=
    (mul_le_mul_of_nonneg_right hcoef (by positivity)).trans
      (zetaChi_dual_stationary_remainder_le hmR hAlo hAup hC.le)
  have hKs : 52 * ‖s - (1 / 2 : ℂ)‖ + 20 * ‖s - (1 / 2 : ℂ)‖ ^ 2 ≤ K := by
    dsimp [K]
    nlinarith [norm_nonneg (s - (1 / 2 : ℂ))]
  have hshift : (52 * ‖s - (1 / 2 : ℂ)‖ + 20 * ‖s - (1 / 2 : ℂ)‖ ^ 2) / n ≤
      (2 * Real.pi * K) / m := by
    apply (div_le_div_of_nonneg_right hKs hnR.le).trans
    apply (div_le_div_iff₀ hnR hm0).mpr
    have hh := mul_le_mul_of_nonneg_left (hmN.trans hAlo) hK
    convert hh using 1; ring
  calc
    _ ≤ _ := hb
    _ ≤ 648 * Real.pi * C / m + (2 * Real.pi * K) / m := add_le_add hmain hshift
    _ = _ := by ring

end RHTower
