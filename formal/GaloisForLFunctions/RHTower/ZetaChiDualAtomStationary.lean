import GaloisForLFunctions.RHTower.ZetaChiCanonicalSaddleCoefficient
import GaloisForLFunctions.RHTower.CompactGaussianRowStationary

open Complex Set Filter Topology MeasureTheory
noncomputable section
namespace RHTower

/-- Coefficient which recovers the literal unweighted dual atom from the
normalized reflected compact row. -/
def zetaChiDualRowCoefficient (s : ℂ) (N x : ℝ) : ℂ :=
  (x : ℂ) ^ (s - 1) / ((Real.sqrt N : ℂ) * (N : ℂ) ^ (s - 1))

/-- Exact removal of the compact-row normalization. -/
theorem zetaChiDualRowCoefficient_mul_row (s : ℂ) {N : ℝ} (hN : 0 < N)
    (x t : ℝ) :
    zetaChiDualRowCoefficient s N x * reflectedCompactGaussianRow s N t =
      zetaChi (s + (t : ℂ) * I) * (x : ℂ) ^ (s - 1) := by
  have hp : (N : ℂ) ^ (s - 1) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr hN.ne'))
  have hs : (Real.sqrt N : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr hN)
  unfold zetaChiDualRowCoefficient reflectedCompactGaussianRow
  field_simp [hp, hs]

/-- The actual normalized-row saddle, with its literal dual coefficient,
is precisely the canonical saddle coefficient. -/
theorem zetaChiDualRowCoefficient_mul_saddle (s : ℂ) {N : ℝ} (hN : 0 < N)
    (x : ℝ) :
    zetaChiDualRowCoefficient s N x *
      (compactGaussianSlowRow s N (2 * Real.pi * x) *
        ((Real.sqrt (2 * Real.pi * (2 * Real.pi * x)) : ℂ) *
          bourgainOscillation (2 * Real.pi * x))) =
      zetaChiCanonicalSaddleCoefficient s x := by
  unfold compactGaussianSlowRow zetaChiCanonicalSaddleCoefficient
  rw [show zetaChiDualRowCoefficient s N x *
      (reflectedCompactGaussianRow s N (2 * Real.pi * x) /
        zetaChi (linePt (2 * Real.pi * x)) *
          ((Real.sqrt (2 * Real.pi * (2 * Real.pi * x)) : ℂ) *
            bourgainOscillation (2 * Real.pi * x))) =
      (zetaChiDualRowCoefficient s N x * reflectedCompactGaussianRow s N (2 * Real.pi * x)) /
        zetaChi (linePt (2 * Real.pi * x)) *
          ((Real.sqrt (2 * Real.pi * (2 * Real.pi * x)) : ℂ) *
            bourgainOscillation (2 * Real.pi * x)) by ring]
  rw [zetaChiDualRowCoefficient_mul_row s hN]
  ring

/-- Each literal unweighted dual atom has integer-saddle value `2*pi`.
The full row-stationary error and compact-shift error are both retained. -/
theorem exists_zetaChi_dual_atom_disc_stationary
    (c : ℂ) {r : ℝ} (hr : 0 ≤ r) (hc0 : 1 / 2 ≤ c.re - r) (hc1 : c.re + r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ s ∈ Metric.closedBall c r,
      ∀ (n : ℕ) (h : ℝ), 0 < n → 8 ≤ 2 * Real.pi * (n : ℝ) →
      0 < h → h ≤ (2 * Real.pi * n) / 2 →
      (2 * Real.pi * n) / 2 ≤ (N : ℝ) →
      (N : ℝ) ≤ 2 * Real.pi * n - h →
      2 * Real.pi * n + h ≤ 2 * N → 2 * (N : ℝ) ≤ 2 * (2 * Real.pi * n) →
      2 * |s.im| ≤ 2 * Real.pi * n →
      26 * ‖s - (1 / 2 : ℂ)‖ + 10 * ‖s - (1 / 2 : ℂ)‖ ^ 2 ≤ 2 * Real.pi * n →
      ‖(∫ t in (N : ℝ)..(2 * N),
          zetaChi (s + (t : ℂ) * I) * (n : ℂ) ^ (s - 1) *
            bourgainOscillation (t * Real.log n)) - ((2 * Real.pi : ℝ) : ℂ)‖ ≤
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
    norm_cast
  rw [intervalIntegral.integral_congr (fun t _ => heq t)] at hscaled
  have htri (x y z : ℂ) : ‖x - z‖ ≤ ‖x - y‖ + ‖y - z‖ := by
    calc
      _ = ‖(x - y) + (y - z)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  exact (htri _ (zetaChiCanonicalSaddleCoefficient s n) _).trans
    (add_le_add hscaled
      (norm_zetaChiCanonicalSaddleCoefficient_nat_sub_two_pi_le hs0 hs1 n hn
        (by linarith) him hsize))

end RHTower
