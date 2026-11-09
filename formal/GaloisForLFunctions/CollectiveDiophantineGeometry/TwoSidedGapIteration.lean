import GaloisForLFunctions.SurfaceOfSpecZ.TheGapMethodIterates

/-!+# Two-sided gap iteration

Absolute bounds on the cubic-spline trace at degrees with power-saving gaps
determine the zero width. At width `a`, interpolation costs `exp ((a + θ - 1)u)`;
the Laplace-transform rate theorem improves the width to `max σ (a + θ - 1)`.
Iteration reaches `σ`. The argument uses absolute convergence and analytic
continuation, with no one-sided Landau step or positivity of the Weil form.
-/

noncomputable section

namespace GaloisForLFunctions.CollectiveDiophantineGeometry

open Zeta23 ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri
  SquareRootThreshold SurfaceOfSpecZ

/-- The real cubic-spline trace at logarithmic degree `u`. -/
def splineTrace (u : ℝ) : ℝ :=
  2 * (lagStructure zetaZeroConfig (boxSpline 1 3) u).re

private theorem trace_rate_reads_width {b : ℝ} (hb : 0 ≤ b)
    (h : ∃ K : ℝ, ∀ u : ℝ, 0 ≤ u → |splineTrace u| ≤ K * Real.exp (b * u)) :
    zetaZeroWidth ≤ b := by
  apply (zeta_splineOrbit_rate_iff_zetaZeroWidth_le hb).mp
  obtain ⟨K, hK⟩ := h
  refine ⟨K, fun u hu => ?_⟩
  rw [orbitCorr_eq_re_lagStructure_spline]
  have ht := hK u hu
  simp only [splineTrace, abs_mul, abs_two] at ht
  linarith [abs_nonneg (lagStructure zetaZeroConfig (boxSpline 1 3) u).re]

/-- One absolute interpolation step improves `a` to `max σ (a + θ - 1)`. -/
theorem twoSided_width_step {a σ θ : ℝ} (ha : 0 ≤ a) (hσ : 0 ≤ σ)
    (hθ : θ < 1) (hw : zetaZeroWidth ≤ a) {D : Set ℕ} (hD : PowGaps θ D)
    {K : ℝ} (hK : ∀ d ∈ D, |splineTrace (Real.log d)| ≤ K * (d : ℝ) ^ σ) :
    zetaZeroWidth ≤ max σ (a + θ - 1) := by
  have hwid := (zetaZeroWidth_le_iff_re_le ha).mp hw
  obtain ⟨C, U, hC, hU, hnear⟩ :=
    exists_degree_trace_near temperedConfig_zetaZeroConfig ha hwid hθ hD
  let b := max σ (a + θ - 1)
  have hb : 0 ≤ b := hσ.trans (le_max_left _ _)
  let L := ∑' z : ℂ, ‖lagCoeff zetaZeroConfig (boxSpline 1 3) z‖ * ‖z‖
  have hL : 0 ≤ L := tsum_nonneg fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  let B := |splineTrace 0| + 2 * L * U * Real.exp (a * U)
  have hB : 0 ≤ B := add_nonneg (abs_nonneg _) (by positivity)
  have hsmall : ∀ u : ℝ, 0 ≤ u → u ≤ U → |splineTrace u| ≤ B := by
    intro u hu huU
    have hmove := abs_two_re_lagStructure_sub_le_of_width
      temperedConfig_zetaZeroConfig ha hwid (s := 0) le_rfl hu
    have hmul : 2 * L * u * Real.exp (a * u) ≤ 2 * L * U * Real.exp (a * U) :=
      mul_le_mul (mul_le_mul_of_nonneg_left huU (by positivity))
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left huU ha))
        (Real.exp_pos _).le (by positivity)
    have htri := abs_add_le (splineTrace u - splineTrace 0) (splineTrace 0)
    rw [sub_add_cancel] at htri
    change |splineTrace u - splineTrace 0| ≤
      2 * L * (u - 0) * Real.exp (a * u) at hmove
    dsimp only [B]
    linarith only [htri, hmove, hmul]
  apply trace_rate_reads_width hb
  refine ⟨|K| + C + B, fun u hu => ?_⟩
  have he : 1 ≤ Real.exp (b * u) := Real.one_le_exp (mul_nonneg hb hu)
  rcases le_total u U with huU | hUu
  · calc |splineTrace u| ≤ B := hsmall u hu huU
      _ ≤ B * Real.exp (b * u) := le_mul_of_one_le_right hB he
      _ ≤ (|K| + C + B) * Real.exp (b * u) :=
        mul_le_mul_of_nonneg_right (by linarith [abs_nonneg K]) (Real.exp_pos _).le
  · obtain ⟨d, hd, hdle, hmove⟩ := hnear u hUu
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hD.1 d hd
    have hdσ : (d : ℝ) ^ σ ≤ Real.exp (b * u) := by
      calc (d : ℝ) ^ σ ≤ (Real.exp u) ^ σ :=
          Real.rpow_le_rpow hd0.le hdle hσ
        _ = Real.exp (σ * u) := by rw [← Real.exp_mul, mul_comm]
        _ ≤ Real.exp (b * u) :=
          Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) hu)
    have hsample : |splineTrace (Real.log d)| ≤ |K| * Real.exp (b * u) :=
      (hK d hd).trans ((mul_le_mul_of_nonneg_right (le_abs_self K)
        (Real.rpow_nonneg hd0.le _)).trans
          (mul_le_mul_of_nonneg_left hdσ (abs_nonneg K)))
    have herror : C * Real.exp ((a + θ - 1) * u) ≤ C * Real.exp (b * u) :=
      mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) hu)) hC
    have htri := abs_add_le (splineTrace u - splineTrace (Real.log d))
      (splineTrace (Real.log d))
    rw [sub_add_cancel] at htri
    change |splineTrace u - splineTrace (Real.log d)| ≤
      C * Real.exp ((a + θ - 1) * u) at hmove
    have hreserve : 0 ≤ B * Real.exp (b * u) := mul_nonneg hB (Real.exp_pos _).le
    nlinarith only [htri, hmove, hsample, herror, hreserve]

/-- At any degree set with power-saving gaps, an absolute trace bound has
exactly the zero-width exponent. No sign hypothesis enters either direction. -/
theorem zeroWidth_iff_twoSided_powGaps {σ θ : ℝ} (hσ : 0 ≤ σ) (hθ : θ < 1)
    {D : Set ℕ} (hD : PowGaps θ D) :
    zetaZeroWidth ≤ σ ↔
      ∃ K : ℝ, ∀ d ∈ D, |splineTrace (Real.log d)| ≤ K * (d : ℝ) ^ σ := by
  constructor
  · intro hw
    obtain ⟨K, hK⟩ := (zeta_splineOrbit_rate_iff_zetaZeroWidth_le hσ).mpr hw
    refine ⟨2 * K, fun d hd => ?_⟩
    have ht := hK (Real.log d) (Real.log_natCast_nonneg d)
    rw [orbitCorr_eq_re_lagStructure_spline] at ht
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hD.1 d hd
    rw [show Real.exp (σ * Real.log d) = (d : ℝ) ^ σ by
      rw [Real.rpow_def_of_pos hd0, mul_comm]] at ht
    simp only [splineTrace, abs_mul, abs_two]
    linarith only [ht]
  · rintro ⟨K, hK⟩
    have hhalf : zetaZeroWidth ≤ 1 / 2 :=
      (zetaZeroWidth_le_iff_re_le (by norm_num)).mpr fun ρ hρ => by
        have hs := (zetaZeroConfig.strip ρ hρ).2
        linarith only [hs]
    have hstep : ∀ n : ℕ,
        zetaZeroWidth ≤ max σ (1 / 2 - n * (1 - θ)) := by
      intro n
      induction n with
      | zero => simpa only [Nat.cast_zero, zero_mul, sub_zero] using
          hhalf.trans (le_max_right σ (1 / 2))
      | succ n ih =>
        have hw := twoSided_width_step (hσ.trans (le_max_left _ _)) hσ hθ ih hD hK
        refine hw.trans ?_
        push_cast
        apply max_le (le_max_left _ _)
        rcases le_total σ (1 / 2 - n * (1 - θ)) with hn | hn
        · rw [max_eq_right hn]
          exact le_max_of_le_right (by linarith)
        · rw [max_eq_left hn]
          exact le_max_of_le_left (by linarith)
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / (2 * (1 - θ)))
    have hn' : 1 / 2 - n * (1 - θ) ≤ σ := by
      rw [div_lt_iff₀ (by linarith : 0 < 2 * (1 - θ))] at hn
      nlinarith only [hn, hσ]
    simpa only [max_eq_left hn'] using hstep n

/-- The two-sided prime-degree receiver, proved by absolute gap iteration. -/
theorem zeroWidth_iff_twoSided_primes {σ : ℝ} (hσ : 0 ≤ σ) :
    zetaZeroWidth ≤ σ ↔ ∃ K : ℝ, ∀ p : ℕ, p.Prime →
      |splineTrace (Real.log p)| ≤ K * (p : ℝ) ^ σ :=
  zeroWidth_iff_twoSided_powGaps hσ (by norm_num : (2 : ℝ) / 3 < 1)
    (powGaps_primes (by norm_num) (by norm_num))

/-- A bounded absolute trace at every prime degree is equivalent to RH. -/
theorem riemannHypothesis_iff_twoSided_primes :
    RiemannHypothesis ↔ ∃ K : ℝ, ∀ p : ℕ, p.Prime →
      |splineTrace (Real.log p)| ≤ K := by
  constructor
  · intro hRH
    have hw := (riemannHypothesis_iff_zetaZeroWidth_eq_zero.mp hRH).le
    simpa only [Real.rpow_zero, mul_one] using
      (zeroWidth_iff_twoSided_primes (σ := 0) le_rfl).mp hw
  · intro h
    have hw := (zeroWidth_iff_twoSided_primes (σ := 0) le_rfl).mpr
      (by simpa only [Real.rpow_zero, mul_one] using h)
    exact riemannHypothesis_iff_zetaZeroWidth_eq_zero.mpr
      (le_antisymm hw zetaZeroWidth_nonneg)

end GaloisForLFunctions.CollectiveDiophantineGeometry
