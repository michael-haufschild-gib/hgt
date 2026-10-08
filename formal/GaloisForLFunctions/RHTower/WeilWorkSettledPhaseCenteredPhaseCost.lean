import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseCenteredContour

/-!
# The actual Gaussian phase cost equals twice centered energy up to a sublinear error

Pole-centered Mellin cancellation and the universal kernel error evaluate the
signed centered contour. Combining its value with the zero-safe reflection
identity gives a quantitative relation for the original full-positive source.
Neither side's positive energy is presumed small.
-/

open Complex Set Filter MeasureTheory Topology
noncomputable section
namespace RHTower.WeilWorkSettledPhase
open WeilSpectral GaussZeroSum
variable {lam : ℕ → ℝ}

def centeredGaussianSum (hW : WeilPositiveFull lam) (T : ℝ) : ℂ :=
  ∑' n : ℕ, centeredSquareCoeff hW n * (gaussW T n : ℂ)

theorem summable_centeredGaussianSum (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 0 < T) :
    Summable (fun n : ℕ => centeredSquareCoeff hW n * (gaussW T n : ℂ)) := by
  let c := centeredSquareCoeff hW
  let w (n : ℕ) := ‖LSeries.term c (2 : ℂ) n‖
  have hw : Summable w := (centeredSquareCoeff_summable hW (s := 2) (by norm_num)).norm
  have hb (n : ℕ) : ‖c n * (gaussW T n : ℂ)‖ ≤ w n * T ^ 2 := by
    by_cases hn : n = 0
    · simp [hn, c, w]
    have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have he : w n = ‖c n‖ / (n : ℝ) ^ 2 := by
      simp only [w, LSeries.norm_term_eq, if_neg hn, Complex.re_ofNat, Real.rpow_two]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gaussW_pos T n), he]
    calc
      _ ≤ ‖c n‖ * (T ^ 2 / (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (gaussW_le_sq_div hT hn0) (norm_nonneg _)
      _ = _ := by ring
  exact (Summable.of_nonneg_of_le (fun n => norm_nonneg _) hb (hw.mul_right _)).of_norm

/-- The universal Gaussian kernel error is summable against the actual square. -/
theorem centeredGaussian_kernel_error (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      Summable (fun n : ℕ => centeredSquareCoeff hW n *
        ((leftKernel T n - 2 * gaussW T n : ℝ) : ℂ)) ∧
      ‖∑' n : ℕ, centeredSquareCoeff hW n *
        ((leftKernel T n - 2 * gaussW T n : ℝ) : ℂ)‖ ≤ C * T ^ (5 / 6 : ℝ) := by
  obtain ⟨K, hK, hb⟩ := WeilSingularArithmetic.exists_weighted_gaussian_kernel_error_le
  let c := centeredSquareCoeff hW
  let w (n : ℕ) := ‖LSeries.term c ((9 / 8 : ℝ) : ℂ) n‖
  have hw : Summable w :=
    (centeredSquareCoeff_summable hW (s := ((9 / 8 : ℝ) : ℂ)) (by norm_num)).norm
  refine ⟨K * ∑' n, w n, by positivity, ?_⟩
  intro T hT
  let e (n : ℕ) := c n * ((leftKernel T n - 2 * gaussW T n : ℝ) : ℂ)
  have hmajor (n : ℕ) : ‖e n‖ ≤ w n * (K * T ^ (5 / 6 : ℝ)) := by
    by_cases hn : n = 0
    · simp [hn, e, c, w]
    have hn0 : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hnp : 0 < (n : ℝ) ^ (9 / 8 : ℝ) := Real.rpow_pos_of_pos hn0 _
    have he : w n = ‖c n‖ / (n : ℝ) ^ (9 / 8 : ℝ) := by
      simp only [w, LSeries.norm_term_eq, if_neg hn, Complex.ofReal_re]
    change ‖c n * ((leftKernel T n - 2 * gaussW T n : ℝ) : ℂ)‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, he]
    calc
      _ = (‖c n‖ / (n : ℝ) ^ (9 / 8 : ℝ)) *
          ((n : ℝ) ^ (9 / 8 : ℝ) * |leftKernel T n - 2 * gaussW T n|) := by
        field_simp [hnp.ne']
      _ ≤ _ := mul_le_mul_of_nonneg_left (hb T hT n (Nat.pos_of_ne_zero hn)) (by positivity)
  have hs : Summable (fun n => ‖e n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hmajor (hw.mul_right _)
  refine ⟨hs.of_norm, (norm_tsum_le_tsum_norm hs).trans ?_⟩
  calc
    _ ≤ ∑' n, w n * (K * T ^ (5 / 6 : ℝ)) := hs.tsum_le_tsum hmajor (hw.mul_right _)
    _ = (K * ∑' n, w n) * T ^ (5 / 6 : ℝ) := by rw [tsum_mul_right]; ring

/-- Quantitative extraction uses only full Weil positivity of the source. -/
theorem centeredGaussian_signed_extraction (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      ‖(∫ t : ℝ, centeredGaussianSignedTrace hW T t) -
        4 * Real.pi * centeredGaussianSum hW T‖ ≤ C * T ^ (5 / 6 : ℝ) := by
  obtain ⟨K, hK, hb⟩ := centeredGaussian_kernel_error hW
  refine ⟨(2 * Real.pi) * K, by positivity, ?_⟩
  intro T hT
  have hg := summable_centeredGaussianSum hW (lt_of_lt_of_le zero_lt_one hT)
  have he := (hb T hT).1
  have hk : Summable (fun n : ℕ => centeredSquareCoeff hW n * (leftKernel T n : ℂ)) := by
    convert he.add (hg.mul_left 2) using 1
    ext n
    push_cast
    ring
  have heq : (∑' n : ℕ, centeredSquareCoeff hW n *
      ((leftKernel T n - 2 * gaussW T n : ℝ) : ℂ)) =
      (∑' n : ℕ, centeredSquareCoeff hW n * (leftKernel T n : ℂ)) -
        2 * centeredGaussianSum hW T := by
    unfold centeredGaussianSum
    rw [← tsum_mul_left]
    rw [← hk.tsum_sub (hg.mul_left 2)]
    apply tsum_congr
    intro n
    push_cast
    ring
  rw [centeredGaussianSignedTrace_eq_kernelSum hW hT]
  have halg : (2 : ℂ) * Real.pi *
      (∑' n : ℕ, centeredSquareCoeff hW n * (leftKernel T n : ℂ)) -
        4 * Real.pi * centeredGaussianSum hW T =
      (2 * Real.pi : ℂ) * (∑' n : ℕ, centeredSquareCoeff hW n *
        ((leftKernel T n - 2 * gaussW T n : ℝ) : ℂ)) := by rw [heq]; ring
  rw [halg, norm_mul]
  have hnorm : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  rw [hnorm]
  calc
    _ ≤ (2 * Real.pi) * (K * T ^ (5 / 6 : ℝ)) :=
      mul_le_mul_of_nonneg_left (hb T hT).2 (by positivity)
    _ = _ := by ring

/-- The whole signed centered moment has an unconditional sublinear power bound. -/
theorem exists_centeredGaussianSignedTrace_integral_le (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      ‖∫ t : ℝ, centeredGaussianSignedTrace hW T t‖ ≤ C * T ^ (5 / 6 : ℝ) := by
  obtain ⟨A, hA, hS⟩ := exists_centeredGaussianSum_le hW (c := 3 / 4) (by norm_num) (by norm_num)
  obtain ⟨K, hK, hJ⟩ := centeredGaussian_signed_extraction hW
  refine ⟨K + (4 * Real.pi) * A, by positivity, fun T hT => ?_⟩
  have hnorm : ‖(4 * Real.pi : ℂ)‖ = 4 * Real.pi := by
    rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos]
  have hS' : ‖centeredGaussianSum hW T‖ ≤ A * T ^ (5 / 6 : ℝ) :=
    (hS T hT).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT (by norm_num)) hA)
  calc
    _ = ‖((∫ t : ℝ, centeredGaussianSignedTrace hW T t) -
          4 * Real.pi * centeredGaussianSum hW T) +
          4 * Real.pi * centeredGaussianSum hW T‖ := by rw [sub_add_cancel]
    _ ≤ ‖(∫ t : ℝ, centeredGaussianSignedTrace hW T t) -
          4 * Real.pi * centeredGaussianSum hW T‖ +
          ‖4 * Real.pi * centeredGaussianSum hW T‖ := norm_add_le _ _
    _ ≤ K * T ^ (5 / 6 : ℝ) + (4 * Real.pi) * (A * T ^ (5 / 6 : ℝ)) := by
      rw [norm_mul, hnorm]
      gcongr
      exact hJ T hT
    _ = _ := by ring

/-- C58: centering identifies the literal phase cost with the full arithmetic energy. -/
theorem exists_gaussianPhaseCost_centeredEnergy_error (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T →
      |quantizationGaussianDefect hW T - 2 * quantizationCenteredGaussianEnergy hW T| ≤
        C * T ^ (5 / 6 : ℝ) := by
  obtain ⟨C, hC, hb⟩ := exists_centeredGaussianSignedTrace_integral_le hW
  refine ⟨C, hC, fun T hT => ?_⟩
  have he := centeredGaussian_signed_energy hW (lt_of_lt_of_le zero_lt_one hT)
  rw [abs_sub_comm, ← he]
  exact (Complex.abs_re_le_norm _).trans (hb T hT)

end RHTower.WeilWorkSettledPhase
