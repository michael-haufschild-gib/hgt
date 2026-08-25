import GaloisForLFunctions.HTGeometry.DigammaSectorBounds

/-!
# Uniform linear digamma growth on compact positive strips

One recurrence moves every positive-strip point into the shifted Watson
sector.  The sector estimate and a uniform reciprocal bound then give one
linear vertical envelope across the whole compact strip.
-/

noncomputable section

open Complex

namespace GaloisForLFunctions.HTGeometry

theorem exists_norm_digamma_positive_strip_le
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (σ : ℝ), a ≤ σ → σ ≤ b → ∀ t : ℝ,
      ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        K * (1 + |t|) := by
  obtain ⟨C, hC, hsector⟩ := exists_norm_digamma_halfShift_le
  let B : ℝ := 2 * b + 4
  let K : ℝ := C * B + 1 / a
  have hb0 : 0 < b := ha.trans_le hab
  have hB : 0 ≤ B := by dsimp only [B]; linarith
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, hK, fun σ haσ hσb t => ?_⟩
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  let z : ℂ := ((2 * σ + 1 : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I
  have hzmem : z ∈ digammaWatsonSector := by
    change -(‖z‖ / 2) ≤ z.re
    have hzre : z.re = 2 * σ + 1 := by simp [z]
    rw [hzre]
    have : 0 ≤ ‖z‖ := norm_nonneg z
    linarith
  have hshift : (1 + z) / 2 = s + 1 := by
    dsimp only [s, z]
    push_cast
    ring
  have hznorm : ‖z‖ ≤ (2 * b + 1) + 2 * |t| := by
    have hre0 : 0 ≤ 2 * σ + 1 := by linarith
    calc
      ‖z‖ ≤ ‖(((2 * σ + 1 : ℝ) : ℂ))‖ +
          ‖(((2 * t : ℝ) : ℂ) * I)‖ := by
        dsimp only [z]
        exact norm_add_le _ _
      _ = (2 * σ + 1) + 2 * |t| := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hre0,
          norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_I, mul_one,
          abs_mul]
        norm_num
      _ ≤ (2 * b + 1) + 2 * |t| := by linarith
  have hlinear : 1 + ‖z‖ ≤ B * (1 + |t|) := by
    dsimp only [B]
    nlinarith [abs_nonneg t]
  have hshiftBound : ‖Complex.digamma (s + 1)‖ ≤
      C * B * (1 + |t|) := by
    rw [← hshift]
    exact (hsector z hzmem).trans
      (by
        calc
          C * (1 + ‖z‖) ≤ C * (B * (1 + |t|)) :=
            mul_le_mul_of_nonneg_left hlinear hC
          _ = C * B * (1 + |t|) := by ring)
  have hsre : s.re = σ := by simp [s]
  have hsne : ∀ m : ℕ, s ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    rw [hsre, Complex.neg_re, Complex.natCast_re] at hre
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hrec := Complex.digamma_apply_add_one s hsne
  have hsinv : ‖s⁻¹‖ ≤ 1 / a := by
    rw [norm_inv]
    have hsnorm : a ≤ ‖s‖ := by
      calc
        a ≤ σ := haσ
        _ = |s.re| := by rw [hsre, abs_of_pos (ha.trans_le haσ)]
        _ ≤ ‖s‖ := Complex.abs_re_le_norm s
    simpa [one_div] using one_div_le_one_div_of_le ha hsnorm
  have hsplit : Complex.digamma s = Complex.digamma (s + 1) - s⁻¹ := by
    rw [hrec]
    ring
  change ‖Complex.digamma s‖ ≤ K * (1 + |t|)
  rw [hsplit]
  refine (norm_sub_le _ _).trans ?_
  calc
    ‖Complex.digamma (s + 1)‖ + ‖s⁻¹‖
        ≤ C * B * (1 + |t|) + 1 / a :=
      add_le_add hshiftBound hsinv
    _ ≤ (C * B + 1 / a) * (1 + |t|) := by
      have ht : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
      nlinarith [mul_nonneg (by positivity : 0 ≤ 1 / a) (sub_nonneg.mpr ht)]
    _ = K * (1 + |t|) := by rfl

end GaloisForLFunctions.HTGeometry
