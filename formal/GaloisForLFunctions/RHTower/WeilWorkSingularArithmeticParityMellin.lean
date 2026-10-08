import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticPolynomialProfile
import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticMellin

/-!
# The actual parity-twisted Mellin transform

Convergence is proved from the full-positive source before identifying
the transform. No continuation or pole for the alternating series is assumed.
-/

open Complex MeasureTheory Set Filter Topology

noncomputable section

namespace RHTower.WeilSingularArithmetic

def sourceAlternatingCoeff (lam : ℕ → ℝ) (n : ℕ) : ℂ :=
  sourceSquareCoeff lam n * (-1 : ℂ) ^ n

def sourceAlternatingZetaSquare (lam : ℕ → ℝ) (s : ℂ) : ℂ :=
  LSeries (sourceAlternatingCoeff lam) s

@[simp] theorem norm_sourceAlternatingCoeff (lam : ℕ → ℝ) (n : ℕ) :
    ‖sourceAlternatingCoeff lam n‖ = ‖sourceSquareCoeff lam n‖ := by
  simp [sourceAlternatingCoeff]

@[simp] theorem sourceAlternatingCoeff_zero (lam : ℕ → ℝ) :
    sourceAlternatingCoeff lam 0 = 0 := by
  simp [sourceAlternatingCoeff]

theorem sourceAlternatingCoeff_summable {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (sourceAlternatingCoeff lam) s := by
  apply Summable.of_norm
  refine (sourceSquareCoeff_summable hW hs).norm.congr fun n => ?_
  simp only [LSeries.norm_term_eq, norm_sourceAlternatingCoeff]

private theorem hasSum_sourceAlternating_exponential {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℕ => sourceAlternatingCoeff lam n *
      (Real.exp (-Real.pi * (n : ℝ) ^ 2 * t) : ℂ))
      (sourceAlternatingGaussianProfile lam t) := by
  convert hasSum_sourceAlternatingGaussianProfile hW ht using 1
  ext n
  simp only [sourceAlternatingCoeff, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_neg, Complex.ofReal_one]
  ring

/-- The actual alternating Gaussian has an absolutely convergent Mellin integral. -/
theorem mellinConvergent_sourceAlternatingGaussianProfile {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {s : ℂ} (hs : 1 < s.re) :
    MellinConvergent (sourceAlternatingGaussianProfile lam) (s / 2) := by
  apply mellinConvergent_of_exponential_series
    (a := sourceAlternatingCoeff lam) (p := fun n => Real.pi * (n : ℝ) ^ 2)
  · intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Or.inl (sourceAlternatingCoeff_zero lam)
    · exact Or.inr (mul_pos Real.pi_pos (sq_pos_of_pos (by exact_mod_cast hn)))
  · rw [div_ofNat_re]
    linarith
  · intro t ht
    simpa only [neg_mul] using hasSum_sourceAlternating_exponential hW ht
  · refine ((source_norm_div_summable hW hs).div_const
      (Real.pi ^ (s.re / 2))).congr fun n => ?_
    rw [norm_sourceAlternatingCoeff, div_ofNat_re,
      Real.mul_rpow Real.pi_pos.le (sq_nonneg _),
      ← Real.rpow_natCast_mul (Nat.cast_nonneg n), Nat.cast_ofNat,
      mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)]
    ring

/-- The alternating series is a distinct actual Mellin transform, with no pole premise. -/
theorem mellin_sourceAlternatingGaussianProfile {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {s : ℂ} (hs : 1 < s.re) :
    mellin (sourceAlternatingGaussianProfile lam) (s / 2) =
      Gammaℝ s * sourceAlternatingZetaSquare lam s := by
  have hn : Summable (fun n : ℕ => ‖sourceAlternatingCoeff lam n‖ /
      |(n : ℝ)| ^ s.re) := by
    simpa only [Nat.abs_cast, norm_sourceAlternatingCoeff] using source_norm_div_summable hW hs
  have hF (t : ℝ) (ht : t ∈ Ioi 0) :
      HasSum (fun n : ℕ => if (n : ℝ) = 0 then 0 else sourceAlternatingCoeff lam n *
        (Real.exp (-Real.pi * (n : ℝ) ^ 2 * t) : ℂ))
        (sourceAlternatingGaussianProfile lam t) := by
    convert hasSum_sourceAlternating_exponential hW ht using 1
    ext n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · simp [hn.ne']
  have h := hasSum_mellin_pi_mul_sq (lt_trans (by norm_num) hs) hF hn
  have he (n : ℕ) : Gammaℝ s * sourceAlternatingCoeff lam n /
      ((|(n : ℝ)| : ℝ) : ℂ) ^ s =
      Gammaℝ s * LSeries.term (sourceAlternatingCoeff lam) s n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · simp [LSeries.term, hn.ne', Nat.abs_cast, mul_div_assoc]
  simp_rw [he] at h
  rw [← h.tsum_eq, tsum_mul_left]
  rfl

end RHTower.WeilSingularArithmetic
