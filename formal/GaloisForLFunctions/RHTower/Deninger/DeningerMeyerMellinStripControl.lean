import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerMellinReconstruction
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerCausalDivision

/-!+# Uniform strip control from the actual logarithmic generator

Powers of the source generator supply all vertical moments. This upgrades
the existing fixed-line Fourier estimates to the strip-regular class used
by contour reconstruction.
-/

open Complex MeasureTheory Set
open GaloisForLFunctions.HTGeometry

namespace RHTower
noncomputable section

theorem deningerMeyerStrongLogMellin_strip_bound
    (g : DeningerMeyerStrongLogTarget) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖deningerMeyerStrongLogMellin g s‖ ≤ C := by
  let B := |a| + |b|
  let major := fun t : ℝ => Real.exp (B * |t|) * ‖g.val t‖
  have hint : Integrable major := by
    simpa [major] using integrable_deningerMeyerStrongLogAbsMoment g.property 0 B
  refine ⟨∫ t, major t, integral_nonneg (fun t => by positivity), ?_⟩
  intro s ha hb
  have hre : |s.re| ≤ B := by
    dsimp [B]
    rw [abs_le]
    constructor <;> linarith [le_abs_self a, neg_le_abs a, le_abs_self b,
      neg_le_abs b, abs_nonneg a, abs_nonneg b]
  apply norm_integral_le_of_norm_le hint
  filter_upwards with t
  rw [norm_deningerMeyerStrongLogMellinJet]
  simp only [pow_zero, one_mul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  calc s.re * t ≤ |s.re * t| := le_abs_self _
    _ = |s.re| * |t| := abs_mul _ _
    _ ≤ B * |t| := mul_le_mul_of_nonneg_right hre (abs_nonneg _)

theorem deningerMeyerStrongLogGenerator_pow_mellin
    (n : ℕ) (g : DeningerMeyerStrongLogTarget) (s : ℂ) :
    deningerMeyerStrongLogMellin ((deningerMeyerStrongLogGenerator ^ n) g) s =
      s^n * deningerMeyerStrongLogMellin g s := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, deningerMeyerStrongLogGenerator_mellin, ih]
      ring

theorem deningerMeyerStrongLogMellin_entireRegular
    (g : DeningerMeyerStrongLogTarget) :
    DeningerEntireMellinRegular (deningerMeyerStrongLogMellin g) := by
  intro α β
  refine ⟨fun s _ _ =>
    (analyticOnNhd_deningerMeyerStrongLogMellin g.property s (Set.mem_univ _)).differentiableAt,
    fun a b _ _ K => ?_⟩
  obtain ⟨C₀, hC₀, hb₀⟩ := deningerMeyerStrongLogMellin_strip_bound g a b
  obtain ⟨C₁, hC₁, hb₁⟩ := deningerMeyerStrongLogMellin_strip_bound
    ((deningerMeyerStrongLogGenerator ^ (2*K)) g) a b
  refine ⟨2^K * (C₀ + C₁), fun s ha hb => ?_⟩
  apply (le_div_iff₀ (by positivity : 0 < (1+s.im^2)^K)).mpr
  have h0 := hb₀ s ha hb
  have h1 := hb₁ s ha hb
  rw [deningerMeyerStrongLogGenerator_pow_mellin, norm_mul, norm_pow] at h1
  have him : s.im^2 ≤ ‖s‖^2 := by
    have h := pow_le_pow_left₀ (abs_nonneg s.im) (Complex.abs_im_le_norm s) 2
    simpa only [sq_abs] using h
  rcases le_total ‖s‖ 1 with hs | hs
  · have ht : 1 + s.im^2 ≤ 2 := by nlinarith [norm_nonneg s]
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1+s.im^2) ht K
    calc ‖deningerMeyerStrongLogMellin g s‖ * (1+s.im^2)^K
        ≤ C₀ * 2^K := mul_le_mul h0 hp (by positivity) hC₀
      _ ≤ 2^K * (C₀+C₁) := by nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) K]
  · have ht : 1 + s.im^2 ≤ 2 * ‖s‖^2 := by nlinarith
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1+s.im^2) ht K
    rw [mul_pow, ← pow_mul] at hp
    calc ‖deningerMeyerStrongLogMellin g s‖ * (1+s.im^2)^K
        ≤ ‖deningerMeyerStrongLogMellin g s‖ * (2^K * ‖s‖^(2*K)) :=
          mul_le_mul_of_nonneg_left hp (norm_nonneg _)
      _ = 2^K * (‖s‖^(2*K) * ‖deningerMeyerStrongLogMellin g s‖) := by ring
      _ ≤ 2^K * C₁ := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ 2^K * (C₀+C₁) := by nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) K]

end
end RHTower
