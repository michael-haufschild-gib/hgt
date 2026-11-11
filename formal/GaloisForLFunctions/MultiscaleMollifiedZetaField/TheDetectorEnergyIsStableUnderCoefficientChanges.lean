import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheLowDetectorBlocksHaveASublinearHead
import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheFixedLinearMollifierChangesLittleAcrossTheGate

/-!
# Stability of detector energy under coefficient changes

Young's inequality separates a small coefficient discrepancy from the
matched detector. The Weyl head bound controls its energy on the entire
height interval. For the linear mollifier the discrepancy envelope is
`D exp D`, where `D` bounds the change of normalized displacement.
-/

open Complex MeasureTheory Set
open RHTower

noncomputable section

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

private theorem detector_energy_intervalIntegrable (N : ℕ) (b : ℕ → ℂ)
    (σ lam : ℝ) {a v : ℝ} (ha : 1 ≤ a) (hav : a ≤ v) :
    IntervalIntegrable (fun t : ℝ =>
      ‖levinsonMollifiedDetector (lam : ℂ) b (Finset.Icc 1 N)
        ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) volume a v := by
  apply ContinuousOn.intervalIntegrable
  intro t ht
  rw [uIcc_of_le hav] at ht
  have hz : ((σ : ℂ) + (t : ℂ) * I) ≠ 1 := by
    intro he
    have hh := congrArg Complex.im he
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add, Complex.one_im] at hh
    linarith only [hh, ht.1, ha]
  have hs : ∀ n ∈ Finset.Icc 1 N, 1 ≤ n := fun n hn => (Finset.mem_Icc.mp hn).1
  have hf := (analyticAt_levinsonMollifiedDetector (lam : ℂ) b hs hz).continuousAt
  have hmap : ContinuousAt (fun t : ℝ => (σ : ℂ) + (t : ℂ) * I) t := by fun_prop
  exact ((hf.comp hmap).norm.pow 2).continuousWithinAt

private theorem norm_sq_young (z w : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ‖z‖ ^ 2 ≤ (1 + ε) * ‖w‖ ^ 2 + (1 + 1 / ε) * ‖z - w‖ ^ 2 := by
  have ht : ‖z‖ ≤ ‖w‖ + ‖z - w‖ := by
    have hh := norm_add_le w (z - w)
    rw [show w + (z - w) = z by ring] at hh
    exact hh
  refine (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans ?_
  apply le_of_sub_nonneg
  have he : ε * ((1 + ε) * ‖w‖ ^ 2 + (1 + 1 / ε) * ‖z - w‖ ^ 2 -
      (‖w‖ + ‖z - w‖) ^ 2) = (ε * ‖w‖ - ‖z - w‖) ^ 2 := by
    field_simp [hε.ne'] <;> ring
  have hp : 0 ≤ ε * ((1 + ε) * ‖w‖ ^ 2 + (1 + 1 / ε) * ‖z - w‖ ^ 2 -
      (‖w‖ + ‖z - w‖) ^ 2) := by rw [he]; exact sq_nonneg _
  exact nonneg_of_mul_nonneg_left hp hε

private theorem detector_sub_coefficients (lam : ℂ) (b c : ℕ → ℂ) (N : ℕ) (s : ℂ) :
    levinsonMollifiedDetector lam b (Finset.Icc 1 N) s -
      levinsonMollifiedDetector lam c (Finset.Icc 1 N) s =
        levinsonMollifiedDetector lam (fun n => b n - c n) (Finset.Icc 1 N) s := by
  unfold levinsonMollifiedDetector edPoly
  simp only [sub_mul, Finset.sum_sub_distrib, mul_sub]

/-- A coefficient error envelope gives a global energy perturbation bound with arbitrary Young slack. -/
theorem exists_integral_detector_coefficient_stability :
    ∃ r > 0, r < 1 / 2 ∧ ∃ C > 0,
      ∀ (N : ℕ) (b c : ℕ → ℂ) (σ lam E ε a v A : ℝ),
      |σ - 1 / 2| ≤ r → |lam| ≤ 1 → 0 ≤ E → 0 < ε →
      (∀ n ∈ Finset.Icc 1 N, ‖b n - c n‖ ≤ E * (n : ℝ) ^ (σ - 1 / 2)) →
      1 ≤ a → a ≤ v → v ≤ A →
      (∫ t in a..v, ‖levinsonMollifiedDetector (lam : ℂ) b (Finset.Icc 1 N)
        ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
      (1 + ε) * (∫ t in a..v, ‖levinsonMollifiedDetector (lam : ℂ) c (Finset.Icc 1 N)
        ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) +
        (1 + 1 / ε) * (C * E ^ 2 * N * A ^ (11 / 8 : ℝ)) := by
  obtain ⟨r, hr, hrhalf, C, hC, hhead⟩ := exists_integral_linearDetector_head_bound
  refine ⟨r, hr, hrhalf, C, hC, ?_⟩
  intro N b c σ lam E ε a v A hσ hlam hE hε he ha hav hvA
  have hi := detector_energy_intervalIntegrable N b σ lam ha hav
  have hj := detector_energy_intervalIntegrable N c σ lam ha hav
  have hk := detector_energy_intervalIntegrable N (fun n => b n - c n) σ lam ha hav
  have hb := hhead N (fun n => b n - c n) σ lam E a v A hσ hlam hE he ha hav hvA
  calc
    _ ≤ ∫ t in a..v,
        (1 + ε) * ‖levinsonMollifiedDetector (lam : ℂ) c (Finset.Icc 1 N)
          ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 +
        (1 + 1 / ε) * ‖levinsonMollifiedDetector (lam : ℂ) (fun n => b n - c n)
          (Finset.Icc 1 N) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
      apply intervalIntegral.integral_mono_on hav hi ((hj.const_mul _).add (hk.const_mul _))
      intro t _
      simpa only [detector_sub_coefficients] using
        norm_sq_young
          (levinsonMollifiedDetector (lam : ℂ) b (Finset.Icc 1 N) ((σ : ℂ) + (t : ℂ) * I))
          (levinsonMollifiedDetector (lam : ℂ) c (Finset.Icc 1 N) ((σ : ℂ) + (t : ℂ) * I)) hε
    _ = (1 + ε) * (∫ t in a..v, ‖levinsonMollifiedDetector (lam : ℂ) c (Finset.Icc 1 N)
          ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) +
        (1 + 1 / ε) * (∫ t in a..v, ‖levinsonMollifiedDetector (lam : ℂ) (fun n => b n - c n)
          (Finset.Icc 1 N) ((σ : ℂ) + (t : ℂ) * I)‖ ^ 2) := by
      rw [intervalIntegral.integral_add (hj.const_mul _) (hk.const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hb (by positivity))

/-- The fixed linear mollifier satisfies the perturbation envelope at every point of its gate strip. -/
theorem fixedLinearMollifier_difference_envelope {N : ℕ} (hN : 1 < N)
    {d₀ d D : ℝ} (hd : d₀ ≤ d) (hD : (d - d₀) * Real.log N ≤ D) :
    ∀ n ∈ Finset.Icc 1 N,
      ‖(linearDetectorWeights N d₀ n : ℂ) - (linearDetectorWeights N d n : ℂ)‖ ≤
        (D * Real.exp D) * (n : ℝ) ^ ((1 / 2 - d) - 1 / 2) := by
  intro n hn
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    show (1 / 2 - d) - 1 / 2 = -d by ring]
  exact (linearDetectorWeights_fixed_envelopes hN hd hD n hn).2

end GaloisForLFunctions.MultiscaleMollifiedZetaField
