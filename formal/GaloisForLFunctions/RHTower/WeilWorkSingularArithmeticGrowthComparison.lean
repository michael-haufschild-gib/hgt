import GaloisForLFunctions.RHTower.WeilProducerReciprocalZeta

/-!
# Actual zeta-quotient growth agrees with zeta up to subpowers

The existing producer Lindelöf theorem is two-sided. Analytic uniqueness
identifies its local reciprocal with the same global literal reciprocal.
Consequently the actual quotient cannot cancel any fixed power of height
from zeta's growth. No zero-free or Lindelöf premise for zeta is used.
-/

open Complex Set Metric

noncomputable section

namespace RHTower.WeilSingularArithmetic

/-- On every strict inner strip, the literal zeta quotient and zeta itself
have the same height growth up to arbitrary positive powers. All inputs
come from full Weil positivity. The comparison also holds at zeta zeros. -/
theorem exists_actual_quotient_growth_comparison {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G {s : ℂ | 1 / 2 < s.re} ∧
      (∀ s : ℂ, 1 < s.re →
        G s = cexp (-LSeries (logZetaCoeff (fun n => if 2 ≤ n then lam n else 0)) s)) ∧
      ∀ δ : ℝ, 0 < δ → δ < 1 / 2 → ∀ ε : ℝ, 0 < ε →
        ∃ T : ℝ, ∀ t : ℝ, T ≤ |t| → ∀ σ : ℝ, 1 / 2 + δ ≤ σ → σ ≤ 5 / 2 →
          (|t| + 3) ^ (-ε) * ‖riemannZeta ((σ : ℂ) + t * I)‖ ≤
            ‖riemannZeta ((σ : ℂ) + t * I) * G ((σ : ℂ) + t * I)‖ ∧
          ‖riemannZeta ((σ : ℂ) + t * I) * G ((σ : ℂ) + t * I)‖ ≤
            (|t| + 3) ^ ε * ‖riemannZeta ((σ : ℂ) + t * I)‖ := by
  let lam' : ℕ → ℝ := fun n => if 2 ≤ n then lam n else 0
  have hH := WeilSpectral.herglotzWeilPositive_of_weilPositiveFull hW
  have hA : DifferentiableOn ℂ zetaArchimedeanDatum {s : ℂ | 1 / 2 < s.re} :=
    differentiableOn_zetaArchimedeanDatum.mono fun s (hs : 1 / 2 < s.re) =>
      show 0 < s.re by linarith
  obtain ⟨G, hGd, hGL⟩ := exists_reciprocalZeta_continuation hH
    (by simp [lam'] : lam' 1 = 0) hA
  refine ⟨G, hGd, hGL, fun δ hδ hδ1 ε hε => ?_⟩
  obtain ⟨T, hT⟩ := exists_producerZeta_subpolynomial_of_weilPositiveFull hW hδ hδ1 hε
  refine ⟨T, fun t ht σ hσ hσ2 => ?_⟩
  obtain ⟨g, hgd, hgL, hbd⟩ := hT t ht
  have hR : (0 : ℝ) < 5 / 2 - δ / 4 := by linarith
  have hcre : 1 < ((3 : ℂ) + t * I).re := by simp
  have hsub : ball ((3 : ℂ) + t * I) (5 / 2 - δ / 4) ⊆ {s : ℂ | 1 / 2 < s.re} := by
    intro w hw
    rw [mem_ball_iff_norm] at hw
    have h := Complex.abs_re_le_norm (w - ((3 : ℂ) + t * I))
    have hre3 : ((3 : ℂ) + t * I).re = 3 := by simp
    rw [Complex.sub_re, hre3] at h
    have := neg_abs_le (w.re - 3)
    show 1 / 2 < w.re
    linarith
  have heq := eqOn_exp_neg_of_agree hR hcre (hGd.mono hsub) hgd
    (fun s _ hs => hGL s hs) hgL
  have hmem : (σ : ℂ) + t * I ∈ ball ((3 : ℂ) + t * I) (5 / 2 - δ / 4) := by
    rw [mem_ball_iff_norm, norm_vertical_sub_center σ t (by linarith)]
    linarith
  obtain ⟨hlow, hhigh⟩ := hbd σ hσ hσ2
  have hB : 0 < (|t| + 3) ^ ε := Real.rpow_pos_of_pos (by positivity) _
  have hF : 0 < ‖cexp (g ((σ : ℂ) + t * I))‖ :=
    norm_pos_iff.mpr (Complex.exp_ne_zero _)
  have hGN : ‖G ((σ : ℂ) + t * I)‖ = ‖cexp (g ((σ : ℂ) + t * I))‖⁻¹ := by
    rw [heq hmem]
    exact congrArg norm (Complex.exp_neg _) |>.trans (norm_inv _)
  have hGlo : (|t| + 3) ^ (-ε) ≤ ‖G ((σ : ℂ) + t * I)‖ := by
    rw [hGN, Real.rpow_neg (by positivity)]
    exact (inv_le_inv₀ hB hF).mpr hhigh
  have hGhi : ‖G ((σ : ℂ) + t * I)‖ ≤ (|t| + 3) ^ ε := by
    rw [hGN]
    apply (inv_le_comm₀ hF hB).mpr
    simpa only [Real.rpow_neg (le_of_lt (show 0 < |t| + 3 by positivity))] using hlow
  rw [norm_mul]
  constructor
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_left hGlo
      (norm_nonneg (riemannZeta ((σ : ℂ) + t * I)))
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_left hGhi
      (norm_nonneg (riemannZeta ((σ : ℂ) + t * I)))

end RHTower.WeilSingularArithmetic
