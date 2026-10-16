import GaloisForLFunctions.RHTower.DeningerMeyerStripJetLocalization
import GaloisForLFunctions.HTGeometry.EntireZeroFactorization

/-! # Full-multiplicity cardinal carriers in the original Mellin class

Dividing a strip-bounded entire denominator by one zero factor leaves a
strip-bounded entire multiplier. Original source jet interpolation then
isolates that node without disturbing any of the other full zero blocks.
-/

open Complex Filter Set Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower
noncomputable section

theorem DeningerEntireMellinRegular.weighted_strip_bound {F : ℂ → ℂ}
    (hF : DeningerEntireMellinRegular F) (r : ℝ) (K : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, |z.re| ≤ r →
      ‖F z‖*(1+z.im^2)^K ≤ C := by
  obtain ⟨C, hC⟩ := (hF (-r-1) (r+1)).decay (-r) r (by linarith) (by linarith) K
  refine ⟨max 1 C, lt_of_lt_of_le one_pos (le_max_left _ _), fun z hz => ?_⟩
  exact ((le_div_iff₀ (by positivity : 0 < (1+z.im^2)^K)).mp
    (hC z (abs_le.mp hz).1 (abs_le.mp hz).2)).trans (le_max_right _ _)

theorem deningerStripBounded_entire_factor {D G : ℂ → ℂ} (hG : Differentiable ℂ G)
    (hB : ∀ a b : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖D z‖ ≤ C)
    (w : ℂ) (m : ℕ) (hDG : ∀ z, D z = (z-w)^m*G z) :
    ∀ a b : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖G z‖ ≤ C := by
  intro a b
  obtain ⟨C, hC₀, hC⟩ := hB a b
  obtain ⟨B, hB⟩ := (isCompact_closedBall w 1).exists_bound_of_continuousOn
    hG.continuous.continuousOn
  refine ⟨max C B, hC₀.trans (le_max_left _ _), fun z hza hzb => ?_⟩
  by_cases hz : ‖z-w‖ ≤ 1
  · exact (hB z (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz)).trans
      (le_max_right _ _)
  · have hp : 1 ≤ ‖z-w‖^m := one_le_pow₀ (le_of_lt (lt_of_not_ge hz))
    calc ‖G z‖ ≤ ‖z-w‖^m*‖G z‖ := by nlinarith [norm_nonneg (G z)]
      _ = ‖D z‖ := by rw [hDG z, norm_mul, norm_pow]
      _ ≤ C := hC z hza hzb
      _ ≤ max C B := le_max_left _ _

/-- A cardinal carrier retains an arbitrary germ at one node and the full
denominator order at every other node. -/
theorem exists_deningerMeyerStripCardinal {D f : ℂ → ℂ}
    (hD : Differentiable ℂ D)
    (hB : ∀ a b : ℝ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖D z‖ ≤ C)
    {w : ℂ} {m : ℕ} (hm : analyticOrderAt D w = (m : ℕ∞))
    (hf : AnalyticAt ℂ f w) :
    ∃ F : ℂ → ℂ, DeningerEntireMellinRegular F ∧
      (m : ℕ∞) ≤ analyticOrderAt (fun z => F z-f z) w ∧
      ∀ z, z ≠ w → analyticOrderAt D z ≤ analyticOrderAt F z := by
  obtain ⟨G, hG, hGw, hDG⟩ := exists_entire_factor_of_analyticOrder hD hm
  have hGA : ∀ z, AnalyticAt ℂ G z := fun z =>
    hG.differentiableOn.analyticAt univ_mem
  obtain ⟨H, hH, hHgerm⟩ := exists_deningerMeyerMellin_finiteGerm
    (hf.div (hGA w) hGw) m
  have hHA : ∀ z, AnalyticAt ℂ H z := fun z =>
    hH.differentiable.differentiableOn.analyticAt univ_mem
  refine ⟨fun z => H z*G z,
    hH.mul_of_strip_bounded hG (deningerStripBounded_entire_factor hG hB w m hDG), ?_, ?_⟩
  · have he : (fun z => H z*G z-f z) =ᶠ[𝓝 w]
        (fun z => (H z-f z/G z)*G z) := by
      filter_upwards [hG.continuous.continuousAt.eventually_ne hGw] with z hz
      field_simp
    rw [analyticOrderAt_congr he]
    change (m : ℕ∞) ≤ analyticOrderAt ((H-f/G)*G) w
    rw [analyticOrderAt_mul ((hHA w).sub (hf.div (hGA w) hGw)) (hGA w)]
    exact hHgerm.trans (le_add_of_nonneg_right bot_le)
  · intro z hz
    have hfactor : D = (fun z => (z-w)^m)*G := funext hDG
    rw [hfactor, analyticOrderAt_mul (analyticAt_sub_pow w m z) (hGA z),
      analyticOrderAt_sub_pow_of_ne w m hz, zero_add]
    change analyticOrderAt G z ≤ analyticOrderAt (H*G) z
    rw [analyticOrderAt_mul (hHA z) (hGA z)]
    exact le_add_of_nonneg_left bot_le

/-- Localization preserves the designated germ and all other vanishing
orders, while paying a chosen weighted strip seminorm. -/
theorem exists_deningerMeyerStripSmallCarrier {F : ℂ → ℂ}
    (hF : DeningerEntireMellinRegular F) (w : ℂ) (m K : ℕ)
    {r ε : ℝ} (hw : r < |w.re|) (hε : 0 < ε) :
    ∃ G : ℂ → ℂ, DeningerEntireMellinRegular G ∧
      (m : ℕ∞) ≤ analyticOrderAt (fun z => G z-F z) w ∧
      (∀ z, analyticOrderAt F z ≤ analyticOrderAt G z) ∧
      ∀ z : ℂ, |z.re| ≤ r → ‖G z‖*(1+z.im^2)^K ≤ ε := by
  obtain ⟨C, hC, hb⟩ := hF.weighted_strip_bound r K
  obtain ⟨L, hL, hLB, hLgerm, hsmall⟩ := exists_deningerMeyerJetLocalizer w m hw
    (show 0 < ε/C by positivity)
  have hFA : ∀ z, AnalyticAt ℂ F z := fun z =>
    hF.differentiable.differentiableOn.analyticAt univ_mem
  have hLA : ∀ z, AnalyticAt ℂ L z := fun z => hL.differentiableOn.analyticAt univ_mem
  refine ⟨fun z => F z*L z, hF.mul_of_strip_bounded hL hLB, ?_, ?_, ?_⟩
  · have he : (fun z => F z*L z-F z) = F*(L-1) := by funext z; simp; ring
    have hL1 : AnalyticAt ℂ (L-1) w := by
      change AnalyticAt ℂ (fun z => L z-1) w
      exact (hLA w).sub analyticAt_const
    rw [he, analyticOrderAt_mul (hFA w) hL1]
    exact hLgerm.trans (le_add_of_nonneg_left bot_le)
  · intro z
    change analyticOrderAt F z ≤ analyticOrderAt (F*L) z
    rw [analyticOrderAt_mul (hFA z) (hLA z)]
    exact le_add_of_nonneg_right bot_le
  · intro z hz
    rw [norm_mul]
    calc ‖F z‖*‖L z‖*(1+z.im^2)^K =
        (‖F z‖*(1+z.im^2)^K)*‖L z‖ := by ring
      _ ≤ C*(ε/C) := mul_le_mul (hb z hz) (hsmall z hz) (norm_nonneg _) hC.le
      _ = ε := mul_div_cancel₀ _ hC.ne'

end
end RHTower
