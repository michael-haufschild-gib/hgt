import Mathlib
import GaloisForLFunctions.HTGeometry.CarrierDichotomy

/-!
# Even + periodic + flank-bounded ⟹ constant

The Liouville finish shared by the reflection-rigidity cards.  An even entire function that is
invariant under a nonzero real period and bounded on the lower flank `Im z ≤ -w` is constant:
evenness reflects the flank bound onto the upper flank, periodicity folds the intervening strip
into one compact fundamental cell on which the continuous function is bounded, the three regions
cover the plane, and Liouville closes the argument.
-/

open Complex Filter Topology

noncomputable section

namespace RHTower

/-- **Even periodic flank rigidity.**  An even entire `G` that is `P`-periodic for a positive real
period `P` and bounded by `B` on the lower flank `Im z ≤ -w` is constant.  No sign condition on
the flank parameter `w` is needed. -/
theorem even_periodic_flankBounded_const {G : ℂ → ℂ} {pR w B : ℝ}
    (hpRpos : 0 < pR) (hG : Differentiable ℂ G)
    (hsym : ∀ z : ℂ, G z = G (-z))
    (hper : Function.Periodic G (pR : ℂ))
    (hflank : ∀ z : ℂ, z.im ≤ -w → ‖G z‖ ≤ B) :
    ∀ s t : ℂ, G s = G t := by
  -- Boundedness on the compact fundamental cell `[0, pR] × [-w, w]`.
  have hKcompact : IsCompact
      ((fun q : ℝ × ℝ => (q.1 : ℂ) + (q.2 : ℂ) * Complex.I) ''
        (Set.Icc 0 pR ×ˢ Set.Icc (-w) w)) :=
    (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  obtain ⟨B₁, hB₁⟩ := hKcompact.exists_bound_of_continuousOn hG.continuous.continuousOn
  -- Boundedness on the whole strip `-w ≤ Im z ≤ w`, transported through the cell by periodicity.
  have hstrip : ∀ (z : ℂ), -w ≤ z.im → z.im ≤ w → ‖G z‖ ≤ B₁ := by
    intro z hlo hhi
    set n : ℤ := ⌊z.re / pR⌋ with hn
    have hfloor_le : (↑n : ℝ) ≤ z.re / pR := by rw [hn]; exact Int.floor_le _
    have hlt_floor : z.re / pR < ↑n + 1 := by rw [hn]; exact Int.lt_floor_add_one _
    have hn_le : (↑n : ℝ) * pR ≤ z.re := by
      have h := mul_le_mul_of_nonneg_right hfloor_le hpRpos.le
      rwa [div_mul_cancel₀ z.re hpRpos.ne'] at h
    have hlt : z.re < (↑n : ℝ) * pR + pR := by
      have h := mul_lt_mul_of_pos_right hlt_floor hpRpos
      rwa [div_mul_cancel₀ z.re hpRpos.ne', add_mul, one_mul] at h
    have hnP : (↑n : ℂ) * (pR : ℂ) = (((↑n : ℝ) * pR : ℝ) : ℂ) := by push_cast; ring
    have hz're : (z - (↑n : ℂ) * (pR : ℂ)).re = z.re - (↑n : ℝ) * pR := by
      rw [hnP, Complex.sub_re, Complex.ofReal_re]
    have hz'im : (z - (↑n : ℂ) * (pR : ℂ)).im = z.im := by
      rw [hnP, Complex.sub_im, Complex.ofReal_im, sub_zero]
    have hre_mem : (z - (↑n : ℂ) * (pR : ℂ)).re ∈ Set.Icc (0 : ℝ) pR := by
      rw [hz're]; exact ⟨by linarith, by linarith⟩
    have him_mem : (z - (↑n : ℂ) * (pR : ℂ)).im ∈ Set.Icc (-w) w := by
      rw [hz'im]; exact ⟨hlo, hhi⟩
    have hmem : (z - (↑n : ℂ) * (pR : ℂ)) ∈
        (fun q : ℝ × ℝ => (q.1 : ℂ) + (q.2 : ℂ) * Complex.I) ''
          (Set.Icc 0 pR ×ˢ Set.Icc (-w) w) :=
      ⟨((z - (↑n : ℂ) * (pR : ℂ)).re, (z - (↑n : ℂ) * (pR : ℂ)).im), ⟨hre_mem, him_mem⟩,
        Complex.re_add_im (z - (↑n : ℂ) * (pR : ℂ))⟩
    calc ‖G z‖ = ‖G (z - (↑n : ℂ) * (pR : ℂ))‖ := by rw [hper.sub_int_mul_eq n]
      _ ≤ B₁ := hB₁ _ hmem
  -- Global bound on the three covering regions; Liouville forces constancy.
  have hglobal : ∀ z : ℂ, ‖G z‖ ≤ max B B₁ := by
    intro z
    rcases le_or_gt z.im (-w) with h | h
    · exact le_trans (hflank z h) (le_max_left _ _)
    · rcases le_or_gt w z.im with h2 | h2
      · rw [hsym z]
        refine le_trans (hflank (-z) ?_) (le_max_left _ _)
        rw [Complex.neg_im]; linarith
      · exact le_trans (hstrip z (le_of_lt h) (le_of_lt h2)) (le_max_right _ _)
  exact GaloisForLFunctions.bounded_entire_symbol_const G hG ⟨max B B₁, hglobal⟩

end RHTower
