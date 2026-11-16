import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicConstantTermPole

/-!
# Uniform bounds for the reciprocal unramified ideal zeta function

The absolutely convergent ideal Möbius series represents `1/Z₀(s)` for `Re s>1`.
Its terms are dominated by the unramified ideal weights at the left edge of any
closed right half-plane contained in this region.
-/

noncomputable section
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein

/-- The reciprocal unramified zeta series is uniformly bounded on closed right half-planes. -/
theorem unramifiedIdealZeta_inv_bounded (a : ℝ) (ha : 1 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → ‖(unramifiedIdealZeta s)⁻¹‖ ≤ C := by
  refine ⟨∑' I : Ideal O, ‖unramifiedNormWeight (a : ℂ) I‖,
    tsum_nonneg (fun _ => norm_nonneg _), ?_⟩
  intro s hs
  have hs1 : 1 < s.re := ha.trans_le hs
  rw [← unramifiedMobiusSeries_eq_inv s hs1, unramifiedMobiusSeries]
  refine (norm_tsum_le_tsum_norm (moebius_unramifiedNormWeight_summable_norm s hs1)).trans ?_
  apply Summable.tsum_le_tsum _ (moebius_unramifiedNormWeight_summable_norm s hs1)
    (unramifiedNormWeight_summable_norm (a : ℂ) (by simpa using ha))
  intro I
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (norm_ideal_moebius_le_one I)).trans
    (unramifiedNormWeight_norm_mono a s hs I)

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
