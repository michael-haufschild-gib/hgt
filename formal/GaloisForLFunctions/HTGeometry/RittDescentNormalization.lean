import GaloisForLFunctions.HTGeometry.RittTreeChannelDegree
import GaloisForLFunctions.HTGeometry.RittFirstOrderForm

/-!
# The leading coefficient of a degenerate descent is a constant

When the tower descent degenerates, the leading coefficient of the numerator is fixed by the shift.
Fixedness in the extension puts it in the base field, and fixedness in the base field, for a map of
degree at least two, puts it in the constants.

That is what licenses normalising the numerator to be monic, after which the leading term carries no
information and the comparison has to be made one coefficient further down — where the affine part
of the shift on the top jet, and so the derivation, enters.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] [CharZero K]

/-- **A shift-fixed element of the extension is a constant, for a channel map of degree at least
two.** -/
theorem frame_base_isConst_of_sigma_fixed {L : Type*} [Field L] [Algebra (RatFunc K) L]
    (Fr : RittFrame (RatFunc K) L) {p : ℕ} (hp : 2 ≤ p) {u v : K} (huv : u ≠ v)
    {hR : ¬ ∃ c : K, treeRG p u v = RatFunc.C c}
    (hψ : ∀ x, Fr.ψ x = ratFuncSubstitutionAlgHom (treeRG p u v) hR x)
    {y : L} (hy : Fr.σ y = y) :
    ∃ c : K, algebraMap (RatFunc K) L (RatFunc.C c) = y := by
  obtain ⟨a, ha⟩ := Fr.fixed y hy
  have hcomp := Fr.comp a
  rw [ha, hy] at hcomp
  have hpsi : Fr.ψ a = a := by
    refine (algebraMap (RatFunc K) L).injective ?_
    rw [← hcomp, ha]
  have hfix : ratFuncSubstitutionAlgHom (treeRG p u v) hR a = a := by
    rw [← hψ a]
    exact hpsi
  obtain ⟨c, hc⟩ := eq_C_of_substitution_fixed_treeRG hp huv (hR := hR) hfix
  exact ⟨c, by rw [← hc, ha]⟩

end GaloisForLFunctions.HTGeometry
