import GaloisForLFunctions.HTGeometry.HypertranscendentalClockBoundary

/-!
# Bornologically cofinal samplings exist

A sampling is bornologically cofinal for a height profile when every height is matched, within one
uniform constant, by a sampled height.  Every surjective sampling is cofinal with constant zero,
and every sampling of a uniformly bounded profile is cofinal with twice the bound — the two extreme
mechanisms, one geometric and one bornological.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **A surjective sampling is bornologically cofinal, with constant zero.** -/
theorem isBornologicallyCofinal_of_surjective {ι κ : Type*} (h : ι → ℝ) {φ : κ → ι}
    (hsurj : Function.Surjective φ) : IsBornologicallyCofinal h φ := by
  refine ⟨0, fun i => ?_⟩
  obtain ⟨j, hj⟩ := hsurj i
  exact ⟨j, by rw [hj, sub_self, abs_zero]⟩

/-- The identity sampling is bornologically cofinal. -/
theorem isBornologicallyCofinal_id {ι : Type*} (h : ι → ℝ) :
    IsBornologicallyCofinal h (id : ι → ι) :=
  isBornologicallyCofinal_of_surjective h Function.surjective_id

/-- **Every nonempty sampling of a uniformly bounded profile is bornologically cofinal.** -/
theorem isBornologicallyCofinal_of_bounded {ι κ : Type*} [Nonempty κ] {h : ι → ℝ} {B : ℝ}
    (hB : ∀ i, |h i| ≤ B) (φ : κ → ι) : IsBornologicallyCofinal h φ := by
  refine ⟨2 * B, fun i => ⟨Classical.arbitrary κ, ?_⟩⟩
  have h1 := hB i
  have h2 := hB (φ (Classical.arbitrary κ))
  have habs := abs_sub (h i) (h (φ (Classical.arbitrary κ)))
  rw [abs_le] at h1 h2 ⊢
  constructor <;> [linarith [h1.1, h1.2, h2.1, h2.2]; linarith [h1.1, h1.2, h2.1, h2.2]]

end GaloisForLFunctions.HTGeometry
