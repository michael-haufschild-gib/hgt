import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.SmoothParabolicInduction

/-! Evaluation at the identity gives Frobenius reciprocity for
smooth induction. Its inverse sends a vector to the evaluations
of its translates under the given intertwining map. -/

noncomputable section

namespace Representation

variable {G H V W : Type*} [Group G] [Group H] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (f : H →* G) (π : Representation ℂ G V) (ρ : Representation ℂ H W)

private def smoothInductionEvalOne (T : π.IntertwiningMap (smoothInduction f ρ)) :
    IntertwiningMap (π.comp f) ρ where
  toLinearMap :=
    { toFun := fun v => (T v).val.val 1
      map_add' := fun u v => by rw [map_add]; rfl
      map_smul' := fun c v => by rw [map_smul]; rfl }
  isIntertwining' h := LinearMap.ext fun v => by
    change (T (π (f h) v)).val.val 1 = ρ h ((T v).val.val 1)
    rw [IntertwiningMap.isIntertwining π (smoothInduction f ρ) T, smoothInduction_apply, one_mul]
    simpa only [mul_one] using smoothInduction_equivariance f ρ (T v) h 1

private def smoothInductionFromMap (hπ : ∀ v : V, IsOpen {g : G | π g v = v})
    (T : IntertwiningMap (π.comp f) ρ) : π.IntertwiningMap (smoothInduction f ρ) := by
  let e : V →ₗ[ℂ] coindV f ρ :=
    { toFun := fun v => ⟨fun g => T (π g v), fun h g => by
        change T (π (f h * g) v) = ρ h (T (π g v))
        rw [map_mul, Module.End.mul_apply]
        exact IntertwiningMap.isIntertwining (π.comp f) ρ T h (π g v)⟩
      map_add' := fun u v => Subtype.ext (funext fun g => by simp)
      map_smul' := fun c v => Subtype.ext (funext fun g => by simp) }
  have he (g : G) (v : V) : e (π g v) = coind f ρ g (e v) := by
    apply Subtype.ext
    funext x
    change T (π x (π g v)) = T (π (x * g) v)
    rw [map_mul, Module.End.mul_apply]
  have hs (v : V) : e v ∈ (coind f ρ).smoothVectors := by
    rw [mem_smoothVectors]
    apply (coind f ρ).isOpen_vectorStabilizer_of_open_subgroup (H := π.vectorStabilizer v) (hπ v)
    intro g hg
    change π g v = v at hg
    rw [← he, hg]
  exact ⟨e.codRestrict _ hs, fun g => LinearMap.ext fun v => Subtype.ext (he g v)⟩

/-- Frobenius reciprocity for smooth induction of complex representations. -/
def smoothInductionHomEquiv (hπ : ∀ v : V, IsOpen {g : G | π g v = v}) :
    (π.IntertwiningMap (smoothInduction f ρ)) ≃ (IntertwiningMap (π.comp f) ρ) where
  toFun := smoothInductionEvalOne f π ρ
  invFun := smoothInductionFromMap f π ρ hπ
  left_inv T := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    apply Subtype.ext
    funext g
    change (T (π g v)).val.val 1 = (T v).val.val g
    rw [IntertwiningMap.isIntertwining π (smoothInduction f ρ) T, smoothInduction_apply, one_mul]
  right_inv T := by
    apply IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    change T (π 1 v) = T v
    rw [map_one, Module.End.one_apply]

end Representation

#print axioms Representation.smoothInductionHomEquiv
