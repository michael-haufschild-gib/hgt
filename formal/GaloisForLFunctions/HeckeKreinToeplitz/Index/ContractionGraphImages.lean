import GaloisForLFunctions.HeckeKreinToeplitz.Index.FiniteNegativeDirections

/-!
# Images of nonpositive contraction graphs

A form-isometry maps the graph of a contraction onto another contraction
graph. The negative projection on the image is injective because a
nonpositive vector with zero negative coordinate vanishes. Finite dimension
makes this projection invertible.
-/

noncomputable section
set_option autoImplicit false
open scoped InnerProductSpace

namespace GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Inclusion into the graph of a linear map. -/
def graphMap (A : E →ₗ[ℂ] H) : E →ₗ[ℂ] (H × E) where
  toFun x := (A x, x)
  map_add' x y := Prod.ext (map_add A x y) rfl
  map_smul' c x := Prod.ext (map_smul A c x) rfl

/-- Negative coordinate of a transformed graph. -/
def graphNegative (T : (H × E) ≃ₗ[ℂ] (H × E)) (A : E →ₗ[ℂ] H) : E →ₗ[ℂ] E where
  toFun x := (T (A x, x)).2
  map_add' x y := by
    change (T (graphMap A (x + y))).2 = _
    rw [map_add, map_add]
    rfl
  map_smul' c x := by
    change (T (graphMap A (c • x))).2 = _
    rw [map_smul, map_smul]
    rfl

/-- Positive coordinate of a transformed graph. -/
def graphPositive (T : (H × E) ≃ₗ[ℂ] (H × E)) (A : E →ₗ[ℂ] H) : E →ₗ[ℂ] H where
  toFun x := (T (A x, x)).1
  map_add' x y := by
    change (T (graphMap A (x + y))).1 = _
    rw [map_add, map_add]
    rfl
  map_smul' c x := by
    change (T (graphMap A (c • x))).1 = _
    rw [map_smul, map_smul]
    rfl

variable (T : (H × E) ≃ₗ[ℂ] (H × E))
    (hT : ∀ v w, pairing (T v) (T w) = pairing v w)
    (A : E →ₗ[ℂ] H) (hA : ∀ x, ‖A x‖ ≤ ‖x‖)

include hT hA in
/-- The negative projection cannot kill a nonzero vector in a nonpositive graph. -/
theorem graphNegative_injective : Function.Injective (graphNegative T A) := by
  have hzero (x : E) (hx : graphNegative T A x = 0) : x = 0 := by
    have hq : (pairing (T (A x, x)) (T (A x, x))).re ≤ 0 := by
      rw [hT]
      exact (pairing_self_nonpos_iff _).mpr (hA x)
    have ht := eq_zero_of_nonpositive_snd_eq_zero hq hx
    exact congrArg Prod.snd (T.injective (ht.trans (map_zero T).symm))
  intro x y hxy
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub, hxy, sub_self]

variable [FiniteDimensional ℂ E]

/-- Invertible negative projection of the transformed graph. -/
def graphNegativeEquiv : E ≃ₗ[ℂ] E :=
  LinearEquiv.ofBijective (graphNegative T A)
    ⟨graphNegative_injective T hT A hA,
      LinearMap.injective_iff_surjective.mp (graphNegative_injective T hT A hA)⟩

/-- Linear map whose graph is the transformed nonpositive graph. -/
def imageGraph : E →ₗ[ℂ] H :=
  (graphPositive T A).comp (graphNegativeEquiv T hT A hA).symm.toLinearMap

theorem imageGraph_graphNegative (x : E) :
    imageGraph T hT A hA (graphNegative T A x) = graphPositive T A x := by
  change graphPositive T A ((graphNegativeEquiv T hT A hA).symm
    ((graphNegativeEquiv T hT A hA) x)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The isometry intertwines the original and image graphs through the negative projection. -/
theorem imageGraph_relation (x : E) :
    T (A x, x) = (imageGraph T hT A hA (graphNegative T A x), graphNegative T A x) := by
  apply Prod.ext
  · exact (imageGraph_graphNegative T hT A hA x).symm
  · rfl

/-- The image graph is again contractive. -/
theorem imageGraph_norm_le (x : E) : ‖imageGraph T hT A hA x‖ ≤ ‖x‖ := by
  obtain ⟨y, hy⟩ := (graphNegativeEquiv T hT A hA).surjective x
  change graphNegative T A y = x at hy
  have hq : (pairing (T (A y, y)) (T (A y, y))).re ≤ 0 := by
    rw [hT]
    exact (pairing_self_nonpos_iff _).mpr (hA y)
  rw [imageGraph_relation T hT A hA y, hy] at hq
  exact (pairing_self_nonpos_iff _).mp hq

/-- The graph relation uniquely determines the transformed operator. -/
theorem eq_imageGraph_of_relation (B : E →ₗ[ℂ] H)
    (hB : ∀ x, T (A x, x) = (B (graphNegative T A x), graphNegative T A x)) :
    B = imageGraph T hT A hA := by
  apply LinearMap.ext
  intro x
  obtain ⟨y, hy⟩ := (graphNegativeEquiv T hT A hA).surjective x
  change graphNegative T A y = x at hy
  have he := congrArg Prod.fst ((hB y).symm.trans (imageGraph_relation T hT A hA y))
  simpa only [hy] using he

#print axioms imageGraph_norm_le

end GaloisForLFunctions.HeckeKreinToeplitz.FiniteNegative
