import GaloisForLFunctions.HTGeometry.PaperQuadricLineObstruction
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.PicardUFD
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.DeterminantUFD

/-!
# An explicit nonzero Picard class killed by the determinant torsor

The ideal `(x,z)` on `xy=z(z+1)` has fractional inverse `(1,(z+1)/x)`.
Their product is the unit submodule: the four products are `x,z,z+1,y`,
and `(z+1)-z=1`. This constructs invertibility, rather than assuming it.
The line has no global generator downstairs, although every invertible
module on the determinant torsor is trivial.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate

noncomputable section

variable (k : Type*) [Field k]

/-- The fraction field of the actual source quadric. -/
abbrev PaperQuadricFractionField := FractionRing (Obstruction.B k)

private abbrev embed := algebraMap (Obstruction.B k) (PaperQuadricFractionField k)

/-- The line ideal embedded in the actual quadric fraction field. -/
def paperQuadricFractionalLine : Submodule (Obstruction.B k) (PaperQuadricFractionField k) :=
  Submodule.span (Obstruction.B k) {embed k (Obstruction.bX k 0), embed k (Obstruction.bX k 2)}

/-- An explicit fractional inverse of the quadric line. -/
def paperQuadricFractionalInverse : Submodule (Obstruction.B k) (PaperQuadricFractionField k) :=
  Submodule.span (Obstruction.B k)
    {1, (embed k (Obstruction.bX k 2) + 1) / embed k (Obstruction.bX k 0)}

/-- The displayed fractional modules multiply to the coefficient submodule. -/
theorem paperQuadricFractionalLine_mul_inverse :
    paperQuadricFractionalLine k * paperQuadricFractionalInverse k = 1 := by
  let x := embed k (Obstruction.bX k 0)
  let y := embed k (Obstruction.bX k 1)
  let z := embed k (Obstruction.bX k 2)
  have hx : x ≠ 0 := by
    intro h
    exact paperQuadric_x_ne_zero k ((IsFractionRing.injective
      (Obstruction.B k) (PaperQuadricFractionField k)) (h.trans (map_zero _).symm))
  have hrel : x * y = z * (z + 1) := by
    have h := congrArg (embed k) (Obstruction.b_relation k)
    simpa only [map_sub, map_mul, map_add, map_one, map_zero, sub_eq_zero] using h
  have hxt : x * ((z + 1) / x) = z + 1 := mul_div_cancel₀ _ hx
  have hzt : z * ((z + 1) / x) = y := by
    rw [← mul_div_assoc, ← hrel, mul_div_cancel_left₀ _ hx]
  have base_mem (q : Obstruction.B k) : embed k q ∈
      (1 : Submodule (Obstruction.B k) (PaperQuadricFractionField k)) := by
    rw [Submodule.one_eq_range]
    exact ⟨q, rfl⟩
  apply le_antisymm
  · rw [paperQuadricFractionalLine, paperQuadricFractionalInverse, Submodule.span_mul_span]
    apply Submodule.span_le.mpr
    rintro t ⟨p, hp, q, hq, rfl⟩
    rcases Set.mem_insert_iff.mp hp with rfl | hp
    · rcases Set.mem_insert_iff.mp hq with rfl | hq
      · change x * 1 ∈ (1 : Submodule (Obstruction.B k) (PaperQuadricFractionField k))
        rw [mul_one]
        exact base_mem (Obstruction.bX k 0)
      · rcases Set.mem_singleton_iff.mp hq with rfl
        change x * ((z + 1) / x) ∈
          (1 : Submodule (Obstruction.B k) (PaperQuadricFractionField k))
        rw [hxt]
        have hb := base_mem (Obstruction.bX k 2 + 1)
        rw [map_add, map_one] at hb
        exact hb
    · rcases Set.mem_singleton_iff.mp hp with rfl
      rcases Set.mem_insert_iff.mp hq with rfl | hq
      · change z * 1 ∈ (1 : Submodule (Obstruction.B k) (PaperQuadricFractionField k))
        rw [mul_one]
        exact base_mem (Obstruction.bX k 2)
      · rcases Set.mem_singleton_iff.mp hq with rfl
        change z * ((z + 1) / x) ∈ _
        rw [hzt]
        exact base_mem (Obstruction.bX k 1)
  · apply Submodule.one_le.mpr
    have hxmem : x ∈ paperQuadricFractionalLine k :=
      Submodule.subset_span (Set.mem_insert_iff.mpr (Or.inl rfl))
    have hzmem : z ∈ paperQuadricFractionalLine k :=
      Submodule.subset_span (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _)))
    have h1mem : (1 : PaperQuadricFractionField k) ∈ paperQuadricFractionalInverse k :=
      Submodule.subset_span (Set.mem_insert_iff.mpr (Or.inl rfl))
    have htmem : (z + 1) / x ∈ paperQuadricFractionalInverse k :=
      Submodule.subset_span (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _)))
    have ha := Submodule.mul_mem_mul hxmem htmem
    have hb := Submodule.mul_mem_mul hzmem h1mem
    rw [hxt] at ha
    rw [mul_one] at hb
    have hh := (paperQuadricFractionalLine k * paperQuadricFractionalInverse k).sub_mem ha hb
    rw [add_sub_cancel_left] at hh
    exact hh

/-- The line and its explicit inverse form a unit in the submodule monoid. -/
def paperQuadricFractionalLineUnit :
    (Submodule (Obstruction.B k) (PaperQuadricFractionField k))ˣ where
  val := paperQuadricFractionalLine k
  inv := paperQuadricFractionalInverse k
  val_inv := paperQuadricFractionalLine_mul_inverse k
  inv_val := (Submodule.mul_comm _ _).trans (paperQuadricFractionalLine_mul_inverse k)

/-- Embedding the ideal in the fraction field does not change its underlying module. -/
def paperQuadricLineFractionalEquiv :
    paperQuadricLineIdeal k ≃ₗ[Obstruction.B k] paperQuadricFractionalLine k := by
  let f : Obstruction.B k →ₗ[Obstruction.B k] PaperQuadricFractionField k :=
    Algebra.linearMap (Obstruction.B k) (PaperQuadricFractionField k)
  let e : paperQuadricLineIdeal k ≃ₗ[Obstruction.B k] Submodule.map f (paperQuadricLineIdeal k) :=
    Submodule.equivMapOfInjective f
      (IsFractionRing.injective (Obstruction.B k) (PaperQuadricFractionField k))
      (paperQuadricLineIdeal k)
  have he : Submodule.map f (paperQuadricLineIdeal k) = paperQuadricFractionalLine k := by
    change (Submodule.span (Obstruction.B k) {Obstruction.bX k 0, Obstruction.bX k 2}).map f = _
    rw [Submodule.map_span, Set.image_insert_eq, Set.image_singleton]
    rfl
  exact e.trans (LinearEquiv.ofEq _ _ he)

/-- Invertibility of the actual ideal is proved by the explicit fractional inverse. -/
instance paperQuadricLineInvertible : Module.Invertible (Obstruction.B k) (paperQuadricLineIdeal k) := by
  letI : Module.Invertible (Obstruction.B k) (paperQuadricFractionalLine k) :=
    inferInstanceAs (Module.Invertible (Obstruction.B k) (paperQuadricFractionalLineUnit k))
  exact Module.Invertible.congr (paperQuadricLineFractionalEquiv k).symm

/-- The actual nonzero Picard class represented by `(x,z)`. -/
def paperQuadricLineClass : CommRing.Pic (Obstruction.B k) :=
  CommRing.Pic.mk (Obstruction.B k) (paperQuadricLineIdeal k)

/-- This invertible line is genuinely nontrivial on the quadric. -/
theorem paperQuadricLineClass_ne_one : paperQuadricLineClass k ≠ 1 := by
  intro h
  obtain ⟨e⟩ := CommRing.Pic.mk_eq_one_iff.mp h
  have hi : Module.IsPrincipal (Obstruction.B k) (paperQuadricLineIdeal k) :=
    e.isPrincipal_iff.mpr inferInstance
  have hp : (paperQuadricLineIdeal k).IsPrincipal := Module.isPrincipal_submodule_iff.mp hi
  exact paperQuadricLineIdeal_not_principal k hp.principal

/-- The quadric itself is not a GCD domain, despite its factorial determinant torsor. -/
theorem paperQuadric_not_gcdDomain : ¬ IsGCDMonoid (Obstruction.B k) := by
  intro h
  letI := h
  exact paperQuadricLineClass_ne_one k (Subsingleton.elim _ _)

/-- Unique factorization upstairs therefore cannot descend along this torsor map. -/
theorem paperQuadric_not_uniqueFactorization : ¬ UniqueFactorizationMonoid (Obstruction.B k) := by
  intro h
  letI := h
  exact paperQuadric_not_gcdDomain k inferInstance

/-- Pullback along the actual quadric-to-determinant algebra map. -/
def paperQuadricPicardPullback : CommRing.Pic (Obstruction.B k) →* CommRing.Pic (Obstruction.C k) := by
  letI : Algebra (Obstruction.B k) (Obstruction.C k) := (Obstruction.baseMap k).toAlgebra
  exact CommRing.Pic.mapAlgebra (Obstruction.B k) (Obstruction.C k)

/-- Every Picard class becomes trivial on this determinant torsor. -/
theorem paperQuadricPicardPullback_eq_one (L : CommRing.Pic (Obstruction.B k)) :
    paperQuadricPicardPullback k L = 1 := Subsingleton.elim _ _

/-- Pullback loses information: the explicit nonzero line class lies in its kernel. -/
theorem paperQuadricPicardPullback_not_injective :
    ¬ Function.Injective (paperQuadricPicardPullback k) := by
  intro h
  exact paperQuadricLineClass_ne_one k (h (by
    rw [paperQuadricPicardPullback_eq_one, map_one]))

end

end GaloisForLFunctions.HTGeometry
