import GaloisForLFunctions.RHTower.DeningerTriangularMono

/-!
# Shearing a biproduct

The two edge families of a subdivided tree both meet the base vertices, so the comparison map is not
triangular as it stands; it becomes triangular after subtracting one edge family from the other,
which is an automorphism of the biproduct.

* `deningerShear` : the shear automorphism.
* `deningerMono_of_shear_triangular` : injectivity after shearing.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits

variable {C : Type*} [Category C] [Abelian C]

/-- The shear automorphism of a square biproduct: it fixes the first summand and subtracts it from
the second. -/
noncomputable def deningerShear (A : C) : A ⊞ A ≅ A ⊞ A where
  hom := biprod.desc biprod.inl (biprod.inr - biprod.inl)
  inv := biprod.desc biprod.inl (biprod.inr + biprod.inl)
  hom_inv_id := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;> simp [Preadditive.sub_comp]
  inv_hom_id := by
    refine biprod.hom_ext' _ _ ?_ ?_ <;> simp [Preadditive.add_comp]

@[simp] theorem deningerShear_inl (A : C) :
    biprod.inl ≫ (deningerShear A).hom = biprod.inl := by
  simp [deningerShear]

@[simp] theorem deningerShear_inr (A : C) :
    biprod.inr ≫ (deningerShear A).hom = biprod.inr - biprod.inl := by
  simp [deningerShear]

/-- **Injectivity after shearing.**  A map out of a square biproduct is injective as soon as its
first column is injective on the first coordinate, and the difference of its two columns is
injective on the second coordinate and vanishes on the first. -/
theorem deningerMono_of_shear_triangular {A X Y : C} (f : A ⊞ A ⟶ X ⊞ Y)
    (h₁ : Mono (biprod.inl ≫ f ≫ biprod.fst))
    (h₂ : Mono ((biprod.inr - biprod.inl) ≫ f ≫ biprod.snd))
    (h₃ : (biprod.inr - biprod.inl) ≫ f ≫ biprod.fst = 0) : Mono f := by
  have hmono : Mono ((deningerShear A).hom ≫ f) := by
    refine deningerMono_of_triangular _ ?_ ?_ ?_
    · simp only [Category.assoc]
      rw [← Category.assoc biprod.inl, deningerShear_inl]
      exact h₁
    · simp only [Category.assoc]
      rw [← Category.assoc biprod.inr, deningerShear_inr]
      exact h₂
    · simp only [Category.assoc]
      rw [← Category.assoc biprod.inr, deningerShear_inr]
      exact h₃
  have hf : f = (deningerShear A).inv ≫ ((deningerShear A).hom ≫ f) := by
    rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [hf]
  exact mono_comp _ _

end RHTower
