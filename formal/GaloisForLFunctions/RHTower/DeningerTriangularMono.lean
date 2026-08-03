import GaloisForLFunctions.RHTower.DeningerProjSplit

/-!
# A triangular map with injective diagonal is injective

A map of biproducts whose matrix is triangular with injective diagonal entries is injective: an
element of the kernel has its first coordinate killed by the first diagonal entry, hence vanishes,
and then its second coordinate is killed by the second.

* `deningerMono_of_triangular` : the criterion.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits

/-- **A triangular map with injective diagonal is injective.** -/
theorem deningerMono_of_triangular {C : Type*} [Category C] [Abelian C] {A B X Y : C}
    (f : A ⊞ B ⟶ X ⊞ Y)
    (h₁ : Mono (biprod.inl ≫ f ≫ biprod.fst))
    (h₂ : Mono (biprod.inr ≫ f ≫ biprod.snd))
    (h₃ : biprod.inr ≫ f ≫ biprod.fst = 0) : Mono f := by
  rw [Preadditive.mono_iff_cancel_zero]
  intro Z g hg
  have hsplit : g = (g ≫ biprod.fst) ≫ biprod.inl + (g ≫ biprod.snd) ≫ biprod.inr := by
    conv_lhs => rw [← Category.comp_id g, ← biprod.total]
    rw [Preadditive.comp_add, Category.assoc, Category.assoc]
  have hfst : g ≫ biprod.fst ≫ biprod.inl ≫ f ≫ biprod.fst = 0 := by
    have h := congrArg (fun t => t ≫ biprod.fst) hg
    simp only [Category.assoc, zero_comp] at h
    rw [hsplit] at h
    simp only [Preadditive.add_comp, Category.assoc] at h
    rw [h₃, comp_zero, comp_zero, add_zero] at h
    exact h
  have hg₁ : g ≫ biprod.fst = 0 := by
    haveI := h₁
    refine (cancel_mono (biprod.inl ≫ f ≫ biprod.fst)).1 ?_
    rw [zero_comp, Category.assoc]
    exact hfst
  have hsnd : g ≫ biprod.snd ≫ biprod.inr ≫ f ≫ biprod.snd = 0 := by
    have h := congrArg (fun t => t ≫ biprod.snd) hg
    simp only [Category.assoc, zero_comp] at h
    rw [hsplit] at h
    simp only [Preadditive.add_comp, Category.assoc] at h
    rw [← Category.assoc g biprod.fst, hg₁, zero_comp, zero_add] at h
    exact h
  have hg₂ : g ≫ biprod.snd = 0 := by
    haveI := h₂
    refine (cancel_mono (biprod.inr ≫ f ≫ biprod.snd)).1 ?_
    rw [zero_comp, Category.assoc]
    exact hsnd
  rw [hsplit, hg₁, hg₂, zero_comp, zero_comp, add_zero]

end RHTower
