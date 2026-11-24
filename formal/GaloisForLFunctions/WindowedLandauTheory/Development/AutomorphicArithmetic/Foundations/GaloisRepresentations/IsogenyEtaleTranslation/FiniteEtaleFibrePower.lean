import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Over
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products

/-! Coordinatewise finite étale surjections induce a finite étale
surjection on the fibre power over the common base. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

private theorem isPullback_coordinateEnd {C : Type*} [Category C] {A : C} {n : ℕ}
    [HasProduct (fun _ : Fin n => A)] (j : Fin n) (f : A ⟶ A) :
    IsPullback (Limits.Pi.map (fun i => if i = j then f else 𝟙 A))
      (Limits.Pi.π (fun _ : Fin n => A) j) (Limits.Pi.π (fun _ : Fin n => A) j) f := by
  refine ⟨⟨by simp only [Limits.Pi.map_π, if_true]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => Limits.Pi.lift fun i => if i = j then s.snd else s.fst ≫ Limits.Pi.π (fun _ : Fin n => A) i)
    ?_ ?_ ?_⟩⟩
  · intro s
    apply Limits.Pi.hom_ext
    intro i
    rw [Category.assoc, Limits.Pi.map_π]
    by_cases h : i = j
    · subst h
      simpa only [if_true, Limits.Pi.lift_π, ← Category.assoc] using s.condition.symm
    · simp only [if_neg h, Category.comp_id, Limits.Pi.lift_π]
  · intro s
    rw [Limits.Pi.lift_π, if_pos rfl]
  · intro s m h₁ h₂
    apply Limits.Pi.hom_ext
    intro i
    rw [Limits.Pi.lift_π]
    by_cases h : i = j
    · subst h
      simpa only [if_true] using h₂
    · have e := congrArg (fun g => g ≫ Limits.Pi.π (fun _ : Fin n => A) i) h₁
      simpa only [Category.assoc, Limits.Pi.map_π, if_neg h, Category.comp_id] using e

private theorem fibrePower_map_prop {S : Scheme} (A : Over S) {n : ℕ}
    (f : Fin n → (A ⟶ A)) (P : MorphismProperty Scheme)
    [P.IsMultiplicative] [P.IsStableUnderBaseChange] (hf : ∀ i, P (f i).left) :
    P (Limits.Pi.map f).left := by
  let F (r : ℕ) (i : Fin n) := if i.val < r then f i else 𝟙 A
  have step (r : ℕ) (hr : r ≤ n) : P (Limits.Pi.map (F r)).left := by
    induction r with
    | zero =>
      simpa only [F, Nat.not_lt_zero, if_false, Limits.Pi.map_id, Over.id_left] using
        P.id_mem (∏ᶜ fun _ : Fin n => A).left
    | succ r ih =>
      let j : Fin n := ⟨r, Nat.lt_of_succ_le hr⟩
      let E (i : Fin n) : A ⟶ A := if i = j then f j else 𝟙 A
      have he : P (Limits.Pi.map E).left :=
        P.of_isPullback ((isPullback_coordinateEnd j (f j)).map (Over.forget S)).flip (hf j)
      have hc (i : Fin n) : F (r + 1) i = F r i ≫ E i := by
        by_cases hi : i = j
        · subst i
          simp only [F, E, j, Nat.lt_succ_self, lt_irrefl, if_true, if_false, Category.id_comp]
        · have hval : i.val ≠ r := fun h => hi (Fin.ext h)
          have hlt : i.val < r + 1 ↔ i.val < r := by omega
          simp only [F, E, hi, if_false, hlt, Category.comp_id]
      rw [funext hc, ← Limits.Pi.map_comp_map, Over.comp_left]
      exact P.comp_mem _ _ (ih (Nat.le_of_succ_le hr)) he
  have hF : F n = f := funext fun i => if_pos i.isLt
  simpa only [hF] using step n le_rfl

/-- Finite étale surjections remain finite étale surjective after taking
a product over the common base. -/
theorem finiteEtaleSurjective_fibrePower_map {S : Scheme} (A : Over S) {n : ℕ}
    (f : Fin n → (A ⟶ A)) (hf : ∀ i, IsFinite (f i).left ∧ Etale (f i).left ∧ Surjective (f i).left) :
    IsFinite (Limits.Pi.map f).left ∧ Etale (Limits.Pi.map f).left ∧ Surjective (Limits.Pi.map f).left :=
  ⟨fibrePower_map_prop A f @IsFinite fun i => (hf i).1,
    fibrePower_map_prop A f @Etale fun i => (hf i).2.1,
    fibrePower_map_prop A f @Surjective fun i => (hf i).2.2⟩

end GlobalTheory
