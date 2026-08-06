import GaloisForLFunctions.HTGeometry.DGroupBasicInstances
import GaloisForLFunctions.HTGeometry.DGroupSourceBoundary

/-!
# Products of commutative `D`-groups

The product of two commutative algebraic `D`-group presentations is again one: coordinates and
logarithmic coordinates concatenate, the logarithmic derivative stays a homomorphism, and each of
the two rationality laws holds blockwise.

Source data also multiply, so a family of points of a product carries the source recurrence of its
two factors.  Together with the additive and multiplicative presentations this makes every split
group `G_a^r × G_m^s` an instance of the general source-boundary theorems.
-/

open Set
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-! ### Ranges of concatenated families -/

theorem range_subset_range_append_left {α : Type*} {m n : ℕ} (u : Fin m → α) (v : Fin n → α) :
    Set.range u ⊆ Set.range (Fin.append u v) := by
  rintro - ⟨i, rfl⟩
  exact ⟨Fin.castAdd n i, Fin.append_left u v i⟩

theorem range_subset_range_append_right {α : Type*} {m n : ℕ} (u : Fin m → α) (v : Fin n → α) :
    Set.range v ⊆ Set.range (Fin.append u v) := by
  rintro - ⟨i, rfl⟩
  exact ⟨Fin.natAdd m i, Fin.append_right u v i⟩

namespace DGroupPresentation

variable {G₁ G₂ : Type*} [CommGroup G₁] [CommGroup G₂] {K L : Type u} [Field K] [Field L]
  [Algebra K L] [Differential K] [Differential L] [DifferentialAlgebra K L]
  {n₁ d₁ n₂ d₂ : ℕ}

/-- The product of two commutative `D`-group presentations. -/
def prod (P₁ : DGroupPresentation G₁ K L n₁ d₁) (P₂ : DGroupPresentation G₂ K L n₂ d₂) :
    DGroupPresentation (G₁ × G₂) K L (n₁ + n₂) (d₁ + d₂) where
  coords g := Fin.append (P₁.coords g.1) (P₂.coords g.2)
  ell g := Fin.append (P₁.ell g.1) (P₂.ell g.2)
  ell_mul g h := by
    funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Fin.append_left, Pi.add_apply, Fin.append_left, Fin.append_left]
      exact congrFun (P₁.ell_mul g.1 h.1) i
    · rw [Fin.append_right, Pi.add_apply, Fin.append_right, Fin.append_right]
      exact congrFun (P₂.ell_mul g.2 h.2) i
  ell_mem_coordAdjoin g j := by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · rw [Fin.append_left]
      refine IntermediateField.adjoin.mono K _ _ ?_ (P₁.ell_mem_coordAdjoin g.1 i)
      exact differentialJetSet_mono
        (range_subset_range_append_left (P₁.coords g.1) (P₂.coords g.2))
    · rw [Fin.append_right]
      refine IntermediateField.adjoin.mono K _ _ ?_ (P₂.ell_mem_coordAdjoin g.2 i)
      exact differentialJetSet_mono
        (range_subset_range_append_right (P₁.coords g.1) (P₂.coords g.2))
  deriv_coords_mem g i := by
    refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i
    · rw [Fin.append_left]
      refine IntermediateField.adjoin.mono K _ _ ?_ (P₁.deriv_coords_mem g.1 i')
      refine Set.union_subset_union
        (range_subset_range_append_left (P₁.coords g.1) (P₂.coords g.2))
        (differentialJetSet_mono
          (range_subset_range_append_left (P₁.ell g.1) (P₂.ell g.2)))
    · rw [Fin.append_right]
      refine IntermediateField.adjoin.mono K _ _ ?_ (P₂.deriv_coords_mem g.2 i')
      refine Set.union_subset_union
        (range_subset_range_append_right (P₁.coords g.1) (P₂.coords g.2))
        (differentialJetSet_mono
          (range_subset_range_append_right (P₁.ell g.1) (P₂.ell g.2)))

@[simp] theorem prod_coords (P₁ : DGroupPresentation G₁ K L n₁ d₁)
    (P₂ : DGroupPresentation G₂ K L n₂ d₂) (g : G₁ × G₂) :
    (P₁.prod P₂).coords g = Fin.append (P₁.coords g.1) (P₂.coords g.2) := rfl

@[simp] theorem prod_ell (P₁ : DGroupPresentation G₁ K L n₁ d₁)
    (P₂ : DGroupPresentation G₂ K L n₂ d₂) (g : G₁ × G₂) :
    (P₁.prod P₂).ell g = Fin.append (P₁.ell g.1) (P₂.ell g.2) := rfl

end DGroupPresentation

/-! ### Products of source data -/

namespace DGroupSourceData

variable {G₁ G₂ : Type*} [CommGroup G₁] [CommGroup G₂] {K L : Type u} [Field K] [Field L]
  [Algebra K L] [Differential K] [Differential L] [DifferentialAlgebra K L]
  {n₁ d₁ n₂ d₂ : ℕ} {I S : Type*} {sigma : I → L ≃+* L}
  {P₁ : DGroupPresentation G₁ K L n₁ d₁} {P₂ : DGroupPresentation G₂ K L n₂ d₂}
  {g₁ : S → G₁} {g₂ : S → G₂}

/-- Source data multiply: the product family carries the source recurrence of both factors. -/
def prod (D₁ : DGroupSourceData P₁ sigma g₁) (D₂ : DGroupSourceData P₂ sigma g₂) :
    DGroupSourceData (P₁.prod P₂) sigma (fun a => (g₁ a, g₂ a)) where
  act i x := (D₁.act i x.1, D₂.act i x.2)
  act_ell i x j := by
    refine Fin.addCases (fun i' => ?_) (fun i' => ?_) j
    · rw [DGroupPresentation.prod_ell, Fin.append_left, DGroupPresentation.prod_ell,
        Fin.append_left]
      exact D₁.act_ell i x.1 i'
    · rw [DGroupPresentation.prod_ell, Fin.append_right, DGroupPresentation.prod_ell,
        Fin.append_right]
      exact D₂.act_ell i x.2 i'
  mult i a := (D₁.mult i a, D₂.mult i a)
  recurrence i a := by
    refine Prod.ext ?_ ?_
    · exact D₁.recurrence i a
    · exact D₂.recurrence i a
  omega i a := Fin.append (D₁.omega i a) (D₂.omega i a)
  omega_spec i a j := by
    refine Fin.addCases (fun i' => ?_) (fun i' => ?_) j
    · rw [Fin.append_left, DGroupPresentation.prod_ell, Fin.append_left]
      exact D₁.omega_spec i a i'
    · rw [Fin.append_right, DGroupPresentation.prod_ell, Fin.append_right]
      exact D₂.omega_spec i a i'

end DGroupSourceData

/-! ### The split groups -/

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  [Differential K] [Differential L] [DifferentialAlgebra K L]

/-- The split group `G_a × G_m`, as a commutative `D`-group presentation. -/
def additiveMulDGroup :
    DGroupPresentation (Multiplicative L × Lˣ) K L (1 + 1) (1 + 1) :=
  (additiveDGroup (K := K)).prod (multiplicativeDGroup (K := K))

end

end GaloisForLFunctions.HTGeometry
