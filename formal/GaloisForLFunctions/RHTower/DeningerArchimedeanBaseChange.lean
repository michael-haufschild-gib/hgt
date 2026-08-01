import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.FieldTheory.PrimitiveElement

/-!
# Archimedean base change for place sums

Restricting a complex embedding of `L` to a subfield `K` has fibres of constant size `[L : K]`:
the fibre over `φ` is the set of `K`-algebra maps `L → ℂ` when `ℂ` is made a `K`-algebra through
`φ`, and an algebraically closed target counts exactly `[L : K]` of them.

Consequently every archimedean place sum multiplies by `[L : K]` under base change.  Together with
the identification of embedding sums with place sums weighted by multiplicity, this is the
archimedean half of the statement that the Weil height does not depend on the field of definition,
which is what makes the place spaces of a tower of number fields glue.

* `deningerEmbeddingSum_eq_placeSum` : embedding sums are place sums weighted by `mult`.
* `deningerEmbeddingFibre_card` : the restriction map has fibres of size `[L : K]`.
* `deningerEmbeddingSum_baseChange`, `deningerArchPlaceSum_baseChange` : the base-change law.
-/

namespace RHTower

open NumberField NumberField.InfinitePlace Module

section EmbeddingPlaceSum

variable {K : Type*} [Field K] [NumberField K]

/-- **Embedding sums are place sums.**  Summing a function of `‖φ x‖` over all complex embeddings
is summing over the infinite places with their multiplicities, because the embeddings inducing a
given place are exactly `mult` many. -/
theorem deningerEmbeddingSum_eq_placeSum (F : ℝ → ℝ) (x : K) :
    ∑ φ : K →+* ℂ, F ‖φ x‖ = ∑ w : InfinitePlace K, (mult w : ℝ) * F (w x) := by
  classical
  have hmaps : ∀ φ ∈ (Finset.univ : Finset (K →+* ℂ)),
      (mk φ) ∈ (Finset.univ : Finset (InfinitePlace K)) := fun _ _ => Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hconst : ∀ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => mk φ = w),
      F ‖φ x‖ = F (w x) := by
    intro φ hφ
    rw [← (Finset.mem_filter.mp hφ).2]
    rfl
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, card_filter_mk_eq, nsmul_eq_mul]

end EmbeddingPlaceSum

section BaseChange

variable {K L : Type*} [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]

/-- **The fibres of restriction of complex embeddings.**  For every complex embedding `φ` of `K`
there are exactly `[L : K]` complex embeddings of `L` restricting to it. -/
theorem deningerEmbeddingFibre_card (φ : K →+* ℂ) :
    Fintype.card {ψ : L →+* ℂ // ψ.comp (algebraMap K L) = φ} = finrank K L := by
  classical
  letI : Algebra K ℂ := φ.toAlgebra
  have hmap : ∀ r : K, algebraMap K ℂ r = φ r := fun _ => rfl
  have e : {ψ : L →+* ℂ // ψ.comp (algebraMap K L) = φ} ≃ (L →ₐ[K] ℂ) :=
    { toFun := fun ψ =>
        { toRingHom := ψ.1
          commutes' := fun r => by
            have h := congrArg (fun f : K →+* ℂ => f r) ψ.2
            simpa [hmap] using h }
      invFun := fun f =>
        ⟨f.toRingHom, by
          ext r
          have := f.commutes r
          simp [hmap] at this ⊢
          exact this⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, AlgHom.card]

/-- **The archimedean base-change law for embedding sums.** -/
theorem deningerEmbeddingSum_baseChange (F : ℝ → ℝ) (x : K) :
    ∑ ψ : L →+* ℂ, F ‖ψ (algebraMap K L x)‖
      = (finrank K L : ℝ) * ∑ φ : K →+* ℂ, F ‖φ x‖ := by
  classical
  have hmaps : ∀ ψ ∈ (Finset.univ : Finset (L →+* ℂ)),
      ψ.comp (algebraMap K L) ∈ (Finset.univ : Finset (K →+* ℂ)) := fun _ _ => Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps, Finset.mul_sum]
  refine Finset.sum_congr rfl fun φ _ => ?_
  have hconst : ∀ ψ ∈ Finset.univ.filter (fun ψ : L →+* ℂ => ψ.comp (algebraMap K L) = φ),
      F ‖ψ (algebraMap K L x)‖ = F ‖φ x‖ := by
    intro ψ hψ
    rw [← (Finset.mem_filter.mp hψ).2]
    rfl
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Fintype.card_subtype.symm.trans
    (deningerEmbeddingFibre_card (L := L) φ), nsmul_eq_mul]

/-- **The archimedean base-change law for place sums.**  Every archimedean place sum, weighted by
multiplicity, multiplies by `[L : K]` when the field of definition is enlarged.  This is the
archimedean half of the independence of the Weil height from the field of definition. -/
theorem deningerArchPlaceSum_baseChange (F : ℝ → ℝ) (x : K) :
    ∑ w : InfinitePlace L, (mult w : ℝ) * F (w (algebraMap K L x))
      = (finrank K L : ℝ) * ∑ v : InfinitePlace K, (mult v : ℝ) * F (v x) := by
  rw [← deningerEmbeddingSum_eq_placeSum F (algebraMap K L x),
    ← deningerEmbeddingSum_eq_placeSum F x]
  exact deningerEmbeddingSum_baseChange F x

end BaseChange

end RHTower
