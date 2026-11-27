import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Distinct simultaneous eigencharacters give coordinate lines for invariant subspaces. -/

open Finset
open scoped Classical

noncomputable section

namespace WindowedLandauTheory.CyclotomicNorms

variable {A k V : Type*} [Field k] [AddCommGroup V] [Module k V] {N : ℕ}

private theorem repr_diag_apply (ρ : A → Module.End k V) (e : Module.Basis (Fin N) k V)
    (χ : Fin N → A → k) (y : A) (hy : ∀ i, ρ y (e i) = χ i y • e i) (v : V) (m : Fin N) :
    e.repr (ρ y v) m = χ m y * e.repr v m := by
  have h : ρ y v = ∑ i, (e.repr v i * χ i y) • e i := by
    conv_lhs => rw [← e.sum_repr v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hy, smul_smul]
  rw [h, e.repr_sum_self]
  exact mul_comm _ _

/-- A simultaneous eigenvector with one of the separated weights lies on its basis line. -/
theorem eigen_mem_span (ρ : A → Module.End k V) (e : Module.Basis (Fin N) k V)
    (χ : Fin N → A → k) (he : ∀ i, ∀ y, ρ y (e i) = χ i y • e i)
    (hsep : ∀ i j, i ≠ j → ∃ y, χ i y ≠ χ j y)
    (j : Fin N) (v : V) (hv : ∀ y, ρ y v = χ j y • v) : v ∈ k ∙ e j := by
  have hc : ∀ i, i ≠ j → e.repr v i = 0 := by
    intro i hij
    obtain ⟨y, hne⟩ := hsep i j hij
    have h1 := repr_diag_apply ρ e χ y (fun l => he l y) v i
    rw [hv y, map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
    have h2 : (χ j y - χ i y) * e.repr v i = 0 := by rw [sub_mul, h1, sub_self]
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (sub_eq_zero.mp h).symm hne
    · exact h
  rw [Submodule.mem_span_singleton]
  refine ⟨e.repr v j, ?_⟩
  conv_rhs => rw [← e.sum_repr v]
  symm
  exact Finset.sum_eq_single j (fun i _ hij => by rw [hc i hij, zero_smul])
    (fun h => absurd (Finset.mem_univ j) h)

/-- An invariant subspace contains every basis line on which one of its vectors has nonzero coordinate. -/
theorem mem_of_repr_ne_zero (ρ : A → Module.End k V) (e : Module.Basis (Fin N) k V)
    (χ : Fin N → A → k) (he : ∀ i, ∀ y, ρ y (e i) = χ i y • e i)
    (hsep : ∀ i j, i ≠ j → ∃ y, χ i y ≠ χ j y) (W : Submodule k V)
    (hW : ∀ y, ∀ x ∈ W, ρ y x ∈ W) :
    ∀ w ∈ W, ∀ i, e.repr w i ≠ 0 → e i ∈ W := by
  intro w hw i hi
  have key : ∀ s : Finset (Fin N), i ∉ s →
      ∃ u ∈ W, e.repr u i ≠ 0 ∧ ∀ l ∈ s, e.repr u l = 0 := by
    intro s
    refine Finset.induction_on s ?_ ?_
    · intro _
      exact ⟨w, hw, hi, fun l hl => by simp at hl⟩
    · intro j s hjs ih hi'
      have hij : i ≠ j := by
        rintro rfl
        exact hi' (Finset.mem_insert_self _ _)
      have his : i ∉ s := fun h => hi' (Finset.mem_insert_of_mem h)
      obtain ⟨u, huW, hui, hus⟩ := ih his
      obtain ⟨y, hne⟩ := hsep i j hij
      have hc : ∀ l, e.repr (ρ y u - χ j y • u) l = (χ l y - χ j y) * e.repr u l := by
        intro l
        rw [map_sub, map_smul, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
          repr_diag_apply ρ e χ y (fun m => he m y) u l, sub_mul]
      refine ⟨ρ y u - χ j y • u, W.sub_mem (hW y u huW) (W.smul_mem _ huW), ?_, ?_⟩
      · rw [hc]
        exact mul_ne_zero (sub_ne_zero.mpr hne) hui
      · intro l hl
        rw [hc]
        rcases Finset.mem_insert.mp hl with rfl | hl
        · rw [sub_self, zero_mul]
        · rw [hus l hl, mul_zero]
  obtain ⟨u, huW, hui, hus⟩ := key (Finset.univ.erase i) (by simp)
  have hu : u = e.repr u i • e i := by
    conv_lhs => rw [← e.sum_repr u]
    exact Finset.sum_eq_single i
      (fun l _ hl => by rw [hus l (Finset.mem_erase.mpr ⟨hl, Finset.mem_univ l⟩), zero_smul])
      (fun h => absurd (Finset.mem_univ i) h)
  have h2 : (e.repr u i)⁻¹ • u = e i := by
    calc (e.repr u i)⁻¹ • u = (e.repr u i)⁻¹ • (e.repr u i • e i) := by rw [← hu]
      _ = e i := by rw [smul_smul, inv_mul_cancel₀ hui, one_smul]
  rw [← h2]
  exact W.smul_mem _ huW


/-- The basis vectors whose lines lie in a given subspace. -/
def basisIndices (e : Module.Basis (Fin N) k V) (W : Submodule k V) : Finset (Fin N) :=
  Finset.univ.filter fun i => e i ∈ W

@[simp]
theorem mem_basisIndices (e : Module.Basis (Fin N) k V) (W : Submodule k V) (i : Fin N) :
    i ∈ basisIndices e W ↔ e i ∈ W := by simp [basisIndices]

/-- The dimension of a coordinate subspace is the number of basis lines it contains. -/
theorem finrank_eq_card_basisIndices (e : Module.Basis (Fin N) k V) (W : Submodule k V)
    (hW : ∀ x ∈ W, ∀ i, e.repr x i ≠ 0 → e i ∈ W) :
    Module.finrank k W = (basisIndices e W).card := by
  have hli : LinearIndependent k (fun i : (basisIndices e W) => e i) :=
    e.linearIndependent.comp _ Subtype.val_injective
  have hspan : W = Submodule.span k (Set.range fun i : (basisIndices e W) => e i) := by
    apply le_antisymm
    · intro x hx
      rw [← e.sum_repr x]
      refine Submodule.sum_mem _ (fun i _ => ?_)
      rcases eq_or_ne (e.repr x i) 0 with h | h
      · rw [h, zero_smul]
        exact Submodule.zero_mem _
      · apply Submodule.smul_mem
        exact Submodule.subset_span ⟨⟨i, (mem_basisIndices e W i).mpr (hW x hx i h)⟩, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact (mem_basisIndices e W i).mp i.2
  calc
    Module.finrank k W = Module.finrank k (Submodule.span k
        (Set.range fun i : (basisIndices e W) => e i)) :=
      congrArg (fun U : Submodule k V => Module.finrank k U) hspan
    _ = _ := (finrank_span_eq_card hli).trans (Fintype.card_coe _)

end WindowedLandauTheory.CyclotomicNorms
