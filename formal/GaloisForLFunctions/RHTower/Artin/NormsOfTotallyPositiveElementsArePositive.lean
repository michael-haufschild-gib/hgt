import GaloisForLFunctions.HeckeLFunctions.ElementsPrimeToAModulusReduceModuloIt

/-!
# Signs and congruences of norms in a number field

* **The norm of an element that is positive at every real place is positive**
  (`norm_pos_of_forall_isReal_pos`). The norm is the product of the conjugates; the conjugates
  above a real place are one positive number, and those above a complex place are a pair
  `σ(α), conj σ(α)` with product `|σ(α)|²`.
* **Congruent integers have congruent norms** (`intCast_norm_eq_of_sub_mem`): if
  `a ≡ b mod m 𝓞_K`, then `N(a) ≡ N(b) mod m`. The norm is the determinant of the
  multiplication on an integral basis, and the two matrices are congruent modulo `m`.
-/

open scoped Classical BigOperators NumberField
open NumberField

noncomputable section

namespace GaloisForLFunctions

variable {K : Type*} [Field K] [NumberField K]

/-- The product of the conjugates of `α ≠ 0` above one infinite place is a positive real
number, if `α` is positive at that place when the place is real. -/
theorem exists_pos_prod_embeddings_above (w : InfinitePlace K) {α : K} (hα : α ≠ 0)
    (h : ∀ hw : w.IsReal, 0 < InfinitePlace.embedding_of_isReal hw α) :
    ∃ r : ℝ, 0 < r ∧
      ∏ φ ∈ Finset.univ.filter (fun φ : K →+* ℂ => InfinitePlace.mk φ = w), φ α = (r : ℂ) := by
  -- the embeddings above `w` are an embedding and its conjugate
  have hset : Finset.univ.filter (fun φ : K →+* ℂ => InfinitePlace.mk φ = w) =
      {w.embedding, ComplexEmbedding.conjugate w.embedding} := by
    ext φ
    rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨-, hφ⟩
      exact (InfinitePlace.mk_eq_iff.mp ((InfinitePlace.mk_embedding w).trans hφ.symm)).imp
        Eq.symm Eq.symm
    · rintro (rfl | rfl)
      · exact ⟨Finset.mem_univ _, InfinitePlace.mk_embedding w⟩
      · exact ⟨Finset.mem_univ _,
          (InfinitePlace.mk_conjugate_eq _).trans (InfinitePlace.mk_embedding w)⟩
  rw [hset]
  by_cases hw : w.IsReal
  · have hconj : ComplexEmbedding.conjugate w.embedding = w.embedding :=
      ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_iff.mp hw)
    refine ⟨InfinitePlace.embedding_of_isReal hw α, h hw, ?_⟩
    rw [hconj, Finset.pair_eq_singleton, Finset.prod_singleton,
      InfinitePlace.embedding_of_isReal_apply]
  · have hconj : w.embedding ≠ ComplexEmbedding.conjugate w.embedding := fun hc =>
      hw (InfinitePlace.isReal_iff.mpr (ComplexEmbedding.isReal_iff.mpr hc.symm))
    refine ⟨Complex.normSq (w.embedding α), Complex.normSq_pos.mpr ((map_ne_zero _).mpr hα), ?_⟩
    rw [Finset.prod_pair hconj, ComplexEmbedding.conjugate_coe_eq, Complex.mul_conj]

/-- **The norm of an element positive at every real place is positive.** -/
theorem norm_pos_of_forall_isReal_pos {α : K} (hα : α ≠ 0)
    (h : ∀ (w : InfinitePlace K) (hw : w.IsReal),
      0 < InfinitePlace.embedding_of_isReal hw α) :
    0 < Algebra.norm ℚ α := by
  choose r hr hprod using fun w : InfinitePlace K => exists_pos_prod_embeddings_above w hα (h w)
  -- the norm is the product of the conjugates, grouped by infinite place
  have hnorm : ((Algebra.norm ℚ α : ℚ) : ℂ) = ((∏ w : InfinitePlace K, r w : ℝ) : ℂ) := by
    rw [← eq_ratCast (algebraMap ℚ ℂ), Algebra.norm_eq_prod_embeddings ℚ ℂ α,
      ← Fintype.prod_equiv RingHom.equivRatAlgHom (fun φ : K →+* ℂ => φ α)
        (fun φ : K →ₐ[ℚ] ℂ => φ α) (fun _ => rfl),
      ← Finset.prod_fiberwise Finset.univ InfinitePlace.mk (fun φ : K →+* ℂ => φ α),
      Complex.ofReal_prod]
    exact Finset.prod_congr rfl fun w _ => hprod w
  have hreal : ((Algebra.norm ℚ α : ℚ) : ℝ) = ∏ w : InfinitePlace K, r w :=
    Complex.ofReal_injective (by rw [← hnorm, Complex.ofReal_ratCast])
  have hpos : (0 : ℝ) < ((Algebra.norm ℚ α : ℚ) : ℝ) := by
    rw [hreal]
    exact Finset.prod_pos fun w _ => hr w
  exact Rat.cast_pos.mp hpos

/-- **Congruent integers have congruent norms**: if `a ≡ b` modulo `m 𝓞_K`, then
`N(a) ≡ N(b)` modulo `m`. -/
theorem intCast_norm_eq_of_sub_mem {m : ℕ} {a b : 𝓞 K}
    (h : a - b ∈ Ideal.span {(m : 𝓞 K)}) :
    ((Algebra.norm ℤ a : ℤ) : ZMod m) = ((Algebra.norm ℤ b : ℤ) : ZMod m) := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h
  have ha : a = b + m • c := by
    rw [nsmul_eq_mul]
    linear_combination (-1 : 𝓞 K) * hc
  -- the matrices of the multiplications by `a` and `b` agree modulo `m`
  show Int.castRingHom (ZMod m) (Algebra.norm ℤ a) = Int.castRingHom (ZMod m) (Algebra.norm ℤ b)
  rw [Algebra.norm_eq_matrix_det (NumberField.RingOfIntegers.basis K),
    Algebra.norm_eq_matrix_det (NumberField.RingOfIntegers.basis K), RingHom.map_det,
    RingHom.map_det, ha, map_add, map_nsmul, map_add, map_nsmul,
    ← Nat.cast_smul_eq_nsmul (ZMod m), ZMod.natCast_self, zero_smul, add_zero]

end GaloisForLFunctions
