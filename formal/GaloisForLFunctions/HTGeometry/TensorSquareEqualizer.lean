import GaloisForLFunctions.HTGeometry.DifferenceTensorGeneration

/-!
# The base field is the equalizer of the two embeddings into the tensor square

For a field `K` and a nonzero `K`-algebra `R`, an element of `R` satisfying `a ⊗ 1 = 1 ⊗ a` in
`R ⊗_K R` already lies in `K`.  The proof is a single linear functional: choose `f : R → K` with
`f 1 = 1`, apply `f ⊗ id`, and read off `f a · 1 = a`.

Applied to a Picard--Vessiot ring this says that a trivial comparison matrix forces the ring to be
the base field: if the two copies of the fundamental matrix agree inside the tensor square, every
entry lies in `K`, and so does the inverse of the determinant, so the whole ring collapses.  That is
the "trivial Galois group implies no extension" half of the Galois correspondence.
-/

open scoped TensorProduct

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K R : Type*} [Field K] [CommRing R] [Algebra K R]

/-- **The equalizer of the two embeddings is the base field.** -/
theorem exists_eq_algebraMap_of_tmul_comm [Nontrivial R] {a : R}
    (h : a ⊗ₜ[K] (1 : R) = (1 : R) ⊗ₜ[K] a) :
    ∃ c : K, a = algebraMap K R c := by
  obtain ⟨f, hf⟩ :=
    Module.Projective.exists_dual_eq_one (V := R) K (x := (1 : R)) one_ne_zero
  set g : (R ⊗[K] R) →ₗ[K] R :=
    (TensorProduct.lid K R).toLinearMap ∘ₗ TensorProduct.map f LinearMap.id with hg
  have hval := congrArg g h
  simp only [hg, LinearMap.coe_comp, Function.comp_apply, TensorProduct.map_tmul,
    LinearMap.id_coe, id_eq, LinearEquiv.coe_coe, TensorProduct.lid_tmul, hf, one_smul] at hval
  refine ⟨f a, ?_⟩
  have hsm : algebraMap K R (f a) = f a • (1 : R) := by rw [Algebra.smul_def, mul_one]
  rw [hsm, hval]

theorem tmul_one_eq_one_tmul_iff [Nontrivial R] {a : R} :
    a ⊗ₜ[K] (1 : R) = (1 : R) ⊗ₜ[K] a ↔ ∃ c : K, a = algebraMap K R c := by
  refine ⟨exists_eq_algebraMap_of_tmul_comm, ?_⟩
  rintro ⟨c, rfl⟩
  rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

variable {n : ℕ}

/-- **A trivial comparison matrix collapses the Picard--Vessiot ring.**  If the two copies of the
fundamental matrix agree in the tensor square, every element of the ring lies in the base field. -/
theorem eq_algebraMap_of_leftFundamental_eq_rightFundamental [Nontrivial R]
    (Y : Matrix (Fin n) (Fin n) R) (u : R) (hu : Y.det * u = 1)
    (htop : Algebra.adjoin K
      (Set.range (fun p : Fin n × Fin n => Y p.1 p.2) ∪ {u}) = ⊤)
    (hZ : leftFundamental K Y = rightFundamental K Y) (x : R) :
    ∃ c : K, x = algebraMap K R c := by
  classical
  have hY : ∀ i j : Fin n, ∃ c : K, Y i j = algebraMap K R c := by
    intro i j
    refine exists_eq_algebraMap_of_tmul_comm ?_
    exact congrFun (congrFun hZ i) j
  have hdet : Y.det ⊗ₜ[K] (1 : R) = (1 : R) ⊗ₜ[K] Y.det := by
    rw [← det_leftFundamental (K := K) Y, ← det_rightFundamental (K := K) Y, hZ]
  have hu' : u ⊗ₜ[K] (1 : R) = (1 : R) ⊗ₜ[K] u := by
    have h1 : (u ⊗ₜ[K] (1 : R)) * (Y.det ⊗ₜ[K] (1 : R)) = 1 := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_comm u Y.det, hu,
        ← Algebra.TensorProduct.one_def]
    have h2 : ((1 : R) ⊗ₜ[K] u) * (Y.det ⊗ₜ[K] (1 : R)) = 1 := by
      rw [hdet, Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_comm u Y.det, hu,
        ← Algebra.TensorProduct.one_def]
    calc u ⊗ₜ[K] (1 : R)
        = (u ⊗ₜ[K] (1 : R)) * (((1 : R) ⊗ₜ[K] u) * (Y.det ⊗ₜ[K] (1 : R))) := by
          rw [h2, mul_one]
      _ = ((u ⊗ₜ[K] (1 : R)) * (Y.det ⊗ₜ[K] (1 : R))) * ((1 : R) ⊗ₜ[K] u) := by ring
      _ = (1 : R) ⊗ₜ[K] u := by rw [h1, one_mul]
  have hubot : ∃ c : K, u = algebraMap K R c := exists_eq_algebraMap_of_tmul_comm hu'
  have hsub : (Set.range (fun p : Fin n × Fin n => Y p.1 p.2) ∪ {u})
      ⊆ ((⊥ : Subalgebra K R) : Set R) := by
    rintro y (⟨p, rfl⟩ | hy)
    · obtain ⟨c, hc⟩ := hY p.1 p.2
      exact Algebra.mem_bot.mpr ⟨c, hc.symm⟩
    · rw [Set.mem_singleton_iff] at hy
      obtain ⟨c, hc⟩ := hubot
      exact Algebra.mem_bot.mpr ⟨c, by rw [hy, hc]⟩
  have hle : (⊤ : Subalgebra K R) ≤ ⊥ := by
    rw [← htop]
    exact Algebra.adjoin_le hsub
  have hx : x ∈ (⊥ : Subalgebra K R) := hle (Algebra.mem_top)
  obtain ⟨c, hc⟩ := Algebra.mem_bot.mp hx
  exact ⟨c, hc.symm⟩

end

end GaloisForLFunctions.HTGeometry
