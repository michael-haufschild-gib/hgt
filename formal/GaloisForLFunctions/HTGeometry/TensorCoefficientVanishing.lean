import Mathlib

/-!
# Tensor coefficient vanishing and operator-Schmidt commutator collapse

Over a field, a tensor `∑_i c_i ⊗ e_i` with a linearly independent family `{e_i}` vanishes only when
every coefficient `c_i` vanishes (`tensor_coeff_eq_zero`).  This is the linear-algebra crux behind the
operator-Schmidt step in factorising-scattering rigidity: if the flip-removed left operator has
minimal operator-Schmidt decomposition `L = ∑_a A_a ⊗ B_a` with linearly independent right family,
the paired commutator identity `∑_{a,b} ⁅A_a,A_b⁆ ⊗ B_a ⊗ B_b = 0` forces every `⁅A_a,A_b⁆ = 0`
(`schmidt_commutator_vanish`).  Combined with the zero-anchor commutation law
`braidZeroAnchor_commute`, this is the algebraic half of local product diagonality.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped TensorProduct BigOperators

/-- **Tensor coefficient vanishing.**  Over a field, if a finite tensor sum `∑_{i∈s} c_i ⊗ e_i`
vanishes and the family `{e_i}` is linearly independent, then every coefficient `c_i` (`i ∈ s`)
vanishes.  Proved by applying a coordinate functional (extended off the span) to the second factor. -/
theorem tensor_coeff_eq_zero {K M N ι : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] {e : ι → N} (he : LinearIndependent K e)
    (c : ι → M) (s : Finset ι) (h : ∑ i ∈ s, c i ⊗ₜ[K] e i = 0) (i : ι) (hi : i ∈ s) :
    c i = 0 := by
  classical
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend ((Finsupp.lapply i).comp he.repr)
  have hφe : ∀ j : ι, φ (e j) = ((Finsupp.single j (1 : K)) i : K) := by
    intro j
    have hmem : e j ∈ Submodule.span K (Set.range e) :=
      Submodule.subset_span (Set.mem_range_self j)
    have hval : φ (e j) = ((Finsupp.lapply i).comp he.repr) ⟨e j, hmem⟩ := by
      have := LinearMap.congr_fun hφ ⟨e j, hmem⟩
      simpa using this
    rw [hval]
    simp only [LinearMap.comp_apply, Finsupp.lapply_apply]
    rw [he.repr_eq_single j ⟨e j, hmem⟩ rfl]
  have key := congrArg
    (fun t => (TensorProduct.rid K M) (TensorProduct.map LinearMap.id φ t)) h
  simp only [map_sum, map_zero] at key
  have hterm : ∀ j : ι,
      (TensorProduct.rid K M) (TensorProduct.map LinearMap.id φ (c j ⊗ₜ[K] e j))
        = φ (e j) • c j := by
    intro j; simp [TensorProduct.map_tmul, TensorProduct.rid_tmul]
  simp only [hterm, hφe, Finsupp.single_apply, ite_smul, one_smul, zero_smul] at key
  rw [Finset.sum_ite_eq' s i c] at key
  simpa [hi] using key

/-- **Operator-Schmidt commutator collapse (equations (7)→(8)).**  In an algebra `R` over a field,
if the paired commutator tensor `∑_{(a,b)∈ s×s} ⁅A_a,A_b⁆ ⊗ (B_a ⊗ B_b)` vanishes and the
tensor-square family `{B_a ⊗ B_b}` is linearly independent, then every commutator `⁅A_a,A_b⁆`
vanishes on `s`. -/
theorem schmidt_commutator_vanish {K R ι : Type*} [Field K] [Ring R] [Algebra K R]
    (A B : ι → R) (s : Finset ι)
    (hB : LinearIndependent K (fun p : ι × ι => B p.1 ⊗ₜ[K] B p.2))
    (h : ∑ p ∈ s ×ˢ s, ⁅A p.1, A p.2⁆ ⊗ₜ[K] (B p.1 ⊗ₜ[K] B p.2) = 0)
    (a b : ι) (ha : a ∈ s) (hb : b ∈ s) :
    ⁅A a, A b⁆ = 0 :=
  tensor_coeff_eq_zero hB (fun p : ι × ι => ⁅A p.1, A p.2⁆) (s ×ˢ s) h (a, b)
    (Finset.mem_product.mpr ⟨ha, hb⟩)

/-- **Tensor of linearly independent families is linearly independent** (a mathlib gap).  Over a
field with finite index types, `{v_i}` and `{w_j}` linearly independent imply `{v_i ⊗ w_j}` linearly
independent.  Proved by regrouping the vanishing relation into the second factor and applying
`tensor_coeff_eq_zero`, then linear independence of `{v_i}`. -/
theorem tmul_linearIndependent {K M N ι κ : Type*} [Field K] [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [Fintype ι] [Fintype κ] {v : ι → M} {w : κ → N}
    (hv : LinearIndependent K v) (hw : LinearIndependent K w) :
    LinearIndependent K (fun p : ι × κ => v p.1 ⊗ₜ[K] w p.2) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hsum p
  have hregr : ∑ j : κ, (∑ i : ι, g (i, j) • v i) ⊗ₜ[K] w j = 0 := by
    have heq : (∑ j : κ, (∑ i : ι, g (i, j) • v i) ⊗ₜ[K] w j)
        = ∑ q : ι × κ, g q • (v q.1 ⊗ₜ[K] w q.2) := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl; intro j _
      rw [TensorProduct.sum_tmul]
      apply Finset.sum_congr rfl; intro i _
      rw [TensorProduct.smul_tmul']
    rw [heq, hsum]
  have hj : ∀ j : κ, ∑ i : ι, g (i, j) • v i = 0 :=
    fun j => tensor_coeff_eq_zero hw (fun j => ∑ i : ι, g (i, j) • v i) Finset.univ hregr j
      (Finset.mem_univ j)
  exact (Fintype.linearIndependent_iff.mp hv (fun i => g (i, p.2)) (hj p.2)) p.1

/-- **Operator-Schmidt commutator collapse, hypothesis-free.**  For a finite operator-Schmidt right
family `B : ι → R` that is linearly independent, the paired commutator relation
`∑_{a,b} ⁅A_a,A_b⁆ ⊗ (B_a ⊗ B_b) = 0` forces every commutator `⁅A_a,A_b⁆ = 0` — the tensor-square
independence needed by `schmidt_commutator_vanish` is discharged by `tmul_linearIndependent`. -/
theorem schmidt_commutator_vanish_of_linearIndependent {K R ι : Type*} [Field K] [Ring R]
    [Algebra K R] [Fintype ι] (A B : ι → R) (hB : LinearIndependent K B)
    (h : ∑ p : ι × ι, ⁅A p.1, A p.2⁆ ⊗ₜ[K] (B p.1 ⊗ₜ[K] B p.2) = 0) (a b : ι) :
    ⁅A a, A b⁆ = 0 :=
  tensor_coeff_eq_zero (tmul_linearIndependent hB hB) (fun p : ι × ι => ⁅A p.1, A p.2⁆)
    Finset.univ h (a, b) (Finset.mem_univ _)

end GaloisForLFunctions.HTGeometry
