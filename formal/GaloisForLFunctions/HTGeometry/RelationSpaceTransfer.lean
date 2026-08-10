import GaloisForLFunctions.HTGeometry.PermutationInvariantSubspace
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Relation spaces transfer along embeddings

The rational relation space of a family lives wherever the family does, and it does not change
when the family is pushed along an injective `ℚ`-algebra map.  So rigidity may be proved where the
Galois action is available — the splitting field — and then transported to `ℂ`, where
Lindemann–Weierstrass is available.

`isPermInvariant_ker` records the source of the rigidity in that setting: a symmetric action by
ring endomorphisms of the *ambient field of the family* makes the relation space permutation
invariant.  Nothing has to be extended to an endomorphism of `ℂ`.
-/

namespace GaloisForLFunctions.HTGeometry

namespace RelationSpace

variable {ι : Type*} [Fintype ι]
variable {L : Type*} [Field L] [Algebra ℚ L]

/-- The rational linear form attached to a family in a `ℚ`-algebra. -/
noncomputable def form (E : ι → L) : (ι → ℚ) →ₗ[ℚ] L :=
  ∑ i, (LinearMap.proj i : (ι → ℚ) →ₗ[ℚ] ℚ).smulRight (E i)

@[simp]
theorem form_apply (E : ι → L) (a : ι → ℚ) : form E a = ∑ i, (a i : ℚ) • E i := by
  simp [form, LinearMap.sum_apply]

/-- **The relation space is unchanged by an injective embedding.** -/
theorem ker_form_comp {M : Type*} [Field M] [Algebra ℚ M] (f : L →ₐ[ℚ] M)
    (hf : Function.Injective f) (E : ι → L) :
    LinearMap.ker (form (fun i => f (E i))) = LinearMap.ker (form E) := by
  ext a
  simp only [LinearMap.mem_ker, form_apply]
  constructor
  · intro h
    refine hf ?_
    rw [map_sum, map_zero]
    rw [← h]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
  · intro h
    rw [← map_zero f, ← h, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul]

variable [DecidableEq ι]

omit [DecidableEq ι] in
/-- **A symmetric action by ring endomorphisms makes the relation space permutation invariant.** -/
theorem isPermInvariant_ker {E : ι → L}
    (hgal : ∀ σ : Equiv.Perm ι, ∃ φ : L →+* L, ∀ i, φ (E i) = E (σ i)) :
    PermSubspace.IsPermInvariant (LinearMap.ker (form E)) := by
  intro σ a ha
  obtain ⟨φ, hφ⟩ := hgal σ⁻¹
  rw [LinearMap.mem_ker, form_apply] at ha ⊢
  have himg : ∑ i, (a i : ℚ) • E (σ⁻¹ i) = 0 := by
    have hmap := congrArg φ ha
    rw [map_sum, map_zero] at hmap
    rw [← hmap]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Algebra.smul_def, map_mul, hφ i]
    congr 1
    simp
  calc ∑ i, ((fun j => a (σ j)) i : ℚ) • E i
      = ∑ i, (a (σ i) : ℚ) • E i := rfl
    _ = ∑ i, (a i : ℚ) • E (σ⁻¹ i) := by
        refine Fintype.sum_equiv σ _ _ fun i => ?_
        simp
    _ = 0 := himg

/-- **The trace relation is the only one.** -/
theorem ker_form_eq_constLine {E : ι → L} [Nonempty ι]
    (hgal : ∀ σ : Equiv.Perm ι, ∃ φ : L →+* L, ∀ i, φ (E i) = E (σ i))
    (htrace : ∑ i, E i = 0) (hne : ∃ i, E i ≠ 0) :
    LinearMap.ker (form E) = PermSubspace.constLine (K := ℚ) (ι := ι) := by
  classical
  refine PermSubspace.eq_constLine_of_le_of_ne_top _ (isPermInvariant_ker hgal) ?_ ?_ ?_
  · exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  · intro a ha
    obtain ⟨c, rfl⟩ := PermSubspace.eq_const_of_mem_constLine ha
    rw [LinearMap.mem_ker, form_apply]
    have hfac : ∑ i, (c : ℚ) • E i = (algebraMap ℚ L c) * ∑ i, E i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [Algebra.smul_def]
    rw [hfac, htrace, mul_zero]
  · intro htop
    obtain ⟨i₀, hi₀⟩ := hne
    have hmem : (fun i => if i = i₀ then (1 : ℚ) else 0) ∈ LinearMap.ker (form E) := by
      rw [htop]; exact Submodule.mem_top
    rw [LinearMap.mem_ker, form_apply] at hmem
    rw [Finset.sum_eq_single i₀] at hmem
    · simp at hmem
      exact hi₀ hmem
    · intro b _ hb
      simp [hb]
    · intro hb
      exact absurd (Finset.mem_univ i₀) hb

/-! ## The rank of the family -/

/-- The range of the relation form is the `ℚ`-span of the family. -/
theorem range_form (E : ι → L) :
    LinearMap.range (form E) = Submodule.span ℚ (Set.range E) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨a, rfl⟩
    rw [form_apply]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨fun j => if j = i then 1 else 0, ?_⟩
    rw [form_apply, Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [hb]
    · intro hb; exact absurd (Finset.mem_univ i) hb

omit [Fintype ι] [DecidableEq ι] in
/-- The constant line is one-dimensional. -/
theorem finrank_constLine [Nonempty ι] :
    Module.finrank ℚ (PermSubspace.constLine (K := ℚ) (ι := ι)) = 1 := by
  refine finrank_span_singleton ?_
  intro h
  have := congrFun h (Classical.arbitrary ι)
  simp at this

/-- **The rank of a rigid family.**  If the only rational relation is the trace relation, the
`ℚ`-span of the family has dimension one less than the number of members. -/
theorem finrank_span_eq_card_sub_one [Nonempty ι] {E : ι → L}
    (h : LinearMap.ker (form E) = PermSubspace.constLine (K := ℚ) (ι := ι)) :
    Module.finrank ℚ (Submodule.span ℚ (Set.range E)) = Fintype.card ι - 1 := by
  have hrank := LinearMap.finrank_range_add_finrank_ker (form E)
  rw [range_form, h, finrank_constLine, Module.finrank_pi] at hrank
  omega

end RelationSpace

end GaloisForLFunctions.HTGeometry
