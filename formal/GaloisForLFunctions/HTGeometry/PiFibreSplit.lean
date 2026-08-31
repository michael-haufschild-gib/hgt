import GaloisForLFunctions.HTGeometry.FibreTransport

/-!
# The fibre of a finite product

```text
single_mem_smul_top     a single coordinate in I • ⊤ gives a vector in I • ⊤
mem_smul_top_pi_iff     ** on a finite product, I • ⊤ is exactly the coordinatewise condition **
piQuotSmulEquiv         ** hence the fibre of a finite product is the product of the fibres **
```

The forward direction of the criterion is the projection; the reverse writes a vector as the sum of
its coordinates, each of which is a single entry.  With it the quotient map splits, and the fibre
dimension of a finite product is the sum of the fibre dimensions.

This is the additivity that lets `Module.equiv_free_prod_directSum` be used: the free part
contributes the rank at every point (`finrank_quotient_finsupp`), each cyclic torsion part
contributes one dimension only where its annihilator vanishes (`finrank_quotient_span_pair`), and
the total is their sum.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Pointwise

variable {A : Type*} [CommRing A] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]

omit [Fintype ι] in
theorem single_mem_smul_top (I : Ideal A) {i : ι} {m : M i}
    (hm : m ∈ I • (⊤ : Submodule A (M i))) :
    (Pi.single i m : ∀ j, M j) ∈ I • (⊤ : Submodule A (∀ j, M j)) := by
  refine Submodule.smul_induction_on (p := fun y => (Pi.single i y : ∀ j, M j) ∈ I • ⊤) hm ?_ ?_
  · intro r hr y _
    have hy : (Pi.single i (r • y) : ∀ j, M j) = r • (Pi.single i y : ∀ j, M j) := by
      ext j
      by_cases hij : j = i
      · subst hij
        simp
      · simp [Pi.single_eq_of_ne hij]
    rw [hy]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  · intro x y hx hy
    have hxy : (Pi.single i (x + y) : ∀ j, M j)
        = (Pi.single i x : ∀ j, M j) + (Pi.single i y : ∀ j, M j) := by
      ext j
      by_cases hij : j = i
      · subst hij
        simp
      · simp [Pi.single_eq_of_ne hij]
    rw [hxy]
    exact Submodule.add_mem _ hx hy

theorem mem_smul_top_pi_iff (I : Ideal A) (x : ∀ i, M i) :
    x ∈ I • (⊤ : Submodule A (∀ i, M i)) ↔ ∀ i, x i ∈ I • (⊤ : Submodule A (M i)) := by
  constructor
  · intro hx i
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr y _
      exact Submodule.smul_mem_smul hr Submodule.mem_top
    · intro a b ha hb
      exact Submodule.add_mem _ ha hb
  · intro hx
    have hsum : x = ∑ i, (Pi.single i (x i) : ∀ j, M j) := by
      ext j
      rw [Finset.sum_apply, ← Finset.add_sum_erase _ _ (Finset.mem_univ j), Pi.single_eq_same,
        show (∑ i ∈ Finset.univ.erase j, (Pi.single i (x i) : ∀ k, M k) j) = 0 from ?_, add_zero]
      refine Finset.sum_eq_zero fun i hi => ?_
      exact Pi.single_eq_of_ne (Ne.symm (Finset.mem_erase.mp hi).1) _
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => single_mem_smul_top I (hx i)

/-- The fibre of a finite product is the product of the fibres. -/
noncomputable def piQuotSmulEquiv (I : Ideal A) :
    ((∀ i, M i) ⧸ (I • (⊤ : Submodule A (∀ i, M i))))
      ≃ₗ[A] (∀ i, (M i ⧸ (I • (⊤ : Submodule A (M i))))) := by
  classical
  set F : (∀ i, M i) →ₗ[A] (∀ i, (M i ⧸ (I • (⊤ : Submodule A (M i))))) :=
    LinearMap.pi fun i => (Submodule.mkQ (I • (⊤ : Submodule A (M i)))).comp (LinearMap.proj i)
    with hF
  have hFapp : ∀ (y : ∀ i, M i) (i : ι), F y i = Submodule.Quotient.mk (y i) := fun y i => rfl
  have hker : I • (⊤ : Submodule A (∀ i, M i)) ≤ LinearMap.ker F := by
    intro x hx
    rw [LinearMap.mem_ker]
    funext i
    rw [hFapp]
    show Submodule.Quotient.mk (x i) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact (mem_smul_top_pi_iff I x).mp hx i
  refine LinearEquiv.ofBijective (Submodule.liftQ _ F hker) ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H y =>
      rw [Submodule.liftQ_apply] at hx
      rw [Submodule.Quotient.mk_eq_zero, mem_smul_top_pi_iff]
      intro i
      have hy : Submodule.Quotient.mk (y i) = (0 : M i ⧸ (I • (⊤ : Submodule A (M i)))) := by
        rw [← hFapp y i, hx]
        rfl
      rwa [Submodule.Quotient.mk_eq_zero] at hy
  · intro g
    choose f hf using fun i => Submodule.Quotient.mk_surjective
      (I • (⊤ : Submodule A (M i))) (g i)
    refine ⟨Submodule.Quotient.mk f, ?_⟩
    rw [Submodule.liftQ_apply]
    funext i
    rw [hFapp]
    exact hf i

end GaloisForLFunctions.HTGeometry
