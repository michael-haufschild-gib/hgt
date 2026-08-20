import GaloisForLFunctions.HTGeometry.TorsorDecomposition
import GaloisForLFunctions.HTGeometry.PointSubsetSeparateModule

/-!
# The specialisations of a torsor separate its points

A point of the group specialises the torsor: through the decomposition `A ≅ R ⊗_C E`, evaluating
the constants at a `C`-point of `E` gives an `R`-algebra map `A → R`.  Writing an element of `A` in
a `C`-basis of `E` turns its value at such a point into a `C`-linear combination of the basis
values, so separation of points on `E` — the Nullstellensatz for a reduced finite-type algebra over
an algebraically closed field — forces all the coefficients, hence the element itself, to vanish.

The consequence recorded here is the one difference Galois theory uses: if two elements of `R` are
proportional after every specialisation, then the corresponding products of the two embeddings into
`A` agree.  For a Picard--Vessiot ring and its tensor square that is the identity `y ⊗ z = z ⊗ y`.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct

variable {C R A : Type*} [Field C] [CommRing R] [CommRing A]
  [Algebra C R] [Algebra C A] [Algebra R A] [IsScalarTower C R A]

/-- The specialisation of the torsor at a point of the group: the `R`-algebra map `A → R` obtained
by evaluating the constants at the point. -/
def torsorSpecialization (E : Subalgebra C A) {ι : Type*} (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C (Set.range (algebraMap R A) ∪ (E : Set A)) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : A)))
    (χ : E →ₐ[C] C) : A →ₐ[R] R :=
  (Algebra.TensorProduct.lift (AlgHom.id R R) ((Algebra.ofId C R).comp χ)
      (fun _ _ => Commute.all _ _)).comp
    (tensorDecompositionEquiv E b hgen hindep).symm.toAlgHom

theorem torsorSpecialization_apply (E : Subalgebra C A) {ι : Type*} (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C (Set.range (algebraMap R A) ∪ (E : Set A)) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : A)))
    (χ : E →ₐ[C] C) (r : R) (e : E) :
    torsorSpecialization E b hgen hindep χ
        (tensorDecompositionEquiv E b hgen hindep (r ⊗ₜ[C] e)) = r * algebraMap C R (χ e) := by
  show (Algebra.TensorProduct.lift (AlgHom.id R R) ((Algebra.ofId C R).comp χ)
      (fun _ _ => Commute.all _ _))
      ((tensorDecompositionEquiv E b hgen hindep).symm
        (tensorDecompositionEquiv E b hgen hindep (r ⊗ₜ[C] e))) = _
  rw [AlgEquiv.symm_apply_apply, Algebra.TensorProduct.lift_tmul]
  rfl

/-- **A separating set of points separates the torsor.** -/
theorem eq_zero_of_forall_torsorSpecialization_subset_eq_zero
    (E : Subalgebra C A)
    {ι : Type*} (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C (Set.range (algebraMap R A) ∪ (E : Set A)) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : A)))
    (S : Set (E →ₐ[C] C)) (hsep : ∀ e : E, (∀ χ ∈ S, χ e = 0) → e = 0)
    {w : A} (h : ∀ χ ∈ S, torsorSpecialization E b hgen hindep χ w = 0) : w = 0 := by
  classical
  set iso := tensorDecompositionEquiv E b hgen hindep with hiso
  set x : R ⊗[C] E := iso.symm w with hx
  set bR : Module.Basis ι R (R ⊗[C] E) := Module.Basis.baseChange R b with hbR
  set f : ι →₀ R := bR.repr x with hf
  have hxsum : x = ∑ i ∈ f.support, (f i) ⊗ₜ[C] (b i) := by
    conv_lhs => rw [← bR.linearCombination_repr x]
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hbR, Module.Basis.baseChange_apply, TensorProduct.smul_tmul']
    congr 1
    rw [smul_eq_mul, mul_one]
  have hw : w = iso x := by rw [hx, AlgEquiv.apply_symm_apply]
  have hval : ∀ χ ∈ S, ∑ i ∈ f.support, (χ (b i)) • (f i) = 0 := by
    intro χ hχ
    have hspec := h χ hχ
    rw [hw, hxsum, map_sum, map_sum] at hspec
    rw [← hspec]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [torsorSpecialization_apply, Algebra.smul_def]
    ring
  set n := f.support.card with hn
  set g : Fin n ≃ (f.support : Finset ι) := (f.support.equivFin).symm with hg
  set bb : Fin n → E := fun j => b ((g j : ι)) with hbb
  set rr : Fin n → R := fun j => f ((g j : ι)) with hrr
  have hginj : Function.Injective (fun j : Fin n => ((g j : ι))) := by
    intro j₁ j₂ hj
    exact g.injective (Subtype.ext hj)
  have hbbindep : ∀ c : Fin n → C, (∑ j, c j • bb j) = 0 → ∀ j, c j = 0 := by
    intro c hc
    have hli : LinearIndependent C bb := by
      rw [hbb]
      exact b.linearIndependent.comp _ hginj
    exact Fintype.linearIndependent_iff.mp hli c hc
  have hsum : ∀ χ ∈ S, (∑ j, (χ (bb j)) • rr j) = 0 := by
    intro χ hχ
    have hre : ∑ j : Fin n, (χ (bb j)) • rr j
        = ∑ i ∈ f.support, (χ (b i)) • (f i) := by
      rw [← Finset.sum_coe_sort f.support (fun i => (χ (b (i : ι))) • (f (i : ι)))]
      exact Fintype.sum_equiv g _ _ fun j => rfl
    rw [hre]
    exact hval χ hχ
  have hzero := eq_zero_of_forall_pointSubset_smul_eq_zero S hsep bb hbbindep rr hsum
  have hfzero : f = 0 := by
    ext i
    by_cases hi : i ∈ f.support
    · have hthis := hzero (g.symm ⟨i, hi⟩)
      rw [hrr] at hthis
      simp only at hthis
      have hval2 : ((g (g.symm ⟨i, hi⟩) : ι)) = i := by
        rw [Equiv.apply_symm_apply]
      rw [hval2] at hthis
      rw [hthis, Finsupp.coe_zero, Pi.zero_apply]
    · rw [Finsupp.notMem_support_iff.mp hi, Finsupp.coe_zero, Pi.zero_apply]
  have hxzero : x = 0 := by
    apply bR.repr.injective
    rw [← hf, hfzero]
    simp
  rw [hw, hxzero, map_zero]

/-- **The specialisations of a torsor separate its points.** -/
theorem eq_zero_of_forall_torsorSpecialization_eq_zero [IsAlgClosed C]
    (E : Subalgebra C A) [IsReduced E] [Algebra.FiniteType C E]
    {ι : Type*} (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C (Set.range (algebraMap R A) ∪ (E : Set A)) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : A)))
    {w : A} (h : ∀ χ : E →ₐ[C] C, torsorSpecialization E b hgen hindep χ w = 0) : w = 0 :=
  eq_zero_of_forall_torsorSpecialization_subset_eq_zero E b hgen hindep Set.univ
    (fun _ he => eq_zero_of_forall_algHom_eq_zero (fun χ => he χ (Set.mem_univ χ)))
    (fun χ _ => h χ)

/-- **Semi-invariance under a separating set of specialisations is a symmetry of the tensor
square.** -/
theorem mul_comm_embeddings_of_forall_specialization_subset
    (E : Subalgebra C A)
    {ι : Type*} (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C (Set.range (algebraMap R A) ∪ (E : Set A)) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : A)))
    (S : Set (E →ₐ[C] C)) (hsep : ∀ e : E, (∀ χ ∈ S, χ e = 0) → e = 0)
    (ρ : R →ₐ[C] A) {r₁ r₂ : R}
    (h : ∀ χ ∈ S,
      r₁ * (torsorSpecialization E b hgen hindep χ) (ρ r₂)
        = r₂ * (torsorSpecialization E b hgen hindep χ) (ρ r₁)) :
    algebraMap R A r₁ * ρ r₂ = algebraMap R A r₂ * ρ r₁ := by
  have hz : algebraMap R A r₁ * ρ r₂ - algebraMap R A r₂ * ρ r₁ = 0 := by
    refine eq_zero_of_forall_torsorSpecialization_subset_eq_zero E b hgen hindep S hsep ?_
    intro χ hχ
    rw [map_sub, map_mul, map_mul]
    have hcomm₁ : (torsorSpecialization E b hgen hindep χ) (algebraMap R A r₁) = r₁ := by
      rw [AlgHom.commutes]
      simp
    have hcomm₂ : (torsorSpecialization E b hgen hindep χ) (algebraMap R A r₂) = r₂ := by
      rw [AlgHom.commutes]
      simp
    rw [hcomm₁, hcomm₂, h χ hχ, sub_self]
  exact sub_eq_zero.mp hz

/-- **Semi-invariance under every specialisation is a symmetry of the tensor square.** -/
theorem mul_comm_embeddings_of_forall_specialization [IsAlgClosed C]
    (E : Subalgebra C A) [IsReduced E] [Algebra.FiniteType C E]
    {ι : Type*} (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C (Set.range (algebraMap R A) ∪ (E : Set A)) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : A)))
    (ρ : R →ₐ[C] A) {r₁ r₂ : R}
    (h : ∀ χ : E →ₐ[C] C,
      r₁ * (torsorSpecialization E b hgen hindep χ) (ρ r₂)
        = r₂ * (torsorSpecialization E b hgen hindep χ) (ρ r₁)) :
    algebraMap R A r₁ * ρ r₂ = algebraMap R A r₂ * ρ r₁ :=
  mul_comm_embeddings_of_forall_specialization_subset E b hgen hindep Set.univ
    (fun _ he => eq_zero_of_forall_algHom_eq_zero (fun χ => he χ (Set.mem_univ χ)))
    ρ (fun χ _ => h χ)

end

end GaloisForLFunctions.HTGeometry
