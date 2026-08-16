import GaloisForLFunctions.HTGeometry.CentralCasimirComplementHallExpansion

/-!
# Splitting an invariant subspace along the common kernel

The quadratic Casimir of a Hermitian matrix family is self-adjoint, its kernel is the simultaneous
kernel of the family, and its range is orthogonal to that kernel.  A subspace invariant under the
Casimir therefore splits: the kernel part is its own intersection with the simultaneous kernel, and
everything else already lies in the orthogonal complement.  No spectral projector and no averaging
is needed — kernel and range of an endomorphism with trivial overlap already exhaust the space.
-/

open Finset Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- An endomorphism whose kernel meets its range trivially has kernel and range spanning. -/
theorem endomorphism_ker_sup_range_eq_top {𝕜 V : Type*} [DivisionRing 𝕜] [AddCommGroup V]
    [Module 𝕜 V] [FiniteDimensional 𝕜 V] (f : V →ₗ[𝕜] V)
    (h : LinearMap.ker f ⊓ LinearMap.range f = ⊥) :
    LinearMap.ker f ⊔ LinearMap.range f = ⊤ := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker f) (LinearMap.range f)
  have h2 := LinearMap.finrank_range_add_finrank_ker f
  rw [h, finrank_bot] at h1
  refine Submodule.eq_top_of_finrank_eq ?_
  omega

section AbstractSplit

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

/-- **A subspace invariant under a self-adjoint operator splits along that operator's kernel.** -/
theorem invariantSubspace_le_ker_sup_orthogonal (K : V →ₗ[ℂ] V) (S U : Submodule ℂ V)
    (hKU : ∀ x ∈ U, K x ∈ U)
    (hker : ∀ x : V, K x = 0 ↔ x ∈ S)
    (hrange : ∀ x : V, K x ∈ Sᗮ) :
    U ≤ (U ⊓ S) ⊔ (U ⊓ Sᗮ) := by
  classical
  set KU : U →ₗ[ℂ] U := (K.domRestrict U).codRestrict U (fun x => hKU x x.2) with hKUdef
  have hval : ∀ y : U, ((KU y : U) : V) = K (y : V) := fun _ => rfl
  have hdisj : LinearMap.ker KU ⊓ LinearMap.range KU = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hy1, hy2⟩
    obtain ⟨z, hz⟩ := hy2
    have h1 : ((y : V)) ∈ S := by
      refine (hker _).mp ?_
      rw [← hval y, LinearMap.mem_ker.mp hy1]
      rfl
    have h2 : ((y : V)) ∈ Sᗮ := by
      rw [← hz, hval z]
      exact hrange _
    have hzero : (y : V) = 0 :=
      (Submodule.mem_bot ℂ).mp ((Submodule.orthogonal_disjoint S).le_bot ⟨h1, h2⟩)
    exact (Submodule.mem_bot ℂ).mpr (Subtype.ext hzero)
  have htop : LinearMap.ker KU ⊔ LinearMap.range KU = ⊤ :=
    endomorphism_ker_sup_range_eq_top KU hdisj
  intro x hx
  have hmem : (⟨x, hx⟩ : U) ∈ LinearMap.ker KU ⊔ LinearMap.range KU := by
    rw [htop]
    trivial
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
  have hxval : x = (a : V) + (b : V) := congrArg Subtype.val hab.symm
  have haS : (a : V) ∈ U ⊓ S := by
    refine ⟨a.2, (hker _).mp ?_⟩
    rw [← hval a, LinearMap.mem_ker.mp ha]
    rfl
  have hbW : (b : V) ∈ U ⊓ Sᗮ := by
    refine ⟨b.2, ?_⟩
    obtain ⟨z, hz⟩ := hb
    rw [← hz, hval z]
    exact hrange _
  rw [hxval]
  exact Submodule.add_mem _ (Submodule.mem_sup_left haS) (Submodule.mem_sup_right hbW)

end AbstractSplit

section Concrete

variable {D J : Type*} [Fintype D] [DecidableEq D] [Fintype J]

/-- The quadratic Casimir of a Hermitian matrix family, as an operator. -/
def hermitianFamilyCasimirOperator (M : J → Matrix D D ℂ) :
    EuclideanSpace ℂ D →ₗ[ℂ] EuclideanSpace ℂ D :=
  ∑ j, (M j).toEuclideanLin ∘ₗ (M j).toEuclideanLin

theorem hermitianFamilyCasimirOperator_apply (M : J → Matrix D D ℂ) (x : EuclideanSpace ℂ D) :
    hermitianFamilyCasimirOperator M x = ∑ j, (M j).toEuclideanLin ((M j).toEuclideanLin x) := by
  rw [hermitianFamilyCasimirOperator]
  simp

theorem adjoint_toEuclideanLin_of_hermitian {M : Matrix D D ℂ} (hM : Mᴴ = M) :
    LinearMap.adjoint M.toEuclideanLin = M.toEuclideanLin := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint, hM]

theorem inner_hermitianFamilyCasimir_self (M : J → Matrix D D ℂ) (hM : ∀ j, (M j)ᴴ = M j)
    (x : EuclideanSpace ℂ D) :
    @inner ℂ _ _ x (hermitianFamilyCasimirOperator M x) =
      ∑ j, ((‖(M j).toEuclideanLin x‖ : ℂ)) ^ 2 := by
  rw [hermitianFamilyCasimirOperator_apply, inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← adjoint_toEuclideanLin_of_hermitian (hM j), LinearMap.adjoint_inner_right,
    adjoint_toEuclideanLin_of_hermitian (hM j)]
  exact inner_self_eq_norm_sq_to_K (𝕜 := ℂ) _

theorem hermitianFamilyCasimir_eq_zero_iff (M : J → Matrix D D ℂ) (hM : ∀ j, (M j)ᴴ = M j)
    (x : EuclideanSpace ℂ D) :
    hermitianFamilyCasimirOperator M x = 0 ↔ x ∈ hermitianMatrixFamilyCommonKernel M := by
  classical
  constructor
  · intro hzero
    have hinner : @inner ℂ _ _ x (hermitianFamilyCasimirOperator M x) = 0 := by
      rw [hzero, inner_zero_right]
    rw [inner_hermitianFamilyCasimir_self M hM] at hinner
    have hreal : (∑ j, ‖(M j).toEuclideanLin x‖ ^ 2) = 0 := by
      have hcast : ((∑ j, ‖(M j).toEuclideanLin x‖ ^ 2 : ℝ) : ℂ) = 0 := by
        push_cast
        exact hinner
      exact_mod_cast hcast
    rw [hermitianMatrixFamilyCommonKernel, Submodule.mem_iInf]
    intro j
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j' _ => sq_nonneg _)).mp hreal j (Finset.mem_univ j)
    exact LinearMap.mem_ker.mpr (norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
      hterm))
  · intro hx
    rw [hermitianMatrixFamilyCommonKernel, Submodule.mem_iInf] at hx
    rw [hermitianFamilyCasimirOperator_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [LinearMap.mem_ker.mp (hx j), map_zero]

theorem hermitianFamilyCasimir_mem_orthogonal (M : J → Matrix D D ℂ) (hM : ∀ j, (M j)ᴴ = M j)
    (x : EuclideanSpace ℂ D) :
    hermitianFamilyCasimirOperator M x ∈ (hermitianMatrixFamilyCommonKernel M)ᗮ := by
  classical
  rw [Submodule.mem_orthogonal]
  intro u hu
  rw [hermitianMatrixFamilyCommonKernel, Submodule.mem_iInf] at hu
  rw [hermitianFamilyCasimirOperator_apply, inner_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [← adjoint_toEuclideanLin_of_hermitian (hM j), LinearMap.adjoint_inner_right,
    adjoint_toEuclideanLin_of_hermitian (hM j), LinearMap.mem_ker.mp (hu j), inner_zero_left]

/-- **A subspace invariant under the family Casimir splits along the simultaneous kernel.** -/
theorem invariantSubspace_le_commonKernel_sup_orthogonal (M : J → Matrix D D ℂ)
    (hM : ∀ j, (M j)ᴴ = M j) (U : Submodule ℂ (EuclideanSpace ℂ D))
    (hKU : ∀ x ∈ U, hermitianFamilyCasimirOperator M x ∈ U) :
    U ≤ (U ⊓ hermitianMatrixFamilyCommonKernel M) ⊔
      (U ⊓ (hermitianMatrixFamilyCommonKernel M)ᗮ) :=
  invariantSubspace_le_ker_sup_orthogonal (hermitianFamilyCasimirOperator M)
    (hermitianMatrixFamilyCommonKernel M) U hKU
    (hermitianFamilyCasimir_eq_zero_iff M hM) (hermitianFamilyCasimir_mem_orthogonal M hM)

end Concrete

end GaloisForLFunctions.HTGeometry
