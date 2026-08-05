import GaloisForLFunctions.HTGeometry.VisibleKernelRecoveryHallExpansion

/-!
# Visible recovery modulo an unavoidable common kernel

Visible-kernel recovery need not be injective when a physical family has
universal zero modes. Retaining the second rank-nullity term gives the exact
correction: output loses only the recovery kernel. If those zero directions
lie in a specified common-kernel subspace, only the part of source input in
that subspace is charged.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Visible-kernel recovery with a possibly noninjective return. The exact
dimension loss is the finrank of the return kernel. -/
theorem visibleKernelRecovery_subspace_finrank_with_kernel
    {K X Z : Type*}
    [Field K]
    [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    [AddCommGroup Z] [Module K Z]
    (S W Uₛ U_w C Yout : Submodule K X)
    (F : Uₛ →ₗ[K] Z)
    (R : LinearMap.ker F →ₗ[K] X)
    (hSW : Disjoint S W)
    (hUₛS : Uₛ ≤ S)
    (hUwW : U_w ≤ W)
    (hCW : C ≤ W)
    (hRrangeS : LinearMap.range R ≤ S)
    (hvisible : Module.finrank K (LinearMap.range F) +
        Module.finrank K U_w ≤
      Module.finrank K ((U_w ⊔ C) : Submodule K X))
    (hout : (U_w ⊔ C) ⊔ LinearMap.range R ≤ Yout) :
    Module.finrank K ((Uₛ ⊔ U_w) : Submodule K X) ≤
      Module.finrank K Yout + Module.finrank K (LinearMap.ker R) := by
  have hinputDisjoint : Disjoint Uₛ U_w := hSW.mono hUₛS hUwW
  have hvisibleW : U_w ⊔ C ≤ W := sup_le hUwW hCW
  have houtputDisjoint : Disjoint (U_w ⊔ C) (LinearMap.range R) :=
    hSW.symm.mono hvisibleW hRrangeS
  have hinput := Submodule.finrank_sup_add_finrank_inf_eq Uₛ U_w
  have houtput := Submodule.finrank_sup_add_finrank_inf_eq
    (U_w ⊔ C) (LinearMap.range R)
  rw [disjoint_iff.mp hinputDisjoint, finrank_bot] at hinput
  rw [disjoint_iff.mp houtputDisjoint, finrank_bot] at houtput
  have hFnullity := LinearMap.finrank_range_add_finrank_ker F
  have hRnullity := LinearMap.finrank_range_add_finrank_ker R
  have houtRank : Module.finrank K
      (((U_w ⊔ C) ⊔ LinearMap.range R) : Submodule K X) ≤
      Module.finrank K Yout :=
    Submodule.finrank_mono hout
  omega

/-- If every recovery-zero direction belongs to `N`, visible recovery proves
Hall expansion with the sharp correction `finrank (Uₛ ⊓ N)`. -/
theorem visibleKernelRecovery_subspace_finrank_mod_commonKernel
    {K X Z : Type*}
    [Field K]
    [AddCommGroup X] [Module K X] [FiniteDimensional K X]
    [AddCommGroup Z] [Module K Z]
    (S W N Uₛ U_w C Yout : Submodule K X)
    (F : Uₛ →ₗ[K] Z)
    (R : LinearMap.ker F →ₗ[K] X)
    (hSW : Disjoint S W)
    (hUₛS : Uₛ ≤ S)
    (hUwW : U_w ≤ W)
    (hCW : C ≤ W)
    (hRrangeS : LinearMap.range R ≤ S)
    (hRkerN : ∀ x : LinearMap.ker R,
      ((((x : LinearMap.ker R) : LinearMap.ker F) : Uₛ) : X) ∈ N)
    (hvisible : Module.finrank K (LinearMap.range F) +
        Module.finrank K U_w ≤
      Module.finrank K ((U_w ⊔ C) : Submodule K X))
    (hout : (U_w ⊔ C) ⊔ LinearMap.range R ≤ Yout) :
    Module.finrank K ((Uₛ ⊔ U_w) : Submodule K X) ≤
      Module.finrank K Yout +
        Module.finrank K ((Uₛ ⊓ N) : Submodule K X) := by
  let j : LinearMap.ker R →ₗ[K] ((Uₛ ⊓ N) : Submodule K X) :=
    { toFun := fun x =>
        ⟨((((x : LinearMap.ker R) : LinearMap.ker F) : Uₛ) : X),
          ⟨(((x : LinearMap.ker R) : LinearMap.ker F) : Uₛ).property,
            hRkerN x⟩⟩
      map_add' := by
        intro x y
        rfl
      map_smul' := by
        intro a x
        rfl }
  have hj : Function.Injective j := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg
      (fun z : ((Uₛ ⊓ N) : Submodule K X) => (z : X)) hxy
  have hkerLe : Module.finrank K (LinearMap.ker R) ≤
      Module.finrank K ((Uₛ ⊓ N) : Submodule K X) :=
    j.finrank_le_finrank_of_injective hj
  have hbase := visibleKernelRecovery_subspace_finrank_with_kernel
    S W Uₛ U_w C Yout F R hSW hUₛS hUwW hCW hRrangeS hvisible hout
  omega

end

end GaloisForLFunctions.HTGeometry
