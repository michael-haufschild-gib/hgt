import GaloisForLFunctions.HTGeometry.TwoReplicaLocalCollectiveCommonKernel

/-!
# Local-commutator Hasse classification for two replicas

The three one-qubit collective Pauli commutators are local places. Their simultaneous kernel is
the unavoidable identity--replica-swap gauge plane. The resulting quotient is therefore exactly
the space of realized three-axis commutator profiles.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Simultaneous three-axis local collective-commutator observation. -/
def twoReplicaLocalCommutatorHasseProfile :
    TwoReplicaLocalMatrix →ₗ[ℂ] (Fin 3 → TwoReplicaLocalMatrix) :=
  LinearMap.pi fun a => twoReplicaLocalCollectiveCommutatorLinear a

@[simp] theorem twoReplicaLocalCommutatorHasseProfile_apply
    (X : TwoReplicaLocalMatrix) (a : Fin 3) :
    twoReplicaLocalCommutatorHasseProfile X a =
      twoReplicaLocalCollectiveCommutatorLinear a X := by
  rfl

/-- Unavoidable global gauge sector: identity and replica swap. -/
abbrev twoReplicaLocalGaugePlane : Submodule ℂ TwoReplicaLocalMatrix :=
  Submodule.span ℂ
    ({(1 : TwoReplicaLocalMatrix), twoReplicaSwap} : Set TwoReplicaLocalMatrix)

/-- Simultaneous local invisibility is exactly identity/swap gauge. -/
theorem twoReplicaLocalCommutatorHasseProfile_ker :
    LinearMap.ker twoReplicaLocalCommutatorHasseProfile =
      twoReplicaLocalGaugePlane := by
  ext X
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    have hx : X ∈ {Y : TwoReplicaLocalMatrix |
        ∀ a : Fin 3, twoReplicaLocalCollectiveCommutatorLinear a Y = 0} :=
      fun a => congrFun h a
    rw [twoReplicaLocalCollectiveCommutator_commonKernel] at hx
    exact hx
  · intro hx
    have hlocal : ∀ a : Fin 3,
        twoReplicaLocalCollectiveCommutatorLinear a X = 0 := by
      have hx' : X ∈ {Y : TwoReplicaLocalMatrix |
          ∀ a : Fin 3, twoReplicaLocalCollectiveCommutatorLinear a Y = 0} := by
        rw [twoReplicaLocalCollectiveCommutator_commonKernel]
        exact hx
      exact hx'
    funext a
    exact hlocal a

/-- Operators modulo identity/swap gauge are exactly realized local commutator profiles. -/
noncomputable def twoReplicaLocalCommutatorHasseEquivRealizedProfiles :
    (TwoReplicaLocalMatrix ⧸ twoReplicaLocalGaugePlane) ≃ₗ[ℂ]
      LinearMap.range twoReplicaLocalCommutatorHasseProfile :=
  (Submodule.quotEquivOfEq _ _
    twoReplicaLocalCommutatorHasseProfile_ker.symm).trans
      (LinearMap.quotKerEquivRange _)

@[simp] theorem twoReplicaLocalCommutatorHasseEquivRealizedProfiles_mk
    (X : TwoReplicaLocalMatrix) :
    twoReplicaLocalCommutatorHasseEquivRealizedProfiles
        (Submodule.Quotient.mk X) =
      ⟨twoReplicaLocalCommutatorHasseProfile X, ⟨X, rfl⟩⟩ := by
  rfl

/-- Local Pauli axes determine a global operator modulo identity/swap gauge. -/
theorem twoReplicaLocalCommutator_congr_hasse_iff
    (X Y : TwoReplicaLocalMatrix) :
    X - Y ∈ twoReplicaLocalGaugePlane ↔
      ∀ a : Fin 3,
        twoReplicaLocalCollectiveCommutatorLinear a X =
          twoReplicaLocalCollectiveCommutatorLinear a Y := by
  rw [← twoReplicaLocalCommutatorHasseProfile_ker, LinearMap.mem_ker,
    map_sub, sub_eq_zero]
  constructor
  · intro h a
    exact congrFun h a
  · intro h
    funext a
    exact h a

/-- A class is zero exactly when every local commutator is zero. -/
theorem twoReplicaLocalCommutatorClass_eq_zero_hasse_iff
    (X : TwoReplicaLocalMatrix) :
    Submodule.Quotient.mk X =
        (0 : TwoReplicaLocalMatrix ⧸ twoReplicaLocalGaugePlane) ↔
      ∀ a : Fin 3, twoReplicaLocalCollectiveCommutatorLinear a X = 0 := by
  rw [Submodule.Quotient.mk_eq_zero,
    ← twoReplicaLocalCommutatorHasseProfile_ker, LinearMap.mem_ker]
  constructor
  · intro h a
    exact congrFun h a
  · intro h
    funext a
    exact h a

/-- Every nontrivial operator class is exposed by at least one Pauli axis. -/
theorem twoReplicaLocalCommutatorClass_ne_zero_iff_exists_axisWitness
    (X : TwoReplicaLocalMatrix) :
    Submodule.Quotient.mk X ≠
        (0 : TwoReplicaLocalMatrix ⧸ twoReplicaLocalGaugePlane) ↔
      ∃ a : Fin 3, twoReplicaLocalCollectiveCommutatorLinear a X ≠ 0 := by
  constructor
  · intro h
    by_contra hn
    have hall : ∀ a : Fin 3,
        twoReplicaLocalCollectiveCommutatorLinear a X = 0 := by
      intro a
      by_contra ha
      exact hn ⟨a, ha⟩
    exact h (twoReplicaLocalCommutatorClass_eq_zero_hasse_iff X |>.2 hall)
  · rintro ⟨a, ha⟩ hzero
    exact ha (twoReplicaLocalCommutatorClass_eq_zero_hasse_iff X |>.1 hzero a)

/-- Every realized three-axis profile has one unique global class modulo identity/swap gauge. -/
theorem twoReplicaLocalCommutatorRealizedProfile_existsUnique_global
    (p : LinearMap.range twoReplicaLocalCommutatorHasseProfile) :
    ∃! x : TwoReplicaLocalMatrix ⧸ twoReplicaLocalGaugePlane,
      twoReplicaLocalCommutatorHasseEquivRealizedProfiles x = p := by
  refine ⟨twoReplicaLocalCommutatorHasseEquivRealizedProfiles.symm p,
    twoReplicaLocalCommutatorHasseEquivRealizedProfiles.apply_symm_apply p, ?_⟩
  intro y hy
  apply twoReplicaLocalCommutatorHasseEquivRealizedProfiles.injective
  rw [hy, twoReplicaLocalCommutatorHasseEquivRealizedProfiles.apply_symm_apply]

end

end GaloisForLFunctions.HTGeometry
