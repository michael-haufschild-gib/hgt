import GaloisForLFunctions.HTGeometry.TwoReplicaSingleSiteCollectiveKernel

/-!
# Finite-register Hasse classification by one-site commutators

Every site and each of its three Pauli axes is treated as a local place. The exact common kernel
of these observations is the product-Clifford-twirl sector. Thus global two-replica operators
modulo that sector are precisely the all-site commutator profiles that occur globally.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Simultaneous one-site, three-axis collective-commutator profile. -/
def finiteTwoReplicaSingleSiteHasseProfile :
    FiniteTwoReplicaMatrix V →ₗ[ℂ]
      (V → Fin 3 → FiniteTwoReplicaMatrix V) :=
  LinearMap.pi fun j => LinearMap.pi fun a =>
    finiteTwoReplicaCollectiveCommutatorLinear
      (finiteSingleSitePauliLabel j a)

@[simp] theorem finiteTwoReplicaSingleSiteHasseProfile_apply
    (X : FiniteTwoReplicaMatrix V) (j : V) (a : Fin 3) :
    finiteTwoReplicaSingleSiteHasseProfile X j a =
      finiteTwoReplicaCollectiveCommutatorLinear
        (finiteSingleSitePauliLabel j a) X := by
  rfl

/-- The complete local kernel is exactly the product-Clifford-twirl sector. -/
theorem finiteTwoReplicaSingleSiteHasseProfile_ker :
    LinearMap.ker (finiteTwoReplicaSingleSiteHasseProfile (V := V)) =
      LinearMap.range (finiteProductCliffordTwoReplicaTwirlLinear (V := V)) := by
  ext X
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    have hx : X ∈ {Y : FiniteTwoReplicaMatrix V |
        ∀ j : V, ∀ a : Fin 3,
          finiteTwoReplicaCollectiveCommutatorLinear
            (finiteSingleSitePauliLabel j a) Y = 0} :=
      fun j a => congrFun (congrFun h j) a
    rw [finiteTwoReplica_singleSiteCollective_commonKernel_eq_productCliffordTwirl_range] at hx
    exact hx
  · intro hx
    have hlocal : ∀ j : V, ∀ a : Fin 3,
        finiteTwoReplicaCollectiveCommutatorLinear
          (finiteSingleSitePauliLabel j a) X = 0 := by
      have hx' : X ∈ {Y : FiniteTwoReplicaMatrix V |
          ∀ j : V, ∀ a : Fin 3,
            finiteTwoReplicaCollectiveCommutatorLinear
              (finiteSingleSitePauliLabel j a) Y = 0} := by
        rw [finiteTwoReplica_singleSiteCollective_commonKernel_eq_productCliffordTwirl_range]
        exact hx
      exact hx'
    funext j a
    exact hlocal j a

/-- Global operators modulo the product-Clifford sector. -/
abbrev FiniteTwoReplicaSingleSiteHasseClass :=
  FiniteTwoReplicaMatrix V ⧸
    LinearMap.range (finiteProductCliffordTwoReplicaTwirlLinear (V := V))

/-- The quotient is exactly the space of realized one-site commutator packets. -/
noncomputable def finiteTwoReplicaSingleSiteHasseEquivRealizedProfiles :
    FiniteTwoReplicaSingleSiteHasseClass (V := V) ≃ₗ[ℂ]
      LinearMap.range (finiteTwoReplicaSingleSiteHasseProfile (V := V)) :=
  (Submodule.quotEquivOfEq _ _
    (finiteTwoReplicaSingleSiteHasseProfile_ker (V := V)).symm).trans
      (LinearMap.quotKerEquivRange _)

@[simp] theorem finiteTwoReplicaSingleSiteHasseEquivRealizedProfiles_mk
    (X : FiniteTwoReplicaMatrix V) :
    finiteTwoReplicaSingleSiteHasseEquivRealizedProfiles
        (Submodule.Quotient.mk X) =
      ⟨finiteTwoReplicaSingleSiteHasseProfile X, ⟨X, rfl⟩⟩ := by
  rfl

/-- All one-site Pauli places determine an operator modulo product-Clifford gauge. -/
theorem finiteTwoReplicaSingleSite_congr_hasse_iff
    (X Y : FiniteTwoReplicaMatrix V) :
    X - Y ∈ LinearMap.range
        (finiteProductCliffordTwoReplicaTwirlLinear (V := V)) ↔
      ∀ j : V, ∀ a : Fin 3,
        finiteTwoReplicaCollectiveCommutatorLinear
            (finiteSingleSitePauliLabel j a) X =
          finiteTwoReplicaCollectiveCommutatorLinear
            (finiteSingleSitePauliLabel j a) Y := by
  rw [← finiteTwoReplicaSingleSiteHasseProfile_ker, LinearMap.mem_ker,
    map_sub, sub_eq_zero]
  constructor
  · intro h j a
    exact congrFun (congrFun h j) a
  · intro h
    funext j a
    exact h j a

/-- The quotient class vanishes exactly when all one-site commutators vanish. -/
theorem finiteTwoReplicaSingleSiteClass_eq_zero_hasse_iff
    (X : FiniteTwoReplicaMatrix V) :
    Submodule.Quotient.mk X =
        (0 : FiniteTwoReplicaSingleSiteHasseClass (V := V)) ↔
      ∀ j : V, ∀ a : Fin 3,
        finiteTwoReplicaCollectiveCommutatorLinear
          (finiteSingleSitePauliLabel j a) X = 0 := by
  rw [Submodule.Quotient.mk_eq_zero,
    ← finiteTwoReplicaSingleSiteHasseProfile_ker, LinearMap.mem_ker]
  constructor
  · intro h j a
    exact congrFun (congrFun h j) a
  · intro h
    funext j a
    exact h j a

/-- Every nonzero quotient class has a site and Pauli-axis witness. -/
theorem finiteTwoReplicaSingleSiteClass_ne_zero_iff_exists_localWitness
    (X : FiniteTwoReplicaMatrix V) :
    Submodule.Quotient.mk X ≠
        (0 : FiniteTwoReplicaSingleSiteHasseClass (V := V)) ↔
      ∃ j : V, ∃ a : Fin 3,
        finiteTwoReplicaCollectiveCommutatorLinear
          (finiteSingleSitePauliLabel j a) X ≠ 0 := by
  constructor
  · intro h
    by_contra hn
    have hall : ∀ j : V, ∀ a : Fin 3,
        finiteTwoReplicaCollectiveCommutatorLinear
          (finiteSingleSitePauliLabel j a) X = 0 := by
      intro j a
      by_contra hja
      exact hn ⟨j, a, hja⟩
    exact h (finiteTwoReplicaSingleSiteClass_eq_zero_hasse_iff X |>.2 hall)
  · rintro ⟨j, a, hja⟩ hzero
    exact hja (finiteTwoReplicaSingleSiteClass_eq_zero_hasse_iff X |>.1 hzero j a)

/-- Every realized all-site packet has one unique global class modulo product-Clifford gauge. -/
theorem finiteTwoReplicaSingleSiteRealizedProfile_existsUnique_global
    (p : LinearMap.range (finiteTwoReplicaSingleSiteHasseProfile (V := V))) :
    ∃! x : FiniteTwoReplicaSingleSiteHasseClass (V := V),
      finiteTwoReplicaSingleSiteHasseEquivRealizedProfiles x = p := by
  refine ⟨finiteTwoReplicaSingleSiteHasseEquivRealizedProfiles.symm p,
    finiteTwoReplicaSingleSiteHasseEquivRealizedProfiles.apply_symm_apply p, ?_⟩
  intro y hy
  apply finiteTwoReplicaSingleSiteHasseEquivRealizedProfiles.injective
  rw [hy, finiteTwoReplicaSingleSiteHasseEquivRealizedProfiles.apply_symm_apply]

end

end GaloisForLFunctions.HTGeometry
