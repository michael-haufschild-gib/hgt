import GaloisForLFunctions.HTGeometry.TwoReplicaHallSaturationCanonical

/-!
# Exact two-replica Hall expansion modulo global synchronization

Canonical two-replica deficiency saturation previously bounded only the greatest obstruction by
the two global identity/swap modes.  The kernel-saturation promotion upgrades that result to every
subspace.  This module also proves directly that arbitrary collective Pauli commutators annihilate
those two modes and concludes that they are the complete simultaneous kernel.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped BigOperators Matrix Kronecker

section KernelSaturation

variable {𝕜 X Y J : Type*} [DivisionRing 𝕜]
  [AddCommGroup X] [Module 𝕜 X] [AddCommGroup Y] [Module 𝕜 Y]

/-- A common-kernel subspace has zero shadow under the whole linear family. -/
theorem linearFamilyShadow_eq_bot_of_le_ker
    (A : J → X →ₗ[𝕜] Y) (N : Submodule 𝕜 X)
    (hN : ∀ j, N ≤ LinearMap.ker (A j)) :
    linearFamilyShadow A N = ⊥ := by
  rw [eq_bot_iff]
  apply iSup_le
  intro j
  rw [Submodule.map_le_iff_le_comap]
  intro x hx
  exact hN j hx

variable [FiniteDimensional 𝕜 X] [FiniteDimensional 𝕜 Y]

/-- **Kernel-saturation promotion.**  If `Ustar` maximizes family deficiency and its deficiency is
at most the dimension of a common kernel `N`, then every input subspace loses no more dimension
than its own intersection with `N`.  Equivalently, the induced family is Hall-expanding after
quotienting the common kernel. -/
theorem linearFamily_finrank_le_shadow_add_inf_of_kernel_saturation
    (A : J → X →ₗ[𝕜] Y) (N Ustar : Submodule 𝕜 X)
    (hN : ∀ j, N ≤ LinearMap.ker (A j))
    (hmax : ∀ U : Submodule 𝕜 X,
      linearFamilyDefect A U ≤ linearFamilyDefect A Ustar)
    (hsat : Module.finrank 𝕜 Ustar ≤
      Module.finrank 𝕜 (linearFamilyShadow A Ustar) + Module.finrank 𝕜 N)
    (U : Submodule 𝕜 X) :
    Module.finrank 𝕜 U ≤
      Module.finrank 𝕜 (linearFamilyShadow A U) + Module.finrank 𝕜 ↥(U ⊓ N) := by
  have hshadowN : linearFamilyShadow A N = ⊥ :=
    linearFamilyShadow_eq_bot_of_le_ker A N hN
  have hshadowSup : linearFamilyShadow A (U ⊔ N) = linearFamilyShadow A U := by
    rw [linearFamilyShadow_sup, hshadowN, sup_bot_eq]
  have hdef := hmax (U ⊔ N)
  have hrank := Submodule.finrank_sup_add_finrank_inf_eq U N
  dsimp [linearFamilyDefect] at hdef
  rw [hshadowSup] at hdef
  omega

end KernelSaturation

/-- Arbitrary doubled Pauli-left words are sitewise tensor products of local left actions. -/
theorem finiteTwoReplicaPauliLeft_eq_localMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : V → Option (Fin 3)) :
    finiteTwoReplicaPauliLeft P =
      finiteTwoReplicaLocalMatrix fun v =>
        boolPauliOption (P v) ⊗ₖ (1 : Matrix Bool Bool ℂ) := by
  ext x y
  rw [finiteTwoReplicaPauliLeft, finitePauliMatrix_eq_finiteLocalMatrix,
    Matrix.kroneckerMap_apply]
  rw [← finiteLocalMatrix_one (sigma := V)]
  change
    (∏ v, boolPauliOption (P v) (x.1 v) (y.1 v)) *
        (∏ v, (1 : Matrix Bool Bool ℂ) (x.2 v) (y.2 v)) =
      ∏ v, (boolPauliOption (P v) ⊗ₖ (1 : Matrix Bool Bool ℂ))
        (x.1 v, x.2 v) (y.1 v, y.2 v)
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v _
  rw [Matrix.kronecker_apply]

/-- Arbitrary doubled Pauli-right words are sitewise tensor products of local right actions. -/
theorem finiteTwoReplicaPauliRight_eq_localMatrix
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : V → Option (Fin 3)) :
    finiteTwoReplicaPauliRight P =
      finiteTwoReplicaLocalMatrix fun v =>
        (1 : Matrix Bool Bool ℂ) ⊗ₖ boolPauliOption (P v) := by
  ext x y
  rw [finiteTwoReplicaPauliRight, finitePauliMatrix_eq_finiteLocalMatrix,
    Matrix.kroneckerMap_apply]
  rw [← finiteLocalMatrix_one (sigma := V)]
  change
    (∏ v, (1 : Matrix Bool Bool ℂ) (x.1 v) (y.1 v)) *
        (∏ v, boolPauliOption (P v) (x.2 v) (y.2 v)) =
      ∏ v, ((1 : Matrix Bool Bool ℂ) ⊗ₖ boolPauliOption (P v))
        (x.1 v, x.2 v) (y.1 v, y.2 v)
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro v _
  rw [Matrix.kronecker_apply]

/-- The global replica swap exchanges arbitrary Pauli-left and Pauli-right words. -/
theorem finiteTwoReplicaPauliLeft_mul_allSwap
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : V → Option (Fin 3)) :
    finiteTwoReplicaPauliLeft P * finiteTwoReplicaSwapRaw twoReplicaAllSwap =
      finiteTwoReplicaSwapRaw twoReplicaAllSwap * finiteTwoReplicaPauliRight P := by
  rw [finiteTwoReplicaPauliLeft_eq_localMatrix,
    finiteTwoReplicaPauliRight_eq_localMatrix,
    finiteTwoReplicaSwapRaw,
    finiteTwoReplicaLocalMatrix_mul, finiteTwoReplicaLocalMatrix_mul]
  congr 1
  funext v
  change (boolPauliOption (P v) ⊗ₖ (1 : Matrix Bool Bool ℂ)) * twoReplicaSwap =
    twoReplicaSwap * ((1 : Matrix Bool Bool ℂ) ⊗ₖ boolPauliOption (P v))
  cases hP : P v with
  | none => simp [boolPauliOption]
  | some a =>
      simpa [boolPauliOption, twoReplicaPauliLeft, twoReplicaPauliRight] using
        (twoReplicaSwap_mul_right a).symm

/-- The reverse global replica-swap exchange law. -/
theorem finiteTwoReplicaPauliRight_mul_allSwap
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : V → Option (Fin 3)) :
    finiteTwoReplicaPauliRight P * finiteTwoReplicaSwapRaw twoReplicaAllSwap =
      finiteTwoReplicaSwapRaw twoReplicaAllSwap * finiteTwoReplicaPauliLeft P := by
  rw [finiteTwoReplicaPauliLeft_eq_localMatrix,
    finiteTwoReplicaPauliRight_eq_localMatrix,
    finiteTwoReplicaSwapRaw,
    finiteTwoReplicaLocalMatrix_mul, finiteTwoReplicaLocalMatrix_mul]
  congr 1
  funext v
  change ((1 : Matrix Bool Bool ℂ) ⊗ₖ boolPauliOption (P v)) * twoReplicaSwap =
    twoReplicaSwap * (boolPauliOption (P v) ⊗ₖ (1 : Matrix Bool Bool ℂ))
  cases hP : P v with
  | none => simp [boolPauliOption]
  | some a =>
      simpa [boolPauliOption, twoReplicaPauliLeft, twoReplicaPauliRight] using
        (twoReplicaSwap_mul_left a).symm

theorem finiteTwoReplicaPauliLeft_mul_allIdentity
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : V → Option (Fin 3)) :
    finiteTwoReplicaPauliLeft P * finiteTwoReplicaSwapRaw twoReplicaAllIdentity =
      finiteTwoReplicaSwapRaw twoReplicaAllIdentity * finiteTwoReplicaPauliLeft P := by
  rw [finiteTwoReplicaPauliLeft_eq_localMatrix,
    finiteTwoReplicaSwapRaw,
    finiteTwoReplicaLocalMatrix_mul, finiteTwoReplicaLocalMatrix_mul]
  congr 1
  funext v
  simp [twoReplicaAllIdentity, twoReplicaLocalSwapRaw]

theorem finiteTwoReplicaPauliRight_mul_allIdentity
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : V → Option (Fin 3)) :
    finiteTwoReplicaPauliRight P * finiteTwoReplicaSwapRaw twoReplicaAllIdentity =
      finiteTwoReplicaSwapRaw twoReplicaAllIdentity * finiteTwoReplicaPauliRight P := by
  rw [finiteTwoReplicaPauliRight_eq_localMatrix,
    finiteTwoReplicaSwapRaw,
    finiteTwoReplicaLocalMatrix_mul, finiteTwoReplicaLocalMatrix_mul]
  congr 1
  funext v
  simp [twoReplicaAllIdentity, twoReplicaLocalSwapRaw]

/-- Every collective Pauli commutator kills the global identity. -/
theorem finiteTwoReplicaCollectiveCommutator_allIdentity_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : V → Option (Fin 3)) :
    finiteTwoReplicaCollectiveCommutatorLinear P
        (finiteTwoReplicaSwapRaw twoReplicaAllIdentity) = 0 := by
  change ringCommutator (finiteTwoReplicaPauliLeft P)
      (finiteTwoReplicaSwapRaw twoReplicaAllIdentity) +
    ringCommutator (finiteTwoReplicaPauliRight P)
      (finiteTwoReplicaSwapRaw twoReplicaAllIdentity) = 0
  rw [ringCommutator, ringCommutator,
    finiteTwoReplicaPauliLeft_mul_allIdentity,
    finiteTwoReplicaPauliRight_mul_allIdentity]
  abel

/-- Every collective Pauli commutator kills the global replica swap. -/
theorem finiteTwoReplicaCollectiveCommutator_allSwap_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (P : V → Option (Fin 3)) :
    finiteTwoReplicaCollectiveCommutatorLinear P
        (finiteTwoReplicaSwapRaw twoReplicaAllSwap) = 0 := by
  change ringCommutator (finiteTwoReplicaPauliLeft P)
      (finiteTwoReplicaSwapRaw twoReplicaAllSwap) +
    ringCommutator (finiteTwoReplicaPauliRight P)
      (finiteTwoReplicaSwapRaw twoReplicaAllSwap) = 0
  rw [ringCommutator, ringCommutator,
    finiteTwoReplicaPauliLeft_mul_allSwap,
    finiteTwoReplicaPauliRight_mul_allSwap]
  abel

/-- The synchronized identity/swap plane lies in the kernel of every `q`-local collective Pauli
commutator. -/
theorem finiteTwoReplicaGlobalSynchronizedSubmodule_le_qlocal_ker
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    (q : ℕ) (P : FiniteQLocalPauliLabel V q) :
    finiteTwoReplicaGlobalSynchronizedSubmodule (V := V) ≤
      LinearMap.ker (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q P) := by
  intro X hX
  rw [LinearMap.mem_ker]
  rcases (mem_finiteTwoReplicaGlobalSynchronizedSubmodule_iff X).1 hX with
    ⟨a, b, rfl⟩
  change finiteTwoReplicaCollectiveCommutatorLinear P.1
      (∑ x : V → Bool,
        twoReplicaGlobalSynchronizedCoeff a b x • finiteTwoReplicaSwapRaw x) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro x _
  rw [map_smul]
  by_cases hid : x = twoReplicaAllIdentity
  · subst x
    rw [finiteTwoReplicaCollectiveCommutator_allIdentity_eq_zero, smul_zero]
  by_cases hswap : x = twoReplicaAllSwap
  · subst x
    rw [finiteTwoReplicaCollectiveCommutator_allSwap_eq_zero, smul_zero]
  · simp [twoReplicaGlobalSynchronizedCoeff, hid, hswap]

/-- **Exact two-replica Hall law modulo synchronization.**  For every subspace, the complete
`q`-local collective Pauli shadow loses no dimension beyond that subspace's own global
identity/swap component. -/
theorem finiteTwoReplicaQLocalCollectiveCommutator_finrank_mod_synchronized
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {q : ℕ} (hq : 2 ≤ q) {G : SimpleGraph V} (hG : G.Preconnected)
    (U : Submodule ℂ (FiniteTwoReplicaMatrix V)) :
    Module.finrank ℂ U ≤
      Module.finrank ℂ
          (linearFamilyShadow
            (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) U) +
        Module.finrank ℂ
          ↥(U ⊓ finiteTwoReplicaGlobalSynchronizedSubmodule (V := V)) := by
  apply linearFamily_finrank_le_shadow_add_inf_of_kernel_saturation
    (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q)
    (finiteTwoReplicaGlobalSynchronizedSubmodule (V := V))
    (canonicalTwoReplicaQLocalObstruction V q)
  · exact finiteTwoReplicaGlobalSynchronizedSubmodule_le_qlocal_ker q
  · exact linearFamilyDefect_le_canonicalTwoReplicaQLocalObstruction q
  · simpa [finrank_finiteTwoReplicaGlobalSynchronizedSubmodule] using
      canonicalTwoReplicaObstruction_finrank_le_shadow_add_two hq hG

/-- Every subspace transverse to global identity/swap is expanded without loss. -/
theorem finiteTwoReplicaQLocalCollectiveCommutator_finrank_of_disjoint_synchronized
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {q : ℕ} (hq : 2 ≤ q) {G : SimpleGraph V} (hG : G.Preconnected)
    (U : Submodule ℂ (FiniteTwoReplicaMatrix V))
    (hU : Disjoint U (finiteTwoReplicaGlobalSynchronizedSubmodule (V := V))) :
    Module.finrank ℂ U ≤
      Module.finrank ℂ
        (linearFamilyShadow
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) U) := by
  have h := finiteTwoReplicaQLocalCollectiveCommutator_finrank_mod_synchronized
    hq hG U
  rw [hU.eq_bot, finrank_bot, add_zero] at h
  exact h

/-- Simultaneous kernel of the complete two-replica `q`-local collective Pauli family. -/
def finiteTwoReplicaQLocalCommonKernel
    (V : Type*) [Fintype V] [DecidableEq V] (q : ℕ) :
    Submodule ℂ (FiniteTwoReplicaMatrix V) :=
  ⨅ P : FiniteQLocalPauliLabel V q,
    LinearMap.ker (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q P)

/-- **Exact common-kernel classification.**  On a connected register and for `q ≥ 2`, the only
two-replica operators killed by every `q`-local collective Pauli commutator are global identity and
global replica swap. -/
theorem finiteTwoReplicaQLocalCommonKernel_eq_synchronized
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {q : ℕ} (hq : 2 ≤ q) {G : SimpleGraph V} (hG : G.Preconnected) :
    finiteTwoReplicaQLocalCommonKernel V q =
      finiteTwoReplicaGlobalSynchronizedSubmodule (V := V) := by
  let A := finiteTwoReplicaQLocalCollectiveCommutatorLinear V q
  let N := finiteTwoReplicaGlobalSynchronizedSubmodule (V := V)
  let K := finiteTwoReplicaQLocalCommonKernel V q
  have hNK : N ≤ K := by
    rw [show K = ⨅ P, LinearMap.ker (A P) by rfl]
    exact le_iInf fun P =>
      finiteTwoReplicaGlobalSynchronizedSubmodule_le_qlocal_ker q P
  have hshadowK : linearFamilyShadow A K = ⊥ := by
    rw [eq_bot_iff]
    apply iSup_le
    intro P
    rw [Submodule.map_le_iff_le_comap]
    intro x hx
    exact (Submodule.mem_iInf _).1 hx P
  have hrank :=
    finiteTwoReplicaQLocalCollectiveCommutator_finrank_mod_synchronized
      hq hG K
  have hKN : K ⊓ N = N := inf_eq_right.mpr hNK
  change Module.finrank ℂ K ≤
    Module.finrank ℂ (linearFamilyShadow A K) + Module.finrank ℂ ↥(K ⊓ N) at hrank
  rw [hshadowK, hKN] at hrank
  have hrank' : Module.finrank ℂ K ≤ Module.finrank ℂ N := by
    simpa using hrank
  change K = N
  exact (Submodule.eq_of_le_of_finrank_le hNK hrank').symm

end

end GaloisForLFunctions.HTGeometry
