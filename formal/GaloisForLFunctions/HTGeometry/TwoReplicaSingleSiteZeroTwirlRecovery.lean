import GaloisForLFunctions.HTGeometry.TwoReplicaProductCliffordVisibleRecovery
import GaloisForLFunctions.HTGeometry.TwoReplicaSingleSiteCollectiveKernel

/-! # Exact one-site recovery of the product-Clifford zero-twirl sector -/

open scoped BigOperators Matrix Kronecker InnerProductSpace
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open QuantumAlg

theorem finiteProductCliffordTwoReplicaTwirl_hsInner_selfAdjoint
    {V : Type*} [Fintype V] [DecidableEq V]
    (X Y : FiniteTwoReplicaMatrix V) :
    hsInner (finiteProductCliffordTwoReplicaTwirlLinear X) Y =
      hsInner X (finiteProductCliffordTwoReplicaTwirlLinear Y) := by
  have hpg0 : ∀ v : FiniteTwoReplicaMatrix V,
      hsInner (v * X * vᴴ) Y = hsInner X (vᴴ * Y * v) := by
    intro v
    simp only [hsInner, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm v]
    simp only [Matrix.mul_assoc]
  have hreidx :
      (∑ g : V → QubitTwoDesign.BinaryOctahedral,
        hsInner X ((finiteProductCliffordDoubledGate g)ᴴ * Y *
          finiteProductCliffordDoubledGate g)) =
      ∑ g : V → QubitTwoDesign.BinaryOctahedral,
        hsInner X (finiteProductCliffordDoubledGate g * Y *
          (finiteProductCliffordDoubledGate g)ᴴ) := by
    have hF : ∀ g : V → QubitTwoDesign.BinaryOctahedral,
        hsInner X (finiteProductCliffordDoubledGate g⁻¹ * Y *
          (finiteProductCliffordDoubledGate g⁻¹)ᴴ) =
        hsInner X ((finiteProductCliffordDoubledGate g)ᴴ * Y *
          finiteProductCliffordDoubledGate g) := by
      intro g
      rw [finiteProductCliffordDoubledGate_conjTranspose_eq_inv g⁻¹]
      simp only [Pi.inv_apply, inv_inv]
      change hsInner X
        (finiteProductCliffordDoubledGate (fun s => (g s)⁻¹) * Y *
          finiteProductCliffordDoubledGate g) = _
      rw [← finiteProductCliffordDoubledGate_conjTranspose_eq_inv g]
    calc
      (∑ g : V → QubitTwoDesign.BinaryOctahedral,
          hsInner X ((finiteProductCliffordDoubledGate g)ᴴ * Y *
            finiteProductCliffordDoubledGate g)) =
        ∑ g : V → QubitTwoDesign.BinaryOctahedral,
          hsInner X (finiteProductCliffordDoubledGate g⁻¹ * Y *
            (finiteProductCliffordDoubledGate g⁻¹)ᴴ) :=
          Finset.sum_congr rfl fun g _ => (hF g).symm
      _ = ∑ g : V → QubitTwoDesign.BinaryOctahedral,
          hsInner X (finiteProductCliffordDoubledGate g * Y *
            (finiteProductCliffordDoubledGate g)ᴴ) :=
          Equiv.sum_comp (Equiv.inv (V → QubitTwoDesign.BinaryOctahedral))
            (fun g => hsInner X (finiteProductCliffordDoubledGate g * Y *
              (finiteProductCliffordDoubledGate g)ᴴ))
  change hsInner (repTwirl finiteProductCliffordDoubledGate X) Y =
    hsInner X (repTwirl finiteProductCliffordDoubledGate Y)
  simp only [repTwirl, hsInner_smul_left, hsInner_sum_left,
    hsInner_smul_right, hsInner_sum_right]
  rw [starRingEnd_apply, star_inv₀, star_natCast,
    Finset.sum_congr rfl
      (fun g _ => hpg0 (finiteProductCliffordDoubledGate g)), hreidx]

def finiteTwoReplicaSingleSiteCollectiveFamily
    (V : Type*) [Fintype V] [DecidableEq V] :
    (V × Fin 3) → FiniteTwoReplicaMatrix V →ₗ[ℂ] FiniteTwoReplicaMatrix V :=
  fun ja => finiteTwoReplicaCollectiveCommutatorLinear
    (finiteSingleSitePauliLabel ja.1 ja.2)

theorem re_inner_finiteTwoReplicaSingleSiteCollectiveSquare_eq_energy
    {V : Type*} [Fintype V] [DecidableEq V]
    (X : FiniteTwoReplicaMatrix V) :
    Complex.re (inner ℂ (finiteMatrixHilbertEquiv X)
      (finiteMatrixHilbertEquiv
        (linearFamilySquare (finiteTwoReplicaSingleSiteCollectiveFamily V) X))) =
      ∑ ja : V × Fin 3,
        ‖finiteMatrixHilbertEquiv
          (finiteTwoReplicaCollectiveCommutatorLinear
            (finiteSingleSitePauliLabel ja.1 ja.2) X)‖ ^ 2 := by
  simp only [linearFamilySquare_apply, map_sum, inner_sum]
  change Complex.reCLM (∑ ja : V × Fin 3,
      inner ℂ (finiteMatrixHilbertEquiv X)
        (finiteMatrixHilbertEquiv
          (finiteTwoReplicaCollectiveCommutatorLinear
            (finiteSingleSitePauliLabel ja.1 ja.2)
            (finiteTwoReplicaCollectiveCommutatorLinear
              (finiteSingleSitePauliLabel ja.1 ja.2) X)))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro ja _
  rw [finiteTwoReplicaCollectiveCommutator_hilbert_energy,
    inner_self_eq_norm_sq_to_K]
  norm_cast

theorem finiteTwoReplicaSingleSiteCollectiveSquare_eq_zero_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (X : FiniteTwoReplicaMatrix V) :
    linearFamilySquare (finiteTwoReplicaSingleSiteCollectiveFamily V) X = 0 ↔
      ∀ j : V, ∀ a : Fin 3,
        finiteTwoReplicaCollectiveCommutatorLinear
          (finiteSingleSitePauliLabel j a) X = 0 := by
  constructor
  · intro hzero
    have henergy : (∑ ja : V × Fin 3,
        ‖finiteMatrixHilbertEquiv
          (finiteTwoReplicaCollectiveCommutatorLinear
            (finiteSingleSitePauliLabel ja.1 ja.2) X)‖ ^ 2) = 0 := by
      rw [← re_inner_finiteTwoReplicaSingleSiteCollectiveSquare_eq_energy,
        hzero]
      simp
    intro j a
    have hterm : ‖finiteMatrixHilbertEquiv
        (finiteTwoReplicaCollectiveCommutatorLinear
          (finiteSingleSitePauliLabel j a) X)‖ ^ 2 = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg
        (fun ja _ => sq_nonneg _)).mp henergy (j, a) (Finset.mem_univ _)
    apply finiteMatrixHilbertEquiv.injective
    apply norm_eq_zero.mp
    exact sq_eq_zero_iff.mp hterm
  · intro hzero
    rw [linearFamilySquare_apply]
    apply Finset.sum_eq_zero
    rintro ⟨j, a⟩ _
    change finiteTwoReplicaCollectiveCommutatorLinear
      (finiteSingleSitePauliLabel j a)
      (finiteTwoReplicaCollectiveCommutatorLinear
        (finiteSingleSitePauliLabel j a) X) = 0
    rw [hzero j a, map_zero]

theorem finiteProductCliffordTwoReplicaTwirl_singleSiteCollectiveCommutator_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    (j : V) (a : Fin 3) (X : FiniteTwoReplicaMatrix V) :
    finiteProductCliffordTwoReplicaTwirlLinear
      (finiteTwoReplicaCollectiveCommutatorLinear
        (finiteSingleSitePauliLabel j a) X) = 0 := by
  let T := finiteProductCliffordTwoReplicaTwirlLinear (V := V)
  let D := finiteTwoReplicaCollectiveCommutatorLinear
    (finiteSingleSitePauliLabel j a)
  let Z := T (D X)
  have hZrange : Z ∈ LinearMap.range T := ⟨D X, rfl⟩
  have hZcommon : Z ∈ {Y : FiniteTwoReplicaMatrix V |
      ∀ k : V, ∀ b : Fin 3,
        finiteTwoReplicaCollectiveCommutatorLinear
          (finiteSingleSitePauliLabel k b) Y = 0} := by
    rw [finiteTwoReplica_singleSiteCollective_commonKernel_eq_productCliffordTwirl_range]
    exact hZrange
  have hDZ : D Z = 0 := hZcommon j a
  have hTZ : T Z = Z := by
    exact finiteProductCliffordTwoReplicaTwirl_idempotent (D X)
  have hinner : hsInner Z Z = 0 := by
    calc
      hsInner Z Z = hsInner (T (D X)) Z := rfl
      _ = hsInner (D X) (T Z) :=
        finiteProductCliffordTwoReplicaTwirl_hsInner_selfAdjoint (D X) Z
      _ = hsInner (D X) Z := by rw [hTZ]
      _ = hsInner X (D Z) :=
        finiteTwoReplicaCollectiveCommutator_hsInner_selfAdjoint
          (finiteSingleSitePauliLabel j a) X Z
      _ = 0 := by rw [hDZ]; simp
  have hflat : finiteMatrixHilbertEquiv Z = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℂ)).mp
    rw [inner_finiteMatrixHilbertEquiv_eq_hsInner]
    exact hinner
  have hZzero : Z = 0 := finiteMatrixHilbertEquiv.injective hflat
  change T (D X) = 0
  exact hZzero

theorem finiteTwoReplicaSingleSiteCollectiveCommutator_mem_productCliffordTwirl_ker
    {V : Type*} [Fintype V] [DecidableEq V]
    (j : V) (a : Fin 3) (X : FiniteTwoReplicaMatrix V) :
    finiteTwoReplicaCollectiveCommutatorLinear
        (finiteSingleSitePauliLabel j a) X ∈
      LinearMap.ker
        (finiteProductCliffordTwoReplicaTwirlLinear (V := V)) :=
  finiteProductCliffordTwoReplicaTwirl_singleSiteCollectiveCommutator_eq_zero
    j a X

theorem finiteTwoReplicaSingleSiteCollectiveSquare_eq_zero_mem_productCliffordTwirl_range
    {V : Type*} [Fintype V] [DecidableEq V]
    {X : FiniteTwoReplicaMatrix V}
    (hX : linearFamilySquare
      (finiteTwoReplicaSingleSiteCollectiveFamily V) X = 0) :
    X ∈ LinearMap.range
      (finiteProductCliffordTwoReplicaTwirlLinear (V := V)) := by
  have hcommon : X ∈ {Y : FiniteTwoReplicaMatrix V |
      ∀ j : V, ∀ a : Fin 3,
        finiteTwoReplicaCollectiveCommutatorLinear
          (finiteSingleSitePauliLabel j a) Y = 0} :=
    (finiteTwoReplicaSingleSiteCollectiveSquare_eq_zero_iff X).mp hX
  rw [finiteTwoReplica_singleSiteCollective_commonKernel_eq_productCliffordTwirl_range]
    at hcommon
  exact hcommon

theorem finiteTwoReplicaSingleSiteCollectiveSquare_injective_on_productCliffordTwirl_ker
    {V : Type*} [Fintype V] [DecidableEq V] :
    Function.Injective
      ((linearFamilySquare (finiteTwoReplicaSingleSiteCollectiveFamily V)).domRestrict
        (LinearMap.ker
          (finiteProductCliffordTwoReplicaTwirlLinear (V := V)))) := by
  intro x y hxy
  apply Subtype.ext
  apply sub_eq_zero.mp
  let d : FiniteTwoReplicaMatrix V := (x : FiniteTwoReplicaMatrix V) - y
  have hxy' : linearFamilySquare (finiteTwoReplicaSingleSiteCollectiveFamily V)
      (x : FiniteTwoReplicaMatrix V) =
      linearFamilySquare (finiteTwoReplicaSingleSiteCollectiveFamily V)
        (y : FiniteTwoReplicaMatrix V) := hxy
  have hsquare : linearFamilySquare
      (finiteTwoReplicaSingleSiteCollectiveFamily V) d = 0 := by
    change linearFamilySquare (finiteTwoReplicaSingleSiteCollectiveFamily V)
      ((x : FiniteTwoReplicaMatrix V) - (y : FiniteTwoReplicaMatrix V)) = 0
    rw [map_sub, hxy', sub_self]
  have hrange : d ∈ LinearMap.range
      (finiteProductCliffordTwoReplicaTwirlLinear (V := V)) :=
    finiteTwoReplicaSingleSiteCollectiveSquare_eq_zero_mem_productCliffordTwirl_range
      hsquare
  have hker : d ∈ LinearMap.ker
      (finiteProductCliffordTwoReplicaTwirlLinear (V := V)) := by
    change finiteProductCliffordTwoReplicaTwirlLinear
      ((x : FiniteTwoReplicaMatrix V) - (y : FiniteTwoReplicaMatrix V)) = 0
    rw [map_sub, x.property, y.property, sub_self]
  have hinter : d ∈
      LinearMap.range (finiteProductCliffordTwoReplicaTwirlLinear (V := V)) ⊓
        LinearMap.ker (finiteProductCliffordTwoReplicaTwirlLinear (V := V)) :=
    ⟨hrange, hker⟩
  have hbot : d ∈ (⊥ : Submodule ℂ (FiniteTwoReplicaMatrix V)) := by
    rw [← finiteProductCliffordTwoReplicaTwirl_range_inf_ker]
    exact hinter
  simpa using hbot

theorem finiteTwoReplicaSingleSite_shadow_le_qlocal_shadow
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} (hq : 1 ≤ q)
    (U : Submodule ℂ (FiniteTwoReplicaMatrix V)) :
    linearFamilyShadow (finiteTwoReplicaSingleSiteCollectiveFamily V) U ≤
      linearFamilyShadow
        (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) U := by
  apply iSup_le
  rintro ⟨j, a⟩
  let Pq : FiniteQLocalPauliLabel V q :=
    ⟨finiteSingleSitePauliLabel j a, by
      rw [finitePauliWeight_finiteSingleSitePauliLabel]
      exact hq⟩
  have hle := le_iSup
    (fun P : FiniteQLocalPauliLabel V q =>
      U.map (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q P)) Pq
  simpa [linearFamilyShadow, finiteTwoReplicaSingleSiteCollectiveFamily,
    finiteTwoReplicaQLocalCollectiveCommutatorLinear, Pq] using hle

theorem finiteTwoReplicaQLocal_greatestMaximizer_zeroTwirl_reproduced
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} (hq : 1 ≤ q)
    (U : Submodule ℂ (FiniteTwoReplicaMatrix V))
    (hgreatest : ∀ W : Submodule ℂ (FiniteTwoReplicaMatrix V),
      linearFamilyDefect
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) W =
        linearFamilyDefect
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) U →
      W ≤ U) :
    U ⊓ LinearMap.ker
          (finiteProductCliffordTwoReplicaTwirlLinear (V := V)) ≤
      linearFamilyShadow
        (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q)
        (U ⊓ LinearMap.ker
          (finiteProductCliffordTwoReplicaTwirlLinear (V := V))) := by
  let Uzero := U ⊓ LinearMap.ker
    (finiteProductCliffordTwoReplicaTwirlLinear (V := V))
  let A := finiteTwoReplicaSingleSiteCollectiveFamily V
  have hAU : ∀ ja x, x ∈ Uzero → A ja x ∈ Uzero := by
    rintro ⟨j, a⟩ x hx
    constructor
    · exact finiteTwoReplicaSingleSiteCollectiveCommutator_mem_greatestMaximizer
        q U hgreatest j a x hx.1
    · exact finiteTwoReplicaSingleSiteCollectiveCommutator_mem_productCliffordTwirl_ker
        j a x
  have hKinj : Function.Injective
      ((linearFamilySquare A).domRestrict Uzero) := by
    intro x y hxy
    let xker : LinearMap.ker
        (finiteProductCliffordTwoReplicaTwirlLinear (V := V)) :=
      ⟨x, x.property.2⟩
    let yker : LinearMap.ker
        (finiteProductCliffordTwoReplicaTwirlLinear (V := V)) :=
      ⟨y, y.property.2⟩
    have hkerxy :
        ((linearFamilySquare A).domRestrict
          (LinearMap.ker
            (finiteProductCliffordTwoReplicaTwirlLinear (V := V)))) xker =
        ((linearFamilySquare A).domRestrict
          (LinearMap.ker
            (finiteProductCliffordTwoReplicaTwirlLinear (V := V)))) yker := hxy
    have heq :=
      finiteTwoReplicaSingleSiteCollectiveSquare_injective_on_productCliffordTwirl_ker
        hkerxy
    apply Subtype.ext
    exact congrArg
      (fun z : LinearMap.ker
        (finiteProductCliffordTwoReplicaTwirlLinear (V := V)) =>
          (z : FiniteTwoReplicaMatrix V)) heq
  have hone : Uzero ≤ linearFamilyShadow A Uzero :=
    invariantSubspace_le_shadow_of_linearFamilySquare_injective
      A Uzero hAU hKinj
  exact hone.trans (finiteTwoReplicaSingleSite_shadow_le_qlocal_shadow hq Uzero)

/-- Unconditional q-local Hall saturation modulo the exact global
identity/swap correction. -/
theorem finiteTwoReplicaQLocal_greatestMaximizer_finrank_mod_synchronized
    {V : Type*} [Fintype V] [Nonempty V] [DecidableEq V]
    {q : ℕ} (hq : 2 ≤ q)
    {G : SimpleGraph V} (hG : G.Preconnected)
    (U : Submodule ℂ (FiniteTwoReplicaMatrix V))
    (hgreatest : ∀ W : Submodule ℂ (FiniteTwoReplicaMatrix V),
      linearFamilyDefect
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) W =
        linearFamilyDefect
          (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) U →
      W ≤ U) :
    Module.finrank ℂ U ≤
      Module.finrank ℂ
          (linearFamilyShadow
            (finiteTwoReplicaQLocalCollectiveCommutatorLinear V q) U) +
        Module.finrank ℂ
          (((U ⊓ LinearMap.range
              (finiteTwoReplicaSwapInvariantEmbed (V := V))) ⊓
            finiteTwoReplicaGlobalSynchronizedSubmodule (V := V)) :
              Submodule ℂ (FiniteTwoReplicaMatrix V)) := by
  apply finiteTwoReplicaQLocal_greatestMaximizer_finrank_mod_synchronized_of_zeroTwirl_reproduced
    hq hG U hgreatest
  exact finiteTwoReplicaQLocal_greatestMaximizer_zeroTwirl_reproduced
    (le_trans (by omega : 1 ≤ 2) hq) U hgreatest

end

end GaloisForLFunctions.HTGeometry
