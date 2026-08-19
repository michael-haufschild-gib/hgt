/-
# Concrete two-Hamiltonian spectral-action witness on a local qubit path

A recursively constructed endpoint-complete qubit path supplies a physical nearest-neighbour
Hamiltonian family.  Its full Hermitian local submodule is put in exact Hilbert--Schmidt
trace-orthonormal coordinates.  For every balanced nonzero spectral character, two fixed local
Hamiltonians then have disjoint squared labelled spectral-action ratios, uniformly over all
spectral labellings.

Main results:
* `PhysicallyRealizedEndpointCompleteSystem.exists_leafLocal_simple_energy_witness` -- every real
  action-to-energy level is avoided by a simple-spectrum physical local Hamiltonian under every
  labelling.
* `PhysicallyRealizedEndpointCompleteSystem.exists_leafLocal_disjoint_actionRatio_pair` -- two
  fixed local Hamiltonians witness all levels simultaneously.
-/
import GaloisForLFunctions.HTGeometry.PhysicalEndpointCompletePathWitness
import GaloisForLFunctions.HTGeometry.PhysicalChartCoordinates
import GaloisForLFunctions.HTGeometry.HermitianSubmoduleTraceOrthonormal
import GaloisForLFunctions.HTGeometry.SpectralEnergyWitnessBridge
import GaloisForLFunctions.HTGeometry.SpectralActionWitnessPair
import GaloisForLFunctions.HTGeometry.TracelessLocalHamiltonianGenericityLaw

open Set Topology
open scoped Matrix BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def PhysicallyRealizedEndpointCompleteSystem.spectralLinearEquiv
    (Z : PhysicallyRealizedEndpointCompleteSystem) :
    (Z.State → ℂ) ≃ₗ[ℂ] (Z.PhysicalState → ℂ) := by
  refine
    { toLinearMap := Matrix.mulVecLin Z.basis
      invFun := fun v => Z.basisᴴ *ᵥ v
      left_inv := ?_
      right_inv := ?_ }
  · intro v
    change Z.basisᴴ *ᵥ (Z.basis *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, Z.star_basis_mul_basis]
    exact Matrix.one_mulVec v
  · intro v
    change Z.basis *ᵥ (Z.basisᴴ *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, Z.basis_mul_star_basis]
    exact Matrix.one_mulVec v

theorem PhysicallyRealizedEndpointCompleteSystem.physicalCard_eq_stateCard
    (Z : PhysicallyRealizedEndpointCompleteSystem) :
    Fintype.card Z.PhysicalState = Fintype.card Z.State := by
  have hfin := Z.spectralLinearEquiv.finrank_eq
  simpa [Module.finrank_pi] using hfin.symm

def PhysicallyRealizedEndpointCompleteSystem.leafSpectralLinearEquiv
    (Z : PhysicallyRealizedEndpointCompleteSystem) :
    (Z.State × Bool → ℂ) ≃ₗ[ℂ] (Z.PhysicalState × Bool → ℂ) := by
  let U := tensorIdentityBasis (ρ := Bool) Z.basis
  have hleft : Uᴴ * U = (1 : Matrix (Z.State × Bool) (Z.State × Bool) ℂ) :=
    star_tensorIdentityBasis_mul_self Z.basis Z.star_basis_mul_basis
  have hright : U * Uᴴ =
      (1 : Matrix (Z.PhysicalState × Bool) (Z.PhysicalState × Bool) ℂ) :=
    tensorIdentityBasis_mul_star_self Z.basis Z.basis_mul_star_basis
  refine
    { toLinearMap := Matrix.mulVecLin U
      invFun := fun v => Uᴴ *ᵥ v
      left_inv := ?_
      right_inv := ?_ }
  · intro v
    change Uᴴ *ᵥ (U *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, hleft]
    exact Matrix.one_mulVec v
  · intro v
    change U *ᵥ (Uᴴ *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, hright]
    exact Matrix.one_mulVec v

theorem PhysicallyRealizedEndpointCompleteSystem.physicalLeaf_charpoly
    (Z : PhysicallyRealizedEndpointCompleteSystem)
    (shift : Bool → ℂ) (edge : Matrix Bool Bool ℂ) :
    (physicalLeafHamiltonian Z.hamiltonian Z.endpointProbe shift edge).charpoly =
      (localExtensionMatrix (fun i => (Z.energy i : ℂ)) shift Z.endpointTransition edge).charpoly := by
  let U := tensorIdentityBasis (ρ := Bool) Z.basis
  let Hphys := physicalLeafHamiltonian Z.hamiltonian Z.endpointProbe shift edge
  let Hspec := localExtensionMatrix (fun i => (Z.energy i : ℂ)) shift Z.endpointTransition edge
  have hcoordinate : Uᴴ * Hphys * U = Hspec := by
    exact tensorIdentityBasis_coordinate_physicalLeafHamiltonian
      Z.basis Z.hamiltonian Z.endpointProbe
      (fun i => (Z.energy i : ℂ)) shift Z.endpointTransition edge
      Z.star_basis_mul_basis Z.hamiltonian_coordinate rfl
  have hright : U * Uᴴ =
      (1 : Matrix (Z.PhysicalState × Bool) (Z.PhysicalState × Bool) ℂ) :=
    tensorIdentityBasis_mul_star_self Z.basis Z.basis_mul_star_basis
  have hrecover : Hphys = U * Hspec * Uᴴ := by
    calc
      Hphys = (1 : Matrix (Z.PhysicalState × Bool) (Z.PhysicalState × Bool) ℂ) *
          Hphys * 1 := by simp
      _ = (U * Uᴴ) * Hphys * (U * Uᴴ) := by rw [hright]
      _ = U * (Uᴴ * Hphys * U) * Uᴴ := by simp only [Matrix.mul_assoc]
      _ = U * Hspec * Uᴴ := by rw [hcoordinate]
  let e := Z.leafSpectralLinearEquiv
  have hconj : e.conj Hspec.mulVecLin = Hphys.mulVecLin := by
    apply LinearMap.ext
    intro v
    change U *ᵥ (Hspec *ᵥ (Uᴴ *ᵥ v)) = Hphys *ᵥ v
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    rw [hrecover]
  calc
    Hphys.charpoly = Hphys.mulVecLin.charpoly := (Matrix.charpoly_mulVecLin Hphys).symm
    _ = (e.conj Hspec.mulVecLin).charpoly := by rw [hconj]
    _ = Hspec.mulVecLin.charpoly := e.charpoly_conj Hspec.mulVecLin
    _ = Hspec.charpoly := Matrix.charpoly_mulVecLin Hspec

theorem hermitianEigenvalues_injective_of_injective_rootPacket
    {I : Type*} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (hH : H.IsHermitian)
    (energy : I → ℂ) (hinjective : Function.Injective energy)
    (hroot : ∀ i, matrixCharpolyRelation (H, energy i) = 0) :
    Function.Injective hH.eigenvalues := by
  let rootsPacket : Multiset ℂ := Finset.univ.val.map energy
  have hpacketNodup : rootsPacket.Nodup := by
    exact Finset.univ.nodup.map hinjective
  have hcharpolyNe : H.charpoly ≠ 0 := H.charpoly_monic.ne_zero
  have hpacketLe : rootsPacket ≤ H.charpoly.roots := by
    rw [Multiset.le_iff_subset hpacketNodup]
    intro z hz
    rcases Multiset.mem_map.mp hz with ⟨i, hi, rfl⟩
    rw [Polynomial.mem_roots hcharpolyNe]
    change H.charpoly.eval (energy i) = 0
    rw [Matrix.eval_charpoly]
    exact hroot i
  have hrootsCard : H.charpoly.roots.card = Fintype.card I := by
    rw [Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits H.charpoly)]
    exact H.charpoly_natDegree_eq_dim
  have hpacketCard : rootsPacket.card = Fintype.card I := by
    simp [rootsPacket]
  have hpacketEq : rootsPacket = H.charpoly.roots := by
    apply Multiset.eq_of_le_of_card_le hpacketLe
    rw [hrootsCard, hpacketCard]
  have heigenPacket : rootsPacket =
      Finset.univ.val.map (fun i => (hH.eigenvalues i : ℂ)) := by
    rw [hpacketEq, hH.roots_charpoly_eq_eigenvalues]
    rfl
  have heigenNodup :
      (Finset.univ.val.map (fun i => (hH.eigenvalues i : ℂ))).Nodup := by
    rw [← heigenPacket]
    exact hpacketNodup
  have hmapInjective : Function.Injective (fun i => (hH.eigenvalues i : ℂ)) := by
    intro a b hab
    exact (Multiset.nodup_map_iff_inj_on Finset.univ.nodup).mp heigenNodup
      a (Finset.mem_univ a) b (Finset.mem_univ b) hab
  intro i j hij
  apply hmapInjective
  exact congrArg (fun x : ℝ => (x : ℂ)) hij

def realPhysicalLeafParameter6 (q : Fin 6 → ℝ) :
    (Bool → ℂ) × Matrix Bool Bool ℂ :=
  (physShift (fun i => (q i : ℂ)), physEdge (fun i => (q i : ℂ)))

theorem continuous_realPhysicalLeafParameter6 : Continuous realPhysicalLeafParameter6 := by
  have hs : Continuous (fun q : Fin 6 → ℝ => physShift (fun i => (q i : ℂ))) := by
    refine continuous_pi fun b : Bool => ?_
    cases b <;> simp only [physShift] <;> fun_prop
  have he : Continuous (fun q : Fin 6 → ℝ => physEdge (fun i => (q i : ℂ))) := by
    refine continuous_pi fun u : Bool => continuous_pi fun v : Bool => ?_
    cases u <;> cases v <;> simp only [physEdge] <;> fun_prop
  exact hs.prodMk he

def physicalSplitCenter (z : ℝ) : Fin 6 → ℝ :=
  fun i => if i = 0 then z / 2 else if i = 1 then -(z / 2) else 0

theorem realPhysicalLeafParameter6_splitCenter (z : ℝ) :
    realPhysicalLeafParameter6 (physicalSplitCenter z) = (boolShift (z : ℂ), 0) := by
  apply Prod.ext
  · funext b
    cases b <;>
      simp [realPhysicalLeafParameter6, physicalSplitCenter, physShift, boolShift]
  · ext u v
    cases u <;> cases v <;>
      simp [realPhysicalLeafParameter6, physicalSplitCenter, physEdge]

def PhysicallyRealizedEndpointCompleteSystem.leafLocalSubmodule
    (Z : PhysicallyRealizedEndpointCompleteSystem) :
    Submodule ℝ (Matrix (Z.PhysicalState × Bool) (Z.PhysicalState × Bool) ℂ) :=
  (RootedTensorTree.leaf Z.tree Bool Z.endpoint).hermitianLocalHamiltonianSubmodule

theorem PhysicallyRealizedEndpointCompleteSystem.leafLocalSubmodule_le_selfAdjoint
    (Z : PhysicallyRealizedEndpointCompleteSystem) :
    Z.leafLocalSubmodule ≤
      selfAdjoint.submodule ℝ
        (Matrix (Z.PhysicalState × Bool) (Z.PhysicalState × Bool) ℂ) :=
  (RootedTensorTree.leaf Z.tree Bool Z.endpoint).hermitianLocalHamiltonianSubmodule_le_selfAdjoint

def PhysicallyRealizedEndpointCompleteSystem.leafLocalParameterCount
    (Z : PhysicallyRealizedEndpointCompleteSystem) : ℕ :=
  Module.finrank ℝ Z.leafLocalSubmodule

noncomputable def PhysicallyRealizedEndpointCompleteSystem.leafLocalTraceGenerator
    (Z : PhysicallyRealizedEndpointCompleteSystem) :
    Fin Z.leafLocalParameterCount →
      Matrix (Z.PhysicalState × Bool) (Z.PhysicalState × Bool) ℂ :=
  traceOrthonormalSubmoduleGenerator Z.leafLocalSubmodule
    Z.leafLocalSubmodule_le_selfAdjoint

def PhysicallyRealizedEndpointCompleteSystem.leafPhysicalIndexEquiv
    (Z : PhysicallyRealizedEndpointCompleteSystem) :
    (Z.PhysicalState × Bool) ≃ Fin (Fintype.card (Z.PhysicalState × Bool)) :=
  Fintype.equivFin _

def PhysicallyRealizedEndpointCompleteSystem.leafSpectralToPhysicalEquiv
    (Z : PhysicallyRealizedEndpointCompleteSystem) :
    (Z.State × Bool) ≃ (Z.PhysicalState × Bool) :=
  Equiv.prodCongr
    (Fintype.equivOfCardEq Z.physicalCard_eq_stateCard).symm
    (Equiv.refl Bool)

def PhysicallyRealizedEndpointCompleteSystem.leafSpectralIndexEquiv
    (Z : PhysicallyRealizedEndpointCompleteSystem) :
    (Z.State × Bool) ≃ Fin (Fintype.card (Z.PhysicalState × Bool)) :=
  Z.leafSpectralToPhysicalEquiv.trans Z.leafPhysicalIndexEquiv

noncomputable def PhysicallyRealizedEndpointCompleteSystem.leafLocalTraceGeneratorFin
    (Z : PhysicallyRealizedEndpointCompleteSystem) :
    Fin Z.leafLocalParameterCount →
      Matrix (Fin (Fintype.card (Z.PhysicalState × Bool)))
        (Fin (Fintype.card (Z.PhysicalState × Bool))) ℂ :=
  fun a => Matrix.reindex Z.leafPhysicalIndexEquiv Z.leafPhysicalIndexEquiv
    (Z.leafLocalTraceGenerator a)

theorem trace_reindex_equiv {A B : Type*} [Fintype A] [Fintype B]
    (e : A ≃ B) (M : Matrix A A ℂ) :
    (Matrix.reindex e e M).trace = M.trace := by
  rw [Matrix.trace, Matrix.trace]
  change (∑ i : B, M (e.symm i) (e.symm i)) = ∑ i : A, M i i
  exact Equiv.sum_comp e.symm (fun i : A => M i i)

theorem PhysicallyRealizedEndpointCompleteSystem.leafLocalTraceGeneratorFin_isHermitian
    (Z : PhysicallyRealizedEndpointCompleteSystem) (a : Fin Z.leafLocalParameterCount) :
    (Z.leafLocalTraceGeneratorFin a).IsHermitian :=
  (traceOrthonormalSubmoduleGenerator_isHermitian Z.leafLocalSubmodule
    Z.leafLocalSubmodule_le_selfAdjoint a).reindex Z.leafPhysicalIndexEquiv

theorem PhysicallyRealizedEndpointCompleteSystem.leafLocalTraceGeneratorFin_trace_mul
    (Z : PhysicallyRealizedEndpointCompleteSystem) (a b : Fin Z.leafLocalParameterCount) :
    (Z.leafLocalTraceGeneratorFin a * Z.leafLocalTraceGeneratorFin b).trace =
      if a = b then (1 : ℂ) else 0 := by
  change ((Matrix.reindex Z.leafPhysicalIndexEquiv Z.leafPhysicalIndexEquiv
      (Z.leafLocalTraceGenerator a)) *
    (Matrix.reindex Z.leafPhysicalIndexEquiv Z.leafPhysicalIndexEquiv
      (Z.leafLocalTraceGenerator b))).trace = _
  have hmul := map_mul (Matrix.reindexAlgEquiv ℂ ℂ Z.leafPhysicalIndexEquiv)
    (Z.leafLocalTraceGenerator a) (Z.leafLocalTraceGenerator b)
  have hmul' : Matrix.reindex Z.leafPhysicalIndexEquiv Z.leafPhysicalIndexEquiv
      (Z.leafLocalTraceGenerator a * Z.leafLocalTraceGenerator b) =
      Matrix.reindex Z.leafPhysicalIndexEquiv Z.leafPhysicalIndexEquiv
          (Z.leafLocalTraceGenerator a) *
        Matrix.reindex Z.leafPhysicalIndexEquiv Z.leafPhysicalIndexEquiv
          (Z.leafLocalTraceGenerator b) := by
    simpa only [Matrix.coe_reindexAlgEquiv] using hmul
  rw [← hmul', trace_reindex_equiv]
  exact traceOrthonormalSubmoduleGenerator_trace_mul Z.leafLocalSubmodule
    Z.leafLocalSubmodule_le_selfAdjoint a b

theorem PhysicallyRealizedEndpointCompleteSystem.leafLocalParameterCount_pos
    (Z : PhysicallyRealizedEndpointCompleteSystem) : 0 < Z.leafLocalParameterCount := by
  let T := RootedTensorTree.leaf Z.tree Bool Z.endpoint
  letI : DecidableEq (Z.PhysicalState × Bool) := T.physicalDecidableEq
  have hphysicalCard : 0 < Fintype.card Z.PhysicalState := by
    rw [Z.physicalCard_eq_stateCard]
    exact lt_of_lt_of_le (by norm_num) Z.three_le_stateCard
  letI : Nonempty Z.PhysicalState := Fintype.card_pos_iff.mp hphysicalCard
  have hone :
      (1 : Matrix (Z.PhysicalState × Bool) (Z.PhysicalState × Bool) ℂ) ≠ 0 :=
    one_ne_zero
  have hmem :
      (1 : Matrix (Z.PhysicalState × Bool) (Z.PhysicalState × Bool) ℂ) ∈
        Z.leafLocalSubmodule :=
    RootedTensorTree.mem_hermitianLocalHamiltonianSubmodule _
      (RootedTensorTree.isLocalHamiltonian_one T) Matrix.isHermitian_one
  apply Module.finrank_pos_iff_exists_ne_zero.mpr
  refine ⟨⟨1, hmem⟩, ?_⟩
  intro hzero
  exact hone (congrArg Subtype.val hzero)

theorem PhysicallyRealizedEndpointCompleteSystem.exists_leafLocal_simple_energy_witness
    (Z : PhysicallyRealizedEndpointCompleteSystem)
    (k : Fin (Fintype.card (Z.PhysicalState × Bool)) → ℝ)
    (hksum : ∑ i, k i = 0) (hkne : k ≠ 0) (κ : ℝ) :
    ∃ θ : Fin Z.leafLocalParameterCount → ℝ,
      Function.Injective
          (isHermitian_spectralEnsembleMatrix
            Z.leafLocalTraceGeneratorFin_isHermitian θ).eigenvalues ∧
        ∀ π : Equiv.Perm (Fin (Fintype.card (Z.PhysicalState × Bool))),
        (∑ j, k j *
          (isHermitian_spectralEnsembleMatrix
            Z.leafLocalTraceGeneratorFin_isHermitian θ).eigenvalues (π j)) ^ 2 ≠
          κ * ∑ i,
            ((isHermitian_spectralEnsembleMatrix
              Z.leafLocalTraceGeneratorFin_isHermitian θ).eigenvalues i) ^ 2 := by
  classical
  let M : Matrix Z.State Z.State ℂ := Z.endpointTransition
  have hMherm : M.IsHermitian :=
    Matrix.isHermitian_conjTranspose_mul_mul Z.basis Z.endpointProbe_isHermitian
  have hM : ∀ a b : Z.State, a ≠ b → M b a ≠ 0 := by
    intro a b hab
    exact Z.endpointTransition_ne_zero b a hab.symm
  have hE : Function.Injective (fun a => (Z.energy a : ℂ)) := by
    intro a b hab
    exact Z.energy_maximallyProjective.injective (Complex.ofReal_injective hab)
  have hgap : ∀ α β γ δ : Z.State, α ≠ β → γ ≠ δ →
      ((Z.energy β : ℂ) - (Z.energy α : ℂ)) =
        ((Z.energy δ : ℂ) - (Z.energy γ : ℂ)) →
      (α, β) = (γ, δ) := by
    intro α β γ δ hαβ hγδ hcomplex
    let p : {p : Z.State × Z.State // p.1 ≠ p.2} := ⟨(β, α), hαβ.symm⟩
    let q : {p : Z.State × Z.State // p.1 ≠ p.2} := ⟨(δ, γ), hγδ.symm⟩
    have hreal : Z.energy β - Z.energy α = Z.energy δ - Z.energy γ := by
      exact Complex.ofReal_injective (by simpa using hcomplex)
    have hpq : p = q :=
      (maximallyProjectiveEnergy_orientedGap_injective
        Z.energy Z.energy_maximallyProjective) hreal
    have hpairs : (β, α) = (δ, γ) := congrArg Subtype.val hpq
    exact Prod.ext (congrArg Prod.snd hpairs) (congrArg Prod.fst hpairs)
  obtain ⟨z, hz⟩ := exists_real_admissible_split_shift Z.energy
  have hbase : Function.Injective
      (layeredEnergy (fun a => (Z.energy a : ℂ)) (boolShift (z : ℂ))) := by
    rw [layeredEnergy_boolShift]
    exact injective_layerSplitEnergy hE hz
  obtain ⟨C⟩ := exists_localExtensionEigenbranchChart
    (fun a => (Z.energy a : ℂ)) (boolShift (z : ℂ)) M hbase
  let V : Set (Fin 6 → ℝ) := realPhysicalLeafParameter6 ⁻¹' C.U
  have hVopen : IsOpen V := C.isOpen_U.preimage continuous_realPhysicalLeafParameter6
  have hVne : V.Nonempty := by
    refine ⟨physicalSplitCenter z, ?_⟩
    change realPhysicalLeafParameter6 (physicalSplitCenter z) ∈ C.U
    rw [realPhysicalLeafParameter6_splitCenter]
    exact C.center_mem
  let e := Z.leafSpectralIndexEquiv
  let c : Z.State × Bool → ℂ := fun i => (k (e i) : ℂ)
  have hczero : ∑ i, c i = 0 := by
    change ∑ i, ((k (e i) : ℝ) : ℂ) = 0
    rw [← Complex.ofReal_sum, Equiv.sum_comp e k, hksum]
    simp
  have hcne : c ≠ 0 := by
    intro hc
    apply hkne
    funext x
    have hx := congrFun hc (e.symm x)
    exact Complex.ofReal_injective (by simpa [c, e] using hx)
  obtain ⟨q, hqV, hedge, hshift, hfail⟩ :=
    exists_mem_real_physicalLeaf_quadraticRate_ne_zero
      Z.three_le_stateCard hE hgap hMherm hM hbase C c (κ : ℂ)
      hczero hcne hVopen hVne
  let p := realPhysicalLeafParameter6 q
  have hp : p ∈ C.U := hqV
  let Hphys : Matrix (Z.PhysicalState × Bool) (Z.PhysicalState × Bool) ℂ :=
    physicalLeafHamiltonian Z.hamiltonian Z.endpointProbe p.1 p.2
  have hHphys : Hphys.IsHermitian :=
    isHermitian_physicalLeafHamiltonian
      (by
        rw [Z.hamiltonian_eq_diagonal]
        exact Matrix.isHermitian_mul_mul_conjTranspose Z.basis
          (isHermitian_diagonal_of_star
            (fun i => Complex.conj_ofReal (Z.energy i))))
      Z.endpointProbe_isHermitian hshift hedge
  have hHlocal : (RootedTensorTree.leaf Z.tree Bool Z.endpoint).IsLocalHamiltonian Hphys :=
    isLocalHamiltonian_physicalLeaf Z.tree Z.endpoint Z.hamiltonian Z.endpointProbe
      p.1 p.2 Z.hamiltonian_local Z.endpointProbe_local
  have hHmem : Hphys ∈ Z.leafLocalSubmodule :=
    RootedTensorTree.mem_hermitianLocalHamiltonianSubmodule _ hHlocal hHphys
  obtain ⟨θ, hθ⟩ := exists_traceOrthonormalCoordinates Z.leafLocalSubmodule
    Z.leafLocalSubmodule_le_selfAdjoint hHmem
  let f := Z.leafPhysicalIndexEquiv
  let Hfin := Matrix.reindex f f Hphys
  have hHfin : Hfin.IsHermitian := hHphys.reindex f
  have hensemble : spectralEnsembleMatrix Z.leafLocalTraceGeneratorFin θ = Hfin := by
    ext i j
    have hentry := congrFun (congrFun hθ (f.symm i)) (f.symm j)
    simp only [spectralEnsembleMatrix, Matrix.sum_apply, Matrix.smul_apply,
      PhysicallyRealizedEndpointCompleteSystem.leafLocalTraceGeneratorFin,
      Matrix.reindex_apply, Matrix.submatrix_apply, f, Hfin]
    change
      (∑ x, (θ x : ℂ) * Z.leafLocalTraceGenerator x (f.symm i) (f.symm j)) =
        Hphys (f.symm i) (f.symm j)
    simpa only [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul,
      smul_eq_mul,
      PhysicallyRealizedEndpointCompleteSystem.leafLocalTraceGenerator] using hentry
  let Hspec := localExtensionMatrix (fun i => (Z.energy i : ℂ)) p.1 M p.2
  have hcharpoly : Hfin.charpoly = Hspec.charpoly := by
    calc
      Hfin.charpoly = Hphys.charpoly := Matrix.charpoly_reindex f Hphys
      _ = Hspec.charpoly := Z.physicalLeaf_charpoly p.1 p.2
  let branchFin : Fin (Fintype.card (Z.PhysicalState × Bool)) → ℂ :=
    fun x => C.branch (e.symm x) p
  have hbranchInj : Function.Injective branchFin := by
    exact (C.simple p hp).comp e.symm.injective
  have hbranchRoot : ∀ x, matrixCharpolyRelation (Hfin, branchFin x) = 0 := by
    intro x
    change (Matrix.scalar _ (branchFin x) - Hfin).det = 0
    rw [← Matrix.eval_charpoly]
    rw [hcharpoly, Matrix.eval_charpoly]
    exact C.root p hp (e.symm x)
  have heigenInj : Function.Injective hHfin.eigenvalues :=
    hermitianEigenvalues_injective_of_injective_rootPacket
      Hfin hHfin branchFin hbranchInj hbranchRoot
  have hrootSpec : ∀ i : Z.State × Bool,
      matrixCharpolyRelation (Hspec, (hHfin.eigenvalues (e i) : ℂ)) = 0 := by
    intro i
    change
      (Matrix.scalar _ ((hHfin.eigenvalues (e i) : ℂ)) - Hspec).det = 0
    rw [← Matrix.eval_charpoly, ← hcharpoly, Matrix.eval_charpoly]
    exact (mem_range_hermitianEigenvalues_iff hHfin
      (hHfin.eigenvalues (e i))).mp ⟨e i, rfl⟩
  have hfailEigen := hfail
    (fun i => (hHfin.eigenvalues (e i) : ℂ))
    (fun i j hij => e.injective (heigenInj (Complex.ofReal_injective hij)))
    hrootSpec
  let hP : ∀ a, (Z.leafLocalTraceGeneratorFin a).IsHermitian :=
    Z.leafLocalTraceGeneratorFin_isHermitian
  have heigen :
      (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues = hHfin.eigenvalues := by
    apply (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
      (isHermitian_spectralEnsembleMatrix hP θ) hHfin).2
    exact congrArg Matrix.charpoly hensemble
  refine ⟨θ, ?_, ?_⟩
  · rw [heigen]
    exact heigenInj
  intro π hcollision
  rw [heigen] at hcollision
  let σ : Equiv.Perm (Z.State × Bool) := (e.trans π).trans e.symm
  apply hfailEigen σ
  have hL1 :
      (∑ j : Z.State × Bool,
        c (σ.symm j) * (hHfin.eigenvalues (e j) : ℂ)) =
      ∑ y, ((k (π.symm y) : ℝ) : ℂ) * (hHfin.eigenvalues y : ℂ) := by
    apply Fintype.sum_equiv e
    intro j
    simp [c, σ, e]
  have hL2 :
      (∑ y, ((k (π.symm y) : ℝ) : ℂ) * (hHfin.eigenvalues y : ℂ)) =
      ∑ x, ((k x : ℝ) : ℂ) * (hHfin.eigenvalues (π x) : ℂ) := by
    refine (Equiv.sum_comp π
      (fun y => ((k (π.symm y) : ℝ) : ℂ) *
        (hHfin.eigenvalues y : ℂ))).symm.trans ?_
    exact Finset.sum_congr rfl fun x _ => by rw [Equiv.symm_apply_apply]
  have hL :
      (∑ j : Z.State × Bool,
        c (σ.symm j) * (hHfin.eigenvalues (e j) : ℂ)) =
      (((∑ x, k x * hHfin.eigenvalues (π x) : ℝ)) : ℂ) := by
    rw [hL1, hL2, Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun x _ => by push_cast; ring
  have hR :
      (∑ j : Z.State × Bool, (hHfin.eigenvalues (e j) : ℂ) ^ 2) =
      (((∑ y, (hHfin.eigenvalues y) ^ 2 : ℝ)) : ℂ) := by
    rw [Equiv.sum_comp e (fun y => (hHfin.eigenvalues y : ℂ) ^ 2),
      Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun j _ => by push_cast; ring
  rw [hL, hR, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    ← Complex.ofReal_sub, hcollision]
  simp

/-- Energy-form corollary of the simple-spectrum local witness. -/
theorem PhysicallyRealizedEndpointCompleteSystem.exists_leafLocal_energy_witness
    (Z : PhysicallyRealizedEndpointCompleteSystem)
    (k : Fin (Fintype.card (Z.PhysicalState × Bool)) → ℝ)
    (hksum : ∑ i, k i = 0) (hkne : k ≠ 0) (κ : ℝ) :
    ∃ θ : Fin Z.leafLocalParameterCount → ℝ,
      ∀ π : Equiv.Perm (Fin (Fintype.card (Z.PhysicalState × Bool))),
        (∑ j, k j *
          (isHermitian_spectralEnsembleMatrix
            Z.leafLocalTraceGeneratorFin_isHermitian θ).eigenvalues (π j)) ^ 2 ≠
          κ * ∑ i,
            ((isHermitian_spectralEnsembleMatrix
              Z.leafLocalTraceGeneratorFin_isHermitian θ).eigenvalues i) ^ 2 := by
  obtain ⟨θ, -, hθ⟩ := Z.exists_leafLocal_simple_energy_witness k hksum hkne κ
  exact ⟨θ, hθ⟩

/-- The concrete local ensemble has a nonzero spectral discriminant: its simple-spectrum premise
is a theorem, not an external genericity assumption. -/
theorem PhysicallyRealizedEndpointCompleteSystem.leafLocal_spectralDiscriminantPoly_ne_zero
    (Z : PhysicallyRealizedEndpointCompleteSystem)
    (k : Fin (Fintype.card (Z.PhysicalState × Bool)) → ℝ)
    (hksum : ∑ i, k i = 0) (hkne : k ≠ 0) :
    spectralDiscriminantPoly Z.leafLocalTraceGeneratorFin ≠ 0 := by
  let hP : ∀ a, (Z.leafLocalTraceGeneratorFin a).IsHermitian :=
    Z.leafLocalTraceGeneratorFin_isHermitian
  obtain ⟨θ, hsimple, -⟩ :=
    Z.exists_leafLocal_simple_energy_witness k hksum hkne 0
  exact spectralDiscriminantPoly_ne_zero hP hsimple

/-- Two fixed local Hamiltonians whose squared labelled spectral-action ratios are disjoint. -/
theorem PhysicallyRealizedEndpointCompleteSystem.exists_leafLocal_disjoint_actionRatio_pair
    (Z : PhysicallyRealizedEndpointCompleteSystem)
    (k : Fin (Fintype.card (Z.PhysicalState × Bool)) → ℝ)
    (hksum : ∑ i, k i = 0) (hkne : k ≠ 0) :
    ∃ θ₁ θ₂ : Fin Z.leafLocalParameterCount → ℝ,
      ∀ π₁ π₂ : Equiv.Perm (Fin (Fintype.card (Z.PhysicalState × Bool))),
        (∑ j, k j *
            (isHermitian_spectralEnsembleMatrix
              Z.leafLocalTraceGeneratorFin_isHermitian θ₁).eigenvalues (π₁ j)) ^ 2
              * (∑ a, (θ₂ a) ^ 2)
          ≠ (∑ j, k j *
            (isHermitian_spectralEnsembleMatrix
              Z.leafLocalTraceGeneratorFin_isHermitian θ₂).eigenvalues (π₂ j)) ^ 2
              * (∑ a, (θ₁ a) ^ 2) := by
  let hP : ∀ a, (Z.leafLocalTraceGeneratorFin a).IsHermitian :=
    Z.leafLocalTraceGeneratorFin_isHermitian
  apply exists_disjoint_actionRatio_pair_of_witness_of_pos hP k
    Z.leafLocalParameterCount_pos
  exact exists_witness_of_energy_witness hP k (c := 1) zero_lt_one
    Z.leafLocalTraceGeneratorFin_trace_mul
    (Z.exists_leafLocal_energy_witness k hksum hkne)

/-- The final leaf extension of the `n`th recursive physical qubit path acts on exactly `n + 3`
qubits. -/
@[simp] theorem physicalEndpointCompleteQubitPath_leafPhysicalCard (n : ℕ) :
    Fintype.card ((physicalEndpointCompleteQubitPath n).PhysicalState × Bool) =
      2 ^ (n + 3) := by
  rw [Fintype.card_prod, Fintype.card_bool,
    physicalEndpointCompleteQubitPath_physicalCard]
  ring

/-- **Concrete path-local two-Hamiltonian witness.**  On every member of the recursive qubit-path
family, and for every balanced nonzero spectral character, two fixed Hamiltonians from the full
Hermitian nearest-neighbour local submodule have disjoint squared spectral-action ratios under
all possible spectral labellings.  The final system has `n + 3` qubits by
`physicalEndpointCompleteQubitPath_leafPhysicalCard`. -/
theorem exists_physicalEndpointCompleteQubitPath_disjoint_actionRatio_pair
    (n : ℕ)
    (k : Fin (Fintype.card
      ((physicalEndpointCompleteQubitPath n).PhysicalState × Bool)) → ℝ)
    (hksum : ∑ i, k i = 0) (hkne : k ≠ 0) :
    ∃ θ₁ θ₂ : Fin
        (physicalEndpointCompleteQubitPath n).leafLocalParameterCount → ℝ,
      ∀ π₁ π₂ : Equiv.Perm (Fin (Fintype.card
          ((physicalEndpointCompleteQubitPath n).PhysicalState × Bool))),
        (∑ j, k j *
            (isHermitian_spectralEnsembleMatrix
              (physicalEndpointCompleteQubitPath n).leafLocalTraceGeneratorFin_isHermitian
                θ₁).eigenvalues (π₁ j)) ^ 2
              * (∑ a, (θ₂ a) ^ 2)
          ≠ (∑ j, k j *
            (isHermitian_spectralEnsembleMatrix
              (physicalEndpointCompleteQubitPath n).leafLocalTraceGeneratorFin_isHermitian
                θ₂).eigenvalues (π₂ j)) ^ 2
              * (∑ a, (θ₁ a) ^ 2) :=
  (physicalEndpointCompleteQubitPath n).exists_leafLocal_disjoint_actionRatio_pair
    k hksum hkne

/-- The recursive qubit-path ensemble itself satisfies the simple-spectrum polynomial premise. -/
theorem physicalEndpointCompleteQubitPath_leafLocal_spectralDiscriminantPoly_ne_zero
    (n : ℕ)
    (k : Fin (Fintype.card
      ((physicalEndpointCompleteQubitPath n).PhysicalState × Bool)) → ℝ)
    (hksum : ∑ i, k i = 0) (hkne : k ≠ 0) :
    spectralDiscriminantPoly
      (physicalEndpointCompleteQubitPath n).leafLocalTraceGeneratorFin ≠ 0 :=
  (physicalEndpointCompleteQubitPath n).leafLocal_spectralDiscriminantPoly_ne_zero
    k hksum hkne

end
end GaloisForLFunctions.HTGeometry
