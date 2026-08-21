/-
# The nonflatness witness inside the nearest-neighbour Pauli span

Running the traceless slice escape on the endpoint-complete Pauli seed produces, at every rate, a
Hamiltonian of the card's own nearest-neighbour Pauli family whose spectrum is a simple root packet
on which no relabelling of the quadratic-rate relation holds.

Main results:
* `charpoly_physicalLeafHamiltonian` — a physical leaf extension and its spectral local-extension
  matrix have the same characteristic polynomial.
* `exists_pauliChain_spanWitness` — **the nonflatness witness in the chain span**.
-/
import GaloisForLFunctions.HTGeometry.ChainPauliFinFamily
import GaloisForLFunctions.HTGeometry.PauliChainSeedInduction
import GaloisForLFunctions.HTGeometry.SliceChartCoordinates
import GaloisForLFunctions.HTGeometry.PhysicalLeafPauliChainSpan
import GaloisForLFunctions.HTGeometry.ExtensionStepQuadraticOrbit
import GaloisForLFunctions.HTGeometry.LayerSplitEndpointStep

open Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

/-- The unitary change of coordinates as a linear equivalence. -/
def unitaryMulVecEquiv {P I : Type*} [Fintype P] [Fintype I] [DecidableEq P] [DecidableEq I]
    {T : Matrix P I ℂ} (hleft : Tᴴ * T = (1 : Matrix I I ℂ))
    (hright : T * Tᴴ = (1 : Matrix P P ℂ)) : (I → ℂ) ≃ₗ[ℂ] (P → ℂ) where
  toLinearMap := Matrix.mulVecLin T
  invFun := fun v => Tᴴ *ᵥ v
  left_inv := by
    intro v
    change Tᴴ *ᵥ (T *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, hleft]
    exact Matrix.one_mulVec v
  right_inv := by
    intro v
    change T *ᵥ (Tᴴ *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, hright]
    exact Matrix.one_mulVec v

/-- **A physical leaf extension and its spectral local-extension matrix are similar**, hence have
the same characteristic polynomial. -/
theorem charpoly_physicalLeafHamiltonian {P I : Type*} [Fintype P] [Fintype I]
    [DecidableEq P] [DecidableEq I]
    (U : Matrix P I ℂ) (hUleft : Uᴴ * U = (1 : Matrix I I ℂ))
    (hUright : U * Uᴴ = (1 : Matrix P P ℂ))
    (energy : I → ℂ) (parent : Matrix P P ℂ) (shift : Bool → ℂ) (edge : Matrix Bool Bool ℂ) :
    (physicalLeafHamiltonian (U * Matrix.diagonal energy * Uᴴ) parent shift edge).charpoly
      = (localExtensionMatrix energy shift (Uᴴ * parent * U) edge).charpoly := by
  obtain ⟨T, hT⟩ : ∃ T, T = tensorIdentityBasis (ρ := Bool) U := ⟨_, rfl⟩
  have hleft : Tᴴ * T = (1 : Matrix (I × Bool) (I × Bool) ℂ) := by
    rw [hT]; exact star_tensorIdentityBasis_mul_self U hUleft
  have hright : T * Tᴴ = (1 : Matrix (P × Bool) (P × Bool) ℂ) := by
    rw [hT]; exact tensorIdentityBasis_mul_star_self U hUright
  have hcoordinate : Tᴴ * physicalLeafHamiltonian (U * Matrix.diagonal energy * Uᴴ) parent
      shift edge * T = localExtensionMatrix energy shift (Uᴴ * parent * U) edge := by
    rw [hT]
    exact physicalLeafHamiltonian_conj_tensorIdentityBasis U hUleft energy parent shift edge
  have hrecover : physicalLeafHamiltonian (U * Matrix.diagonal energy * Uᴴ) parent shift edge
      = T * (localExtensionMatrix energy shift (Uᴴ * parent * U) edge) * Tᴴ := by
    calc physicalLeafHamiltonian (U * Matrix.diagonal energy * Uᴴ) parent shift edge
        = (T * Tᴴ) * physicalLeafHamiltonian (U * Matrix.diagonal energy * Uᴴ) parent shift edge
            * (T * Tᴴ) := by rw [hright]; simp
      _ = T * (Tᴴ * physicalLeafHamiltonian (U * Matrix.diagonal energy * Uᴴ) parent shift edge
            * T) * Tᴴ := by simp only [Matrix.mul_assoc]
      _ = T * (localExtensionMatrix energy shift (Uᴴ * parent * U) edge) * Tᴴ := by
          rw [hcoordinate]
  have hconj : (unitaryMulVecEquiv hleft hright).conj
      (localExtensionMatrix energy shift (Uᴴ * parent * U) edge).mulVecLin
      = (physicalLeafHamiltonian (U * Matrix.diagonal energy * Uᴴ) parent shift edge).mulVecLin := by
    apply LinearMap.ext
    intro v
    change T *ᵥ ((localExtensionMatrix energy shift (Uᴴ * parent * U) edge) *ᵥ (Tᴴ *ᵥ v))
      = _ *ᵥ v
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hrecover, Matrix.mul_assoc]
  calc (physicalLeafHamiltonian (U * Matrix.diagonal energy * Uᴴ) parent shift edge).charpoly
      = (physicalLeafHamiltonian (U * Matrix.diagonal energy * Uᴴ) parent
          shift edge).mulVecLin.charpoly :=
        (Matrix.charpoly_mulVecLin _).symm
    _ = ((unitaryMulVecEquiv hleft hright).conj
          (localExtensionMatrix energy shift (Uᴴ * parent * U) edge).mulVecLin).charpoly := by
        rw [hconj]
    _ = (localExtensionMatrix energy shift (Uᴴ * parent * U) edge).mulVecLin.charpoly :=
        (unitaryMulVecEquiv hleft hright).charpoly_conj _
    _ = (localExtensionMatrix energy shift (Uᴴ * parent * U) edge).charpoly :=
        Matrix.charpoly_mulVecLin _

theorem card_seedIndexLeaf (k : ℕ) : Fintype.card (seedIndex k × Bool) = 2 ^ (k + 3) := by
  rw [Fintype.card_prod, Fintype.card_bool, card_seedIndex k]
  ring

/-- The numbering of the spectral index of the `k`-th leaf extension. -/
def seedLeafFin (k : ℕ) : seedIndex k × Bool ≃ Fin (2 ^ (k + 3)) :=
  Fintype.equivFinOfCardEq (card_seedIndexLeaf k)

/-- **The nonflatness witness in the nearest-neighbour Pauli span.**  At every rate and every
balanced nonzero spectral character there is a Hamiltonian of the card's own nearest-neighbour
Pauli family whose spectrum is a simple root packet failing every relabelled quadratic-rate
relation. -/
theorem exists_pauliChain_spanWitness (k : ℕ) (κ : ℝ)
    (kvec : Fin (2 ^ (k + 3)) → ℝ) (hksum : ∑ j, kvec j = 0) (hkne : kvec ≠ 0) :
    ∃ (H₀ : Matrix (Fin (2 ^ (k + 3))) (Fin (2 ^ (k + 3))) ℂ)
      (energy₀ : Fin (2 ^ (k + 3)) → ℂ),
      H₀ ∈ Submodule.span ℝ (Set.range (chainPauliFin (k + 3))) ∧
      Function.Injective energy₀ ∧
      (∀ j, matrixCharpolyRelation (H₀, energy₀ j) = 0) ∧
      ∀ σ : Equiv.Perm (Fin (2 ^ (k + 3))),
        (∑ j, ((kvec (σ.symm j) : ℝ) : ℂ) * energy₀ j) ^ 2
          - ((κ : ℝ) : ℂ) * ∑ j, energy₀ j ^ 2 ≠ 0 := by
  classical
  obtain ⟨E, U, V, hEmax, hEsum, hUleft, hUright, hVherm, hVspan, hHspan, hVtrans⟩ :=
    exists_pauliChainSeed k
  obtain ⟨M, hMdef⟩ : ∃ M, M = Uᴴ * V * U := ⟨_, rfl⟩
  have hMherm : M.IsHermitian := by
    rw [hMdef]; exact Matrix.isHermitian_conjTranspose_mul_mul U hVherm
  have hM : ∀ α β : seedIndex k, α ≠ β → M β α ≠ 0 := by
    intro α β hαβ
    rw [hMdef]
    exact hVtrans β α (Ne.symm hαβ)
  have hE : Function.Injective fun a => ((E a : ℝ) : ℂ) := by
    intro a b hab
    exact MaximallyProjectiveEnergy.injective hEmax (Complex.ofReal_injective hab)
  have hgap : ∀ α β γ δ : seedIndex k, α ≠ β → γ ≠ δ →
      ((E β : ℂ) - (E α : ℂ)) = ((E δ : ℂ) - (E γ : ℂ)) → (α, β) = (γ, δ) := by
    intro α β γ δ hαβ hγδ hcomplex
    have hreal : E β - E α = E δ - E γ :=
      Complex.ofReal_injective (by push_cast; exact hcomplex)
    have hpq : (⟨(β, α), hαβ.symm⟩ : {p : seedIndex k × seedIndex k // p.1 ≠ p.2})
        = ⟨(δ, γ), hγδ.symm⟩ :=
      (maximallyProjectiveEnergy_orientedGap_injective E hEmax) hreal
    have hpairs : (β, α) = (δ, γ) := congrArg Subtype.val hpq
    exact Prod.ext (congrArg Prod.snd hpairs) (congrArg Prod.fst hpairs)
  obtain ⟨z, hz⟩ := exists_real_admissible_split_shift E
  have hbase : Function.Injective
      (layeredEnergy (fun a => ((E a : ℝ) : ℂ)) (boolShift ((z : ℝ) : ℂ))) := by
    rw [layeredEnergy_boolShift]
    exact injective_layerSplitEnergy hE hz
  obtain ⟨C⟩ := exists_localExtensionEigenbranchChart
    (fun a => ((E a : ℝ) : ℂ)) (boolShift ((z : ℝ) : ℂ)) M hbase
  obtain ⟨W, hWdef⟩ : ∃ W : Set (Fin 2 → ℝ), W = realSliceParameter ⁻¹' C.U := ⟨_, rfl⟩
  have hWopen : IsOpen W := by
    rw [hWdef]; exact C.isOpen_U.preimage continuous_realSliceParameter
  have hWne : W.Nonempty := by
    refine ⟨![z, 0], ?_⟩
    rw [hWdef]
    show realSliceParameter ![z, 0] ∈ C.U
    have hpt : realSliceParameter ![z, 0] = (boolShift ((z : ℝ) : ℂ), 0) := by
      refine Prod.ext rfl ?_
      show sliceEdge (fun i => ((![z, 0] i : ℝ) : ℂ)) = 0
      show (((![z, 0] 1 : ℝ) : ℂ)) • selectedLayerExchangeMatrix false true = 0
      norm_num
    rw [hpt]
    exact C.center_mem
  obtain ⟨c, hcdef⟩ : ∃ c : seedIndex k × Bool → ℂ,
      c = fun i => ((kvec (seedLeafFin k i) : ℝ) : ℂ) := ⟨_, rfl⟩
  have hczero : ∑ i, c i = 0 := by
    rw [hcdef]
    rw [← Complex.ofReal_sum, Equiv.sum_comp (seedLeafFin k) kvec, hksum]
    simp
  have hcne : c ≠ 0 := by
    intro h0
    refine hkne ?_
    funext j
    have hj := congrFun h0 ((seedLeafFin k).symm j)
    rw [hcdef] at hj
    simp only [Equiv.apply_symm_apply, Pi.zero_apply] at hj
    exact Complex.ofReal_injective hj
  obtain ⟨q, hqW, hedge, hshiftEq, hfail⟩ :=
    exists_mem_real_sliceLeaf_quadraticRate_ne_zero (three_le_card_seedIndex k) hE hgap
      hMherm hM hbase C c ((κ : ℝ) : ℂ) hczero hcne hWopen hWne
  have hp : realSliceParameter q ∈ C.U := by rw [hWdef] at hqW; exact hqW
  obtain ⟨Hphys, hHphysdef⟩ : ∃ Hphys, Hphys = physicalLeafHamiltonian
      (U * Matrix.diagonal (fun i => ((E i : ℝ) : ℂ)) * Uᴴ) V
      (sliceShift (fun i => ((q i : ℝ) : ℂ))) (sliceEdge (fun i => ((q i : ℝ) : ℂ))) := ⟨_, rfl⟩
  have hchain : Matrix.reindex (snocConfig (k + 2)) (snocConfig (k + 2)) Hphys
      ∈ pauliChainSpan (k + 3) := by
    rw [hHphysdef, hshiftEq]
    exact physicalLeaf_mem_pauliChainSpan hHspan hVspan (q 0) hedge
  obtain ⟨H₀, hH₀def⟩ : ∃ H₀, H₀ = Matrix.reindex (qubitConfigFin (k + 3)) (qubitConfigFin (k + 3))
      (Matrix.reindex (snocConfig (k + 2)) (snocConfig (k + 2)) Hphys) := ⟨_, rfl⟩
  have hspan : H₀ ∈ Submodule.span ℝ (Set.range (chainPauliFin (k + 3))) := by
    rw [hH₀def]
    exact reindexFin_mem_span_range_chainPauliFin hchain
  obtain ⟨energy₀, henergydef⟩ : ∃ energy₀ : Fin (2 ^ (k + 3)) → ℂ,
      energy₀ = fun j => C.branch ((seedLeafFin k).symm j) (realSliceParameter q) := ⟨_, rfl⟩
  have hinj₀ : Function.Injective energy₀ := by
    rw [henergydef]
    exact (C.simple _ hp).comp (seedLeafFin k).symm.injective
  have hcharpoly : H₀.charpoly = (localExtensionMatrix (fun a => ((E a : ℝ) : ℂ))
      (realSliceParameter q).1 M (realSliceParameter q).2).charpoly := by
    rw [hH₀def, Matrix.charpoly_reindex, Matrix.charpoly_reindex, hHphysdef, hMdef]
    exact charpoly_physicalLeafHamiltonian U hUleft hUright _ V _ _
  have hroot₀ : ∀ j, matrixCharpolyRelation (H₀, energy₀ j) = 0 := by
    intro j
    show (Matrix.scalar _ (energy₀ j) - H₀).det = 0
    rw [← Matrix.eval_charpoly, hcharpoly, Matrix.eval_charpoly]
    rw [henergydef]
    exact C.root _ hp _
  refine ⟨H₀, energy₀, hspan, hinj₀, hroot₀, ?_⟩
  intro σ
  obtain ⟨σ', hσ'⟩ : ∃ σ' : Equiv.Perm (seedIndex k × Bool),
      σ' = (seedLeafFin k).trans (σ.trans (seedLeafFin k).symm) := ⟨_, rfl⟩
  have hσsymm : ∀ i, (seedLeafFin k) (σ'.symm i) = σ.symm (seedLeafFin k i) := by
    intro i
    rw [hσ']
    simp
  have hkey := hfail (fun i => C.branch i (realSliceParameter q))
    (C.simple _ hp) (C.root _ hp) σ'
  intro hzeroEq
  refine hkey ?_
  have hsum1 : (∑ i, c (σ'.symm i) * C.branch i (realSliceParameter q))
      = ∑ j, ((kvec (σ.symm j) : ℝ) : ℂ) * energy₀ j := by
    rw [← Equiv.sum_comp (seedLeafFin k)
      (fun j => ((kvec (σ.symm j) : ℝ) : ℂ) * energy₀ j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hcdef, henergydef]
    simp only [hσsymm i, Equiv.symm_apply_apply]
  have hsum2 : (∑ i, (C.branch i (realSliceParameter q)) ^ 2) = ∑ j, energy₀ j ^ 2 := by
    rw [← Equiv.sum_comp (seedLeafFin k) (fun j => energy₀ j ^ 2)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [henergydef]
    simp only [Equiv.symm_apply_apply]
  rw [hsum1, hsum2]
  exact hzeroEq

end GaloisForLFunctions.HTGeometry

end
