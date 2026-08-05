import GaloisForLFunctions.HTGeometry.ArbitraryGraphLocalHamiltonianGenericityLaw

/-!
# Traceless local-Hamiltonian genericity

Projective spectral arithmetic is invariant under a common energy shift.
This module centers any maximally projective tensor-tree-local Hermitian
witness, proves that the scalar identity is architecture-local, and lifts
generic maximality to the exact traceless local-Hamiltonian subspace.
-/

open Set SimpleGraph MeasureTheory Topology Filter
open scoped Matrix Kronecker BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

/-- Subtracting a common real energy preserves every balanced spectral
character, hence maximal projective independence. -/
theorem MaximallyProjectiveEnergy.sub_const
    {I : Type*} [Fintype I]
    {energy : I → ℝ} (hmax : MaximallyProjectiveEnergy energy)
    (c : ℝ) :
    MaximallyProjectiveEnergy (fun i => energy i - c) := by
  intro k hbalanced hzero
  have hbalancedReal : ∑ i, (k i : ℝ) = 0 := by
    exact_mod_cast hbalanced
  apply hmax k hbalanced
  calc
    ∑ i, (k i : ℝ) * energy i =
        ∑ i, ((k i : ℝ) * (energy i - c) + (k i : ℝ) * c) := by
          apply Finset.sum_congr rfl
          intro i _hi
          ring
    _ = (∑ i, (k i : ℝ) * (energy i - c)) +
          ∑ i, (k i : ℝ) * c := Finset.sum_add_distrib
    _ = (∑ i, (k i : ℝ) * (energy i - c)) +
          c * ∑ i, (k i : ℝ) := by
            rw [Finset.mul_sum]
            congr 1
            apply Finset.sum_congr rfl
            intro i _hi
            ring
    _ = 0 := by rw [hzero, hbalancedReal]; ring

/-- Subtracting a real scalar matrix preserves maximal projective spectrum.
The proof constructs the finite eigenvalue relabelling from the real
spectrum rather than assuming an ordering convention. -/
theorem Matrix.IsHermitian.maximallyProjective_sub_real_smul_one
    {I : Type*} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℂ} (hA : A.IsHermitian)
    (hmax : MaximallyProjectiveEnergy hA.eigenvalues)
    (c : ℝ) :
    let B := A - (c : ℂ) • (1 : Matrix I I ℂ)
    let hB : B.IsHermitian := hA.sub
      (Matrix.isHermitian_one.smul (Complex.conj_ofReal c))
    MaximallyProjectiveEnergy hB.eigenvalues := by
  dsimp
  let B : Matrix I I ℂ := A - (c : ℂ) • (1 : Matrix I I ℂ)
  have hB : B.IsHermitian := hA.sub
    (Matrix.isHermitian_one.smul (Complex.conj_ofReal c))
  have hspec : ∀ i : I,
      hA.eigenvalues i - c ∈ spectrum ℝ B := by
    intro i
    have hi := hA.eigenvalues_mem_spectrum_real i
    have hshift :=
      (spectrum.add_mem_add_iff
        (a := A) (r := hA.eigenvalues i) (s := -c)).mpr hi
    simpa [B, sub_eq_add_neg, Algebra.algebraMap_eq_smul_one,
      add_comm] using hshift
  have hexists : ∀ i : I, ∃ j : I,
      hB.eigenvalues j = hA.eigenvalues i - c := by
    intro i
    have hi := hspec i
    rw [hB.spectrum_real_eq_range_eigenvalues] at hi
    simpa [eq_comm] using hi
  let g : I → I := fun i => Classical.choose (hexists i)
  have hg : ∀ i, hB.eigenvalues (g i) = hA.eigenvalues i - c :=
    fun i => Classical.choose_spec (hexists i)
  have hginj : Function.Injective g := by
    intro i j hij
    apply hmax.injective
    have heq := congrArg hB.eigenvalues hij
    rw [hg i, hg j] at heq
    linarith
  let e : I ≃ I := Equiv.ofBijective g hginj.bijective_of_finite
  have heigen : hB.eigenvalues =
      fun j => hA.eigenvalues (e.symm j) - c := by
    funext j
    calc
      hB.eigenvalues j = hB.eigenvalues (e (e.symm j)) := by
        rw [e.apply_symm_apply]
      _ = hA.eigenvalues (e.symm j) - c := by
        change hB.eigenvalues (g (e.symm j)) = _
        exact hg (e.symm j)
  rw [heigen]
  exact maximallyProjectiveEnergy_equiv e.symm (hmax.sub_const c)

/-- Zero is localized at every site of a rooted tensor-tree architecture. -/
theorem RootedTensorTree.isOneSite_zero
    {Physical Observer : Type u}
    (T : RootedTensorTree Physical Observer) (site : Observer) :
    T.IsOneSite site 0 := by
  induction T with
  | atom Physical Observer => trivial
  | edge left right Observer side =>
      by_cases hs : side site = false
      · simp only [RootedTensorTree.IsOneSite, if_pos hs]
        refine ⟨0, ?_⟩
        ext x y
        simp [layerMatrixCoupling]
      · simp only [RootedTensorTree.IsOneSite, if_neg hs]
        refine ⟨0, ?_⟩
        ext x y
        simp [layerMatrixCoupling]
  | @leaf Physical Observer old _ _ _ _ newFactor _ _ parent ih =>
      cases site with
      | inl site =>
          simp only [RootedTensorTree.IsOneSite]
          refine ⟨0, ih site, ?_⟩
          ext x y
          simp [layerMatrixCoupling]
      | inr site =>
          simp only [RootedTensorTree.IsOneSite]
          refine ⟨0, ?_⟩
          ext x y
          simp [layerMatrixCoupling]

/-- The scalar identity is local in every rooted tensor-tree architecture. -/
theorem RootedTensorTree.isLocalHamiltonian_one
    {Physical Observer : Type u}
    (T : RootedTensorTree Physical Observer) :
    letI : DecidableEq Physical := T.physicalDecidableEq
    T.IsLocalHamiltonian 1 := by
  induction T with
  | atom Physical Observer => trivial
  | edge left right Observer side => trivial
  | @leaf Physical Observer old _ _ _ _ newFactor _ _ parent ih =>
      let oldDec : DecidableEq Physical := by infer_instance
      have hone :
          @OfNat.ofNat (Matrix Physical Physical ℂ) 1
              (@One.toOfNat1 (Matrix Physical Physical ℂ)
                (@Matrix.one Physical ℂ old.physicalDecidableEq
                  Complex.instZero Complex.instOne)) =
            @OfNat.ofNat (Matrix Physical Physical ℂ) 1
              (@One.toOfNat1 (Matrix Physical Physical ℂ)
                (@Matrix.one Physical ℂ oldDec
                  Complex.instZero Complex.instOne)) := by
        ext i j
        by_cases hij : i = j <;> simp [hij]
      have ih' : old.IsLocalHamiltonian 1 := by
        rw [← hone]
        exact ih
      refine ⟨1, 0, 0, 0, ih', old.isOneSite_zero parent, ?_⟩
      ext x y
      by_cases hxy : x = y
      · subst y
        simp [physicalLeafHamiltonian]
      · simp [physicalLeafHamiltonian, hxy]

/-- Exact real subspace of architecture-local Hermitian matrices with zero
complex trace. -/
def PhysicallyRealizedTensorTreeSystem.tracelessLocalHamiltonianSubmodule
    (Z : PhysicallyRealizedTensorTreeSystem.{u}) :
    Submodule ℝ (Matrix Z.PhysicalState Z.PhysicalState ℂ) := by
  letI : Fintype Z.PhysicalState := Z.physicalFintype
  exact Z.localHamiltonianSubmodule ⊓
    LinearMap.ker
      ((Matrix.traceLinearMap Z.PhysicalState ℂ ℂ).restrictScalars ℝ)

/-- Every traceless local Hamiltonian is Hermitian. -/
theorem PhysicallyRealizedTensorTreeSystem.tracelessLocalHamiltonianSubmodule_le_selfAdjoint
    (Z : PhysicallyRealizedTensorTreeSystem.{u}) :
    Z.tracelessLocalHamiltonianSubmodule ≤
      selfAdjoint.submodule ℝ
        (Matrix Z.PhysicalState Z.PhysicalState ℂ) := by
  intro H hH
  exact Z.localHamiltonianSubmodule_le_selfAdjoint hH.1

/-- The scalar identity belongs to the complete local-Hamiltonian subspace. -/
theorem PhysicallyRealizedTensorTreeSystem.one_mem_localHamiltonianSubmodule
    (Z : PhysicallyRealizedTensorTreeSystem.{u}) :
    letI : DecidableEq Z.PhysicalState := Z.physicalDecidableEq
    (1 : Matrix Z.PhysicalState Z.PhysicalState ℂ) ∈
      Z.localHamiltonianSubmodule := by
  letI : Fintype Z.spectral.State := Z.spectral.stateFintype
  letI : DecidableEq Z.spectral.State := Z.spectral.stateDecidableEq
  letI : Fintype Z.PhysicalState := Z.physicalFintype
  letI : DecidableEq Z.PhysicalState := Z.physicalDecidableEq
  apply Z.locality.tree.mem_hermitianLocalHamiltonianSubmodule
  · have hone :
        @OfNat.ofNat (Matrix Z.PhysicalState Z.PhysicalState ℂ) 1
            (@One.toOfNat1 (Matrix Z.PhysicalState Z.PhysicalState ℂ)
              (@Matrix.one Z.PhysicalState ℂ
                Z.locality.tree.physicalDecidableEq
                Complex.instZero Complex.instOne)) =
          @OfNat.ofNat (Matrix Z.PhysicalState Z.PhysicalState ℂ) 1
            (@One.toOfNat1 (Matrix Z.PhysicalState Z.PhysicalState ℂ)
              (@Matrix.one Z.PhysicalState ℂ Z.physicalDecidableEq
                Complex.instZero Complex.instOne)) := by
        ext i j
        by_cases hij : i = j <;> simp [hij]
    have htreeLocal := Z.locality.tree.isLocalHamiltonian_one
    exact (congrArg Z.locality.tree.IsLocalHamiltonian hone).mp htreeLocal
  · have hone :
        @OfNat.ofNat (Matrix Z.PhysicalState Z.PhysicalState ℂ) 1
            (@One.toOfNat1 (Matrix Z.PhysicalState Z.PhysicalState ℂ)
              (@Matrix.one Z.PhysicalState ℂ
                Z.locality.tree.physicalDecidableEq
                Complex.instZero Complex.instOne)) =
          @OfNat.ofNat (Matrix Z.PhysicalState Z.PhysicalState ℂ) 1
            (@One.toOfNat1 (Matrix Z.PhysicalState Z.PhysicalState ℂ)
              (@Matrix.one Z.PhysicalState ℂ Z.physicalDecidableEq
                Complex.instZero Complex.instOne)) := by
        ext i j
        by_cases hij : i = j <;> simp [hij]
    have htreeHermitian : Matrix.IsHermitian
        (@OfNat.ofNat (Matrix Z.PhysicalState Z.PhysicalState ℂ) 1
          (@One.toOfNat1 (Matrix Z.PhysicalState Z.PhysicalState ℂ)
            (@Matrix.one Z.PhysicalState ℂ
              Z.locality.tree.physicalDecidableEq
              Complex.instZero Complex.instOne))) := by
      letI : DecidableEq Z.PhysicalState :=
        Z.locality.tree.physicalDecidableEq
      exact Matrix.isHermitian_one
    exact (congrArg Matrix.IsHermitian hone).mp htreeHermitian

/-- **Exact traceless tensor-tree local genericity.** In the full real
trace-zero subspace of arbitrary Hermitian onsite and edge terms, maximal
projective spectrum is dense, residual, and full Lebesgue measure. -/
theorem PhysicallyRealizedTensorTreeSystem.tracelessLocalHamiltonianMaximalSet_dense_residual_fullMeasure
    (Z : PhysicallyRealizedTensorTreeSystem.{u}) :
    letI : Fintype Z.PhysicalState := Z.physicalFintype
    letI : DecidableEq Z.PhysicalState := Z.physicalDecidableEq
    let L := Z.tracelessLocalHamiltonianSubmodule
    let hL := Z.tracelessLocalHamiltonianSubmodule_le_selfAdjoint
    Dense (realHermitianSubmoduleMaximalSet L hL) ∧
      realHermitianSubmoduleMaximalSet L hL ∈
        residual (Fin (Module.finrank ℝ L) → ℝ) ∧
      volume (realHermitianSubmoduleMaximalSet L hL)ᶜ = 0 := by
  letI : Fintype Z.spectral.State := Z.spectral.stateFintype
  letI : DecidableEq Z.spectral.State := Z.spectral.stateDecidableEq
  letI : Nonempty Z.spectral.State := Z.spectral.stateNonempty
  letI : Fintype Z.PhysicalState := Z.physicalFintype
  letI : DecidableEq Z.PhysicalState := Z.physicalDecidableEq
  letI : Nonempty Z.PhysicalState :=
    Fintype.card_pos_iff.mp (by
      rw [Z.realization.physicalCard_eq_stateCard]
      exact Fintype.card_pos)
  let hH := Z.realization.hamiltonian_isHermitian
  let c : ℝ :=
    (∑ i, hH.eigenvalues i) / Fintype.card Z.PhysicalState
  let centered : Matrix Z.PhysicalState Z.PhysicalState ℂ :=
    Z.hamiltonian - (c : ℂ) • 1
  have hcentered : centered.IsHermitian :=
    hH.sub (Matrix.isHermitian_one.smul (Complex.conj_ofReal c))
  have hcenteredLocal : centered ∈ Z.localHamiltonianSubmodule := by
    exact Z.localHamiltonianSubmodule.sub_mem
      Z.hamiltonian_mem_localHamiltonianSubmodule
      (Z.localHamiltonianSubmodule.smul_mem c
        Z.one_mem_localHamiltonianSubmodule)
  have hcenteredTrace : Matrix.trace centered = 0 := by
    change Matrix.trace
      (Z.realization.hamiltonian - (c : ℂ) • 1) = 0
    rw [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one,
      hH.trace_eq_sum_eigenvalues]
    simp only [smul_eq_mul]
    norm_cast
    dsimp [c]
    have hcard : (Fintype.card Z.PhysicalState : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    field_simp
    ring
  have hcenteredMem : centered ∈
      Z.tracelessLocalHamiltonianSubmodule := by
    refine ⟨hcenteredLocal, ?_⟩
    change Matrix.trace centered = 0
    exact hcenteredTrace
  have hcenteredMax :
      MaximallyProjectiveEnergy hcentered.eigenvalues := by
    exact Matrix.IsHermitian.maximallyProjective_sub_real_smul_one hH
      Z.realization.hamiltonianEigenvalues_maximallyProjective c
  exact realHermitianSubmoduleMaximalSet_dense_residual_fullMeasure
    Z.tracelessLocalHamiltonianSubmodule
    Z.tracelessLocalHamiltonianSubmodule_le_selfAdjoint
    centered hcenteredMem hcentered hcenteredMax

end

end GaloisForLFunctions.HTGeometry
