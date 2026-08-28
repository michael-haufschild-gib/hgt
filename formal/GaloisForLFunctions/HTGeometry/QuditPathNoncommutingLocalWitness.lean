import GaloisForLFunctions.HTGeometry.QuditPathChainRecurrenceExponent
import GaloisForLFunctions.HTGeometry.DiagonalCommutatorWidth

open scoped Matrix Kronecker

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Digit observable on a `q`-level site. -/
def quditDigitObservable (q : ℕ) : Matrix (Fin q) (Fin q) ℂ :=
  Matrix.diagonal fun i => ((i.1 : ℝ) : ℂ)

/-- Symmetric exchange between levels zero and one. -/
def quditZeroOneExchange (q : ℕ) (hq : 2 ≤ q) : Matrix (Fin q) (Fin q) ℂ :=
  symmetricProbe (⟨0, by omega⟩ : Fin q) (⟨1, by omega⟩ : Fin q)

theorem quditDigitObservable_isHermitian (q : ℕ) :
    (quditDigitObservable q).IsHermitian := by
  rw [quditDigitObservable, Matrix.isHermitian_diagonal_iff]
  intro i
  exact Complex.conj_ofReal _

theorem quditZeroOneExchange_isHermitian (q : ℕ) (hq : 2 ≤ q) :
    (quditZeroOneExchange q hq).IsHermitian := by
  exact symmetricProbe_isHermitian _ _

theorem quditZeroOneExchange_ne_zero (q : ℕ) (hq : 2 ≤ q) :
    quditZeroOneExchange q hq ≠ 0 := by
  intro h
  have hentry := congrFun (congrFun h (⟨0, by omega⟩ : Fin q))
    (⟨1, by omega⟩ : Fin q)
  simp [quditZeroOneExchange, symmetricProbe, unitProbe] at hentry

theorem quditDigit_exchange_commutator_ne_zero (q : ℕ) (hq : 2 ≤ q) :
    quditDigitObservable q * quditZeroOneExchange q hq ≠
      quditZeroOneExchange q hq * quditDigitObservable q := by
  intro h
  have hentry := congrFun (congrFun h (⟨0, by omega⟩ : Fin q))
    (⟨1, by omega⟩ : Fin q)
  have hc := commutator_diagonal_apply
    (fun i : Fin q => (i.1 : ℝ)) (quditZeroOneExchange q hq)
      (⟨0, by omega⟩ : Fin q) (⟨1, by omega⟩ : Fin q)
  have hentry' :
      ((Matrix.diagonal fun i : Fin q => (((i.1 : ℕ) : ℝ) : ℂ)) *
          quditZeroOneExchange q hq) (⟨0, by omega⟩) (⟨1, by omega⟩) =
        (quditZeroOneExchange q hq *
          (Matrix.diagonal fun i : Fin q => (((i.1 : ℕ) : ℝ) : ℂ)))
          (⟨0, by omega⟩) (⟨1, by omega⟩) := by
    simpa [quditDigitObservable] using hentry
  rw [Matrix.sub_apply, hentry', sub_self] at hc
  simp [quditZeroOneExchange, symmetricProbe, unitProbe] at hc

theorem kronecker_left_commutator_ne_zero
    {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (A B : Matrix I I ℂ) (C : Matrix J J ℂ)
    (hAB : A * B ≠ B * A) (hC : C ≠ 0) :
    (A ⊗ₖ (1 : Matrix J J ℂ)) * (B ⊗ₖ C) ≠
      (B ⊗ₖ C) * (A ⊗ₖ (1 : Matrix J J ℂ)) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hAB
  obtain ⟨j, hij⟩ := Function.ne_iff.mp hi
  obtain ⟨r, hr⟩ := Function.ne_iff.mp hC
  obtain ⟨s, hrs⟩ := Function.ne_iff.mp hr
  intro h
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul] at h
  simp only [Matrix.one_mul, Matrix.mul_one] at h
  have hentry := congrFun (congrFun h (i, r)) (j, s)
  simp only [Matrix.kronecker_apply] at hentry
  exact hij (mul_right_cancel₀ hrs hentry)

theorem kronecker_right_commutator_ne_zero
    {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J]
    (P : Matrix I I ℂ) (A B : Matrix J J ℂ)
    (hP : P ≠ 0) (hAB : A * B ≠ B * A) :
    ((1 : Matrix I I ℂ) ⊗ₖ A) * (P ⊗ₖ B) ≠
      (P ⊗ₖ B) * ((1 : Matrix I I ℂ) ⊗ₖ A) := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hP
  obtain ⟨j, hij⟩ := Function.ne_iff.mp hi
  obtain ⟨r, hr⟩ := Function.ne_iff.mp hAB
  obtain ⟨s, hrs⟩ := Function.ne_iff.mp hr
  intro h
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul] at h
  simp only [Matrix.one_mul, Matrix.mul_one] at h
  have hentry := congrFun (congrFun h (i, r)) (j, s)
  simp only [Matrix.kronecker_apply] at hentry
  exact hrs (mul_left_cancel₀ hij hentry)

/-- A single parent--child edge summand in the rooted construction.  At the two-site seed every
matrix is an edge term; at a leaf this records the literal parent operator tensored with the new
factor operator. -/
def RootedTensorTree.IsElementaryEdgeTerm :
    {Physical Observer : Type} →
      (T : RootedTensorTree Physical Observer) →
      Matrix Physical Physical ℂ → Prop
  | _, _, @RootedTensorTree.atom Physical Observer _ _ _ _, _ => False
  | _, _, @RootedTensorTree.edge left right Observer _ _ _ _ _ _ _side, _ => True
  | _, _, @RootedTensorTree.leaf Physical Observer old _ _ _ _ newFactor _ _ parent, B =>
      ∃ parentOperator edge,
        old.IsOneSite parent parentOperator ∧
        B = layerMatrixCoupling parentOperator edge

/-- Exact physical pair used in the noncommuting local chart: one onsite summand, one elementary
edge summand, both Hermitian and both lying in the full local Hamiltonian subspace. -/
def RootedTensorTree.HasNoncommutingOnsiteEdgePair
    {Physical Observer : Type}
    [Fintype Physical] [DecidableEq Physical]
    (T : RootedTensorTree Physical Observer) : Prop :=
  ∃ site A B,
    T.IsOneSite site A ∧
    T.IsElementaryEdgeTerm B ∧
    A.IsHermitian ∧ B.IsHermitian ∧
    A ∈ T.hermitianLocalHamiltonianSubmodule ∧
    B ∈ T.hermitianLocalHamiltonianSubmodule ∧
    A * B ≠ B * A

theorem RootedTensorTree.isLocalHamiltonian_zero
    {Physical Observer : Type}
    (T : RootedTensorTree Physical Observer) :
    T.IsLocalHamiltonian (0 : Matrix Physical Physical ℂ) := by
  induction T with
  | atom => trivial
  | edge => trivial
  | @leaf Physical Observer old _ _ _ _ newFactor _ _ parent ih =>
      refine ⟨0, 0, 0, 0, ih, old.isOneSite_zero parent, ?_⟩
      ext x y
      simp [physicalLeafHamiltonian]

theorem twoSiteQuditTree_hasNoncommutingOnsiteEdgePair
    (q : ℕ) (hq : 2 ≤ q) :
    let T := RootedTensorTree.edge (Fin q) (Fin q) Bool (Equiv.refl Bool)
    T.HasNoncommutingOnsiteEdgePair := by
  let T := RootedTensorTree.edge (Fin q) (Fin q) Bool (Equiv.refl Bool)
  let Z := quditDigitObservable q
  let X := quditZeroOneExchange q hq
  let A := layerMatrixCoupling Z (1 : Matrix (Fin q) (Fin q) ℂ)
  let B := layerMatrixCoupling X X
  have hZ : Z.IsHermitian := quditDigitObservable_isHermitian q
  have hX : X.IsHermitian := quditZeroOneExchange_isHermitian q hq
  have hA : A.IsHermitian := layerMatrixCoupling_isHermitian hZ Matrix.isHermitian_one
  have hB : B.IsHermitian := layerMatrixCoupling_isHermitian hX hX
  refine ⟨false, A, B, ?_, ?_, hA, hB, ?_, ?_, ?_⟩
  · exact ⟨Z, rfl⟩
  · trivial
  · exact T.mem_hermitianLocalHamiltonianSubmodule trivial hA
  · exact T.mem_hermitianLocalHamiltonianSubmodule trivial hB
  · simpa only [A, B, layerMatrixCoupling_eq_kronecker] using
      kronecker_left_commutator_ne_zero Z X X
        (quditDigit_exchange_commutator_ne_zero q hq)
        (quditZeroOneExchange_ne_zero q hq)

theorem leafQuditTree_hasNoncommutingOnsiteEdgePair
    {Physical Observer : Type}
    [Fintype Physical] [DecidableEq Physical]
    [Fintype Observer] [DecidableEq Observer]
    (old : RootedTensorTree Physical Observer) (parent : Observer)
    (q : ℕ) (hq : 2 ≤ q)
    (P : Matrix Physical Physical ℂ)
    (hPlocal : old.IsOneSite parent P)
    (hPHermitian : P.IsHermitian) (hPne : P ≠ 0) :
    (RootedTensorTree.leaf old (Fin q) parent).HasNoncommutingOnsiteEdgePair := by
  let T := RootedTensorTree.leaf old (Fin q) parent
  let Z := quditDigitObservable q
  let X := quditZeroOneExchange q hq
  let A := layerMatrixCoupling (1 : Matrix Physical Physical ℂ) Z
  let B := layerMatrixCoupling P X
  have hZ : Z.IsHermitian := quditDigitObservable_isHermitian q
  have hX : X.IsHermitian := quditZeroOneExchange_isHermitian q hq
  have hA : A.IsHermitian := layerMatrixCoupling_isHermitian Matrix.isHermitian_one hZ
  have hB : B.IsHermitian := layerMatrixCoupling_isHermitian hPHermitian hX
  have hAlocal : T.IsLocalHamiltonian A := by
    refine ⟨0, 0, (fun i : Fin q => ((i.1 : ℝ) : ℂ)), 0,
      old.isLocalHamiltonian_zero, old.isOneSite_zero parent, ?_⟩
    ext x y
    simp [A, Z, quditDigitObservable, physicalLeafHamiltonian]
  have hBlocal : T.IsLocalHamiltonian B := by
    refine ⟨0, P, 0, X, old.isLocalHamiltonian_zero, hPlocal, ?_⟩
    ext x y
    simp [B, physicalLeafHamiltonian]
  refine ⟨Sum.inr (), A, B, ?_, ?_, hA, hB, ?_, ?_, ?_⟩
  · exact ⟨Z, rfl⟩
  · exact ⟨P, X, hPlocal, rfl⟩
  · exact T.mem_hermitianLocalHamiltonianSubmodule hAlocal hA
  · exact T.mem_hermitianLocalHamiltonianSubmodule hBlocal hB
  · simpa only [A, B, layerMatrixCoupling_eq_kronecker] using
      kronecker_right_commutator_ne_zero P Z X hPne
        (quditDigit_exchange_commutator_ne_zero q hq)

theorem PhysicallyRealizedTensorTreeSystem.exists_nonzeroHermitianOneSiteProbe
    (Z : PhysicallyRealizedTensorTreeSystem.{0})
    (site : Z.spectral.Observer) :
    letI : Fintype Z.spectral.State := Z.spectral.stateFintype
    letI : DecidableEq Z.spectral.State := Z.spectral.stateDecidableEq
    letI : Fintype Z.spectral.Observer := Z.spectral.observerFintype
    letI : DecidableEq Z.spectral.Observer := Z.spectral.observerDecidableEq
    letI : Fintype Z.PhysicalState := Z.physicalFintype
    letI : DecidableEq Z.PhysicalState := Z.physicalDecidableEq
    ∃ P : Matrix Z.PhysicalState Z.PhysicalState ℂ,
      Z.locality.tree.IsOneSite site P ∧ P.IsHermitian ∧ P ≠ 0 := by
  classical
  letI : Fintype Z.spectral.State := Z.spectral.stateFintype
  letI : DecidableEq Z.spectral.State := Z.spectral.stateDecidableEq
  letI : Fintype Z.spectral.Observer := Z.spectral.observerFintype
  letI : DecidableEq Z.spectral.Observer := Z.spectral.observerDecidableEq
  letI : Fintype Z.PhysicalState := Z.physicalFintype
  letI : DecidableEq Z.PhysicalState := Z.physicalDecidableEq
  letI : Fintype (Z.spectral.Probe site) := Z.spectral.probeFintype site
  letI : DecidableEq (Z.spectral.Probe site) := Classical.decEq _
  obtain ⟨p, hAHermitian, _hgraph, _hconnected, hAnonbipartite⟩ :=
    exists_hermitianTransition_good_of_family_good
      (Z.spectral.transition site)
      (Z.spectral.observerFamily_good site).1
      (Z.spectral.observerFamily_good site).2.1
      (Z.spectral.observerFamily_good site).2.2
  let A := realMatrixFamilyCombination (Z.spectral.transition site) p
  let P := realMatrixFamilyCombination (Z.realization.physicalProbe site) p
  have hAlocal : Z.locality.tree.IsOneSite site P :=
    Z.locality.tree.isOneSite_realMatrixFamilyCombination site
      (Z.realization.physicalProbe site) p (Z.locality.probe_local site)
  have hAne : A ≠ 0 := by
    intro hA
    apply hAnonbipartite
    change (transitionSupportGraph A).IsBipartite
    rw [hA]
    refine ⟨⟨fun _ => 0, ?_⟩⟩
    simp [transitionSupportGraph]
  have hback : P = Z.realization.basis * A * Z.realization.basisᴴ := by
    exact physicalCombination_eq_basis_mul_spectralCombination
      Z.realization.basis (Z.realization.physicalProbe site)
      (Z.spectral.transition site) p
      Z.realization.basis_mul_star_basis
      (Z.realization.transition_eq_coordinate site)
  have hPHermitian : P.IsHermitian := by
    rw [hback]
    change (Z.realization.basis * A * Z.realization.basisᴴ)ᴴ =
      Z.realization.basis * A * Z.realization.basisᴴ
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    simpa only [Matrix.mul_assoc] using congrArg
      (fun X => Z.realization.basis * X * Z.realization.basisᴴ) hAHermitian
  have hPne : P ≠ 0 := by
    intro hP
    have hcoordinate : A = Z.realization.basisᴴ * P * Z.realization.basis := by
      simpa [A, P] using
        (realMatrixFamilyCombination_coordinate
          Z.realization.basis (Z.realization.physicalProbe site)
          (Z.spectral.transition site) p
          (Z.realization.transition_eq_coordinate site))
    rw [hP] at hcoordinate
    simp at hcoordinate
    exact hAne hcoordinate
  exact ⟨P, hAlocal, hPHermitian, hPne⟩

/-- The arbitrary-qudit path producer with a literal noncommuting onsite/edge pair retained in the
same escaping local Hamiltonian space. -/
theorem exists_quditPathChain_spectrumEscapes_with_noncommutingPair
    (n q : ℕ) (hn : 2 ≤ n) (hq : 2 ≤ q) :
    ∃ (Physical Observer : Type) (instP : Fintype Physical)
      (instPd : DecidableEq Physical)
      (T : RootedTensorTree Physical Observer) (eObs : Observer ≃ Fin n),
      letI := instP
      letI := instPd
      T.graph = SimpleGraph.comap eObs (SimpleGraph.pathGraph n) ∧
      @Fintype.card Physical instP = q ^ n ∧
      T.HasNoncommutingOnsiteEdgePair ∧
      @SpectrumEscapesAffineRelations Physical instP instPd
        (↑T.hermitianLocalHamiltonianSubmodule) := by
  classical
  rcases eq_or_lt_of_le hn with hn2 | hn3
  · refine ⟨Fin q × Fin q, Bool, inferInstance, inferInstance,
      RootedTensorTree.edge (Fin q) (Fin q) Bool (Equiv.refl Bool),
      (finTwoEquiv.symm.trans (finCongr hn2)), ?_, ?_,
      twoSiteQuditTree_hasNoncommutingOnsiteEdgePair q hq, ?_⟩
    · ext a b
      rw [SimpleGraph.comap_adj, SimpleGraph.pathGraph_adj]
      cases a <;> cases b <;>
        simp [RootedTensorTree.graph, finTwoEquiv, finCongr]
    · rw [← hn2]
      simp [pow_two]
    · refine diagonalSet_spectrumEscapesAffineRelations.mono ?_
      rintro M ⟨E, rfl⟩
      refine RootedTensorTree.mem_hermitianLocalHamiltonianSubmodule _ ?_ ?_
      · exact trivial
      · exact Matrix.isHermitian_diagonal_iff.mpr fun i => Complex.conj_ofReal _
  · obtain ⟨Z, e, hgraph, hstate, -, -, -⟩ :=
      exists_uniformQuditPathLocalHamiltonianMaximalSet_dense_residual_fullMeasure
        (n - 1) q (by omega) hq
    letI : Fintype Z.spectral.State := Z.spectral.stateFintype
    letI : DecidableEq Z.spectral.State := Z.spectral.stateDecidableEq
    letI : Nonempty Z.spectral.State := Z.spectral.stateNonempty
    letI : Fintype Z.spectral.Observer := Z.spectral.observerFintype
    letI : DecidableEq Z.spectral.Observer := Z.spectral.observerDecidableEq
    letI : Fintype Z.PhysicalState := Z.physicalFintype
    letI : DecidableEq Z.PhysicalState := Z.physicalDecidableEq
    let root : Z.spectral.Observer := e.symm ⟨n - 2, by omega⟩
    have hroot : ((e root : Fin (n - 1)) : ℕ) + 1 = n - 1 := by
      have hval : (e root : Fin (n - 1)) = (⟨n - 2, by omega⟩ : Fin (n - 1)) := by
        simp [root]
      rw [hval]
      show n - 2 + 1 = n - 1
      omega
    letI : Fintype (Z.spectral.Probe root) := Z.spectral.probeFintype root
    obtain ⟨parentProbe, hparentLocal, hparentHermitian, hparentNe⟩ :=
      Z.exists_nonzeroHermitianOneSiteProbe root
    refine ⟨Z.PhysicalState × Fin q, LeafExtendedObserver Z.spectral.Observer,
      inferInstance, inferInstance,
      RootedTensorTree.leaf Z.locality.tree (Fin q) root,
      (leafPathEquiv e).trans (finCongr (by omega)), ?_, ?_, ?_, ?_⟩
    · show leafGraphExtension Z.locality.tree.graph root =
          SimpleGraph.comap _ (SimpleGraph.pathGraph n)
      have hcomap :
          SimpleGraph.comap
              ((leafPathEquiv e).trans
                (finCongr (show n - 1 + 1 = n by omega)))
              (SimpleGraph.pathGraph n) =
            SimpleGraph.comap (leafPathEquiv e)
              (SimpleGraph.comap
                (finCongr (show n - 1 + 1 = n by omega))
                (SimpleGraph.pathGraph n)) := rfl
      rw [hcomap]
      have hpath :
          SimpleGraph.comap
              (finCongr (show n - 1 + 1 = n by omega))
              (SimpleGraph.pathGraph n) =
            SimpleGraph.pathGraph (n - 1 + 1) := by
        ext i j
        rw [SimpleGraph.comap_adj, SimpleGraph.pathGraph_adj,
          SimpleGraph.pathGraph_adj]
        simp [finCongr]
      rw [hpath]
      have hZgraph :
          Z.locality.tree.graph =
            SimpleGraph.comap e (SimpleGraph.pathGraph (n - 1)) := hgraph
      rw [hZgraph]
      exact leafGraphExtension_comap_pathGraph e root hroot
    · have hcardPhysical :
          Fintype.card Z.PhysicalState = Fintype.card Z.spectral.State :=
        card_eq_of_coordinateUnitary Z.realization.star_basis_mul_basis
          Z.realization.basis_mul_star_basis
      rw [Fintype.card_prod, hcardPhysical, Fintype.card_fin]
      have : Fintype.card Z.spectral.State = q ^ (n - 1) := hstate
      rw [this, ← pow_succ]
      congr 1
      omega
    · exact leafQuditTree_hasNoncommutingOnsiteEdgePair
        Z.locality.tree root q hq parentProbe hparentLocal
        hparentHermitian hparentNe
    · exact leafHermitianLocalHamiltonian_spectrumEscapesAffineRelations
        Z.locality.tree root (Fin q) (by simpa using hq)
        Z.spectral.energy Z.spectral.energy_maximallyProjective
        Z.realization.basis Z.realization.star_basis_mul_basis
        Z.realization.basis_mul_star_basis
        Z.hamiltonian Z.locality.hamiltonian_local
        Z.realization.hamiltonian_coordinate
        (Z.realization.physicalProbe root) (Z.locality.probe_local root)
        (Z.spectral.transition root) (Z.realization.transition_eq_coordinate root)
        (Z.spectral.observerFamily_good root).1
        (Z.spectral.observerFamily_good root).2.1
        (Z.spectral.observerFamily_good root).2.2

/-- Canonical coordinate family retaining its fixed noncommuting onsite/edge generators. -/
theorem exists_quditPathChain_coordinateFamily_with_noncommutingPair
    (n q : ℕ) (hn : 2 ≤ n) (hq : 2 ≤ q) :
    ∃ D : ℕ, q ^ n = D ∧ 4 ≤ D ∧
    ∃ (Physical Observer : Type) (instP : Fintype Physical)
      (instPd : DecidableEq Physical)
      (T : RootedTensorTree Physical Observer) (eObs : Observer ≃ Fin n),
      letI := instP
      letI := instPd
      T.graph = SimpleGraph.comap eObs (SimpleGraph.pathGraph n) ∧
      T.HasNoncommutingOnsiteEdgePair ∧
      ∃ (eSt : Physical ≃ Fin D)
        (_ : NeZero (Module.finrank ℝ T.hermitianLocalHamiltonianSubmodule))
        (P : Fin (Module.finrank ℝ T.hermitianLocalHamiltonianSubmodule) →
          Matrix (Fin D) (Fin D) ℂ)
        (_hP : ∀ a, (P a).IsHermitian),
        (∀ a, P a = Matrix.reindex eSt eSt
          (realMatrixSubmoduleGenerator T.hermitianLocalHamiltonianSubmodule a)) ∧
        SpectrumEscapesAffineRelations (Set.range (spectralEnsembleMatrix P)) := by
  classical
  obtain ⟨Physical, Observer, instP, instPd, T, eObs, hgraph, hcard,
      hpair, hescape⟩ :=
    exists_quditPathChain_spectrumEscapes_with_noncommutingPair n q hn hq
  letI := instP
  letI := instPd
  have hq4 : 4 ≤ q ^ n := by
    calc
      (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
      _ ≤ q ^ n := Nat.pow_le_pow_right (by omega) hn
  refine ⟨q ^ n, rfl, hq4, Physical, Observer, instP, instPd, T, eObs,
    hgraph, hpair, ?_⟩
  set L := T.hermitianLocalHamiltonianSubmodule with hL
  have hLself : L ≤ selfAdjoint.submodule ℝ (Matrix Physical Physical ℂ) :=
    T.hermitianLocalHamiltonianSubmodule_le_selfAdjoint
  set eSt : Physical ≃ Fin (q ^ n) := Fintype.equivFinOfCardEq hcard with heSt
  set gen := realMatrixSubmoduleGenerator L with hgen
  set P : Fin (Module.finrank ℝ L) → Matrix (Fin (q ^ n)) (Fin (q ^ n)) ℂ :=
    fun a => Matrix.reindex eSt eSt (gen a) with hP
  have hPHermitian : ∀ a, (P a).IsHermitian := by
    intro a
    rw [hP]
    exact (Matrix.isHermitian_reindex_iff eSt).mpr
      (realMatrixSubmoduleGenerator_isHermitian L hLself a)
  have hNeZero : NeZero (Module.finrank ℝ L) := by
    refine ⟨?_⟩
    obtain ⟨H, hHmem, hHne⟩ :=
      exists_ne_zero_of_spectrumEscapes (I := Physical) (by omega) (hL ▸ hescape)
    have hpos : 0 < Module.finrank ℝ L :=
      Module.finrank_pos_iff_exists_ne_zero.mpr
        ⟨⟨H, hHmem⟩, fun h0 => hHne (congrArg Subtype.val h0)⟩
    omega
  have hfamily : SpectrumEscapesAffineRelations
      (Set.range (spectralEnsembleMatrix P)) := by
    refine (hescape.ofSubmodule (L := L)).reindex eSt ?_
    rintro M ⟨p, rfl⟩
    refine ⟨p, ?_⟩
    ext i j
    simp [spectralEnsembleMatrix, realAffineMatrix, Matrix.reindex, hP, hgen,
      Matrix.sum_apply, Matrix.smul_apply]
  exact ⟨eSt, hNeZero, P, hPHermitian, fun a => rfl, hfamily⟩

theorem spectralEnsembleMatrix_cons_two_compensated
    {m D : ℕ}
    (A B : Matrix (Fin D) (Fin D) ℂ)
    (P : Fin m → Matrix (Fin D) (Fin D) ℂ)
    (theta pA pB : Fin m → ℝ)
    (hA : spectralEnsembleMatrix P pA = A)
    (hB : spectralEnsembleMatrix P pB = B) :
    spectralEnsembleMatrix (Fin.cons A (Fin.cons B P))
        (Fin.cons 1 (Fin.cons 1 fun i => theta i - pA i - pB i)) =
      spectralEnsembleMatrix P theta := by
  ext i j
  simp only [spectralEnsembleMatrix, Fin.sum_univ_succ, Fin.cons_zero,
    Fin.cons_succ, Matrix.sum_apply, Matrix.smul_apply]
  have hAij := congrFun (congrFun hA i) j
  have hBij := congrFun (congrFun hB i) j
  simp only [spectralEnsembleMatrix, Matrix.sum_apply, Matrix.smul_apply] at hAij hBij
  push_cast
  simp only [one_smul, sub_smul, Finset.sum_sub_distrib]
  rw [hAij, hBij]
  abel

end

end GaloisForLFunctions.HTGeometry
