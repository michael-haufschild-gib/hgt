/-
# Maximal projectivity is generic on the path shell

The nearest-neighbour Pauli shell carries one direction whose spectrum admits no nonzero balanced
integer relation.  Transported through the identification of the path labels with the numbered
nearest-neighbour Pauli labels, that single witness makes maximal projectivity a full-measure
property of the path shell, hence of its unit sphere; every direction outside the resulting null
set carries an orthonormal eigenbasis of the path-local Hamiltonian with maximally projective
eigenvalues.

Main results:
* `MaximallyProjectiveEnergy.comp_equiv` — maximal projectivity is a relabelling invariant.
* `volume_notMaximallyProjective_eq_zero` — one witness makes the property full measure.
* `pathShellProb_pathBadSphere_eq_zero` — the degenerate path directions are null.
* `pathEigenBasis`, `isOrthoEigenBasis_pathEigenBasis`, `maximallyProjectiveEnergy_pathEigenValues`
  — **the eigenbasis, and its genericity at a nondegenerate direction**.
* `exists_mem_notMem_pathBadSphere` — selecting one inside a positive-measure sector.
-/
import GaloisForLFunctions.HTGeometry.PathChainLabelIdentification
import GaloisForLFunctions.HTGeometry.ChainShellMaximalProjectivity
import GaloisForLFunctions.HTGeometry.PathShellFixedSeed
import GaloisForLFunctions.HTGeometry.SphereHomogeneousNullSet
import GaloisForLFunctions.HTGeometry.ChainShellCollisionBound

open MeasureTheory Metric Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

/-- Maximal projectivity does not see a relabelling of the spectrum. -/
theorem MaximallyProjectiveEnergy.comp_equiv {α β : Type*} [Fintype α] [Fintype β]
    {mu : β → ℝ} (h : MaximallyProjectiveEnergy mu) (σ : α ≃ β) :
    MaximallyProjectiveEnergy (fun i => mu (σ i)) := by
  intro k hbal hsum
  have hbal' : SpectralCharacterBalanced (fun j => k (σ.symm j)) := by
    show ∑ j, k (σ.symm j) = 0
    rw [← Equiv.sum_comp σ (fun j => k (σ.symm j))]
    simp only [Equiv.symm_apply_apply]
    exact hbal
  have hsum' : (∑ j, ((k (σ.symm j) : ℤ) : ℝ) * mu j) = 0 := by
    rw [← Equiv.sum_comp σ (fun j => ((k (σ.symm j) : ℤ) : ℝ) * mu j)]
    simp only [Equiv.symm_apply_apply]
    exact hsum
  have hzero := h (fun j => k (σ.symm j)) hbal' hsum'
  funext i
  have hi := congrFun hzero (σ i)
  simpa using hi

section Generic

variable {N D : ℕ}

/-- **A single maximally projective direction makes maximal projectivity full measure.** -/
theorem volume_notMaximallyProjective_eq_zero {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) {θ₀ : Fin N → ℝ}
    (hθ₀ : MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues) :
    (volume : Measure (Fin N → ℝ))
        {θ | ¬ MaximallyProjectiveEnergy
          (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues} = 0 := by
  classical
  have hBadEq : {θ : Fin N → ℝ | ¬ MaximallyProjectiveEnergy
        (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues}
      = (polynomialMatrixProjectiveGenericSet (spectralGenericMatrix P))ᶜ := by
    ext θ
    exact not_congr (mem_genericSet_iff_maximallyProjective hP θ).symm
  rw [hBadEq]
  refine (polynomialMatrixProjectiveGenericSet_dense_residual_fullMeasure
    (spectralGenericMatrix P) θ₀
    (isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues hθ₀ hθ₀.injective ?_).2.2
  intro i
  show (Matrix.scalar _ (((isHermitian_spectralEnsembleMatrix hP θ₀).eigenvalues i : ℝ) : ℂ)
      - (spectralGenericMatrix P).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun t => ((θ₀ t : ℝ) : ℂ)))).det = 0
  rw [map_spectralGenericMatrix_eq θ₀]
  exact charpolyRelation_eigenvalues (isHermitian_spectralEnsembleMatrix hP θ₀) i

theorem volume_notMaximallyProjective_chain_eq_zero (k : ℕ) :
    (volume : Measure (Fin (Fintype.card (ChainLabel (k + 3))) → ℝ))
        {θ | ¬ MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix
          (chainPauliFin_isHermitian (k + 3)) θ).eigenvalues} = 0 := by
  obtain ⟨θ₀, hθ₀⟩ := exists_chainShell_maximallyProjective_witness k
  exact volume_notMaximallyProjective_eq_zero (chainPauliFin_isHermitian (k + 3)) hθ₀

end Generic


section PathTransport

variable (k : ℕ)

/-- The chain coefficients of a path-shell coefficient vector. -/
def pathChainCoeff (u : PathLabel (k + 1) → ℝ) :
    Fin (Fintype.card (ChainLabel (k + 3))) → ℝ :=
  fun a => u (pathCoeffEquiv (k + 1) a)

/-- The degenerate path-shell coefficient vectors. -/
def pathBadSet : Set (PathLabel (k + 1) → ℝ) :=
  {u | ¬ MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix
    (chainPauliFin_isHermitian (k + 3)) (pathChainCoeff k u)).eigenvalues}

theorem measurableSet_pathBadSet : MeasurableSet (pathBadSet k) := by
  classical
  have hmeas : Measurable (pathChainCoeff k) := by
    refine measurable_pi_lambda _ fun a => ?_
    exact measurable_pi_apply _
  have hchain : MeasurableSet {θ : Fin (Fintype.card (ChainLabel (k + 3))) → ℝ |
      ¬ MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix
        (chainPauliFin_isHermitian (k + 3)) θ).eigenvalues} := by
    have hEq : {θ : Fin (Fintype.card (ChainLabel (k + 3))) → ℝ |
        ¬ MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix
          (chainPauliFin_isHermitian (k + 3)) θ).eigenvalues}
        = (polynomialMatrixProjectiveGenericSet
            (spectralGenericMatrix (chainPauliFin (k + 3))))ᶜ := by
      ext θ
      exact not_congr (mem_genericSet_iff_maximallyProjective
        (chainPauliFin_isHermitian (k + 3)) θ).symm
    rw [hEq]
    exact measurableSet_polynomialMatrixProjectiveGenericSet_compl _
  exact hmeas hchain

theorem volume_pathBadSet_eq_zero :
    (volume : Measure (PathLabel (k + 1) → ℝ)) (pathBadSet k) = 0 := by
  classical
  have hmp : MeasurePreserving (pathChainCoeff k)
      (volume : Measure (PathLabel (k + 1) → ℝ))
      (volume : Measure (Fin (Fintype.card (ChainLabel (k + 3))) → ℝ)) := by
    have h := (volume_measurePreserving_piCongrLeft
      (fun _ : PathLabel (k + 1) => ℝ) (pathCoeffEquiv (k + 1))).symm
      (MeasurableEquiv.piCongrLeft (fun _ : PathLabel (k + 1) => ℝ) (pathCoeffEquiv (k + 1)))
    have hmap : ⇑(MeasurableEquiv.piCongrLeft
        (fun _ : PathLabel (k + 1) => ℝ) (pathCoeffEquiv (k + 1))).symm
        = pathChainCoeff k := by
      funext u a
      rfl
    rwa [hmap] at h
  have hchainnull := volume_notMaximallyProjective_chain_eq_zero k
  have hchainmeas : MeasurableSet {θ : Fin (Fintype.card (ChainLabel (k + 3))) → ℝ |
      ¬ MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix
        (chainPauliFin_isHermitian (k + 3)) θ).eigenvalues} := by
    have hEq : {θ : Fin (Fintype.card (ChainLabel (k + 3))) → ℝ |
        ¬ MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix
          (chainPauliFin_isHermitian (k + 3)) θ).eigenvalues}
        = (polynomialMatrixProjectiveGenericSet
            (spectralGenericMatrix (chainPauliFin (k + 3))))ᶜ := by
      ext θ
      exact not_congr (mem_genericSet_iff_maximallyProjective
        (chainPauliFin_isHermitian (k + 3)) θ).symm
    rw [hEq]
    exact measurableSet_polynomialMatrixProjectiveGenericSet_compl _
  have hpre : pathBadSet k = pathChainCoeff k ⁻¹'
      {θ : Fin (Fintype.card (ChainLabel (k + 3))) → ℝ |
        ¬ MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix
          (chainPauliFin_isHermitian (k + 3)) θ).eigenvalues} := rfl
  rw [hpre, hmp.measure_preimage hchainmeas.nullMeasurableSet, hchainnull]

/-- The degenerate directions of the path shell, in Euclidean coordinates. -/
def pathBadEuclid : Set (PathShell (k + 1)) :=
  {x | ¬ MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix
    (chainPauliFin_isHermitian (k + 3)) (pathChainCoeff k (WithLp.ofLp x))).eigenvalues}

theorem volume_pathBadEuclid_eq_zero :
    (volume : Measure (PathShell (k + 1))) (pathBadEuclid k) = 0 := by
  have hmp := PiLp.volume_preserving_ofLp (PathLabel (k + 1))
  have hpre : pathBadEuclid k = WithLp.ofLp ⁻¹' pathBadSet k := rfl
  rw [hpre, hmp.measure_preimage (measurableSet_pathBadSet k).nullMeasurableSet,
    volume_pathBadSet_eq_zero]


/-- The degenerate directions of the unit path shell. -/
def pathBadSphere : Set (sphere (0 : PathShell (k + 1)) 1) :=
  {v | ¬ MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix
    (chainPauliFin_isHermitian (k + 3))
      (pathChainCoeff k (WithLp.ofLp (v : PathShell (k + 1))))).eigenvalues}

theorem measurableSet_pathBadEuclid : MeasurableSet (pathBadEuclid k) := by
  have hpre : pathBadEuclid k = WithLp.ofLp ⁻¹' pathBadSet k := rfl
  rw [hpre]
  exact (measurableSet_pathBadSet k).preimage (by fun_prop)

theorem measurableSet_pathBadSphere : MeasurableSet (pathBadSphere k) := by
  have hpre : pathBadSphere k = Subtype.val ⁻¹' pathBadEuclid k := rfl
  rw [hpre]
  exact (measurableSet_pathBadEuclid k).preimage measurable_subtype_coe

theorem toSphere_pathBadSphere_eq_zero :
    (volume : Measure (PathShell (k + 1))).toSphere (pathBadSphere k) = 0 := by
  refine toSphere_eq_zero_of_scaleInvariant (volume_pathBadEuclid_eq_zero k) ?_
    (measurableSet_pathBadSphere k) (fun v hv => hv)
  intro r hr x hx hmax
  refine hx ?_
  exact (maximallyProjectiveEnergy_spectralEnsemble_smul_iff
    (chainPauliFin_isHermitian (k + 3)) hr.ne' (pathChainCoeff k (WithLp.ofLp x))).mp hmax

theorem pathShellProb_pathBadSphere_eq_zero : pathShellProb (pathBadSphere k) = 0 := by
  rw [pathShellProb, toSphere_pathBadSphere_eq_zero k]
  simp


/-- The numbered chain matrix of a path-shell coefficient vector. -/
def pathChainMatrix (u : PathShell (k + 1)) :
    Matrix (Fin (2 ^ (k + 3))) (Fin (2 ^ (k + 3))) ℂ :=
  spectralEnsembleMatrix (chainPauliFin (k + 3)) (pathChainCoeff k (WithLp.ofLp u))

theorem isHermitian_pathChainMatrix (u : PathShell (k + 1)) :
    (pathChainMatrix k u).IsHermitian :=
  isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (k + 3)) _

/-- The canonical orthonormal eigenbasis of the path-local Hamiltonian, on the register. -/
def pathEigenBasis (u : PathShell (k + 1)) :
    FiniteQubitConfiguration (Fin (k + 3)) → FiniteQubitConfiguration (Fin (k + 3)) → ℂ :=
  fun j x => hermitianEigenBasis (pathChainMatrix k u) (isHermitian_pathChainMatrix k u)
    (qubitConfigFin (k + 3) j) (qubitConfigFin (k + 3) x)

/-- Its eigenvalues. -/
def pathEigenValues (u : PathShell (k + 1)) :
    FiniteQubitConfiguration (Fin (k + 3)) → ℝ :=
  fun j => (isHermitian_pathChainMatrix k u).eigenvalues (qubitConfigFin (k + 3) j)

theorem isOrthoEigenBasis_pathEigenBasis (u : PathShell (k + 1)) :
    IsOrthoEigenBasis (pathHamiltonian u) (pathEigenBasis k u) (pathEigenValues k u) := by
  have h0 : IsOrthoEigenBasis (pathChainMatrix k u)
      (hermitianEigenBasis (pathChainMatrix k u) (isHermitian_pathChainMatrix k u))
      (isHermitian_pathChainMatrix k u).eigenvalues :=
    isOrthoEigenBasis_hermitian _ _
  have hre : Matrix.reindex (qubitConfigFin (k + 3)) (qubitConfigFin (k + 3))
      (pathHamiltonian u) = pathChainMatrix k u := reindex_pathHamiltonian u
  have hb : IsOrthoEigenBasis (Matrix.reindex (qubitConfigFin (k + 3)) (qubitConfigFin (k + 3))
      (pathHamiltonian u))
      (hermitianEigenBasis (pathChainMatrix k u) (isHermitian_pathChainMatrix k u))
      (isHermitian_pathChainMatrix k u).eigenvalues :=
    ⟨h0.orth, fun j => by rw [hre]; exact h0.eigen j, h0.complete⟩
  exact IsOrthoEigenBasis.ofReindex (qubitConfigFin (k + 3)) hb

theorem maximallyProjectiveEnergy_pathEigenValues {v : sphere (0 : PathShell (k + 1)) 1}
    (hv : v ∉ pathBadSphere k) :
    MaximallyProjectiveEnergy (pathEigenValues k (v : PathShell (k + 1))) :=
  (not_not.mp hv).comp_equiv (qubitConfigFin (k + 3))

/-- **Outside a null set of directions, the path-local Hamiltonian has an orthonormal eigenbasis
with maximally projective spectrum.** -/
theorem exists_pathHamiltonian_orthoEigenBasis {v : sphere (0 : PathShell (k + 1)) 1}
    (hv : v ∉ pathBadSphere k) :
    ∃ (e : FiniteQubitConfiguration (Fin (k + 3)) → FiniteQubitConfiguration (Fin (k + 3)) → ℂ)
      (lam : FiniteQubitConfiguration (Fin (k + 3)) → ℝ),
      IsOrthoEigenBasis (pathHamiltonian (v : PathShell (k + 1))) e lam
        ∧ MaximallyProjectiveEnergy lam := by
  classical
  have hmax : MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix
      (chainPauliFin_isHermitian (k + 3))
        (pathChainCoeff k (WithLp.ofLp (v : PathShell (k + 1))))).eigenvalues := not_not.mp hv
  obtain ⟨M, hMdef⟩ : ∃ M, M = spectralEnsembleMatrix (chainPauliFin (k + 3))
    (pathChainCoeff k (WithLp.ofLp (v : PathShell (k + 1)))) := ⟨_, rfl⟩
  have hMherm : M.IsHermitian := by
    rw [hMdef]
    exact isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (k + 3)) _
  have h0 : IsOrthoEigenBasis M (hermitianEigenBasis M hMherm) hMherm.eigenvalues :=
    isOrthoEigenBasis_hermitian M hMherm
  have hre : Matrix.reindex (qubitConfigFin (k + 3)) (qubitConfigFin (k + 3))
      (pathHamiltonian (v : PathShell (k + 1))) = M := by
    rw [hMdef]
    exact reindex_pathHamiltonian (v : PathShell (k + 1))
  have hb : IsOrthoEigenBasis (Matrix.reindex (qubitConfigFin (k + 3)) (qubitConfigFin (k + 3))
      (pathHamiltonian (v : PathShell (k + 1))))
      (hermitianEigenBasis M hMherm) hMherm.eigenvalues :=
    ⟨h0.orth, fun j => by rw [hre]; exact h0.eigen j, h0.complete⟩
  refine ⟨_, _, IsOrthoEigenBasis.ofReindex (qubitConfigFin (k + 3)) hb, ?_⟩
  have hev : hMherm.eigenvalues = (isHermitian_spectralEnsembleMatrix
      (chainPauliFin_isHermitian (k + 3))
        (pathChainCoeff k (WithLp.ofLp (v : PathShell (k + 1))))).eigenvalues :=
    eigenvalues_congr_of_eq hMherm _ hMdef
  rw [hev]
  exact hmax.comp_equiv (qubitConfigFin (k + 3))


/-- **Selecting a nondegenerate direction inside a positive-measure sector.** -/
theorem exists_mem_notMem_pathBadSphere {A : Set (sphere (0 : PathShell (k + 1)) 1)}
    (hA : 0 < pathShellProb A) : ∃ v ∈ A, v ∉ pathBadSphere k := by
  by_contra hcon
  have hsub : A ⊆ pathBadSphere k := by
    intro v hv
    by_contra hnot
    exact hcon ⟨v, hv, hnot⟩
  have hzero : (volume : Measure (PathShell (k + 1))).toSphere A = 0 := by
    refine le_antisymm ?_ zero_le
    rw [← toSphere_pathBadSphere_eq_zero k]
    exact measure_mono hsub
  exact absurd hzero (pathShellProb_pos_iff.mp hA)

end PathTransport

end GaloisForLFunctions.HTGeometry

end
