/-
# The patch reading of the nearest-neighbour shell

Everything the incubation law needs about the nearest-neighbour shell -- the Hamiltonian, its
eigenbasis, the collision of a seed, and the genericity of the spectrum -- is pulled back to the
patch space of the diagonal splitting along one linear isometry, so the codimension tube estimates
and the shell laws meet on the same object.  The collision is read through the gauge-invariant
`crossCollision`, which is continuous on the simple locus and hence measurable, as the Fubini seed
selection requires.

Main results:
* `patchCoeffIsometry`, `patchToCoeff`, `toSphere_preimage_patchToCoeff`.
* `chainBadSphere`, `toSphere_preimage_chainBadSphere_eq_zero` — the degenerate directions are null.
* `patchGood`, `measurableSet_patchGood`, `density_patchGood` — **the density certificate `(5)`**.
* `patchEigenBasis`, `isOrthoEigenBasis_patchEigenBasis`,
  `maximallyProjectiveEnergy_patchEigenValues`.
* `edgeRho_le_norm_edgePart`, `edgeCoupling_lower` — **`(21)`**.
-/
import GaloisForLFunctions.HTGeometry.PathShellPatchTransport
import GaloisForLFunctions.HTGeometry.ShellPlateauAssembly
import GaloisForLFunctions.HTGeometry.CubicSeedPlateauLaw
import GaloisForLFunctions.HTGeometry.CapacityIncubationLaw
import GaloisForLFunctions.HTGeometry.StabilizerSeededPlateauLaw
import GaloisForLFunctions.HTGeometry.DiagonalPatchConstruction
import GaloisForLFunctions.HTGeometry.IncubationTubeTransport

open MeasureTheory Metric Set Matrix
open scoped Matrix Matrix.Norms.L2Operator

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable (k : ℕ)

/-- The chain-coefficient reading of a path-shell coefficient vector, as an isometry. -/
def pathToChainIsometry (k : ℕ) :
    PathShell (k + 1) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (Fintype.card (ChainLabel (k + 3)))) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (pathCoeffEquiv (k + 1)).symm

theorem ofLp_pathToChainIsometry (u : PathShell (k + 1)) :
    WithLp.ofLp (pathToChainIsometry k u) = pathChainCoeff k (WithLp.ofLp u) := rfl

/-- The patch space of the diagonal splitting, read in chain coefficients. -/
def patchCoeffIsometry (k : ℕ) :
    PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (Fintype.card (ChainLabel (k + 3)))) :=
  (pathPatchIsometry (k + 1)).trans (pathToChainIsometry k)

/-- The induced map of unit spheres. -/
def patchToCoeff (k : ℕ) :
    sphere (0 : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)) 1 →
      coeffSphere (Fintype.card (ChainLabel (k + 3))) :=
  crossSphereMap (patchCoeffIsometry k)

theorem continuous_patchToCoeff : Continuous (patchToCoeff k) :=
  continuous_crossSphereMap (patchCoeffIsometry k)

theorem toSphere_preimage_patchToCoeff
    {S : Set (coeffSphere (Fintype.card (ChainLabel (k + 3))))} (hS : MeasurableSet S) :
    (volume : Measure (PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))).toSphere
        (patchToCoeff k ⁻¹' S)
      = (volume : Measure (EuclideanSpace ℝ
          (Fin (Fintype.card (ChainLabel (k + 3)))))).toSphere S :=
  toSphere_preimage_crossSphereMap (patchCoeffIsometry k) hS

/-- The degenerate directions of the numbered chain shell. -/
def chainBadSphere (k : ℕ) : Set (coeffSphere (Fintype.card (ChainLabel (k + 3)))) :=
  {x | ¬ MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix
    (chainPauliFin_isHermitian (k + 3)) (sphereCoeff x)).eigenvalues}

theorem measurableSet_chainBadSphere : MeasurableSet (chainBadSphere k) := by
  classical
  have hEq : {θ : Fin (Fintype.card (ChainLabel (k + 3))) → ℝ |
      ¬ MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix
        (chainPauliFin_isHermitian (k + 3)) θ).eigenvalues}
      = (polynomialMatrixProjectiveGenericSet
          (spectralGenericMatrix (chainPauliFin (k + 3))))ᶜ := by
    ext θ
    exact not_congr (mem_genericSet_iff_maximallyProjective
      (chainPauliFin_isHermitian (k + 3)) θ).symm
  have hmeas : MeasurableSet {θ : Fin (Fintype.card (ChainLabel (k + 3))) → ℝ |
      ¬ MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix
        (chainPauliFin_isHermitian (k + 3)) θ).eigenvalues} := by
    rw [hEq]
    exact measurableSet_polynomialMatrixProjectiveGenericSet_compl _
  exact hmeas.preimage continuous_sphereCoeff.measurable

theorem toSphere_chainBadSphere_eq_zero :
    (volume : Measure (EuclideanSpace ℝ (Fin (Fintype.card (ChainLabel (k + 3)))))).toSphere
      (chainBadSphere k) = 0 := by
  classical
  obtain ⟨B, hBdef⟩ : ∃ B : Set (EuclideanSpace ℝ (Fin (Fintype.card (ChainLabel (k + 3))))),
    B = {x | ¬ MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix
      (chainPauliFin_isHermitian (k + 3)) (WithLp.ofLp x)).eigenvalues} := ⟨_, rfl⟩
  refine toSphere_eq_zero_of_scaleInvariant (B := B) ?_ ?_ (measurableSet_chainBadSphere k)
    (fun x hx => by rw [hBdef]; exact hx)
  · have hmp := PiLp.volume_preserving_ofLp (Fin (Fintype.card (ChainLabel (k + 3))))
    have hmeas : MeasurableSet {θ : Fin (Fintype.card (ChainLabel (k + 3))) → ℝ |
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
    have hpre : {x : EuclideanSpace ℝ (Fin (Fintype.card (ChainLabel (k + 3)))) |
        ¬ MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix
          (chainPauliFin_isHermitian (k + 3)) (WithLp.ofLp x)).eigenvalues}
        = WithLp.ofLp ⁻¹' {θ | ¬ MaximallyProjectiveEnergy
          (isHermitian_spectralEnsembleMatrix (chainPauliFin_isHermitian (k + 3)) θ).eigenvalues} :=
      rfl
    rw [hBdef, hpre, hmp.measure_preimage hmeas.nullMeasurableSet,
      volume_notMaximallyProjective_chain_eq_zero k]
  · intro r hr x hx
    rw [hBdef] at hx ⊢
    intro hmax
    refine hx ?_
    exact (maximallyProjectiveEnergy_spectralEnsemble_smul_iff
      (chainPauliFin_isHermitian (k + 3)) hr.ne' (WithLp.ofLp x)).mp hmax

theorem toSphere_preimage_chainBadSphere_eq_zero :
    (volume : Measure (PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))).toSphere
      (patchToCoeff k ⁻¹' chainBadSphere k) = 0 := by
  rw [toSphere_preimage_patchToCoeff k (measurableSet_chainBadSphere k)]
  exact toSphere_chainBadSphere_eq_zero k


section Good

variable {k}

/-- The register dimension. -/
abbrev regDim (k : ℕ) : ℝ := (Fintype.card (FiniteQubitConfiguration (Fin (k + 3))) : ℝ)

/-- The unit sphere of the patch space of the diagonal splitting. -/
abbrev PatchSphere (k : ℕ) :=
  sphere (0 : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)) 1

/-- The patch directions at which a cubic seed is collision-good, together with the degenerate
directions where the requirement is vacuous. -/
def patchGood (k : ℕ) (kap : ℝ) (c : MonLe (Fin (k + 3)) 3 → ZMod 8) : Set (PatchSphere k) :=
  patchToCoeff k ⁻¹'
    (goodSet (chainPauliFin_isHermitian (k + 3)) (cubicSeed (k + 3) c)
        ((2 + kap) / regDim k)
      ∪ (simpleLocus (chainPauliFin_isHermitian (k + 3)))ᶜ)

theorem measurableSet_patchGood (kap : ℝ) (c : MonLe (Fin (k + 3)) 3 → ZMod 8) :
    MeasurableSet (patchGood k kap c) := by
  refine MeasurableSet.preimage ?_ (continuous_patchToCoeff k).measurable
  exact (measurableSet_goodSet _ _ _).union
    (isOpen_simpleLocus (chainPauliFin_isHermitian (k + 3))).measurableSet.compl

/-- **The density certificate.**  At every patch direction, all but a `96/(κ²D)` fraction of the
cubic seeds are collision-good. -/
theorem density_patchGood {kap : ℝ} (hkap : 0 < kap)
    (ω : PatchSphere k) :
    ((Fintype.card (MonLe (Fin (k + 3)) 3 → ZMod 8) : ℝ)) * (1 - 96 / (kap ^ 2 * regDim k))
      ≤ ∑ c : MonLe (Fin (k + 3)) 3 → ZMod 8,
        Set.indicator (patchGood k kap c) (1 : PatchSphere k → ℝ) ω := by
  classical
  obtain ⟨N, hNdef⟩ : ∃ N : ℝ,
    N = (Fintype.card (MonLe (Fin (k + 3)) 3 → ZMod 8) : ℝ) := ⟨_, rfl⟩
  have hNpos : 0 < N := by
    rw [hNdef]
    have : 0 < Fintype.card (MonLe (Fin (k + 3)) 3 → ZMod 8) := Fintype.card_pos
    exact_mod_cast this
  obtain ⟨x, hxdef⟩ : ∃ x, x = patchToCoeff k ω := ⟨_, rfl⟩
  obtain ⟨Sg, hSgdef⟩ : ∃ Sg : Finset (MonLe (Fin (k + 3)) 3 → ZMod 8),
    Sg = Finset.univ.filter fun c => ω ∈ patchGood k kap c := ⟨_, rfl⟩
  have hind : (∑ c : MonLe (Fin (k + 3)) 3 → ZMod 8,
      Set.indicator (patchGood k kap c) (1 : PatchSphere k → ℝ) ω) = (Sg.card : ℝ) := by
    rw [hSgdef, Finset.card_filter]
    push_cast
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Set.indicator_apply]
    by_cases hc : ω ∈ patchGood k kap c <;> simp [hc]
  rw [hind, ← hNdef]
  obtain ⟨Sb, hSbdef⟩ : ∃ Sb : Finset (MonLe (Fin (k + 3)) 3 → ZMod 8),
    Sb = Finset.univ.filter fun c =>
      (2 + kap) / regDim k
        < phaseCollision (registerEigenBasis (k + 3) (chainPauliFin_isHermitian (k + 3)) x)
          (eighthPhase (polyEval 3 c)) := ⟨_, rfl⟩
  have hcompl : Sg.card + Sb.card ≥ Fintype.card (MonLe (Fin (k + 3)) 3 → ZMod 8) := by
    have hsub : (Finset.univ : Finset (MonLe (Fin (k + 3)) 3 → ZMod 8)) ⊆ Sg ∪ Sb := by
      intro c _
      rw [Finset.mem_union, hSgdef, hSbdef, Finset.mem_filter, Finset.mem_filter]
      by_cases hgood : ω ∈ patchGood k kap c
      · exact Or.inl ⟨Finset.mem_univ c, hgood⟩
      · refine Or.inr ⟨Finset.mem_univ c, ?_⟩
        by_contra hle
        refine hgood ?_
        rw [patchGood, Set.mem_preimage, ← hxdef]
        by_cases hxs : x ∈ simpleLocus (chainPauliFin_isHermitian (k + 3))
        · refine Or.inl ⟨hxs, ?_⟩
          show crossCollision (chainPauliFin_isHermitian (k + 3)) (cubicSeed (k + 3) c) x
            ≤ (2 + kap) / regDim k
          rw [crossCollision_cubicSeed k c hxs]
          exact not_lt.mp hle
        · exact Or.inr hxs
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_univ] at hcard
    exact le_trans hcard (Finset.card_union_le Sg Sb)
  have hbad : (Sb.card : ℝ) ≤ N * (96 / (kap ^ 2 * regDim k)) := by
    have horth := orth_registerEigenBasis (k + 3) (chainPauliFin_isHermitian (k + 3)) x
    have htail := card_filter_phaseCollision_polyEval_gt_le (ι := Fin (k + 3))
      (J := FiniteQubitConfiguration (Fin (k + 3))) 3 (by norm_num)
      (registerEigenBasis (k + 3) (chainPauliFin_isHermitian (k + 3)) x) horth rfl hkap
    rw [hSbdef]
    rw [mul_comm, ← div_le_iff₀ hNpos, div_eq_mul_inv, hNdef]
    exact htail
  have hcardR : (Fintype.card (MonLe (Fin (k + 3)) 3 → ZMod 8) : ℝ) ≤ (Sg.card : ℝ) + Sb.card := by
    exact_mod_cast hcompl
  rw [← hNdef] at hcardR
  nlinarith [hbad, hcardR]

end Good


section Eigen

variable {k}

/-- The register eigenbasis of the path-local Hamiltonian at a patch direction. -/
def patchEigenBasis (k : ℕ) (ω : PatchSphere k) :
    FiniteQubitConfiguration (Fin (k + 3)) → FiniteQubitConfiguration (Fin (k + 3)) → ℂ :=
  registerEigenBasis (k + 3) (chainPauliFin_isHermitian (k + 3)) (patchToCoeff k ω)

/-- Its eigenvalues. -/
def patchEigenValues (k : ℕ) (ω : PatchSphere k) :
    FiniteQubitConfiguration (Fin (k + 3)) → ℝ :=
  fun j => spectralTuple (chainPauliFin_isHermitian (k + 3)) (sphereCoeff (patchToCoeff k ω))
    (qubitConfigFin (k + 3) j)

theorem patchHam_reindex (ω : PatchSphere k) :
    Matrix.reindex (qubitConfigFin (k + 3)) (qubitConfigFin (k + 3))
        (pathHamiltonian (pathPatchIsometry (k + 1)
          (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))))
      = spectralEnsembleMatrix (chainPauliFin (k + 3)) (sphereCoeff (patchToCoeff k ω)) :=
  reindex_pathHamiltonian _

theorem isOrthoEigenBasis_patchEigenBasis (ω : PatchSphere k) :
    IsOrthoEigenBasis (pathHamiltonian (pathPatchIsometry (k + 1)
        (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12))))
      (patchEigenBasis k ω) (patchEigenValues k ω) := by
  have h0 := isOrthoEigenBasis_sortedEigenBasis (chainPauliFin_isHermitian (k + 3))
    (sphereCoeff (patchToCoeff k ω))
  have hre := patchHam_reindex ω
  have hb : IsOrthoEigenBasis (Matrix.reindex (qubitConfigFin (k + 3)) (qubitConfigFin (k + 3))
      (pathHamiltonian (pathPatchIsometry (k + 1)
        (ω : PatchSpace (2 * (k + 1) + 3) (10 * (k + 1) + 12)))))
      (sortedEigenBasis (chainPauliFin_isHermitian (k + 3)) (sphereCoeff (patchToCoeff k ω)))
      (spectralTuple (chainPauliFin_isHermitian (k + 3)) (sphereCoeff (patchToCoeff k ω))) :=
    ⟨h0.orth, fun j => by rw [hre]; exact h0.eigen j, h0.complete⟩
  exact IsOrthoEigenBasis.ofReindex (qubitConfigFin (k + 3)) hb

theorem maximallyProjectiveEnergy_patchEigenValues {ω : PatchSphere k}
    (hω : ω ∉ patchToCoeff k ⁻¹' chainBadSphere k) :
    MaximallyProjectiveEnergy (patchEigenValues k ω) := by
  have hmax : MaximallyProjectiveEnergy (isHermitian_spectralEnsembleMatrix
      (chainPauliFin_isHermitian (k + 3)) (sphereCoeff (patchToCoeff k ω))).eigenvalues :=
    not_not.mp hω
  have hsorted : MaximallyProjectiveEnergy
      (spectralTuple (chainPauliFin_isHermitian (k + 3)) (sphereCoeff (patchToCoeff k ω))) :=
    hmax.comp_equiv_relabel (Tuple.sort (isHermitian_spectralEnsembleMatrix
      (chainPauliFin_isHermitian (k + 3)) (sphereCoeff (patchToCoeff k ω))).eigenvalues)
  exact hsorted.comp_equiv_relabel (qubitConfigFin (k + 3))

theorem mem_simpleLocus_of_notMem_chainBadSphere {ω : PatchSphere k}
    (hω : ω ∉ patchToCoeff k ⁻¹' chainBadSphere k) :
    patchToCoeff k ω ∈ simpleLocus (chainPauliFin_isHermitian (k + 3)) :=
  (not_not.mp hω : MaximallyProjectiveEnergy _).injective

end Eigen


section EdgeCoupling

variable {k}

theorem hsNormSq_matrix_eq_trace {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    ((hsNormSq A : ℝ) : ℂ) = (Aᴴ * A).trace := by
  rw [hsNormSq_eq_sum_star, Matrix.trace]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Matrix.diag_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun x _ => rfl

/-- **The Hilbert--Schmidt norm of a Pauli combination.** -/
theorem hsNormSq_pauliCombination {m : ℕ} {κ : Type*} [Fintype κ] [DecidableEq κ]
    {P : κ → Fin m → Option (Fin 3)} (hP : Function.Injective P) (J : κ → ℝ) :
    hsNormSq (∑ q, ((J q : ℝ) : ℂ) • finitePauliMatrix (P q))
      = (2 ^ m : ℝ) * ∑ q, J q ^ 2 := by
  classical
  obtain ⟨A, hAdef⟩ : ∃ A, A = ∑ q, ((J q : ℝ) : ℂ) • finitePauliMatrix (P q) := ⟨_, rfl⟩
  have hherm : Aᴴ = A := by
    rw [hAdef, Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Matrix.conjTranspose_smul, RCLike.star_def, Complex.conj_ofReal]
    exact congrArg _ (finitePauliMatrix_isHermitian (P q))
  have hcomplex : ((hsNormSq A : ℝ) : ℂ) = ((((2 : ℝ) ^ m : ℝ) * ∑ q, J q ^ 2 : ℝ) : ℂ) := by
    rw [hsNormSq_matrix_eq_trace, hherm, hAdef, Finset.sum_mul_sum, Matrix.trace_sum]
    have hterm : ∀ q, (∑ p, (((J q : ℝ) : ℂ) • finitePauliMatrix (P q)) *
        (((J p : ℝ) : ℂ) • finitePauliMatrix (P p))).trace
        = ((J q : ℝ) : ℂ) * ((J q : ℝ) : ℂ) * ((2 : ℝ) ^ m : ℂ) := by
      intro q
      rw [Matrix.trace_sum]
      have hone : ∀ p, ((((J q : ℝ) : ℂ) • finitePauliMatrix (P q)) *
          (((J p : ℝ) : ℂ) • finitePauliMatrix (P p))).trace
          = if p = q then ((J q : ℝ) : ℂ) * ((J q : ℝ) : ℂ) * ((2 : ℝ) ^ m : ℂ) else 0 := by
        intro p
        rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul,
          trace_pauli_mul]
        by_cases hpq : p = q
        · subst hpq
          rw [if_pos rfl, if_pos rfl, Fintype.card_fin]
          push_cast
          ring
        · rw [if_neg hpq, if_neg (fun hc => hpq (hP hc.symm))]
          simp
      rw [Finset.sum_congr rfl (fun p _ => hone p), Finset.sum_ite_eq' Finset.univ q,
        if_pos (Finset.mem_univ q)]
    rw [Finset.sum_congr rfl (fun q _ => hterm q)]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  rw [← hAdef]
  exact_mod_cast hcomplex

theorem edgeRho_le_norm_edgePart {n : ℕ} (u : PathShell n) (e : Fin (n + 1)) :
    edgeRho (edgeCoeff u e) ≤ ‖edgePart u e‖ := by
  classical
  have hinj : Function.Injective (fun ab : Fin 3 × Fin 3 => couplingWord e ab) := by
    intro ab cd h
    have hne : e.succ ≠ e.castSucc := by
      intro hc
      have hv := congrArg Fin.val hc
      rw [Fin.val_succ, Fin.val_castSucc] at hv
      omega
    have h1 : (if e.castSucc = e.castSucc then some ab.1
          else if e.castSucc = e.succ then some ab.2 else none)
        = (if e.castSucc = e.castSucc then some cd.1
          else if e.castSucc = e.succ then some cd.2 else none) := congrFun h e.castSucc
    have h2 : (if e.succ = e.castSucc then some ab.1
          else if e.succ = e.succ then some ab.2 else none)
        = (if e.succ = e.castSucc then some cd.1
          else if e.succ = e.succ then some cd.2 else none) := congrFun h e.succ
    rw [if_pos rfl, if_pos rfl] at h1
    rw [if_neg hne, if_pos rfl, if_neg hne, if_pos rfl] at h2
    exact Prod.ext (Option.some_injective _ h1) (Option.some_injective _ h2)
  have hhs : hsNormSq (edgePart u e) = (2 ^ (n + 2) : ℝ) * ∑ ab, edgeCoeff u e ab ^ 2 :=
    hsNormSq_pauliCombination hinj (fun ab => edgeCoeff u e ab)
  have hle := hsNormSq_le_card_mul_sq (edgePart u e)
  have hcard : (Fintype.card (FiniteQubitConfiguration (Fin (n + 2))) : ℝ) = (2 ^ (n + 2) : ℝ) := by
    simp [FiniteQubitConfiguration]
  rw [hhs, hcard] at hle
  have hpow : (0 : ℝ) < (2 ^ (n + 2) : ℝ) := by positivity
  have hsq : edgeRho (edgeCoeff u e) ^ 2 ≤ ‖edgePart u e‖ ^ 2 := by
    rw [edgeRho_sq]
    nlinarith [hle, hpow]
  nlinarith [hsq, edgeRho_nonneg (edgeCoeff u e), norm_nonneg (edgePart u e)]

theorem abs_edgeCoeff_le_edgeRho (J : Fin 3 × Fin 3 → ℝ) (ab : Fin 3 × Fin 3) :
    |J ab| ≤ edgeRho J := by
  rw [edgeRho, ← Real.sqrt_sq (abs_nonneg (J ab))]
  refine Real.sqrt_le_sqrt ?_
  rw [sq_abs]
  exact Finset.single_le_sum (f := fun q => J q ^ 2) (fun q _ => by positivity)
    (Finset.mem_univ ab)

/-- The coordinates of an embedded carrier point. -/
theorem ofLp_pathPatchIsometry_embed {n : ℕ}
    (w : EuclideanSpace ℝ (Fin (2 * n + 3))) (l : PathLabel n) :
    WithLp.ofLp (pathPatchIsometry n
        (WithLp.toLp 2 (w, (0 : EuclideanSpace ℝ (Fin (10 * n + 12)))))) l
      = Sum.elim (WithLp.ofLp w) (0 : Fin (10 * n + 12) → ℝ) ((pathPatchEquiv n).symm l) := rfl

theorem pathPatchEquiv_symm_isDiag {n : ℕ} {l : PathLabel n} (hl : IsDiagLabel l) :
    ∃ i, (pathPatchEquiv n).symm l = Sum.inl i := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, (Equiv.sumCompl (IsDiagLabel (n := n))).symm l = Sum.inl j :=
    ⟨⟨l, hl⟩, by
      have : (Equiv.sumCompl (IsDiagLabel (n := n))) (Sum.inl ⟨l, hl⟩) = l := rfl
      exact (Equiv.symm_apply_eq _).mpr this.symm⟩
  refine ⟨Fintype.equivFinOfCardEq (card_diagLabel n) j, ?_⟩
  show (Equiv.sumCongr (Fintype.equivFinOfCardEq (card_diagLabel n)).symm
      (Fintype.equivFinOfCardEq (card_offDiagLabel n)).symm).symm
      ((Equiv.sumCompl (IsDiagLabel (n := n))).symm l) = _
  rw [hj]
  rfl

/-- **`(21)`.**  Inside the tube over the cap, every edge stays quantitatively coupled. -/
theorem edgeCoupling_lower {n : ℕ} {ρ r : ℝ}
    {u : PathShell n} {w : EuclideanSpace ℝ (Fin (2 * n + 3))}
    (hw : w ∈ sphericalCap (uniformDir (2 * n + 3)) ρ)
    (hdist : ‖u - pathPatchIsometry n
      (WithLp.toLp 2 (w, (0 : EuclideanSpace ℝ (Fin (10 * n + 12)))))‖ ≤ r)
    (e : Fin (n + 1)) :
    (Real.sqrt ((2 * n + 3 : ℕ) : ℝ))⁻¹ - ρ - r ≤ ‖edgePart u e‖ := by
  classical
  obtain ⟨y, hydef⟩ : ∃ y : PathShell n, y = pathPatchIsometry n
    (WithLp.toLp 2 (w, (0 : EuclideanSpace ℝ (Fin (10 * n + 12))))) := ⟨_, rfl⟩
  obtain ⟨l, hldef⟩ : ∃ l : PathLabel n, l = Sum.inr (e, ((2 : Fin 3), (2 : Fin 3))) := ⟨_, rfl⟩
  have hldiag : IsDiagLabel l := by rw [hldef]; rfl
  obtain ⟨i, hi⟩ := pathPatchEquiv_symm_isDiag hldiag
  have hy : WithLp.ofLp y l = WithLp.ofLp w i := by
    rw [hydef, ofLp_pathPatchIsometry_embed, hi]
    rfl
  have hylow : (Real.sqrt ((2 * n + 3 : ℕ) : ℝ))⁻¹ - ρ ≤ WithLp.ofLp y l := by
    rw [hy]
    exact sphericalCap_coord_ge hw i
  have hclose : |WithLp.ofLp u l - WithLp.ofLp y l| ≤ r := by
    rw [hydef]
    exact le_trans (abs_coord_le_norm (u - pathPatchIsometry n
      (WithLp.toLp 2 (w, (0 : EuclideanSpace ℝ (Fin (10 * n + 12)))))) l) hdist
  have hcoef : (Real.sqrt ((2 * n + 3 : ℕ) : ℝ))⁻¹ - ρ - r ≤ WithLp.ofLp u l := by
    have := abs_le.mp hclose
    linarith [this.1, hylow]
  have hrho : |edgeCoeff u e ((2 : Fin 3), (2 : Fin 3))| ≤ edgeRho (edgeCoeff u e) :=
    abs_edgeCoeff_le_edgeRho _ _
  have hval : edgeCoeff u e ((2 : Fin 3), (2 : Fin 3)) = WithLp.ofLp u l := by
    rw [hldef]
    rfl
  have hop : edgeRho (edgeCoeff u e) ≤ ‖edgePart u e‖ := edgeRho_le_norm_edgePart u e
  have habs : WithLp.ofLp u l ≤ |edgeCoeff u e ((2 : Fin 3), (2 : Fin 3))| := by
    rw [hval]
    exact le_abs_self _
  linarith [hcoef, habs, hrho, hop]

end EdgeCoupling

end GaloisForLFunctions.HTGeometry

end
