import GaloisForLFunctions.RHTower.StaticChoiProjectiveCubicScalarReturnLaw
import GaloisForLFunctions.RHTower.StaticChoiResidualDesignFirstReturnLaw
import GaloisForLFunctions.RHTower.ResidualReplicaOptimalDesignTransportLaw
import GaloisForLFunctions.RHTower.TwoLocalAnchorTransversePseudodeterminantLaw
import GaloisForLFunctions.RHTower.AutonomousReturnReflection

/-!
# Same-draw growth and complete-target cubic first return

A determinant design is chosen before the Hamiltonian draw from physical
traceless Choi residuals. A uniform anchor--transverse pseudodeterminant law
then selects one ordinary time-independent two-local draw with laboratory
growth, maximal projective spectrum, and small residual moment. The scalar
projective-return obstruction and return-excised coarea law combine to exclude
continuous re-entry into every member of the supplied finite endpoint family
through the full inverse-square cubic window.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator
open Matrix Set

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Draw-independent speed ceiling on the certified local coefficient box. -/
def pairQubitProjectiveStaticChoiSpeedCeiling
    (L : ℕ) (rho scale : ℝ) : ℝ :=
  (Fintype.card (FiniteQubitConfiguration (Fin (L * 2))) : ℝ) *
    ((L : ℝ) + 1 + rho * nearestNeighborPathLocalGeneratorMass L +
      |scale| * (18 * ((L * 2 : ℕ) : ℝ) ^ (3 : ℕ))) + 1

/-- Full spectral Choi speed is at most dimension times operator norm plus one. -/
theorem staticChoiSpeed_eigenvalues_le_card_mul_norm_add_one
    {d : ℕ} [Nonempty (Fin d)]
    {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian) :
    staticChoiSpeed hH.eigenvalues ≤ (d : ℝ) * ‖H‖ + 1 := by
  unfold staticChoiSpeed
  have heig : ∀ i, |hH.eigenvalues i| ≤ ‖H‖ := by
    intro i
    have hspec : hH.eigenvalues i ∈ spectrum ℝ H :=
      hH.eigenvalues_mem_spectrum_real i
    simpa [Real.norm_eq_abs] using spectrum.norm_le_norm_of_mem hspec
  calc
    (∑ i, |hH.eigenvalues i|) + 1 ≤ (∑ _ : Fin d, ‖H‖) + 1 := by
      gcongr with i
      exact heig i
    _ = (d : ℝ) * ‖H‖ + 1 := by simp

/-- The same certified local draw obeys the deterministic Choi-speed ceiling. -/
theorem pairQubitProjective_staticChoiSpeed_le_ceiling
    {L : ℕ} (hL : 1 ≤ L)
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    {rho scale : ℝ}
    (hseed : ‖nearestNeighborPathLocalHamiltonian L p -
        inverseSquareChainHamiltonian L‖ ≤
      rho * nearestNeighborPathLocalGeneratorMass L)
    {x : TwoLocalPauliCoefficientSpace (L * 2)}
    (hx : x ∈ weakTwoLocalPauliCertifiedGrowthSet L) :
    staticChoiSpeed
        (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x) ≤
      pairQubitProjectiveStaticChoiSpeedCeiling L rho scale := by
  let P := twoLocalPauliGaussianHermitianPencil (L * 2)
  let H := P.affineReindexedHamiltonian
    (pairQubitProjectivePauliSeed L p) (scale • x)
  let hH : H.IsHermitian := P.affineReindexedHamiltonian_isHermitian
    (pairQubitProjectivePauliSeed_isHermitian L p) (scale • x)
  have hs := staticChoiSpeed_eigenvalues_le_card_mul_norm_add_one hH
  have hnorm : ‖H‖ ≤
      (L : ℝ) + 1 + rho * nearestNeighborPathLocalGeneratorMass L +
        |scale| * (18 * ((L * 2 : ℕ) : ℝ) ^ (3 : ℕ)) := by
    rw [show H = Matrix.reindexAlgEquiv ℂ ℂ
        (Fintype.equivFin (FiniteQubitConfiguration (Fin (L * 2))))
      (Matrix.reindexAlgEquiv ℂ ℂ (pairQubitPathConfigurationEquiv L)
        (projectiveSeedWeakTwoLocalHamiltonian L p scale x)) by
      exact pairQubitProjective_finiteHamiltonian_eq_doubleReindex L p scale x]
    rw [norm_reindexAlgEquiv_eq, norm_reindexAlgEquiv_eq]
    exact norm_projectiveSeedWeakTwoLocalHamiltonian_le hL hseed hx
  change staticChoiSpeed hH.eigenvalues ≤ _
  exact hs.trans (by
    unfold pairQubitProjectiveStaticChoiSpeedCeiling
    gcongr)

/-- Same-draw complete-target law: one ordinary static two-local Hamiltonian
has certified growth and maximal projective spectrum, yet cannot re-enter any
endpoint in the complete supplied finite image throughout the post-onset
cubic window. All selection and coarea budgets are fixed before the draw. -/
theorem exists_pairQubitProjective_growth_noCompleteTargetReturn
    {L : ℕ} (hL : 2 ≤ L)
    {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    (hp : p ∈ nearestNeighborPathLocalMaximalSet L)
    {rho scale : ℝ} (hrho : 0 ≤ rho)
    (hseed : ‖nearestNeighborPathLocalHamiltonian L p -
        inverseSquareChainHamiltonian L‖ ≤
      rho * nearestNeighborPathLocalGeneratorMass L)
    (hscale : scale ≠ 0)
    {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    {r : ℕ} (hr : 0 < r) {delta kappa : ℝ}
    (hdelta : 0 < delta) (hkappa : 0 < kappa)
    (hpos : 0 < Module.finrank ℂ (replicaTargetSpan r
      (physicalUnitaryChoiResidualTarget (fun c =>
        finiteGaussianHermitianPencilReindexedEndpoint
          (pairQubitPathUnitaryReindex L (U c))))))
    {guard eta returnRadius thetaN thetaW : ℝ}
    (hguard : 0 ≤ guard)
    (hTpos : 0 < 2 * Real.pi * (L : ℝ) ^ (3 : ℕ) - guard)
    (hreturnPos : 0 < returnRadius)
    (hthetaW : 0 < thetaW) (hgap : thetaW < thetaN)
    (hmeshReturn : thetaN - thetaW ≤ returnRadius)
    (hreturnT : returnRadius ≤ 2 * Real.pi * (L : ℝ) ^ (3 : ℕ) - guard)
    (hguardStart : guard ≤ returnRadius)
    (hscalarBudget :
      Real.sqrt (1 - inverseSquareChainCubicReturnSeparation L guard ^ (2 : ℕ) /
          (2 * (Fintype.card (Config (PairQubit L)) : ℝ) ^ (2 : ℕ))) +
        (2 * Real.pi * (L : ℝ) ^ (3 : ℕ)) *
          (rho * nearestNeighborPathLocalGeneratorMass L +
            |scale| * (18 * ((L * 2 : ℕ) : ℝ) ^ (3 : ℕ))) < eta)
    (hselect : pairQubitWeakTwoLocalGrowthFailureBudget L +
        Real.exp (-twoLocalAnchorTransverseUniformRate (L * 2) r scale
          (pairQubitProjectiveSeedGrowingReplicaOscillationCeiling L rho scale)) /
            kappa < 1)
    (hmoment :
      (Module.finrank ℂ (replicaTargetSpan r
          (physicalUnitaryChoiResidualTarget (fun c =>
            finiteGaussianHermitianPencilReindexedEndpoint
              (pairQubitPathUnitaryReindex L (U c))))) : ℝ) *
        ((r.factorial : ℝ) *
            (Fintype.card
              (FiniteQubitConfiguration (Fin (L * 2))) : ℝ)⁻¹ ^ r +
          kappa +
          Real.exp (-(((2 * Real.pi * (L : ℝ) ^ (3 : ℕ) - guard) * delta) ^ (2 : ℕ)) / 2)) <
        gaussianFloorTwo *
          (((thetaN - thetaW) /
              pairQubitProjectiveStaticChoiSpeedCeiling L rho scale) /
            (2 * (2 * Real.pi * (L : ℝ) ^ (3 : ℕ) - guard))) *
              (thetaW ^ (2 : ℕ)) ^ r) :
    ∃ x : TwoLocalPauliCoefficientSpace (L * 2),
      x ∈ weakTwoLocalPauliCertifiedGrowthSet L ∧
      MaximallyProjectiveEnergy
        (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x) ∧
      ¬ ∃ t ∈ Icc
          (returnRadius + (thetaN - thetaW) /
            staticChoiSpeed
              (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x))
          (2 * Real.pi * (L : ℝ) ^ (3 : ℕ) - guard),
        ∃ c, eta + thetaN ≤ ‖inner ℂ
          (staticSpectralChoiVector
            (Fintype.card (FiniteQubitConfiguration (Fin (L * 2)))) t
            (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x))
          (GaloisForLFunctions.RHTower.choiVector
            (pairQubitProjectiveSeedWeakTwoLocalSpectralEndpoint
              L p scale x (U c) :
                Matrix (Fin (Fintype.card
                  (FiniteQubitConfiguration (Fin (L * 2)))))
                  (Fin (Fintype.card
                    (FiniteQubitConfiguration (Fin (L * 2))))) ℂ))‖ := by
  let Ufin := fun c => finiteGaussianHermitianPencilReindexedEndpoint
    (pairQubitPathUnitaryReindex L (U c))
  change 0 < Module.finrank ℂ
    (replicaTargetSpan r (physicalUnitaryChoiResidualTarget Ufin)) at hpos
  obtain ⟨w, hw, hdesignAll⟩ :=
    exists_physicalUnitaryChoiResidual_optimalDesign_allSpectralBases
      (Fintype.card_pos : 0 < Fintype.card
        (FiniteQubitConfiguration (Fin (L * 2)))) r Ufin hpos
  have hcarrier :=
    pairQubitProjectiveSeedWeightedReturnExcisedGrowingReplicaBudget_le_uniformRate
      (by omega) hrho hscale U w hw hr hkappa
  have hjoint : pairQubitWeakTwoLocalGrowthFailureBudget L +
      pairQubitProjectiveSeedWeightedReturnExcisedGrowingReplicaBudget
        L rho scale U w r kappa < 1 :=
    (add_le_add le_rfl hcarrier).trans_lt hselect
  obtain ⟨x, hx, hnear, hmax⟩ :=
    exists_pairQubitProjectiveSeedWeightedReturnExcisedGrowingReplica_sameDraw
      (by omega) hp hrho hseed hscale U w hw r delta hkappa hjoint
  let P := twoLocalPauliGaussianHermitianPencil (L * 2)
  let Hfin := P.affineReindexedHamiltonian
    (pairQubitProjectivePauliSeed L p) (scale • x)
  have hHfin : Hfin.IsHermitian := by
    exact P.affineReindexedHamiltonian_isHermitian
      (pairQubitProjectivePauliSeed_isHermitian L p) (scale • x)
  let energy := hHfin.eigenvalues
  let target := fun c => GaloisForLFunctions.RHTower.choiVector
    (hermitianSpectralEndpoint hHfin (Ufin c) :
      Matrix (Fin (Fintype.card (FiniteQubitConfiguration (Fin (L * 2)))))
        (Fin (Fintype.card (FiniteQubitConfiguration (Fin (L * 2))))) ℂ)
  have henergy : energy =
      pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x := by
    rfl
  have hendpoint (c : C) : hermitianSpectralEndpoint hHfin (Ufin c) =
      pairQubitProjectiveSeedWeakTwoLocalSpectralEndpoint L p scale x (U c) := by
    rfl
  have hmax' : MaximallyProjectiveEnergy energy := by
    rw [henergy]
    exact hmax
  refine ⟨x, hx, hmax, ?_⟩
  have htarget : ∀ c, ‖target c‖ = 1 := by
    intro c
    exact GaloisForLFunctions.RHTower.norm_choiVector_eq_one Fintype.card_pos
      (Unitary.coe_star_mul_self (hermitianSpectralEndpoint hHfin (Ufin c)))
  have hresFamily :
      (fun j => (staticChoiAnchorResidual hHfin.eigenvalues 0
        (target j)).ofLp) =
      (fun j => (staticChoiTracelessResidual energy (target j)).ofLp) := by
    funext j
    rw [staticChoiAnchorResidual_zero_eq_tracelessResidual]
  have hdesign : ∀ (psi :
      (Fin (Fintype.card (FiniteQubitConfiguration (Fin (L * 2)))) ×
        Fin (Fintype.card (FiniteQubitConfiguration (Fin (L * 2))))) → ℂ)
      (c : C),
      finitePureStateFidelity psi
          (staticChoiTracelessResidual energy (target c)).ofLp ^ r ≤
        (Module.finrank ℂ (replicaTargetSpan r (fun j =>
          (staticChoiTracelessResidual energy (target j)).ofLp)) : ℝ) *
          ∑ j, w j * finitePureStateFidelity psi
            (staticChoiTracelessResidual energy (target j)).ofLp ^ r := by
    intro psi c
    have hcore := hdesignAll Hfin hHfin psi c
    change finitePureStateFidelity psi
        (staticChoiAnchorResidual hHfin.eigenvalues 0 (target c)).ofLp ^ r ≤
      (Module.finrank ℂ (replicaTargetSpan r (fun j =>
        (staticChoiAnchorResidual hHfin.eigenvalues 0 (target j)).ofLp)) : ℝ) *
        ∑ j, w j * finitePureStateFidelity psi
          (staticChoiAnchorResidual hHfin.eigenvalues 0 (target j)).ofLp ^ r at hcore
    rw [hresFamily] at hcore
    simpa [energy, staticChoiAnchorResidual_zero_eq_tracelessResidual] using hcore
  have hspeed : staticChoiSpeed energy ≤
      pairQubitProjectiveStaticChoiSpeedCeiling L rho scale := by
    rw [henergy]
    exact pairQubitProjective_staticChoiSpeed_le_ceiling (by omega) hseed hx
  have hspeedOne : 1 ≤ staticChoiSpeed energy := by
    unfold staticChoiSpeed
    have hsum : 0 ≤ ∑ i, |energy i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  have hmeshActual :
      (thetaN - thetaW) / staticChoiSpeed energy ≤ returnRadius := by
    calc
      (thetaN - thetaW) / staticChoiSpeed energy ≤ thetaN - thetaW := by
        exact div_le_self (sub_nonneg.mpr hgap.le) hspeedOne
      _ ≤ returnRadius := hmeshReturn
  have hguardActual : guard ≤ returnRadius +
      (thetaN - thetaW) / staticChoiSpeed energy := by
    have hmeshNonneg : 0 ≤
        (thetaN - thetaW) / staticChoiSpeed energy :=
      div_nonneg (sub_nonneg.mpr hgap.le) (staticChoiSpeed_pos energy).le
    exact hguardStart.trans (le_add_of_nonneg_right hmeshNonneg)
  have hnear' :
      ∑ c, w c * directStaticChoiTargetNearActionMass
        (staticChoiTracelessResidual energy (target c)) energy r delta < kappa := by
    rw [henergy]
    simp_rw [show ∀ c, target c =
        GaloisForLFunctions.RHTower.choiVector
          (pairQubitProjectiveSeedWeakTwoLocalSpectralEndpoint
            L p scale x (U c) : Matrix
              (Fin (Fintype.card (FiniteQubitConfiguration (Fin (L * 2)))))
              (Fin (Fintype.card (FiniteQubitConfiguration (Fin (L * 2))))) ℂ) by
      intro c
      exact congrArg GaloisForLFunctions.RHTower.choiVector (congrArg Subtype.val (hendpoint c))]
    simpa [pairQubitProjectiveSeedWeightedReturnExcisedGrowingReplicaNearAction,
      staticChoiAnchorResidual_zero_eq_tracelessResidual] using hnear
  have hrank : Module.finrank ℂ (replicaTargetSpan r (fun c =>
      (staticChoiTracelessResidual energy (target c)).ofLp)) =
      Module.finrank ℂ (replicaTargetSpan r
        (physicalUnitaryChoiResidualTarget Ufin)) := by
    have hfamily := unitaryTransportTarget_physicalUnitaryChoiResidualTarget
      (Fintype.card_pos : 0 < Fintype.card
        (FiniteQubitConfiguration (Fin (L * 2)))) hHfin Ufin
    have htransport := finrank_replicaTargetSpan_unitaryTransportTarget
      r (pureConjugationUnitary (star hHfin.eigenvectorUnitary))
        (physicalUnitaryChoiResidualTarget Ufin)
    rw [hfamily] at htransport
    change Module.finrank ℂ (replicaTargetSpan r (fun c =>
        (staticChoiAnchorResidual hHfin.eigenvalues 0 (target c)).ofLp)) =
      Module.finrank ℂ
        (replicaTargetSpan r (physicalUnitaryChoiResidualTarget Ufin)) at htransport
    rw [hresFamily] at htransport
    exact htransport
  have hrankPos : 0 < (Module.finrank ℂ (replicaTargetSpan r (fun c =>
      (staticChoiTracelessResidual energy (target c)).ofLp)) : ℝ) := by
    rw [hrank]
    exact Nat.cast_pos.mpr hpos
  have hbudget :
      (Module.finrank ℂ (replicaTargetSpan r (fun c =>
          (staticChoiTracelessResidual energy (target c)).ofLp)) : ℝ) *
        ((r.factorial : ℝ) *
            (Fintype.card (FiniteQubitConfiguration (Fin (L * 2))) : ℝ)⁻¹ ^ r +
          ∑ c, w c * directStaticChoiTargetNearActionMass
            (staticChoiTracelessResidual energy (target c)) energy r delta +
          Real.exp (-(((2 * Real.pi * (L : ℝ) ^ (3 : ℕ) - guard) * delta) ^ (2 : ℕ)) / 2)) <
        gaussianFloorTwo *
          (((thetaN - thetaW) / staticChoiSpeed energy) /
            (2 * (2 * Real.pi * (L : ℝ) ^ (3 : ℕ) - guard))) *
              (thetaW ^ (2 : ℕ)) ^ r := by
    rw [hrank]
    have hinside :
        (r.factorial : ℝ) *
              (Fintype.card (FiniteQubitConfiguration (Fin (L * 2))) : ℝ)⁻¹ ^ r +
            ∑ c, w c * directStaticChoiTargetNearActionMass
              (staticChoiTracelessResidual energy (target c)) energy r delta +
            Real.exp (-(((2 * Real.pi * (L : ℝ) ^ (3 : ℕ) - guard) * delta) ^ (2 : ℕ)) / 2) <
          (r.factorial : ℝ) *
              (Fintype.card (FiniteQubitConfiguration (Fin (L * 2))) : ℝ)⁻¹ ^ r +
            kappa +
            Real.exp (-(((2 * Real.pi * (L : ℝ) ^ (3 : ℕ) - guard) * delta) ^ (2 : ℕ)) / 2) := by
      linarith
    have hrankPhysicalPos : 0 <
        (Module.finrank ℂ (replicaTargetSpan r
          (physicalUnitaryChoiResidualTarget Ufin)) : ℝ) :=
      Nat.cast_pos.mpr hpos
    have hmul := mul_lt_mul_of_pos_left hinside hrankPhysicalPos
    have hfixed := hmul.trans (by simpa [Ufin] using hmoment)
    have hceilingPos : 0 < pairQubitProjectiveStaticChoiSpeedCeiling L rho scale :=
      (staticChoiSpeed_pos energy).trans_le hspeed
    have hmeshLower :
        (thetaN - thetaW) /
            pairQubitProjectiveStaticChoiSpeedCeiling L rho scale ≤
          (thetaN - thetaW) / staticChoiSpeed energy := by
      exact div_le_div_of_nonneg_left (sub_nonneg.mpr hgap.le)
        (staticChoiSpeed_pos energy) hspeed
    have hright :
        gaussianFloorTwo *
            (((thetaN - thetaW) /
                pairQubitProjectiveStaticChoiSpeedCeiling L rho scale) /
              (2 * (2 * Real.pi * (L : ℝ) ^ (3 : ℕ) - guard))) *
                (thetaW ^ (2 : ℕ)) ^ r ≤
          gaussianFloorTwo *
            (((thetaN - thetaW) / staticChoiSpeed energy) /
              (2 * (2 * Real.pi * (L : ℝ) ^ (3 : ℕ) - guard))) *
                (thetaW ^ (2 : ℕ)) ^ r := by
      have hgf : 0 ≤ gaussianFloorTwo := gaussianFloorTwo_pos.le
      gcongr
    exact hfixed.trans_le hright
  have hscalar : ∀ t ∈ Icc
      (returnRadius + (thetaN - thetaW) / staticChoiSpeed energy)
      (2 * Real.pi * (L : ℝ) ^ (3 : ℕ) - guard),
      ‖inner ℂ (staticSpectralChoiVector
          (Fintype.card (FiniteQubitConfiguration (Fin (L * 2)))) t energy)
        (staticSpectralChoiVector
          (Fintype.card (FiniteQubitConfiguration (Fin (L * 2)))) 0 energy)‖ < eta := by
    intro t ht
    rw [henergy]
    exact pairQubitProjective_spectralChoiScalar_cubic_lt
        hL hseed hguard hscalarBudget hx
          ⟨hguardActual.trans ht.1, ht.2⟩
  have hno :=
    no_forward_staticChoiTargetCapture_of_scalarReturn_and_residualDesignWeightedCrowding_lt
      (Fintype.card_pos : 0 < Fintype.card
        (FiniteQubitConfiguration (Fin (L * 2)))) hmax' target htarget
      hTpos hreturnPos hthetaW hgap hdelta
      hmeshActual hreturnT hscalar w hw hdesign hbudget
  rw [henergy] at hno
  simp_rw [show ∀ c, target c =
      GaloisForLFunctions.RHTower.choiVector
        (pairQubitProjectiveSeedWeakTwoLocalSpectralEndpoint
          L p scale x (U c) : Matrix
            (Fin (Fintype.card (FiniteQubitConfiguration (Fin (L * 2)))))
            (Fin (Fintype.card (FiniteQubitConfiguration (Fin (L * 2))))) ℂ) by
    intro c
    exact congrArg GaloisForLFunctions.RHTower.choiVector (congrArg Subtype.val (hendpoint c))] at hno
  exact hno

/-- A fixed nonidentity Pauli word, transported to the physical pair-qubit register. -/
def pairQubitCanonicalTracelessEndpoint (L : ℕ) :
    Matrix.unitaryGroup (Config (PairQubit L)) ℂ :=
  unitaryGroupReindex (pairQubitPathConfigurationEquiv L).symm
    ⟨finitePauliMatrix (fun _ : Fin (L * 2) => some 0),
      finitePauliMatrix_mem_unitary _⟩

/-- The canonical endpoint remains traceless after both coordinate changes used by the pencil. -/
theorem pairQubitCanonicalTracelessEndpoint_finite_trace_zero
    {L : ℕ} (hL : 0 < L) :
    Matrix.trace
      (finiteGaussianHermitianPencilReindexedEndpoint
        (pairQubitPathUnitaryReindex L
          (pairQubitCanonicalTracelessEndpoint L)) :
        Matrix (Fin (Fintype.card (FiniteQubitConfiguration (Fin (L * 2)))))
          (Fin (Fintype.card (FiniteQubitConfiguration (Fin (L * 2))))) ℂ) = 0 := by
  let V : Matrix.unitaryGroup (FiniteQubitConfiguration (Fin (L * 2))) ℂ :=
    ⟨finitePauliMatrix (fun _ : Fin (L * 2) => some 0),
      finitePauliMatrix_mem_unitary _⟩
  have hcancel : pairQubitPathUnitaryReindex L
      (pairQubitCanonicalTracelessEndpoint L) = V := by
    exact unitaryGroupReindex_apply_symm (pairQubitPathConfigurationEquiv L) V
  rw [hcancel]
  change Matrix.trace
      (Matrix.reindexAlgEquiv ℂ ℂ
        (Fintype.equivFin (FiniteQubitConfiguration (Fin (L * 2))))
        (finitePauliMatrix (fun _ : Fin (L * 2) => some 0))) = 0
  rw [trace_reindexAlgEquiv]
  apply finitePauliMatrix_trace_eq_zero_of_ne_identity
  intro h
  have hcard : 0 < L * 2 := Nat.mul_pos hL (by omega)
  have hc := congrFun h (⟨0, hcard⟩ : Fin (L * 2))
  simp at hc

/-- Adjoin one canonical traceless endpoint to an arbitrary supplied family. -/
def pairQubitRankAugmentedEndpoint
    {L : ℕ} {C : Type*}
    (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ) :
    Sum C Unit → Matrix.unitaryGroup (Config (PairQubit L)) ℂ :=
  Sum.elim U (fun _ => pairQubitCanonicalTracelessEndpoint L)

/-- The augmented residual dictionary has positive occupied replica rank at every order. -/
theorem pairQubitRankAugmentedEndpoint_residual_finrank_pos
    {L : ℕ} (hL : 0 < L) {C : Type*}
    (r : ℕ) (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ) :
    0 < Module.finrank ℂ (replicaTargetSpan r
      (physicalUnitaryChoiResidualTarget (fun c =>
        finiteGaussianHermitianPencilReindexedEndpoint
          (pairQubitPathUnitaryReindex L
            (pairQubitRankAugmentedEndpoint U c))))) := by
  apply physicalUnitaryChoiResidualTarget_finrank_pos_of_exists_trace_zero
    (Fintype.card_pos : 0 < Fintype.card
      (FiniteQubitConfiguration (Fin (L * 2)))) r _ (Sum.inr ())
  exact pairQubitCanonicalTracelessEndpoint_finite_trace_zero hL

end

end RHTower
