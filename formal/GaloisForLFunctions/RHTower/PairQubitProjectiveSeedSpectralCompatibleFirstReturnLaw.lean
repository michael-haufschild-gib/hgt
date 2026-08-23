import GaloisForLFunctions.RHTower.PairQubitProjectiveSeedWeakTwoLocalSameDrawLaw
import GaloisForLFunctions.RHTower.WeightedAffineTwoLocalPauliOscillationSpectralActionLaw
import GaloisForLFunctions.RHTower.UnitaryReplicaOptimalDesignTransportLaw

open scoped BigOperators Matrix ComplexConjugate Matrix.Norms.L2Operator ENNReal NNReal
open Matrix Set MeasureTheory ProbabilityTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Physical circuit endpoint after the fixed, draw-independent matrix-index
relabeling used by spectral coordinates. -/
abbrev pairQubitSpectralCompatiblePhysicalEndpoint
    {L : ℕ} {C : Type*}
    (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ) (c : C) :=
  finiteGaussianHermitianPencilReindexedEndpoint
    (pairQubitPathUnitaryReindex L (U c))

/-- Canonical pre-draw weights selected after fixed index relabeling but
before the Hamiltonian and its eigenbasis are known. -/
noncomputable def pairQubitSpectralCompatibleOptimalDesignWeight
    {L : ℕ} {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ) (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ) : C → ℝ :=
  finiteUnitaryChoiOptimalDesignWeight r
    (pairQubitSpectralCompatiblePhysicalEndpoint U)

theorem pairQubitSpectralCompatibleOptimalDesignWeight_mem_stdSimplex
    {L : ℕ} {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ) (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ) :
    pairQubitSpectralCompatibleOptimalDesignWeight r U ∈ stdSimplex ℝ C :=
  finiteUnitaryChoiOptimalDesignWeight_mem_stdSimplex r
    (pairQubitSpectralCompatiblePhysicalEndpoint U)

/-- Determinant-optimal Choi weights chosen in a fixed physical basis retain
their exact leverage inequality in every Hermitian eigenbasis. -/
theorem finiteUnitaryChoiOptimalDesignWeight_pointwise_hermitianSpectralEndpoint
    {d : ℕ} [Nonempty (Fin d)]
    {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    {H : Matrix (Fin d) (Fin d) ℂ} (hH : H.IsHermitian)
    (r : ℕ) (U : C → Matrix.unitaryGroup (Fin d) ℂ)
    (ψ : (Fin d × Fin d) → ℂ) (c : C) :
    finitePureStateFidelity ψ
        (GaloisForLFunctions.RHTower.choiVector
          (hermitianSpectralEndpoint hH (U c) :
            Matrix (Fin d) (Fin d) ℂ)).ofLp ^ r ≤
      (Module.finrank ℂ
        (replicaTargetSpan r (fun j =>
          (GaloisForLFunctions.RHTower.choiVector
            (hermitianSpectralEndpoint hH (U j) :
              Matrix (Fin d) (Fin d) ℂ)).ofLp)) : ℝ) *
        ∑ j, finiteUnitaryChoiOptimalDesignWeight r U j *
          finitePureStateFidelity ψ
            (GaloisForLFunctions.RHTower.choiVector
              (hermitianSpectralEndpoint hH (U j) :
                Matrix (Fin d) (Fin d) ℂ)).ofLp ^ r := by
  let Kstar : Matrix.unitaryGroup (Fin d) ℂ := star hH.eigenvectorUnitary
  let V := pureConjugationUnitary Kstar
  have htarget : unitaryTransportTarget V (finiteUnitaryChoiTarget U) =
      fun c =>
        (GaloisForLFunctions.RHTower.choiVector
          (hermitianSpectralEndpoint hH (U c) :
            Matrix (Fin d) (Fin d) ℂ)).ofLp := by
    funext j
    change pureConjugationChannel (Kstar : Matrix (Fin d) (Fin d) ℂ) *ᵥ
        (GaloisForLFunctions.RHTower.choiVector
          (U j : Matrix (Fin d) (Fin d) ℂ)).ofLp = _
    rw [pureConjugationChannel_mulVec_choiVector]
    congr 1
    apply congrArg GaloisForLFunctions.RHTower.choiVector
    change star (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ) *
        (U j : Matrix (Fin d) (Fin d) ℂ) *
        star (star (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℂ)) = _
    rw [star_star]
    rfl
  have h := replicaTargetOptimalDesignWeight_pointwise_unitaryTransport
    r (finiteUnitaryChoiTarget U) (finiteUnitaryChoiTarget_normalized U)
      V ψ c
  have hrank := congrArg
    (fun target : C → (Fin d × Fin d) → ℂ =>
      Module.finrank ℂ (replicaTargetSpan r target)) htarget
  rw [hrank] at h
  simpa only [htarget, finiteUnitaryChoiOptimalDesignWeight] using h

def pairQubitSpectralCompatibleOscillationNearActionGapEvent
    {L : ℕ}
    (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ)
    (scale : ℝ)
    {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ) (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    (δ κ : ℝ) : Set (TwoLocalPauliCoefficientSpace (L * 2)) :=
  {x |
    (∑ c, pairQubitSpectralCompatibleOptimalDesignWeight r U c *
      staticChoiOscillationAdaptiveReplicaBase
        (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x)
        ((Fintype.card
            (FiniteQubitConfiguration (Fin (L * 2))) : ℝ)⁻¹ *
          (scale ^ 2 *
            (twoLocalPauliGaussianHermitianPencil (L * 2)).commutatorActivation
              (pairQubitPathUnitaryReindex L (U c)))) ^ r) + κ ≤
    ∑ c, pairQubitSpectralCompatibleOptimalDesignWeight r U c *
      directStaticChoiTargetNearActionMass
        (GaloisForLFunctions.RHTower.choiVector
          (pairQubitProjectiveSeedWeakTwoLocalSpectralEndpoint
              L p scale x (U c) :
            Matrix (Fin (Fintype.card
              (FiniteQubitConfiguration (Fin (L * 2)))))
              (Fin (Fintype.card
                (FiniteQubitConfiguration (Fin (L * 2))))) ℂ))
        (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x) r δ}

def pairQubitSpectralCompatibleCarrierBudget
    {L : ℕ} {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ) (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    (κ : ℝ) : ℝ :=
  (∑ c, pairQubitSpectralCompatibleOptimalDesignWeight r U c *
    Real.exp (-(gaussianIntervalActivationMass ^ 2 / 2) *
      (((6 * (L * 2) - 4 : ℕ) : ℝ) *
        pairQubitUnitaryProjectiveTraceDeficit (U c)))) / κ

theorem stdGaussian_measure_pairQubitSpectralCompatibleOscillationNearAction_gap_le
    {L : ℕ} {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    {scale : ℝ} (hscale : scale ≠ 0)
    {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ) (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    (δ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace (L * 2))).real
        (pairQubitSpectralCompatibleOscillationNearActionGapEvent
          p scale r U δ κ) ≤
      pairQubitSpectralCompatibleCarrierBudget r U κ := by
  unfold pairQubitSpectralCompatibleOscillationNearActionGapEvent
    pairQubitSpectralCompatibleCarrierBudget
    pairQubitUnitaryProjectiveTraceDeficit
  exact
    stdGaussian_measure_weightedScaledAffineTwoLocalOscillationNearAction_gap_le_traceDeficit
      (pairQubitProjectivePauliSeed_isHermitian L p) hscale
      (fun c => pairQubitPathUnitaryReindex L (U c))
      (pairQubitSpectralCompatibleOptimalDesignWeight r U)
      (pairQubitSpectralCompatibleOptimalDesignWeight_mem_stdSimplex r U)
      r δ hκ

theorem pairQubitSpectralCompatibleCarrierBudget_le_of_projectiveDeficit
    {L : ℕ} {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ) (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    {η κ : ℝ} (hη : ∀ c, η ≤ pairQubitUnitaryProjectiveTraceDeficit (U c))
    (hκ : 0 < κ) :
    pairQubitSpectralCompatibleCarrierBudget r U κ ≤
      Real.exp (-(gaussianIntervalActivationMass ^ 2 / 2) *
        (((6 * (L * 2) - 4 : ℕ) : ℝ) * η)) / κ := by
  unfold pairQubitSpectralCompatibleCarrierBudget
  apply div_le_div_of_nonneg_right _ hκ.le
  let w := pairQubitSpectralCompatibleOptimalDesignWeight r U
  have hw : w ∈ stdSimplex ℝ C :=
    pairQubitSpectralCompatibleOptimalDesignWeight_mem_stdSimplex r U
  calc
    (∑ c, w c * Real.exp (-(gaussianIntervalActivationMass ^ 2 / 2) *
        (((6 * (L * 2) - 4 : ℕ) : ℝ) *
          pairQubitUnitaryProjectiveTraceDeficit (U c)))) ≤
      ∑ c, w c * Real.exp (-(gaussianIntervalActivationMass ^ 2 / 2) *
        (((6 * (L * 2) - 4 : ℕ) : ℝ) * η)) := by
      apply Finset.sum_le_sum
      intro c _
      apply mul_le_mul_of_nonneg_left _ (hw.1 c)
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonpos_left
      · exact mul_le_mul_of_nonneg_left (hη c) (by positivity)
      · exact neg_nonpos.mpr (by positivity)
    _ = Real.exp (-(gaussianIntervalActivationMass ^ 2 / 2) *
        (((6 * (L * 2) - 4 : ℕ) : ℝ) * η)) := by
      rw [← Finset.sum_mul, hw.2, one_mul]

/-- One ordinary draw simultaneously lies in the robust growth box, avoids
the spectral-compatible complete weighted carrier, and has maximally
projective spectrum. -/
theorem exists_pairQubitProjectiveSeedWeakTwoLocal_sameDraw_spectralCompatibleCarrier_maximal
    {L : ℕ} {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    (hp : p ∈ nearestNeighborPathLocalMaximalSet L)
    {scale : ℝ} (hscale : scale ≠ 0)
    {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ) (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    (δ : ℝ) {κ : ℝ} (hκ : 0 < κ)
    (hjoint : pairQubitWeakTwoLocalGrowthFailureBudget L +
        pairQubitSpectralCompatibleCarrierBudget r U κ < 1) :
    ∃ x : TwoLocalPauliCoefficientSpace (L * 2),
      x ∈ weakTwoLocalPauliCertifiedGrowthSet L ∧
      x ∉ pairQubitSpectralCompatibleOscillationNearActionGapEvent
        p scale r U δ κ ∧
      MaximallyProjectiveEnergy
        (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x) := by
  let μ := stdGaussian (TwoLocalPauliCoefficientSpace (L * 2))
  let G := weakTwoLocalPauliCertifiedGrowthSet L
  let S := pairQubitSpectralCompatibleOscillationNearActionGapEvent
    p scale r U δ κ
  let M : Set (TwoLocalPauliCoefficientSpace (L * 2)) :=
    {x | MaximallyProjectiveEnergy
      (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x)}
  have hGc : μ.real Gᶜ ≤ pairQubitWeakTwoLocalGrowthFailureBudget L :=
    stdGaussian_weakTwoLocalPauliCertifiedGrowthSet_compl_le L
  have hS : μ.real S ≤ pairQubitSpectralCompatibleCarrierBudget r U κ :=
    stdGaussian_measure_pairQubitSpectralCompatibleOscillationNearAction_gap_le
      hscale r U δ hκ
  have hae : ∀ᵐ x ∂μ, x ∈ M :=
    pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy_maximallyProjective_ae hp scale
  have hMnull : μ Mᶜ = 0 := by
    rw [ae_iff] at hae
    change μ {x | x ∉ M} = 0
    exact hae
  have hMreal : μ.real Mᶜ = 0 := by
    simp [MeasureTheory.measureReal_def, hMnull]
  by_contra hnone
  have hcover : Set.univ ⊆ Gᶜ ∪ S ∪ Mᶜ := by
    intro x _
    by_cases hxG : x ∈ G
    · by_cases hxS : x ∈ S
      · exact Or.inl (Or.inr hxS)
      · exact Or.inr (by
          intro hxM
          exact hnone ⟨x, hxG, hxS, hxM⟩)
    · exact Or.inl (Or.inl hxG)
  have hone : 1 ≤ μ.real Gᶜ + μ.real S + μ.real Mᶜ := by
    calc
      1 = μ.real Set.univ := by simp [μ]
      _ ≤ μ.real (Gᶜ ∪ S ∪ Mᶜ) := measureReal_mono hcover
      _ ≤ μ.real (Gᶜ ∪ S) + μ.real Mᶜ := measureReal_union_le _ _
      _ ≤ (μ.real Gᶜ + μ.real S) + μ.real Mᶜ := by
        gcongr
        exact measureReal_union_le _ _
  rw [hMreal, add_zero] at hone
  linarith

abbrev pairQubitProjectiveSeedWeakTwoLocalSpectralChoiTarget
    {L : ℕ} (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ)
    (scale : ℝ) (x : TwoLocalPauliCoefficientSpace (L * 2))
    {C : Type*} (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    (c : C) : EuclideanSpace ℂ
      (Fin (Fintype.card (FiniteQubitConfiguration (Fin (L * 2)))) ×
        Fin (Fintype.card (FiniteQubitConfiguration (Fin (L * 2))))) :=
  GaloisForLFunctions.RHTower.choiVector
    (pairQubitProjectiveSeedWeakTwoLocalSpectralEndpoint
      L p scale x (U c) :
        Matrix (Fin (Fintype.card (FiniteQubitConfiguration (Fin (L * 2)))))
          (Fin (Fintype.card (FiniteQubitConfiguration (Fin (L * 2))))) ℂ)

/-- Outside the spectral-compatible quenched gap event, the stronger
oscillation remainder compiles directly into first exclusion from the entire
finite circuit image. -/
theorem no_forward_pairQubitProjectiveSeedWeakTwoLocalCircuitReturn_of_not_spectralCompatibleGap
    {L : ℕ} {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    {scale : ℝ} {x : TwoLocalPauliCoefficientSpace (L * 2)}
    {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    {r : ℕ} (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    {δ κ : ℝ}
    (hmax : MaximallyProjectiveEnergy
      (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x))
    (hxgap : x ∉ pairQubitSpectralCompatibleOscillationNearActionGapEvent
      p scale r U δ κ)
    {T epsn epsw : ℝ}
    (hTpos : 0 < T) (hδ : 0 < δ)
    (hepsn : 0 ≤ epsn) (hgap : epsn < epsw)
    (hepswOne : epsw < 1)
    (hT : epsw /
        staticChoiSpeed
          (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x) ≤ T)
    (hbudget :
      (Module.finrank ℂ
          (replicaTargetSpan r (fun c =>
            (pairQubitProjectiveSeedWeakTwoLocalSpectralChoiTarget
              p scale x U c).ofLp)) : ℝ) *
        ((r.factorial : ℝ) *
            (Fintype.card
              (FiniteQubitConfiguration (Fin (L * 2))) : ℝ)⁻¹ ^ r +
          (∑ c, pairQubitSpectralCompatibleOptimalDesignWeight r U c *
            staticChoiOscillationAdaptiveReplicaBase
              (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x)
              ((Fintype.card
                  (FiniteQubitConfiguration (Fin (L * 2))) : ℝ)⁻¹ *
                (scale ^ 2 *
                  (twoLocalPauliGaussianHermitianPencil
                    (L * 2)).commutatorActivation
                      (pairQubitPathUnitaryReindex L (U c)))) ^ r) +
          κ + Real.exp (-((T * δ) ^ 2) / 2)) <
        gaussianFloorTwo *
          ((epsw - epsn) /
              staticChoiSpeed
                (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy
                  L p scale x) / (2 * T)) *
          (1 - epsw ^ 2) ^ r) :
    ¬ ∃ t ∈ Icc
        (epsw /
            staticChoiSpeed
              (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x) +
          (epsw - epsn) /
            staticChoiSpeed
              (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x)) T,
      ∃ c, pureStateTraceDistance
        (staticSpectralChoiVector
          (Fintype.card (FiniteQubitConfiguration (Fin (L * 2)))) t
          (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x))
        (pairQubitProjectiveSeedWeakTwoLocalSpectralChoiTarget
          p scale x U c) ≤ epsn := by
  let energy := pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x
  let target := pairQubitProjectiveSeedWeakTwoLocalSpectralChoiTarget
    p scale x U
  let w := pairQubitSpectralCompatibleOptimalDesignWeight r U
  have hw : w ∈ stdSimplex ℝ C :=
    pairQubitSpectralCompatibleOptimalDesignWeight_mem_stdSimplex r U
  have htarget : ∀ c, ‖target c‖ = 1 := by
    intro c
    exact GaloisForLFunctions.RHTower.norm_choiVector_eq_one
      Fintype.card_pos
      (Unitary.coe_star_mul_self
        (pairQubitProjectiveSeedWeakTwoLocalSpectralEndpoint
          L p scale x (U c)))
  have hdesign : ∀ (φ :
      (Fin (Fintype.card (FiniteQubitConfiguration (Fin (L * 2)))) ×
        Fin (Fintype.card (FiniteQubitConfiguration (Fin (L * 2))))) → ℂ)
      (c : C),
      finitePureStateFidelity φ (target c).ofLp ^ r ≤
        (Module.finrank ℂ
          (replicaTargetSpan r (fun j => (target j).ofLp)) : ℝ) *
          ∑ j, w j * finitePureStateFidelity φ (target j).ofLp ^ r := by
    intro φ c
    let P := twoLocalPauliGaussianHermitianPencil (L * 2)
    let hH := P.affineReindexedHamiltonian_isHermitian
      (pairQubitProjectivePauliSeed_isHermitian L p) (scale • x)
    let Ufin := pairQubitSpectralCompatiblePhysicalEndpoint U
    have hcore :=
      finiteUnitaryChoiOptimalDesignWeight_pointwise_hermitianSpectralEndpoint
        hH r Ufin φ c
    change finitePureStateFidelity φ
        (GaloisForLFunctions.RHTower.choiVector
          (hermitianSpectralEndpoint hH (Ufin c) :
            Matrix (Fin (Fintype.card
              (FiniteQubitConfiguration (Fin (L * 2)))))
              (Fin (Fintype.card
                (FiniteQubitConfiguration (Fin (L * 2))))) ℂ)).ofLp ^ r ≤
      (Module.finrank ℂ
        (replicaTargetSpan r (fun j =>
          (GaloisForLFunctions.RHTower.choiVector
            (hermitianSpectralEndpoint hH (Ufin j) :
              Matrix (Fin (Fintype.card
                (FiniteQubitConfiguration (Fin (L * 2)))))
                (Fin (Fintype.card
                  (FiniteQubitConfiguration (Fin (L * 2))))) ℂ)).ofLp)) : ℝ) *
        ∑ j, finiteUnitaryChoiOptimalDesignWeight r Ufin j *
          finitePureStateFidelity φ
            (GaloisForLFunctions.RHTower.choiVector
              (hermitianSpectralEndpoint hH (Ufin j) :
                Matrix (Fin (Fintype.card
                  (FiniteQubitConfiguration (Fin (L * 2)))))
                  (Fin (Fintype.card
                    (FiniteQubitConfiguration (Fin (L * 2))))) ℂ)).ofLp ^ r
    exact hcore
  have hnear :
      (∑ c, w c * directStaticChoiTargetNearActionMass
        (target c) energy r δ) <
        (∑ c, w c * staticChoiOscillationAdaptiveReplicaBase energy
          ((Fintype.card
              (FiniteQubitConfiguration (Fin (L * 2))) : ℝ)⁻¹ *
            (scale ^ 2 *
              (twoLocalPauliGaussianHermitianPencil
                (L * 2)).commutatorActivation
                  (pairQubitPathUnitaryReindex L (U c)))) ^ r) + κ := by
    exact lt_of_not_ge hxgap
  have hbudget' :
      (Module.finrank ℂ
          (replicaTargetSpan r (fun c => (target c).ofLp)) : ℝ) *
        ((r.factorial : ℝ) *
            (Fintype.card
              (FiniteQubitConfiguration (Fin (L * 2))) : ℝ)⁻¹ ^ r +
          ∑ c, w c * directStaticChoiTargetNearActionMass
            (target c) energy r δ +
          Real.exp (-((T * δ) ^ 2) / 2)) <
        gaussianFloorTwo *
          ((epsw - epsn) / staticChoiSpeed energy / (2 * T)) *
          (1 - epsw ^ 2) ^ r := by
    apply lt_of_le_of_lt _ hbudget
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    linarith
  exact no_forward_pureChoiCircuitReturn_of_optimalDesignWeightedCrowding
    Fintype.card_pos hmax target htarget hTpos hδ hepsn hgap hepswOne hT
      w hw hdesign hbudget'

end

end RHTower
