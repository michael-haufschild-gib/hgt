import GaloisForLFunctions.HTGeometry.ProjectiveSeedWeakTwoLocalGrowthLaw
import GaloisForLFunctions.RHTower.PairQubitWeakTwoLocalSpectralActionLaw

open scoped BigOperators Matrix ComplexConjugate Matrix.Norms.L2Operator ENNReal NNReal
open Matrix Set MeasureTheory ProbabilityTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
open GaloisForLFunctions.RHTower

noncomputable section

attribute [local instance] Classical.propDecidable

def pairQubitProjectivePauliSeed (L : ℕ)
    (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ) :
    Matrix (FiniteQubitConfiguration (Fin (L * 2)))
      (FiniteQubitConfiguration (Fin (L * 2))) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (pairQubitPathConfigurationEquiv L)
    (nearestNeighborPathLocalHamiltonian L p)

theorem pairQubitProjectivePauliSeed_isHermitian (L : ℕ)
    (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ) :
    (pairQubitProjectivePauliSeed L p).IsHermitian := by
  exact (Matrix.isHermitian_iff_isSelfAdjoint.mpr
    (nearestNeighborPathLocalHamiltonian_isSelfAdjoint L p)).reindex
      (pairQubitPathConfigurationEquiv L)

theorem pairQubitProjectivePauliSeed_maximallyProjective
    {L : ℕ} {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    (hp : p ∈ nearestNeighborPathLocalMaximalSet L) :
    MaximallyProjectiveEnergy
      (pairQubitProjectivePauliSeed_isHermitian L p).eigenvalues := by
  exact Matrix.IsHermitian.maximallyProjective_reindexAlgEquiv
    (pairQubitPathConfigurationEquiv L)
    (nearestNeighborPathLocalHamiltonian_isHermitian L p)
    (maximallyProjectiveEnergy_nearestNeighborPathLocalHamiltonian hp)

abbrev pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy
    (L : ℕ) (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ)
    (scale : ℝ) (x : TwoLocalPauliCoefficientSpace (L * 2)) :=
  (twoLocalPauliGaussianHermitianPencil (L * 2)).scaledAffineSpectralEnergy
    (pairQubitProjectivePauliSeed_isHermitian L p) scale x

abbrev pairQubitProjectiveSeedWeakTwoLocalSpectralEndpoint
    (L : ℕ) (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ)
    (scale : ℝ) (x : TwoLocalPauliCoefficientSpace (L * 2))
    (U : Matrix.unitaryGroup (Config (PairQubit L)) ℂ) :=
  (twoLocalPauliGaussianHermitianPencil (L * 2)).scaledAffineSpectralEndpoint
    (pairQubitProjectivePauliSeed_isHermitian L p) scale x
      (pairQubitPathUnitaryReindex L U)

theorem pairQubitProjectiveSeed_reindexedHamiltonian_eq_physical
    (L : ℕ) (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ)
    (scale : ℝ) (x : TwoLocalPauliCoefficientSpace (L * 2)) :
    pairQubitProjectivePauliSeed L p +
        (scale : ℂ) • realActivePauliHamiltonian x =
      Matrix.reindexAlgEquiv ℂ ℂ (pairQubitPathConfigurationEquiv L)
        (projectiveSeedWeakTwoLocalHamiltonian L p scale x) := by
  exact (reindex_projectiveSeedWeakTwoLocalHamiltonian L p scale x).symm

theorem pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy_maximallyProjective_ae
    {L : ℕ} {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    (hp : p ∈ nearestNeighborPathLocalMaximalSet L) (scale : ℝ) :
    ∀ᵐ x ∂(stdGaussian (TwoLocalPauliCoefficientSpace (L * 2))),
      MaximallyProjectiveEnergy
        (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x) := by
  have hbase := pairQubitProjectivePauliSeed_maximallyProjective hp
  have hae := maximallyProjective_scaledAffine_activePauli_ae
    (pairQubitProjectivePauliSeed L p)
    (pairQubitProjectivePauliSeed_isHermitian L p) hbase scale
  filter_upwards [hae] with x hx
  let hsum := (pairQubitProjectivePauliSeed_isHermitian L p).add
    (Matrix.isHermitian_iff_isSelfAdjoint.mpr
      (isSelfAdjoint_realActivePauliHamiltonian (scale • x)))
  have hr := Matrix.IsHermitian.maximallyProjective_reindexAlgEquiv
    (Fintype.equivFin (FiniteQubitConfiguration (Fin (L * 2)))) hsum hx
  simpa [pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy,
    FiniteGaussianHermitianPencil.scaledAffineSpectralEnergy,
    FiniteGaussianHermitianPencil.affineSpectralEnergy,
    FiniteGaussianHermitianPencil.affineReindexedHamiltonian,
    twoLocalPauliGaussianHermitianPencil_hamiltonian,
    realActivePauliHamiltonian_smul] using hr

def pairQubitProjectiveSeedWeakTwoLocalNearActionGapEvent
    {L : ℕ}
    (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ)
    (scale : ℝ)
    {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ) (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    (δ κ : ℝ) : Set (TwoLocalPauliCoefficientSpace (L * 2)) :=
  {x |
    (∑ c, finiteUnitaryChoiOptimalDesignWeight r
          (fun c => pairQubitPathUnitaryReindex L (U c)) c *
      staticChoiAdaptiveReplicaBase
        (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x)
        ((Fintype.card
            (FiniteQubitConfiguration (Fin (L * 2))) : ℝ)⁻¹ *
          (scale ^ 2 *
            (twoLocalPauliGaussianHermitianPencil (L * 2)).commutatorActivation
              (pairQubitPathUnitaryReindex L (U c)))) ^ r) + κ ≤
    ∑ c, finiteUnitaryChoiOptimalDesignWeight r
          (fun c => pairQubitPathUnitaryReindex L (U c)) c *
      directStaticChoiTargetNearActionMass
        (choiVector
          (pairQubitProjectiveSeedWeakTwoLocalSpectralEndpoint
              L p scale x (U c) :
            Matrix (Fin (Fintype.card
              (FiniteQubitConfiguration (Fin (L * 2)))))
              (Fin (Fintype.card
                (FiniteQubitConfiguration (Fin (L * 2))))) ℂ))
        (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x) r δ}

theorem stdGaussian_measure_pairQubitProjectiveSeedOptimalDesignScaledAffineTwoLocalNearAction_gap_le
    {L : ℕ} {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    {scale : ℝ} (hscale : scale ≠ 0)
    {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ) (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    (δ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace (L * 2))).real
        (pairQubitProjectiveSeedWeakTwoLocalNearActionGapEvent p scale r U δ κ) ≤
      pairQubitWeakTwoLocalCarrierBudget r U κ := by
  unfold pairQubitProjectiveSeedWeakTwoLocalNearActionGapEvent
    pairQubitWeakTwoLocalCarrierBudget pairQubitUnitaryProjectiveTraceDeficit
  exact stdGaussian_measure_optimalDesignScaledAffineTwoLocalNearAction_gap_le_traceDeficit
    (pairQubitProjectivePauliSeed_isHermitian L p) hscale r
      (fun c => pairQubitPathUnitaryReindex L (U c)) δ hκ

/-- A maximally projective local seed pays no extra probability cost: one
two-local draw simultaneously lies in the robust growth box, avoids the full
weighted carrier gap, and has maximally projective spectrum. -/
theorem exists_pairQubitProjectiveSeedWeakTwoLocal_sameDraw_carrier_maximal
    {L : ℕ} {p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ}
    (hp : p ∈ nearestNeighborPathLocalMaximalSet L)
    {scale : ℝ} (hscale : scale ≠ 0)
    {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ) (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    (δ : ℝ) {κ : ℝ} (hκ : 0 < κ)
    (hjoint : pairQubitWeakTwoLocalGrowthFailureBudget L +
        pairQubitWeakTwoLocalCarrierBudget r U κ < 1) :
    ∃ x : TwoLocalPauliCoefficientSpace (L * 2),
      x ∈ weakTwoLocalPauliCertifiedGrowthSet L ∧
      x ∉ pairQubitProjectiveSeedWeakTwoLocalNearActionGapEvent
        p scale r U δ κ ∧
      MaximallyProjectiveEnergy
        (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x) := by
  let μ := stdGaussian (TwoLocalPauliCoefficientSpace (L * 2))
  let G := weakTwoLocalPauliCertifiedGrowthSet L
  let S := pairQubitProjectiveSeedWeakTwoLocalNearActionGapEvent
    p scale r U δ κ
  let M : Set (TwoLocalPauliCoefficientSpace (L * 2)) :=
    {x | MaximallyProjectiveEnergy
      (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x)}
  have hGc : μ.real Gᶜ ≤ pairQubitWeakTwoLocalGrowthFailureBudget L := by
    exact stdGaussian_weakTwoLocalPauliCertifiedGrowthSet_compl_le L
  have hS : μ.real S ≤ pairQubitWeakTwoLocalCarrierBudget r U κ := by
    exact
      stdGaussian_measure_pairQubitProjectiveSeedOptimalDesignScaledAffineTwoLocalNearAction_gap_le
        hscale r U δ hκ
  have hae : ∀ᵐ x ∂μ, x ∈ M := by
    exact pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy_maximallyProjective_ae
      hp scale
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

/-- **Same-draw projective local growth--carrier law.**  One ordinary
time-independent two-local Hamiltonian simultaneously has a maximally
projective spectrum, a robust linear laboratory-time complexity ramp, and the
complete count-free weighted spectral-action carrier bound. -/
theorem exists_pairQubitProjectiveSeedWeakTwoLocal_sameDraw_growth_carrier_maximal
    {L : ℕ} (hL : 1 ≤ L)
    {ρ T ε scale : ℝ} (hρ : 0 < ρ) (hT : 0 ≤ T)
    (hε : 0 < ε) (hεmax : ε ≤ 1 / 200)
    (hscale : scale ≠ 0)
    (hbudget : T * (ρ * nearestNeighborPathLocalGeneratorMass L +
        |scale| * (18 * ((L * 2 : ℕ) : ℝ) ^ 3)) ≤ ε)
    {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ) (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    (δ : ℝ) {κ : ℝ} (hκ : 0 < κ)
    (hjoint : pairQubitWeakTwoLocalGrowthFailureBudget L +
        pairQubitWeakTwoLocalCarrierBudget r U κ < 1) :
    ∃ (p : Fin (nearestNeighborPathLocalParameterCount L) → ℝ)
        (x : TwoLocalPauliCoefficientSpace (L * 2)),
      p ∈ nearestNeighborPathLocalMaximalSet L ∧
      ‖nearestNeighborPathLocalHamiltonian L p -
          inverseSquareChainHamiltonian L‖ ≤
        ρ * nearestNeighborPathLocalGeneratorMass L ∧
      (∀ t : ℝ,
        2048 * Real.pi * ε ≤ t →
        t ≤ ε * L →
        t ≤ T →
        ((⌊t / (256 * Real.pi * ε)⌋₊ : ℕ) : ℕ∞) ≤
          operatorTwoGateComplexityTo L ε
            (unitaryEvolution
              (projectiveSeedWeakTwoLocalHamiltonian L p scale x) t)) ∧
      x ∉ pairQubitProjectiveSeedWeakTwoLocalNearActionGapEvent
        p scale r U δ κ ∧
      MaximallyProjectiveEnergy
        (pairQubitProjectiveSeedWeakTwoLocalSpectralEnergy L p scale x) := by
  obtain ⟨p, hp, hpclose⟩ :=
    exists_maximallyProjective_nearestNeighborSeed_close
      (lt_of_lt_of_le Nat.zero_lt_one hL) hρ
  obtain ⟨x, hxgrowth, hxcarrier, hxmax⟩ :=
    exists_pairQubitProjectiveSeedWeakTwoLocal_sameDraw_carrier_maximal
      hp hscale r U δ hκ hjoint
  refine ⟨p, x, hp, hpclose, ?_, hxcarrier, hxmax⟩
  exact projectiveSeedWeakTwoLocal_uniform_laboratory_growth
    hL hpclose hT hε hεmax hbudget hxgrowth

end

end RHTower
