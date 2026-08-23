import GaloisForLFunctions.HTGeometry.WeakTwoLocalPauliPerturbationGrowthLaw
import GaloisForLFunctions.RHTower.AffineTwoLocalPauliSpectralActionLaw

open scoped BigOperators Matrix ComplexConjugate Matrix.Norms.L2Operator
open Matrix Set MeasureTheory ProbabilityTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
open GaloisForLFunctions.RHTower

noncomputable section

attribute [local instance] Classical.propDecidable

def pairQubitInverseSquarePauliSeed (L : ℕ) :
    Matrix (FiniteQubitConfiguration (Fin (L * 2)))
      (FiniteQubitConfiguration (Fin (L * 2))) ℂ :=
  Matrix.reindexAlgEquiv ℂ ℂ (pairQubitPathConfigurationEquiv L)
    (inverseSquareChainHamiltonian L)

theorem pairQubitInverseSquarePauliSeed_isHermitian (L : ℕ) :
    (pairQubitInverseSquarePauliSeed L).IsHermitian := by
  exact (Matrix.isHermitian_iff_isSelfAdjoint.mpr
    (inverseSquareChainHamiltonian_isSelfAdjoint L)).reindex
      (pairQubitPathConfigurationEquiv L)

def pairQubitPathUnitaryReindex (L : ℕ)
    (U : Matrix.unitaryGroup (Config (PairQubit L)) ℂ) :
    Matrix.unitaryGroup (FiniteQubitConfiguration (Fin (L * 2))) ℂ :=
  unitaryGroupReindex (pairQubitPathConfigurationEquiv L) U

def pairQubitUnitaryProjectiveTraceDeficit {L : ℕ}
    (U : Matrix.unitaryGroup (Config (PairQubit L)) ℂ) : ℝ :=
  unitaryProjectiveTraceDeficit (pairQubitPathUnitaryReindex L U)

abbrev pairQubitWeakTwoLocalSpectralEnergy
    (L : ℕ) (scale : ℝ) (x : TwoLocalPauliCoefficientSpace (L * 2)) :=
  (twoLocalPauliGaussianHermitianPencil (L * 2)).scaledAffineSpectralEnergy
    (pairQubitInverseSquarePauliSeed_isHermitian L) scale x

abbrev pairQubitWeakTwoLocalSpectralEndpoint
    (L : ℕ) (scale : ℝ) (x : TwoLocalPauliCoefficientSpace (L * 2))
    (U : Matrix.unitaryGroup (Config (PairQubit L)) ℂ) :=
  (twoLocalPauliGaussianHermitianPencil (L * 2)).scaledAffineSpectralEndpoint
    (pairQubitInverseSquarePauliSeed_isHermitian L) scale x
      (pairQubitPathUnitaryReindex L U)

theorem pairQubitWeakTwoLocal_reindexedHamiltonian_eq_physical
    (L : ℕ) (scale : ℝ) (x : TwoLocalPauliCoefficientSpace (L * 2)) :
    pairQubitInverseSquarePauliSeed L +
        (scale : ℂ) • realActivePauliHamiltonian x =
      Matrix.reindexAlgEquiv ℂ ℂ (pairQubitPathConfigurationEquiv L)
        (weakTwoLocalPauliPerturbedInverseSquareHamiltonian L scale x) := by
  exact (reindex_weakTwoLocalPauliPerturbedInverseSquareHamiltonian L scale x).symm

def pairQubitWeakTwoLocalNearActionGapEvent
    {L : ℕ} (scale : ℝ)
    {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ) (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    (δ κ : ℝ) : Set (TwoLocalPauliCoefficientSpace (L * 2)) :=
  {x |
    (∑ c, finiteUnitaryChoiOptimalDesignWeight r
          (fun c => pairQubitPathUnitaryReindex L (U c)) c *
      staticChoiAdaptiveReplicaBase
        (pairQubitWeakTwoLocalSpectralEnergy L scale x)
        ((Fintype.card
            (FiniteQubitConfiguration (Fin (L * 2))) : ℝ)⁻¹ *
          (scale ^ 2 *
            (twoLocalPauliGaussianHermitianPencil (L * 2)).commutatorActivation
              (pairQubitPathUnitaryReindex L (U c)))) ^ r) + κ ≤
    ∑ c, finiteUnitaryChoiOptimalDesignWeight r
          (fun c => pairQubitPathUnitaryReindex L (U c)) c *
      directStaticChoiTargetNearActionMass
        (choiVector
          (pairQubitWeakTwoLocalSpectralEndpoint L scale x (U c) :
            Matrix (Fin (Fintype.card
              (FiniteQubitConfiguration (Fin (L * 2)))))
              (Fin (Fintype.card
                (FiniteQubitConfiguration (Fin (L * 2))))) ℂ))
        (pairQubitWeakTwoLocalSpectralEnergy L scale x) r δ}

def pairQubitWeakTwoLocalCarrierBudget
    {L : ℕ}
    {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ) (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    (κ : ℝ) : ℝ :=
  (∑ c, finiteUnitaryChoiOptimalDesignWeight r
      (fun c => pairQubitPathUnitaryReindex L (U c)) c *
    Real.exp (-(gaussianIntervalActivationMass ^ 2 / 2) *
      (((6 * (L * 2) - 4 : ℕ) : ℝ) *
        pairQubitUnitaryProjectiveTraceDeficit (U c)))) / κ

def pairQubitWeakTwoLocalGrowthFailureBudget (L : ℕ) : ℝ :=
  (Fintype.card (PauliTracelessLabel (L * 2) 2) : ℝ) *
    (2 * Real.exp (-((L * 2 : ℕ) : ℝ) ^ 2 / 2))

theorem stdGaussian_measure_pairQubitOptimalDesignScaledAffineTwoLocalNearAction_gap_le
    {L : ℕ} {scale : ℝ} (hscale : scale ≠ 0)
    {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ) (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    (δ : ℝ) {κ : ℝ} (hκ : 0 < κ) :
    (stdGaussian (TwoLocalPauliCoefficientSpace (L * 2))).real
        (pairQubitWeakTwoLocalNearActionGapEvent scale r U δ κ) ≤
      pairQubitWeakTwoLocalCarrierBudget r U κ := by
  unfold pairQubitWeakTwoLocalNearActionGapEvent
    pairQubitWeakTwoLocalCarrierBudget
    pairQubitUnitaryProjectiveTraceDeficit
  exact stdGaussian_measure_optimalDesignScaledAffineTwoLocalNearAction_gap_le_traceDeficit
    (pairQubitInverseSquarePauliSeed_isHermitian L) hscale r
      (fun c => pairQubitPathUnitaryReindex L (U c)) δ hκ

theorem exists_pairQubitWeakTwoLocal_sameDraw_growth_and_carrier
    {L : ℕ} {scale : ℝ} (hscale : scale ≠ 0)
    {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ) (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    (δ : ℝ) {κ : ℝ} (hκ : 0 < κ)
    (hjoint : pairQubitWeakTwoLocalGrowthFailureBudget L +
        pairQubitWeakTwoLocalCarrierBudget r U κ < 1) :
    ∃ x : TwoLocalPauliCoefficientSpace (L * 2),
      x ∈ weakTwoLocalPauliCertifiedGrowthSet L ∧
      x ∉ pairQubitWeakTwoLocalNearActionGapEvent scale r U δ κ := by
  let μ := stdGaussian (TwoLocalPauliCoefficientSpace (L * 2))
  let G := weakTwoLocalPauliCertifiedGrowthSet L
  let S := pairQubitWeakTwoLocalNearActionGapEvent scale r U δ κ
  have hGc : μ.real Gᶜ ≤ pairQubitWeakTwoLocalGrowthFailureBudget L := by
    exact stdGaussian_weakTwoLocalPauliCertifiedGrowthSet_compl_le L
  have hS : μ.real S ≤ pairQubitWeakTwoLocalCarrierBudget r U κ := by
    exact stdGaussian_measure_pairQubitOptimalDesignScaledAffineTwoLocalNearAction_gap_le
      hscale r U δ hκ
  by_contra hnone
  push Not at hnone
  have hcover : Set.univ ⊆ Gᶜ ∪ S := by
    intro x _
    by_cases hx : x ∈ G
    · exact Or.inr (hnone x hx)
    · exact Or.inl hx
  have hone : 1 ≤ μ.real Gᶜ + μ.real S := by
    calc
      1 = μ.real Set.univ := by simp [μ]
      _ ≤ μ.real (Gᶜ ∪ S) := measureReal_mono hcover
      _ ≤ μ.real Gᶜ + μ.real S := measureReal_union_le _ _
  linarith

/-- A uniform projective-return excision collapses the complete optimal-design
carrier to one dimension-linear exponential, with no target-count factor. -/
theorem pairQubitWeakTwoLocalCarrierBudget_le_of_projectiveDeficit
    {L : ℕ} {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ) (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    {η κ : ℝ} (hη : ∀ c, η ≤ pairQubitUnitaryProjectiveTraceDeficit (U c))
    (hκ : 0 < κ) :
    pairQubitWeakTwoLocalCarrierBudget r U κ ≤
      Real.exp (-(gaussianIntervalActivationMass ^ 2 / 2) *
        (((6 * (L * 2) - 4 : ℕ) : ℝ) * η)) / κ := by
  unfold pairQubitWeakTwoLocalCarrierBudget
  apply div_le_div_of_nonneg_right _ hκ.le
  let w := finiteUnitaryChoiOptimalDesignWeight r
    (fun c => pairQubitPathUnitaryReindex L (U c))
  have hw : w ∈ stdSimplex ℝ C :=
    finiteUnitaryChoiOptimalDesignWeight_mem_stdSimplex r
      (fun c => pairQubitPathUnitaryReindex L (U c))
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

/-- **Count-free same-draw growth/carrier fusion.**  After removing one
projective-return tube, a single explicit exponential budget guarantees one
fixed ordinary two-local draw with both robust laboratory growth and complete
optimal-design carrier control. -/
theorem exists_pairQubitWeakTwoLocal_sameDraw_growth_and_carrier_of_projectiveDeficit
    {L : ℕ} {scale : ℝ} (hscale : scale ≠ 0)
    {C : Type*} [Fintype C] [Nonempty C] [DecidableEq C]
    (r : ℕ) (U : C → Matrix.unitaryGroup (Config (PairQubit L)) ℂ)
    (δ : ℝ) {η κ : ℝ}
    (hη : ∀ c, η ≤ pairQubitUnitaryProjectiveTraceDeficit (U c))
    (hκ : 0 < κ)
    (hjoint : pairQubitWeakTwoLocalGrowthFailureBudget L +
        Real.exp (-(gaussianIntervalActivationMass ^ 2 / 2) *
          (((6 * (L * 2) - 4 : ℕ) : ℝ) * η)) / κ < 1) :
    ∃ x : TwoLocalPauliCoefficientSpace (L * 2),
      x ∈ weakTwoLocalPauliCertifiedGrowthSet L ∧
      x ∉ pairQubitWeakTwoLocalNearActionGapEvent scale r U δ κ := by
  apply exists_pairQubitWeakTwoLocal_sameDraw_growth_and_carrier
    hscale r U δ hκ
  exact lt_of_le_of_lt
    (add_le_add le_rfl
      (pairQubitWeakTwoLocalCarrierBudget_le_of_projectiveDeficit r U hη hκ))
    hjoint

end

end RHTower
