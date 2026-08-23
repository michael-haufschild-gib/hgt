import GaloisForLFunctions.HTGeometry.FullProjectiveChoiPhysicalWindowLaw
import GaloisForLFunctions.RHTower.StaticChoiFirstReturnPackingLaw

open scoped BigOperators
open Set MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- Canonical anchored spectrum realizing any projective frequency packet. -/
def projectiveFrequencyEnergy {d : ℕ} (omega : Fin d → ℝ) : Fin (d + 1) → ℝ :=
  Fin.cases 0 (fun j => -omega j)

@[simp] theorem zeroProjectiveFrequency_projectiveFrequencyEnergy
    {d : ℕ} (omega : Fin d → ℝ) :
    zeroProjectiveFrequency (projectiveFrequencyEnergy omega) = omega := by
  funext j
  simp [zeroProjectiveFrequency, projectiveFrequencyEnergy]

theorem projectivePhysicalPhaseFlow_projectiveFrequencyEnergy
    {d : ℕ} (omega : Fin d → ℝ) (t : ℝ) :
    projectivePhysicalPhaseFlow (projectiveFrequencyEnergy omega) t =
      angularPhasePoint (fun j => t * omega j) := by
  funext j
  simp [projectivePhysicalPhaseFlow, angularPhasePoint]

theorem zeroAnchoredMetricBallFamilyAngularVisit_eq_projectiveChoiCapture
    {d m : ℕ} (delta : ℝ)
    (target : Fin m → EuclideanSpace ℂ (Fin (d + 1) × Fin (d + 1)))
    (omega : Fin d → ℝ) :
    zeroAnchoredMetricBallFamilyAngularVisit d m delta target omega =
      {t | ∃ a,
        dist (projectiveChoiDensityFlow (projectiveFrequencyEnergy omega) t)
          (target a) ≤ delta} := by
  ext t
  simp only [zeroAnchoredMetricBallFamilyAngularVisit,
    zeroAnchoredMetricBallTarget, projectiveChoiDensityFlow, Set.mem_setOf_eq]
  rw [projectivePhysicalPhaseFlow_projectiveFrequencyEnergy]

/-- Explicit physical-time occupation budget for a full projective target
family over the symmetric laboratory window `(-T,T]`. -/
def fullProjectiveTensorPhysicalOccupationBudget
    (n N m : ℕ) (g eta epsw T C : ℝ) : ℝ :=
  (2 : ℝ) ^ (n + 1) * (2 * T) *
    (((m : ℕ) : ℝ) *
        (2 * zeroAnchoredChoiAngularRadius (n + 1) epsw / (2 * Real.pi) +
          periodicTentFejerError N
            (2 * zeroAnchoredChoiAngularRadius (n + 1) epsw)) ^ (n + 1) +
      (2 * C / (g * (2 * T))) * ((m : ℝ) *
        periodicFejerMajorantAffineCostUpperBound N n
          (2 * zeroAnchoredChoiAngularRadius (n + 1) epsw)
          (periodicTentFejerError N
            (2 * zeroAnchoredChoiAngularRadius (n + 1) epsw)) eta))

/-- Lipschitz speed of the full projective density orbit after restoring
the clock gap. -/
def fullProjectiveDensitySpeed {n : ℕ} (g : ℝ) (y : Fin n → ℝ) : ℝ :=
  Real.sqrt 2 * projectiveChoiSpeed
    (projectiveFrequencyEnergy (clockScaledFullProjectiveFrequency g y))

theorem fullProjectiveDensitySpeed_pos {n : ℕ} (g : ℝ) (y : Fin n → ℝ) :
    0 < fullProjectiveDensitySpeed g y := by
  exact mul_pos (Real.sqrt_pos.2 (by norm_num)) (projectiveChoiSpeed_pos _)

/-- Tensorized affine occupation forces an unconditional alternative:
either the explicit target entropy budget pays the complete two-cell return
cost, or no second capture of the entire adaptive family occurs. -/
theorem exists_fullProjectiveChoiTensor_firstReturnDichotomy
    {n : ℕ} {y : Fin n → ℝ} (hy : ¬ KleinbockMargulis.VWMA y)
    {g eta epsw : ℝ} (hg : 0 < g) (heta : 0 < eta) (hepsw : 0 < epsw)
    (N m : ℕ)
    (hsmall : 2 * zeroAnchoredChoiAngularRadius (n + 1) epsw ≤ Real.pi) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ (target : Fin m →
          EuclideanSpace ℂ (Fin (n + 2) × Fin (n + 2)))
        (c0 : Fin m),
        target c0 = projectiveChoiDensityFlow
          (projectiveFrequencyEnergy (clockScaledFullProjectiveFrequency g y)) 0 →
        ∀ epsn T : ℝ, 0 ≤ epsn → epsn < epsw → 0 < T →
          epsw / fullProjectiveDensitySpeed g y ≤ T →
          2 * (epsw / fullProjectiveDensitySpeed g y) +
                (epsw - epsn) / fullProjectiveDensitySpeed g y ≤
              fullProjectiveTensorPhysicalOccupationBudget n N m g eta epsw T C ∨
            ¬ ∃ t ∈ Set.Icc
                (epsw / fullProjectiveDensitySpeed g y +
                  (epsw - epsn) / fullProjectiveDensitySpeed g y) T,
              ∃ c, dist
                (projectiveChoiDensityFlow
                  (projectiveFrequencyEnergy
                    (clockScaledFullProjectiveFrequency g y)) t)
                (target c) ≤ epsn := by
  obtain ⟨C, hC, hoccupation⟩ :=
    exists_fullProjectiveMetricBallFamily_centerFreeTensorPhysicalWindowUpper
      hy hg heta hepsw N m hsmall
  refine ⟨C, hC, ?_⟩
  intro target c0 htarget0 epsn T hepsn hgap hT honset
  let energy := projectiveFrequencyEnergy (clockScaledFullProjectiveFrequency g y)
  let speed := fullProjectiveDensitySpeed g y
  let budget := fullProjectiveTensorPhysicalOccupationBudget n N m g eta epsw T C
  let width := 2 * (epsw / speed) + (epsw - epsn) / speed
  by_cases hbudget : budget < width
  · right
    have hvisit := hoccupation target (-T) (2 * T) (by positivity)
    have hwide :
        volume.real
          {t | t ∈ Set.Ioc (-T) T ∧ ∃ c,
            dist (projectiveChoiDensityFlow energy t) (target c) ≤ epsw} <
          width := by
      apply lt_of_le_of_lt ?_ hbudget
      have hset :
          {t | t ∈ Set.Ioc (-T) T ∧ ∃ c,
              dist (projectiveChoiDensityFlow energy t) (target c) ≤ epsw} =
            zeroAnchoredMetricBallFamilyAngularVisit (n + 1) m epsw target
                (clockScaledFullProjectiveFrequency g y) ∩
              Set.Ioc (-T) (-T + 2 * T) := by
        rw [zeroAnchoredMetricBallFamilyAngularVisit_eq_projectiveChoiCapture]
        have hend : -T + 2 * T = T := by ring
        rw [hend]
        ext t
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
        exact and_comm
      rw [hset]
      simpa only [budget, fullProjectiveTensorPhysicalOccupationBudget] using hvisit
    exact no_second_capture_of_wide_occupation_lt
      dist (projectiveChoiDensityFlow energy) target c0
      (fullProjectiveDensitySpeed_pos g y) hepsn hgap honset
      (by simpa only [energy] using htarget0)
      (fun t u c => dist_triangle _ _ _)
      (fun t u => by
        simpa only [speed, energy, fullProjectiveDensitySpeed] using
          dist_projectiveChoiDensityFlow_le energy t u)
      (by simpa only [width, speed, energy] using hwide)
  · left
    exact le_of_not_gt hbudget

/-- Quenched full-projective first-return law for one fixed ratio packet. -/
def HasFullProjectiveChoiTensorFirstReturnDichotomy {n : ℕ}
    (y : Fin n → ℝ) : Prop :=
  ∀ g : ℝ, 0 < g → ∀ eta epsw : ℝ, 0 < eta → 0 < epsw →
    ∀ N m : ℕ,
      2 * zeroAnchoredChoiAngularRadius (n + 1) epsw ≤ Real.pi →
      ∃ C : ℝ, 1 ≤ C ∧
        ∀ (target : Fin m →
            EuclideanSpace ℂ (Fin (n + 2) × Fin (n + 2)))
          (c0 : Fin m),
          target c0 = projectiveChoiDensityFlow
            (projectiveFrequencyEnergy (clockScaledFullProjectiveFrequency g y)) 0 →
          ∀ epsn T : ℝ, 0 ≤ epsn → epsn < epsw → 0 < T →
            epsw / fullProjectiveDensitySpeed g y ≤ T →
            2 * (epsw / fullProjectiveDensitySpeed g y) +
                  (epsw - epsn) / fullProjectiveDensitySpeed g y ≤
                fullProjectiveTensorPhysicalOccupationBudget n N m g eta epsw T C ∨
              ¬ ∃ t ∈ Set.Icc
                  (epsw / fullProjectiveDensitySpeed g y +
                    (epsw - epsn) / fullProjectiveDensitySpeed g y) T,
                ∃ c, dist
                  (projectiveChoiDensityFlow
                    (projectiveFrequencyEnergy
                      (clockScaledFullProjectiveFrequency g y)) t)
                  (target c) ≤ epsn

theorem hasFullProjectiveChoiTensorFirstReturnDichotomy_of_not_vwma
    {n : ℕ} {y : Fin n → ℝ} (hy : ¬ KleinbockMargulis.VWMA y) :
    HasFullProjectiveChoiTensorFirstReturnDichotomy y := by
  intro g hg eta epsw heta hepsw N m hsmall
  exact exists_fullProjectiveChoiTensor_firstReturnDichotomy
    hy hg heta hepsw N m hsmall

variable {K D n : ℕ} {P : Fin K → Matrix (Fin D) (Fin D) ℂ}

theorem volume_not_hasFullProjectiveChoiTensorFirstReturnDichotomy_eq_zero
    [NeZero K]
    (hP : ∀ a, (P a).IsHermitian)
    (hS : SpectrumEscapesRealRelations (Set.range (spectralEnsembleMatrix P)))
    {anchor clock : Fin D} {ι : Fin n → Fin D} (hι : Function.Injective ι)
    (hanchor : ∀ k, ι k ≠ anchor) (hclock : ∀ k, ι k ≠ clock)
    (hac : anchor ≠ clock) :
    volume {x ∈ simpleEnsembleLocus hP |
      ¬ HasFullProjectiveChoiTensorFirstReturnDichotomy
        (fun k => anchoredGapRatioMap
          (sortedEnsembleSpectrum hP x) anchor clock ι k)} = 0 := by
  refine measure_mono_null ?_
    (volume_vwma_sortedGapRatio_eq_zero hP hS hι hanchor hclock hac)
  rintro x ⟨hx, hfail⟩
  refine ⟨hx, ?_⟩
  by_contra hvwma
  exact hfail
    (hasFullProjectiveChoiTensorFirstReturnDichotomy_of_not_vwma hvwma)

/-- Lowest sorted spectral level. -/
def chainFullProjectiveAnchor (k : ℕ) : Fin (2 ^ (k + 3)) :=
  ⟨0, Nat.two_pow_pos _⟩

/-- Next sorted spectral level, used as a positive physical clock. -/
def chainFullProjectiveClock (k : ℕ) : Fin (2 ^ (k + 3)) :=
  ⟨1, Nat.one_lt_pow (by omega) (by omega)⟩

/-- Every remaining spectral level after the lowest-two-level clock. -/
def chainFullProjectiveTailIndex (k : ℕ) :
    Fin (2 ^ (k + 3) - 2) → Fin (2 ^ (k + 3)) :=
  fun j => ⟨j.1 + 2, by omega⟩

theorem chainFullProjectiveTailIndex_injective (k : ℕ) :
    Function.Injective (chainFullProjectiveTailIndex k) := by
  intro i j hij
  apply Fin.ext
  have hv := congrArg Fin.val hij
  change i.1 + 2 = j.1 + 2 at hv
  omega

theorem chainFullProjectiveTailIndex_ne_anchor (k : ℕ) (j : Fin (2 ^ (k + 3) - 2)) :
    chainFullProjectiveTailIndex k j ≠ chainFullProjectiveAnchor k := by
  intro h
  have hv := congrArg Fin.val h
  simp [chainFullProjectiveTailIndex, chainFullProjectiveAnchor] at hv

theorem chainFullProjectiveTailIndex_ne_clock (k : ℕ) (j : Fin (2 ^ (k + 3) - 2)) :
    chainFullProjectiveTailIndex k j ≠ chainFullProjectiveClock k := by
  intro h
  have hv := congrArg Fin.val h
  simp [chainFullProjectiveTailIndex, chainFullProjectiveClock] at hv

theorem chainFullProjectiveAnchor_ne_clock (k : ℕ) :
    chainFullProjectiveAnchor k ≠ chainFullProjectiveClock k := by
  intro h
  have hv := congrArg Fin.val h
  simp [chainFullProjectiveAnchor, chainFullProjectiveClock] at hv

/-- **One-draw full-spectrum first-return law.** Almost every standard
Gaussian nearest-neighbour time-independent Pauli Hamiltonian has simple
spectrum and, using its lowest two levels as clock and every other level as
the ratio packet, obeys the complete adaptive Choi first-return dichotomy. -/
theorem chainFullGapRatio_hasFullProjectiveChoiTensorFirstReturnDichotomy_ae_stdGaussian
    (k : ℕ) :
    ∀ᵐ x ∂(ProbabilityTheory.stdGaussian
      (EuclideanSpace ℝ (Fin (Fintype.card (ChainLabel (k + 3)))))),
      WithLp.ofLp x ∈ simpleEnsembleLocus
        (chainPauliFin_isHermitian (k + 3)) ∧
      HasFullProjectiveChoiTensorFirstReturnDichotomy
        (fun j => anchoredGapRatioMap
          (sortedEnsembleSpectrum (chainPauliFin_isHermitian (k + 3))
            (WithLp.ofLp x))
          (chainFullProjectiveAnchor k) (chainFullProjectiveClock k)
          (chainFullProjectiveTailIndex k) j) := by
  classical
  let p := Fintype.card (ChainLabel (k + 3))
  let hP := chainPauliFin_isHermitian (k + 3)
  have hmp := PiLp.volume_preserving_ofLp (Fin p)
  have hnullSimple :
      (volume : Measure (EuclideanSpace ℝ (Fin p)))
        {x | WithLp.ofLp x ∉ simpleEnsembleLocus hP} = 0 := by
    have hsub :
        {theta : Fin p → ℝ | theta ∉ simpleEnsembleLocus hP} ⊆
          {theta | ¬ MaximallyProjectiveEnergy
            (isHermitian_spectralEnsembleMatrix hP theta).eigenvalues} := by
      intro theta htheta hmax
      exact htheta hmax.injective
    have hbase :
        (volume : Measure (Fin p → ℝ))
          {theta | theta ∉ simpleEnsembleLocus hP} = 0 :=
      measure_mono_null hsub (volume_notMaximallyProjective_chain_eq_zero k)
    have hpre :
        {x : EuclideanSpace ℝ (Fin p) |
          WithLp.ofLp x ∉ simpleEnsembleLocus hP} =
          WithLp.ofLp ⁻¹' {theta | theta ∉ simpleEnsembleLocus hP} := rfl
    rw [hpre, hmp.measure_preimage (NullMeasurableSet.of_null hbase), hbase]
  have hnullLaw :
      (volume : Measure (EuclideanSpace ℝ (Fin p)))
        {x | WithLp.ofLp x ∈ simpleEnsembleLocus hP ∧
          ¬ HasFullProjectiveChoiTensorFirstReturnDichotomy
            (fun j => anchoredGapRatioMap
              (sortedEnsembleSpectrum hP (WithLp.ofLp x))
              (chainFullProjectiveAnchor k) (chainFullProjectiveClock k)
              (chainFullProjectiveTailIndex k) j)} = 0 := by
    have hbase :
        (volume : Measure (Fin p → ℝ))
          {theta ∈ simpleEnsembleLocus hP |
            ¬ HasFullProjectiveChoiTensorFirstReturnDichotomy
              (fun j => anchoredGapRatioMap
                (sortedEnsembleSpectrum hP theta)
                (chainFullProjectiveAnchor k) (chainFullProjectiveClock k)
                (chainFullProjectiveTailIndex k) j)} = 0 :=
      volume_not_hasFullProjectiveChoiTensorFirstReturnDichotomy_eq_zero
        hP (chainPauliFin_spectrumEscapesRealRelations k)
        (chainFullProjectiveTailIndex_injective k)
        (chainFullProjectiveTailIndex_ne_anchor k)
        (chainFullProjectiveTailIndex_ne_clock k)
        (chainFullProjectiveAnchor_ne_clock k)
    have hpre :
        {x : EuclideanSpace ℝ (Fin p) |
          WithLp.ofLp x ∈ simpleEnsembleLocus hP ∧
            ¬ HasFullProjectiveChoiTensorFirstReturnDichotomy
              (fun j => anchoredGapRatioMap
                (sortedEnsembleSpectrum hP (WithLp.ofLp x))
                (chainFullProjectiveAnchor k) (chainFullProjectiveClock k)
                (chainFullProjectiveTailIndex k) j)} =
          WithLp.ofLp ⁻¹' {theta ∈ simpleEnsembleLocus hP |
            ¬ HasFullProjectiveChoiTensorFirstReturnDichotomy
              (fun j => anchoredGapRatioMap
                (sortedEnsembleSpectrum hP theta)
                (chainFullProjectiveAnchor k) (chainFullProjectiveClock k)
                (chainFullProjectiveTailIndex k) j)} := rfl
    rw [hpre, hmp.measure_preimage (NullMeasurableSet.of_null hbase), hbase]
  have hnullBad :
      (volume : Measure (EuclideanSpace ℝ (Fin p)))
        ({x | WithLp.ofLp x ∉ simpleEnsembleLocus hP} ∪
          {x | WithLp.ofLp x ∈ simpleEnsembleLocus hP ∧
            ¬ HasFullProjectiveChoiTensorFirstReturnDichotomy
              (fun j => anchoredGapRatioMap
                (sortedEnsembleSpectrum hP (WithLp.ofLp x))
                (chainFullProjectiveAnchor k) (chainFullProjectiveClock k)
                (chainFullProjectiveTailIndex k) j)}) = 0 :=
    measure_union_null hnullSimple hnullLaw
  have hgauss :
      ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin p))
        ({x | WithLp.ofLp x ∉ simpleEnsembleLocus hP} ∪
          {x | WithLp.ofLp x ∈ simpleEnsembleLocus hP ∧
            ¬ HasFullProjectiveChoiTensorFirstReturnDichotomy
              (fun j => anchoredGapRatioMap
                (sortedEnsembleSpectrum hP (WithLp.ofLp x))
                (chainFullProjectiveAnchor k) (chainFullProjectiveClock k)
                (chainFullProjectiveTailIndex k) j)}) = 0 :=
    (stdGaussian_absolutelyContinuous_volume_finEuclidean p) hnullBad
  refine MeasureTheory.ae_iff.mpr (measure_mono_null ?_ hgauss)
  intro x hx
  by_cases hs : WithLp.ofLp x ∈ simpleEnsembleLocus hP
  · exact Or.inr ⟨hs, fun hlaw => hx ⟨hs, hlaw⟩⟩
  · exact Or.inl hs

end RHTower
