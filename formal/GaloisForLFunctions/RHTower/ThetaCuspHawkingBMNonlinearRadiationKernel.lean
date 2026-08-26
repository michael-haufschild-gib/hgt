import GaloisForLFunctions.RHTower.ThetaCuspHawkingNonlinearBoundaryHelicityFluxDichotomy
import GaloisForLFunctions.RHTower.DeningerDivisorSchwarzMonodromy

open Complex Real
open scoped InnerProductSpace

namespace RHTower

noncomputable section

abbrev d4BMGaugeFixedSecondHarmonicRadiationSpace :=
  EuclideanSpace ℂ (Fin 4)

/-- Normalizable-boundary transfer in one BM second-harmonic sector. -/
def d4BMXiSecondHarmonicBoundaryTransfer (q : XiZeroCopy) : ℂ :=
  d4BMGravitationalNormalizableBoundaryTransfer
    (d4ThetaHawkingSelfDualSecondHarmonicFrequency (xiSpectralPoint q))
    (xiSpectralPoint q)

/-- Horizon readout makes the complete BM radiation map injective. -/
theorem d4BMGaugeFixedSecondHarmonicRadiationMap_injective (q : XiZeroCopy) :
    Function.Injective (d4BMGaugeFixedSecondHarmonicRadiationMap q) := by
  intro x y h
  have hplus := congrArg
    (fun v : d4BMGaugeFixedSecondHarmonicRadiationSpace => v 0) h
  have hminus := congrArg
    (fun v : d4BMGaugeFixedSecondHarmonicRadiationSpace => v 2) h
  simp only [d4BMGaugeFixedSecondHarmonicRadiationMap, LinearMap.coe_mk,
    AddHom.coe_mk] at hplus hminus
  apply Prod.ext
  · exact mul_left_cancel₀
      (d4BMGaugeFixedSecondHarmonicGreen_ne_zero q) hplus
  · exact mul_left_cancel₀
      (d4BMGaugeFixedSecondHarmonicGreen_ne_zero q) hminus

/-- Exact linear kernel of the full horizon-plus-boundary radiation record. -/
theorem d4BMGaugeFixedSecondHarmonicRadiationMap_ker_eq_bot (q : XiZeroCopy) :
    LinearMap.ker (d4BMGaugeFixedSecondHarmonicRadiationMap q) = ⊥ := by
  exact LinearMap.ker_eq_bot.mpr
    (d4BMGaugeFixedSecondHarmonicRadiationMap_injective q)

/-- Radiation carried by the actual opposite-helicity source coordinate. -/
def d4BMGaugeFixedActualOrthogonalHelicityRadiation
    (q : XiZeroCopy) (mixing : ℂ) :
    d4BMGaugeFixedSecondHarmonicRadiationSpace :=
  d4BMGaugeFixedSecondHarmonicRadiationMap q (0, mixing)

/-- Squared norm of the actual opposite-helicity radiation channel. -/
def d4BMGaugeFixedActualOrthogonalHelicityFlux
    (q : XiZeroCopy) (mixing : ℂ) : ℝ :=
  ‖d4BMGaugeFixedActualOrthogonalHelicityRadiation q mixing‖ ^ 2

theorem d4BMGaugeFixedActualOrthogonalHelicityRadiation_eq_zero_iff
    (q : XiZeroCopy) (mixing : ℂ) :
    d4BMGaugeFixedActualOrthogonalHelicityRadiation q mixing = 0 ↔
      mixing = 0 := by
  constructor
  · intro h
    have hm := congrArg
      (fun v : d4BMGaugeFixedSecondHarmonicRadiationSpace => v 2) h
    simp [d4BMGaugeFixedActualOrthogonalHelicityRadiation,
      d4BMGaugeFixedSecondHarmonicRadiationMap] at hm
    exact hm.resolve_left (d4BMGaugeFixedSecondHarmonicGreen_ne_zero q)
  · rintro rfl
    ext i
    fin_cases i <;>
      simp [d4BMGaugeFixedActualOrthogonalHelicityRadiation,
        d4BMGaugeFixedSecondHarmonicRadiationMap]

/-- Actual orthogonal flux vanishes by source absence, not by critical-line placement. -/
theorem d4BMGaugeFixedActualOrthogonalHelicityFlux_eq_zero_iff
    (q : XiZeroCopy) (mixing : ℂ) :
    d4BMGaugeFixedActualOrthogonalHelicityFlux q mixing = 0 ↔
      mixing = 0 := by
  rw [d4BMGaugeFixedActualOrthogonalHelicityFlux, sq_eq_zero_iff, norm_eq_zero]
  exact d4BMGaugeFixedActualOrthogonalHelicityRadiation_eq_zero_iff q mixing

theorem d4BMGaugeFixedActualOrthogonalHelicityFlux_pos
    (q : XiZeroCopy) {mixing : ℂ} (hmixing : mixing ≠ 0) :
    0 < d4BMGaugeFixedActualOrthogonalHelicityFlux q mixing := by
  have hne : d4BMGaugeFixedActualOrthogonalHelicityFlux q mixing ≠ 0 := by
    intro hzero
    exact hmixing
      ((d4BMGaugeFixedActualOrthogonalHelicityFlux_eq_zero_iff q mixing).mp hzero)
  exact lt_of_le_of_ne
    (by simp [d4BMGaugeFixedActualOrthogonalHelicityFlux]) hne.symm

/-- Exact zero fibre of the first nonlinear full-Einstein BM radiation map. -/
theorem d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation_eq_zero_iff
    (amplitude orthogonalMixing : ℂ) (q : XiZeroCopy) :
    d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation
        amplitude orthogonalMixing q = 0 ↔
      amplitude = 0 ∧ orthogonalMixing = 0 := by
  constructor
  · intro h
    have hmapzero : d4BMGaugeFixedSecondHarmonicRadiationMap q
        (d4ThetaHawkingSelfDualQuadraticCarrierCoefficient amplitude
          (xiSpectralPoint q), orthogonalMixing) =
        d4BMGaugeFixedSecondHarmonicRadiationMap q 0 := by
      simpa [d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation] using h
    have hsource :=
      d4BMGaugeFixedSecondHarmonicRadiationMap_injective q hmapzero
    have hcarrier : d4ThetaHawkingSelfDualQuadraticCarrierCoefficient amplitude
        (xiSpectralPoint q) = 0 := congrArg Prod.fst hsource
    have hmixing : orthogonalMixing = 0 := congrArg Prod.snd hsource
    refine ⟨?_, hmixing⟩
    by_contra ha
    exact d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_ne_zero
      ha q hcarrier
  · rintro ⟨rfl, rfl⟩
    ext i
    fin_cases i <;>
      simp [d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation,
        d4ThetaHawkingSelfDualQuadraticCarrierCoefficient,
        d4BMGaugeFixedSecondHarmonicRadiationMap]

/-- Tagged nonlinear radiation record on the reflected/conjugated Xi orbit. -/
def d4BMXiFESchwarzTaggedNonlinearRadiation
    (q : XiZeroCopy) (seed : (ℂ × ℂ) × (ℂ × ℂ)) :
    d4BMGaugeFixedSecondHarmonicRadiationSpace ×
      d4BMGaugeFixedSecondHarmonicRadiationSpace :=
  (d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation
      seed.1.1 seed.1.2 (xiZeroCopyReflectEquiv q),
    d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation
      seed.2.1 seed.2.2 (xiZeroCopyConjEquiv q))

/-- Full tagged FE--Schwarz nonlinear radiation has trivial zero fibre. -/
theorem d4BMXiFESchwarzTaggedNonlinearRadiation_eq_zero_iff
    (q : XiZeroCopy) (seed : (ℂ × ℂ) × (ℂ × ℂ)) :
    d4BMXiFESchwarzTaggedNonlinearRadiation q seed = 0 ↔ seed = 0 := by
  constructor
  · intro h
    have hr : d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation
        seed.1.1 seed.1.2 (xiZeroCopyReflectEquiv q) = 0 :=
      congrArg Prod.fst h
    have hc : d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation
        seed.2.1 seed.2.2 (xiZeroCopyConjEquiv q) = 0 :=
      congrArg Prod.snd h
    have hr0 :=
      (d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation_eq_zero_iff
        _ _ (xiZeroCopyReflectEquiv q)).mp hr
    have hc0 :=
      (d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation_eq_zero_iff
        _ _ (xiZeroCopyConjEquiv q)).mp hc
    apply Prod.ext
    · exact Prod.ext hr0.1 hr0.2
    · exact Prod.ext hc0.1 hc0.2
  · rintro rfl
    simp [d4BMXiFESchwarzTaggedNonlinearRadiation,
      (d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation_eq_zero_iff
        0 0 (xiZeroCopyReflectEquiv q)).mpr ⟨rfl, rfl⟩,
      (d4ThetaFullEinsteinGaugeFixedSecondHarmonicRadiation_eq_zero_iff
        0 0 (xiZeroCopyConjEquiv q)).mpr ⟨rfl, rfl⟩]

/-- Untagged difference of reflected and conjugated opposite-helicity radiation. -/
def d4BMXiFESchwarzFoldedOrthogonalHelicityRadiation
    (q : XiZeroCopy) (mixing : ℂ × ℂ) :
    d4BMGaugeFixedSecondHarmonicRadiationSpace :=
  d4BMGaugeFixedActualOrthogonalHelicityRadiation
      (xiZeroCopyReflectEquiv q) mixing.1 -
    d4BMGaugeFixedActualOrthogonalHelicityRadiation
      (xiZeroCopyConjEquiv q) mixing.2

/-- Untagged difference of reflected and conjugated direct-helicity radiation. -/
def d4BMXiFESchwarzFoldedDirectHelicityRadiation
    (q : XiZeroCopy) (direct : ℂ × ℂ) :
    d4BMGaugeFixedSecondHarmonicRadiationSpace :=
  d4BMGaugeFixedSecondHarmonicRadiationMap
      (xiZeroCopyReflectEquiv q) (direct.1, 0) -
    d4BMGaugeFixedSecondHarmonicRadiationMap
      (xiZeroCopyConjEquiv q) (direct.2, 0)

def d4BMXiFESchwarzHasOrthogonalHelicityDarkKernel
    (q : XiZeroCopy) : Prop :=
  ∃ mixing : ℂ × ℂ, mixing ≠ 0 ∧
    d4BMXiFESchwarzFoldedOrthogonalHelicityRadiation q mixing = 0

def d4BMXiFESchwarzHasDirectHelicityDarkKernel
    (q : XiZeroCopy) : Prop :=
  ∃ direct : ℂ × ℂ, direct ≠ 0 ∧
    d4BMXiFESchwarzFoldedDirectHelicityRadiation q direct = 0

theorem d4BMXiFESchwarzFoldedOrthogonalHelicityRadiation_eq_zero_iff
    (q : XiZeroCopy) (mixing : ℂ × ℂ) :
    d4BMXiFESchwarzFoldedOrthogonalHelicityRadiation q mixing = 0 ↔
      d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyReflectEquiv q) * mixing.1 =
        d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyConjEquiv q) * mixing.2 ∧
      d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyReflectEquiv q) *
          d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyReflectEquiv q) * mixing.1 =
        d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyConjEquiv q) *
          d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyConjEquiv q) * mixing.2 := by
  constructor
  · intro h
    have hh := congrArg
      (fun v : d4BMGaugeFixedSecondHarmonicRadiationSpace => v 2) h
    have hb := congrArg
      (fun v : d4BMGaugeFixedSecondHarmonicRadiationSpace => v 3) h
    constructor
    · apply sub_eq_zero.mp
      simpa [d4BMXiFESchwarzFoldedOrthogonalHelicityRadiation,
        d4BMGaugeFixedActualOrthogonalHelicityRadiation,
        d4BMGaugeFixedSecondHarmonicRadiationMap] using hh
    · apply sub_eq_zero.mp
      simpa [d4BMXiFESchwarzFoldedOrthogonalHelicityRadiation,
        d4BMGaugeFixedActualOrthogonalHelicityRadiation,
        d4BMGaugeFixedSecondHarmonicRadiationMap,
        d4BMXiSecondHarmonicBoundaryTransfer] using hb
  · rintro ⟨hh, hb⟩
    have hb' :
        d4BMGravitationalNormalizableBoundaryTransfer
            (d4ThetaHawkingSelfDualSecondHarmonicFrequency
              (xiSpectralPoint (xiZeroCopyReflectEquiv q)))
            (xiSpectralPoint (xiZeroCopyReflectEquiv q)) *
              d4BMGaugeFixedSecondHarmonicGreen
                (xiZeroCopyReflectEquiv q) * mixing.1 =
          d4BMGravitationalNormalizableBoundaryTransfer
            (d4ThetaHawkingSelfDualSecondHarmonicFrequency
              (xiSpectralPoint (xiZeroCopyConjEquiv q)))
            (xiSpectralPoint (xiZeroCopyConjEquiv q)) *
              d4BMGaugeFixedSecondHarmonicGreen
                (xiZeroCopyConjEquiv q) * mixing.2 := by
      simpa [d4BMXiSecondHarmonicBoundaryTransfer] using hb
    ext i
    fin_cases i
    · simp [d4BMXiFESchwarzFoldedOrthogonalHelicityRadiation,
        d4BMGaugeFixedActualOrthogonalHelicityRadiation,
        d4BMGaugeFixedSecondHarmonicRadiationMap]
    · simp [d4BMXiFESchwarzFoldedOrthogonalHelicityRadiation,
        d4BMGaugeFixedActualOrthogonalHelicityRadiation,
        d4BMGaugeFixedSecondHarmonicRadiationMap]
    · simpa [d4BMXiFESchwarzFoldedOrthogonalHelicityRadiation,
        d4BMGaugeFixedActualOrthogonalHelicityRadiation,
        d4BMGaugeFixedSecondHarmonicRadiationMap] using sub_eq_zero.mpr hh
    · simpa [d4BMXiFESchwarzFoldedOrthogonalHelicityRadiation,
        d4BMGaugeFixedActualOrthogonalHelicityRadiation,
        d4BMGaugeFixedSecondHarmonicRadiationMap] using sub_eq_zero.mpr hb'

theorem d4BMXiFESchwarzFoldedDirectHelicityRadiation_eq_zero_iff
    (q : XiZeroCopy) (direct : ℂ × ℂ) :
    d4BMXiFESchwarzFoldedDirectHelicityRadiation q direct = 0 ↔
      d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyReflectEquiv q) * direct.1 =
        d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyConjEquiv q) * direct.2 ∧
      d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyReflectEquiv q) *
          d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyReflectEquiv q) * direct.1 =
        d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyConjEquiv q) *
          d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyConjEquiv q) * direct.2 := by
  constructor
  · intro h
    have hh := congrArg
      (fun v : d4BMGaugeFixedSecondHarmonicRadiationSpace => v 0) h
    have hb := congrArg
      (fun v : d4BMGaugeFixedSecondHarmonicRadiationSpace => v 1) h
    constructor
    · apply sub_eq_zero.mp
      simpa [d4BMXiFESchwarzFoldedDirectHelicityRadiation,
        d4BMGaugeFixedSecondHarmonicRadiationMap] using hh
    · apply sub_eq_zero.mp
      simpa [d4BMXiFESchwarzFoldedDirectHelicityRadiation,
        d4BMGaugeFixedSecondHarmonicRadiationMap,
        d4BMXiSecondHarmonicBoundaryTransfer] using hb
  · rintro ⟨hh, hb⟩
    have hb' :
        d4BMGravitationalNormalizableBoundaryTransfer
            (d4ThetaHawkingSelfDualSecondHarmonicFrequency
              (xiSpectralPoint (xiZeroCopyReflectEquiv q)))
            (xiSpectralPoint (xiZeroCopyReflectEquiv q)) *
              d4BMGaugeFixedSecondHarmonicGreen
                (xiZeroCopyReflectEquiv q) * direct.1 =
          d4BMGravitationalNormalizableBoundaryTransfer
            (d4ThetaHawkingSelfDualSecondHarmonicFrequency
              (xiSpectralPoint (xiZeroCopyConjEquiv q)))
            (xiSpectralPoint (xiZeroCopyConjEquiv q)) *
              d4BMGaugeFixedSecondHarmonicGreen
                (xiZeroCopyConjEquiv q) * direct.2 := by
      simpa [d4BMXiSecondHarmonicBoundaryTransfer] using hb
    ext i
    fin_cases i
    · simpa [d4BMXiFESchwarzFoldedDirectHelicityRadiation,
        d4BMGaugeFixedSecondHarmonicRadiationMap] using sub_eq_zero.mpr hh
    · simpa [d4BMXiFESchwarzFoldedDirectHelicityRadiation,
        d4BMGaugeFixedSecondHarmonicRadiationMap] using sub_eq_zero.mpr hb'
    · simp [d4BMXiFESchwarzFoldedDirectHelicityRadiation,
        d4BMGaugeFixedSecondHarmonicRadiationMap]
    · simp [d4BMXiFESchwarzFoldedDirectHelicityRadiation,
        d4BMGaugeFixedSecondHarmonicRadiationMap]

/-- Folded opposite-helicity dark kernel is exactly a BM transfer collision. -/
theorem d4BMXiFESchwarzHasOrthogonalHelicityDarkKernel_iff_transfer_eq
    (q : XiZeroCopy) :
    d4BMXiFESchwarzHasOrthogonalHelicityDarkKernel q ↔
      d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyReflectEquiv q) =
        d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyConjEquiv q) := by
  constructor
  · rintro ⟨mixing, hmixing, hfold⟩
    obtain ⟨hhorizon, hboundary⟩ :=
      (d4BMXiFESchwarzFoldedOrthogonalHelicityRadiation_eq_zero_iff
        q mixing).mp hfold
    have hcommon :
        d4BMGaugeFixedSecondHarmonicGreen
            (xiZeroCopyReflectEquiv q) * mixing.1 ≠ 0 := by
      intro hzero
      have hm1 : mixing.1 = 0 :=
        (mul_eq_zero.mp hzero).resolve_left
          (d4BMGaugeFixedSecondHarmonicGreen_ne_zero
            (xiZeroCopyReflectEquiv q))
      have hother : d4BMGaugeFixedSecondHarmonicGreen
          (xiZeroCopyConjEquiv q) * mixing.2 = 0 := by
        rw [← hhorizon, hzero]
      have hm2 : mixing.2 = 0 :=
        (mul_eq_zero.mp hother).resolve_left
          (d4BMGaugeFixedSecondHarmonicGreen_ne_zero
            (xiZeroCopyConjEquiv q))
      apply hmixing
      exact Prod.ext hm1 hm2
    have hcancel :
        d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyReflectEquiv q) *
            (d4BMGaugeFixedSecondHarmonicGreen
              (xiZeroCopyReflectEquiv q) * mixing.1) =
          d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyConjEquiv q) *
            (d4BMGaugeFixedSecondHarmonicGreen
              (xiZeroCopyReflectEquiv q) * mixing.1) := by
      calc
        _ = d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyReflectEquiv q) *
              d4BMGaugeFixedSecondHarmonicGreen
                (xiZeroCopyReflectEquiv q) * mixing.1 := by ring
        _ = d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyConjEquiv q) *
              d4BMGaugeFixedSecondHarmonicGreen
                (xiZeroCopyConjEquiv q) * mixing.2 := hboundary
        _ = d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyConjEquiv q) *
              (d4BMGaugeFixedSecondHarmonicGreen
                (xiZeroCopyConjEquiv q) * mixing.2) := by ring
        _ = _ := by rw [hhorizon]
    exact mul_right_cancel₀ hcommon hcancel
  · intro htransfer
    let reflectedGreen :=
      d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyReflectEquiv q)
    let conjugateGreen :=
      d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyConjEquiv q)
    refine ⟨(conjugateGreen, reflectedGreen), ?_, ?_⟩
    · intro hzero
      have hz := congrArg Prod.fst hzero
      simp only [Prod.fst_zero] at hz
      exact d4BMGaugeFixedSecondHarmonicGreen_ne_zero
        (xiZeroCopyConjEquiv q) hz
    · apply
        (d4BMXiFESchwarzFoldedOrthogonalHelicityRadiation_eq_zero_iff q _).mpr
      dsimp only [reflectedGreen, conjugateGreen]
      constructor
      · ring
      · rw [htransfer]
        ring

/-- Folded direct-helicity dark kernel has the same transfer-collision criterion. -/
theorem d4BMXiFESchwarzHasDirectHelicityDarkKernel_iff_transfer_eq
    (q : XiZeroCopy) :
    d4BMXiFESchwarzHasDirectHelicityDarkKernel q ↔
      d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyReflectEquiv q) =
        d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyConjEquiv q) := by
  constructor
  · rintro ⟨direct, hdirect, hfold⟩
    obtain ⟨hhorizon, hboundary⟩ :=
      (d4BMXiFESchwarzFoldedDirectHelicityRadiation_eq_zero_iff q direct).mp hfold
    have hcommon :
        d4BMGaugeFixedSecondHarmonicGreen
            (xiZeroCopyReflectEquiv q) * direct.1 ≠ 0 := by
      intro hzero
      have hd1 : direct.1 = 0 :=
        (mul_eq_zero.mp hzero).resolve_left
          (d4BMGaugeFixedSecondHarmonicGreen_ne_zero
            (xiZeroCopyReflectEquiv q))
      have hother : d4BMGaugeFixedSecondHarmonicGreen
          (xiZeroCopyConjEquiv q) * direct.2 = 0 := by
        rw [← hhorizon, hzero]
      have hd2 : direct.2 = 0 :=
        (mul_eq_zero.mp hother).resolve_left
          (d4BMGaugeFixedSecondHarmonicGreen_ne_zero
            (xiZeroCopyConjEquiv q))
      apply hdirect
      exact Prod.ext hd1 hd2
    have hcancel :
        d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyReflectEquiv q) *
            (d4BMGaugeFixedSecondHarmonicGreen
              (xiZeroCopyReflectEquiv q) * direct.1) =
          d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyConjEquiv q) *
            (d4BMGaugeFixedSecondHarmonicGreen
              (xiZeroCopyReflectEquiv q) * direct.1) := by
      calc
        _ = d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyReflectEquiv q) *
              d4BMGaugeFixedSecondHarmonicGreen
                (xiZeroCopyReflectEquiv q) * direct.1 := by ring
        _ = d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyConjEquiv q) *
              d4BMGaugeFixedSecondHarmonicGreen
                (xiZeroCopyConjEquiv q) * direct.2 := hboundary
        _ = d4BMXiSecondHarmonicBoundaryTransfer (xiZeroCopyConjEquiv q) *
              (d4BMGaugeFixedSecondHarmonicGreen
                (xiZeroCopyConjEquiv q) * direct.2) := by ring
        _ = _ := by rw [hhorizon]
    exact mul_right_cancel₀ hcommon hcancel
  · intro htransfer
    let reflectedGreen :=
      d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyReflectEquiv q)
    let conjugateGreen :=
      d4BMGaugeFixedSecondHarmonicGreen (xiZeroCopyConjEquiv q)
    refine ⟨(conjugateGreen, reflectedGreen), ?_, ?_⟩
    · intro hzero
      have hz := congrArg Prod.fst hzero
      simp only [Prod.fst_zero] at hz
      exact d4BMGaugeFixedSecondHarmonicGreen_ne_zero
        (xiZeroCopyConjEquiv q) hz
    · apply
        (d4BMXiFESchwarzFoldedDirectHelicityRadiation_eq_zero_iff q _).mpr
      dsimp only [reflectedGreen, conjugateGreen]
      constructor
      · ring
      · rw [htransfer]
        ring

/-- Folded dark kernels are not helicity-specific. -/
theorem d4BMXiFESchwarzHasOrthogonalHelicityDarkKernel_iff_direct
    (q : XiZeroCopy) :
    d4BMXiFESchwarzHasOrthogonalHelicityDarkKernel q ↔
      d4BMXiFESchwarzHasDirectHelicityDarkKernel q := by
  rw [d4BMXiFESchwarzHasOrthogonalHelicityDarkKernel_iff_transfer_eq,
    d4BMXiFESchwarzHasDirectHelicityDarkKernel_iff_transfer_eq]

/-- Critical-line copy coincidence produces both folded dark kernels simultaneously. -/
theorem d4BMXiFESchwarzDarkKernels_of_re_eq_half
    (q : XiZeroCopy) (hline : (q.1 : ℂ).re = 1 / 2) :
    d4BMXiFESchwarzHasOrthogonalHelicityDarkKernel q ∧
      d4BMXiFESchwarzHasDirectHelicityDarkKernel q := by
  have hcopy : xiZeroCopyReflectEquiv q = xiZeroCopyConjEquiv q :=
    xiZeroCopyReflectEquiv_eq_conjEquiv_of_re_eq_half q (by
      simpa [deningerDivisorThetaEigen] using hline)
  constructor
  · rw [d4BMXiFESchwarzHasOrthogonalHelicityDarkKernel_iff_transfer_eq, hcopy]
  · rw [d4BMXiFESchwarzHasDirectHelicityDarkKernel_iff_transfer_eq, hcopy]

end

end RHTower
