import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaBreatherMovingNLS
import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaBreatherPhysicalNLS
import Mathlib.Tactic

/-!
# Physical moving breathers

The paper's Galilean velocity and physical scaling are composed.  This produces dimensional
Akhmediev and Ma fields, their physical propagation speeds, moving reflection axes, inherited peak
bounds and periods, and closed certificates for Brizard's dimensional NLS.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

noncomputable def physicalMovingAkhmedievBreather
    (P : BreatherPhysicalScales) (u : ℝ) (φ : BreatherAngle) (s t : ℝ) : ℂ :=
  (physicalAkhmedievAmplitude P φ : ℂ) *
    movingAkhmedievBreather u φ (physicalAkhmedievXi P φ s)
      (physicalAkhmedievTau P φ t)

noncomputable def physicalMovingMaBreather
    (P : BreatherPhysicalScales) (u : ℝ) (φ : MaAngle) (s t : ℝ) : ℂ :=
  (physicalMaAmplitude P φ : ℂ) *
    movingMaBreather u φ (physicalMaXi P φ s) (physicalMaTau P φ t)

noncomputable def physicalMovingAkhmedievSolution
    (P : BreatherPhysicalScales) (u : ℝ) (φ : BreatherAngle) :
    BrizardSolutionJet (P.circulation : ℝ) :=
  physicalizeFocusingSolution (P.circulation : ℝ)
    ((P.waveNumber : ℝ) / akhmedievWaveNumber φ) (movingAkhmedievSolution u φ)

noncomputable def physicalMovingMaSolution
    (P : BreatherPhysicalScales) (u : ℝ) (φ : MaAngle) :
    BrizardSolutionJet (P.circulation : ℝ) :=
  physicalizeFocusingSolution (P.circulation : ℝ)
    ((P.waveNumber : ℝ) / maWaveNumber φ) (movingMaSolution u φ)

theorem physicalMovingAkhmedievSolution_field
    (P : BreatherPhysicalScales) (u : ℝ) (φ : BreatherAngle) (t s : ℝ) :
    (physicalMovingAkhmedievSolution P u φ).val.u t s =
      physicalMovingAkhmedievBreather P u φ s t := by
  simp only [physicalMovingAkhmedievSolution, physicalizeFocusingSolution,
    physicalizeFocusingJet]
  rw [movingAkhmedievSolution_field, physicalMovingAkhmedievBreather,
    physicalAkhmedievAmplitude, physicalAkhmedievXi, physicalAkhmedievTau,
    physicalAkhmedievFrequency]
  have hp : akhmedievWaveNumber φ ≠ 0 := ne_of_gt (akhmedievWaveNumber_pos φ)
  have hOmega : akhmedievOmega φ ≠ 0 := by
    rw [akhmedievOmega]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
      (by linarith [φ.property.1]) (by linarith [φ.property.2, Real.pi_pos]))
  congr 1
  · push_cast
    ring
  · congr 1
    · field_simp [hp]
    · field_simp [hp, hOmega]

theorem physicalMovingMaSolution_field
    (P : BreatherPhysicalScales) (u : ℝ) (φ : MaAngle) (t s : ℝ) :
    (physicalMovingMaSolution P u φ).val.u t s = physicalMovingMaBreather P u φ s t := by
  simp only [physicalMovingMaSolution, physicalizeFocusingSolution, physicalizeFocusingJet]
  rw [movingMaSolution_field, physicalMovingMaBreather, physicalMaAmplitude,
    physicalMaXi, physicalMaTau, physicalMaFrequency]
  have hp : maWaveNumber φ ≠ 0 := ne_of_gt (maWaveNumber_pos φ)
  have hOmega : maOmega φ ≠ 0 := ne_of_gt (maOmega_pos φ)
  congr 1
  · push_cast
    ring
  · congr 1
    · field_simp [hp]
    · field_simp [hp, hOmega]

theorem physicalMovingAkhmedievSolution_solves
    (P : BreatherPhysicalScales) (u : ℝ) (φ : BreatherAngle) :
    SolvesNLS (P.circulation : ℝ) (physicalMovingAkhmedievSolution P u φ).val :=
  (physicalMovingAkhmedievSolution P u φ).property

theorem physicalMovingMaSolution_solves
    (P : BreatherPhysicalScales) (u : ℝ) (φ : MaAngle) :
    SolvesNLS (P.circulation : ℝ) (physicalMovingMaSolution P u φ).val :=
  (physicalMovingMaSolution P u φ).property

noncomputable def physicalAkhmedievVelocity
    (P : BreatherPhysicalScales) (u : ℝ) (φ : BreatherAngle) : ℝ :=
  u * (P.circulation : ℝ) * (P.waveNumber : ℝ) / akhmedievWaveNumber φ

noncomputable def physicalMaVelocity
    (P : BreatherPhysicalScales) (u : ℝ) (φ : MaAngle) : ℝ :=
  u * (P.circulation : ℝ) * (P.waveNumber : ℝ) / maWaveNumber φ

theorem physicalAkhmediev_center_coordinates
    (P : BreatherPhysicalScales) (u : ℝ) (φ : BreatherAngle) (t : ℝ) :
    physicalAkhmedievXi P φ (physicalAkhmedievVelocity P u φ * t) =
      u * physicalAkhmedievTau P φ t := by
  rw [physicalAkhmedievXi, physicalAkhmedievVelocity, physicalAkhmedievTau,
    physicalAkhmedievFrequency]
  have hp : akhmedievWaveNumber φ ≠ 0 := ne_of_gt (akhmedievWaveNumber_pos φ)
  have hOmega : akhmedievOmega φ ≠ 0 := by
    rw [akhmedievOmega]
    exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
      (by linarith [φ.property.1]) (by linarith [φ.property.2, Real.pi_pos]))
  field_simp [hp, hOmega]

theorem physicalMa_center_coordinates
    (P : BreatherPhysicalScales) (u : ℝ) (φ : MaAngle) (t : ℝ) :
    physicalMaXi P φ (physicalMaVelocity P u φ * t) = u * physicalMaTau P φ t := by
  rw [physicalMaXi, physicalMaVelocity, physicalMaTau, physicalMaFrequency]
  field_simp [ne_of_gt (maWaveNumber_pos φ), ne_of_gt (maOmega_pos φ)]

theorem norm_physicalMovingAkhmedievBreather
    (P : BreatherPhysicalScales) (u : ℝ) (φ : BreatherAngle) (s t : ℝ) :
    ‖physicalMovingAkhmedievBreather P u φ s t‖ =
      physicalAkhmedievAmplitude P φ *
        ‖movingAkhmedievBreather u φ (physicalAkhmedievXi P φ s)
          (physicalAkhmedievTau P φ t)‖ := by
  rw [physicalMovingAkhmedievBreather, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (physicalAkhmedievAmplitude_pos P φ)]

theorem norm_physicalMovingMaBreather
    (P : BreatherPhysicalScales) (u : ℝ) (φ : MaAngle) (s t : ℝ) :
    ‖physicalMovingMaBreather P u φ s t‖ = physicalMaAmplitude P φ *
      ‖movingMaBreather u φ (physicalMaXi P φ s) (physicalMaTau P φ t)‖ := by
  rw [physicalMovingMaBreather, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (physicalMaAmplitude_pos P φ)]

theorem norm_physicalMovingAkhmedievBreather_reflection
    (P : BreatherPhysicalScales) (u : ℝ) (φ : BreatherAngle) (δ t : ℝ) :
    ‖physicalMovingAkhmedievBreather P u φ
        (physicalAkhmedievVelocity P u φ * t - δ) t‖ =
      ‖physicalMovingAkhmedievBreather P u φ
        (physicalAkhmedievVelocity P u φ * t + δ) t‖ := by
  rw [norm_physicalMovingAkhmedievBreather, norm_physicalMovingAkhmedievBreather]
  have hc := physicalAkhmediev_center_coordinates P u φ t
  have hsub : physicalAkhmedievXi P φ
      (physicalAkhmedievVelocity P u φ * t - δ) =
      u * physicalAkhmedievTau P φ t - physicalAkhmedievXi P φ δ := by
    simp only [physicalAkhmedievXi] at hc ⊢
    linear_combination hc
  have hadd : physicalAkhmedievXi P φ
      (physicalAkhmedievVelocity P u φ * t + δ) =
      u * physicalAkhmedievTau P φ t + physicalAkhmedievXi P φ δ := by
    simp only [physicalAkhmedievXi] at hc ⊢
    linear_combination hc
  rw [hsub, hadd, norm_movingAkhmedievBreather_reflection]

theorem norm_physicalMovingMaBreather_reflection
    (P : BreatherPhysicalScales) (u : ℝ) (φ : MaAngle) (δ t : ℝ) :
    ‖physicalMovingMaBreather P u φ (physicalMaVelocity P u φ * t - δ) t‖ =
      ‖physicalMovingMaBreather P u φ (physicalMaVelocity P u φ * t + δ) t‖ := by
  rw [norm_physicalMovingMaBreather, norm_physicalMovingMaBreather]
  have hc := physicalMa_center_coordinates P u φ t
  have hsub : physicalMaXi P φ (physicalMaVelocity P u φ * t - δ) =
      u * physicalMaTau P φ t - physicalMaXi P φ δ := by
    simp only [physicalMaXi] at hc ⊢
    linear_combination hc
  have hadd : physicalMaXi P φ (physicalMaVelocity P u φ * t + δ) =
      u * physicalMaTau P φ t + physicalMaXi P φ δ := by
    simp only [physicalMaXi] at hc ⊢
    linear_combination hc
  rw [hsub, hadd, norm_movingMaBreather_reflection]

theorem norm_physicalMovingAkhmedievBreather_periodic
    (P : BreatherPhysicalScales) (u : ℝ) (φ : BreatherAngle) (s t : ℝ) :
    ‖physicalMovingAkhmedievBreather P u φ
        (s + physicalAkhmedievSpatialPeriod P) t‖ =
      ‖physicalMovingAkhmedievBreather P u φ s t‖ := by
  rw [norm_physicalMovingAkhmedievBreather, norm_physicalMovingAkhmedievBreather,
    physicalAkhmedievXi_add_period, norm_movingAkhmedievBreather_periodic]

theorem norm_physicalMovingMaBreather_screw_periodic
    (P : BreatherPhysicalScales) (u : ℝ) (φ : MaAngle) (s t : ℝ) :
    ‖physicalMovingMaBreather P u φ
        (s + physicalMaVelocity P u φ * physicalMaTemporalPeriod P φ)
        (t + physicalMaTemporalPeriod P φ)‖ =
      ‖physicalMovingMaBreather P u φ s t‖ := by
  rw [norm_physicalMovingMaBreather, norm_physicalMovingMaBreather]
  have ht := physicalMaTau_add_period P φ t
  have ht0 := physicalMaTau_add_period P φ 0
  have hc := physicalMa_center_coordinates P u φ (physicalMaTemporalPeriod P φ)
  have hx : physicalMaXi P φ
      (s + physicalMaVelocity P u φ * physicalMaTemporalPeriod P φ) =
      physicalMaXi P φ s + u * maTemporalPeriod φ := by
    simp only [physicalMaXi] at hc ⊢
    simp only [physicalMaTau, mul_zero, zero_div, zero_add] at ht0
    rw [physicalMaTau] at hc
    rw [ht0] at hc
    linear_combination hc
  rw [hx, ht, norm_movingMaBreather_screw_periodic]

theorem norm_physicalMovingAkhmedievBreather_le_center
    (P : BreatherPhysicalScales) (u : ℝ) (φ : BreatherAngle) (s t : ℝ) :
    ‖physicalMovingAkhmedievBreather P u φ s t‖ ≤
      ‖physicalMovingAkhmedievBreather P u φ 0 0‖ := by
  rw [norm_physicalMovingAkhmedievBreather, norm_physicalMovingAkhmedievBreather]
  simp only [physicalAkhmedievXi, physicalAkhmedievTau, mul_zero, zero_div]
  have hzero : ‖movingAkhmedievBreather u φ 0 0‖ = ‖akhmedievBreather φ 0 0‖ := by
    simpa using norm_movingAkhmedievBreather u φ 0 0
  rw [hzero]
  exact mul_le_mul_of_nonneg_left (norm_movingAkhmedievBreather_le_center u φ _ _)
    (physicalAkhmedievAmplitude_pos P φ).le

theorem norm_physicalMovingMaBreather_le_center
    (P : BreatherPhysicalScales) (u : ℝ) (φ : MaAngle) (s t : ℝ) :
    ‖physicalMovingMaBreather P u φ s t‖ ≤ ‖physicalMovingMaBreather P u φ 0 0‖ := by
  rw [norm_physicalMovingMaBreather, norm_physicalMovingMaBreather]
  simp only [physicalMaXi, physicalMaTau, mul_zero, zero_div]
  have hzero : ‖movingMaBreather u φ 0 0‖ = ‖maBreather φ 0 0‖ := by
    simpa using norm_movingMaBreather u φ 0 0
  rw [hzero]
  exact mul_le_mul_of_nonneg_left (norm_movingMaBreather_le_center u φ _ _)
    (physicalMaAmplitude_pos P φ).le

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
