import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaAkhmedievQuarter
import Mathlib.Tactic

/-!
# Physical scaling of Brizard's dimensionless breathers

The substitutions preceding equation (35), `A=2k/p` and `ω=Dk²Ω/p²`, transport dimensionless
breather facts back to arclength and physical time.  Modulation cancels from the resulting physical
periods: Akhmediev spatial period is `2π/k`, while Ma magnitude period is `2π/ω`.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

abbrev PositiveScale := {x : ℝ // 0 < x}

structure BreatherPhysicalScales where
  circulation : PositiveScale
  waveNumber : PositiveScale

noncomputable def physicalAkhmedievAmplitude
    (P : BreatherPhysicalScales) (φ : BreatherAngle) : ℝ :=
  2 * (P.waveNumber : ℝ) / akhmedievWaveNumber φ

noncomputable def physicalAkhmedievFrequency
    (P : BreatherPhysicalScales) (φ : BreatherAngle) : ℝ :=
  (P.circulation : ℝ) * (P.waveNumber : ℝ) ^ (2 : ℕ) * akhmedievOmega φ /
    akhmedievWaveNumber φ ^ (2 : ℕ)

noncomputable def physicalMaAmplitude (P : BreatherPhysicalScales) (φ : MaAngle) : ℝ :=
  2 * (P.waveNumber : ℝ) / maWaveNumber φ

noncomputable def physicalMaFrequency (P : BreatherPhysicalScales) (φ : MaAngle) : ℝ :=
  (P.circulation : ℝ) * (P.waveNumber : ℝ) ^ (2 : ℕ) * maOmega φ / maWaveNumber φ ^ (2 : ℕ)

theorem physicalAkhmedievAmplitude_pos (P : BreatherPhysicalScales) (φ : BreatherAngle) :
    0 < physicalAkhmedievAmplitude P φ := by
  exact div_pos (mul_pos (by norm_num) P.waveNumber.property) (akhmedievWaveNumber_pos φ)

theorem physicalAkhmedievFrequency_pos (P : BreatherPhysicalScales) (φ : BreatherAngle) :
    0 < physicalAkhmedievFrequency P φ := by
  have hOmega : 0 < akhmedievOmega φ := by
    rw [akhmedievOmega]
    exact Real.sin_pos_of_pos_of_lt_pi
      (by linarith [φ.property.1]) (by linarith [φ.property.2, Real.pi_pos])
  exact div_pos
    (mul_pos (mul_pos P.circulation.property (sq_pos_of_pos P.waveNumber.property)) hOmega)
    (sq_pos_of_pos (akhmedievWaveNumber_pos φ))

theorem physicalMaAmplitude_pos (P : BreatherPhysicalScales) (φ : MaAngle) :
    0 < physicalMaAmplitude P φ := by
  exact div_pos (mul_pos (by norm_num) P.waveNumber.property) (maWaveNumber_pos φ)

theorem physicalMaFrequency_pos (P : BreatherPhysicalScales) (φ : MaAngle) :
    0 < physicalMaFrequency P φ := by
  exact div_pos (mul_pos (mul_pos P.circulation.property (sq_pos_of_pos P.waveNumber.property))
    (maOmega_pos φ)) (sq_pos_of_pos (maWaveNumber_pos φ))

theorem physicalAkhmedievAmplitude_scale (P : BreatherPhysicalScales) (φ : BreatherAngle) :
    physicalAkhmedievAmplitude P φ * akhmedievWaveNumber φ =
      2 * (P.waveNumber : ℝ) := by
  rw [physicalAkhmedievAmplitude]
  field_simp [ne_of_gt (akhmedievWaveNumber_pos φ)]

theorem physicalAkhmedievFrequency_scale (P : BreatherPhysicalScales) (φ : BreatherAngle) :
    physicalAkhmedievFrequency P φ * akhmedievWaveNumber φ ^ (2 : ℕ) =
      (P.circulation : ℝ) * (P.waveNumber : ℝ) ^ (2 : ℕ) * akhmedievOmega φ := by
  rw [physicalAkhmedievFrequency]
  field_simp [ne_of_gt (akhmedievWaveNumber_pos φ)]

theorem physicalMaAmplitude_scale (P : BreatherPhysicalScales) (φ : MaAngle) :
    physicalMaAmplitude P φ * maWaveNumber φ = 2 * (P.waveNumber : ℝ) := by
  rw [physicalMaAmplitude]
  field_simp [ne_of_gt (maWaveNumber_pos φ)]

theorem physicalMaFrequency_scale (P : BreatherPhysicalScales) (φ : MaAngle) :
    physicalMaFrequency P φ * maWaveNumber φ ^ (2 : ℕ) =
      (P.circulation : ℝ) * (P.waveNumber : ℝ) ^ (2 : ℕ) * maOmega φ := by
  rw [physicalMaFrequency]
  field_simp [ne_of_gt (maWaveNumber_pos φ)]

noncomputable def physicalAkhmedievXi
    (P : BreatherPhysicalScales) (φ : BreatherAngle) (s : ℝ) : ℝ :=
  (P.waveNumber : ℝ) * s / akhmedievWaveNumber φ

noncomputable def physicalAkhmedievTau
    (P : BreatherPhysicalScales) (φ : BreatherAngle) (t : ℝ) : ℝ :=
  physicalAkhmedievFrequency P φ * t / akhmedievOmega φ

noncomputable def physicalMaXi (P : BreatherPhysicalScales) (φ : MaAngle) (s : ℝ) : ℝ :=
  (P.waveNumber : ℝ) * s / maWaveNumber φ

noncomputable def physicalMaTau (P : BreatherPhysicalScales) (φ : MaAngle) (t : ℝ) : ℝ :=
  physicalMaFrequency P φ * t / maOmega φ

noncomputable def physicalAkhmedievBreather
    (P : BreatherPhysicalScales) (φ : BreatherAngle) (s t : ℝ) : ℂ :=
  (physicalAkhmedievAmplitude P φ : ℂ) *
    akhmedievBreather φ (physicalAkhmedievXi P φ s) (physicalAkhmedievTau P φ t)

noncomputable def physicalMaBreather
    (P : BreatherPhysicalScales) (φ : MaAngle) (s t : ℝ) : ℂ :=
  (physicalMaAmplitude P φ : ℂ) *
    maBreather φ (physicalMaXi P φ s) (physicalMaTau P φ t)

noncomputable def physicalAkhmedievSpatialPeriod (P : BreatherPhysicalScales) : ℝ :=
  2 * Real.pi / (P.waveNumber : ℝ)

noncomputable def physicalMaTemporalPeriod (P : BreatherPhysicalScales) (φ : MaAngle) : ℝ :=
  2 * Real.pi / physicalMaFrequency P φ

theorem physicalAkhmedievXi_add_period
    (P : BreatherPhysicalScales) (φ : BreatherAngle) (s : ℝ) :
    physicalAkhmedievXi P φ (s + physicalAkhmedievSpatialPeriod P) =
      physicalAkhmedievXi P φ s + akhmedievSpatialPeriod φ := by
  rw [physicalAkhmedievXi, physicalAkhmedievXi, physicalAkhmedievSpatialPeriod,
    akhmedievSpatialPeriod]
  field_simp [ne_of_gt P.waveNumber.property, ne_of_gt (akhmedievWaveNumber_pos φ)]

theorem physicalMaTau_add_period (P : BreatherPhysicalScales) (φ : MaAngle) (t : ℝ) :
    physicalMaTau P φ (t + physicalMaTemporalPeriod P φ) =
      physicalMaTau P φ t + maTemporalPeriod φ := by
  rw [physicalMaTau, physicalMaTau, physicalMaTemporalPeriod, maTemporalPeriod]
  field_simp [ne_of_gt (physicalMaFrequency_pos P φ), ne_of_gt (maOmega_pos φ)]

/-- Physical Akhmediev field has spatial period `2π/k`, independent of modulation angle. -/
theorem physicalAkhmedievBreather_periodic
    (P : BreatherPhysicalScales) (φ : BreatherAngle) (s t : ℝ) :
    physicalAkhmedievBreather P φ (s + physicalAkhmedievSpatialPeriod P) t =
      physicalAkhmedievBreather P φ s t := by
  rw [physicalAkhmedievBreather, physicalAkhmedievBreather,
    physicalAkhmedievXi_add_period, akhmedievBreather_periodic]

theorem norm_physicalAkhmedievBreather
    (P : BreatherPhysicalScales) (φ : BreatherAngle) (s t : ℝ) :
    ‖physicalAkhmedievBreather P φ s t‖ =
      physicalAkhmedievAmplitude P φ *
        ‖akhmedievBreather φ (physicalAkhmedievXi P φ s) (physicalAkhmedievTau P φ t)‖ := by
  rw [physicalAkhmedievBreather, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (physicalAkhmedievAmplitude_pos P φ)]

theorem norm_physicalMaBreather (P : BreatherPhysicalScales) (φ : MaAngle) (s t : ℝ) :
    ‖physicalMaBreather P φ s t‖ =
      physicalMaAmplitude P φ * ‖maBreather φ (physicalMaXi P φ s) (physicalMaTau P φ t)‖ := by
  rw [physicalMaBreather, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (physicalMaAmplitude_pos P φ)]

/-- Physical Akhmediev global peak inherited from the dimensionless profile. -/
theorem norm_physicalAkhmedievBreather_le_center
    (P : BreatherPhysicalScales) (φ : BreatherAngle) (s t : ℝ) :
    ‖physicalAkhmedievBreather P φ s t‖ ≤ ‖physicalAkhmedievBreather P φ 0 0‖ := by
  rw [norm_physicalAkhmedievBreather, norm_physicalAkhmedievBreather]
  simp only [physicalAkhmedievXi, physicalAkhmedievTau, mul_zero, zero_div]
  exact mul_le_mul_of_nonneg_left (norm_akhmedievBreather_le_center φ _ _)
    (physicalAkhmedievAmplitude_pos P φ).le

/-- Physical Ma magnitude has period `2π/ω`. -/
theorem norm_physicalMaBreather_periodic
    (P : BreatherPhysicalScales) (φ : MaAngle) (s t : ℝ) :
    ‖physicalMaBreather P φ s (t + physicalMaTemporalPeriod P φ)‖ =
      ‖physicalMaBreather P φ s t‖ := by
  rw [norm_physicalMaBreather, norm_physicalMaBreather, physicalMaTau_add_period,
    norm_maBreather_periodic]

theorem norm_physicalMaBreather_le_center
    (P : BreatherPhysicalScales) (φ : MaAngle) (s t : ℝ) :
    ‖physicalMaBreather P φ s t‖ ≤ ‖physicalMaBreather P φ 0 0‖ := by
  rw [norm_physicalMaBreather, norm_physicalMaBreather]
  simp only [physicalMaXi, physicalMaTau, mul_zero, zero_div]
  exact mul_le_mul_of_nonneg_left (norm_maBreather_le_center φ _ _)
    (physicalMaAmplitude_pos P φ).le

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
