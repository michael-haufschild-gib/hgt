import GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElasticaAkhmedievLocalization
import Mathlib.Tactic

/-!
# Physical-variable localization of Brizard's breathers

Positive coordinate scales transport both dimensionless asymptotes without changing their ends.
The physical background magnitudes are the paper amplitudes divided by `sqrt 2`.
-/

namespace GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica

open Filter

theorem tendsto_physicalAkhmedievTau_atTop
    (P : BreatherPhysicalScales) (φ : BreatherAngle) :
    Tendsto (physicalAkhmedievTau P φ) atTop atTop := by
  have hcoef : 0 < physicalAkhmedievFrequency P φ / akhmedievOmega φ :=
    div_pos (physicalAkhmedievFrequency_pos P φ) (akhmedievOmega_pos φ)
  have h := tendsto_id.const_mul_atTop hcoef
  apply h.congr'
  filter_upwards with t
  simp only [id_eq]
  rw [physicalAkhmedievTau]
  ring

theorem tendsto_physicalAkhmedievTau_atBot
    (P : BreatherPhysicalScales) (φ : BreatherAngle) :
    Tendsto (physicalAkhmedievTau P φ) atBot atBot := by
  have hcoef : 0 < physicalAkhmedievFrequency P φ / akhmedievOmega φ :=
    div_pos (physicalAkhmedievFrequency_pos P φ) (akhmedievOmega_pos φ)
  have h := tendsto_id.const_mul_atBot hcoef
  apply h.congr'
  filter_upwards with t
  simp only [id_eq]
  rw [physicalAkhmedievTau]
  ring

theorem tendsto_physicalMaXi_atTop (P : BreatherPhysicalScales) (φ : MaAngle) :
    Tendsto (physicalMaXi P φ) atTop atTop := by
  have hcoef : 0 < (P.waveNumber : ℝ) / maWaveNumber φ :=
    div_pos P.waveNumber.property (maWaveNumber_pos φ)
  have h := tendsto_id.const_mul_atTop hcoef
  apply h.congr'
  filter_upwards with s
  simp only [id_eq]
  rw [physicalMaXi]
  ring

theorem tendsto_physicalMaXi_atBot (P : BreatherPhysicalScales) (φ : MaAngle) :
    Tendsto (physicalMaXi P φ) atBot atBot := by
  have hcoef : 0 < (P.waveNumber : ℝ) / maWaveNumber φ :=
    div_pos P.waveNumber.property (maWaveNumber_pos φ)
  have h := tendsto_id.const_mul_atBot hcoef
  apply h.congr'
  filter_upwards with s
  simp only [id_eq]
  rw [physicalMaXi]
  ring

theorem tendsto_norm_physicalAkhmedievBreather_atTop
    (P : BreatherPhysicalScales) (φ : BreatherAngle) (s : ℝ) :
    Tendsto (fun t => ‖physicalAkhmedievBreather P φ s t‖) atTop
      (nhds (physicalAkhmedievAmplitude P φ * (Real.sqrt 2)⁻¹)) := by
  have h := (tendsto_norm_akhmedievBreather_atTop φ (physicalAkhmedievXi P φ s)).comp
    (tendsto_physicalAkhmedievTau_atTop P φ)
  have hscaled :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => physicalAkhmedievAmplitude P φ) atTop
        (nhds (physicalAkhmedievAmplitude P φ))).mul h
  apply hscaled.congr'
  filter_upwards with t
  simp only [Function.comp_apply]
  rw [norm_physicalAkhmedievBreather]

theorem tendsto_norm_physicalAkhmedievBreather_atBot
    (P : BreatherPhysicalScales) (φ : BreatherAngle) (s : ℝ) :
    Tendsto (fun t => ‖physicalAkhmedievBreather P φ s t‖) atBot
      (nhds (physicalAkhmedievAmplitude P φ * (Real.sqrt 2)⁻¹)) := by
  have h := (tendsto_norm_akhmedievBreather_atBot φ (physicalAkhmedievXi P φ s)).comp
    (tendsto_physicalAkhmedievTau_atBot P φ)
  have hscaled :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => physicalAkhmedievAmplitude P φ) atBot
        (nhds (physicalAkhmedievAmplitude P φ))).mul h
  apply hscaled.congr'
  filter_upwards with t
  simp only [Function.comp_apply]
  rw [norm_physicalAkhmedievBreather]

theorem tendsto_physicalMaBreather_atTop
    (P : BreatherPhysicalScales) (φ : MaAngle) (t : ℝ) :
    Tendsto (fun s => physicalMaBreather P φ s t) atTop
      (nhds ((physicalMaAmplitude P φ : ℂ) *
        (-linearPhase 1 0 (physicalMaTau P φ t) 0 / (Real.sqrt 2 : ℂ)))) := by
  have h := (tendsto_maBreather_atTop φ (physicalMaTau P φ t)).comp
    (tendsto_physicalMaXi_atTop P φ)
  have hscaled :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => (physicalMaAmplitude P φ : ℂ)) atTop
        (nhds (physicalMaAmplitude P φ : ℂ))).mul h
  apply hscaled.congr'
  filter_upwards with s
  simp only [Function.comp_apply]
  rw [physicalMaBreather]

theorem tendsto_physicalMaBreather_atBot
    (P : BreatherPhysicalScales) (φ : MaAngle) (t : ℝ) :
    Tendsto (fun s => physicalMaBreather P φ s t) atBot
      (nhds ((physicalMaAmplitude P φ : ℂ) *
        (-linearPhase 1 0 (physicalMaTau P φ t) 0 / (Real.sqrt 2 : ℂ)))) := by
  have h := (tendsto_maBreather_atBot φ (physicalMaTau P φ t)).comp
    (tendsto_physicalMaXi_atBot P φ)
  have hscaled :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => (physicalMaAmplitude P φ : ℂ)) atBot
        (nhds (physicalMaAmplitude P φ : ℂ))).mul h
  apply hscaled.congr'
  filter_upwards with s
  simp only [Function.comp_apply]
  rw [physicalMaBreather]

end GaloisForLFunctions.HTGeometry.DispersivePDE.BrizardElastica
