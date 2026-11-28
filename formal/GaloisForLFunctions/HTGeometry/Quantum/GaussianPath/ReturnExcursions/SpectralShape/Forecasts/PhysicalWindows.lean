import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.CircuitWindings
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.Forecasts.ConditionalShape

/-! # Exterior-field forecasts of all late physical circuit windings -/

open MeasureTheory ProbabilityTheory Filter Set Finset WithLp Real
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
open Dephasing.PairedFields SharpOccupation
noncomputable section
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

/-- The variance per site of the original Gaussian path tends to twelve. -/
theorem regular_shells : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
    let K : ℝ := (n+2:ℕ)
    ‖pathPauliDisorderShell ω n‖^2∈Icc K (13*K) := by
  filter_upwards [SpectralGapMass.Bulk.gaussian_variance_per_site] with ω hw
  filter_upwards [hw.eventually_const_lt (by norm_num : (1:ℝ)<12),
    hw.eventually_lt_const (by norm_num : (12:ℝ)<13)] with n hl hu
  intro K
  have hK : 0<K := by dsimp only [K]; positivity
  rw [EuclideanSpace.real_norm_sq_eq]
  exact ⟨by simpa only [one_mul] using ((lt_div_iff₀ hK).mp hl).le,((div_lt_iff₀ hK).mp hu).le⟩

/-- At least one laboratory circuit fits at a late date with a winding shape
forecast from the exterior of the designated bond. -/
def forecastHit {n m : ℕ} (e : Fin (n+1)) (f : Fin m → (Exterior e→ℝ) → ℝ)
    (T ε : ℝ) (h : PathShell n) : Prop :=
  ∃ t≥T, ∃ C : TwoQubitCircuit (n+2), ∃ w : (Fin (n+2)→Bool) → ℤ,
    windingFit h C.eval w t ε ∧ ∃ j, windingShape w=f j (outside e h)

private theorem hit_sublevel {n : ℕ} {h : PathShell n} {c T x r : ℝ} (hh : classHit c T x h)
    (hT : 0<T) (hx : 0≤x) (hres : 16*x≤T*sqrt ((n+2:ℕ):ℝ))
    (hcut : 16000*x*sqrt (13*((n+2:ℕ):ℝ))^5<T*((2/3)*r^6))
    (hv : ‖h‖^2∈Icc ((n+2:ℕ):ℝ) (13*((n+2:ℕ):ℝ))) :
    |skewConstraint c h|<(2/3)*r^6 := by
  obtain ⟨b,hb,t,ht,p,hfit⟩ := hh
  have hlo := sqrt_le_iff.mpr ⟨norm_nonneg h,hv.1⟩
  have hhi := le_sqrt_of_sq_le hv.2
  have ht' := hT.trans_le ht
  have hR := (sqrt_pos.mpr (by positivity : (0:ℝ)<((n+2:ℕ):ℝ))).trans_le hlo
  have hbound := template_constraint h b (Equiv.refl _) ht' hR hx
    (hres.trans (mul_le_mul ht hlo (sqrt_nonneg _) ht'.le)) hfit
  rw [hb] at hbound
  apply lt_of_mul_lt_mul_left (a:=T) _ hT.le
  exact ((mul_le_mul_of_nonneg_right ht (abs_nonneg _)).trans hbound).trans_lt
    ((mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hhi 5) (by positivity)).trans_lt hcut)

/-- Even after conditioning on a measurable exterior event, m forecasts selected
from the other couplings cost at most 12mr times that event's probability.
The single variance restriction is eventually satisfied on almost every chain. -/
theorem gaussian_forecast_window {n m : ℕ} (e : Fin (n+1)) (f : Fin m → (Exterior e→ℝ) → ℝ)
    (hf : ∀ j, Measurable (f j)) (D : Set (Exterior e→ℝ)) (hD : MeasurableSet D) (T ε r : ℝ) :
    let K : ℝ := (n+2:ℕ)
    let x := π*(1+physicalArc ε)
    let Z (ω) := pathPauliDisorderShell ω n
    let O := (fun ω => outside e (Z ω)) ⁻¹' D
    ε∈Ioo (0:ℝ) (sqrt 2) → 0<T → 0<r → 16*x≤T*sqrt K →
    16000*x*(sqrt (13*K))^5<T*((2/3)*r^6) →
    pathPauliDisorderLaw.real ({ω | ‖Z ω‖^2∈Icc K (13*K) ∧ forecastHit e f T ε (Z ω)} ∩ O)
      ≤ (m:ℝ)*(12*r)*pathPauliDisorderLaw.real O := by
  intro K x Z O he hT hr hres hcut
  let A (j : Fin m) := {h : PathShell n | |skewConstraint (f j (outside e h)) h|<(2/3)*r^6}
  let B := outside e ⁻¹' D
  have hB : MeasurableSet B := hD.preimage (measurable_outside e)
  have ha (j) : MeasurableSet (A j) :=
    measurableSet_lt (measurable_forecast_discrepancy e _ (hf j)).abs measurable_const
  have hmap : MeasurePreserving Z pathPauliDisorderLaw (stdGaussian (PathShell n)) := by
    have hT : MeasurePreserving (toLp 2 : Coeff n → PathShell n) (fieldLaw n) (stdGaussian (PathShell n)) :=
      ⟨(MeasurableEquiv.toLp 2 (Coeff n)).measurable,map_pi_eq_stdGaussian⟩
    exact hT.comp (BlockDilations.prefix_measure n)
  have hprice (j) : pathPauliDisorderLaw.real (Z ⁻¹' (A j ∩ B))≤12*r*pathPauliDisorderLaw.real O := by
    change _ ≤ _*pathPauliDisorderLaw.real (Z ⁻¹' B)
    rw [hmap.measureReal_preimage ((ha j).inter hB).nullMeasurableSet,hmap.measureReal_preimage hB.nullMeasurableSet]
    have hh := conditional_shape_price e (f j) (hf j) D hD hr
    have hh' := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hh
    rwa [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : 0≤12*r)] at hh'
  have hx : 0≤x := mul_nonneg pi_pos.le (by linarith only [(physicalArc_spec he.1 he.2).1.1])
  calc
    _ ≤ pathPauliDisorderLaw.real (⋃ j : Fin m, Z ⁻¹' (A j ∩ B)) := by
      apply measureReal_mono _ (measure_ne_top _ _)
      rintro ω ⟨⟨hv,t,ht,C,w,hw,j,hc⟩,hO⟩
      have hb := hit_sublevel (class_of_fit _ C.eval w ht hw) hT hx hres hcut hv
      rw [hc] at hb
      exact mem_iUnion.mpr ⟨j,hb,hO⟩
    _ ≤ ∑ j : Fin m, pathPauliDisorderLaw.real (Z ⁻¹' (A j ∩ B)) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin m, 12*r*pathPauliDisorderLaw.real O := sum_le_sum fun j _ => hprice j
    _ = _ := by simp [mul_assoc]

#print axioms gaussian_forecast_window
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
