import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.Resolution.Resampling
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.Resolution.AngularSlope
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.Forecasts.PhysicalWindows

/-! # Physical windings with two unobserved onsite couplings -/

open MeasureTheory Set Finset Real WithLp Function
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
open Dephasing.PairedFields Dephasing.PairedFields.ClockAdjustment SharpOccupation
noncomputable section
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

/-- Couplings observable when only two adjacent onsite fields are withheld. -/
abbrev PairExterior {n : ℕ} (e : Fin (n+1)) :=
  {i : PathLabel n // i≠leftSite e 0 ∧ i≠rightSite e 0}

def pairReadings {n : ℕ} (e : Fin (n+1)) (h : Coeff n) (i : PairExterior e) : ℝ := h i.val

/-- Every fitting date and every implementing circuit share the physical
variance and the cubic trace. The date pays for the accuracy of the shape. -/
private theorem finite_shape_error {n : ℕ} {h : PathShell n} {c T x : ℝ} (hh : classHit c T x h)
    (hT : 0<T) (hx : 0≤x) (hres : 16*x≤T*sqrt ((n+2:ℕ):ℝ))
    (hv : ‖h‖^2∈Icc ((n+2:ℕ):ℝ) (13*((n+2:ℕ):ℝ))) :
    |skewConstraint c h|≤16000*x*(sqrt (13*((n+2:ℕ):ℝ)))^5/T := by
  obtain ⟨b,hb,t,ht,p,hfit⟩ := hh
  have hlo := sqrt_le_iff.mpr ⟨norm_nonneg h,hv.1⟩
  have hhi := le_sqrt_of_sq_le hv.2
  have ht' := hT.trans_le ht
  have hR := (sqrt_pos.mpr (by positivity : (0:ℝ)<((n+2:ℕ):ℝ))).trans_le hlo
  have hh := template_constraint h b (Equiv.refl _) ht' hR hx
    (hres.trans (mul_le_mul ht hlo (sqrt_nonneg _) ht'.le)) hfit
  rw [hb] at hh
  rw [le_div_iff₀ hT,mul_comm _ T]
  exact ((mul_le_mul_of_nonneg_right ht (abs_nonneg _)).trans hh).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hhi 5) (by positivity))

/-- A winding at any later date has a shape in the list selected by the
observed fields. Neither its circuit nor its time needs to be prescribed. -/
def pairHit {n m : ℕ} (e : Fin (n+1)) (f : Fin m → (PairExterior e→ℝ) → ℝ)
    (T ε : ℝ) (h : PathShell n) : Prop :=
  ∃ t≥T, ∃ C : TwoQubitCircuit (n+2), ∃ w,
    windingFit h C.eval w t ε ∧ ∃ j, windingShape w=f j (pairReadings e h.ofLp)

/-- On the physical variance and derivative event, seeing any of m forecast
shapes costs at most 24mρ times the probability of any exterior selection. -/
theorem resolved_forecast_window {n m : ℕ} (e : Fin (n+1)) (f : Fin m → (PairExterior e→ℝ) → ℝ)
    (hf : ∀ j, Measurable (f j)) (O : Set (PairExterior e→ℝ)) (hO : MeasurableSet O) (T ε r ρ : ℝ) :
    let K : ℝ := (n+2:ℕ)
    let x := π*(1+physicalArc ε)
    let Z (ω) := pathPauliDisorderShell ω n
    let D := (fun ω => pairReadings e (Z ω).ofLp) ⁻¹' O
    ε∈Ioo (0:ℝ) (sqrt 2) → 0<T → 0<r → 0<ρ → 16*x≤T*sqrt K →
    6*(16000*x*(sqrt (13*K))^5/T)<ρ*(r^6/(1+13*K)) →
    pathPauliDisorderLaw.real ({ω | ‖Z ω‖^2∈Icc K (13*K) ∧ resolvedEdge (Z ω).ofLp e r ∧
      pairHit e f T ε (Z ω)} ∩ D) ≤ (m:ℝ)*(24*ρ)*pathPauliDisorderLaw.real D := by
  intro K x Z D he hT hr hρ hdate hres
  let μ := pathPauliDisorderLaw
  let X (ω) : Coeff n := (Z ω).ofLp
  let B := pairReadings e ⁻¹' O
  let κ := r^6/(1+13*K)
  let δ := 16000*x*(sqrt (13*K))^5/T
  let c (j : Fin m) (h : Coeff n) := f j (pairReadings e h)
  let S (j : Fin m) (p) := {h : Coeff n | |skewConstraint (c j h) (toLp 2 h)|≤δ ∧ κ≤|shapeSlope (c j h) h p|}
  have hm : Measurable (pairReadings e) := measurable_pi_lambda _ fun i => measurable_pi_apply i.val
  have hB : MeasurableSet B := hO.preimage hm
  have price (j : Fin m) (p) (hp : ∀ i : PairExterior e, i.val≠p) :
      μ.real (X ⁻¹' (S j p ∩ B))≤12*ρ*μ.real D := by
    have hfix (h : Coeff n) (u : ℝ) : pairReadings e (update h p u)=pairReadings e h :=
      funext fun i => update_of_ne (hp i) _ _
    have hc := (hf j).comp hm
    have hh := resampled_shape_bound p (c j) hc (fun h u => congrArg (f j) (hfix h u)) B hB
      (fun h u => by change pairReadings e (update h p u)∈O ↔ pairReadings e h∈O; rw [hfix]) hρ hres
    have hH := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hh
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity : 0≤12*ρ)] at hH
    obtain ⟨hJ,hs⟩ := measurable_readings p (c j) hc
    have hS : MeasurableSet (S j p) := (measurableSet_le hJ.abs measurable_const).inter
      (measurableSet_le measurable_const hs.abs)
    change μ.real (X ⁻¹' (S j p ∩ B))≤12*ρ*μ.real (X ⁻¹' B)
    rw [(BlockDilations.prefix_measure n).measureReal_preimage ((hS.inter hB).nullMeasurableSet),
      (BlockDilations.prefix_measure n).measureReal_preimage hB.nullMeasurableSet]
    exact hH
  let A (j : Fin m) := X ⁻¹' (S j (leftSite e 0) ∩ B) ∪ X ⁻¹' (S j (rightSite e 0) ∩ B)
  have hA (j) : μ.real (A j)≤24*ρ*μ.real D := by
    apply (measureReal_union_le ..).trans
    linarith only [price j _ (fun i => i.property.1),price j _ (fun i => i.property.2)]
  have hx : 0≤x := mul_nonneg pi_pos.le (by linarith only [(physicalArc_spec he.1 he.2).1.1])
  calc
    _ ≤ μ.real (⋃ j : Fin m, A j) := by
      apply measureReal_mono _ (measure_ne_top _ _)
      rintro ω ⟨⟨hv,hg,t,ht,C,w,hw,j,hj⟩,hO'⟩
      have hδ := finite_shape_error (class_of_fit _ C.eval w ht hw) hT hx hdate hv
      rw [hj] at hδ
      refine mem_iUnion.mpr ⟨j,?_⟩
      rcases large_coordinate_slope (X ω) e hr hg hv.2 (c j (X ω)) with hl | hu
      · exact Or.inl ⟨⟨hδ,hl⟩,hO'⟩
      · exact Or.inr ⟨⟨hδ,hu⟩,hO'⟩
    _ ≤ ∑ j : Fin m, μ.real (A j) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin m, 24*ρ*μ.real D := sum_le_sum fun j _ => hA j
    _ = _ := by simp [μ,mul_assoc]

#print axioms resolved_forecast_window
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
