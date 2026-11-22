import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.FieldBox
import GaloisForLFunctions.HTGeometry.ComplexGaussianCoefficientProbability

/-! # Uniform probability of detecting a calibrated response -/
open MeasureTheory ProbabilityTheory Set
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section

/-- A fixed number of Gaussian fields preserves a common detectable
response except on any prescribed fraction of draws. The threshold is
uniform over the response and over calibrations in a fixed box. -/
theorem gaussian_fields_signal (n : ℕ) {a h η : ℝ} (hh : 0<h) (hη : 0<η)
    (M : ℝ → ℝ) (hM : ∀ R, 0≤M R) :
    ∃ ε : ℝ, 0<ε ∧ ∀ (F : (Fin n → ℝ) → ℝ), Continuous F → (∀ i, EntireFieldSlice F M i) →
      ∀ u : Fin n → ℝ, (∀ i, |u i|≤a) → h≤|F u| →
        (Measure.pi (fun _ : Fin n => gaussianReal 0 1)) {x | |F x|≤ε} ≤ ENNReal.ofReal η := by
  let δ := η/(2*((n:ℝ)+1))
  have hδ : 0<δ := by dsimp only [δ]; positivity
  let b := max a (max 1 δ⁻¹)
  have ha : a≤b := le_max_left ..
  have hb1 : 1≤b := (le_max_left ..).trans (le_max_right ..)
  have hb : 0<b := zero_lt_one.trans_le hb1
  have hbi : δ⁻¹≤b := (le_max_right ..).trans (le_max_right ..)
  have htail : (b^2)⁻¹ ≤ δ := by
    rw [inv_le_comm₀ (pow_pos hb _) hδ]
    exact hbi.trans (by nlinarith only [hb,hb1,mul_le_mul_of_nonneg_right hb1 hb.le])
  obtain ⟨ε,hε,hbox⟩ := gaussian_field_box n hb hh hδ M hM
  refine ⟨ε,hε,?_⟩
  intro F hc hf u hu hcal
  let μ := Measure.pi (fun _ : Fin n => gaussianReal 0 1)
  let S := {x : Fin n → ℝ | (∀ i, x i ∈ Ioo (-b) b) ∧ |F x|≤ε}
  let C (i : Fin n) := {x : Fin n → ℝ | b≤|x i|}
  have hS : μ S≤n*ENNReal.ofReal δ := hbox F hc hf u (fun i => (hu i).trans ha) hcal
  have hC (i : Fin n) : μ (C i)≤ENNReal.ofReal δ := by
    have he := (measurePreserving_eval (fun _ : Fin n => gaussianReal 0 1) i).measure_preimage
      (s := {x : ℝ | b≤|x|}) (isClosed_le continuous_const continuous_abs).measurableSet.nullMeasurableSet
    exact he.le.trans ((measure_abs_ge_le hb).trans (ENNReal.ofReal_le_ofReal htail))
  have hU : μ (⋃ i, C i)≤n*ENNReal.ofReal δ := by
    refine (measure_iUnion_fintype_le μ C).trans ((Finset.sum_le_sum (fun i _ => hC i)).trans_eq ?_)
    simp
  have hsub : {x | |F x|≤ε} ⊆ S ∪ ⋃ i, C i := by
    intro x hx
    by_cases hx' : ∀ i, |x i|<b
    · exact Or.inl ⟨fun i => abs_lt.mp (hx' i),hx⟩
    · push Not at hx'
      obtain ⟨i,hi⟩ := hx'
      exact Or.inr (mem_iUnion.mpr ⟨i,hi⟩)
  apply (measure_mono hsub).trans ((measure_union_le _ _).trans ((add_le_add hS hU).trans ?_))
  have he : (n:ℝ)*δ+n*δ≤η := by
    have hv : 2*((n:ℝ)+1)*δ=η := by dsimp only [δ]; field_simp
    linarith only [hv,hδ]
  simpa only [ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg n) hδ.le) (mul_nonneg (Nat.cast_nonneg n) hδ.le),
    ENNReal.ofReal_mul (Nat.cast_nonneg n),ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal he

end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
