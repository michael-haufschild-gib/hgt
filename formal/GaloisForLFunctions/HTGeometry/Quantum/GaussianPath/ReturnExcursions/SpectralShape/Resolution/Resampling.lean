import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.Resolution.Coordinate
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.Resolution.RootDistance

/-! # Linear resolution on a single withheld Gaussian coupling -/

open ProbabilityTheory MeasureTheory Set WithLp Function
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
open Dephasing.PairedFields Dephasing.PairedFields.ClockAdjustment
noncomputable section

theorem measurable_readings {n : ℕ} (p : PathLabel n) (f : Coeff n → ℝ) (hf : Measurable f) :
    Measurable (fun h => skewConstraint (f h) (toLp 2 h)) ∧ Measurable (fun h => shapeSlope (f h) h p) := by
  have hH : Continuous (fun h : Coeff n => (generator h).val) := by
    simp only [generator,pathHamiltonian_eq_sum]
    fun_prop
  have hM : Continuous (fun h : Coeff n => thirdMoment (toLp 2 h)) := by
    change Continuous (fun h : Coeff n => (((generator h).val^3).trace.re)/(2:ℝ)^(n+2))
    fun_prop
  have ha : Continuous (fun h : Coeff n => cubicSlope h p) := by
    unfold cubicSlope squareTrace
    fun_prop
  have hV : Measurable (fun h : Coeff n => ‖toLp 2 h‖^2) :=
    (continuous_norm.measurable.comp (MeasurableEquiv.toLp 2 (Coeff n)).measurable).pow_const 2
  constructor
  · exact (hM.measurable.pow_const 2).sub (hf.mul (hV.pow_const 3))
  · unfold shapeSlope
    fun_prop

/-- Conditional on any event independent of the chosen coordinate, the resolved
part of a sextic sublevel has probability proportional to tolerance divided by slope.
The forecast may depend on all the other coordinates. -/
theorem resampled_shape_bound {n : ℕ} (p : PathLabel n) (f : Coeff n → ℝ) (hf : Measurable f)
    (hfix : ∀ h x, f (update h p x)=f h) (B : Set (Coeff n)) (hB : MeasurableSet B)
    (hBfix : ∀ h x, update h p x∈B ↔ h∈B) {δ κ ρ : ℝ} (hρ : 0<ρ) (hres : 6*δ<ρ*κ) :
    let S := {h | |skewConstraint (f h) (toLp 2 h)|≤δ ∧ κ≤|shapeSlope (f h) h p|}
    (fieldLaw n) (S ∩ B) ≤ ENNReal.ofReal (12*ρ)*(fieldLaw n) B := by
  intro S
  let μ := fieldLaw n
  let γ := gaussianReal 0 1
  let a := ENNReal.ofReal (12*ρ)
  obtain ⟨hJ,hslope⟩ := measurable_readings p f hf
  have hS : MeasurableSet S := (measurableSet_le hJ.abs measurable_const).inter
    (measurableSet_le measurable_const hslope.abs)
  have hU := PrefixCouplings.resample_preserving γ p
  simp only [Measure.infinitePi_eq_pi] at hU
  have sample (A : Set (Coeff n)) (hm : MeasurableSet A) :
      μ A=∫⁻ h, γ {x | update h p x∈A} ∂μ := by
    rw [←hU.measure_preimage hm.nullMeasurableSet,Measure.prod_apply (hm.preimage hU.measurable)]
    rfl
  have slice (h : Coeff n) : γ {x | update h p x∈S}≤a := by
    obtain ⟨Q,hd,hQ⟩ := coordinate_polynomial (f h) h p
    have hd' : (Q.natDegree:ℝ)≤6 := by exact_mod_cast hd
    rw [←ofReal_measureReal (measure_ne_top _ _)]
    apply ENNReal.ofReal_le_ofReal
    refine (measureReal_mono ?_ (measure_ne_top _ _)).trans ((gaussian_resolved_sublevel Q hρ).trans ?_)
    · intro x hx
      change |skewConstraint (f (update h p x)) (toLp 2 (update h p x))|≤δ ∧
        κ≤|shapeSlope (f (update h p x)) (update h p x) p| at hx
      rw [hfix h x] at hx
      change _*‖Q.eval (x:ℂ)‖<ρ*‖Q.derivative.eval (x:ℂ)‖
      rw [(hQ x).1,(hQ x).2,Complex.norm_real,Complex.norm_real,Real.norm_eq_abs,Real.norm_eq_abs]
      exact ((mul_le_mul hd' hx.1 (abs_nonneg _) (by norm_num)).trans_lt hres).trans_le
        (mul_le_mul_of_nonneg_left hx.2 hρ.le)
    · linarith only [mul_le_mul_of_nonneg_right hd' hρ.le]
  rw [sample _ (hS.inter hB),sample _ hB,←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro h
  dsimp only
  by_cases hh : h∈B
  · rw [show {x : ℝ | update h p x∈B}=univ from eq_univ_of_forall fun x => (hBfix h x).mpr hh,
      measure_univ,mul_one]
    exact (measure_mono (fun _ hx => hx.1)).trans (slice h)
  · rw [show {x : ℝ | update h p x∈S ∩ B}=∅ from eq_empty_iff_forall_notMem.mpr
      (fun x hx => hh ((hBfix h x).mp hx.2)),measure_empty]
    exact zero_le

#print axioms resampled_shape_bound
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
