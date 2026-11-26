import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrefixCoordinates.SubsetEnergy

/-! # Gaussian energy beside seams selected from independent bond data -/

open MeasureTheory ProbabilityTheory Real Finset Set
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
noncomputable section

/-- Select a set of at most m coordinates from independent data. Its
Gaussian square-energy tail has the fixed-set bound, uniform in the
number of possible choices. -/
theorem selected_neighbour_tail {Y I : Type*} [MeasurableSpace Y] [Fintype I] [DecidableEq I]
    (ν : Measure Y) [IsProbabilityMeasure ν] (S : Y→Finset I)
    (hS : ∀ i, MeasurableSet {y | i∈S y}) (m : ℕ) (hm : ∀ y, (S y).card ≤ m) (B : ℝ) :
    let μ := Measure.pi fun _ : I => gaussianReal 0 1
    let E := {p : Y × (I→ℝ) | B≤∑ i ∈ S p.1, (p.2 i)^2}
    (ν.prod μ).real E ≤ (sqrt 2)^m/exp (B/4) := by
  classical
  intro μ E
  let b := (sqrt 2)^m/exp (B/4)
  have hb : 0≤b := div_nonneg (pow_nonneg (sqrt_nonneg _) _) (exp_pos _).le
  have hmeas : MeasurableSet E := by
    apply measurableSet_le measurable_const
    have hs (p : Y × (I→ℝ)) : (∑ i ∈ S p.1, (p.2 i)^2)=
        ∑ i : I, if i∈S p.1 then (p.2 i)^2 else 0 := by
      rw [←sum_filter]
      simp
    simp_rw [hs]
    exact Finset.measurable_fun_sum _ fun i _ =>
      Measurable.ite ((hS i).preimage measurable_fst) (by fun_prop) measurable_const
  have hrow (y : Y) : μ (Prod.mk y ⁻¹' E) ≤ ENNReal.ofReal b := by
    have h := GaussianCoordinates.gaussian_seam_square_tail (S y) B
    have hcount : (sqrt 2)^(S y).card≤(sqrt 2)^m :=
      pow_le_pow_right₀ (by norm_num) (hm y)
    have hh : μ.real (Prod.mk y ⁻¹' E)≤b := by
      apply (le_div_iff₀ (exp_pos _)).mpr
      rw [mul_comm]
      exact h.trans hcount
    simpa only [measureReal_def,ENNReal.ofReal_toReal (measure_ne_top _ _)] using ENNReal.ofReal_le_ofReal hh
  have hμ : (ν.prod μ) E≤ENNReal.ofReal b := by
    rw [Measure.prod_apply hmeas]
    simpa only [lintegral_const,measure_univ,mul_one] using lintegral_mono hrow
  simpa only [measureReal_def,ENNReal.toReal_ofReal hb] using ENNReal.toReal_mono ENNReal.ofReal_ne_top hμ

#print axioms selected_neighbour_tail
end
end GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
