import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.SelectedCoordinates
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Gaussian mass from the number of successful coordinate dilations -/

open MeasureTheory ProbabilityTheory Set Finset
namespace GaloisForLFunctions.HTGeometry.BlockDilations
noncomputable section
variable {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]

private theorem measurable_expand (S : Finset ι) (a : ℝ) : Measurable (expand S a) := by
  apply measurable_pi_lambda
  intro i
  by_cases h : i∈S
  · simpa only [expand,if_pos h] using (measurable_pi_apply i).const_mul a
  · simpa only [expand,if_neg h] using (measurable_pi_apply (X:=fun _ : ι => ℝ) i)

/-- The mass of an event times the sum of reciprocal Gaussian
Jacobians is bounded by the expected number of dilations landing in it. -/
theorem gaussian_pattern_mass (S : J→Finset ι) {a : ℝ} (ha : 1≤a)
    {E : Set (ι→ℝ)} (hE : MeasurableSet E) :
    open Classical in
    let μ := Measure.pi fun _ : ι => gaussianReal 0 1
    μ.real E*(∑ j, (a^(S j).card)⁻¹) ≤
      ∫ x, ((univ.filter fun j => expand (S j) a x∈E).card:ℝ) ∂μ := by
  classical
  intro μ
  let T := fun j => expand (S j) a ⁻¹' E
  have hT (j : J) : MeasurableSet (T j) := hE.preimage (measurable_expand _ _)
  have h (j : J) : μ.real E*(a^(S j).card)⁻¹≤μ.real (T j) := by
    rw [←div_eq_mul_inv,div_le_iff₀ (pow_pos (zero_lt_one.trans_le ha) _),mul_comm]
    exact selected_gaussian_comparison (S j) ha hE
  rw [mul_sum]
  apply (sum_le_sum (fun j _ => h j)).trans
  let f := fun j => (T j).indicator (1 : (ι→ℝ)→ℝ)
  have hf (j : J) : Integrable (f j) μ := (integrable_const (1:ℝ)).indicator (hT j)
  have he (j : J) : μ.real (T j)=∫ x, f j x ∂μ := (integral_indicator_one (hT j)).symm
  simp_rw [he]
  rw [←integral_finsetSum _ (fun j _ => hf j)]
  apply le_of_eq
  apply integral_congr_ae
  filter_upwards with x
  change ∑ j, (T j).indicator (1 : (ι→ℝ)→ℝ) x = _
  simpa only [Set.indicator_apply,Pi.one_apply,T,mem_preimage] using
    (sum_boole (R:=ℝ) (fun j => expand (S j) a x∈E) univ)

#print axioms gaussian_pattern_mass
end
end GaloisForLFunctions.HTGeometry.BlockDilations
