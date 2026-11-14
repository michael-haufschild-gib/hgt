import GaloisForLFunctions.GaloisTheoryOfZeros.Probability.GammaCoxDetection
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Laplace functional of finite Gamma-driven atomic intensities

Independent Gamma coordinates give an exact product Laplace functional.
Nonzero residuals disappear from its limit; a positive test at any true zero
forces the limiting Laplace functional to vanish.
-/

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators Classical NNReal
namespace GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox
noncomputable section

/-- The single-atom Laplace factor at a nonnegative test value. -/
def laplaceFactor (K r : ℝ) (t : ℝ≥0) : ℝ :=
  Real.exp (-K * Real.log (1 + (t : ℝ) * weight K r))

/-- Exact product Laplace functional, with Gamma integrals proved from their densities. -/
theorem gamma_product_laplace {ι : Type*} [Fintype ι]
    (K : ℝ) (hK : 0 < K) (g : ι → ℝ) (f : ι → ℝ≥0) :
    (∫ c : ι → ℝ, Real.exp (-(∑ i, (f i : ℝ) * weight K (g i) * c i))
      ∂Measure.pi (fun _ : ι => gammaMeasure K 1)) =
        ∏ i, laplaceFactor K (g i) (f i) := by
  letI : IsProbabilityMeasure (gammaMeasure K 1) :=
    isProbabilityMeasure_gammaMeasure hK zero_lt_one
  have hexp (c : ι → ℝ) :
      Real.exp (-(∑ i, (f i : ℝ) * weight K (g i) * c i)) =
        ∏ i, Real.exp (-((f i : ℝ) * weight K (g i) * c i)) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
  simp_rw [hexp]
  rw [integral_fintype_prod_eq_prod
    (μ := fun _ : ι => gammaMeasure K 1)
    (fun i (x : ℝ) => Real.exp (-((f i : ℝ) * weight K (g i) * x)))]
  apply Finset.prod_congr rfl
  intro i _
  have hw : 0 < weight K (g i) := Real.exp_pos _
  have ht : 0 ≤ (f i : ℝ) * weight K (g i) := mul_nonneg (f i).coe_nonneg hw.le
  rw [gamma_laplace K 1 _ hK zero_lt_one ht, one_div,
    Real.inv_rpow (by positivity : 0 ≤ 1 + (f i : ℝ) * weight K (g i)),
    ← Real.rpow_neg (by positivity : 0 ≤ 1 + (f i : ℝ) * weight K (g i)),
    Real.rpow_def_of_pos (by positivity : 0 < 1 + (f i : ℝ) * weight K (g i))]
  simp only [laplaceFactor, mul_comm]

/-- A nonnegative test's Laplace deficit is controlled by its mean weighted intensity. -/
theorem laplace_deficit_bounds (K r : ℝ) (t : ℝ≥0) (hK : 0 ≤ K) :
    0 ≤ 1 - laplaceFactor K r t ∧
      1 - laplaceFactor K r t ≤ (t : ℝ) * (K * weight K r) := by
  have hw : 0 < weight K r := Real.exp_pos _
  have ht : 0 ≤ (t : ℝ) * weight K r := mul_nonneg t.coe_nonneg hw.le
  have hl : 0 ≤ Real.log (1 + (t : ℝ) * weight K r) := Real.log_nonneg (by linarith)
  have hlog : Real.log (1 + (t : ℝ) * weight K r) ≤ (t : ℝ) * weight K r := by
    simpa using Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + (t : ℝ) * weight K r)
  constructor
  · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hK) hl))
  · have he := Real.add_one_le_exp (-K * Real.log (1 + (t : ℝ) * weight K r))
    have hm := mul_le_mul_of_nonneg_left hlog hK
    dsimp [laplaceFactor]
    nlinarith only [he, hm]

/-- The limiting factor remembers exactly whether its test sees a true zero. -/
theorem tendsto_laplaceFactor (r : ℝ) (t : ℝ≥0) :
    Tendsto (fun K => laplaceFactor K r t) atTop
      (𝓝 (if r = 0 ∧ t ≠ 0 then 0 else 1)) := by
  by_cases ht : t = 0
  · subst t
    simp [laplaceFactor]
  have htpos : 0 < (t : ℝ) := by exact_mod_cast pos_iff_ne_zero.mpr ht
  by_cases hr : r = 0
  · subst r
    have hl : 0 < Real.log (1 + (t : ℝ)) := Real.log_pos (by linarith)
    have h := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_mul_const hl)
    simpa [laplaceFactor, weight, ht, Function.comp_def, neg_mul] using h
  · have hzero : Tendsto (fun K => 1 - laplaceFactor K r t) atTop (𝓝 0) := by
      apply squeeze_zero'
        ((eventually_ge_atTop 0).mono fun K hK => (laplace_deficit_bounds K r t hK).1)
        ((eventually_ge_atTop 0).mono fun K hK => (laplace_deficit_bounds K r t hK).2)
      simpa only [mul_zero] using (tendsto_mean_nonzero r hr).const_mul (t : ℝ)
    simpa only [sub_sub_cancel, sub_zero, if_neg (not_and_of_not_left _ hr)] using
      (tendsto_const_nhds (x := (1 : ℝ))).sub hzero

/-- The full limiting Laplace functional is the product of the zero-visibility indicators. -/
theorem tendsto_laplace_product {ι : Type*} [Fintype ι] (g : ι → ℝ) (f : ι → ℝ≥0) :
    Tendsto (fun K => ∏ i, laplaceFactor K (g i) (f i)) atTop
      (𝓝 (∏ i, if g i = 0 ∧ f i ≠ 0 then (0 : ℝ) else 1)) :=
  tendsto_finsetProd Finset.univ (fun i _ => tendsto_laplaceFactor (g i) (f i))

end
end GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox

#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.gamma_product_laplace
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.laplace_deficit_bounds
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.tendsto_laplaceFactor
#print axioms GaloisForLFunctions.GaloisTheoryOfZeros.GammaCox.tendsto_laplace_product
