import GaloisForLFunctions.RHTower.SelbergMaassFullCurvatureBudget

/-!
# Finite actual modular hyperbolic area

The literal full modular domain lies in the half-height unit strip. The actual
primitive -1/y proves inverse-square tail integrability and its exact integral.
Product integration gives strip area two and hence a full-domain area bound.
-/

open Set Filter Topology MeasureTheory
namespace GaloisForLFunctions.RHTower.SelbergModularHyperbolicArea
open SelbergMaassFullCurvatureBudget SelbergModularDomainSlices
noncomputable section

/-- The literal negative reciprocal has inverse-square derivative off zero. -/
theorem inverse_primitive_hasDerivAt {y : ℝ} (hy : y ≠ 0) :
    HasDerivAt (fun t : ℝ => -1 / t) (1 / y ^ (2 : ℕ)) y := by
  have h := (hasDerivAt_const y (-1 : ℝ)).div (hasDerivAt_id y) hy
  apply h.congr_deriv
  simp

/-- The positive inverse-square derivative is integrable on every positive closed ray. -/
theorem inverse_square_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y : ℝ => 1 / y ^ (2 : ℕ)) (Ici a) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  exact integrableOn_Ioi_deriv_of_nonneg'
    (fun y hy => inverse_primitive_hasDerivAt (ha.trans_le hy).ne')
    (fun y _ => div_nonneg zero_le_one (sq_nonneg y))
    (tendsto_const_nhds.div_atTop tendsto_id)

/-- Exact inverse-square ray integral from the actual primitive and its limit. -/
theorem inverse_square_integral {a : ℝ} (ha : 0 < a) :
    (∫ y in Ici a, 1 / y ^ (2 : ℕ)) = 1 / a := by
  rw [integral_Ici_eq_integral_Ioi]
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun y hy => inverse_primitive_hasDerivAt (ha.trans_le hy).ne')
    (fun y _ => div_nonneg zero_le_one (sq_nonneg y))
    (tendsto_const_nhds.div_atTop tendsto_id)
  simpa only [zero_sub, neg_div, neg_neg] using h

/-- The unit horizontal strip above height one half. -/
def strip : Set (ℝ × ℝ) := Icc (-(1 / 2 : ℝ)) (1 / 2) ×ˢ Ici (1 / 2 : ℝ)

/-- The actual modular domain lies in the explicit half-height strip. -/
theorem fullDomain_subset_strip : fullDomain ⊆ strip :=
  fun _ hp => ⟨hp.1, (arcHeight_half_le hp.1).trans hp.2⟩

/-- The strip hyperbolic weight is integrable by genuine product integration. -/
theorem strip_weight_integrable : IntegrableOn (fun p : ℝ × ℝ => 1 / p.2 ^ (2 : ℕ)) strip := by
  have hx : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Icc (-(1 / 2 : ℝ)) (1 / 2)) volume :=
    continuous_const.integrableOn_Icc
  have hy := inverse_square_integrable (by norm_num : (0 : ℝ) < 1 / 2)
  rw [IntegrableOn, strip, Measure.volume_eq_prod, ← Measure.prod_restrict]
  simpa only [one_mul] using hx.mul_prod hy

/-- The explicit half-height unit strip has hyperbolic area two. -/
theorem strip_weight_integral : (∫ p in strip, 1 / p.2 ^ (2 : ℕ)) = 2 := by
  have h := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun _ : ℝ => (1 : ℝ)) (fun y : ℝ => 1 / y ^ (2 : ℕ))
    (Icc (-(1 / 2 : ℝ)) (1 / 2)) (Ici (1 / 2 : ℝ))
  simp only [one_mul] at h
  rw [inverse_square_integral (by norm_num : (0 : ℝ) < 1 / 2), setIntegral_const,
    Real.volume_real_Icc_of_le (by norm_num : -(1 / 2 : ℝ) ≤ 1 / 2)] at h
  norm_num at h
  simpa only [← Measure.volume_eq_prod, strip, one_div] using h

/-- The actual full modular domain has integrable hyperbolic area density. -/
theorem full_weight_integrable : IntegrableOn (fun p : ℝ × ℝ => 1 / p.2 ^ (2 : ℕ)) fullDomain :=
  strip_weight_integrable.mono_set fullDomain_subset_strip

/-- The actual full modular hyperbolic area is bounded by two. -/
theorem full_weight_integral_le_two : (∫ p in fullDomain, 1 / p.2 ^ (2 : ℕ)) ≤ 2 := by
  rw [← strip_weight_integral]
  exact setIntegral_mono_set strip_weight_integrable
    (Eventually.of_forall (fun p : ℝ × ℝ => div_nonneg zero_le_one (sq_nonneg p.2)))
    (Eventually.of_forall fullDomain_subset_strip)

end
end GaloisForLFunctions.RHTower.SelbergModularHyperbolicArea
