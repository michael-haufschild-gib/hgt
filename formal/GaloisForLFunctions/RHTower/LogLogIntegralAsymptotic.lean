import GaloisForLFunctions.HTGeometry.LogExpTailIntegral

/-!
# The logarithmic-logarithmic integral near the abscissa

The substitution `u = δ log t` turns the weighted `log log` integral into the logarithmic moment of
the exponential density:

```text
δ ∫_2^T t^(-δ-1) log log t dt = ∫_{δ log 2}^{δ log T} (log u - log δ) e^(-u) du.
```

Letting `T → ∞` and then `δ → 0⁺` gives

```text
δ ∫_2^∞ t^(-δ-1) log log t dt + log δ → -γ.
```
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## The substitution -/

theorem integral_logLog_change_of_variables {δ : ℝ} (hδ : 0 < δ) {T : ℝ} (hT : 2 ≤ T) :
    (∫ t in (2 : ℝ)..T, δ * (t ^ (-δ - 1) * Real.log (Real.log t))) =
      ∫ u in (δ * Real.log 2)..(δ * Real.log T),
        (Real.log u - Real.log δ) * Real.exp (-u) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have huIcc : uIcc (2 : ℝ) T = Icc (2 : ℝ) T := uIcc_of_le hT
  have hderiv : ∀ x ∈ uIcc (2 : ℝ) T,
      HasDerivAt (fun t : ℝ => δ * Real.log t) (δ / x) x := by
    intro x hx
    rw [huIcc] at hx
    have hx2 : (2 : ℝ) ≤ x := hx.1
    have hx0 : x ≠ 0 := by intro h; rw [h] at hx2; linarith
    have h := (Real.hasDerivAt_log hx0).const_mul δ
    rw [show δ / x = δ * x⁻¹ by rw [div_eq_mul_inv]]
    exact h
  have hf'cont : ContinuousOn (fun x : ℝ => δ / x) (uIcc (2 : ℝ) T) := by
    rw [huIcc]
    intro x hx
    have hx2 : (2 : ℝ) ≤ x := hx.1
    have hx0 : x ≠ 0 := by intro h; rw [h] at hx2; linarith
    exact (continuousAt_const.div continuousAt_id hx0).continuousWithinAt
  have himg : (fun t : ℝ => δ * Real.log t) '' uIcc (2 : ℝ) T ⊆ Ioi (0 : ℝ) := by
    rintro y ⟨t, ht, rfl⟩
    rw [huIcc] at ht
    have ht2 : (2 : ℝ) ≤ t := ht.1
    have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
    exact mul_pos hδ hlogt
  have hgcont : ContinuousOn (fun u : ℝ => (Real.log u - Real.log δ) * Real.exp (-u))
      ((fun t : ℝ => δ * Real.log t) '' uIcc (2 : ℝ) T) := by
    refine ContinuousOn.mono ?_ himg
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt hu
    exact (((Real.continuousAt_log hu0).sub continuousAt_const).mul
      (Real.continuous_exp.continuousAt.comp continuousAt_neg)).continuousWithinAt
  have hsub := intervalIntegral.integral_deriv_smul_comp' hderiv hf'cont hgcont
  rw [← hsub]
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [huIcc] at ht
  have ht2 : (2 : ℝ) ≤ t := ht.1
  have ht0 : (0 : ℝ) < t := by linarith
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  simp only [Function.comp_apply, smul_eq_mul]
  rw [Real.log_mul hδ.ne' hlogt.ne', Real.rpow_def_of_pos ht0]
  have hexp : Real.exp (Real.log t * (-δ - 1)) = Real.exp (-(δ * Real.log t)) * t⁻¹ := by
    rw [show Real.log t * (-δ - 1) = -(δ * Real.log t) + -Real.log t by ring, Real.exp_add]
    congr 1
    rw [Real.exp_neg, Real.exp_log ht0]
  rw [hexp]
  field_simp
  ring

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology MeasureTheory Set Asymptotics
open scoped BigOperators

/-! ## Integrability of the two sides -/

theorem abs_logLog_le {t : ℝ} (ht : 2 ≤ t) :
    |Real.log (Real.log t)| ≤ |Real.log (Real.log 2)| + Real.log t := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogt : 0 < Real.log t := lt_of_lt_of_le hlog2 (Real.log_le_log (by norm_num) ht)
  have hmono : Real.log (Real.log 2) ≤ Real.log (Real.log t) :=
    Real.log_le_log hlog2 (Real.log_le_log (by norm_num) ht)
  have hupper : Real.log (Real.log t) ≤ Real.log t := by
    have := Real.log_le_sub_one_of_pos hlogt
    linarith
  have hlogtpos : 0 ≤ Real.log t := hlogt.le
  rcases le_or_gt 0 (Real.log (Real.log t)) with h | h
  · rw [abs_of_nonneg h]
    have := abs_nonneg (Real.log (Real.log 2))
    linarith
  · rw [abs_of_neg h]
    have h2 : -Real.log (Real.log 2) ≤ |Real.log (Real.log 2)| := neg_le_abs _
    linarith

theorem integrableOn_rpow_mul_logLog {δ : ℝ} (hδ : 0 < δ) :
    IntegrableOn (fun t : ℝ => t ^ (-δ - 1) * Real.log (Real.log t)) (Ioi (2 : ℝ)) := by
  have hmajorO : (fun t : ℝ => t ^ (-δ - 1) *
      (|Real.log (Real.log 2)| + Real.log t)) =O[atTop] (fun t : ℝ => t ^ (-1 - δ / 2)) := by
    have hlogO : (fun t : ℝ => |Real.log (Real.log 2)| + Real.log t) =O[atTop]
        (fun t : ℝ => t ^ (δ / 2)) := by
      refine IsBigO.add ?_ ((isLittleO_log_rpow_atTop (by positivity : (0 : ℝ) < δ / 2)).isBigO)
      refine IsBigO.of_bound |Real.log (Real.log 2)| ?_
      filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      have h1 : (1 : ℝ) ≤ t ^ (δ / 2) := Real.one_le_rpow ht (by positivity)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ t ^ (δ/2)),
        abs_abs]
      nlinarith [abs_nonneg (Real.log (Real.log 2))]
    have hmul := (isBigO_refl (fun t : ℝ => t ^ (-δ - 1)) atTop).mul hlogO
    refine hmul.trans (IsBigO.of_bound 1 ?_)
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [← Real.rpow_add ht, show -δ - 1 + δ / 2 = -1 - δ / 2 by ring, one_mul]
  have hmajorInt : IntegrableAtFilter (fun t : ℝ => t ^ (-1 - δ / 2)) atTop :=
    ⟨Ioi (1 : ℝ), Ioi_mem_atTop 1, integrableOn_Ioi_rpow_of_lt (by linarith) one_pos⟩
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-δ - 1) * Real.log (Real.log t))
      (Ici (2 : ℝ)) := by
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := ht
    have ht0 : (0 : ℝ) < t := by linarith
    have hlogt : 0 < Real.log t :=
      lt_of_lt_of_le (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) ht2)
    exact ((Real.continuousAt_rpow_const t (-δ - 1) (Or.inl ht0.ne')).mul
      ((Real.continuousAt_log hlogt.ne').comp (Real.continuousAt_log ht0.ne'))).continuousWithinAt
  have hloc : LocallyIntegrableOn (fun t : ℝ => t ^ (-δ - 1) * Real.log (Real.log t))
      (Ici (2 : ℝ)) := hcont.locallyIntegrableOn measurableSet_Ici
  have hbigO : (fun t : ℝ => t ^ (-δ - 1) * Real.log (Real.log t)) =O[atTop]
      (fun t : ℝ => t ^ (-1 - δ / 2)) := by
    refine IsBigO.trans (IsBigO.of_bound 1 ?_) hmajorO
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
    have ht0 : (0 : ℝ) < t := by linarith
    have hpow : (0 : ℝ) < t ^ (-δ - 1) := Real.rpow_pos_of_pos ht0 _
    have hlogt : 0 < Real.log t :=
      lt_of_lt_of_le (Real.log_pos (by norm_num)) (Real.log_le_log (by norm_num) ht)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_pos hpow, one_mul,
      abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ t ^ (-δ - 1) * (|Real.log (Real.log 2)| + Real.log t))]
    exact mul_le_mul_of_nonneg_left (abs_logLog_le ht) hpow.le
  have hIci := hloc.integrableOn_of_isBigO_atTop hbigO hmajorInt
  exact hIci.mono_set Ioi_subset_Ici_self

theorem integrableOn_logSub_mul_exp {δ a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn (fun u : ℝ => (Real.log u - Real.log δ) * Real.exp (-u)) (Ioi a) := by
  have h1 := HTGeometry.integrableOn_log_mul_exp_neg_Ioi ha
  have h2 := (integrableOn_exp_neg_Ioi a).const_mul (Real.log δ)
  refine (h1.sub h2).congr_fun (fun u _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioi

end

end RHTower
