import GaloisForLFunctions.HTGeometry.GaussianHalfLineMoment

/-!
# Watson's lemma on the Gaussian half line

If a profile agrees with a polynomial in `v²` to order `m` with a uniform coefficient, its Gaussian
transform agrees with the corresponding combination of even Gaussian moments, and the error is that
coefficient times the `m`-th real Gaussian moment at the real part of the parameter.

The bound is uniform over the whole open right half plane and does not degrade along rays, because
only the real part of the parameter enters the majorant.
-/

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Watson

variable {w : ℂ}

/-- The even Gaussian majorant at the real part of the parameter. -/
def realGaussianHalfMoment (b : ℝ) (k : ℕ) : ℝ :=
  ∫ v in Ioi (0 : ℝ), v ^ (2 * k) * Real.exp (-(b * v ^ 2))

theorem integrableOn_real_pow_mul_exp {b : ℝ} (hb : 0 < b) (m : ℕ) :
    IntegrableOn (fun v : ℝ => v ^ m * Real.exp (-(b * v ^ 2))) (Ioi 0) := by
  have h := integrable_rpow_mul_exp_neg_mul_sq hb
    (s := (m : ℝ)) (by have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m; linarith)
  refine (h.integrableOn (s := Ioi (0 : ℝ))).congr_fun_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with v _
  rw [Real.rpow_natCast]
  ring_nf

theorem realGaussianHalfMoment_nonneg (b : ℝ) (k : ℕ) :
    0 ≤ realGaussianHalfMoment b k := by
  refine setIntegral_nonneg measurableSet_Ioi fun v hv => ?_
  have : (0 : ℝ) ≤ v := le_of_lt hv
  positivity

/-- The polynomial part of a Watson expansion. -/
def watsonPoly (c : ℕ → ℝ) (m : ℕ) (v : ℝ) : ℝ := ∑ k ∈ Finset.range m, c k * v ^ (2 * k)

theorem continuous_watsonPoly (c : ℕ → ℝ) (m : ℕ) : Continuous (watsonPoly c m) := by
  refine continuous_finsetSum _ fun k _ => ?_
  fun_prop

theorem integrableOn_watsonPoly_gauss (hw : 0 < w.re) (c : ℕ → ℝ) (m : ℕ) :
    IntegrableOn (fun v : ℝ => ((watsonPoly c m v : ℝ) : ℂ)
      * Complex.exp (-w * (v : ℂ) ^ 2)) (Ioi 0) := by
  have hsum : ∀ v : ℝ, ((watsonPoly c m v : ℝ) : ℂ) * Complex.exp (-w * (v : ℂ) ^ 2)
      = ∑ k ∈ Finset.range m, (c k : ℂ)
        * ((v : ℂ) ^ (2 * k) * Complex.exp (-w * (v : ℂ) ^ 2)) := by
    intro v
    rw [watsonPoly]
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  refine (integrable_finsetSum (Finset.range m)
    (fun k _ => (integrableOn_pow_mul_cexp_neg_mul_sq hw (2 * k)).const_mul (c k : ℂ))).congr ?_
  filter_upwards with v
  exact (hsum v).symm

theorem integral_watsonPoly_gauss (hw : 0 < w.re) (c : ℕ → ℝ) (m : ℕ) :
    (∫ v in Ioi (0 : ℝ), ((watsonPoly c m v : ℝ) : ℂ) * Complex.exp (-w * (v : ℂ) ^ 2))
      = ∑ k ∈ Finset.range m, (c k : ℂ) * gaussianHalfMoment w k := by
  have hsum : ∀ v : ℝ, ((watsonPoly c m v : ℝ) : ℂ) * Complex.exp (-w * (v : ℂ) ^ 2)
      = ∑ k ∈ Finset.range m, (c k : ℂ)
        * ((v : ℂ) ^ (2 * k) * Complex.exp (-w * (v : ℂ) ^ 2)) := by
    intro v
    rw [watsonPoly]
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun v _ => hsum v),
    MeasureTheory.integral_finsetSum _
      (fun k _ => (integrableOn_pow_mul_cexp_neg_mul_sq hw (2 * k)).const_mul (c k : ℂ))]
  exact Finset.sum_congr rfl fun k _ => by
    rw [MeasureTheory.integral_const_mul, gaussianHalfMoment]

/-- **Watson's lemma with an explicit remainder.** -/
theorem norm_integral_sub_watson_le (hw : 0 < w.re) {f : ℝ → ℝ}
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ)))) (c : ℕ → ℝ) (m : ℕ)
    {C : ℝ}
    (hrem : ∀ v ∈ Ioi (0 : ℝ), |f v - watsonPoly c m v| ≤ C * v ^ (2 * m)) :
    ‖(∫ v in Ioi (0 : ℝ), ((f v : ℝ) : ℂ) * Complex.exp (-w * (v : ℂ) ^ 2))
        - ∑ k ∈ Finset.range m, (c k : ℂ) * gaussianHalfMoment w k‖
      ≤ C * realGaussianHalfMoment w.re m := by
  have hmajor : IntegrableOn
      (fun v : ℝ => C * (v ^ (2 * m) * Real.exp (-(w.re * v ^ 2)))) (Ioi 0) :=
    (integrableOn_real_pow_mul_exp hw (2 * m)).const_mul C
  have hdiffmeas : AEStronglyMeasurable
      (fun v : ℝ => (((f v - watsonPoly c m v : ℝ)) : ℂ) * Complex.exp (-w * (v : ℂ) ^ 2))
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine AEStronglyMeasurable.mul ?_ (by fun_prop)
    exact Complex.continuous_ofReal.comp_aestronglyMeasurable
      (hfm.sub (continuous_watsonPoly c m).aestronglyMeasurable)
  have hbd : ∀ᵐ v ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖(((f v - watsonPoly c m v : ℝ)) : ℂ) * Complex.exp (-w * (v : ℂ) ^ 2)‖
        ≤ C * (v ^ (2 * m) * Real.exp (-(w.re * v ^ 2))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      _root_.HTGeometry.norm_cexp_neg_mul_sq]
    have hexp : (0 : ℝ) < Real.exp (-(w.re * v ^ 2)) := Real.exp_pos _
    calc |f v - watsonPoly c m v| * Real.exp (-(w.re * v ^ 2))
        ≤ (C * v ^ (2 * m)) * Real.exp (-(w.re * v ^ 2)) :=
          mul_le_mul_of_nonneg_right (hrem v hv) hexp.le
      _ = C * (v ^ (2 * m) * Real.exp (-(w.re * v ^ 2))) := by ring
  have hdiffint : IntegrableOn
      (fun v : ℝ => (((f v - watsonPoly c m v : ℝ)) : ℂ) * Complex.exp (-w * (v : ℂ) ^ 2))
      (Ioi 0) := Integrable.mono' hmajor hdiffmeas hbd
  have hfint : IntegrableOn (fun v : ℝ => ((f v : ℝ) : ℂ) * Complex.exp (-w * (v : ℂ) ^ 2))
      (Ioi 0) := by
    have h := hdiffint.add (integrableOn_watsonPoly_gauss hw c m)
    refine h.congr ?_
    filter_upwards with v
    simp only [Pi.add_apply]
    push_cast
    ring
  have hsplit : (∫ v in Ioi (0 : ℝ), ((f v : ℝ) : ℂ) * Complex.exp (-w * (v : ℂ) ^ 2))
      - ∑ k ∈ Finset.range m, (c k : ℂ) * gaussianHalfMoment w k
      = ∫ v in Ioi (0 : ℝ),
          (((f v - watsonPoly c m v : ℝ)) : ℂ) * Complex.exp (-w * (v : ℂ) ^ 2) := by
    rw [← integral_watsonPoly_gauss hw c m,
      ← MeasureTheory.integral_sub hfint (integrableOn_watsonPoly_gauss hw c m)]
    refine setIntegral_congr_fun measurableSet_Ioi fun v _ => ?_
    push_cast
    ring
  rw [hsplit]
  refine le_trans (MeasureTheory.norm_integral_le_of_norm_le hmajor hbd) (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul, realGaussianHalfMoment]

end Watson

end

end GaloisForLFunctions.HTGeometry
