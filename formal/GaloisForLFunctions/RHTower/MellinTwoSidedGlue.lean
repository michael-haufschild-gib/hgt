import GaloisForLFunctions.RHTower.MellinHeadChart
import GaloisForLFunctions.RHTower.MellinHeadHardy
import GaloisForLFunctions.RHTower.SoninExtendedFunctionalEquation
import GaloisForLFunctions.HTGeometry.TwoSidedLaplaceVanishing

/-!
# Gluing a head representation to a tail representation across the critical line

Suppose one analytic object `Ψ` on the strip `0 < Re s < 1` is, on the left of the critical line,
the Mellin transform of a head datum `u|_{(0,a)}`, and on the right of it the Mellin transform of a
constant head `c` plus a tail datum `(g-u)|_{(a,∞)}`.  Passing to the `w = s - 1/2` variable and the
logarithmic charts of `MellinHardyBridge` / `MellinHeadChart`, the two representations become
half-line Laplace transforms on the two sides of the imaginary axis, so
`TwoSidedLaplaceVanishing.eq_zero_of_two_sided_laplace` forces both charts to vanish: `u` is the
constant `c` on the head and equals `g` on the tail.

This is the analytic engine behind the two-sided converse of Burnol's Proposition 4.1 — the step
that turns a prescribed element of `L̂_a` back into a vector of `L_a`.

## Main results

* `ae_eq_of_two_sided_mellin`
-/

namespace RHTower

open MeasureTheory Set Complex Filter Topology

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem isFiniteMeasure_restrict_Ioo (a : ℝ) :
    IsFiniteMeasure (volume.restrict (Ioo (0 : ℝ) a)) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  exact measure_Ioo_lt_top

/-- **The two-sided Mellin gluing lemma.** -/
theorem ae_eq_of_two_sided_mellin {a : ℝ} (ha : 0 < a) {u g : ℝ → ℂ} {c : ℂ}
    (hu0 : MemLp u 2 (volume.restrict (Ioo (0 : ℝ) a)))
    (hgu : MemLp (fun t : ℝ => g t - u t) 2 (volume.restrict (Ioi a)))
    {Ψ : ℂ → ℂ} (hΨ : ContinuousOn Ψ {s : ℂ | 0 < s.re ∧ s.re < 1})
    (hleft : ∀ s : ℂ, 0 < s.re → s.re < 1 / 2 →
      Ψ s = ∫ t in Ioo (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-s) * u t)
    (hright : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 →
      Ψ s = c * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - s) / (1 - s)
        + ∫ t in Ioi a, ((t : ℝ) : ℂ) ^ (-s) * (g t - u t)) :
    (∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) a)), u t = c) ∧
      (∀ᵐ t ∂(volume.restrict (Ioi a)), u t = g t) := by
  classical
  haveI := isFiniteMeasure_restrict_Ioo a
  have hac : ((a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  set ψ₁ : ℝ → ℂ := logChart a (fun t : ℝ => g t - u t) with hψ₁
  set ψ₂ : ℝ → ℂ := logChartHead a (fun t : ℝ => u t - c) with hψ₂
  have hm1 : MemLp ψ₁ 2 (volume.restrict (Ioi (0 : ℝ))) := memLp_two_logChart ha hgu
  have hm2 : MemLp ψ₂ 2 (volume.restrict (Ioi (0 : ℝ))) :=
    memLp_two_logChartHead ha
      (hu0.sub (memLp_const (μ := volume.restrict (Ioo (0 : ℝ) a)) (p := 2) c))
  set G : ℂ → ℂ := fun w : ℂ =>
    ((a : ℝ) : ℂ) ^ w * Ψ (1 / 2 + w) - c * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2) / (1 / 2 - w) with hG
  have hre : ∀ w : ℂ, ((1 : ℂ) / 2 + w).re = 1 / 2 + w.re := by
    intro w
    rw [Complex.add_re]
    norm_num
  have hp1 : ∀ w : ℂ, ((a : ℝ) : ℂ) ^ w * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - w)
      = ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2) := by
    intro w
    rw [← Complex.cpow_add _ _ hac]
    congr 1
    ring
  have hp2 : ∀ w : ℂ, ((a : ℝ) : ℂ) ^ w * ((a : ℝ) : ℂ) ^ (-w) = 1 := by
    intro w
    rw [← Complex.cpow_add _ _ hac, add_neg_cancel, Complex.cpow_zero]
  -- the right half-plane representation
  have hrightG : ∀ w : ℂ, 0 < w.re → w.re < 1 / 2 → G w = laplaceRay ψ₁ w := by
    intro w hw1 hw2
    have hs1 : (1 : ℝ) / 2 < ((1 : ℂ) / 2 + w).re := by rw [hre]; linarith
    have hs2 : ((1 : ℂ) / 2 + w).re < 1 := by rw [hre]; linarith
    have hΨv := hright ((1 : ℂ) / 2 + w) hs1 hs2
    have htail := mellinTail_eq_laplaceRay ha (fun t : ℝ => g t - u t) ((1 : ℂ) / 2 + w)
    rw [htail] at hΨv
    rw [show (1 : ℂ) - ((1 : ℂ) / 2 + w) = 1 / 2 - w from by ring] at hΨv
    rw [show (1 : ℂ) / 2 - ((1 : ℂ) / 2 + w) = -w from by ring] at hΨv
    rw [show ((1 : ℂ) / 2 + w) - 1 / 2 = w from by ring] at hΨv
    rw [hG]
    simp only
    rw [hΨv, mul_add]
    have hd : (1 : ℂ) / 2 - w ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    have e1 : ((a : ℝ) : ℂ) ^ w * (c * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - w) / (1 / 2 - w))
        = c * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2) / (1 / 2 - w) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      calc ((a : ℝ) : ℂ) ^ w * (c * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - w) * (1 / 2 - w)⁻¹)
          = (((a : ℝ) : ℂ) ^ w * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - w)) * (c * (1 / 2 - w)⁻¹) := by
            ring
        _ = ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2) * (c * (1 / 2 - w)⁻¹) := by rw [hp1 w]
        _ = c * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2) * (1 / 2 - w)⁻¹ := by ring
    have e2 : ((a : ℝ) : ℂ) ^ w * (((a : ℝ) : ℂ) ^ (-w) * laplaceRay ψ₁ w)
        = laplaceRay ψ₁ w := by
      rw [← mul_assoc, hp2 w, one_mul]
    rw [e1, e2]
    ring
  -- the left half-plane representation
  have hleftG : ∀ w : ℂ, -(1 / 2 : ℝ) < w.re → w.re < 0 → G w = laplaceRay ψ₂ (-w) := by
    intro w hw1 hw2
    have hs1 : (0 : ℝ) < ((1 : ℂ) / 2 + w).re := by rw [hre]; linarith
    have hs2 : ((1 : ℂ) / 2 + w).re < 1 / 2 := by rw [hre]; linarith
    have hΨv := hleft ((1 : ℂ) / 2 + w) hs1 hs2
    set s : ℂ := (1 : ℂ) / 2 + w with hs
    -- split the head integral
    have hsre : s.re < 1 / 2 := hs2
    have hint1 : IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s) * (u t - c))
        (Ioo (0 : ℝ) a) volume :=
      (memLp_two_cpow_Ioo ha hsre).integrable_mul
        (hu0.sub (memLp_const (μ := volume.restrict (Ioo (0 : ℝ) a)) (p := 2) c))
    have hcmem : MemLp (fun _ : ℝ => c) 2 (volume.restrict (Ioo (0 : ℝ) a)) := memLp_const c
    have hint2 : IntegrableOn (fun t : ℝ => ((t : ℝ) : ℂ) ^ (-s) * c)
        (Ioo (0 : ℝ) a) volume :=
      (memLp_two_cpow_Ioo ha hsre).integrable_mul hcmem
    have hsplit : (∫ t in Ioo (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-s) * u t)
        = (∫ t in Ioo (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-s) * (u t - c))
          + ∫ t in Ioo (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-s) * c := by
      rw [← MeasureTheory.integral_add hint1 hint2]
      refine setIntegral_congr_fun measurableSet_Ioo (fun t _ => ?_)
      ring
    have hconstint : (∫ t in Ioo (0 : ℝ) a, ((t : ℝ) : ℂ) ^ (-s) * c)
        = c * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - s) / (1 - s) := by
      rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc]
      exact integral_head_cpow_Ioc ha (by linarith) c
    have hhead := mellinHead_eq_laplaceRay ha (fun t : ℝ => u t - c) s
    rw [hsplit, hhead, hconstint] at hΨv
    rw [show (1 : ℂ) - s = 1 / 2 - w from by rw [hs]; ring] at hΨv
    rw [show (1 : ℂ) / 2 - s = -w from by rw [hs]; ring] at hΨv
    rw [hG]
    simp only
    rw [← hs, hΨv, mul_add]
    have hd : (1 : ℂ) / 2 - w ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    have e1 : ((a : ℝ) : ℂ) ^ w * (((a : ℝ) : ℂ) ^ (-w) * laplaceRay ψ₂ (-w))
        = laplaceRay ψ₂ (-w) := by
      rw [← mul_assoc, hp2 w, one_mul]
    have e2 : ((a : ℝ) : ℂ) ^ w * (c * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - w) / (1 / 2 - w))
        = c * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2) / (1 / 2 - w) := by
      rw [div_eq_mul_inv, div_eq_mul_inv]
      calc ((a : ℝ) : ℂ) ^ w * (c * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - w) * (1 / 2 - w)⁻¹)
          = (((a : ℝ) : ℂ) ^ w * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2 - w)) * (c * (1 / 2 - w)⁻¹) := by
            ring
        _ = ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2) * (c * (1 / 2 - w)⁻¹) := by rw [hp1 w]
        _ = c * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2) * (1 / 2 - w)⁻¹ := by ring
    rw [e1, e2]
    ring
  -- continuity of `G` on the strip
  have hGcont : ContinuousOn G {w : ℂ | |w.re| < 1 / 2} := by
    have hcpow : Continuous fun w : ℂ => ((a : ℝ) : ℂ) ^ w := by
      have h : (fun w : ℂ => ((a : ℝ) : ℂ) ^ w)
          = fun w : ℂ => Complex.exp (Complex.log ((a : ℝ) : ℂ) * w) := by
        funext w
        rw [Complex.cpow_def_of_ne_zero hac]
      rw [h]
      fun_prop
    have hshift : Continuous fun w : ℂ => (1 : ℂ) / 2 + w := by fun_prop
    have hmaps : Set.MapsTo (fun w : ℂ => (1 : ℂ) / 2 + w) {w : ℂ | |w.re| < 1 / 2}
        {s : ℂ | 0 < s.re ∧ s.re < 1} := by
      intro w hw
      have hw' : |w.re| < 1 / 2 := hw
      have h1 := abs_lt.1 hw'
      refine ⟨?_, ?_⟩ <;> rw [hre] <;> linarith [h1.1, h1.2]
    have hΨc : ContinuousOn (fun w : ℂ => Ψ ((1 : ℂ) / 2 + w)) {w : ℂ | |w.re| < 1 / 2} :=
      hΨ.comp hshift.continuousOn hmaps
    have hden : ContinuousOn (fun w : ℂ => c * ((a : ℝ) : ℂ) ^ ((1 : ℂ) / 2) / (1 / 2 - w))
        {w : ℂ | |w.re| < 1 / 2} := by
      refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
      intro w hw
      have hw' : |w.re| < 1 / 2 := hw
      have h1 := abs_lt.1 hw'
      intro hzero
      have := congrArg Complex.re hzero
      simp at this
      linarith [h1.2]
    exact (hcpow.continuousOn.mul hΨc).sub hden
  -- the two-sided vanishing theorem
  obtain ⟨hz1, hz2⟩ := eq_zero_of_two_sided_laplace hm1 hm2 (by norm_num : (0:ℝ) < 1 / 2)
    hGcont (fun w hw1 hw2 => hrightG w hw1 hw2)
    (fun w hw1 hw2 => hleftG w (by simpa using hw1) hw2)
  constructor
  · -- the head datum is the constant
    have hmass : (∫ t in Ioo (0 : ℝ) a, ‖u t - c‖ ^ 2) = 0 := by
      rw [← integral_norm_sq_logChartHead ha (fun t : ℝ => u t - c)]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hz2] with x hx
      rw [hψ₂] at hx
      rw [hx]
      simp
    have hnn : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) a)), ‖u t - c‖ ^ 2 = 0 := by
      have hint : IntegrableOn (fun t : ℝ => ‖u t - c‖ ^ 2) (Ioo (0 : ℝ) a) volume := by
        have h := hu0.sub (memLp_const (μ := volume.restrict (Ioo (0 : ℝ) a)) (p := 2) c)
        exact (memLp_two_iff_integrable_sq_norm h.1).1 h
      refine (integral_eq_zero_iff_of_nonneg_ae ?_ hint).1 hmass
      filter_upwards with t
      positivity
    filter_upwards [hnn] with t ht
    have : ‖u t - c‖ = 0 := by nlinarith [norm_nonneg (u t - c)]
    have := norm_eq_zero.1 this
    linear_combination this
  · have hmass : (∫ t in Ioi a, ‖g t - u t‖ ^ 2) = 0 := by
      rw [← integral_norm_sq_logChart ha (fun t : ℝ => g t - u t)]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hz1] with x hx
      rw [hψ₁] at hx
      rw [hx]
      simp
    have hnn : ∀ᵐ t ∂(volume.restrict (Ioi a)), ‖g t - u t‖ ^ 2 = 0 := by
      have hint : IntegrableOn (fun t : ℝ => ‖g t - u t‖ ^ 2) (Ioi a) volume :=
        (memLp_two_iff_integrable_sq_norm hgu.1).1 hgu
      refine (integral_eq_zero_iff_of_nonneg_ae ?_ hint).1 hmass
      filter_upwards with t
      positivity
    filter_upwards [hnn] with t ht
    have h0 : ‖g t - u t‖ = 0 := by nlinarith [norm_nonneg (g t - u t)]
    have := norm_eq_zero.1 h0
    linear_combination -this

end

end RHTower
