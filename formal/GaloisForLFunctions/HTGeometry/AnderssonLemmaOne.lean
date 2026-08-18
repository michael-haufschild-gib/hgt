import Mathlib
import GaloisForLFunctions.HTGeometry.HalfPlaneMellinRepresentation
import GaloisForLFunctions.RHTower.AnalyticDividedDifference

/-!
# Andersson's Lemma 1

If `(s² + s) f(s)` is uniformly approximable on the closed half plane `Re s ≥ 1` by entire
functions, then

```text
f(s) = ∫_1^∞ q(x) x^{-s} dx + g(s)        (Re s > 1)
```

for a bounded density `q` vanishing at infinity and an entire `g`.

The multiplier `s² + s = s(s+1)` rather than `s²` is what keeps the correction terms elementary:
partial fractions give `G/(s(s+1)) = H + A/s + B/(s+1)` with `H` entire, and both `1/s` and
`1/(s+1)` are Mellin transforms of the `o(1)` densities `1/x` and `1/x²`.  With `s²` the second
correction would be `1/s²`, whose density is `log x / x`.
-/

noncomputable section

open Complex MeasureTheory Filter Set

namespace GaloisForLFunctions.HTGeometry

theorem differentiable_dslope_of_differentiable {G : ℂ → ℂ} (hG : Differentiable ℂ G) (a : ℂ) :
    Differentiable ℂ (dslope G a) := fun z =>
  (RHTower.analyticAt_dslope_of_analyticAt (f := G) (a := a) (z := z)
    (hG.analyticAt a) (hG.analyticAt z)).differentiableAt

/-- `1/(s + k - 1)` is the Mellin transform of `x^{-k}`. -/
theorem integral_Ioi_inv_pow_cpow {s : ℂ} {k : ℕ} (hk : 1 ≤ k) (hs : 0 < s.re) :
    (∫ x in Ioi (1:ℝ), ((x : ℂ) ^ k)⁻¹ * (x : ℂ) ^ (-s)) = 1 / (s + (k : ℂ) - 1) := by
  have hkR : (1:ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hlt : (-s - (k : ℂ)).re < -1 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.natCast_re]
    linarith
  have heq : ∀ x ∈ Ioi (1:ℝ),
      ((x : ℂ) ^ k)⁻¹ * (x : ℂ) ^ (-s) = (x : ℂ) ^ (-s - (k : ℂ)) := by
    intro x hx
    have hxpos : (0:ℝ) < x := lt_trans one_pos hx
    have hxne : ((x : ℝ) : ℂ) ≠ 0 := by simpa using ne_of_gt hxpos
    rw [Complex.cpow_sub _ _ hxne, Complex.cpow_natCast, div_eq_mul_inv]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_Ioi_cpow_of_lt hlt one_pos]
  have hone : ((1:ℝ) : ℂ) ^ (-s - (k : ℂ) + 1) = 1 := by
    rw [Complex.ofReal_one, Complex.one_cpow]
  rw [hone]
  have hden : -s - (k : ℂ) + 1 ≠ 0 := by
    intro h
    have hz : (-s - (k : ℂ) + 1).re = 0 := by rw [h]; simp
    simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.natCast_re,
      Complex.one_re] at hz
    linarith
  have hden2 : s + (k : ℂ) - 1 ≠ 0 := by
    intro h
    apply hden
    linear_combination -h
  field_simp
  ring

theorem integrableOn_mellin_term {q : ℝ → ℂ} {M : ℝ}
    (hq : ∀ x : ℝ, 1 ≤ x → ‖q x‖ ≤ M)
    (hmeas : AEStronglyMeasurable q (volume.restrict (Ioi (1:ℝ))))
    {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ => q x * (x : ℂ) ^ (-s)) (Ioi (1:ℝ)) := by
  have henv : IntegrableOn (fun x : ℝ => M * x ^ (-s.re)) (Ioi (1:ℝ)) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) one_pos).const_mul M
  refine Integrable.mono' henv ?_ ?_
  · refine hmeas.mul ?_
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro x hx
    have hxpos : (0:ℝ) < x := lt_trans one_pos hx
    have hslit : ((x : ℝ) : ℂ) ∈ Complex.slitPlane := Or.inl (by simpa using hxpos)
    have hc : ContinuousAt (fun y : ℝ => ((y : ℝ) : ℂ) ^ (-s)) x :=
      Complex.continuousAt_ofReal_cpow_const x (-s) (Or.inr (ne_of_gt hxpos))
    exact hc.continuousWithinAt
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hxpos : (0:ℝ) < x := lt_trans one_pos hx
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hxpos, Complex.neg_re]
    exact mul_le_mul_of_nonneg_right (hq x (le_of_lt hx)) (Real.rpow_nonneg hxpos.le _)

theorem aestronglyMeasurable_mellinDensity (φ : ℂ → ℂ)
    (hφ : ∀ z : ℂ, 1 ≤ z.re → AnalyticAt ℂ φ z) :
    AEStronglyMeasurable (mellinDensity φ) (volume.restrict (Ioi (1:ℝ))) := by
  have hbdry : Measurable fun t : ℝ => φ ((1 : ℂ) + (t : ℂ) * I) :=
    (continuous_boundary hφ).measurable
  have hjoint : Measurable (Function.uncurry fun (x : ℝ) (t : ℝ) =>
      Complex.exp ((t : ℂ) * I * (Real.log x : ℂ)) * φ ((1 : ℂ) + (t : ℂ) * I)) := by
    have h1 : Measurable fun z : ℝ × ℝ =>
        Complex.exp ((z.2 : ℂ) * I * (Real.log z.1 : ℂ)) := by
      refine Complex.measurable_exp.comp ?_
      exact ((Complex.measurable_ofReal.comp measurable_snd).mul measurable_const).mul
        (Complex.measurable_ofReal.comp (Real.measurable_log.comp measurable_fst))
    exact h1.mul (hbdry.comp measurable_snd)
  have hint : StronglyMeasurable fun x : ℝ =>
      ∫ (t : ℝ), Complex.exp ((t : ℂ) * I * (Real.log x : ℂ)) * φ ((1 : ℂ) + (t : ℂ) * I) :=
    hjoint.stronglyMeasurable.integral_prod_right'
  exact ((hint.const_mul (1 / (2 * Real.pi) : ℂ)).aestronglyMeasurable).restrict

/-- **Andersson's Lemma 1.**  If `(s² + s) f` is uniformly approximable on the closed half plane by
an entire function, then `f` is a Mellin transform of a bounded `o(1)` density plus an entire
function. -/
theorem exists_mellin_add_entire {f : ℂ → ℂ} {G : ℂ → ℂ}
    (hf : ∀ z : ℂ, 1 ≤ z.re → AnalyticAt ℂ f z)
    (hGd : Differentiable ℂ G)
    (hGb : ∀ s : ℂ, 1 ≤ s.re → ‖(s ^ 2 + s) * f s - G s‖ ≤ 1) :
    ∃ (q : ℝ → ℂ) (g : ℂ → ℂ), Differentiable ℂ g ∧
      Tendsto q atTop (nhds 0) ∧ (∃ M : ℝ, ∀ x : ℝ, 1 ≤ x → ‖q x‖ ≤ M) ∧
      ∀ s : ℂ, 1 < s.re → f s = (∫ x in Ioi (1:ℝ), q x * (x : ℂ) ^ (-s)) + g s := by
  -- the partial fraction split of `G / (s (s+1))`
  set A : ℂ := G 0 with hAdef
  set B : ℂ := -G (-1) with hBdef
  set N : ℂ → ℂ := fun s => G s - A * (s + 1) - B * s with hNdef
  have hNd : Differentiable ℂ N := by
    rw [hNdef]
    exact (hGd.sub ((differentiable_const _).mul
      (differentiable_id.add (differentiable_const _)))).sub
      ((differentiable_const _).mul differentiable_id)
  have hN0 : N 0 = 0 := by
    rw [hNdef, hAdef]
    simp
  have hNneg : N (-1) = 0 := by
    rw [hNdef, hAdef, hBdef]
    ring
  set N1 : ℂ → ℂ := dslope N 0 with hN1def
  have hN1d : Differentiable ℂ N1 := differentiable_dslope_of_differentiable hNd 0
  have hN1val : ∀ s : ℂ, s ≠ 0 → N1 s = N s / s := by
    intro s hs
    rw [hN1def, dslope_of_ne _ hs, slope_def_field, hN0]
    simp
  have hN1neg : N1 (-1) = 0 := by
    rw [hN1val _ (by norm_num), hNneg, zero_div]
  set H : ℂ → ℂ := dslope N1 (-1) with hHdef
  have hHd : Differentiable ℂ H := differentiable_dslope_of_differentiable hN1d (-1)
  have hHval : ∀ s : ℂ, s ≠ 0 → s ≠ -1 → G s / (s * (s + 1)) = H s + A / s + B / (s + 1) := by
    intro s hs0 hs1
    have hsp : s + 1 ≠ 0 := fun h => hs1 (by linear_combination h)
    have hsp2 : (1 : ℂ) + s ≠ 0 := fun h => hsp (by linear_combination h)
    have hHs : H s = N s / (s * (s + 1)) := by
      rw [hHdef, dslope_of_ne _ hs1, slope_def_field, hN1neg, hN1val s hs0]
      field_simp
      ring
    rw [hHs, hNdef]
    field_simp
    ring
  -- the decaying remainder
  set φ : ℂ → ℂ := fun s => ((s ^ 2 + s) * f s - G s) / (s ^ 2 + s) with hφdef
  have hquad : ∀ z : ℂ, 1 ≤ z.re → z ^ 2 + z ≠ 0 := by
    intro z hz h
    have hfac : z * (z + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hfac with h1 | h1
    · rw [h1] at hz
      simp at hz
      linarith
    · have : z = -1 := by linear_combination h1
      rw [this] at hz
      simp at hz
      linarith
  have hφana : ∀ z : ℂ, 1 ≤ z.re → AnalyticAt ℂ φ z := by
    intro z hz
    rw [hφdef]
    refine AnalyticAt.div ?_ ?_ (hquad z hz)
    · exact ((((analyticAt_id.pow 2).add analyticAt_id).mul (hf z hz)).sub (hGd.analyticAt z))
    · exact (analyticAt_id.pow 2).add analyticAt_id
  have hφbound : ∀ z : ℂ, 1 ≤ z.re → ‖φ z‖ ≤ 1 / ‖z‖ ^ 2 := by
    intro z hz
    have hznorm : (0:ℝ) < ‖z‖ := by
      have : z ≠ 0 := by
        intro h
        rw [h] at hz
        simp at hz
        linarith
      exact norm_pos_iff.mpr this
    have hsq : ‖z‖ ^ 2 ≤ ‖z ^ 2 + z‖ := by
      have hfac : z ^ 2 + z = z * (z + 1) := by ring
      rw [hfac, norm_mul]
      have hz1 : ‖z‖ ≤ ‖z + 1‖ := by
        have e1 : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
        have e2 : ‖z + 1‖ ^ 2 = (z.re + 1) ^ 2 + z.im ^ 2 := by
          rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
          simp
          ring
        nlinarith [norm_nonneg z, norm_nonneg (z + 1)]
      nlinarith [norm_nonneg z]
    rw [hφdef, norm_div]
    have hnum := hGb z hz
    have hden : (0:ℝ) < ‖z ^ 2 + z‖ := by
      have := hquad z hz
      exact norm_pos_iff.mpr this
    calc ‖(z ^ 2 + z) * f z - G z‖ / ‖z ^ 2 + z‖ ≤ 1 / ‖z ^ 2 + z‖ := by gcongr
      _ ≤ 1 / ‖z‖ ^ 2 := by
          gcongr
  -- the Mellin density of the remainder
  set q0 : ℝ → ℂ := mellinDensity φ with hq0def
  set Kb : ℝ := (1 / (2 * Real.pi)) * ∫ (t : ℝ), ‖φ ((1 : ℂ) + (t : ℂ) * I)‖ with hKdef
  have hq0bound : ∀ x : ℝ, ‖q0 x‖ ≤ Kb := fun x => norm_mellinDensity_le φ x
  have hq0meas : AEStronglyMeasurable q0 (volume.restrict (Ioi (1:ℝ))) :=
    aestronglyMeasurable_mellinDensity φ hφana
  have hAmeas : AEStronglyMeasurable (fun x : ℝ => A * ((x : ℂ) ^ 1)⁻¹)
      (volume.restrict (Ioi (1:ℝ))) :=
    (((Complex.measurable_ofReal.pow_const 1).inv).const_mul A).aestronglyMeasurable
  have hBmeas : AEStronglyMeasurable (fun x : ℝ => B * ((x : ℂ) ^ 2)⁻¹)
      (volume.restrict (Ioi (1:ℝ))) :=
    (((Complex.measurable_ofReal.pow_const 2).inv).const_mul B).aestronglyMeasurable
  have hnormpow : ∀ (k : ℕ) (x : ℝ), 1 ≤ x → ‖((x : ℂ) ^ k)⁻¹‖ ≤ 1 := by
    intro k x hx
    have hxpos : (0:ℝ) < x := lt_of_lt_of_le one_pos hx
    rw [norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hxpos]
    have hone : (1:ℝ) ≤ x ^ k := one_le_pow₀ hx
    rw [inv_le_one_iff₀]
    exact Or.inr hone
  have hAbound : ∀ x : ℝ, 1 ≤ x → ‖A * ((x : ℂ) ^ 1)⁻¹‖ ≤ ‖A‖ := by
    intro x hx
    rw [norm_mul]
    calc ‖A‖ * ‖((x : ℂ) ^ 1)⁻¹‖ ≤ ‖A‖ * 1 :=
          mul_le_mul_of_nonneg_left (hnormpow 1 x hx) (norm_nonneg A)
      _ = ‖A‖ := by ring
  have hBbound : ∀ x : ℝ, 1 ≤ x → ‖B * ((x : ℂ) ^ 2)⁻¹‖ ≤ ‖B‖ := by
    intro x hx
    rw [norm_mul]
    calc ‖B‖ * ‖((x : ℂ) ^ 2)⁻¹‖ ≤ ‖B‖ * 1 :=
          mul_le_mul_of_nonneg_left (hnormpow 2 x hx) (norm_nonneg B)
      _ = ‖B‖ := by ring
  refine ⟨fun x => q0 x + A * ((x : ℂ) ^ 1)⁻¹ + B * ((x : ℂ) ^ 2)⁻¹, H, hHd, ?_,
    ⟨Kb + ‖A‖ + ‖B‖, ?_⟩, ?_⟩
  · have hinv : Tendsto (fun x : ℝ => ((x : ℂ))⁻¹) atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have heq : (fun x : ℝ => ‖((x : ℂ))⁻¹‖) =ᶠ[atTop] fun x : ℝ => x⁻¹ := by
        filter_upwards [eventually_gt_atTop (0:ℝ)] with x hx
        rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx]
      exact tendsto_inv_atTop_zero.congr' heq.symm
    have h0 := tendsto_mellinDensity_atTop φ
    have h1 : Tendsto (fun x : ℝ => A * ((x : ℂ) ^ 1)⁻¹) atTop (nhds 0) := by
      simp only [pow_one]
      simpa using hinv.const_mul A
    have h2 : Tendsto (fun x : ℝ => B * ((x : ℂ) ^ 2)⁻¹) atTop (nhds 0) := by
      have hp : Tendsto (fun x : ℝ => ((x : ℂ) ^ 2)⁻¹) atTop (nhds 0) := by
        simp only [← inv_pow]
        simpa using hinv.pow 2
      simpa using hp.const_mul B
    simpa using (h0.add h1).add h2
  · intro x hx
    calc ‖q0 x + A * ((x : ℂ) ^ 1)⁻¹ + B * ((x : ℂ) ^ 2)⁻¹‖
        ≤ ‖q0 x + A * ((x : ℂ) ^ 1)⁻¹‖ + ‖B * ((x : ℂ) ^ 2)⁻¹‖ := norm_add_le _ _
      _ ≤ (‖q0 x‖ + ‖A * ((x : ℂ) ^ 1)⁻¹‖) + ‖B * ((x : ℂ) ^ 2)⁻¹‖ :=
          add_le_add (norm_add_le _ _) le_rfl
      _ ≤ (Kb + ‖A‖) + ‖B‖ :=
          add_le_add (add_le_add (hq0bound x) (hAbound x hx)) (hBbound x hx)
  · intro s hs
    have hsre : (0:ℝ) < s.re := by linarith
    have hs0 : s ≠ 0 := by
      intro h
      rw [h] at hs
      simp at hs
      linarith
    have hsn1 : s ≠ -1 := by
      intro h
      rw [h] at hs
      simp at hs
      linarith
    have hquads : s ^ 2 + s ≠ 0 := hquad s (le_of_lt hs)
    have hint0 : IntegrableOn (fun x : ℝ => q0 x * (x : ℂ) ^ (-s)) (Ioi (1:ℝ)) :=
      integrableOn_mellin_term (fun x _ => hq0bound x) hq0meas hs
    have hint1 : IntegrableOn (fun x : ℝ => (A * ((x : ℂ) ^ 1)⁻¹) * (x : ℂ) ^ (-s))
        (Ioi (1:ℝ)) :=
      integrableOn_mellin_term hAbound hAmeas hs
    have hint2 : IntegrableOn (fun x : ℝ => (B * ((x : ℂ) ^ 2)⁻¹) * (x : ℂ) ^ (-s))
        (Ioi (1:ℝ)) :=
      integrableOn_mellin_term hBbound hBmeas hs
    have hsum : (∫ x in Ioi (1:ℝ),
          (q0 x + A * ((x : ℂ) ^ 1)⁻¹ + B * ((x : ℂ) ^ 2)⁻¹) * (x : ℂ) ^ (-s))
        = (∫ x in Ioi (1:ℝ), q0 x * (x : ℂ) ^ (-s))
          + (∫ x in Ioi (1:ℝ), (A * ((x : ℂ) ^ 1)⁻¹) * (x : ℂ) ^ (-s))
          + (∫ x in Ioi (1:ℝ), (B * ((x : ℂ) ^ 2)⁻¹) * (x : ℂ) ^ (-s)) := by
      have hint01 : IntegrableOn (fun x : ℝ =>
          q0 x * (x : ℂ) ^ (-s) + (A * ((x : ℂ) ^ 1)⁻¹) * (x : ℂ) ^ (-s)) (Ioi (1:ℝ)) :=
        hint0.add hint1
      have e1 : ∀ x : ℝ,
          (q0 x + A * ((x : ℂ) ^ 1)⁻¹ + B * ((x : ℂ) ^ 2)⁻¹) * (x : ℂ) ^ (-s)
            = (q0 x * (x : ℂ) ^ (-s) + (A * ((x : ℂ) ^ 1)⁻¹) * (x : ℂ) ^ (-s))
              + (B * ((x : ℂ) ^ 2)⁻¹) * (x : ℂ) ^ (-s) := fun x => by ring
      rw [setIntegral_congr_fun measurableSet_Ioi (fun x _ => e1 x),
        MeasureTheory.integral_add hint01 hint2, MeasureTheory.integral_add hint0 hint1]
    have hA1 : (∫ x in Ioi (1:ℝ), (A * ((x : ℂ) ^ 1)⁻¹) * (x : ℂ) ^ (-s)) = A / s := by
      have hcongr : ∀ x : ℝ, (A * ((x : ℂ) ^ 1)⁻¹) * (x : ℂ) ^ (-s)
          = A * (((x : ℂ) ^ 1)⁻¹ * (x : ℂ) ^ (-s)) := by
        intro x; ring
      simp_rw [hcongr]
      rw [MeasureTheory.integral_const_mul,
        integral_Ioi_inv_pow_cpow (k := 1) le_rfl hsre]
      push_cast
      rw [add_sub_cancel_right]
      ring
    have hB1 : (∫ x in Ioi (1:ℝ), (B * ((x : ℂ) ^ 2)⁻¹) * (x : ℂ) ^ (-s)) = B / (s + 1) := by
      have hcongr : ∀ x : ℝ, (B * ((x : ℂ) ^ 2)⁻¹) * (x : ℂ) ^ (-s)
          = B * (((x : ℂ) ^ 2)⁻¹ * (x : ℂ) ^ (-s)) := by
        intro x; ring
      simp_rw [hcongr]
      rw [MeasureTheory.integral_const_mul,
        integral_Ioi_inv_pow_cpow (k := 2) (by norm_num) hsre]
      push_cast
      ring_nf
    have h0 : (∫ x in Ioi (1:ℝ), q0 x * (x : ℂ) ^ (-s)) = φ s :=
      integral_mellinDensity_eq hφana hφbound hs
    have hfs : f s = φ s + G s / (s ^ 2 + s) := by
      rw [hφdef, ← add_div, sub_add_cancel]
      exact (mul_div_cancel_left₀ (f s) hquads).symm
    have hfac : s ^ 2 + s = s * (s + 1) := by ring
    rw [hsum, h0, hA1, hB1, hfs, hfac, hHval s hs0 hsn1]
    ring

end GaloisForLFunctions.HTGeometry

end
