import GaloisForLFunctions.RHTower.DirichletExponentBridge

/-!
# Recovering a Dirichlet term from its smoothed sum

The smoothed Perron summation of the corpus turns a Dirichlet series into the piecewise-linear
partial sum `A₁(x) = ∑ aₙ max(x−n, 0)`.  The identity going back is

```text
∫_n^∞ (x − n) x^{−s−2} dx  =  n^{−s} / (s(s+1))        (Re s > 0, n > 0) ,
```

so that `s(s+1) ∫_1^∞ A₁(x) x^{−s−2} dx` reproduces the series term by term.  It is the exact
inverse of the smoothing, and it is what converts a growth bound on `A₁` into a convergence
statement for the series.

The proof is the improper fundamental theorem of calculus twice: `x^{−s−1}` integrates to
`n^{−s}/s` and `x^{−s−2}` to `n^{−s−1}/(s+1)`, and `1/s − 1/(s+1) = 1/(s(s+1))`.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace GaloisForLFunctions.RHTower

/-- Measurability of a complex power on a positive ray. -/
theorem aestronglyMeasurable_cpow_Ioi {w : ℂ} (hw : w ≠ 0) {a : ℝ} (ha : 0 < a) :
    AEStronglyMeasurable (fun x : ℝ => (x : ℂ) ^ w) (volume.restrict (Set.Ioi a)) := by
  refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
  intro x hx
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans ha hx)
  exact ((hasDerivAt_ofReal_cpow_const hx0 hw).continuousAt).continuousWithinAt

/-- The tail integral of a complex power. -/
theorem integral_Ioi_cpow_neg_succ {s : ℂ} (hs : 0 < s.re) {a : ℝ} (ha : 0 < a) :
    ∫ x in Set.Ioi a, (x : ℂ) ^ (-s - 1) = (a : ℂ) ^ (-s) / s := by
  have hsne : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  have hcont : ContinuousWithinAt (fun x : ℝ => -((x : ℂ) ^ (-s)) / s) (Set.Ici a) a := by
    have hd := hasDerivAt_ofReal_cpow_const (x := a) (ne_of_gt ha) (r := -s) (neg_ne_zero.2 hsne)
    exact ((hd.continuousAt.neg).div_const s).continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioi a, HasDerivAt (fun y : ℝ => -((y : ℂ) ^ (-s)) / s)
      ((x : ℂ) ^ (-s - 1)) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_trans ha hx)
    have hd := hasDerivAt_ofReal_cpow_const hx0 (r := -s) (neg_ne_zero.2 hsne)
    have hd2 := (hd.neg).div_const s
    have hval : -(-s * (x : ℂ) ^ (-s - 1)) / s = (x : ℂ) ^ (-s - 1) := by
      field_simp
    rwa [hval] at hd2
  have hint : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1)) (Set.Ioi a) volume := by
    have hmaj : IntegrableOn (fun x : ℝ => x ^ (-s.re - 1)) (Set.Ioi a) volume :=
      integrableOn_Ioi_rpow_of_lt (by linarith) ha
    have hwne : (-s - 1 : ℂ) ≠ 0 := by
      intro h
      have : (-s - 1).re = 0 := by rw [h]; simp
      simp at this
      linarith
    refine Integrable.mono' hmaj (aestronglyMeasurable_cpow_Ioi hwne ha) ?_
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
      have hx0 : (0 : ℝ) < x := lt_trans ha hx
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
      have hre : (-s - 1).re = -s.re - 1 := by simp
      rw [hre]
  have hlim : Tendsto (fun x : ℝ => -((x : ℂ) ^ (-s)) / s) atTop (𝓝 0) := by
    have hnorm : Tendsto (fun x : ℝ => ‖-((x : ℂ) ^ (-s)) / s‖) atTop (𝓝 0) := by
      have heq : ∀ x : ℝ, 0 < x → ‖-((x : ℂ) ^ (-s)) / s‖ = x ^ (-s.re) / ‖s‖ := by
        intro x hx
        rw [norm_div, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hx]
        congr 2
      have hbase : Tendsto (fun x : ℝ => x ^ (-s.re) / ‖s‖) atTop (𝓝 0) := by
        have h := (tendsto_rpow_neg_atTop hs).div_const ‖s‖
        simpa using h
      refine hbase.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact (heq x hx).symm
    exact tendsto_zero_iff_norm_tendsto_zero.2 hnorm
  rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim]
  ring

/-- **The inverse of the smoothing: the smoothed kernel integrates to the Dirichlet kernel.** -/
theorem integral_Ioi_smoothed_kernel {s : ℂ} (hs : 0 < s.re) {n : ℝ} (hn : 0 < n) :
    ∫ x in Set.Ioi n, ((x : ℂ) ^ (-s - 1) - (n : ℂ) * (x : ℂ) ^ (-(s + 1) - 1))
      = (n : ℂ) ^ (-s) / (s * (s + 1)) := by
  have hs1 : 0 < (s + 1).re := by
    rw [Complex.add_re, Complex.one_re]
    linarith
  have hsne : s ≠ 0 := by
    intro h; rw [h] at hs; simp at hs
  have hs1ne : s + 1 ≠ 0 := by
    intro h
    rw [h] at hs1
    simp at hs1
  have hnne : ((n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt hn)
  have hint1 : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (-s - 1)) (Set.Ioi n) volume := by
    have hmaj : IntegrableOn (fun x : ℝ => x ^ (-s.re - 1)) (Set.Ioi n) volume :=
      integrableOn_Ioi_rpow_of_lt (by linarith) hn
    have hwne : (-s - 1 : ℂ) ≠ 0 := by
      intro h
      have : (-s - 1).re = 0 := by rw [h]; simp
      simp at this
      linarith
    refine Integrable.mono' hmaj (aestronglyMeasurable_cpow_Ioi hwne hn) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := lt_trans hn hx
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (-s - 1).re = -s.re - 1 := by simp
    rw [hre]
  have hint2 : IntegrableOn (fun x : ℝ => (n : ℂ) * (x : ℂ) ^ (-(s + 1) - 1))
      (Set.Ioi n) volume := by
    have hmaj : IntegrableOn (fun x : ℝ => x ^ (-(s + 1).re - 1)) (Set.Ioi n) volume :=
      integrableOn_Ioi_rpow_of_lt (by linarith) hn
    have hwne : (-(s + 1) - 1 : ℂ) ≠ 0 := by
      intro h
      have : (-(s + 1) - 1).re = 0 := by rw [h]; simp
      simp at this
      linarith
    refine (Integrable.mono' (hmaj.const_mul ‖((n : ℝ) : ℂ)‖)
      ((aestronglyMeasurable_cpow_Ioi hwne hn).const_mul _) ?_)
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hx0 : (0 : ℝ) < x := lt_trans hn hx
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (-(s + 1) - 1).re = -(s + 1).re - 1 := by simp
    rw [hre]
  rw [integral_sub hint1 hint2, integral_Ioi_cpow_neg_succ hs hn,
    integral_const_mul, integral_Ioi_cpow_neg_succ hs1 hn]
  have hpow : ((n : ℝ) : ℂ) * ((n : ℝ) : ℂ) ^ (-(s + 1)) = ((n : ℝ) : ℂ) ^ (-s) := by
    have h1 : ((n : ℝ) : ℂ) = ((n : ℝ) : ℂ) ^ (1 : ℂ) := (Complex.cpow_one _).symm
    nth_rewrite 1 [h1]
    rw [← Complex.cpow_add _ _ hnne]
    congr 1
    ring
  rw [show ((n : ℝ) : ℂ) * (((n : ℝ) : ℂ) ^ (-(s + 1)) / (s + 1))
      = (((n : ℝ) : ℂ) * ((n : ℝ) : ℂ) ^ (-(s + 1))) / (s + 1) by ring, hpow]
  field_simp
  ring

end GaloisForLFunctions.RHTower

end
