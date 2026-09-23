import GaloisForLFunctions.RHTower.Sieve.LogWindowCount
import GaloisForLFunctions.RHTower.Sieve.GallagherDyadicTail

/-!
# The fibre mean square, by one Gallagher application

The direct route.  Every fibre is the logarithmic window of the *same* width `fibreWidth x h` at
`log(x/a)` (`abs_fibre_sum_sub_open_le`, up to one term), the `√x` starting points are
`1/(2√x)`-separated (`log_start_separated`), and across such a shift the window sum changes by at
most five terms (`norm_logWindowSum_sub_le`).  So `sum_le_integral_of_separated` converts the whole
family into a single line integral, which one Gallagher application bounds:

```text
∑_{a ∈ block} ( ∑_{b ∈ fibre a} f(b) )²
    ≤ 8√x · [ 2·fibreWidth² ·(αW₀+β) + 4α/(π²W₀) + 4β/(3π²W₀²) ]  +  102·#block .
```

No block decomposition of the starting points, no maximal window and no Rademacher–Menshov loss
occur: the fibres are multiplicative windows of one width, so the `K'` and `(log h)²` factors of the
additive route are absent.  With `fibreWidth ≍ h/√x` and `#block ≍ √x` the bound is `≍ hα + √x`,
against the target `o(h²√x)` of `AveragedMeanSquare`.
-/

noncomputable section

namespace RHTower.Sieve

open MeasureTheory Finset

/-- `e^t − 1 ≤ 2t` on `[0, 1/2]`. -/
theorem exp_sub_one_le_two_mul_of_le_half {t : ℝ} (ht : 0 ≤ t) (ht2 : t ≤ 1 / 2) :
    Real.exp t - 1 ≤ 2 * t := by
  have h1 : 1 - t ≤ Real.exp (-t) := by
    have := Real.add_one_le_exp (-t)
    linarith
  have h1t : (0 : ℝ) < 1 - t := by linarith
  have hexp : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]
    simp
  have hle : Real.exp t * (1 - t) ≤ 1 := by
    have hpos : (0 : ℝ) < Real.exp t := Real.exp_pos t
    nlinarith [h1, hpos, hexp]
  nlinarith [hle, ht, ht2]

/-- A quantity within one of another is at most twice its square plus two. -/
theorem sq_le_two_sq_add_two {A B : ℝ} (hab : |A - B| ≤ 1) : A ^ (2 : ℕ) ≤ 2 * B ^ (2 : ℕ) + 2 := by
  have habs := abs_le.1 hab
  have hd1 : (0 : ℝ) ≤ 1 - (A - B) := by linarith [habs.2]
  have hd2 : (0 : ℝ) ≤ 1 + (A - B) := by linarith [habs.1]
  nlinarith [mul_nonneg hd1 hd2, sq_nonneg (A - 2 * B)]

/-- **The fibre mean square, bounded by one Gallagher application.** -/
theorem sum_fibreSq_le_gallagher (f : ℕ → ℝ) (hf : ∀ n, |f n| ≤ 1) {x h : ℝ}
    (hx : 16 ≤ x) (hh1 : 1 ≤ h) (hhx : h ≤ Real.sqrt x) {M : ℕ}
    (hMsub : ∀ a ∈ outerBlock x h, innerFibre x h a ⊆ Finset.Icc 1 M)
    {α β W₀ : ℝ} (hW₀ : 0 < W₀) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hG : ∀ T : ℝ, W₀ ≤ T → (∫ w in Set.Icc (-T) T,
      ‖logPoly (fun n => ((f n : ℝ) : ℂ)) (Finset.Icc 1 M) w‖ ^ (2 : ℕ)) ≤ α * T + β) :
    ∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, f b) ^ (2 : ℕ)
      ≤ 8 * Real.sqrt x
          * (2 * fibreWidth x h ^ (2 : ℕ) * (α * W₀ + β)
              + (4 * α / (Real.pi ^ (2 : ℕ) * W₀) + 4 * β / (3 * Real.pi ^ (2 : ℕ) * W₀ ^ (2 : ℕ))))
        + 102 * ((outerBlock x h).card : ℝ) := by
  classical
  have hh0 : (0 : ℝ) ≤ h := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hs4 : (4 : ℝ) ≤ Real.sqrt x := by
    have h16 : Real.sqrt 16 = 4 := by
      rw [show (16 : ℝ) = 4 ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)]
    rw [← h16]
    exact Real.sqrt_le_sqrt hx
  have hs0 : (0 : ℝ) < Real.sqrt x := by linarith
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx0.le
  set c : ℕ → ℂ := fun n => ((f n : ℝ) : ℂ) with hc
  set s : Finset ℕ := Finset.Icc 1 M with hsdef
  set δ : ℝ := fibreWidth x h with hδ
  set σ : ℝ := 1 / (2 * Real.sqrt x) with hσdef
  have hcnorm : ∀ n : ℕ, ‖c n‖ ≤ 1 := by
    intro n
    rw [hc, Complex.norm_real, Real.norm_eq_abs]
    exact hf n
  have hs1 : ∀ n ∈ s, 1 ≤ n := by
    intro n hn
    rw [hsdef, Finset.mem_Icc] at hn
    exact hn.1
  have hδ0 : 0 ≤ δ := by
    rw [hδ, fibreWidth]
    refine Real.log_nonneg ?_
    have : (0 : ℝ) ≤ h / Real.sqrt x := by positivity
    linarith
  have hexpδ : Real.exp δ = 1 + h / Real.sqrt x := by
    rw [hδ, fibreWidth, Real.exp_log (by positivity)]
  have hσ0 : (0 : ℝ) < σ := by rw [hσdef]; positivity
  have hσδ : σ ≤ δ := by
    have ht0 : (0 : ℝ) < h / Real.sqrt x := by positivity
    have ht1 : h / Real.sqrt x ≤ 1 := by
      rw [div_le_one hs0]
      exact hhx
    have hlow : (h / Real.sqrt x) / (1 + h / Real.sqrt x) ≤ δ := by
      have hkey : Real.log (1 / (1 + h / Real.sqrt x)) ≤ 1 / (1 + h / Real.sqrt x) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have hrw : Real.log (1 / (1 + h / Real.sqrt x)) = -δ := by
        rw [hδ, fibreWidth, Real.log_div one_ne_zero (by positivity), Real.log_one]
        ring
      rw [hrw] at hkey
      have hval : 1 / (1 + h / Real.sqrt x) - 1
          = -((h / Real.sqrt x) / (1 + h / Real.sqrt x)) := by
        field_simp
        ring
      rw [hval] at hkey
      linarith
    have hhalf : (h / Real.sqrt x) / (1 + h / Real.sqrt x) ≥ (h / Real.sqrt x) / 2 := by
      refine div_le_div_of_nonneg_left ht0.le (by positivity) (by linarith)
    have hσval : σ ≤ (h / Real.sqrt x) / 2 := by
      rw [hσdef]
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      rw [div_mul_eq_mul_div, le_div_iff₀ hs0]
      nlinarith [hh1, hs0]
    linarith
  have hσsmall : σ ≤ 1 / 2 := by
    rw [hσdef]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  set F : ℝ → ℝ := fun v => ‖logWindowSum c s δ v‖ ^ (2 : ℕ) with hF
  have hF0 : ∀ v, 0 ≤ F v := fun v => by positivity
  have hFint : Integrable F := by
    rw [hF]
    exact integrable_normSq_logWindowSum c s δ
  -- step 1: each fibre sum is the window sum, up to one term
  have hstep1 : ∀ a ∈ outerBlock x h,
      (∑ b ∈ innerFibre x h a, f b) ^ (2 : ℕ) ≤ 2 * F (Real.log (x / a)) + 2 := by
    intro a ha
    have hbase := abs_fibre_sum_sub_open_le hf (by linarith : (4:ℝ) ≤ x) hh0 ha hs1 (hMsub a ha)
    have hcast : logWindowSum c s δ (Real.log (x / a))
        = (((∑ b ∈ s.filter (fun b : ℕ =>
            Real.log (x / a) < Real.log (b : ℝ)
              ∧ Real.log (b : ℝ) ≤ Real.log (x / a) + fibreWidth x h), f b : ℝ)) : ℂ) := by
      rw [logWindowSum_eq_filter, hδ, hc]
      push_cast
      ring
    have hnorm : F (Real.log (x / a))
        = (∑ b ∈ s.filter (fun b : ℕ =>
            Real.log (x / a) < Real.log (b : ℝ)
              ∧ Real.log (b : ℝ) ≤ Real.log (x / a) + fibreWidth x h), f b) ^ (2 : ℕ) := by
      show ‖logWindowSum c s δ (Real.log (x / a))‖ ^ (2 : ℕ) = _
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [hnorm]
    exact sq_le_two_sq_add_two hbase
  -- step 2: the sampling comparison, with an absolute constant
  have hdom : ∀ a ∈ outerBlock x h, ∀ v ∈ Set.Ioc (Real.log (x / a)) (Real.log (x / a) + σ),
      F (Real.log (x / a)) ≤ 2 * F v + 50 := by
    intro a ha v hv
    rw [Set.mem_Ioc] at hv
    rw [mem_outerBlock] at ha
    obtain ⟨⟨ha1, -⟩, halow, -⟩ := ha
    have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha1
    set u : ℝ := Real.log (x / a) with hu
    have hexpu : Real.exp u = x / (a : ℝ) := Real.exp_log (by positivity)
    have hupper : Real.exp u ≤ Real.sqrt x := by
      rw [hexpu, div_le_iff₀ haR]
      nlinarith [halow, hsq, hs0]
    have hupper2 : Real.exp (u + δ) ≤ 2 * Real.sqrt x := by
      rw [Real.exp_add, hexpδ]
      have hfac : (0 : ℝ) ≤ h / Real.sqrt x := by positivity
      have hstep : Real.exp u * (1 + h / Real.sqrt x)
          ≤ Real.sqrt x * (1 + h / Real.sqrt x) :=
        mul_le_mul_of_nonneg_right hupper (by linarith)
      have hval : Real.sqrt x * (1 + h / Real.sqrt x) = Real.sqrt x + h := by
        field_simp
      rw [hval] at hstep
      linarith
    have hvu : v - u ≤ σ := by linarith [hv.2]
    have hvu0 : 0 ≤ v - u := by linarith [hv.1]
    have hexpv : Real.exp (v - u) - 1 ≤ 1 / Real.sqrt x := by
      refine le_trans (exp_sub_one_le_two_mul_of_le_half hvu0 (by linarith)) ?_
      rw [hσdef] at hvu
      have : 2 * (v - u) ≤ 2 * (1 / (2 * Real.sqrt x)) := by linarith
      have heq : 2 * (1 / (2 * Real.sqrt x)) = 1 / Real.sqrt x := by
        field_simp
      linarith [heq ▸ this]
    have hdiff := norm_logWindowSum_sub_le (δ := δ) hcnorm s hs1 (le_of_lt hv.1)
      (by linarith [hv.2, hσδ])
    have hfive : ‖logWindowSum c s δ u - logWindowSum c s δ v‖ ≤ 5 := by
      refine le_trans hdiff ?_
      have hc0 : (0 : ℝ) ≤ Real.exp (v - u) - 1 := by
        have := Real.one_le_exp hvu0
        linarith
      have h1 : Real.exp u * (Real.exp (v - u) - 1) ≤ 1 := by
        have hb := mul_le_mul hupper hexpv hc0 (by positivity)
        have hval : Real.sqrt x * (1 / Real.sqrt x) = 1 := by field_simp
        linarith [hb, hval]
      have h2 : Real.exp (u + δ) * (Real.exp (v - u) - 1) ≤ 2 := by
        have hb := mul_le_mul hupper2 hexpv hc0 (by positivity)
        have hval : 2 * Real.sqrt x * (1 / Real.sqrt x) = 2 := by field_simp
        linarith [hb, hval]
      linarith
    have hle : ‖logWindowSum c s δ u‖ ≤ ‖logWindowSum c s δ v‖ + 5 := by
      have := norm_sub_norm_le (logWindowSum c s δ u) (logWindowSum c s δ v)
      linarith [le_trans this hfive]
    show ‖logWindowSum c s δ u‖ ^ (2 : ℕ) ≤ 2 * ‖logWindowSum c s δ v‖ ^ (2 : ℕ) + 50
    nlinarith [hle, norm_nonneg (logWindowSum c s δ v), norm_nonneg (logWindowSum c s δ u),
      sq_nonneg (‖logWindowSum c s δ v‖ - 5)]
  have hsep : ∀ a ∈ outerBlock x h, ∀ a' ∈ outerBlock x h, a ≠ a' →
      σ ≤ |Real.log (x / a) - Real.log (x / a')| := by
    intro a ha a' ha' hne
    exact log_start_separated (by linarith : (4:ℝ) ≤ x) ha ha' hne
  have hstep2 := sum_le_integral_of_separated hF0 hFint hσ0 hsep hdom
  -- step 3: one Gallagher application
  have hgal : (∫ v, F v) ≤ 2 * δ ^ (2 : ℕ) * (α * W₀ + β)
      + (4 * α / (Real.pi ^ (2 : ℕ) * W₀) + 4 * β / (3 * Real.pi ^ (2 : ℕ) * W₀ ^ (2 : ℕ))) := by
    rcases eq_or_lt_of_le hδ0 with hzero | hpos
    · -- a degenerate width makes the window empty
      have hFzero : ∀ v, F v = 0 := by
        intro v
        show ‖logWindowSum c s δ v‖ ^ (2 : ℕ) = 0
        rw [logWindowSum_eq_filter]
        have hempty : s.filter (fun n : ℕ => v < Real.log n ∧ Real.log n ≤ v + δ) = ∅ := by
          refine Finset.eq_empty_of_forall_notMem fun n hn => ?_
          rw [Finset.mem_filter] at hn
          have := hn.2
          rw [← hzero] at this
          linarith [this.1, this.2]
        rw [hempty]
        simp
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hFzero)]
      simp
      have h1 : (0 : ℝ) ≤ 2 * δ ^ (2 : ℕ) * (α * W₀ + β) := by positivity
      have h2 : (0 : ℝ) ≤ 4 * α / (Real.pi ^ (2 : ℕ) * W₀) := by positivity
      have h3 : (0 : ℝ) ≤ 4 * β / (3 * Real.pi ^ (2 : ℕ) * W₀ ^ (2 : ℕ)) := by positivity
      linarith
    · exact gallagher_split_integral_dyadic c s hpos hW₀ hG
  -- assemble
  have hsum1 : ∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, f b) ^ (2 : ℕ)
      ≤ 2 * (∑ a ∈ outerBlock x h, F (Real.log (x / a)))
        + 2 * ((outerBlock x h).card : ℝ) := by
    have hb := Finset.sum_le_sum hstep1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hb
    linarith [hb]
  have htwo : (2 : ℝ) / σ = 4 * Real.sqrt x := by
    rw [hσdef]
    field_simp
    ring
  rw [htwo] at hstep2
  have hcard0 : (0 : ℝ) ≤ ((outerBlock x h).card : ℝ) := Nat.cast_nonneg _
  have hint0 : (0 : ℝ) ≤ ∫ v, F v :=
    MeasureTheory.integral_nonneg (fun v => hF0 v)
  nlinarith [hsum1, hstep2, hgal, hcard0, hs0, hint0]

end RHTower.Sieve

end
