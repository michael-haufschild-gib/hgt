import Mathlib

/-!
# The Nevanlinna characteristic of an entire function

For a function analytic on all of `ℂ` the counting term of the characteristic vanishes: the divisor
of an analytic function is non-negative, so its negative part — the pole divisor, which is what the
logarithmic counting function of the value `⊤` measures — is zero.  Hence

`T(r, f) = m(r, f) = (2π)⁻¹ ∫ log⁺‖f(r e^{iθ})‖ dθ`.

This is the specialization that every growth argument about entire solutions of algebraic
differential equations uses: for entire functions the characteristic *is* the proximity function, so
statements about `T` are statements about a circle average of `log⁺‖f‖`.
-/

open MeasureTheory Real Complex Metric

namespace GaloisForLFunctions.Nevanlinna

/-- **An entire function has no pole counting term.** -/
theorem logCounting_top_eq_zero_of_analyticOnNhd {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) :
    ValueDistribution.logCounting f ⊤ = 0 := by
  rw [ValueDistribution.logCounting_top]
  have hnn : 0 ≤ MeromorphicOn.divisor f Set.univ :=
    MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf
  rw [negPart_eq_zero.mpr hnn, map_zero]

/-- **The characteristic of an entire function is its proximity function.** -/
theorem characteristic_top_eq_proximity_of_analyticOnNhd {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) :
    ValueDistribution.characteristic f ⊤ = ValueDistribution.proximity f ⊤ := by
  rw [ValueDistribution.characteristic, logCounting_top_eq_zero_of_analyticOnNhd hf, add_zero]

/-- **The characteristic of an entire function as a circle average.** -/
theorem characteristic_top_eq_circleAverage_of_analyticOnNhd {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) :
    ValueDistribution.characteristic f ⊤
      = Real.circleAverage (fun x => Real.posLog ‖f x‖) 0 := by
  rw [characteristic_top_eq_proximity_of_analyticOnNhd hf, ValueDistribution.proximity_top]

/-- **The characteristic is at most the positive logarithm of the maximum modulus.**  The
characteristic of an entire function is a circle average of `log⁺‖f‖`, so any pointwise bound on the
circle bounds it. -/
theorem characteristic_top_le_posLog_of_bound {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) {r M : ℝ}
    (hM : ∀ z ∈ Metric.sphere (0 : ℂ) |r|, ‖f z‖ ≤ M) :
    ValueDistribution.characteristic f ⊤ r ≤ Real.posLog M := by
  have hmero : MeromorphicOn f (Metric.sphere (0 : ℂ) |r|) :=
    fun x _ => (hf x (Set.mem_univ x)).meromorphicAt
  have hint1 : CircleIntegrable (fun x => Real.posLog ‖f x‖) 0 r :=
    hmero.circleIntegrable_posLog_norm
  have hint2 : CircleIntegrable (fun _ : ℂ => Real.posLog M) 0 r := circleIntegrable_const _ _ _
  have hstep : Real.circleAverage (fun x => Real.posLog ‖f x‖) 0 r
      ≤ Real.circleAverage (fun _ : ℂ => Real.posLog M) 0 r := by
    refine Real.circleAverage_mono hint1 hint2 ?_
    intro z hz
    exact Real.posLog_le_posLog (norm_nonneg _) (hM z hz)
  rw [characteristic_top_eq_circleAverage_of_analyticOnNhd hf]
  exact le_trans hstep (le_of_eq (Real.circleAverage_const _ _ _))

/-! ## Arithmetic of the characteristic

Mathlib carries the value-distribution definitions but not their arithmetic.  For entire functions
the characteristic is a circle average of `log⁺‖·‖`, so the submultiplicativity and subadditivity of
`log⁺` transfer directly. -/

/-- Circle integrability of `log⁺‖f‖` for an entire `f`. -/
private theorem circleIntegrable_posLog_norm_of_analytic {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f Set.univ) (r : ℝ) :
    CircleIntegrable (fun x => Real.posLog ‖f x‖) 0 r := by
  have hmero : MeromorphicOn f (Metric.sphere (0 : ℂ) |r|) :=
    fun x _ => (hf x (Set.mem_univ x)).meromorphicAt
  exact hmero.circleIntegrable_posLog_norm

/-- **The characteristic is submultiplicative.**  For entire `f` and `g`,
`T(r, f g) <= T(r, f) + T(r, g)`. -/
theorem characteristic_mul_le {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ) (r : ℝ) :
    ValueDistribution.characteristic (fun z => f z * g z) ⊤ r
      ≤ ValueDistribution.characteristic f ⊤ r + ValueDistribution.characteristic g ⊤ r := by
  have hfg : AnalyticOnNhd ℂ (fun z => f z * g z) Set.univ := fun x hx => (hf x hx).mul (hg x hx)
  have hif := circleIntegrable_posLog_norm_of_analytic hf r
  have hig := circleIntegrable_posLog_norm_of_analytic hg r
  have hifg := circleIntegrable_posLog_norm_of_analytic hfg r
  have hpi : ((fun x => Real.posLog ‖f x‖) + fun x => Real.posLog ‖g x‖)
      = fun x => Real.posLog ‖f x‖ + Real.posLog ‖g x‖ := rfl
  have hsum : Real.circleAverage (fun x => Real.posLog ‖f x‖ + Real.posLog ‖g x‖) 0 r
      = Real.circleAverage (fun x => Real.posLog ‖f x‖) 0 r
        + Real.circleAverage (fun x => Real.posLog ‖g x‖) 0 r := by
    rw [← hpi]
    exact Real.circleAverage_add hif hig
  rw [characteristic_top_eq_circleAverage_of_analyticOnNhd hfg,
    characteristic_top_eq_circleAverage_of_analyticOnNhd hf,
    characteristic_top_eq_circleAverage_of_analyticOnNhd hg, ← hsum]
  refine Real.circleAverage_mono hifg (hif.add hig) ?_
  intro z _
  rw [norm_mul]
  exact Real.posLog_mul

/-- **The characteristic is subadditive up to `log 2`.**  For entire `f` and `g`,
`T(r, f + g) <= T(r, f) + T(r, g) + log 2`. -/
theorem characteristic_add_le {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ) (r : ℝ) :
    ValueDistribution.characteristic (fun z => f z + g z) ⊤ r
      ≤ ValueDistribution.characteristic f ⊤ r + ValueDistribution.characteristic g ⊤ r
        + Real.log 2 := by
  have hfg : AnalyticOnNhd ℂ (fun z => f z + g z) Set.univ := fun x hx => (hf x hx).add (hg x hx)
  have hif := circleIntegrable_posLog_norm_of_analytic hf r
  have hig := circleIntegrable_posLog_norm_of_analytic hg r
  have hifg := circleIntegrable_posLog_norm_of_analytic hfg r
  have hic : CircleIntegrable (fun _ : ℂ => Real.log 2) 0 r := circleIntegrable_const _ _ _
  have hpi : ((fun x => Real.posLog ‖f x‖) + fun x => Real.posLog ‖g x‖)
      = fun x => Real.posLog ‖f x‖ + Real.posLog ‖g x‖ := rfl
  have hsum1 : Real.circleAverage (fun x => Real.posLog ‖f x‖ + Real.posLog ‖g x‖) 0 r
      = Real.circleAverage (fun x => Real.posLog ‖f x‖) 0 r
        + Real.circleAverage (fun x => Real.posLog ‖g x‖) 0 r := by
    rw [← hpi]
    exact Real.circleAverage_add hif hig
  have hpi2 : ((fun x => Real.posLog ‖f x‖ + Real.posLog ‖g x‖) + fun _ : ℂ => Real.log 2)
      = fun x => (Real.posLog ‖f x‖ + Real.posLog ‖g x‖) + Real.log 2 := rfl
  have hifsum : CircleIntegrable (fun x => Real.posLog ‖f x‖ + Real.posLog ‖g x‖) 0 r := by
    rw [← hpi]
    exact hif.add hig
  have hsum : Real.circleAverage
      (fun x => (Real.posLog ‖f x‖ + Real.posLog ‖g x‖) + Real.log 2) 0 r
      = (Real.circleAverage (fun x => Real.posLog ‖f x‖) 0 r
          + Real.circleAverage (fun x => Real.posLog ‖g x‖) 0 r) + Real.log 2 := by
    rw [← hpi2, Real.circleAverage_add hifsum hic, hsum1, Real.circleAverage_const]
  rw [characteristic_top_eq_circleAverage_of_analyticOnNhd hfg,
    characteristic_top_eq_circleAverage_of_analyticOnNhd hf,
    characteristic_top_eq_circleAverage_of_analyticOnNhd hg, ← hsum]
  refine Real.circleAverage_mono hifg (hifsum.add hic) ?_
  intro z _
  have hmono : Real.posLog ‖f z + g z‖ ≤ Real.posLog (‖f z‖ + ‖g z‖) :=
    Real.posLog_le_posLog (norm_nonneg _) (norm_add_le _ _)
  have hadd : Real.posLog (‖f z‖ + ‖g z‖)
      ≤ Real.log 2 + Real.posLog ‖f z‖ + Real.posLog ‖g z‖ := Real.posLog_add
  linarith


/-- **The characteristic of a constant.** -/
theorem characteristic_const_eq (c : ℂ) (r : ℝ) :
    ValueDistribution.characteristic (fun _ : ℂ => c) ⊤ r = Real.posLog ‖c‖ := by
  have hconst : AnalyticOnNhd ℂ (fun _ : ℂ => c) Set.univ := fun x _ => analyticAt_const
  rw [characteristic_top_eq_circleAverage_of_analyticOnNhd hconst, Real.circleAverage_const]

/-- **The characteristic of a power.** -/
theorem characteristic_pow_le {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ) (n : ℕ) (r : ℝ) :
    ValueDistribution.characteristic (fun z => f z ^ n) ⊤ r
      ≤ (n : ℝ) * ValueDistribution.characteristic f ⊤ r := by
  induction n with
  | zero =>
      have hfun : (fun z : ℂ => f z ^ (0 : ℕ)) = fun _ : ℂ => (1 : ℂ) := by
        funext z
        rw [pow_zero]
      rw [hfun, characteristic_const_eq]
      simp
  | succ k ih =>
      have hpow : AnalyticOnNhd ℂ (fun z => f z ^ k) Set.univ := fun x hx => (hf x hx).pow k
      have h := characteristic_mul_le hpow hf r
      have hfun : (fun z : ℂ => f z ^ (k + 1)) = fun z : ℂ => f z ^ k * f z := by
        funext z
        rw [pow_succ]
      rw [hfun]
      push_cast
      linarith

/-- **The characteristic of a finite product.** -/
theorem characteristic_prod_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, AnalyticOnNhd ℂ (f i) Set.univ) (r : ℝ) :
    ValueDistribution.characteristic (fun z => ∏ i ∈ s, f i z) ⊤ r
      ≤ ∑ i ∈ s, ValueDistribution.characteristic (f i) ⊤ r := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hfun : (fun z : ℂ => ∏ i ∈ (∅ : Finset ι), f i z) = fun _ : ℂ => (1 : ℂ) := by
        funext z
        simp
      rw [hfun, characteristic_const_eq]
      simp
  | insert j t hjt ih =>
      have hfj : AnalyticOnNhd ℂ (f j) Set.univ := hf j (Finset.mem_insert_self j t)
      have hft : ∀ i ∈ t, AnalyticOnNhd ℂ (f i) Set.univ :=
        fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hprod : AnalyticOnNhd ℂ (fun z => ∏ i ∈ t, f i z) Set.univ := by
        have hpi : (fun z : ℂ => ∏ i ∈ t, f i z) = ∏ i ∈ t, f i := by
          funext z
          simp
        rw [hpi]
        intro x hx
        exact Finset.analyticAt_prod t fun i hi => hft i hi x hx
      have hfun : (fun z : ℂ => ∏ i ∈ insert j t, f i z)
          = fun z : ℂ => f j z * ∏ i ∈ t, f i z := by
        funext z
        rw [Finset.prod_insert hjt]
      rw [hfun, Finset.sum_insert hjt]
      have h := characteristic_mul_le hfj hprod r
      have h2 := ih hft
      linarith

/-- **The characteristic of a finite sum.**  Each addition costs one `log 2`. -/
theorem characteristic_sum_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, AnalyticOnNhd ℂ (f i) Set.univ) (r : ℝ) :
    ValueDistribution.characteristic (fun z => ∑ i ∈ s, f i z) ⊤ r
      ≤ (∑ i ∈ s, ValueDistribution.characteristic (f i) ⊤ r) + s.card * Real.log 2 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hfun : (fun z : ℂ => ∑ i ∈ (∅ : Finset ι), f i z) = fun _ : ℂ => (0 : ℂ) := by
        funext z
        simp
      rw [hfun, characteristic_const_eq]
      simp
  | insert j t hjt ih =>
      have hfj : AnalyticOnNhd ℂ (f j) Set.univ := hf j (Finset.mem_insert_self j t)
      have hft : ∀ i ∈ t, AnalyticOnNhd ℂ (f i) Set.univ :=
        fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hsum : AnalyticOnNhd ℂ (fun z => ∑ i ∈ t, f i z) Set.univ := by
        have hpi : (fun z : ℂ => ∑ i ∈ t, f i z) = ∑ i ∈ t, f i := by
          funext z
          simp
        rw [hpi]
        intro x hx
        exact Finset.analyticAt_sum t fun i hi => hft i hi x hx
      have hfun : (fun z : ℂ => ∑ i ∈ insert j t, f i z)
          = fun z : ℂ => f j z + ∑ i ∈ t, f i z := by
        funext z
        rw [Finset.sum_insert hjt]
      rw [hfun, Finset.sum_insert hjt, Finset.card_insert_of_notMem hjt]
      have h := characteristic_add_le hfj hsum r
      have h2 := ih hft
      push_cast
      linarith

end GaloisForLFunctions.Nevanlinna
