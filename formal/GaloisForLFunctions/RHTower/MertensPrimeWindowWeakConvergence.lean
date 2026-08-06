import GaloisForLFunctions.RHTower.MertensFirst

/-!
# Weak convergence of the Mertens prime window

The finite prime measures

```text
ν_N = (1 / log N) ∑_{p ≤ N} (log p / p) δ_{log p / log N}
```

converge weakly to Lebesgue measure on `[0, 1]`.  The only arithmetic input is Mertens' first
theorem in prime form, `|∑_{p ≤ N} (log p)/p - log N| ≤ C`; everything else is Abel summation, one
logarithmic substitution, and the Weierstrass approximation theorem.

Concretely, for every function `g` continuous on `[0, 1]`,

```text
(1 / log N) ∑_{p ≤ N} (log p / p) g(log p / log N) → ∫₀¹ g.
```
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## The prime log-density weight -/

/-- The prime logarithmic density weight `log p / p`, extended by zero off the primes. -/
def mertensPrimeWeight (n : ℕ) : ℝ := if n.Prime then Real.log n / n else 0

theorem mertensPrimeWeight_nonneg (n : ℕ) : 0 ≤ mertensPrimeWeight n := by
  unfold mertensPrimeWeight
  split_ifs with h
  · exact div_nonneg (Real.log_nonneg (by exact_mod_cast h.one_le)) (by positivity)
  · exact le_rfl

/-- The cumulative prime log-density `∑_{p ≤ N} (log p) / p`. -/
def mertensPrimeWeightSum (N : ℕ) : ℝ := ∑ n ∈ Finset.Icc 0 N, mertensPrimeWeight n

theorem mertensPrimeWeightSum_eq (N : ℕ) :
    mertensPrimeWeightSum N = ∑ n ∈ Finset.Icc 1 N with n.Prime, Real.log n / (n : ℝ) := by
  rw [mertensPrimeWeightSum]
  simp only [mertensPrimeWeight]
  rw [show Finset.Icc 0 N = insert 0 (Finset.Icc 1 N) by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega,
    Finset.sum_insert (by simp), Finset.sum_filter]
  simp

theorem mertensPrimeWeightSum_nonneg (N : ℕ) : 0 ≤ mertensPrimeWeightSum N :=
  Finset.sum_nonneg fun n _ => mertensPrimeWeight_nonneg n

/-- The uniform Mertens error constant of the prime log-density. -/
def mertensPrimeWindowBound : ℝ := (Real.log 4 + 4) + (8 + Mertens.mertensTail)

theorem mertensPrimeWindowBound_nonneg : 0 ≤ mertensPrimeWindowBound := by
  have htail : 0 ≤ Mertens.mertensTail := by
    rw [Mertens.mertensTail]
    exact tsum_nonneg fun i => by positivity
  have hlog : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [mertensPrimeWindowBound]
  positivity

/-- **Mertens' first theorem in prime form.** -/
theorem abs_mertensPrimeWeightSum_sub_log_le (N : ℕ) (hN : 1 ≤ N) :
    |mertensPrimeWeightSum N - Real.log N| ≤ mertensPrimeWindowBound := by
  rw [mertensPrimeWeightSum_eq]
  exact Mertens.mertens_first_prime N hN

theorem abs_mertensPrimeWeightSum_floor_sub_log_le {t : ℝ} (ht : 2 ≤ t) :
    |mertensPrimeWeightSum ⌊t⌋₊ - Real.log t| ≤ mertensPrimeWindowBound + 1 := by
  have ht0 : 0 ≤ t := by linarith
  have hfloor1 : 1 ≤ ⌊t⌋₊ := (Nat.one_le_floor_iff t).mpr (by linarith)
  have hfloorpos : (0 : ℝ) < ⌊t⌋₊ := by exact_mod_cast (Nat.zero_lt_of_lt hfloor1)
  have hfloorle : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le ht0
  have hlt : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
  have hratio0 : 0 < t / (⌊t⌋₊ : ℝ) := div_pos (by linarith) hfloorpos
  have hlogdiff1 : Real.log t - Real.log (⌊t⌋₊ : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos hratio0
    rw [Real.log_div (by linarith) hfloorpos.ne'] at h
    nlinarith [(div_le_iff₀ hfloorpos).mpr (by nlinarith : t ≤ 2 * (⌊t⌋₊ : ℝ))]
  have hprime := abs_mertensPrimeWeightSum_sub_log_le ⌊t⌋₊ hfloor1
  calc
    |mertensPrimeWeightSum ⌊t⌋₊ - Real.log t| =
        |(mertensPrimeWeightSum ⌊t⌋₊ - Real.log ⌊t⌋₊) +
          (Real.log ⌊t⌋₊ - Real.log t)| := by ring_nf
    _ ≤ |mertensPrimeWeightSum ⌊t⌋₊ - Real.log ⌊t⌋₊| +
        |Real.log ⌊t⌋₊ - Real.log t| := abs_add_le _ _
    _ ≤ mertensPrimeWindowBound + 1 := by
      rw [abs_of_nonpos (sub_nonpos.mpr (Real.log_le_log hfloorpos hfloorle))]
      linarith

theorem mertensPrimeWeightSum_le (N : ℕ) (hN : 1 ≤ N) :
    mertensPrimeWeightSum N ≤ Real.log N + mertensPrimeWindowBound := by
  have h := abs_mertensPrimeWeightSum_sub_log_le N hN
  have := abs_le.mp h
  linarith [this.2]

/-! ## The window functional -/

/-- The finite Mertens prime-window functional
`∑_{p ≤ N} (log p / p) g(log p / log N)`. -/
def mertensPrimeWindow (g : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 N, g (Real.log n / Real.log N) * mertensPrimeWeight n

private def windowTest (g : ℝ → ℝ) (N : ℕ) (t : ℝ) : ℝ := g (Real.log t / Real.log N)

private def windowTestDeriv (g : ℝ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  deriv g (Real.log t / Real.log N) * (1 / (t * Real.log N))

private theorem hasDerivAt_windowTest {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {N : ℕ} (hN : 1 < N)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (windowTest g N) (windowTestDeriv g N t) t := by
  have hlogN : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hz : HasDerivAt (fun x : ℝ => Real.log x / Real.log N) (1 / (t * Real.log N)) t := by
    have h := (Real.hasDerivAt_log ht0).div_const (Real.log (N : ℝ))
    rw [show 1 / (t * Real.log (N : ℝ)) = t⁻¹ / Real.log (N : ℝ) by field_simp]
    exact h
  have hgd : HasDerivAt g (deriv g (Real.log t / Real.log N)) (Real.log t / Real.log N) :=
    ((hg.differentiable (by norm_num)) (Real.log t / Real.log N)).hasDerivAt
  exact hgd.comp t hz

private theorem continuousOn_windowTestDeriv {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {N : ℕ}
    (hN : 1 < N) : ContinuousOn (windowTestDeriv g N) (Ioi 0) := by
  have hlogN : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  have hderiv : Continuous (deriv g) := hg.continuous_deriv le_rfl
  intro t ht
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hlog : ContinuousAt Real.log t := Real.continuousAt_log ht0
  have hz : ContinuousAt (fun x : ℝ => Real.log x / Real.log N) t := hlog.div_const _
  have hnum : ContinuousAt (fun x : ℝ => deriv g (Real.log x / Real.log N)) t :=
    hderiv.continuousAt.comp hz
  have hden : ContinuousAt (fun x : ℝ => 1 / (x * Real.log N)) t :=
    continuousAt_const.div (continuousAt_id.mul continuousAt_const) (mul_ne_zero ht0 hlogN)
  exact (hnum.mul hden).continuousWithinAt

private theorem windowTest_eq_of_le {g : ℝ → ℝ} {N : ℕ} (hN : 2 ≤ N) :
    windowTest g N (N : ℝ) = g 1 := by
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two hN))).ne'
  rw [windowTest, div_self hlogN]

/-! ## Abel summation -/

private theorem mertensPrimeWindow_abel {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {N : ℕ} (hN : 2 ≤ N) :
    mertensPrimeWindow g N =
      g 1 * mertensPrimeWeightSum N -
        ∫ t in Ioc (2 : ℝ) N, windowTestDeriv g N t * mertensPrimeWeightSum ⌊t⌋₊ := by
  have hN' : 1 < N := lt_of_lt_of_le one_lt_two hN
  have hdiff : ∀ t ∈ Icc ((2 : ℕ) : ℝ) ((N : ℕ) : ℝ),
      DifferentiableAt ℝ (windowTest g N) t := by
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := by exact_mod_cast ht.1
    exact (hasDerivAt_windowTest hg hN' (by linarith)).differentiableAt
  have hcontDeriv : ContinuousOn (deriv (windowTest g N)) (Icc ((2 : ℕ) : ℝ) ((N : ℕ) : ℝ)) := by
    refine ContinuousOn.congr
      ((continuousOn_windowTestDeriv hg hN').mono ?_) (fun t ht => ?_)
    · intro t ht
      have ht2 : (2 : ℝ) ≤ t := by exact_mod_cast ht.1
      exact lt_of_lt_of_le two_pos ht2
    · have ht2 : (2 : ℝ) ≤ t := by exact_mod_cast ht.1
      exact (hasDerivAt_windowTest hg hN' (by linarith)).deriv
  have hint : IntegrableOn (deriv (windowTest g N)) (Icc ((2 : ℕ) : ℝ) ((N : ℕ) : ℝ)) :=
    hcontDeriv.integrableOn_Icc
  have hab := sum_mul_eq_sub_sub_integral_mul' mertensPrimeWeight (n := 2) (m := N) hN hdiff hint
  have hsplit : mertensPrimeWindow g N =
      windowTest g N 2 * mertensPrimeWeight 2 +
        ∑ k ∈ Finset.Ioc 2 N, windowTest g N k * mertensPrimeWeight k := by
    rw [mertensPrimeWindow, show Finset.Icc 0 N = Finset.Icc 0 2 ∪ Finset.Ioc 2 N by
        ext n
        simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
        omega,
      Finset.sum_union (by
        rw [Finset.disjoint_left]
        intro a ha hb
        simp only [Finset.mem_Icc] at ha
        simp only [Finset.mem_Ioc] at hb
        omega)]
    congr 1
    · rw [show Finset.Icc 0 2 = ({0, 1, 2} : Finset ℕ) by decide]
      norm_num [mertensPrimeWeight, windowTest]
  have hlowweight : mertensPrimeWeight 2 = Real.log 2 / 2 := by
    norm_num [mertensPrimeWeight]
  have hlowsum : ∑ k ∈ Finset.Icc 0 2, mertensPrimeWeight k = Real.log 2 / 2 := by
    rw [show Finset.Icc 0 2 = ({0, 1, 2} : Finset ℕ) by decide]
    norm_num [mertensPrimeWeight]
  rw [hsplit, hab, windowTest_eq_of_le hN]
  have hcong : (∫ t in Ioc ((2 : ℕ) : ℝ) ((N : ℕ) : ℝ),
      deriv (windowTest g N) t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, mertensPrimeWeight k) =
      ∫ t in Ioc (2 : ℝ) (N : ℝ),
        windowTestDeriv g N t * mertensPrimeWeightSum ⌊t⌋₊ := by
    push_cast
    refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
    have ht2 : (2 : ℝ) < t := ht.1
    rw [(hasDerivAt_windowTest hg hN' (by linarith)).deriv, mertensPrimeWeightSum]
  push_cast at hcong ⊢
  rw [hcong, hlowweight, hlowsum, mertensPrimeWeightSum]
  ring

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology MeasureTheory Set
open scoped BigOperators

/-! ## The Mertens main term -/

private def windowMain (g : ℝ → ℝ) (N : ℕ) : ℝ :=
  g 1 * Real.log N - ∫ t in Ioc (2 : ℝ) N, windowTestDeriv g N t * Real.log t

private theorem continuousOn_windowTestDeriv_Icc {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {N : ℕ}
    (hN : 2 ≤ N) : ContinuousOn (windowTestDeriv g N) (Icc (2 : ℝ) N) :=
  (continuousOn_windowTestDeriv hg (lt_of_lt_of_le one_lt_two hN)).mono
    (fun _ ht => lt_of_lt_of_le two_pos ht.1)

private theorem integrableOn_windowTestDeriv {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {N : ℕ}
    (hN : 2 ≤ N) : IntegrableOn (windowTestDeriv g N) (Icc (2 : ℝ) N) :=
  (continuousOn_windowTestDeriv_Icc hg hN).integrableOn_Icc

private theorem continuousOn_log_Icc {N : ℕ} (_hN : 2 ≤ N) :
    ContinuousOn (fun t : ℝ => Real.log t) (Icc (2 : ℝ) N) :=
  Real.continuousOn_log.mono (by
    intro t ht
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith [ht.1])

private theorem integrableOn_windowTestDeriv_mul_log {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {N : ℕ}
    (hN : 2 ≤ N) :
    IntegrableOn (fun t : ℝ => windowTestDeriv g N t * Real.log t) (Icc (2 : ℝ) N) :=
  ((continuousOn_windowTestDeriv_Icc hg hN).mul (continuousOn_log_Icc hN)).integrableOn_Icc

private theorem integrableOn_windowTestDeriv_mul_sum {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {N : ℕ}
    (hN : 2 ≤ N) :
    IntegrableOn (fun t : ℝ => windowTestDeriv g N t * mertensPrimeWeightSum ⌊t⌋₊)
      (Icc (2 : ℝ) N) := by
  simpa only [mertensPrimeWeightSum] using
    (integrableOn_mul_sum_Icc mertensPrimeWeight (m := 0) (by norm_num : (0 : ℝ) ≤ 2)
      (integrableOn_windowTestDeriv hg hN))

private theorem mertensPrimeWindow_sub_windowMain {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {N : ℕ}
    (hN : 2 ≤ N) :
    mertensPrimeWindow g N - windowMain g N =
      g 1 * (mertensPrimeWeightSum N - Real.log N) -
        ∫ t in Ioc (2 : ℝ) N,
          windowTestDeriv g N t * (mertensPrimeWeightSum ⌊t⌋₊ - Real.log t) := by
  have hlog' := (integrableOn_windowTestDeriv_mul_log hg hN).mono_set Ioc_subset_Icc_self
  have hsum' := (integrableOn_windowTestDeriv_mul_sum hg hN).mono_set Ioc_subset_Icc_self
  have hsplit :
      (∫ t in Ioc (2 : ℝ) N, windowTestDeriv g N t * mertensPrimeWeightSum ⌊t⌋₊) =
      (∫ t in Ioc (2 : ℝ) N, windowTestDeriv g N t * Real.log t) +
      ∫ t in Ioc (2 : ℝ) N,
        windowTestDeriv g N t * (mertensPrimeWeightSum ⌊t⌋₊ - Real.log t) := by
    rw [← MeasureTheory.integral_add hlog' (by
      have : IntegrableOn (fun t : ℝ =>
          windowTestDeriv g N t * mertensPrimeWeightSum ⌊t⌋₊ -
            windowTestDeriv g N t * Real.log t) (Ioc (2 : ℝ) N) := hsum'.sub hlog'
      refine this.congr_fun (fun t _ => by ring) measurableSet_Ioc)]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    ring
  rw [mertensPrimeWindow_abel hg hN, windowMain, hsplit]
  ring

private theorem abs_windowTestDeriv_le {g : ℝ → ℝ} {N : ℕ} (hN : 2 ≤ N) {M : ℝ}
    (hM : ∀ u ∈ Icc (0 : ℝ) 1, |deriv g u| ≤ M) {t : ℝ} (ht : t ∈ Ioc (2 : ℝ) (N : ℝ)) :
    |windowTestDeriv g N t| ≤ M * (1 / (t * Real.log N)) := by
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have ht0 : 0 < t := lt_trans two_pos ht.1
  have hmem : Real.log t / Real.log N ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (Real.log_nonneg (by linarith [ht.1])) hlogN.le
    · rw [div_le_one hlogN]
      exact Real.log_le_log ht0 ht.2
  have hpos : 0 < 1 / (t * Real.log (N : ℝ)) := by positivity
  rw [windowTestDeriv, abs_mul, abs_of_pos hpos]
  exact mul_le_mul_of_nonneg_right (hM _ hmem) hpos.le

private theorem integral_inv_Ioc {N : ℕ} (hN : 2 ≤ N) :
    (∫ t in Ioc (2 : ℝ) (N : ℝ), t⁻¹) = Real.log (N : ℝ) - Real.log 2 := by
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  rw [← intervalIntegral.integral_of_le hNr, integral_inv_of_pos (by norm_num) (by linarith)]
  rw [Real.log_div (by linarith) (by norm_num)]

private theorem abs_mertensPrimeWindow_sub_windowMain_le {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    {N : ℕ} (hN : 2 ≤ N) {M : ℝ} (hM : ∀ u ∈ Icc (0 : ℝ) 1, |deriv g u| ≤ M) :
    |mertensPrimeWindow g N - windowMain g N| ≤
      (mertensPrimeWindowBound + 1) * (|g 1| + M) := by
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hD : (0 : ℝ) ≤ mertensPrimeWindowBound + 1 := by
    linarith [mertensPrimeWindowBound_nonneg]
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 ⟨le_rfl, by norm_num⟩)
  set D : ℝ := mertensPrimeWindowBound + 1 with hDdef
  have hlog' := (integrableOn_windowTestDeriv_mul_log hg hN).mono_set Ioc_subset_Icc_self
  have hsum' := (integrableOn_windowTestDeriv_mul_sum hg hN).mono_set Ioc_subset_Icc_self
  have herr : IntegrableOn (fun t : ℝ =>
      windowTestDeriv g N t * (mertensPrimeWeightSum ⌊t⌋₊ - Real.log t))
      (Ioc (2 : ℝ) N) := by
    refine (hsum'.sub hlog').congr_fun
      (fun t _ => by simp only [Pi.sub_apply]; ring) measurableSet_Ioc
  have hMajor : IntegrableOn (fun t : ℝ => D * M * (1 / (t * Real.log N)))
      (Ioc (2 : ℝ) N) := by
    have hcont : ContinuousOn (fun t : ℝ => D * M * (1 / (t * Real.log N))) (Icc (2 : ℝ) N) := by
      intro t ht
      have ht0 : t ≠ 0 := by
        have := ht.1
        intro h
        rw [h] at this
        linarith
      exact (continuousAt_const.div (continuousAt_id.mul continuousAt_const)
        (mul_ne_zero ht0 hlogN.ne')).continuousWithinAt.const_smul (D * M) |>.congr
          (fun s _ => rfl) rfl
    exact (hcont.integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hAbsInt : IntegrableOn (fun t : ℝ =>
      |windowTestDeriv g N t * (mertensPrimeWeightSum ⌊t⌋₊ - Real.log t)|)
      (Ioc (2 : ℝ) N) := herr.abs
  have hle : ∀ t ∈ Ioc (2 : ℝ) (N : ℝ),
      |windowTestDeriv g N t * (mertensPrimeWeightSum ⌊t⌋₊ - Real.log t)| ≤
        D * M * (1 / (t * Real.log N)) := by
    intro t ht
    have h1 := abs_windowTestDeriv_le hN hM ht
    have h2 : |mertensPrimeWeightSum ⌊t⌋₊ - Real.log t| ≤ D :=
      abs_mertensPrimeWeightSum_floor_sub_log_le (le_of_lt ht.1)
    have hpos : (0 : ℝ) ≤ 1 / (t * Real.log N) := by
      have ht0 : 0 < t := lt_trans two_pos ht.1
      positivity
    calc |windowTestDeriv g N t * (mertensPrimeWeightSum ⌊t⌋₊ - Real.log t)|
        = |windowTestDeriv g N t| * |mertensPrimeWeightSum ⌊t⌋₊ - Real.log t| := abs_mul _ _
      _ ≤ (M * (1 / (t * Real.log N))) * D :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ = D * M * (1 / (t * Real.log N)) := by ring
  have hintbound : |∫ t in Ioc (2 : ℝ) N,
      windowTestDeriv g N t * (mertensPrimeWeightSum ⌊t⌋₊ - Real.log t)| ≤ D * M := by
    calc |∫ t in Ioc (2 : ℝ) N,
          windowTestDeriv g N t * (mertensPrimeWeightSum ⌊t⌋₊ - Real.log t)|
        ≤ ∫ t in Ioc (2 : ℝ) N,
            |windowTestDeriv g N t * (mertensPrimeWeightSum ⌊t⌋₊ - Real.log t)| :=
          abs_integral_le_integral_abs
      _ ≤ ∫ t in Ioc (2 : ℝ) N, D * M * (1 / (t * Real.log N)) :=
          setIntegral_mono_on hAbsInt hMajor measurableSet_Ioc hle
      _ = (D * M / Real.log N) * (Real.log (N : ℝ) - Real.log 2) := by
          have hrw : (fun t : ℝ => D * M * (1 / (t * Real.log N)))
              = fun t : ℝ => (D * M / Real.log N) * t⁻¹ := by
            funext t
            field_simp
          rw [hrw, MeasureTheory.integral_const_mul, integral_inv_Ioc hN]
      _ ≤ D * M := by
          have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
          rw [div_mul_eq_mul_div, div_le_iff₀ hlogN]
          nlinarith [mul_nonneg hD hM0]
  have hend : |g 1 * (mertensPrimeWeightSum N - Real.log N)| ≤ D * |g 1| := by
    rw [abs_mul]
    have h := abs_mertensPrimeWeightSum_sub_log_le N (by omega)
    have : |mertensPrimeWeightSum N - Real.log N| ≤ D := by
      dsimp [D, hDdef]; linarith
    calc |g 1| * |mertensPrimeWeightSum N - Real.log N| ≤ |g 1| * D :=
          mul_le_mul_of_nonneg_left this (abs_nonneg _)
      _ = D * |g 1| := by ring
  rw [mertensPrimeWindow_sub_windowMain hg hN]
  calc |g 1 * (mertensPrimeWeightSum N - Real.log N) -
        ∫ t in Ioc (2 : ℝ) N,
          windowTestDeriv g N t * (mertensPrimeWeightSum ⌊t⌋₊ - Real.log t)|
      ≤ |g 1 * (mertensPrimeWeightSum N - Real.log N)| +
        |∫ t in Ioc (2 : ℝ) N,
          windowTestDeriv g N t * (mertensPrimeWeightSum ⌊t⌋₊ - Real.log t)| := abs_sub _ _
    _ ≤ D * |g 1| + D * M := add_le_add hend hintbound
    _ = D * (|g 1| + M) := by ring

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology MeasureTheory Set
open scoped BigOperators

/-! ## The logarithmic substitution -/

private theorem hasDerivAt_logRatio {N : ℕ} (hN : 2 ≤ N) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => Real.log t / Real.log N) (1 / (x * Real.log N)) x := by
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : Real.log (N : ℝ) ≠ 0 := (Real.log_pos (by linarith)).ne'
  have h := (Real.hasDerivAt_log (ne_of_gt hx)).div_const (Real.log (N : ℝ))
  rw [show 1 / (x * Real.log (N : ℝ)) = x⁻¹ / Real.log (N : ℝ) by field_simp]
  exact h

private theorem windowMain_integral_eq {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {N : ℕ} (hN : 2 ≤ N) :
    (∫ t in Ioc (2 : ℝ) N, windowTestDeriv g N t * Real.log t) =
      Real.log (N : ℝ) * ∫ u in (Real.log 2 / Real.log N)..1, u * deriv g u := by
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have huIcc : uIcc (2 : ℝ) (N : ℝ) = Icc (2 : ℝ) (N : ℝ) := uIcc_of_le hNr
  have hderiv : ∀ x ∈ uIcc (2 : ℝ) (N : ℝ),
      HasDerivAt (fun t : ℝ => Real.log t / Real.log N) (1 / (x * Real.log N)) x := by
    intro x hx
    rw [huIcc] at hx
    exact hasDerivAt_logRatio hN (lt_of_lt_of_le two_pos hx.1)
  have hcont' : ContinuousOn (fun x : ℝ => 1 / (x * Real.log N)) (uIcc (2 : ℝ) (N : ℝ)) := by
    rw [huIcc]
    intro x hx
    have hx0 : x ≠ 0 := by
      have := hx.1
      intro h
      rw [h] at this
      linarith
    exact (continuousAt_const.div (continuousAt_id.mul continuousAt_const)
      (mul_ne_zero hx0 hlogN.ne')).continuousWithinAt
  have hcontg : Continuous (fun u : ℝ => Real.log (N : ℝ) * (u * deriv g u)) :=
    continuous_const.mul (continuous_id.mul (hg.continuous_deriv le_rfl))
  have hsub := intervalIntegral.integral_deriv_smul_comp hderiv hcont' hcontg
  rw [show Real.log (2 : ℝ) / Real.log (N : ℝ) =
      (fun t : ℝ => Real.log t / Real.log N) (2 : ℝ) from rfl]
  rw [← intervalIntegral.integral_of_le hNr]
  rw [show (1 : ℝ) = (fun t : ℝ => Real.log t / Real.log N) (N : ℝ) by
      simp [div_self hlogN.ne']]
  rw [← intervalIntegral.integral_const_mul, ← hsub]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [huIcc] at hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le two_pos hx.1
  simp only [Function.comp_apply, smul_eq_mul, windowTestDeriv]
  field_simp

private theorem windowMain_div_log {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) {N : ℕ} (hN : 2 ≤ N) :
    windowMain g N / Real.log N =
      g 1 - ∫ u in (Real.log 2 / Real.log N)..1, u * deriv g u := by
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  rw [windowMain, windowMain_integral_eq hg hN]
  field_simp

private theorem tendsto_windowMain_div_log {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) :
    Tendsto (fun N : ℕ => windowMain g N / Real.log N) atTop
      (nhds (g 1 - ∫ u in (0 : ℝ)..1, u * deriv g u)) := by
  have hcontg : Continuous (fun u : ℝ => u * deriv g u) :=
    continuous_id.mul (hg.continuous_deriv le_rfl)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcontg.continuousOn
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0 ⟨le_rfl, by norm_num⟩)
  have hlogtop : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ha : Tendsto (fun N : ℕ => Real.log 2 / Real.log N) atTop (nhds 0) :=
    Tendsto.div_atTop tendsto_const_nhds hlogtop
  have hkey : Tendsto
      (fun N : ℕ => ∫ u in (Real.log 2 / Real.log N)..1, u * deriv g u) atTop
      (nhds (∫ u in (0 : ℝ)..1, u * deriv g u)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hsq : ∀ᶠ N : ℕ in atTop,
        ‖(∫ u in (Real.log 2 / Real.log N)..1, u * deriv g u) -
          ∫ u in (0 : ℝ)..1, u * deriv g u‖ ≤ C * (Real.log 2 / Real.log N) := by
      filter_upwards [Filter.eventually_ge_atTop 2] with N hN
      have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
      have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
      have haN0 : 0 ≤ Real.log 2 / Real.log (N : ℝ) := by positivity
      have haN1 : Real.log 2 / Real.log (N : ℝ) ≤ 1 := by
        rw [div_le_one hlogN]
        exact Real.log_le_log (by norm_num) hNr
      have hint01 : IntervalIntegrable (fun u : ℝ => u * deriv g u) volume 0 1 :=
        hcontg.intervalIntegrable 0 1
      have hint0a : IntervalIntegrable (fun u : ℝ => u * deriv g u) volume 0
          (Real.log 2 / Real.log (N : ℝ)) := hcontg.intervalIntegrable _ _
      have hsplit := intervalIntegral.integral_interval_sub_left hint01 hint0a
      rw [← hsplit]
      have hbound : ‖∫ u in (0 : ℝ)..(Real.log 2 / Real.log (N : ℝ)), u * deriv g u‖ ≤
          C * |Real.log 2 / Real.log (N : ℝ) - 0| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => ?_
        rw [uIoc_of_le haN0] at hu
        exact hC u ⟨le_of_lt hu.1, le_trans hu.2 haN1⟩
      have hrw : ((∫ u in (0 : ℝ)..1, u * deriv g u) -
          ∫ u in (0 : ℝ)..(Real.log 2 / Real.log (N : ℝ)), u * deriv g u) -
          (∫ u in (0 : ℝ)..1, u * deriv g u) =
          -∫ u in (0 : ℝ)..(Real.log 2 / Real.log (N : ℝ)), u * deriv g u := by ring
      rw [hrw, norm_neg]
      simpa [abs_of_nonneg haN0] using hbound
    have hzero : Tendsto (fun N : ℕ => C * (Real.log 2 / Real.log N)) atTop (nhds 0) := by
      simpa using ha.const_mul C
    refine squeeze_zero' (Filter.Eventually.of_forall fun N => norm_nonneg _) hsq hzero
  have heq : (fun N : ℕ => g 1 - ∫ u in (Real.log 2 / Real.log N)..1, u * deriv g u)
      =ᶠ[atTop] fun N : ℕ => windowMain g N / Real.log N := by
    filter_upwards [Filter.eventually_ge_atTop 2] with N hN
    exact (windowMain_div_log hg hN).symm
  exact Tendsto.congr' heq (tendsto_const_nhds.sub hkey)

/-! ## The smooth weak-convergence theorem -/

private theorem integral_mul_deriv {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) :
    (∫ u in (0 : ℝ)..1, u * deriv g u) = g 1 - ∫ u in (0 : ℝ)..1, g u := by
  have hcontderiv : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hu : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => t) 1 x := fun x _ => hasDerivAt_id x
  have hv : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt g (deriv g x) x :=
    fun x _ => ((hg.differentiable (by norm_num)) x).hasDerivAt
  have hu' : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume 0 1 :=
    intervalIntegrable_const
  have hv' : IntervalIntegrable (deriv g) volume 0 1 := hcontderiv.intervalIntegrable 0 1
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv hu' hv'
  simpa using h

/-- **Weak convergence of the Mertens prime window, smooth test functions.** -/
theorem tendsto_mertensPrimeWindow_div_log_of_contDiff {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g) :
    Tendsto (fun N : ℕ => mertensPrimeWindow g N / Real.log N) atTop
      (nhds (∫ u in (0 : ℝ)..1, g u)) := by
  have hcontderiv : Continuous (deriv g) := hg.continuous_deriv le_rfl
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hcontderiv.continuousOn
  have hM' : ∀ u ∈ Icc (0 : ℝ) 1, |deriv g u| ≤ M := by
    intro u hu
    simpa [Real.norm_eq_abs] using hM u hu
  have hlogtop : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have herr : Tendsto
      (fun N : ℕ => mertensPrimeWindow g N / Real.log N - windowMain g N / Real.log N)
      atTop (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : ∀ᶠ N : ℕ in atTop,
        ‖(mertensPrimeWindow g N / Real.log N - windowMain g N / Real.log N) - 0‖ ≤
          (mertensPrimeWindowBound + 1) * (|g 1| + M) / Real.log N := by
      filter_upwards [Filter.eventually_ge_atTop 2] with N hN
      have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
      rw [sub_zero, ← sub_div, Real.norm_eq_abs, abs_div, abs_of_pos hlogN]
      have hnum := abs_mertensPrimeWindow_sub_windowMain_le hg hN hM'
      gcongr
    refine squeeze_zero' (Filter.Eventually.of_forall fun N => norm_nonneg _) hb ?_
    exact Tendsto.div_atTop tendsto_const_nhds hlogtop
  have hmain := tendsto_windowMain_div_log hg
  have hsum := herr.add hmain
  rw [zero_add] at hsum
  have hrw : ∀ N : ℕ,
      (mertensPrimeWindow g N / Real.log N - windowMain g N / Real.log N) +
        windowMain g N / Real.log N = mertensPrimeWindow g N / Real.log N := by
    intro N; ring
  rw [integral_mul_deriv hg] at hsum
  have : g 1 - (g 1 - ∫ u in (0 : ℝ)..1, g u) = ∫ u in (0 : ℝ)..1, g u := by ring
  rw [this] at hsum
  exact hsum.congr hrw

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology MeasureTheory Set
open scoped BigOperators

/-! ## Weak convergence against continuous test functions -/

private theorem logRatio_mem_Icc {n N : ℕ} (hn : n.Prime) (hnN : n ≤ N) :
    Real.log n / Real.log N ∈ Icc (0 : ℝ) 1 := by
  have hn2 : 2 ≤ n := hn.two_le
  have hN2 : 2 ≤ N := le_trans hn2 hnN
  have hnr : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hlogN]
  exact Real.log_le_log (by linarith) (by exact_mod_cast hnN)

/-- Uniform comparison of two window functionals by their sup-distance on `[0, 1]`. -/
theorem abs_mertensPrimeWindow_sub_le {g h : ℝ → ℝ} (N : ℕ) {ε : ℝ}
    (hgh : ∀ u ∈ Icc (0 : ℝ) 1, |g u - h u| ≤ ε) :
    |mertensPrimeWindow g N - mertensPrimeWindow h N| ≤ ε * mertensPrimeWeightSum N := by
  rw [mertensPrimeWindow, mertensPrimeWindow, ← Finset.sum_sub_distrib,
    mertensPrimeWeightSum, Finset.mul_sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum fun n hn => ?_)
  by_cases hp : n.Prime
  · have hnN : n ≤ N := (Finset.mem_Icc.mp hn).2
    have hmem := logRatio_mem_Icc hp hnN
    rw [← sub_mul, abs_mul, abs_of_nonneg (mertensPrimeWeight_nonneg n)]
    exact mul_le_mul_of_nonneg_right (hgh _ hmem) (mertensPrimeWeight_nonneg n)
  · simp [mertensPrimeWeight, hp]

/-- **Weak convergence of the Mertens prime window.**  For every function continuous on the unit
interval, the normalized prime window converges to the Lebesgue integral: the finite prime measures
`(1/log N) ∑_{p ≤ N} (log p / p) δ_{log p / log N}` converge weakly to `du` on `[0, 1]`. -/
theorem tendsto_mertensPrimeWindow_div_log {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (0 : ℝ) 1)) :
    Tendsto (fun N : ℕ => mertensPrimeWindow g N / Real.log N) atTop
      (nhds (∫ u in (0 : ℝ)..1, g u)) := by
  have huIcc : uIcc (0 : ℝ) 1 = Icc (0 : ℝ) 1 := uIcc_of_le (by norm_num)
  have hgint : IntervalIntegrable g volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [huIcc]
    exact hg
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨P, hP⟩ := exists_polynomial_near_of_continuousOn 0 1 g hg (ε / 8) (by positivity)
  have hpcd : ContDiff ℝ 1 (fun x : ℝ => P.eval x) := Polynomial.contDiff_aeval P 1
  have hpcont : Continuous (fun x : ℝ => P.eval x) := hpcd.continuous
  have hpint : IntervalIntegrable (fun x : ℝ => P.eval x) volume 0 1 :=
    hpcont.intervalIntegrable 0 1
  have hPtend := tendsto_mertensPrimeWindow_div_log_of_contDiff hpcd
  rw [Metric.tendsto_atTop] at hPtend
  obtain ⟨N₁, hN₁⟩ := hPtend (ε / 8) (by positivity)
  have hlogtop : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp
    (hlogtop.eventually_ge_atTop mertensPrimeWindowBound)
  refine ⟨max (max N₁ N₂) 2, fun N hN => ?_⟩
  have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_left N₁ N₂) (le_max_left _ 2)) hN
  have hN2' : N₂ ≤ N := le_trans (le_trans (le_max_right N₁ N₂) (le_max_left _ 2)) hN
  have hN2 : 2 ≤ N := le_trans (le_max_right _ 2) hN
  have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN2
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hAle : mertensPrimeWeightSum N ≤ 2 * Real.log (N : ℝ) := by
    have h1 := mertensPrimeWeightSum_le N (by omega)
    have h2 := hN₂ N hN2'
    linarith
  have hclose : ∀ u ∈ Icc (0 : ℝ) 1, |g u - P.eval u| ≤ ε / 8 := by
    intro u hu
    rw [abs_sub_comm]
    exact (hP u hu).le
  have hwin := abs_mertensPrimeWindow_sub_le (g := g) (h := fun x : ℝ => P.eval x) N hclose
  have hstep1 : |mertensPrimeWindow g N / Real.log N -
      mertensPrimeWindow (fun x : ℝ => P.eval x) N / Real.log N| ≤ ε / 4 := by
    rw [← sub_div, abs_div, abs_of_pos hlogN, div_le_iff₀ hlogN]
    calc |mertensPrimeWindow g N - mertensPrimeWindow (fun x : ℝ => P.eval x) N|
        ≤ ε / 8 * mertensPrimeWeightSum N := hwin
      _ ≤ ε / 8 * (2 * Real.log (N : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hAle (by positivity)
      _ = ε / 4 * Real.log (N : ℝ) := by ring
  have hstep2 : |mertensPrimeWindow (fun x : ℝ => P.eval x) N / Real.log N -
      ∫ u in (0 : ℝ)..1, P.eval u| < ε / 8 := by
    have := hN₁ N hN1
    rwa [Real.dist_eq] at this
  have hstep3 : |(∫ u in (0 : ℝ)..1, P.eval u) - ∫ u in (0 : ℝ)..1, g u| ≤ ε / 8 := by
    rw [← intervalIntegral.integral_sub hpint hgint]
    have hbound : ‖∫ u in (0 : ℝ)..1, (P.eval u - g u)‖ ≤ ε / 8 * |(1 : ℝ) - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu => ?_
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hu
      exact (hP u ⟨hu.1.le, hu.2⟩).le
    simpa using hbound
  rw [Real.dist_eq]
  calc |mertensPrimeWindow g N / Real.log N - ∫ u in (0 : ℝ)..1, g u|
      ≤ |mertensPrimeWindow g N / Real.log N -
          mertensPrimeWindow (fun x : ℝ => P.eval x) N / Real.log N| +
        |mertensPrimeWindow (fun x : ℝ => P.eval x) N / Real.log N -
          ∫ u in (0 : ℝ)..1, g u| := abs_sub_le _ _ _
    _ ≤ |mertensPrimeWindow g N / Real.log N -
          mertensPrimeWindow (fun x : ℝ => P.eval x) N / Real.log N| +
        (|mertensPrimeWindow (fun x : ℝ => P.eval x) N / Real.log N -
            ∫ u in (0 : ℝ)..1, P.eval u| +
          |(∫ u in (0 : ℝ)..1, P.eval u) - ∫ u in (0 : ℝ)..1, g u|) := by
        gcongr
        exact abs_sub_le _ _ _
    _ < ε := by linarith

end

end RHTower

namespace RHTower

noncomputable section

open Filter Topology MeasureTheory Set
open scoped BigOperators

/-! ## The strict prime window -/

/-- The prime window summed over the primes strictly below the cutoff. -/
def mertensPrimeWindowBelow (g : ℝ → ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ Nat.primesBelow N, g (Real.log p / Real.log N) * (Real.log p / (p : ℝ))

private theorem mertensPrimeWindow_eq_below_add (g : ℝ → ℝ) {N : ℕ} (hN : 2 ≤ N) :
    mertensPrimeWindow g N =
      mertensPrimeWindowBelow g N +
        (if N.Prime then g 1 * (Real.log N / (N : ℝ)) else 0) := by
  have hlogN : Real.log (N : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (lt_of_lt_of_le one_lt_two hN))).ne'
  rw [mertensPrimeWindow, mertensPrimeWindowBelow]
  rw [show Finset.Icc 0 N = insert N (Finset.Ico 0 N) by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]
      omega,
    Finset.sum_insert (by simp)]
  have hbelow : ∑ n ∈ Finset.Ico 0 N, g (Real.log n / Real.log N) * mertensPrimeWeight n =
      ∑ p ∈ Nat.primesBelow N, g (Real.log p / Real.log N) * (Real.log p / (p : ℝ)) := by
    rw [Nat.primesBelow, Finset.sum_filter, Finset.range_eq_Ico]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hp : n.Prime
    · simp [mertensPrimeWeight, hp]
    · simp [mertensPrimeWeight, hp]
  rw [hbelow, add_comm]
  congr 1
  by_cases hp : N.Prime
  · simp [mertensPrimeWeight, hp, div_self hlogN]
  · simp [mertensPrimeWeight, hp]

/-- **Weak convergence of the strict prime window.** -/
theorem tendsto_mertensPrimeWindowBelow_div_log {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc (0 : ℝ) 1)) :
    Tendsto (fun N : ℕ => mertensPrimeWindowBelow g N / Real.log N) atTop
      (nhds (∫ u in (0 : ℝ)..1, g u)) := by
  have hmain := tendsto_mertensPrimeWindow_div_log hg
  have hdiff : Tendsto
      (fun N : ℕ => mertensPrimeWindow g N / Real.log N -
        mertensPrimeWindowBelow g N / Real.log N) atTop (nhds 0) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb : ∀ᶠ N : ℕ in atTop,
        ‖(mertensPrimeWindow g N / Real.log N -
            mertensPrimeWindowBelow g N / Real.log N) - 0‖ ≤ |g 1| / (N : ℝ) := by
      filter_upwards [Filter.eventually_ge_atTop 2] with N hN
      have hNr : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
      rw [sub_zero, ← sub_div, mertensPrimeWindow_eq_below_add g hN]
      simp only [add_sub_cancel_left, Real.norm_eq_abs, abs_div, abs_of_pos hlogN]
      by_cases hp : N.Prime
      · rw [if_pos hp, abs_mul, abs_div, abs_of_pos hlogN,
          abs_of_pos (by linarith : (0 : ℝ) < (N : ℝ))]
        rw [div_le_div_iff₀ hlogN (by linarith), mul_comm]
        field_simp
        exact le_rfl
      · rw [if_neg hp]
        simp only [abs_zero, zero_div]
        positivity
    refine squeeze_zero' (Filter.Eventually.of_forall fun N => norm_nonneg _) hb ?_
    exact Tendsto.div_atTop tendsto_const_nhds tendsto_natCast_atTop_atTop
  have := hmain.sub hdiff
  rw [sub_zero] at this
  refine this.congr fun N => ?_
  ring

end

end RHTower
