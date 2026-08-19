import GaloisForLFunctions.RHTower.MobiusCriticalClockWeakConvergence
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Sharp aperture quantiles of the critical Möbius boundary layer

`mobius-critical-exponential-boundary-layer-law.md`, equations `(7)`, `(12)`, `(13)`.

The rescaled logarithmic divisor coordinate `Y_omega(d) = 2 omega log d` converges in law to the
mean-one exponential (already formalized as `tendsto_squarefreeMobiusCriticalClockProbabilityMeasure`).
Since the limit law has no atoms, the portmanteau theorem upgrades that weak limit to convergence of
the actual window masses:

```text
P_omega{a <= 2 omega log d <= b} -> e^{-a} - e^{-b} ,
P_omega{d <= exp(c/(2 omega))}   -> 1 - e^{-c} ,
P_omega{d >  exp(c/(2 omega))}   -> e^{-c} .
```
-/

open Complex MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology ENNReal NNReal

noncomputable section
namespace RHTower

/-! ### The limiting exponential law -/

instance instIsProbabilityMeasure_mobiusCriticalExponential :
    IsProbabilityMeasure (mobiusCriticalExponentialProbabilityMeasure : Measure ℝ) :=
  ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)

theorem mobiusCriticalExponential_coe :
    (mobiusCriticalExponentialProbabilityMeasure : Measure ℝ) = ProbabilityTheory.expMeasure 1 :=
  rfl

theorem mobiusCriticalExponential_singleton (x : ℝ) :
    (mobiusCriticalExponentialProbabilityMeasure : Measure ℝ) {x} = 0 := by
  rw [mobiusCriticalExponential_coe, ProbabilityTheory.expMeasure,
    ProbabilityTheory.gammaMeasure, withDensity_apply _ (measurableSet_singleton x)]
  simp

theorem one_sub_exp_neg_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ 1 - Real.exp (-x) := by
  have : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  linarith

theorem mobiusCriticalExponential_Iic {x : ℝ} (hx : 0 ≤ x) :
    (mobiusCriticalExponentialProbabilityMeasure : Measure ℝ) (Iic x)
      = ENNReal.ofReal (1 - Real.exp (-x)) := by
  have hprob : IsProbabilityMeasure (ProbabilityTheory.expMeasure 1) :=
    ProbabilityTheory.isProbabilityMeasure_expMeasure (by norm_num)
  have h := ProbabilityTheory.ofReal_cdf (ProbabilityTheory.expMeasure 1) x
  rw [ProbabilityTheory.cdf_expMeasure_eq (by norm_num : (0:ℝ) < 1) x, if_pos hx] at h
  rw [mobiusCriticalExponential_coe, ← h]
  norm_num

theorem mobiusCriticalExponential_Ioc {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (mobiusCriticalExponentialProbabilityMeasure : Measure ℝ) (Ioc a b)
      = ENNReal.ofReal (Real.exp (-a) - Real.exp (-b)) := by
  have hsub : Iic a ⊆ Iic b := Iic_subset_Iic.mpr hab
  have hdiff : Ioc a b = Iic b \ Iic a := by
    ext t
    simp only [mem_Ioc, Set.mem_sdiff, mem_Iic, not_le]
    tauto
  rw [hdiff, measure_sdiff hsub measurableSet_Iic.nullMeasurableSet
      (measure_ne_top _ _),
    mobiusCriticalExponential_Iic ha, mobiusCriticalExponential_Iic (ha.trans hab),
    ← ENNReal.ofReal_sub _ (one_sub_exp_neg_nonneg ha)]
  congr 1
  ring

theorem mobiusCriticalExponential_Icc {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (mobiusCriticalExponentialProbabilityMeasure : Measure ℝ) (Icc a b)
      = ENNReal.ofReal (Real.exp (-a) - Real.exp (-b)) := by
  have hsplit : Icc a b ⊆ {a} ∪ Ioc a b := by
    intro t ht
    simp only [mem_Icc] at ht
    rcases eq_or_lt_of_le ht.1 with h | h
    · exact Or.inl (by simp [h.symm])
    · exact Or.inr ⟨h, ht.2⟩
  have hle : (mobiusCriticalExponentialProbabilityMeasure : Measure ℝ) (Icc a b)
      = (mobiusCriticalExponentialProbabilityMeasure : Measure ℝ) (Ioc a b) := by
    refine le_antisymm ?_ (measure_mono Ioc_subset_Icc_self)
    calc (mobiusCriticalExponentialProbabilityMeasure : Measure ℝ) (Icc a b)
        ≤ (mobiusCriticalExponentialProbabilityMeasure : Measure ℝ) ({a} ∪ Ioc a b) :=
          measure_mono hsplit
      _ ≤ (mobiusCriticalExponentialProbabilityMeasure : Measure ℝ) {a} +
            (mobiusCriticalExponentialProbabilityMeasure : Measure ℝ) (Ioc a b) :=
          measure_union_le _ _
      _ = (mobiusCriticalExponentialProbabilityMeasure : Measure ℝ) (Ioc a b) := by
          rw [mobiusCriticalExponential_singleton, zero_add]
  rw [hle]
  exact mobiusCriticalExponential_Ioc ha hab

theorem mobiusCriticalExponential_Ioi {x : ℝ} (hx : 0 ≤ x) :
    (mobiusCriticalExponentialProbabilityMeasure : Measure ℝ) (Ioi x)
      = ENNReal.ofReal (Real.exp (-x)) := by
  have hcompl : Ioi x = (Iic x)ᶜ := by ext t; simp
  have huniv : (mobiusCriticalExponentialProbabilityMeasure : Measure ℝ) univ = 1 :=
    measure_univ
  rw [hcompl, measure_compl measurableSet_Iic (measure_ne_top _ _), huniv,
    mobiusCriticalExponential_Iic hx,
    show (1 : ℝ≥0∞) = ENNReal.ofReal (1 : ℝ) by simp,
    ← ENNReal.ofReal_sub _ (one_sub_exp_neg_nonneg hx)]
  congr 1
  ring

/-! ### The window mass of the critical clock -/

/-- The squarefree channel mass carried by a window of the rescaled logarithmic clock. -/
def squarefreeMobiusClockMass (sigma : ℝ) (S : Set ℝ) : ℝ :=
  ∑' n : ℕ, S.indicator (fun _ => squarefreeMobiusProbability sigma n)
    (squarefreeMobiusCriticalClock sigma n)

theorem squarefreeMobiusClockMassTerm_nonneg
    {sigma : ℝ} (hsigma : 1 < sigma) (S : Set ℝ) (n : ℕ) :
    0 ≤ S.indicator (fun _ => squarefreeMobiusProbability sigma n)
      (squarefreeMobiusCriticalClock sigma n) := by
  by_cases hmem : squarefreeMobiusCriticalClock sigma n ∈ S
  · rw [Set.indicator_of_mem hmem]
    exact squarefreeMobiusProbability_nonneg hsigma n
  · rw [Set.indicator_of_notMem hmem]

theorem squarefreeMobiusClockMassTerm_le
    {sigma : ℝ} (hsigma : 1 < sigma) (S : Set ℝ) (n : ℕ) :
    S.indicator (fun _ => squarefreeMobiusProbability sigma n)
      (squarefreeMobiusCriticalClock sigma n) ≤ squarefreeMobiusProbability sigma n := by
  by_cases hmem : squarefreeMobiusCriticalClock sigma n ∈ S
  · rw [Set.indicator_of_mem hmem]
  · rw [Set.indicator_of_notMem hmem]
    exact squarefreeMobiusProbability_nonneg hsigma n

theorem summable_squarefreeMobiusClockMassTerm {sigma : ℝ} (hsigma : 1 < sigma) (S : Set ℝ) :
    Summable (fun n : ℕ => S.indicator (fun _ => squarefreeMobiusProbability sigma n)
      (squarefreeMobiusCriticalClock sigma n)) :=
  Summable.of_nonneg_of_le (squarefreeMobiusClockMassTerm_nonneg hsigma S)
    (squarefreeMobiusClockMassTerm_le hsigma S) (summable_squarefreeMobiusProbability hsigma)

theorem squarefreeMobiusClockMass_nonneg {sigma : ℝ} (hsigma : 1 < sigma) (S : Set ℝ) :
    0 ≤ squarefreeMobiusClockMass sigma S :=
  tsum_nonneg (squarefreeMobiusClockMassTerm_nonneg hsigma S)

/-- The clock probability measure evaluates to the window mass. -/
theorem clockProbabilityMeasure_apply
    {sigma : ℝ} (hsigma : 1 < sigma) {S : Set ℝ} (hS : MeasurableSet S) :
    (squarefreeMobiusCriticalClockProbabilityMeasure sigma : Measure ℝ) S
      = ENNReal.ofReal (squarefreeMobiusClockMass sigma S) := by
  rw [squarefreeMobiusCriticalClockProbabilityMeasure, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply_of_aemeasurable Measurable.of_discrete.aemeasurable hS]
  change (squarefreeMobiusCriticalPMF sigma).toMeasure
      (squarefreeMobiusCriticalClock sigma ⁻¹' S) = _
  rw [PMF.toMeasure_apply _ (MeasurableSet.preimage hS (by fun_prop))]
  rw [squarefreeMobiusClockMass, ENNReal.ofReal_tsum_of_nonneg
    (squarefreeMobiusClockMassTerm_nonneg hsigma S)
    (summable_squarefreeMobiusClockMassTerm hsigma S)]
  refine tsum_congr fun n => ?_
  by_cases hmem : squarefreeMobiusCriticalClock sigma n ∈ S
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (by simpa using hmem),
      ← squarefreeMobiusCriticalPMF_toReal hsigma n,
      ENNReal.ofReal_toReal (PMF.apply_ne_top _ n)]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (by simpa using hmem),
      ENNReal.ofReal_zero]

/-! ### Portmanteau transport -/

private theorem tendsto_clock_measure_of_null_frontier
    {S : Set ℝ} (hS : (mobiusCriticalExponentialProbabilityMeasure : Measure ℝ) (frontier S) = 0) :
    Tendsto (fun sigma : ℝ =>
        (squarefreeMobiusCriticalClockProbabilityMeasure sigma : Measure ℝ) S)
      (nhdsWithin 1 (Ioi 1))
      (nhds ((mobiusCriticalExponentialProbabilityMeasure : Measure ℝ) S)) :=
  ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
    tendsto_squarefreeMobiusCriticalClockProbabilityMeasure hS

private theorem tendsto_clockMass_of_null_frontier
    {S : Set ℝ} (hSmeas : MeasurableSet S)
    (hS : (mobiusCriticalExponentialProbabilityMeasure : Measure ℝ) (frontier S) = 0)
    {L : ℝ} (hL : 0 ≤ L)
    (hval : (mobiusCriticalExponentialProbabilityMeasure : Measure ℝ) S = ENNReal.ofReal L) :
    Tendsto (fun sigma : ℝ => squarefreeMobiusClockMass sigma S)
      (nhdsWithin 1 (Ioi 1)) (nhds L) := by
  have hport := tendsto_clock_measure_of_null_frontier hS
  have hreal := (ENNReal.tendsto_toReal (by rw [hval]; exact ENNReal.ofReal_ne_top)).comp hport
  rw [Function.comp_def] at hreal
  rw [hval, ENNReal.toReal_ofReal hL] at hreal
  refine hreal.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  have hsig : 1 < sigma := hsigma
  rw [clockProbabilityMeasure_apply hsig hSmeas,
    ENNReal.toReal_ofReal (squarefreeMobiusClockMass_nonneg hsig S)]

/-! ### The card's aperture quantiles -/

private theorem frontier_Icc_subset (a b : ℝ) : frontier (Icc a b) ⊆ {a, b} := by
  intro t ht
  have h1 : t ∈ closure (Icc a b) := ht.1
  have h2 : t ∉ interior (Icc a b) := ht.2
  rw [closure_Icc] at h1
  rw [interior_Icc] at h2
  simp only [mem_Icc] at h1
  simp only [mem_Ioo, not_and, not_lt] at h2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rcases eq_or_lt_of_le h1.1 with h | h
  · exact Or.inl h.symm
  · exact Or.inr (le_antisymm h1.2 (h2 h))

/-- **Card `(7)`.**  The window mass of the rescaled logarithmic divisor coordinate converges to
the exponential window mass. -/
theorem tendsto_squarefreeMobiusClockMass_Icc {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Tendsto (fun sigma : ℝ => squarefreeMobiusClockMass sigma (Icc a b))
      (nhdsWithin 1 (Ioi 1)) (nhds (Real.exp (-a) - Real.exp (-b))) := by
  refine tendsto_clockMass_of_null_frontier measurableSet_Icc ?_ ?_
    (mobiusCriticalExponential_Icc ha hab)
  · refine measure_mono_null (frontier_Icc_subset a b) ?_
    refine measure_union_null ?_ ?_
    · exact mobiusCriticalExponential_singleton a
    · exact mobiusCriticalExponential_singleton b
  · have : Real.exp (-b) ≤ Real.exp (-a) := Real.exp_le_exp.mpr (by linarith)
    linarith

/-- **Card `(12)`.**  The mass below the critical divisor cutoff `exp(c/(2 omega))`. -/
theorem tendsto_squarefreeMobiusClockMass_Iic {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun sigma : ℝ => squarefreeMobiusClockMass sigma (Iic c))
      (nhdsWithin 1 (Ioi 1)) (nhds (1 - Real.exp (-c))) := by
  refine tendsto_clockMass_of_null_frontier measurableSet_Iic ?_ (one_sub_exp_neg_nonneg hc)
    (mobiusCriticalExponential_Iic hc)
  rw [frontier_Iic]
  exact mobiusCriticalExponential_singleton c

/-- **Card `(13)`.**  The mass above the critical divisor cutoff. -/
theorem tendsto_squarefreeMobiusClockMass_Ioi {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun sigma : ℝ => squarefreeMobiusClockMass sigma (Ioi c))
      (nhdsWithin 1 (Ioi 1)) (nhds (Real.exp (-c))) := by
  refine tendsto_clockMass_of_null_frontier measurableSet_Ioi ?_ (Real.exp_nonneg _)
    (mobiusCriticalExponential_Ioi hc)
  rw [frontier_Ioi]
  exact mobiusCriticalExponential_singleton c

/-- The clock window mass in the divisor coordinate: `2 omega log d <= c` is `d <= exp(c/(2 omega))`,
with `sigma - 1 = 2 omega`. -/
theorem squarefreeMobiusClockMass_Iic_eq_divisorCutoff
    {sigma c : ℝ} (hsigma : 1 < sigma) (hc : 0 ≤ c) :
    squarefreeMobiusClockMass sigma (Iic c)
      = ∑' n : ℕ, (Iic (Real.exp (c / (sigma - 1)))).indicator
          (fun _ => squarefreeMobiusProbability sigma n) (n : ℝ) := by
  have hpos : 0 < sigma - 1 := by linarith
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have hzero : squarefreeMobiusProbability sigma 0 = 0 := by
      simp [squarefreeMobiusProbability, squarefreeMobiusMass, not_squarefree_zero]
    by_cases h1 : squarefreeMobiusCriticalClock sigma 0 ∈ Iic c
    · rw [Set.indicator_of_mem h1, hzero]
      by_cases h2 : ((0 : ℕ) : ℝ) ∈ Iic (Real.exp (c / (sigma - 1)))
      · rw [Set.indicator_of_mem h2]
      · rw [Set.indicator_of_notMem h2]
    · exact absurd (by
        simp only [squarefreeMobiusCriticalClock, Nat.cast_zero, Real.log_zero, mul_zero,
          mem_Iic]
        exact hc) h1
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hiff : squarefreeMobiusCriticalClock sigma n ∈ Iic c ↔
        ((n : ℝ) ∈ Iic (Real.exp (c / (sigma - 1)))) := by
      simp only [squarefreeMobiusCriticalClock, mem_Iic]
      rw [← Real.log_le_iff_le_exp hnpos, le_div_iff₀ hpos]
      constructor
      · intro h; linarith [h]
      · intro h; linarith [h]
    by_cases hmem : squarefreeMobiusCriticalClock sigma n ∈ Iic c
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hiff.mp hmem)]
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem (fun h => hmem (hiff.mpr h))]

/-! ### Moving apertures -/

theorem squarefreeMobiusClockMass_mono
    {sigma : ℝ} (hsigma : 1 < sigma) {S T : Set ℝ} (hST : S ⊆ T) :
    squarefreeMobiusClockMass sigma S ≤ squarefreeMobiusClockMass sigma T := by
  refine Summable.tsum_le_tsum ?_ (summable_squarefreeMobiusClockMassTerm hsigma S)
    (summable_squarefreeMobiusClockMassTerm hsigma T)
  intro n
  by_cases hmem : squarefreeMobiusCriticalClock sigma n ∈ S
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hST hmem)]
  · rw [Set.indicator_of_notMem hmem]
    exact squarefreeMobiusClockMassTerm_nonneg hsigma T n

theorem squarefreeMobiusClockMass_le_one {sigma : ℝ} (hsigma : 1 < sigma) (S : Set ℝ) :
    squarefreeMobiusClockMass sigma S ≤ 1 := by
  calc squarefreeMobiusClockMass sigma S
      ≤ ∑' n : ℕ, squarefreeMobiusProbability sigma n :=
        Summable.tsum_le_tsum (squarefreeMobiusClockMassTerm_le hsigma S)
          (summable_squarefreeMobiusClockMassTerm hsigma S)
          (summable_squarefreeMobiusProbability hsigma)
    _ = 1 := tsum_squarefreeMobiusProbability hsigma

private theorem exp_neg_neg_log {y : ℝ} (hy : 0 < y) : Real.exp (-(-Real.log y)) = y := by
  rw [neg_neg, Real.exp_log hy]

/-- **Card §3(2), §4(15).**  A cutoff whose rescaled logarithm converges to `c` retains exactly the
fraction `1 - e^{-c}`. -/
theorem tendsto_squarefreeMobiusClockMass_Iic_moving
    {x : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hx : Tendsto x (nhdsWithin 1 (Ioi 1)) (nhds c)) :
    Tendsto (fun sigma : ℝ => squarefreeMobiusClockMass sigma (Iic (x sigma)))
      (nhdsWithin 1 (Ioi 1)) (nhds (1 - Real.exp (-c))) := by
  refine tendsto_order.2 ⟨fun u hu => ?_, fun v hv => ?_⟩
  · rcases lt_or_ge u 0 with hu0 | hu0
    · filter_upwards [self_mem_nhdsWithin] with sigma hsigma
      exact lt_of_lt_of_le hu0 (squarefreeMobiusClockMass_nonneg hsigma _)
    · set u' : ℝ := (u + (1 - Real.exp (-c))) / 2 with hu'
      have hu'u : u < u' := by rw [hu']; linarith
      have hu'L : u' < 1 - Real.exp (-c) := by rw [hu']; linarith
      have hu'0 : 0 ≤ u' := le_trans hu0 hu'u.le
      have hpos : 0 < 1 - u' := by
        have hexp0 : 0 < Real.exp (-c) := Real.exp_pos _
        linarith
      set c' : ℝ := -Real.log (1 - u') with hc'
      have hexpc' : Real.exp (-c') = 1 - u' := by rw [hc']; exact exp_neg_neg_log hpos
      have hc'0 : 0 ≤ c' := by
        rw [hc', neg_nonneg]
        exact Real.log_nonpos (by linarith) (by linarith)
      have hc'lt : c' < c := by
        by_contra hcon
        push Not at hcon
        have hmono : Real.exp (-c') ≤ Real.exp (-c) := Real.exp_le_exp.mpr (by linarith)
        rw [hexpc'] at hmono
        linarith
      have hlim := tendsto_squarefreeMobiusClockMass_Iic hc'0
      have hbase : ∀ᶠ sigma : ℝ in nhdsWithin 1 (Ioi 1),
          u < squarefreeMobiusClockMass sigma (Iic c') := by
        have : u < 1 - Real.exp (-c') := by rw [hexpc']; linarith
        exact hlim.eventually_const_lt this
      have hxev : ∀ᶠ sigma : ℝ in nhdsWithin 1 (Ioi 1), c' < x sigma :=
        hx.eventually_const_lt hc'lt
      filter_upwards [hbase, hxev, self_mem_nhdsWithin] with sigma hb hxc hsigma
      exact lt_of_lt_of_le hb
        (squarefreeMobiusClockMass_mono hsigma (Iic_subset_Iic.mpr hxc.le))
  · rcases le_or_gt v 1 with hv1 | hv1
    · have hL0 : 0 ≤ 1 - Real.exp (-c) := one_sub_exp_neg_nonneg hc
      set v' : ℝ := (v + (1 - Real.exp (-c))) / 2 with hv'
      have hv'v : v' < v := by rw [hv']; linarith
      have hLv' : 1 - Real.exp (-c) < v' := by rw [hv']; linarith
      have hv'1 : v' < 1 := by rw [hv']; nlinarith [Real.exp_pos (-c)]
      have hpos : 0 < 1 - v' := by linarith
      set c'' : ℝ := -Real.log (1 - v') with hc''
      have hexpc'' : Real.exp (-c'') = 1 - v' := by rw [hc'']; exact exp_neg_neg_log hpos
      have hc''0 : 0 ≤ c'' := by
        rw [hc'', neg_nonneg]
        exact Real.log_nonpos (by linarith) (by linarith)
      have hcc'' : c < c'' := by
        by_contra hcon
        push Not at hcon
        have hmono : Real.exp (-c) ≤ Real.exp (-c'') := Real.exp_le_exp.mpr (by linarith)
        rw [hexpc''] at hmono
        linarith
      have hlim := tendsto_squarefreeMobiusClockMass_Iic hc''0
      have hbase : ∀ᶠ sigma : ℝ in nhdsWithin 1 (Ioi 1),
          squarefreeMobiusClockMass sigma (Iic c'') < v := by
        have : 1 - Real.exp (-c'') < v := by rw [hexpc'']; linarith
        exact hlim.eventually_lt_const this
      have hxev : ∀ᶠ sigma : ℝ in nhdsWithin 1 (Ioi 1), x sigma < c'' :=
        hx.eventually_lt_const hcc''
      filter_upwards [hbase, hxev, self_mem_nhdsWithin] with sigma hb hxc hsigma
      exact lt_of_le_of_lt
        (squarefreeMobiusClockMass_mono hsigma (Iic_subset_Iic.mpr hxc.le)) hb
    · filter_upwards [self_mem_nhdsWithin] with sigma hsigma
      exact lt_of_le_of_lt (squarefreeMobiusClockMass_le_one hsigma _) hv1

/-- **Card §3(4), §4(14).**  Full critical mass transport requires — and follows from — a cutoff
whose rescaled logarithm diverges. -/
theorem tendsto_squarefreeMobiusClockMass_Iic_moving_atTop
    {x : ℝ → ℝ} (hx : Tendsto x (nhdsWithin 1 (Ioi 1)) atTop) :
    Tendsto (fun sigma : ℝ => squarefreeMobiusClockMass sigma (Iic (x sigma)))
      (nhdsWithin 1 (Ioi 1)) (nhds 1) := by
  refine tendsto_order.2 ⟨fun u hu => ?_, fun v hv => ?_⟩
  · rcases lt_or_ge u 0 with hu0 | hu0
    · filter_upwards [self_mem_nhdsWithin] with sigma hsigma
      exact lt_of_lt_of_le hu0 (squarefreeMobiusClockMass_nonneg hsigma _)
    · set u' : ℝ := (u + 1) / 2 with hu'
      have hu'u : u < u' := by rw [hu']; linarith
      have hu'1 : u' < 1 := by rw [hu']; linarith
      have hpos : 0 < 1 - u' := by linarith
      set c' : ℝ := -Real.log (1 - u') with hc'
      have hexpc' : Real.exp (-c') = 1 - u' := by rw [hc']; exact exp_neg_neg_log hpos
      have hc'0 : 0 ≤ c' := by
        rw [hc', neg_nonneg]
        exact Real.log_nonpos (by linarith) (by linarith)
      have hlim := tendsto_squarefreeMobiusClockMass_Iic hc'0
      have hbase : ∀ᶠ sigma : ℝ in nhdsWithin 1 (Ioi 1),
          u < squarefreeMobiusClockMass sigma (Iic c') := by
        have : u < 1 - Real.exp (-c') := by rw [hexpc']; linarith
        exact hlim.eventually_const_lt this
      have hxev : ∀ᶠ sigma : ℝ in nhdsWithin 1 (Ioi 1), c' ≤ x sigma :=
        hx.eventually_ge_atTop c'
      filter_upwards [hbase, hxev, self_mem_nhdsWithin] with sigma hb hxc hsigma
      exact lt_of_lt_of_le hb (squarefreeMobiusClockMass_mono hsigma (Iic_subset_Iic.mpr hxc))
  · filter_upwards [self_mem_nhdsWithin] with sigma hsigma
    exact lt_of_le_of_lt (squarefreeMobiusClockMass_le_one hsigma _) hv

/-- **Card §3(1).**  A fixed divisor cutoff captures asymptotically no critical mass. -/
theorem tendsto_squarefreeMobiusClockMass_fixed_cutoff (D : ℝ) :
    Tendsto (fun sigma : ℝ =>
        squarefreeMobiusClockMass sigma (Iic ((sigma - 1) * Real.log D)))
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
  have hx : Tendsto (fun sigma : ℝ => (sigma - 1) * Real.log D)
      (nhdsWithin 1 (Ioi 1)) (nhds 0) := by
    have hcont : Continuous (fun sigma : ℝ => (sigma - 1) * Real.log D) := by fun_prop
    have h : Tendsto (fun sigma : ℝ => (sigma - 1) * Real.log D)
        (nhdsWithin (1 : ℝ) (Ioi 1)) (nhds ((1 - 1) * Real.log D)) :=
      hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa using h
  have h := tendsto_squarefreeMobiusClockMass_Iic_moving (c := 0) le_rfl hx
  simpa using h

end RHTower
