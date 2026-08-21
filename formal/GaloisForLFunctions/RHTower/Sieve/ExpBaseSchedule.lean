import GaloisForLFunctions.RHTower.Sieve.TwoRangeAggregates

/-!
# The low designated range with an exponential bottom

The moment method pins the order `k` from both sides, `2(log x)^{1−a} ≤ k = O(log x/log log x)`, and
that window is non-empty only when the low designated range starts at `exp((log x)^a)`.  With a
polylogarithmic bottom `⌈(log x)^K⌉` the diagonal term `NA^k` of Lemma 2.5 beats every saving, for
every constant `K`.

So the low ladder is

```text
   R = ⌈exp((log x)^a)⌉ < p ≤ h = exp((log x)^β) ,   0 < a < β ,
   step ratio 1 + (log x)^{−c} ,   L = ⌊log(h/R)/log(1+η)⌋ .
```

Everything the low half needs is easier at this bottom than at the polylogarithmic one: the step
count is the same `O((log x)^{β+c})`, the ladder-defect terms `1/(Rη)`, `1/(R²η)` are exponentially
small instead of merely polylogarithmically small, and the harmonic mass acquires a **two-sided**
bound `≍ (β − a)·log log x` because both endpoints now have logarithms that are powers of `log x`.
-/

namespace RHTower.Sieve

open Filter Topology Finset

noncomputable section

/-- The number of steps of the low ladder with an exponential bottom. -/
def expSteps (a c β x : ℝ) : ℕ :=
  ⌊Real.log (cardLength β x / ((highBase a x : ℕ) : ℝ)) / Real.log (1 + lowEta c x)⌋₊

/-- The top of the low ladder with an exponential bottom. -/
def expTop (a c β x : ℝ) : ℕ :=
  ⌊((highBase a x : ℕ) : ℝ) * (1 + lowEta c x) ^ (expSteps a c β x)⌋₊

/-- **The exponential bottom is below the window length.** -/
theorem expBase_lt_cardLength {a β : ℝ} (ha : 0 < a) (hab : a < β) :
    ∀ᶠ x : ℝ in atTop, ((highBase a x : ℕ) : ℝ) < cardLength β x := by
  have hquot : Tendsto (fun x : ℝ => (Real.log x) ^ (a - β)) atTop (𝓝 0) := by
    refine (tendsto_log_rpow_neg (δ := β - a) (by linarith)).congr fun x => ?_
    congr 1
    ring
  have hpowβ : Tendsto (fun x : ℝ => (Real.log x) ^ β) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp Real.tendsto_log_atTop
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2) hquot,
    hpowβ.eventually_ge_atTop (4 : ℝ)] with x hx1 hsm hbig
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hpb : (0 : ℝ) < (Real.log x) ^ β := Real.rpow_pos_of_pos hlogx β
  have hid : (Real.log x) ^ a = (Real.log x) ^ (a - β) * (Real.log x) ^ β := by
    rw [← Real.rpow_add hlogx]
    congr 1
    ring
  have hhalf : (Real.log x) ^ a ≤ (Real.log x) ^ β / 2 := by
    rw [hid]
    nlinarith [hsm, hpb]
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hub := (highBase_bounds (a := a) hx1).2
  have hexp : 2 * cardLength a x < cardLength β x := by
    rw [cardLength, cardLength, show (2 : ℝ) = Real.exp (Real.log 2) by
      rw [Real.exp_log (by norm_num)], ← Real.exp_add]
    exact Real.exp_lt_exp.2 (by linarith)
  linarith

/-- **The low ladder with an exponential bottom has polylogarithmically many steps.** -/
theorem expSteps_le {a c β : ℝ} (_ha : 0 < a) (hc : 0 < c) (_hβ : 0 < β) :
    ∀ᶠ x : ℝ in atTop, ((expSteps a c β x : ℕ) : ℝ) ≤ 2 * (Real.log x) ^ (β + c) := by
  have hzero := tendsto_lowEta (c := c) hc
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) hzero] with x hx1 hη1
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hη : 0 < lowEta c x := lowEta_pos hx1
  have hQ1 : (1 : ℝ) ≤ ((highBase a x : ℕ) : ℝ) := by
    have h1 := (highBase_bounds (a := a) hx1).1
    have h2 : (1 : ℝ) ≤ cardLength a x := by
      rw [cardLength]
      exact Real.one_le_exp (Real.rpow_nonneg hlogx.le a)
    linarith
  have hQ0 : (0 : ℝ) < ((highBase a x : ℕ) : ℝ) := by linarith
  have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
  have hlogr : (0 : ℝ) < Real.log (1 + lowEta c x) := Real.log_pos (by linarith)
  have hhalf := log_one_add_ge_half_self hη hη1
  have hratio : Real.log (cardLength β x / ((highBase a x : ℕ) : ℝ)) ≤ (Real.log x) ^ β := by
    rw [Real.log_div (ne_of_gt hh0) (ne_of_gt hQ0), log_cardLength]
    have : (0 : ℝ) ≤ Real.log ((highBase a x : ℕ) : ℝ) := Real.log_nonneg hQ1
    linarith
  have hpowβ : (0 : ℝ) ≤ (Real.log x) ^ β := Real.rpow_nonneg hlogx.le β
  have hkey : 2 * (Real.log x) ^ β / lowEta c x = 2 * (Real.log x) ^ (β + c) := by
    rw [lowEta, div_eq_mul_inv, ← Real.rpow_neg hlogx.le, neg_neg, mul_assoc,
      ← Real.rpow_add hlogx]
  by_cases hnn : 0 ≤ Real.log (cardLength β x / ((highBase a x : ℕ) : ℝ))
  · have hfl : ((expSteps a c β x : ℕ) : ℝ)
        ≤ Real.log (cardLength β x / ((highBase a x : ℕ) : ℝ)) / Real.log (1 + lowEta c x) := by
      rw [expSteps]
      exact Nat.floor_le (div_nonneg hnn hlogr.le)
    refine hfl.trans ?_
    rw [← hkey]
    refine (div_le_div₀ (by positivity) hratio (by linarith) hhalf).trans (le_of_eq ?_)
    field_simp
  · have hneg : Real.log (cardLength β x / ((highBase a x : ℕ) : ℝ)) < 0 := lt_of_not_ge hnn
    have hzz : expSteps a c β x = 0 := by
      rw [expSteps]
      refine Nat.floor_eq_zero.2 ?_
      have : Real.log (cardLength β x / ((highBase a x : ℕ) : ℝ))
          / Real.log (1 + lowEta c x) < 0 := div_neg_of_neg_of_pos hneg hlogr
      linarith
    rw [hzz]
    push_cast
    positivity

/-- **The low ladder with an exponential bottom has at least one step.** -/
theorem one_le_expSteps {a c β : ℝ} (ha : 0 < a) (hab : a < β) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ expSteps a c β x := by
  have hzero := tendsto_lowEta (c := c) hc
  have hquot : Tendsto (fun x : ℝ => (Real.log x) ^ (a - β)) atTop (𝓝 0) := by
    refine (tendsto_log_rpow_neg (δ := β - a) (by linarith)).congr fun x => ?_
    congr 1
    ring
  have hpowβ : Tendsto (fun x : ℝ => (Real.log x) ^ β) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp Real.tendsto_log_atTop
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) hzero,
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 2) hquot,
    hpowβ.eventually_ge_atTop (8 : ℝ)] with x hx1 hη1 hsm hbig
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hη : 0 < lowEta c x := lowEta_pos hx1
  have hlogr : (0 : ℝ) < Real.log (1 + lowEta c x) := Real.log_pos (by linarith)
  have hLHS : Real.log (1 + lowEta c x) ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + lowEta c x)
    linarith
  have hQ1 : (1 : ℝ) ≤ ((highBase a x : ℕ) : ℝ) := by
    have h1 := (highBase_bounds (a := a) hx1).1
    have h2 : (1 : ℝ) ≤ cardLength a x := by
      rw [cardLength]
      exact Real.one_le_exp (Real.rpow_nonneg hlogx.le a)
    linarith
  have hQ0 : (0 : ℝ) < ((highBase a x : ℕ) : ℝ) := by linarith
  have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
  have hpb : (0 : ℝ) < (Real.log x) ^ β := Real.rpow_pos_of_pos hlogx β
  have hid : (Real.log x) ^ a = (Real.log x) ^ (a - β) * (Real.log x) ^ β := by
    rw [← Real.rpow_add hlogx]
    congr 1
    ring
  have hhalf : (Real.log x) ^ a ≤ (Real.log x) ^ β / 2 := by
    rw [hid]
    nlinarith [hsm, hpb]
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogQ : Real.log ((highBase a x : ℕ) : ℝ) ≤ Real.log 2 + (Real.log x) ^ a := by
    have hub := (highBase_bounds (a := a) hx1).2
    have hstep : Real.log ((highBase a x : ℕ) : ℝ) ≤ Real.log (2 * cardLength a x) :=
      Real.log_le_log hQ0 hub
    refine hstep.trans (le_of_eq ?_)
    rw [Real.log_mul (by norm_num) (ne_of_gt (cardLength_pos a x)), log_cardLength]
  have hratio : Real.log (1 + lowEta c x)
      ≤ Real.log (cardLength β x / ((highBase a x : ℕ) : ℝ)) := by
    have hRHS : Real.log (cardLength β x / ((highBase a x : ℕ) : ℝ))
        = (Real.log x) ^ β - Real.log ((highBase a x : ℕ) : ℝ) := by
      rw [Real.log_div (ne_of_gt hh0) (ne_of_gt hQ0), log_cardLength]
    rw [hRHS]
    linarith
  rw [expSteps]
  refine Nat.le_floor ?_
  rw [Nat.cast_one, le_div_iff₀ hlogr, one_mul]
  exact hratio

/-- **The low ladder with an exponential bottom does not overshoot the window.** -/
theorem expTop_le_cardLength {a c β : ℝ} (ha : 0 < a) (hab : a < β) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop,
      ((highBase a x : ℕ) : ℝ) * (1 + lowEta c x) ^ (expSteps a c β x) ≤ cardLength β x := by
  have hzero := tendsto_lowEta (c := c) hc
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) hzero,
    expBase_lt_cardLength (a := a) (β := β) ha hab] with x hx1 hη1 hlt
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hη : 0 < lowEta c x := lowEta_pos hx1
  have hQ1 : (1 : ℝ) ≤ ((highBase a x : ℕ) : ℝ) := by
    have h1 := (highBase_bounds (a := a) hx1).1
    have h2 : (1 : ℝ) ≤ cardLength a x := by
      rw [cardLength]
      exact Real.one_le_exp (Real.rpow_nonneg hlogx.le a)
    linarith
  have hQ0 : (0 : ℝ) < ((highBase a x : ℕ) : ℝ) := by linarith
  have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
  have hlogr : (0 : ℝ) < Real.log (1 + lowEta c x) := Real.log_pos (by linarith)
  have hratio1 : (1 : ℝ) ≤ cardLength β x / ((highBase a x : ℕ) : ℝ) := by
    rw [le_div_iff₀ hQ0, one_mul]
    exact hlt.le
  have hlognn : (0 : ℝ) ≤ Real.log (cardLength β x / ((highBase a x : ℕ) : ℝ)) :=
    Real.log_nonneg hratio1
  have hfl : ((expSteps a c β x : ℕ) : ℝ) * Real.log (1 + lowEta c x)
      ≤ Real.log (cardLength β x / ((highBase a x : ℕ) : ℝ)) := by
    have hle : ((expSteps a c β x : ℕ) : ℝ)
        ≤ Real.log (cardLength β x / ((highBase a x : ℕ) : ℝ)) / Real.log (1 + lowEta c x) := by
      rw [expSteps]
      exact Nat.floor_le (div_nonneg hlognn hlogr.le)
    have := mul_le_mul_of_nonneg_right hle hlogr.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hlogr)] at this
  have hpow : (1 + lowEta c x) ^ (expSteps a c β x)
      ≤ cardLength β x / ((highBase a x : ℕ) : ℝ) := by
    have hlogpow : Real.log ((1 + lowEta c x) ^ (expSteps a c β x))
        = ((expSteps a c β x : ℕ) : ℝ) * Real.log (1 + lowEta c x) := by
      rw [Real.log_pow]
    have hpos : (0 : ℝ) < (1 + lowEta c x) ^ (expSteps a c β x) := by positivity
    have hposr : (0 : ℝ) < cardLength β x / ((highBase a x : ℕ) : ℝ) := by positivity
    have := Real.log_le_log_iff hpos hposr
    rw [← this, hlogpow]
    exact hfl
  calc ((highBase a x : ℕ) : ℝ) * (1 + lowEta c x) ^ (expSteps a c β x)
      ≤ ((highBase a x : ℕ) : ℝ) * (cardLength β x / ((highBase a x : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow hQ0.le
    _ = cardLength β x := by field_simp

/-- The bottom of the low ladder is at least two, and below its own top. -/
theorem two_le_highBase_and_le_expTop {a c β : ℝ} (ha : 0 < a) (_hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, 2 ≤ highBase a x ∧ highBase a x ≤ expTop a c β x := by
  have hpowa : Tendsto (fun x : ℝ => (Real.log x) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp Real.tendsto_log_atTop
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ), hpowa.eventually_ge_atTop (1 : ℝ)]
    with x hx1 hbig
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hη : 0 < lowEta c x := lowEta_pos hx1
  have hc2 : (2 : ℝ) ≤ cardLength a x := by
    rw [cardLength]
    have h1 : (1 : ℝ) + (Real.log x) ^ a ≤ Real.exp ((Real.log x) ^ a) :=
      Real.add_one_le_exp _ |>.trans_eq' (by ring)
    linarith
  have hQ2 : (2 : ℝ) ≤ ((highBase a x : ℕ) : ℝ) := by
    have := (highBase_bounds (a := a) hx1).1
    linarith
  have hQ2n : 2 ≤ highBase a x := by exact_mod_cast hQ2
  refine ⟨hQ2n, ?_⟩
  have hpowge : (1 : ℝ) ≤ (1 + lowEta c x) ^ (expSteps a c β x) := one_le_pow₀ (by linarith)
  rw [expTop]
  refine Nat.le_floor ?_
  nlinarith [hQ2, hpowge]

/-- The logarithm of the top of the low ladder, from both sides. -/
theorem log_expTop_bounds {a c β : ℝ} (ha : 0 < a) (hab : a < β) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop,
      (Real.log x) ^ β - Real.log 4 ≤ Real.log ((expTop a c β x : ℕ) : ℝ)
        ∧ Real.log ((expTop a c β x : ℕ) : ℝ) ≤ (Real.log x) ^ β := by
  have hzero := tendsto_lowEta (c := c) hc
  have hcard := tendsto_cardLength (β := β) (by linarith)
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) hzero,
    hcard.eventually_ge_atTop (8 : ℝ),
    expTop_le_cardLength (a := a) (c := c) (β := β) ha hab hc,
    two_le_highBase_and_le_expTop (a := a) (c := c) (β := β) ha hc] with x hx1 hη1 hh8 htop hlow
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hη : 0 < lowEta c x := lowEta_pos hx1
  have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
  have hQ0 : (0 : ℝ) < ((highBase a x : ℕ) : ℝ) := by
    have h1 := (highBase_bounds (a := a) hx1).1
    have h2 := cardLength_pos a x
    linarith
  have hlogr : (0 : ℝ) < Real.log (1 + lowEta c x) := Real.log_pos (by linarith)
  -- the upper bound
  have hTle : ((expTop a c β x : ℕ) : ℝ) ≤ cardLength β x := by
    rw [expTop]
    refine le_trans (Nat.floor_le (by positivity)) htop
  have hT2 : (2 : ℝ) ≤ ((expTop a c β x : ℕ) : ℝ) := by
    have h1 : (2 : ℕ) ≤ expTop a c β x := le_trans hlow.1 hlow.2
    exact_mod_cast h1
  have hupper : Real.log ((expTop a c β x : ℕ) : ℝ) ≤ (Real.log x) ^ β := by
    have := Real.log_le_log (by linarith) hTle
    rwa [log_cardLength] at this
  refine ⟨?_, hupper⟩
  -- the lower bound
  have hfl : Real.log (cardLength β x / ((highBase a x : ℕ) : ℝ)) / Real.log (1 + lowEta c x)
      < ((expSteps a c β x : ℕ) : ℝ) + 1 := by
    rw [expSteps]
    exact Nat.lt_floor_add_one _
  have hA : Real.log (cardLength β x / (((highBase a x : ℕ) : ℝ) * (1 + lowEta c x)))
      < Real.log ((1 + lowEta c x) ^ (expSteps a c β x)) := by
    have hsplit : Real.log (cardLength β x / (((highBase a x : ℕ) : ℝ) * (1 + lowEta c x)))
        = Real.log (cardLength β x / ((highBase a x : ℕ) : ℝ)) - Real.log (1 + lowEta c x) := by
      rw [Real.log_div (ne_of_gt hh0) (by positivity),
        Real.log_div (ne_of_gt hh0) (ne_of_gt hQ0),
        Real.log_mul (ne_of_gt hQ0) (by positivity)]
      ring
    rw [hsplit, Real.log_pow]
    have := mul_lt_mul_of_pos_right hfl hlogr
    rw [div_mul_cancel₀ _ (ne_of_gt hlogr)] at this
    linarith
  have hB : cardLength β x / (((highBase a x : ℕ) : ℝ) * (1 + lowEta c x))
      < (1 + lowEta c x) ^ (expSteps a c β x) := by
    by_contra hcon
    rw [not_lt] at hcon
    have := Real.log_le_log (by positivity) hcon
    linarith [hA]
  have hprod : cardLength β x / (1 + lowEta c x)
      < ((highBase a x : ℕ) : ℝ) * (1 + lowEta c x) ^ (expSteps a c β x) := by
    have hmul := mul_lt_mul_of_pos_left hB hQ0
    have hid : ((highBase a x : ℕ) : ℝ)
        * (cardLength β x / (((highBase a x : ℕ) : ℝ) * (1 + lowEta c x)))
        = cardLength β x / (1 + lowEta c x) := by
      field_simp
    rw [hid] at hmul
    exact hmul
  have hquarter : cardLength β x / 4 ≤ ((expTop a c β x : ℕ) : ℝ) := by
    have hlt := Nat.lt_floor_add_one (((highBase a x : ℕ) : ℝ)
      * (1 + lowEta c x) ^ (expSteps a c β x))
    have hTdef : ((expTop a c β x : ℕ) : ℝ)
        = ((⌊((highBase a x : ℕ) : ℝ) * (1 + lowEta c x) ^ (expSteps a c β x)⌋₊ : ℕ) : ℝ) := by
      rw [expTop]
    have hhalf : cardLength β x / 2 ≤ cardLength β x / (1 + lowEta c x) :=
      div_le_div_of_nonneg_left hh0.le (by linarith) (by linarith)
    rw [hTdef]
    linarith [hprod, hlt, hhalf, hh8]
  have hlog4 : Real.log (cardLength β x / 4) = (Real.log x) ^ β - Real.log 4 := by
    rw [Real.log_div (ne_of_gt hh0) (by norm_num), log_cardLength]
  have := Real.log_le_log (by positivity : (0 : ℝ) < cardLength β x / 4) hquarter
  rw [hlog4] at this
  exact this

/-- **The harmonic mass of the low range, from above.** -/
theorem expRange_harmonic_le {a c β : ℝ} (ha : 0 < a) (hab : a < β) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop,
      ∑ p ∈ primesRange (highBase a x) (expTop a c β x), 1 / (p : ℝ)
        ≤ β * Real.log (Real.log x) := by
  have hpowa : Tendsto (fun x : ℝ => (Real.log x) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp Real.tendsto_log_atTop
  have herr : Tendsto (fun x : ℝ =>
      2 * ((2 * mertensFirstConst + 1 / 2) / (Real.log x) ^ a)) atTop (𝓝 0) := by
    have := (Tendsto.div_atTop (tendsto_const_nhds
      (x := 2 * mertensFirstConst + 1 / 2)) hpowa).const_mul (2 : ℝ)
    simpa using this
  have hll : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    two_le_highBase_and_le_expTop (a := a) (c := c) (β := β) ha hc,
    log_expTop_bounds (a := a) (c := c) (β := β) ha hab hc,
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) herr,
    hpowa.eventually_ge_atTop (1 : ℝ),
    hll.eventually_ge_atTop (1 / a)] with x hx1 hlow hTlog hsmall hpow1 hubig
  obtain ⟨h₀, hz⟩ := hlow
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hmass := sum_inv_primesRange_le_logLog_diff h₀ hz
  have hQ0 : (0 : ℝ) < ((highBase a x : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ≤ ((highBase a x : ℕ) : ℝ) := by exact_mod_cast h₀
    linarith
  have hlogQ : (Real.log x) ^ a ≤ Real.log ((highBase a x : ℕ) : ℝ) := by
    have h1 := (highBase_bounds (a := a) hx1).1
    have := Real.log_le_log (cardLength_pos a x) h1
    rwa [log_cardLength] at this
  have hlogQ0 : (0 : ℝ) < Real.log ((highBase a x : ℕ) : ℝ) := by linarith
  have hT0 : (0 : ℝ) < Real.log ((expTop a c β x : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ≤ ((expTop a c β x : ℕ) : ℝ) := by
      have : (2 : ℕ) ≤ expTop a c β x := le_trans h₀ hz
      exact_mod_cast this
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2
    have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have hupperT : Real.log (Real.log ((expTop a c β x : ℕ) : ℝ)) ≤ β * Real.log (Real.log x) := by
    have hstep := Real.log_le_log hT0 hTlog.2
    rwa [Real.log_rpow hlogx] at hstep
  have hlowerQ : a * Real.log (Real.log x)
      ≤ Real.log (Real.log ((highBase a x : ℕ) : ℝ)) := by
    have hp0 : (0 : ℝ) < (Real.log x) ^ a := Real.rpow_pos_of_pos hlogx a
    have := Real.log_le_log hp0 hlogQ
    rwa [Real.log_rpow hlogx] at this
  have herrle : 2 * ((2 * mertensFirstConst + 1 / 2)
        / Real.log ((highBase a x : ℕ) : ℝ))
      ≤ 2 * ((2 * mertensFirstConst + 1 / 2) / (Real.log x) ^ a) := by
    have hc0 : (0 : ℝ) ≤ 2 * mertensFirstConst + 1 / 2 := by
      have := mertensFirstConst_nonneg
      linarith
    have hp0 : (0 : ℝ) < (Real.log x) ^ a := Real.rpow_pos_of_pos hlogx a
    have := div_le_div_of_nonneg_left hc0 hp0 hlogQ
    linarith
  have hau : 1 ≤ a * Real.log (Real.log x) := by
    have : 1 / a ≤ Real.log (Real.log x) := hubig
    rw [div_le_iff₀ ha] at this
    nlinarith [this, ha]
  linarith [hmass, hupperT, hlowerQ, herrle, hsmall, hau]

/-- **The harmonic mass of the low range, from below.**  This is the input the rough group needs:
the mass sits in a denominator. -/
theorem expRange_harmonic_ge {a c β : ℝ} (ha : 0 < a) (hab : a < β) (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop,
      (β - a) / 2 * Real.log (Real.log x)
        ≤ ∑ p ∈ primesRange (highBase a x) (expTop a c β x), 1 / (p : ℝ) := by
  have hpowa : Tendsto (fun x : ℝ => (Real.log x) ^ a) atTop atTop :=
    (tendsto_rpow_atTop ha).comp Real.tendsto_log_atTop
  have hpowβ : Tendsto (fun x : ℝ => (Real.log x) ^ β) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp Real.tendsto_log_atTop
  have herr : Tendsto (fun x : ℝ =>
      2 * ((2 * mertensFirstConst + 1 / 2) / (Real.log x) ^ a)) atTop (𝓝 0) := by
    have := (Tendsto.div_atTop (tendsto_const_nhds
      (x := 2 * mertensFirstConst + 1 / 2)) hpowa).const_mul (2 : ℝ)
    simpa using this
  have hll : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    two_le_highBase_and_le_expTop (a := a) (c := c) (β := β) ha hc,
    log_expTop_bounds (a := a) (c := c) (β := β) ha hab hc,
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) herr,
    hpowa.eventually_ge_atTop (1 : ℝ),
    hpowβ.eventually_ge_atTop (4 : ℝ),
    hll.eventually_ge_atTop (2 * (2 * Real.log 2 + 1) / (β - a))]
    with x hx1 hlow hTlog hsmall hpow1 hpowβ4 hubig
  obtain ⟨h₀, hz⟩ := hlow
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
  have hmass := sum_inv_primesRange_ge_logLog_diff h₀ hz
  have hQ0 : (0 : ℝ) < ((highBase a x : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ≤ ((highBase a x : ℕ) : ℝ) := by exact_mod_cast h₀
    linarith
  have hl2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  -- upper bound for the bottom's double logarithm
  have hlogQup : Real.log ((highBase a x : ℕ) : ℝ) ≤ 2 * (Real.log x) ^ a := by
    have hub := (highBase_bounds (a := a) hx1).2
    have hstep : Real.log ((highBase a x : ℕ) : ℝ) ≤ Real.log (2 * cardLength a x) :=
      Real.log_le_log hQ0 hub
    have hsplit : Real.log (2 * cardLength a x) = Real.log 2 + (Real.log x) ^ a := by
      rw [Real.log_mul (by norm_num) (ne_of_gt (cardLength_pos a x)), log_cardLength]
    linarith [hstep, hsplit, hl2, hpow1]
  have hlogQ0 : (0 : ℝ) < Real.log ((highBase a x : ℕ) : ℝ) := by
    have h2 : (2 : ℝ) ≤ ((highBase a x : ℕ) : ℝ) := by exact_mod_cast h₀
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) h2
    have hl2p : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    linarith
  have hupperQ : Real.log (Real.log ((highBase a x : ℕ) : ℝ))
      ≤ Real.log 2 + a * Real.log (Real.log x) := by
    have hp0 : (0 : ℝ) < 2 * (Real.log x) ^ a := by positivity
    have hstep := Real.log_le_log hlogQ0 hlogQup
    have hsplit : Real.log (2 * (Real.log x) ^ a) = Real.log 2 + a * Real.log (Real.log x) := by
      rw [Real.log_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hlogx a)),
        Real.log_rpow hlogx]
    linarith [hstep, hsplit]
  -- lower bound for the top's double logarithm
  have hTlow : (Real.log x) ^ β / 2 ≤ Real.log ((expTop a c β x : ℕ) : ℝ) := by
    have := hTlog.1
    rw [hl4] at this
    nlinarith [this, hpowβ4, hl2]
  have hT0 : (0 : ℝ) < Real.log ((expTop a c β x : ℕ) : ℝ) := by
    have : (0 : ℝ) < (Real.log x) ^ β / 2 := by
      have := Real.rpow_pos_of_pos hlogx β
      linarith
    linarith [hTlow]
  have hlowerT : β * Real.log (Real.log x) - Real.log 2
      ≤ Real.log (Real.log ((expTop a c β x : ℕ) : ℝ)) := by
    have hp0 : (0 : ℝ) < (Real.log x) ^ β / 2 := by
      have := Real.rpow_pos_of_pos hlogx β
      linarith
    have hstep := Real.log_le_log hp0 hTlow
    have hsplit : Real.log ((Real.log x) ^ β / 2) = β * Real.log (Real.log x) - Real.log 2 := by
      rw [Real.log_div (ne_of_gt (Real.rpow_pos_of_pos hlogx β)) (by norm_num),
        Real.log_rpow hlogx]
    linarith [hstep, hsplit]
  have herrle : 2 * ((2 * mertensFirstConst + 1 / 2)
        / Real.log ((highBase a x : ℕ) : ℝ))
      ≤ 2 * ((2 * mertensFirstConst + 1 / 2) / (Real.log x) ^ a) := by
    have hc0 : (0 : ℝ) ≤ 2 * mertensFirstConst + 1 / 2 := by
      have := mertensFirstConst_nonneg
      linarith
    have hp0 : (0 : ℝ) < (Real.log x) ^ a := Real.rpow_pos_of_pos hlogx a
    have hlogQ : (Real.log x) ^ a ≤ Real.log ((highBase a x : ℕ) : ℝ) := by
      have h1 := (highBase_bounds (a := a) hx1).1
      have := Real.log_le_log (cardLength_pos a x) h1
      rwa [log_cardLength] at this
    have := div_le_div_of_nonneg_left hc0 hp0 hlogQ
    linarith
  have hslack : 2 * Real.log 2 + 1 ≤ (β - a) / 2 * Real.log (Real.log x) := by
    have hba : (0 : ℝ) < β - a := by linarith
    rw [div_le_iff₀ hba] at hubig
    nlinarith [hubig, hba]
  linarith [hmass, hupperQ, hlowerT, herrle, hsmall, hslack]

end

end RHTower.Sieve
