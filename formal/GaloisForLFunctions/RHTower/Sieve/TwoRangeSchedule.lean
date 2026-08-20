import GaloisForLFunctions.RHTower.Sieve.ShortIntervalLength
import GaloisForLFunctions.RHTower.Sieve.LogPowerLimits

/-!
# The schedule of the two-range argument

The low designated range starts at a **polylogarithmic** bottom — that is the whole point of the
two-range architecture, and it is what the exceptional-set measure permits once Halász–Montgomery
carries the reciprocal kernel decay:

```text
   low  range : (log x)^K < p ≤ h = exp((log x)^β) ,  step ratio 1 + (log x)^{−c} ,
                threshold  θ = (log x)^{−A} ;
   high range : exp((log x)^a) < q ≤ exp((log x)^b) ,  9/10 < a < b < 1 ,
                step ratio 1 + (log x)^{−c'} ,  never thresholded ;
   window     : W = T₀ = (M/h)·log log x ,  M = ⌊√x + h⌋ ,  disc radius w₀ = O(1) ,
   split      : δ = (log log x)^{−1/2} .
```

The exponents obey `c > 1 + β`, `c' > 1 + b − a`, `2A > β + c`, `K > max(2(3+c+2A), (c+1)/2)`; the
first two come from the ladder defect, the third from the small half's diagonal, and the last from
the exceptional measure.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The bottom of the low designated range: a fixed power of the logarithm. -/
def lowBase (K x : ℝ) : ℕ := ⌈(Real.log x) ^ K⌉₊

/-- The step ratio of the low ladder. -/
def lowEta (c x : ℝ) : ℝ := (Real.log x) ^ (-c)

/-- The relative threshold on the low prime blocks. -/
def lowTheta (A x : ℝ) : ℝ := (Real.log x) ^ (-A)

/-- The bottom of the high designated range. -/
def highBase (a x : ℝ) : ℕ := ⌈Real.exp ((Real.log x) ^ a)⌉₊

/-- The step ratio of the high ladder. -/
def highEta (c' x : ℝ) : ℝ := (Real.log x) ^ (-c')

/-- The length of the Dirichlet polynomial. -/
def twoRangeLength (β x : ℝ) : ℕ := ⌊Real.sqrt x + cardLength β x⌋₊

/-- The Gallagher cutoff. -/
def twoRangeCut (β x : ℝ) : ℝ := ((twoRangeLength β x : ℕ) : ℝ) / cardLength β x

/-- The height at which the single head bound is taken. -/
def twoRangeTop (β x : ℝ) : ℝ := twoRangeCut β x * Real.log (Real.log x)

/-- The weight of the Cauchy–Schwarz split between the bilinear part and the rough part. -/
def twoRangeDelta (x : ℝ) : ℝ := (Real.log (Real.log x)) ^ (-(1 : ℝ) / 2)

theorem lowEta_pos {c x : ℝ} (hx : 1 < x) : 0 < lowEta c x :=
  Real.rpow_pos_of_pos (Real.log_pos hx) _

theorem highEta_pos {c' x : ℝ} (hx : 1 < x) : 0 < highEta c' x :=
  Real.rpow_pos_of_pos (Real.log_pos hx) _

theorem lowTheta_pos {A x : ℝ} (hx : 1 < x) : 0 < lowTheta A x :=
  Real.rpow_pos_of_pos (Real.log_pos hx) _

theorem twoRangeDelta_pos {x : ℝ} (hx : Real.exp 1 < x) : 0 < twoRangeDelta x := by
  have hlog : 1 < Real.log x := by
    have := Real.log_lt_log (Real.exp_pos 1) hx
    rwa [Real.log_exp] at this
  have hll : 0 < Real.log (Real.log x) := Real.log_pos hlog
  exact Real.rpow_pos_of_pos hll _

/-- **The step ratios vanish.** -/
theorem tendsto_lowEta {c : ℝ} (hc : 0 < c) : Tendsto (fun x : ℝ => lowEta c x) atTop (𝓝 0) := by
  refine (tendsto_log_rpow_neg hc).congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
  rfl

theorem tendsto_highEta {c' : ℝ} (hc' : 0 < c') :
    Tendsto (fun x : ℝ => highEta c' x) atTop (𝓝 0) := by
  refine (tendsto_log_rpow_neg hc').congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
  rfl

theorem tendsto_lowTheta {A : ℝ} (hA : 0 < A) :
    Tendsto (fun x : ℝ => lowTheta A x) atTop (𝓝 0) := by
  refine (tendsto_log_rpow_neg hA).congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
  rfl

/-- **The split weight vanishes, but only at the rate of a root of `log log`.** -/
theorem tendsto_twoRangeDelta : Tendsto twoRangeDelta atTop (𝓝 0) := by
  have hcomp : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hbase : Tendsto (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) atTop (𝓝 0) := by
    have h := tendsto_rpow_neg_atTop (y := (1 : ℝ) / 2) (by norm_num)
    refine h.congr fun t => ?_
    congr 1
    ring
  exact hbase.comp hcomp

/-- The bottom of the low range is at least one. -/
theorem one_le_lowBase {K x : ℝ} (hK : 0 ≤ K) (hx : Real.exp 1 ≤ x) : 1 ≤ lowBase K x := by
  have hlog : 1 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hx
    rwa [Real.log_exp] at this
  have hpow : (1 : ℝ) ≤ (Real.log x) ^ K := Real.one_le_rpow hlog hK
  have := Nat.one_le_ceil_iff.2 (lt_of_lt_of_le zero_lt_one hpow)
  exact this

/-- The bottom of the low range has the expected logarithm, up to rounding. -/
theorem lowBase_bounds {K x : ℝ} (hK : 0 ≤ K) (hx : Real.exp 1 ≤ x) :
    (Real.log x) ^ K ≤ ((lowBase K x : ℕ) : ℝ)
      ∧ ((lowBase K x : ℕ) : ℝ) ≤ (Real.log x) ^ K + 1 := by
  have hlog : 1 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hx
    rwa [Real.log_exp] at this
  have hpow : (1 : ℝ) ≤ (Real.log x) ^ K := Real.one_le_rpow hlog hK
  rw [lowBase]
  refine ⟨Nat.le_ceil _, ?_⟩
  have := Nat.ceil_lt_add_one (le_of_lt (lt_of_lt_of_le zero_lt_one hpow))
  linarith

/-- The number of steps of the low ladder. -/
def lowSteps (K c β x : ℝ) : ℕ :=
  ⌊Real.log (cardLength β x / ((lowBase K x : ℕ) : ℝ)) / Real.log (1 + lowEta c x)⌋₊

/-- The number of steps of the high ladder. -/
def highSteps (a b c' x : ℝ) : ℕ :=
  ⌊((Real.log x) ^ b - (Real.log x) ^ a) / Real.log (1 + highEta c' x)⌋₊

/-- `η/2 ≤ log(1+η)` below unit ratio. -/
theorem log_one_add_ge_half_self {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    η / 2 ≤ Real.log (1 + η) := by
  have h1 : (0 : ℝ) < 1 + η := by linarith
  have hkey : η / (1 + η) ≤ Real.log (1 + η) := by
    have hexp := Real.add_one_le_exp (-(η / (1 + η)))
    have hval : -(η / (1 + η)) + 1 = 1 / (1 + η) := by
      field_simp
      ring
    rw [hval] at hexp
    have hlog := Real.log_le_log (by positivity) hexp
    rw [Real.log_exp, Real.log_div one_ne_zero (ne_of_gt h1), Real.log_one] at hlog
    linarith
  have hdiv : η / 2 ≤ η / (1 + η) :=
    div_le_div_of_nonneg_left hη.le (by linarith) (by linarith)
  linarith

/-- **The low ladder has polylogarithmically many steps.** -/
theorem lowSteps_le {K c β : ℝ} (hK : 0 ≤ K) (hc : 0 < c) (_hβ : 0 < β) :
    ∀ᶠ x : ℝ in atTop,
      ((lowSteps K c β x : ℕ) : ℝ) ≤ 2 * (Real.log x) ^ (β + c) := by
  have hzero := tendsto_lowEta (c := c) hc
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 1),
    Filter.eventually_gt_atTop (1 : ℝ),
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) hzero] with x hxe hx1 hη1
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hη : 0 < lowEta c x := lowEta_pos hx1
  have hQ1 : (1 : ℝ) ≤ ((lowBase K x : ℕ) : ℝ) := by
    have := one_le_lowBase hK hxe
    exact_mod_cast this
  have hQ0 : (0 : ℝ) < ((lowBase K x : ℕ) : ℝ) := by linarith
  have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
  have hlogr : (0 : ℝ) < Real.log (1 + lowEta c x) := Real.log_pos (by linarith)
  have hhalf := log_one_add_ge_half_self hη hη1
  have hratio : Real.log (cardLength β x / ((lowBase K x : ℕ) : ℝ)) ≤ (Real.log x) ^ β := by
    rw [Real.log_div (ne_of_gt hh0) (ne_of_gt hQ0), log_cardLength]
    have : (0 : ℝ) ≤ Real.log ((lowBase K x : ℕ) : ℝ) := Real.log_nonneg hQ1
    linarith
  have hfl : ((lowSteps K c β x : ℕ) : ℝ)
      ≤ Real.log (cardLength β x / ((lowBase K x : ℕ) : ℝ)) / Real.log (1 + lowEta c x)
        ∨ Real.log (cardLength β x / ((lowBase K x : ℕ) : ℝ)) < 0 := by
    by_cases hnn : 0 ≤ Real.log (cardLength β x / ((lowBase K x : ℕ) : ℝ))
    · left
      rw [lowSteps]
      exact Nat.floor_le (div_nonneg hnn hlogr.le)
    · right
      exact lt_of_not_ge hnn
  have hpowβ : (0 : ℝ) ≤ (Real.log x) ^ β := Real.rpow_nonneg hlogx.le β
  have hkey : 2 * (Real.log x) ^ β / lowEta c x = 2 * (Real.log x) ^ (β + c) := by
    rw [lowEta, div_eq_mul_inv, ← Real.rpow_neg hlogx.le, neg_neg, mul_assoc,
      ← Real.rpow_add hlogx]
  rcases hfl with hfl | hneg
  · refine hfl.trans ?_
    rw [← hkey]
    refine (div_le_div₀ (by positivity) hratio (by linarith) hhalf).trans (le_of_eq ?_)
    field_simp
  · have hzero : ((lowSteps K c β x : ℕ) : ℝ) = 0 := by
      have : lowSteps K c β x = 0 := by
        rw [lowSteps]
        refine Nat.floor_eq_zero.2 ?_
        have : Real.log (cardLength β x / ((lowBase K x : ℕ) : ℝ))
            / Real.log (1 + lowEta c x) < 0 := div_neg_of_neg_of_pos hneg hlogr
        linarith
      rw [this]
      norm_num
    rw [hzero]
    positivity

end

end RHTower.Sieve
