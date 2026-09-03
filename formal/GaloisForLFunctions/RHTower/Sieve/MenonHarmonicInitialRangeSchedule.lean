import GaloisForLFunctions.RHTower.Sieve.ExceptionalMeasureSchedule

/-!
# Variable-top initial prime range for Menon's quantitative theorem

The initial designated range starts at an exponential logarithmic scale but follows the actual
short-interval length at its upper endpoint.  This is essential for the growing reciprocal-marker
grid: a fixed upper exponent would leave a rough remainder of constant density.
-/

namespace RHTower.Sieve

open Filter Topology Finset MeasureTheory

noncomputable section

/-- Geometric depth from the exponential bottom to an arbitrary natural upper endpoint. -/
def menonInitialRangeSteps (a c x : ℝ) (hN : ℕ) : ℕ :=
  ⌊Real.log ((hN : ℝ) / ((highBase a x : ℕ) : ℝ)) /
      Real.log (1 + lowEta c x)⌋₊

/-- Last fully retained geometric endpoint below the supplied natural upper endpoint. -/
def menonInitialRangeTop (a c x : ℝ) (hN : ℕ) : ℕ :=
  ⌊((highBase a x : ℕ) : ℝ) *
      (1 + lowEta c x) ^ menonInitialRangeSteps a c x hN⌋₊

/-- Literal prime range used by the initial Ramaré decomposition. -/
def menonInitialRangePrimes (a c x : ℝ) (hN : ℕ) : Finset ℕ :=
  primesRange (highBase a x) (menonInitialRangeTop a c x hN)

/-- The variable-top ladder never overshoots its supplied endpoint. -/
theorem menonInitialRangeTop_le
    {a c x : ℝ} {hN : ℕ} (hx : 1 < x)
    (hQh : ((highBase a x : ℕ) : ℝ) < (hN : ℝ)) :
    menonInitialRangeTop a c x hN ≤ hN := by
  have hQ0 : (0 : ℝ) < ((highBase a x : ℕ) : ℝ) := by
    have hbase := (highBase_bounds (a := a) hx).1
    exact lt_of_lt_of_le (cardLength_pos a x) hbase
  have hh0 : (0 : ℝ) < (hN : ℝ) := lt_trans hQ0 hQh
  have heta : 0 < lowEta c x := lowEta_pos hx
  have hlogr : 0 < Real.log (1 + lowEta c x) := Real.log_pos (by linarith)
  have hratio1 : (1 : ℝ) ≤ (hN : ℝ) / ((highBase a x : ℕ) : ℝ) := by
    rw [le_div_iff₀ hQ0, one_mul]
    exact hQh.le
  have hlognn : 0 ≤ Real.log ((hN : ℝ) / ((highBase a x : ℕ) : ℝ)) :=
    Real.log_nonneg hratio1
  have hfl : ((menonInitialRangeSteps a c x hN : ℕ) : ℝ) *
      Real.log (1 + lowEta c x) ≤
        Real.log ((hN : ℝ) / ((highBase a x : ℕ) : ℝ)) := by
    have hle : ((menonInitialRangeSteps a c x hN : ℕ) : ℝ) ≤
        Real.log ((hN : ℝ) / ((highBase a x : ℕ) : ℝ)) /
          Real.log (1 + lowEta c x) := by
      rw [menonInitialRangeSteps]
      exact Nat.floor_le (div_nonneg hlognn hlogr.le)
    have hmul := mul_le_mul_of_nonneg_right hle hlogr.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hlogr)] at hmul
  have hpow : (1 + lowEta c x) ^ menonInitialRangeSteps a c x hN ≤
      (hN : ℝ) / ((highBase a x : ℕ) : ℝ) := by
    have hpow0 : 0 < (1 + lowEta c x) ^ menonInitialRangeSteps a c x hN := by positivity
    have hratio0 : 0 < (hN : ℝ) / ((highBase a x : ℕ) : ℝ) := by positivity
    rw [← Real.log_le_log_iff hpow0 hratio0, Real.log_pow]
    exact hfl
  have hreal : ((menonInitialRangeTop a c x hN : ℕ) : ℝ) ≤ (hN : ℝ) := by
    rw [menonInitialRangeTop]
    refine (Nat.floor_le (by positivity)).trans ?_
    calc
      ((highBase a x : ℕ) : ℝ) *
          (1 + lowEta c x) ^ menonInitialRangeSteps a c x hN
          ≤ ((highBase a x : ℕ) : ℝ) *
              ((hN : ℝ) / ((highBase a x : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left hpow hQ0.le
      _ = (hN : ℝ) := by field_simp
  exact_mod_cast hreal

/-- Before the terminal rounding, the retained endpoint is within one ladder ratio of `hN`. -/
theorem menonInitialRange_beforeTop_lt
    {a c x : ℝ} {hN : ℕ} (hx : 1 < x)
    (hQh : ((highBase a x : ℕ) : ℝ) < (hN : ℝ)) :
    (hN : ℝ) / (1 + lowEta c x) <
      ((highBase a x : ℕ) : ℝ) *
        (1 + lowEta c x) ^ menonInitialRangeSteps a c x hN := by
  have hQ0 : (0 : ℝ) < ((highBase a x : ℕ) : ℝ) := by
    have hbase := (highBase_bounds (a := a) hx).1
    exact lt_of_lt_of_le (cardLength_pos a x) hbase
  have hh0 : (0 : ℝ) < (hN : ℝ) := lt_trans hQ0 hQh
  have heta : 0 < lowEta c x := lowEta_pos hx
  have hlogr : 0 < Real.log (1 + lowEta c x) := Real.log_pos (by linarith)
  have hq : Real.log ((hN : ℝ) / ((highBase a x : ℕ) : ℝ)) /
      Real.log (1 + lowEta c x) <
        ((menonInitialRangeSteps a c x hN : ℕ) : ℝ) + 1 := by
    rw [menonInitialRangeSteps]
    exact Nat.lt_floor_add_one _
  have hlog : Real.log ((hN : ℝ) / ((highBase a x : ℕ) : ℝ)) <
      (((menonInitialRangeSteps a c x hN : ℕ) : ℝ) + 1) *
        Real.log (1 + lowEta c x) := by
    have hmul := mul_lt_mul_of_pos_right hq hlogr
    rwa [div_mul_cancel₀ _ (ne_of_gt hlogr)] at hmul
  have hlogpow : (((menonInitialRangeSteps a c x hN : ℕ) : ℝ) + 1) *
      Real.log (1 + lowEta c x) =
        Real.log ((1 + lowEta c x) ^ (menonInitialRangeSteps a c x hN + 1)) := by
    rw [Real.log_pow]
    push_cast
    rfl
  rw [hlogpow] at hlog
  have hratio0 : 0 < (hN : ℝ) / ((highBase a x : ℕ) : ℝ) := by positivity
  have hpow0 : 0 < (1 + lowEta c x) ^ (menonInitialRangeSteps a c x hN + 1) := by positivity
  have hexp : (hN : ℝ) / ((highBase a x : ℕ) : ℝ) <
      (1 + lowEta c x) ^ (menonInitialRangeSteps a c x hN + 1) := by
    exact (Real.log_lt_log_iff hratio0 hpow0).mp hlog
  rw [pow_succ] at hexp
  have hstep0 : 0 < 1 + lowEta c x := by linarith
  rw [div_lt_iff₀ hstep0]
  calc
    (hN : ℝ) < ((highBase a x : ℕ) : ℝ) *
        ((1 + lowEta c x) ^ menonInitialRangeSteps a c x hN *
          (1 + lowEta c x)) := by
      have hexp' := (div_lt_iff₀ hQ0).mp hexp
      simpa only [mul_assoc, mul_left_comm, mul_comm] using hexp'
    _ = (((highBase a x : ℕ) : ℝ) *
        (1 + lowEta c x) ^ menonInitialRangeSteps a c x hN) *
          (1 + lowEta c x) := by ring

/-- After natural rounding, the retained top is still at least one quarter of `hN`. -/
theorem menonInitialRangeTop_ge_quarter
    {a c x : ℝ} {hN : ℕ} (hx : 1 < x)
    (hQh : ((highBase a x : ℕ) : ℝ) < (hN : ℝ))
    (heta1 : lowEta c x ≤ 1) (hh4 : 4 ≤ hN) :
    (hN : ℝ) / 4 ≤ (menonInitialRangeTop a c x hN : ℝ) := by
  have hnear := menonInitialRange_beforeTop_lt (c := c) hx hQh
  have hrle : 1 + lowEta c x ≤ 2 := by linarith
  have hr0 : 0 < 1 + lowEta c x := by linarith [lowEta_pos (c := c) hx]
  have hhalf : (hN : ℝ) / 2 ≤ (hN : ℝ) / (1 + lowEta c x) := by
    exact div_le_div_of_nonneg_left (by positivity) hr0 hrle
  have hfloor : ((highBase a x : ℕ) : ℝ) *
        (1 + lowEta c x) ^ menonInitialRangeSteps a c x hN <
      (menonInitialRangeTop a c x hN : ℝ) + 1 := by
    rw [menonInitialRangeTop]
    exact Nat.lt_floor_add_one _
  have hh4r : (4 : ℝ) ≤ (hN : ℝ) := by exact_mod_cast hh4
  linarith

/-- Every initial-range prime has the exact geometric-ladder range needed by Ramaré assembly. -/
theorem menonInitialRangePrimes_range
    {a c x : ℝ} {hN : ℕ} (hx : 1 < x) :
    ∀ p ∈ menonInitialRangePrimes a c x hN,
      ((highBase a x : ℕ) : ℝ) < (p : ℝ) ∧
        (p : ℝ) ≤ ((highBase a x : ℕ) : ℝ) *
          (1 + lowEta c x) ^ menonInitialRangeSteps a c x hN := by
  intro p hp
  have hpRange := (mem_primesRange.mp hp).2
  refine ⟨by exact_mod_cast hpRange.1, ?_⟩
  have hQ0 : (0 : ℝ) < ((highBase a x : ℕ) : ℝ) := by
    have hbase := (highBase_bounds (a := a) hx).1
    exact lt_of_lt_of_le (cardLength_pos a x) hbase
  have hstep0 : 0 < 1 + lowEta c x := by linarith [lowEta_pos (c := c) hx]
  have hfloor : ((menonInitialRangeTop a c x hN : ℕ) : ℝ) ≤
      ((highBase a x : ℕ) : ℝ) *
        (1 + lowEta c x) ^ menonInitialRangeSteps a c x hN := by
    rw [menonInitialRangeTop]
    exact Nat.floor_le (mul_nonneg hQ0.le (pow_nonneg hstep0.le _))
  exact (by exact_mod_cast hpRange.2 : (p : ℝ) ≤ (menonInitialRangeTop a c x hN : ℝ)).trans hfloor

/-- The variable-top ladder has at most `2 log(hN) (log x)^c` steps. -/
theorem menonInitialRangeSteps_le
    {a c x : ℝ} {hN : ℕ} (hx : Real.exp 1 ≤ x) (hc : 0 < c)
    (hQh : highBase a x ≤ hN) :
    ((menonInitialRangeSteps a c x hN : ℕ) : ℝ) ≤
      2 * Real.log (hN : ℝ) * (Real.log x) ^ c := by
  have hx1 : 1 < x := lt_of_lt_of_le (by have := Real.exp_one_gt_d9; linarith) hx
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hlogx1 : 1 ≤ Real.log x := by
    have := Real.log_le_log (Real.exp_pos 1) hx
    rwa [Real.log_exp] at this
  have heta : 0 < lowEta c x := lowEta_pos hx1
  have heta1 : lowEta c x ≤ 1 := by
    rw [lowEta]
    have hpow := Real.rpow_le_rpow_of_exponent_le hlogx1 (by linarith : -c ≤ 0)
    simpa using hpow
  have hlogr : 0 < Real.log (1 + lowEta c x) := Real.log_pos (by linarith)
  have hQ1 : (1 : ℝ) ≤ ((highBase a x : ℕ) : ℝ) := by
    have hbase := (highBase_bounds (a := a) hx1).1
    have hcard1 : 1 ≤ cardLength a x := by
      rw [cardLength]
      exact Real.one_le_exp (Real.rpow_nonneg hlogx.le a)
    linarith
  have hh1 : (1 : ℝ) ≤ (hN : ℝ) := by
    exact_mod_cast (le_trans (by exact_mod_cast hQ1 : 1 ≤ highBase a x) hQh)
  have hratio1 : 1 ≤ (hN : ℝ) / ((highBase a x : ℕ) : ℝ) := by
    rw [le_div_iff₀ (by positivity), one_mul]
    exact_mod_cast hQh
  have hnum0 : 0 ≤ Real.log ((hN : ℝ) / ((highBase a x : ℕ) : ℝ)) :=
    Real.log_nonneg hratio1
  have hfloor : ((menonInitialRangeSteps a c x hN : ℕ) : ℝ) ≤
      Real.log ((hN : ℝ) / ((highBase a x : ℕ) : ℝ)) /
        Real.log (1 + lowEta c x) := by
    rw [menonInitialRangeSteps]
    exact Nat.floor_le (div_nonneg hnum0 hlogr.le)
  have hnum : Real.log ((hN : ℝ) / ((highBase a x : ℕ) : ℝ)) ≤ Real.log (hN : ℝ) := by
    rw [Real.log_div (by positivity) (by positivity)]
    exact sub_le_self _ (Real.log_nonneg hQ1)
  have hhalf := log_one_add_ge_half_self heta heta1
  have hpre : Real.log ((hN : ℝ) / ((highBase a x : ℕ) : ℝ)) /
      Real.log (1 + lowEta c x) ≤ 2 * Real.log (hN : ℝ) / lowEta c x := by
    calc
      Real.log ((hN : ℝ) / ((highBase a x : ℕ) : ℝ)) /
          Real.log (1 + lowEta c x)
          ≤ Real.log (hN : ℝ) / (lowEta c x / 2) :=
        div_le_div₀ (Real.log_nonneg hh1) hnum (by positivity) hhalf
      _ = 2 * Real.log (hN : ℝ) / lowEta c x := by field_simp
  have hetaInv : 1 / lowEta c x = (Real.log x) ^ c := by
    rw [lowEta, one_div, ← Real.rpow_neg hlogx.le, neg_neg]
  calc
    ((menonInitialRangeSteps a c x hN : ℕ) : ℝ) ≤
        Real.log ((hN : ℝ) / ((highBase a x : ℕ) : ℝ)) /
          Real.log (1 + lowEta c x) := hfloor
    _ ≤ 2 * Real.log (hN : ℝ) / lowEta c x := hpre
    _ = 2 * Real.log (hN : ℝ) * (Real.log x) ^ c := by
      rw [div_eq_mul_inv]
      have hinv : (lowEta c x)⁻¹ = (Real.log x) ^ c := by
        simpa [one_div] using hetaInv
      rw [hinv]

/-- The variable-top ladder embeds in the same ladder whose upper endpoint is `x`. -/
theorem menonInitialRangeSteps_le_expSteps_one
    {a c x : ℝ} {hN : ℕ} (hx : 1 < x)
    (hQh : ((highBase a x : ℕ) : ℝ) < (hN : ℝ)) (hhx : (hN : ℝ) ≤ x) :
    menonInitialRangeSteps a c x hN ≤ expSteps a c 1 x := by
  have hQ0 : (0 : ℝ) < ((highBase a x : ℕ) : ℝ) := by
    have hbase := (highBase_bounds (a := a) hx).1
    exact lt_of_lt_of_le (cardLength_pos a x) hbase
  have hh0 : (0 : ℝ) < (hN : ℝ) := lt_trans hQ0 hQh
  have hlogr : 0 < Real.log (1 + lowEta c x) :=
    Real.log_pos (by linarith [lowEta_pos (c := c) hx])
  have hcard : cardLength 1 x = x := by
    rw [cardLength, Real.rpow_one, Real.exp_log (by linarith)]
  have hratio : (hN : ℝ) / ((highBase a x : ℕ) : ℝ) ≤
      cardLength 1 x / ((highBase a x : ℕ) : ℝ) := by
    rw [hcard]
    exact div_le_div_of_nonneg_right hhx hQ0.le
  have hlog : Real.log ((hN : ℝ) / ((highBase a x : ℕ) : ℝ)) ≤
      Real.log (cardLength 1 x / ((highBase a x : ℕ) : ℝ)) :=
    Real.log_le_log (div_pos hh0 hQ0) hratio
  have hquot : Real.log ((hN : ℝ) / ((highBase a x : ℕ) : ℝ)) /
      Real.log (1 + lowEta c x) ≤
        Real.log (cardLength 1 x / ((highBase a x : ℕ) : ℝ)) /
          Real.log (1 + lowEta c x) :=
    div_le_div_of_nonneg_right hlog hlogr.le
  rw [menonInitialRangeSteps, expSteps]
  exact Nat.floor_mono hquot

/-- Every retained variable-top block is literally its block in the full ladder to `x`. -/
theorem geomBlock_menonInitialRangePrimes_eq_expOne
    {a c x : ℝ} {hN j : ℕ} (hx : 1 < x)
    (hQh : ((highBase a x : ℕ) : ℝ) < (hN : ℝ)) (hhx : (hN : ℝ) ≤ x)
    (hj : j ∈ Finset.range (menonInitialRangeSteps a c x hN)) :
    geomBlock (menonInitialRangePrimes a c x hN)
        ((highBase a x : ℕ) : ℝ) (1 + lowEta c x) j =
      geomBlock (primesRange (highBase a x) (expTop a c 1 x))
        ((highBase a x : ℕ) : ℝ) (1 + lowEta c x) j := by
  classical
  have hjL : j + 1 ≤ menonInitialRangeSteps a c x hN := Finset.mem_range.1 hj
  have hsteps := menonInitialRangeSteps_le_expSteps_one (c := c) hx hQh hhx
  have hjE : j + 1 ≤ expSteps a c 1 x := hjL.trans hsteps
  apply Finset.ext
  intro p
  rw [menonInitialRangePrimes, menonInitialRangeTop, expTop,
    mem_geomBlock_primesRange (lowEta_pos (c := c) hx).le rfl hjL rfl p,
    mem_geomBlock_primesRange (lowEta_pos (c := c) hx).le rfl hjE rfl p]

/-- Uniform moment input for every block of every variable-top initial range below `x`. -/
theorem menonInitialRange_moment_bounds {a c A : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hc : 0 < c) (hA : 0 < A) :
    ∀ᶠ x : ℝ in atTop, ∀ hN : ℕ,
      ((highBase a x : ℕ) : ℝ) < (hN : ℝ) → (hN : ℝ) ≤ x →
      ∀ j ∈ Finset.range (menonInitialRangeSteps a c x hN),
        0 < ((geomBlock (menonInitialRangePrimes a c x hN)
              ((highBase a x : ℕ) : ℝ) (1 + lowEta c x) j).card : ℝ)
          ∧ (Real.log x) ^ a / 2
              ≤ Real.log (((geomBlock (menonInitialRangePrimes a c x hN)
                  ((highBase a x : ℕ) : ℝ) (1 + lowEta c x) j).card : ℝ)
                * lowTheta A x ^ 2 / ((momentOrder a x : ℕ) : ℝ))
          ∧ Real.log ((⌊((highBase a x : ℕ) : ℝ) *
                (1 + lowEta c x) ^ (j + 1)⌋₊ : ℕ) : ℝ)
              ≤ Real.log 2 + Real.log x
          ∧ -((c + 2 * A + 3) * Real.log (Real.log x))
              ≤ Real.log (((geomBlock (menonInitialRangePrimes a c x hN)
                  ((highBase a x : ℕ) : ℝ) (1 + lowEta c x) j).card : ℝ)
                * lowTheta A x ^ 2 / ((momentOrder a x : ℕ) : ℝ))
                - Real.log ((⌊((highBase a x : ℕ) : ℝ) *
                    (1 + lowEta c x) ^ (j + 1)⌋₊ : ℕ) : ℝ) := by
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    expBlock_moment_bounds (a := a) (c := c) (A := A) (β := (1 : ℝ))
      ha ha1 ha1 hc hA] with x hx hfull
  intro hN hQh hhx j hj
  have hsteps := menonInitialRangeSteps_le_expSteps_one (c := c) hx hQh hhx
  have hjE : j ∈ Finset.range (expSteps a c 1 x) :=
    Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hj) hsteps)
  have heq := geomBlock_menonInitialRangePrimes_eq_expOne
    (a := a) (c := c) hx hQh hhx hj
  have h := hfull j hjE
  rw [← heq] at h
  rcases h with ⟨hcard, hgain, hupper, hgap⟩
  refine ⟨hcard, hgain, ?_, ?_⟩
  · simpa using hupper
  · have hconst : c + 2 * A + (1 : ℝ) + 2 = c + 2 * A + 3 := by ring
    rw [hconst] at hgap
    exact hgap

/-- Exceptional-frequency measure for the variable-top initial range, uniformly in its endpoint. -/
theorem measureReal_menonInitialRange_annulusLarge_le {a c A : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hc : 0 < c) (hA : 0 < A) :
    ∀ᶠ x : ℝ in atTop, ∀ (hN : ℕ) (W w₀ : ℝ),
      ((highBase a x : ℕ) : ℝ) < (hN : ℝ) → (hN : ℝ) ≤ x → 0 ≤ W →
      volume.real (annulusLarge
          (allBlocksSmall (menonInitialRangePrimes a c x hN)
            ((highBase a x : ℕ) : ℝ) (lowEta c x)
            (menonInitialRangeSteps a c x hN)
            (fun j => ((geomBlock (menonInitialRangePrimes a c x hN)
                ((highBase a x : ℕ) : ℝ) (1 + lowEta c x) j).card : ℝ) *
              lowTheta A x) W) W w₀)
        ≤ ((menonInitialRangeSteps a c x hN : ℕ) : ℝ)
          * (2 * W / x
            + 2 * (1 + ((momentOrder a x : ℕ) : ℝ) * (Real.log 2 + Real.log x))
              * Real.exp (((momentOrder a x : ℕ) : ℝ)
                  * ((c + 2 * A + 3) * Real.log (Real.log x)))) := by
  have hll : Tendsto (fun x : ℝ => Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ),
    menonInitialRange_moment_bounds ha ha1 hc hA,
    two_le_highBase_and_le_expTop (a := a) (c := c) (β := (1 : ℝ)) ha hc,
    hll.eventually_ge_atTop (0 : ℝ)] with x hx hblock hlow2 hloglog
  intro hN W w₀ hQh hhx hW
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx
  have hη0 : (0 : ℝ) < lowEta c x := lowEta_pos hx
  have hθ0 : (0 : ℝ) < lowTheta A x := lowTheta_pos hx
  have hR2 : (2 : ℝ) ≤ ((highBase a x : ℕ) : ℝ) := by exact_mod_cast hlow2.1
  have hR0 : (0 : ℝ) < ((highBase a x : ℕ) : ℝ) := by linarith
  have hNA : ∀ j ∈ Finset.range (menonInitialRangeSteps a c x hN),
      1 ≤ ⌊((highBase a x : ℕ) : ℝ) * (1 + lowEta c x) ^ (j + 1)⌋₊ := by
    intro j _
    refine Nat.le_floor ?_
    have hpj : (1 : ℝ) ≤ (1 + lowEta c x) ^ (j + 1) :=
      one_le_pow₀ (by linarith)
    push_cast
    nlinarith [hR2, hpj]
  exact measureReal_annulusLarge_le_growing
    (P := menonInitialRangePrimes a c x hN)
    (R := ((highBase a x : ℕ) : ℝ)) (η := lowEta c x) (θ := lowTheta A x)
    (W := W) (w₀ := w₀) (nmax := Real.log 2 + Real.log x)
    (D := c + 2 * A + 3) (a₀ := a) (L := menonInitialRangeSteps a c x hN)
    (k := momentOrder a x)
    hR0 hη0.le (one_le_momentOrder hx) hW hθ0
    (by positivity) hx (by linarith) hloglog
    (fun p hp => ((mem_primesRange).1 hp).1)
    hNA (fun j hj => (hblock hN hQh hhx j hj).1) momentOrder_ge
    (fun j hj => (hblock hN hQh hhx j hj).2.1)
    (fun j hj => (hblock hN hQh hhx j hj).2.2.1)
    (fun j hj => (hblock hN hQh hhx j hj).2.2.2)

end

end RHTower.Sieve
