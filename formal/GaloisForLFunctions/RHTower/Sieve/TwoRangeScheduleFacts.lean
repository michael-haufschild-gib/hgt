import GaloisForLFunctions.RHTower.Sieve.TwoRangeSchedule
import GaloisForLFunctions.RHTower.Sieve.GeomBlockPrimesRange
import GaloisForLFunctions.RHTower.Sieve.PolyDecayLimits

/-!
# The structural facts of the two-range schedule

The hypotheses of `Sieve/MoebiusTwoRangeWindow.integral_Icc_normSq_logPoly_moebius_le_twoRange`
that do not involve the analytic layers — that each designated range is covered by its ladder, that
the low range stays below the window length, that the Gallagher cutoff exceeds one — are collected
here.  Everything is elementary; only the two prime ranges and the two ladders enter.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The top of the low ladder. -/
def lowTop (K c β x : ℝ) : ℕ :=
  ⌊((lowBase K x : ℕ) : ℝ) * (1 + lowEta c x) ^ (lowSteps K c β x)⌋₊

/-- The top of the high ladder. -/
def highTop (a b c' x : ℝ) : ℕ :=
  ⌊((highBase a x : ℕ) : ℝ) * (1 + highEta c' x) ^ (highSteps a b c' x)⌋₊

/-- **The designated primes of a ladder lie in the ladder's range.** -/
theorem primesRange_ladder_bounds_self {z₀ z L : ℕ} {Q η : ℝ} (hQ : Q = (z₀ : ℝ)) (hη : 0 ≤ η)
    (hQ0 : 0 ≤ Q) (hz : z = ⌊Q * (1 + η) ^ L⌋₊) :
    ∀ p ∈ primesRange z₀ z, Q < (p : ℝ) ∧ (p : ℝ) ≤ Q * (1 + η) ^ L := by
  intro p hp
  rw [mem_primesRange] at hp
  obtain ⟨-, hlo, hhi⟩ := hp
  refine ⟨by rw [hQ]; exact_mod_cast hlo, ?_⟩
  have hle : (p : ℝ) ≤ ((⌊Q * (1 + η) ^ L⌋₊ : ℕ) : ℝ) := by
    rw [← hz]
    exact_mod_cast hhi
  refine hle.trans (Nat.floor_le ?_)
  positivity

/-- The low range is covered by the low ladder. -/
theorem lowRange_bounds {K c β x : ℝ} (hx : 1 < x) :
    ∀ p ∈ primesRange (lowBase K x) (lowTop K c β x),
      ((lowBase K x : ℕ) : ℝ) < (p : ℝ)
        ∧ (p : ℝ) ≤ ((lowBase K x : ℕ) : ℝ) * (1 + lowEta c x) ^ (lowSteps K c β x) :=
  primesRange_ladder_bounds_self rfl (lowEta_pos hx).le (Nat.cast_nonneg _) rfl

/-- The high range is covered by the high ladder. -/
theorem highRange_bounds {a b c' x : ℝ} (hx : 1 < x) :
    ∀ p ∈ primesRange (highBase a x) (highTop a b c' x),
      ((highBase a x : ℕ) : ℝ) < (p : ℝ)
        ∧ (p : ℝ) ≤ ((highBase a x : ℕ) : ℝ) * (1 + highEta c' x) ^ (highSteps a b c' x) :=
  primesRange_ladder_bounds_self rfl (highEta_pos hx).le (Nat.cast_nonneg _) rfl

/-- **The polylogarithmic bottom is far below the window length.** -/
theorem lowBase_lt_cardLength {K β : ℝ} (hK : 0 ≤ K) (hβ : 0 < β) :
    ∀ᶠ x : ℝ in atTop, ((lowBase K x : ℕ) : ℝ) < cardLength β x := by
  have hlim := tendsto_rpow_log_div_cardLength (β := β) hβ (c := K)
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 1), Filter.eventually_gt_atTop (1 : ℝ),
    Tendsto.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2) hlim] with x hxe hx1 hsmall
  have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
  have hbd := (lowBase_bounds hK hxe).2
  have hkey : (Real.log x) ^ K < cardLength β x / 2 := by
    rw [div_lt_iff₀ hh0] at hsmall
    linarith [hsmall]
  have hone : (1 : ℝ) ≤ cardLength β x / 2 := by
    have hlogx : (0 : ℝ) < Real.log x := Real.log_pos hx1
    have hpow : (1 : ℝ) ≤ (Real.log x) ^ K := by
      refine Real.one_le_rpow ?_ hK
      have := Real.log_le_log (Real.exp_pos 1) hxe
      rwa [Real.log_exp] at this
    linarith
  linarith

/-- **The low ladder does not overshoot the window length.** -/
theorem lowTop_le_cardLength {K c β : ℝ} (hK : 0 ≤ K) (hc : 0 < c) (hβ : 0 < β) :
    ∀ᶠ x : ℝ in atTop,
      ((lowBase K x : ℕ) : ℝ) * (1 + lowEta c x) ^ (lowSteps K c β x) ≤ cardLength β x := by
  have hzero := tendsto_lowEta (c := c) hc
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 1), Filter.eventually_gt_atTop (1 : ℝ),
    Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1) hzero,
    lowBase_lt_cardLength (K := K) (β := β) hK hβ] with x hxe hx1 hη1 hlt
  have hη : 0 < lowEta c x := lowEta_pos hx1
  have hQ1 : (1 : ℝ) ≤ ((lowBase K x : ℕ) : ℝ) := by
    have := one_le_lowBase hK hxe
    exact_mod_cast this
  have hQ0 : (0 : ℝ) < ((lowBase K x : ℕ) : ℝ) := by linarith
  have hh0 : (0 : ℝ) < cardLength β x := cardLength_pos β x
  have hr1 : (1 : ℝ) < 1 + lowEta c x := by linarith
  have hlogr : (0 : ℝ) < Real.log (1 + lowEta c x) := Real.log_pos hr1
  have hcase : ((lowBase K x : ℕ) : ℝ) < cardLength β x := hlt
  have hratio1 : (1 : ℝ) ≤ cardLength β x / ((lowBase K x : ℕ) : ℝ) := by
    rw [le_div_iff₀ hQ0, one_mul]
    exact hcase.le
  have hlognn : (0 : ℝ) ≤ Real.log (cardLength β x / ((lowBase K x : ℕ) : ℝ)) :=
    Real.log_nonneg hratio1
  have hfl : ((lowSteps K c β x : ℕ) : ℝ) * Real.log (1 + lowEta c x)
      ≤ Real.log (cardLength β x / ((lowBase K x : ℕ) : ℝ)) := by
    have hle : ((lowSteps K c β x : ℕ) : ℝ)
        ≤ Real.log (cardLength β x / ((lowBase K x : ℕ) : ℝ)) / Real.log (1 + lowEta c x) := by
      rw [lowSteps]
      exact Nat.floor_le (div_nonneg hlognn hlogr.le)
    have := mul_le_mul_of_nonneg_right hle hlogr.le
    rw [div_mul_cancel₀ _ (ne_of_gt hlogr)] at this
    exact this
  have hpow : (1 + lowEta c x) ^ (lowSteps K c β x)
      ≤ cardLength β x / ((lowBase K x : ℕ) : ℝ) := by
    have hlogpow : Real.log ((1 + lowEta c x) ^ (lowSteps K c β x))
        = ((lowSteps K c β x : ℕ) : ℝ) * Real.log (1 + lowEta c x) := by
      rw [Real.log_pow]
    have hpos : (0 : ℝ) < (1 + lowEta c x) ^ (lowSteps K c β x) := by positivity
    have hposr : (0 : ℝ) < cardLength β x / ((lowBase K x : ℕ) : ℝ) := by positivity
    have := Real.log_le_log_iff hpos hposr
    rw [← this, hlogpow]
    exact hfl
  calc ((lowBase K x : ℕ) : ℝ) * (1 + lowEta c x) ^ (lowSteps K c β x)
      ≤ ((lowBase K x : ℕ) : ℝ) * (cardLength β x / ((lowBase K x : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_left hpow hQ0.le
    _ = cardLength β x := by field_simp

end

end RHTower.Sieve
