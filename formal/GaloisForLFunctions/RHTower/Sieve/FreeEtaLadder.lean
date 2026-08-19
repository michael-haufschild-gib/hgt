import GaloisForLFunctions.RHTower.Sieve.SpectralParameters

/-!
# A geometric ladder at a free ratio

`Sieve/SpectralParameters.{ladderSteps, ladderTop}` bake in the ratio `ladderEta β γ x`, whose
exponent `γβ − β − 5/4` is pinned to the pair of exponents defining the range.  The long designated
range of the §4 arrangement needs a *smaller* ratio than that: its own defect forces
`η ≤ (log x)^{a−b−1−β/2}`, and `a − b − 5/4` meets that only for `β ≤ 1/2`.

This module carries the same three facts at a free ratio.  Every proof is the corpus's, with `η`
loose: only `0 < η` and `Q ≤ top` are used.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The number of steps of a ladder from `Q` to `top` at ratio `1 + η`. -/
def gLadderSteps (Q η top : ℝ) : ℕ := ⌊Real.log (top / Q) / Real.log (1 + η)⌋₊

/-- The top of that ladder, rounded down. -/
def gLadderTop (Q η top : ℝ) : ℕ := ⌊Q * (1 + η) ^ (gLadderSteps Q η top)⌋₊

/-- **The ladder does not overshoot.** -/
theorem gLadderPow_le {Q η top : ℝ} (hQ0 : 0 < Q) (hQtop : Q ≤ top) (hη : 0 < η) :
    Q * (1 + η) ^ (gLadderSteps Q η top) ≤ top := by
  have hr : (1 : ℝ) < 1 + η := by linarith
  have hlogr : (0 : ℝ) < Real.log (1 + η) := Real.log_pos hr
  have hratio : (1 : ℝ) ≤ top / Q := (one_le_div hQ0).2 hQtop
  have hlogratio : (0 : ℝ) ≤ Real.log (top / Q) := Real.log_nonneg hratio
  have htop0 : (0 : ℝ) < top := lt_of_lt_of_le hQ0 hQtop
  have hfl : ((gLadderSteps Q η top : ℕ) : ℝ) ≤ Real.log (top / Q) / Real.log (1 + η) := by
    rw [gLadderSteps]
    exact Nat.floor_le (div_nonneg hlogratio hlogr.le)
  have hmul : ((gLadderSteps Q η top : ℕ) : ℝ) * Real.log (1 + η) ≤ Real.log (top / Q) :=
    (le_div_iff₀ hlogr).1 hfl
  have hlogpow : Real.log ((1 + η) ^ (gLadderSteps Q η top))
      = ((gLadderSteps Q η top : ℕ) : ℝ) * Real.log (1 + η) := Real.log_pow _ _
  have hpow0 : (0 : ℝ) < (1 + η) ^ (gLadderSteps Q η top) := by positivity
  have hle : (1 + η) ^ (gLadderSteps Q η top) ≤ top / Q := by
    have h := Real.log_le_log_iff hpow0 (by positivity : (0 : ℝ) < top / Q)
    rw [← h, hlogpow]
    exact hmul
  rw [le_div_iff₀ hQ0] at hle
  linarith [hle]

/-- **The ladder reaches within one step of the top.** -/
theorem gLadderPow_ge {Q η top : ℝ} (hQ0 : 0 < Q) (hQtop : Q ≤ top) (hη : 0 < η) :
    top / (1 + η) ≤ Q * (1 + η) ^ (gLadderSteps Q η top) := by
  have hr : (1 : ℝ) < 1 + η := by linarith
  have hlogr : (0 : ℝ) < Real.log (1 + η) := Real.log_pos hr
  have hratio : (1 : ℝ) ≤ top / Q := (one_le_div hQ0).2 hQtop
  have hlogratio : (0 : ℝ) ≤ Real.log (top / Q) := Real.log_nonneg hratio
  have htop0 : (0 : ℝ) < top := lt_of_lt_of_le hQ0 hQtop
  have hfl : Real.log (top / Q) / Real.log (1 + η) < ((gLadderSteps Q η top : ℕ) : ℝ) + 1 := by
    rw [gLadderSteps]
    exact Nat.lt_floor_add_one _
  have hmul : Real.log (top / Q)
      < (((gLadderSteps Q η top : ℕ) : ℝ) + 1) * Real.log (1 + η) := by
    rw [div_lt_iff₀ hlogr] at hfl
    exact hfl
  have hlogpow : Real.log ((1 + η) ^ (gLadderSteps Q η top + 1))
      = (((gLadderSteps Q η top : ℕ) : ℝ) + 1) * Real.log (1 + η) := by
    rw [Real.log_pow]
    push_cast
    ring
  have hpow0 : (0 : ℝ) < (1 + η) ^ (gLadderSteps Q η top + 1) := by positivity
  have hlt : top / Q < (1 + η) ^ (gLadderSteps Q η top + 1) := by
    refine (Real.log_lt_log_iff (by positivity : (0 : ℝ) < top / Q) hpow0).1 ?_
    rw [hlogpow]
    exact hmul
  rw [div_lt_iff₀ hQ0] at hlt
  have hexp : (1 + η) ^ (gLadderSteps Q η top + 1)
      = (1 + η) ^ (gLadderSteps Q η top) * (1 + η) := by rw [pow_succ]
  rw [hexp] at hlt
  rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 + η)]
  linarith [hlt]

/-- **The ladder's top, two-sidedly.** -/
theorem gLadderTop_bounds {Q η top : ℝ} (hQ0 : 0 < Q) (hQtop : Q ≤ top) (hη : 0 < η) :
    ((gLadderTop Q η top : ℕ) : ℝ) ≤ top
      ∧ top / (1 + η) - 1 ≤ ((gLadderTop Q η top : ℕ) : ℝ) := by
  have hpow0 : (0 : ℝ) < Q * (1 + η) ^ (gLadderSteps Q η top) := by positivity
  constructor
  · exact le_trans (Nat.floor_le hpow0.le) (gLadderPow_le hQ0 hQtop hη)
  · have hfl := Nat.lt_floor_add_one (Q * (1 + η) ^ (gLadderSteps Q η top))
    have hge := gLadderPow_ge hQ0 hQtop hη
    rw [gLadderTop]
    linarith [hfl, hge]

/-- **The harmonic mass of a range, from Mertens' second theorem.** -/
theorem gLadderMass_ge {A B : ℕ} (ha : 2 ≤ A) (hb : 2 ≤ B) :
    Real.log (Real.log (A : ℝ)) - Real.log (Real.log (B : ℝ)) + ladderMassConst
      ≤ mertensS A - mertensS B := by
  have h1 := logLog_sub_le_mertensS ha
  have h2 := mertensS_le_logLog_add hb
  rw [logLog] at h1
  rw [logLog] at h2
  rw [ladderMassConst]
  linarith [h1, h2]

end

end RHTower.Sieve
