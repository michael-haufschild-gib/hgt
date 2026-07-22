import GaloisForLFunctions.RHTower.UniversalPhaseCoherenceAvoidance

/-!
# Universal minimax phase-coherence time

This file packages the two finite directions into one intrinsic clock.  The
upper bound is simultaneous recurrence.  The lower bound is Haar avoidance,
so it applies to the same worst-frequency minimax clock without probabilistic
or independence assumptions.
-/

open MeasureTheory Set
open scoped BigOperators

noncomputable section

namespace RHTower

/-- The explicit Haar upper bound for a `1 - η` coherence target in dimension
`d`. -/
def phaseCoherenceTargetBudget (d : ℕ) (η : ℝ) : ℝ :=
  (d : ℝ) * Real.exp ((d : ℝ) / 2) *
    Real.sqrt (Real.pi * η / 2) ^ (d - 1)

/-- The defect supplied by the quantitative simultaneous-recurrence theorem
at resolution `Q + 1`. -/
def recurrencePhaseDefect (Q : ℕ) : ℝ :=
  (2 * Real.pi / (Q + 1 : ℝ)) ^ 2 / 2

theorem phaseCoherenceTargetBudget_pos
    {d : ℕ} (hd : 0 < d) {η : ℝ} (hη : 0 < η) :
    0 < phaseCoherenceTargetBudget d η := by
  rw [phaseCoherenceTargetBudget]
  have hsqrt : 0 < Real.sqrt (Real.pi * η / 2) := by positivity
  positivity

theorem recurrencePhaseDefect_pos (Q : ℕ) :
    0 < recurrencePhaseDefect Q := by
  rw [recurrencePhaseDefect]
  positivity

/-- Universal deadlines are monotone in the allowed clock. -/
theorem IsUniversalPhaseCoherenceDeadline.mono
    {d N M : ℕ} {η : ℝ}
    (h : IsUniversalPhaseCoherenceDeadline d η N) (hNM : N ≤ M) :
    IsUniversalPhaseCoherenceDeadline d η M := by
  intro ω
  obtain ⟨n, hn0, hnN, hncoh⟩ := h ω
  exact ⟨n, hn0, hnN.trans hNM, hncoh⟩

/-- The least universal deadline at recurrence resolution `Q + 1`. -/
noncomputable def universalPhaseCoherenceTime
    (d Q : ℕ) (hd : 0 < d) : ℕ := by
  classical
  exact Nat.find (show ∃ N,
      IsUniversalPhaseCoherenceDeadline d (recurrencePhaseDefect Q) N from
    ⟨(Q + 1) ^ d,
      isUniversalPhaseCoherenceDeadline_recurrence hd le_rfl⟩)

theorem universalPhaseCoherenceTime_isDeadline
    (d Q : ℕ) (hd : 0 < d) :
    IsUniversalPhaseCoherenceDeadline d (recurrencePhaseDefect Q)
      (universalPhaseCoherenceTime d Q hd) := by
  classical
  unfold universalPhaseCoherenceTime
  exact Nat.find_spec _

/-- Quantitative recurrence gives the finite minimax ceiling. -/
theorem universalPhaseCoherenceTime_le
    (d Q : ℕ) (hd : 0 < d) :
    universalPhaseCoherenceTime d Q hd ≤ (Q + 1) ^ d := by
  classical
  unfold universalPhaseCoherenceTime
  exact Nat.find_min' _
    (isUniversalPhaseCoherenceDeadline_recurrence hd le_rfl)

theorem universalPhaseCoherenceTime_pos
    (d Q : ℕ) (hd : 0 < d) :
    0 < universalPhaseCoherenceTime d Q hd := by
  obtain ⟨n, hn0, hnT, _hncoh⟩ :=
    universalPhaseCoherenceTime_isDeadline d Q hd (fun _ ↦ 0)
  exact hn0.trans_le hnT

/-- Every integer whose Haar budget is below one lies strictly before the
universal minimax coherence time. -/
theorem lt_universalPhaseCoherenceTime_of_budget
    {d Q N : ℕ} (hd : 0 < d)
    (hbudget :
      (N : ℝ) * phaseCoherenceTargetBudget d (recurrencePhaseDefect Q) < 1) :
    N < universalPhaseCoherenceTime d Q hd := by
  have hnot : ¬ IsUniversalPhaseCoherenceDeadline d
      (recurrencePhaseDefect Q) N := by
    apply not_isUniversalPhaseCoherenceDeadline_of_budget hd
      (recurrencePhaseDefect_pos Q)
    simpa only [phaseCoherenceTargetBudget] using hbudget
  by_contra hNT
  push Not at hNT
  exact hnot ((universalPhaseCoherenceTime_isDeadline d Q hd).mono hNT)

/-- **Finite minimax entropy lower bound.**  The logarithm of the universal
coherence time dominates the negative logarithm of twice the Haar target
budget. -/
theorem neg_log_two_mul_phaseCoherenceTargetBudget_lt_log_time
    {d Q : ℕ} (hd : 0 < d) :
    -Real.log (2 * phaseCoherenceTargetBudget d (recurrencePhaseDefect Q)) <
      Real.log (universalPhaseCoherenceTime d Q hd : ℝ) := by
  let B : ℝ := phaseCoherenceTargetBudget d (recurrencePhaseDefect Q)
  have hB : 0 < B := phaseCoherenceTargetBudget_pos hd
    (recurrencePhaseDefect_pos Q)
  let N : ℕ := ⌊1 / (2 * B)⌋₊
  have hfloor : (N : ℝ) ≤ 1 / (2 * B) := by
    exact Nat.floor_le (by positivity)
  have hNB : (N : ℝ) * B < 1 := by
    have hhalf : (N : ℝ) * B ≤ 1 / 2 := by
      calc
        (N : ℝ) * B ≤ (1 / (2 * B)) * B :=
          mul_le_mul_of_nonneg_right hfloor hB.le
        _ = 1 / 2 := by field_simp [hB.ne']
    linarith
  have hNT : N < universalPhaseCoherenceTime d Q hd :=
    lt_universalPhaseCoherenceTime_of_budget hd (by
      simpa only [B] using hNB)
  have hreal : 1 / (2 * B) <
      (universalPhaseCoherenceTime d Q hd : ℝ) := by
    have hfloorlt : 1 / (2 * B) < (N : ℝ) + 1 := Nat.lt_floor_add_one _
    have hsucc : N + 1 ≤ universalPhaseCoherenceTime d Q hd := by omega
    exact hfloorlt.trans_le (by exact_mod_cast hsucc)
  have hleftmem : 1 / (2 * B) ∈ Set.Ioi (0 : ℝ) := by
    change 0 < 1 / (2 * B)
    positivity
  have hrightmem :
      (universalPhaseCoherenceTime d Q hd : ℝ) ∈ Set.Ioi (0 : ℝ) := by
    change 0 < (universalPhaseCoherenceTime d Q hd : ℝ)
    exact_mod_cast universalPhaseCoherenceTime_pos d Q hd
  have hlog := Real.strictMonoOn_log hleftmem hrightmem hreal
  rw [one_div, Real.log_inv] at hlog
  simpa only [B] using hlog

/-- **Universal finite entropy sandwich.**  At recurrence resolution `Q + 1`
the minimax clock lies between the reciprocal Haar target budget and the
simultaneous-recurrence ceiling. -/
theorem universalPhaseCoherenceTime_log_sandwich
    {d Q : ℕ} (hd : 0 < d) :
    -Real.log (2 * phaseCoherenceTargetBudget d (recurrencePhaseDefect Q)) <
        Real.log (universalPhaseCoherenceTime d Q hd : ℝ) ∧
      Real.log (universalPhaseCoherenceTime d Q hd : ℝ) ≤
        (d : ℝ) * Real.log (Q + 1 : ℝ) := by
  refine ⟨neg_log_two_mul_phaseCoherenceTargetBudget_lt_log_time hd, ?_⟩
  have hTpos : 0 < (universalPhaseCoherenceTime d Q hd : ℝ) := by
    exact_mod_cast universalPhaseCoherenceTime_pos d Q hd
  have hQpos : 0 < (((Q + 1) ^ d : ℕ) : ℝ) := by positivity
  have hlog := Real.strictMonoOn_log.monotoneOn hTpos hQpos
    (by exact_mod_cast universalPhaseCoherenceTime_le d Q hd)
  rw [show (((Q + 1) ^ d : ℕ) : ℝ) = (Q + 1 : ℝ) ^ d by norm_num,
    Real.log_pow] at hlog
  exact hlog

/-- The universal resolution constant converting the recurrence defect to a
one-circle chord scale. -/
def phaseCoherenceResolutionConstant : ℝ :=
  Real.sqrt (Real.pi ^ 3)

theorem phaseCoherenceResolutionConstant_pos :
    0 < phaseCoherenceResolutionConstant := by
  rw [phaseCoherenceResolutionConstant]
  positivity

theorem sqrt_recurrencePhaseDefect_scale (Q : ℕ) :
    Real.sqrt (Real.pi * recurrencePhaseDefect Q / 2) =
      phaseCoherenceResolutionConstant / (Q + 1 : ℝ) := by
  have hQ : 0 < (Q + 1 : ℝ) := by positivity
  have hinside :
      Real.pi * recurrencePhaseDefect Q / 2 =
        Real.pi ^ 3 / (Q + 1 : ℝ) ^ 2 := by
    rw [recurrencePhaseDefect]
    field_simp
  rw [hinside, Real.sqrt_div (by positivity), Real.sqrt_sq_eq_abs,
    abs_of_pos hQ]
  rfl

/-- Exact logarithmic expansion of the optimized target budget at recurrence
resolution.  This identity exposes the dimension--resolution term and every
lower-order entropy cost. -/
theorem neg_log_two_mul_phaseCoherenceTargetBudget_eq
    {d Q : ℕ} (hd : 0 < d) :
    -Real.log (2 * phaseCoherenceTargetBudget d (recurrencePhaseDefect Q)) =
      ((d - 1 : ℕ) : ℝ) * Real.log (Q + 1 : ℝ) -
        ((d - 1 : ℕ) : ℝ) * Real.log phaseCoherenceResolutionConstant -
          (d : ℝ) / 2 - Real.log (2 * (d : ℝ)) := by
  have hC : 0 < phaseCoherenceResolutionConstant :=
    phaseCoherenceResolutionConstant_pos
  have hQ : 0 < (Q + 1 : ℝ) := by positivity
  rw [phaseCoherenceTargetBudget, sqrt_recurrencePhaseDefect_scale]
  rw [show 2 * ((d : ℝ) * Real.exp ((d : ℝ) / 2) *
      (phaseCoherenceResolutionConstant / (Q + 1 : ℝ)) ^ (d - 1)) =
      (2 * (d : ℝ)) * Real.exp ((d : ℝ) / 2) *
        (phaseCoherenceResolutionConstant / (Q + 1 : ℝ)) ^ (d - 1) by ring]
  rw [Real.log_mul
      (mul_ne_zero (mul_ne_zero (by norm_num) (by positivity))
        (Real.exp_ne_zero _))
      (pow_ne_zero _ (div_ne_zero hC.ne' hQ.ne')),
    Real.log_mul (mul_ne_zero (by norm_num) (by positivity))
      (Real.exp_ne_zero _),
    Real.log_exp, Real.log_pow, Real.log_div hC.ne' hQ.ne']
  ring

/-- **Dimension--resolution law.**  The minimax logarithmic time is trapped
between an explicit `(d - 1)`-dimensional Haar entropy and the exact
`d`-dimensional recurrence ceiling.  In particular the leading resolution
coefficient is one, equivalently one half when parametrized by the quadratic
coherence defect. -/
theorem universalPhaseCoherence_dimensionResolution_sandwich
    {d Q : ℕ} (hd : 0 < d) :
    ((d - 1 : ℕ) : ℝ) * Real.log (Q + 1 : ℝ) -
        ((d - 1 : ℕ) : ℝ) * Real.log phaseCoherenceResolutionConstant -
          (d : ℝ) / 2 - Real.log (2 * (d : ℝ)) <
        Real.log (universalPhaseCoherenceTime d Q hd : ℝ) ∧
      Real.log (universalPhaseCoherenceTime d Q hd : ℝ) ≤
        (d : ℝ) * Real.log (Q + 1 : ℝ) := by
  rw [← neg_log_two_mul_phaseCoherenceTargetBudget_eq hd]
  exact universalPhaseCoherenceTime_log_sandwich hd

/-- Dimension-independent remainder in the normalized entropy law. -/
def phaseCoherenceEntropyRemainder : ℝ :=
  |Real.log phaseCoherenceResolutionConstant| +
    1 / 2 + Real.log 2 + 1

theorem log_two_mul_natCast_le
    {d : ℕ} (hd : 0 < d) :
    Real.log (2 * (d : ℝ)) ≤ (d : ℝ) * (Real.log 2 + 1) := by
  have hD : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hlogD := Real.log_le_sub_one_of_pos
    (show 0 < (d : ℝ) by positivity)
  have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  rw [Real.log_mul (by norm_num) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.mpr hD) hlog2]

/-- **Normalized universal entropy law.**  The exact minimax clock has
dimension--resolution ratio at most one and within
`1/d + phaseCoherenceEntropyRemainder / log(Q+1)` of one from below.  Thus the
coefficient tends to one as dimension and resolution diverge, equivalently to
one half when resolution is expressed by the quadratic coherence defect. -/
theorem universalPhaseCoherence_normalized_entropy_sandwich
    {d Q : ℕ} (hd : 0 < d) (hQ : 0 < Q) :
    1 - 1 / (d : ℝ) -
        phaseCoherenceEntropyRemainder / Real.log (Q + 1 : ℝ) <
        Real.log (universalPhaseCoherenceTime d Q hd : ℝ) /
          ((d : ℝ) * Real.log (Q + 1 : ℝ)) ∧
      Real.log (universalPhaseCoherenceTime d Q hd : ℝ) /
          ((d : ℝ) * Real.log (Q + 1 : ℝ)) ≤ 1 := by
  let D : ℝ := d
  let a : ℝ := Real.log (Q + 1 : ℝ)
  let c : ℝ := Real.log phaseCoherenceResolutionConstant
  have hD : 0 < D := by dsimp only [D]; positivity
  have ha : 0 < a := by
    dsimp only [a]
    exact Real.log_pos (by exact_mod_cast (show 1 < Q + 1 by omega))
  have hpred : ((d - 1 : ℕ) : ℝ) = D - 1 := by
    dsimp only [D]
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    norm_num
  have hlog2D : Real.log (2 * D) ≤ D * (Real.log 2 + 1) := by
    simpa only [D] using log_two_mul_natCast_le hd
  have hcweight : (D - 1) * c ≤ D * |c| := by
    calc
      (D - 1) * c ≤ (D - 1) * |c| := by
        exact mul_le_mul_of_nonneg_left (le_abs_self c) (by linarith)
      _ ≤ D * |c| := by
        exact mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg c)
  have hcost :
      (D - 1) * c + D / 2 + Real.log (2 * D) ≤
        D * phaseCoherenceEntropyRemainder := by
    dsimp only [phaseCoherenceEntropyRemainder]
    nlinarith
  obtain ⟨hlow, hupp⟩ :=
    universalPhaseCoherence_dimensionResolution_sandwich (Q := Q) hd
  rw [hpred] at hlow
  change (D - 1) * a - (D - 1) * c - D / 2 - Real.log (2 * D) <
    Real.log (universalPhaseCoherenceTime d Q hd : ℝ) at hlow
  have hnum : D * a *
      (1 - 1 / D - phaseCoherenceEntropyRemainder / a) <
      Real.log (universalPhaseCoherenceTime d Q hd : ℝ) := by
    have heq : D * a *
        (1 - 1 / D - phaseCoherenceEntropyRemainder / a) =
        (D - 1) * a - D * phaseCoherenceEntropyRemainder := by
      field_simp [hD.ne', ha.ne']
    rw [heq]
    exact lt_of_le_of_lt (by linarith [hcost]) hlow
  constructor
  · change 1 - 1 / D - phaseCoherenceEntropyRemainder / a <
      Real.log (universalPhaseCoherenceTime d Q hd : ℝ) / (D * a)
    apply (lt_div_iff₀ (mul_pos hD ha)).2
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hnum
  · change Real.log (universalPhaseCoherenceTime d Q hd : ℝ) / (D * a) ≤ 1
    apply (div_le_iff₀ (mul_pos hD ha)).2
    simpa only [one_mul, D, a] using hupp

end RHTower
