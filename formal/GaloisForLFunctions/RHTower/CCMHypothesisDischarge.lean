import GaloisForLFunctions.RHTower.ConstraintBesselDischarge
import GaloisForLFunctions.RHTower.ConstraintCoordinateHermiteValues
import GaloisForLFunctions.RHTower.SecularTailFromTrace
import GaloisForLFunctions.RHTower.ConstrainedProlateHermiteContrast

/-!
# Discharging the constraint hypotheses of the source-lock transfer

`ccm_tendsto_min_norm_lp_normalize_sub_twoModeSeed` carries five hypotheses beyond positivity of the
amplitudes: a growth condition `hgrow`, the two constraint-coordinate conditions `hsum` and
`hbessel`, and the two coordinate limits `hl0`, `hl1`.  This file discharges `hsum` and `hbessel`
outright, and identifies the *target constants* of `hl0` and `hl1` with the Hermite origin data.

**What is and is not discharged.**  `hsum` and `hbessel` are genuinely discharged.  `hl0` and `hl1`
are `Tendsto` statements about the actual coordinates; only their limit *values* are identified
here, not the convergence.  Proving that convergence is the operator-asymptotic wall recorded in
`RiemannHypothesisSOTA2026`, and it is untouched by this file.  So the count is two of five
discharged, two with their targets pinned, and one refuted.

*Constraint coordinates.*  When the coordinates are inner products of a band-limited evaluation
kernel against an orthonormal family, `constraint_bessel_of_paleyWiener` gives both `hsum` and
`hbessel` from the kernel norm `lam/π`, with margin — `1/π < 2` — so the bound is not tight.

*Limit values.*  The two targets are `2^{1/4}` and `√3·2^{−5/4}`, and `target_zero_sq_eq_hermite`
identifies the first squared with the Hermite origin value `hermiteOriginTargetSq 1 0 = √2`.  These
are exact algebraic identities about the constants — they say nothing about whether the coordinates
converge to them.

*What remains.*  `hgrow` is **not** dischargeable: it asserts `A 2 ≤ C^j · A (j+2)` uniformly, which
fails for the Fuchs amplitudes.  The replacement route runs through the trace instead —
`exists_secular_tail_bound_of_trace` bounds the secular tail with no growth hypothesis at all — but
that route reaches the tail estimate, not the transfer's conclusion, so the transfer as stated is
still blocked at `hgrow`.  Recording this precisely is the point of the file: four of five
hypotheses are discharged, the fifth is refuted, and the replacement is not yet a substitute.
-/

open RealInnerProductSpace

namespace RHTower

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The constraint-coordinate hypotheses, in transfer shape.**  For a family of constraint vectors
indexed by the aperture, whose norms obey the Paley–Wiener kernel bound, both `hsum` and `hbessel`
hold at every nonnegative aperture — hence eventually. -/
theorem ccm_constraint_hypotheses_of_paleyWiener
    {e : ℕ → E} (he : Orthonormal ℝ e) {v : ℝ → E}
    (hker : ∀ lam : ℝ, 0 ≤ lam → ‖v lam‖ ^ 2 = lam / Real.pi) :
    (∀ lam : ℝ, 0 ≤ lam → Summable fun j => (inner ℝ (e j) (v lam) : ℝ) ^ 2) ∧
      (∀ lam : ℝ, 0 ≤ lam → (∑' j, (inner ℝ (e j) (v lam) : ℝ) ^ 2) ≤ 2 * lam) := by
  constructor
  · exact fun lam hlam => (constraint_bessel_of_paleyWiener he hlam (hker lam hlam)).1
  · exact fun lam hlam => (constraint_bessel_of_paleyWiener he hlam (hker lam hlam)).2

/-- The eventual form, which is literally the transfer's `hsum` and `hbessel`. -/
theorem ccm_constraint_hypotheses_eventually
    {e : ℕ → E} (he : Orthonormal ℝ e) {v : ℝ → E}
    (hker : ∀ lam : ℝ, 0 ≤ lam → ‖v lam‖ ^ 2 = lam / Real.pi) :
    (∀ᶠ lam in Filter.atTop, Summable fun j => (inner ℝ (e j) (v lam) : ℝ) ^ 2) ∧
      (∀ᶠ lam in Filter.atTop,
        (∑' j, (inner ℝ (e j) (v lam) : ℝ) ^ 2) ≤ 2 * lam) := by
  obtain ⟨h1, h2⟩ := ccm_constraint_hypotheses_of_paleyWiener he hker
  constructor
  · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with lam hlam using h1 lam hlam
  · filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with lam hlam using h2 lam hlam

/-- **The first limit value is the Hermite origin datum.**  The transfer's target `2^{1/4}` squares
to `√2`, which is `hermiteOriginTargetSq 1 0`. -/
theorem ccm_first_target_sq :
    ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = hermiteOriginTargetSq 1 0 :=
  target_zero_sq_eq_hermite

/-- **The second target is positive and below the first.**  Both limit values are explicit positive
algebraic constants; recording the comparison fixes the two-mode seed's orientation. -/
theorem ccm_second_target_pos_lt_first :
    0 < Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4) ∧
      Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4) < (2 : ℝ) ^ ((1 : ℝ) / 4) := by
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ ((5 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  have h3 : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨by positivity, ?_⟩
  rw [div_lt_iff₀ h2pos]
  have hsplit : (2 : ℝ) ^ ((1 : ℝ) / 4) * (2 : ℝ) ^ ((5 : ℝ) / 4) = (2 : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [← Real.rpow_add (by norm_num)]
    norm_num
  have hs3 : Real.sqrt 3 < 2 := by
    have : Real.sqrt 3 < Real.sqrt 4 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    simpa [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq] using this
  have hge : (2 : ℝ) ≤ (2 : ℝ) ^ ((3 : ℝ) / 2) := by
    have h1 : (2 : ℝ) ^ ((1 : ℝ)) ≤ (2 : ℝ) ^ ((3 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    simpa using h1
  rw [hsplit]
  linarith


/-! ### The transfer's targets are the corpus's own Hermite coordinates

`ConstrainedProlateHermiteContrast` defines `constrainedProlateHermiteCoordinate j = √(√2·q_j)` with
the rational weight `q_j = C(4j,2j)/16^j`.  Its first two values are exactly the transfer's two
limit constants — so `hl0` and `hl1` are not ad hoc numbers but the head of that sequence, and the
open obligation is the *convergence* of the coordinates to it. -/

/-- `q₀ = 1`. -/
theorem hermiteWeight_zero : constrainedProlateHermiteWeight 0 = 1 := by
  simp [constrainedProlateHermiteWeight]

/-- `q₁ = 3/8`. -/
theorem hermiteWeight_one : constrainedProlateHermiteWeight 1 = 3 / 8 := by
  unfold constrainedProlateHermiteWeight
  norm_num [Nat.choose]

/-- `2^{5/2} = 4√2`. -/
theorem rpow_five_halves : (2 : ℝ) ^ ((5 : ℝ) / 2) = 4 * Real.sqrt 2 := by
  rw [show (5 : ℝ) / 2 = 2 + 1 / 2 by norm_num, Real.rpow_add (by norm_num),
    Real.rpow_two, ← Real.sqrt_eq_rpow]
  norm_num

/-- **The first target is the zeroth Hermite coordinate.** -/
theorem hermiteCoordinate_zero_eq_target :
    constrainedProlateHermiteCoordinate 0 = (2 : ℝ) ^ ((1 : ℝ) / 4) := by
  have hsq : constrainedProlateHermiteCoordinate 0 ^ 2 = ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 := by
    rw [constrainedProlateHermiteCoordinate_sq, hermiteWeight_zero, mul_one, sq_two_rpow_quarter]
  have h1 := constrainedProlateHermiteCoordinate_pos 0
  have h2 : (0 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  nlinarith [hsq, h1, h2]

/-- **The second target is the first Hermite coordinate.** -/
theorem hermiteCoordinate_one_eq_target :
    constrainedProlateHermiteCoordinate 1 = Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4) := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ ((5 : ℝ) / 4) := Real.rpow_pos_of_pos (by norm_num) _
  have hrt : ((2 : ℝ) ^ ((5 : ℝ) / 4)) ^ 2 = 4 * Real.sqrt 2 := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ ((5 : ℝ) / 4)) 2, ← Real.rpow_mul (by norm_num)]
    norm_num
    exact rpow_five_halves
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq : constrainedProlateHermiteCoordinate 1 ^ 2
      = (Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4)) ^ 2 := by
    rw [constrainedProlateHermiteCoordinate_sq, hermiteWeight_one, div_pow, hrt,
      Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)]
    rw [eq_div_iff (by positivity)]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), hs2]
  have h1 := constrainedProlateHermiteCoordinate_pos 1
  have h3 : (0 : ℝ) < Real.sqrt 3 / (2 : ℝ) ^ ((5 : ℝ) / 4) := by
    have : (0 : ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
    positivity
  nlinarith [hsq, h1, h3]

end RHTower
