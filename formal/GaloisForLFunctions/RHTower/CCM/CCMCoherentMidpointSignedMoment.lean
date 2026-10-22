import GaloisForLFunctions.RHTower.CCM.CCMCoherentMidpointSpectralCurrent

/-!
# Cancellation-preserving moment control of the midpoint current

The first frequency moment stays signed. Only the cubic sine remainder is
bounded absolutely. Consequently the signed current has an exact quadratic
principal term and a globally valid quartic error bound, including the terminal
cell. No uniform bound on the arithmetic moments is assumed.
-/

noncomputable section
open scoped BigOperators

namespace RHTower

/-- The signed first frequency moment of the full arithmetic packet. -/
def ccmActualHeadMidpointSignedMoment (T : ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  (∑ n ∈ Finset.range N, ccmOutgoingQuantileDisplacementCellDensity n r *
    (2*Real.pi*(Real.log n+r/2))) +
  ccmActualHeadQuantileTerminalDisplacementDensity T N r * (2*Real.pi*(T+r/2))

/-- The absolute third frequency moment controls only the error after signed cancellation. -/
def ccmActualHeadMidpointCubicMoment (T : ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  (∑ n ∈ Finset.range N, |ccmOutgoingQuantileDisplacementCellDensity n r| *
    |2*Real.pi*(Real.log n+r/2)|^3) +
  |ccmActualHeadQuantileTerminalDisplacementDensity T N r| * |2*Real.pi*(T+r/2)|^3

theorem ccmActualHeadMidpointCubicMoment_nonneg (T : ℝ) (N : ℕ) (r : ℝ) :
    0 ≤ ccmActualHeadMidpointCubicMoment T N r := by
  unfold ccmActualHeadMidpointCubicMoment
  positivity

private theorem packet_cubic_error {ι : Type*} (I : Finset ι) (c β : ι → ℝ) (ξ : ℝ) :
    |(∑ i ∈ I, c i * Real.sin (β i*ξ)) - ξ*(∑ i ∈ I, c i*β i)| ≤
      |ξ|^3/6 * (∑ i ∈ I, |c i| * |β i|^3) := by
  have he : (∑ i ∈ I, c i * Real.sin (β i*ξ)) - ξ*(∑ i ∈ I, c i*β i) =
      ∑ i ∈ I, c i*(Real.sin (β i*ξ)-β i*ξ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  have h := mul_le_mul_of_nonneg_left (Real.abs_sub_sin_le (β i*ξ)) (abs_nonneg (c i))
  rw [abs_sub_comm (β i*ξ), abs_mul, mul_pow] at h
  convert h using 1; ring

/-- Global cubic error after retaining the literal signed first moment. -/
theorem abs_ccmActualHeadMidpointSineSymbol_sub_moment_le (T : ℝ) (N : ℕ) (r ξ : ℝ) :
    |ccmActualHeadMidpointSineSymbol T N r ξ - ξ*ccmActualHeadMidpointSignedMoment T N r| ≤
      |ξ|^3/6 * ccmActualHeadMidpointCubicMoment T N r := by
  have h := packet_cubic_error (Finset.range N).insertNone
    (fun o : Option ℕ => o.elim (ccmActualHeadQuantileTerminalDisplacementDensity T N r)
      (fun n => ccmOutgoingQuantileDisplacementCellDensity n r))
    (fun o : Option ℕ => o.elim (2*Real.pi*(T+r/2))
      (fun n => 2*Real.pi*(Real.log n+r/2))) ξ
  simpa only [Finset.sum_insertNone, Option.elim, add_comm,
    ccmActualHeadMidpointSineSymbol, ccmActualHeadMidpointSignedMoment,
    ccmActualHeadMidpointCubicMoment] using h

/-- Explicit coefficient of the quartic current error. -/
def ccmActualHeadMidpointQuarticBudget (T : ℝ) (N : ℕ) (r : ℝ) : ℝ :=
  (|Real.pi*r| * ccmActualHeadMidpointCubicMoment T N r +
    |Real.pi*r|^3*|ccmActualHeadMidpointSignedMoment T N r|)/3

theorem ccmActualHeadMidpointQuarticBudget_nonneg (T : ℝ) (N : ℕ) (r : ℝ) :
    0 ≤ ccmActualHeadMidpointQuarticBudget T N r := by
  have h := ccmActualHeadMidpointCubicMoment_nonneg T N r
  unfold ccmActualHeadMidpointQuarticBudget
  positivity

/-- The signed current is its quadratic signed-moment term plus a quartic error.
This estimate is valid for every real frequency, not only asymptotically. -/
theorem abs_ccmActualHeadMidpointCurrentSymbol_add_quadratic_le
    (T : ℝ) (N : ℕ) (r ξ : ℝ) :
    |ccmActualHeadMidpointCurrentSymbol T N r ξ +
      2*(Real.pi*r)*ccmActualHeadMidpointSignedMoment T N r*ξ^2| ≤
        ccmActualHeadMidpointQuarticBudget T N r * ξ^4 := by
  let a := Real.pi*r
  let S := ccmActualHeadMidpointSineSymbol T N r ξ
  let M := ccmActualHeadMidpointSignedMoment T N r
  let B := ccmActualHeadMidpointCubicMoment T N r
  have hB : 0 ≤ B := ccmActualHeadMidpointCubicMoment_nonneg T N r
  have hS : |S-ξ*M| ≤ |ξ|^3/6*B := abs_ccmActualHeadMidpointSineSymbol_sub_moment_le T N r ξ
  have hs : |Real.sin (a*ξ)| ≤ |a| * |ξ| := by
    simpa only [abs_mul] using (Real.abs_sin_le_abs (x := a*ξ))
  have he : |Real.sin (a*ξ)-a*ξ| ≤ |a|^3*|ξ|^3/6 := by
    simpa only [abs_sub_comm, abs_mul, mul_pow] using Real.abs_sub_sin_le (a*ξ)
  change |-2*Real.sin (a*ξ)*S + 2*a*M*ξ^2| ≤ ((|a| * B+|a|^3*|M|)/3)*ξ^4
  have hid : -2*Real.sin (a*ξ)*S + 2*a*M*ξ^2 =
      -2*Real.sin (a*ξ)*(S-ξ*M) - 2*ξ*M*(Real.sin (a*ξ)-a*ξ) := by ring
  rw [hid]
  calc
    _ ≤ |-2*Real.sin (a*ξ)*(S-ξ*M)| + |2*ξ*M*(Real.sin (a*ξ)-a*ξ)| := abs_sub _ _
    _ = 2*|Real.sin (a*ξ)| * |S-ξ*M| + 2*|ξ| * |M| * |Real.sin (a*ξ)-a*ξ| := by
      simp only [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    _ ≤ 2*(|a| * |ξ|)*(|ξ|^3/6*B) + 2*|ξ| * |M| * (|a|^3*|ξ|^3/6) := by
      apply add_le_add
      · exact mul_le_mul (mul_le_mul_of_nonneg_left hs (by positivity)) hS
          (abs_nonneg _) (by positivity)
      · exact mul_le_mul_of_nonneg_left he (by positivity)
    _ = ((|a| * B+|a|^3*|M|)/3)*ξ^4 := by
      have hpow : |ξ|^4 = ξ^4 := by
        rw [show (4 : ℕ) = 2*2 by norm_num, pow_mul, sq_abs, pow_mul]
      calc
        _ = ((|a| * B+|a|^3*|M|)/3)*|ξ|^4 := by ring
        _ = _ := by rw [hpow]

/-- A signed lower bound preserves the actual quadratic coefficient. -/
theorem ccmActualHeadMidpointCurrentSymbol_lower_bound (T : ℝ) (N : ℕ) (r ξ : ℝ) :
    -2*(Real.pi*r)*ccmActualHeadMidpointSignedMoment T N r*ξ^2 -
      ccmActualHeadMidpointQuarticBudget T N r*ξ^4 ≤
        ccmActualHeadMidpointCurrentSymbol T N r ξ := by
  have h := (abs_le.mp (abs_ccmActualHeadMidpointCurrentSymbol_add_quadratic_le T N r ξ)).1
  linarith only [h]

end RHTower
