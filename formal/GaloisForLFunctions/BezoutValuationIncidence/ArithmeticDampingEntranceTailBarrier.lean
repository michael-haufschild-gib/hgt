import GaloisForLFunctions.BezoutValuationIncidence.ArithmeticDampingEntranceLaw

/-!
# Entrance tails and the scope of total-variation control

The probability tail forces a nonsquare-summable row error at damping at most
one half. The reciprocal observable has a faster, square-summable omitted tail.
Thus the obstruction concerns absolute row control, not the signed source.
-/

open Finset RHTower

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- Entrance probability beyond the positive-state cutoff `N`. -/
def arithmeticDampingEntranceTail (η : ℝ) (N : ℕ) : ℝ :=
  ∑' k : ℕ, arithmeticDampingEntrance η (N + k + 1)

theorem summable_arithmeticDampingEntrance_tail {η : ℝ} (hη : 0 < η) (N : ℕ) :
    Summable (fun k : ℕ => arithmeticDampingEntrance η (N + k + 1)) := by
  simpa only [Nat.add_comm N] using
    (summable_nat_add_iff N).mpr (hasSum_arithmeticDampingEntrance hη).summable

theorem arithmeticDampingEntranceTail_nonneg {η : ℝ} (hη : 0 < η) (N : ℕ) :
    0 ≤ arithmeticDampingEntranceTail η N :=
  tsum_nonneg fun k => arithmeticDampingEntrance_nonneg hη (N + k + 1)

/-- Size bias turns the exact reciprocal tail into a probability-tail lower bound. -/
theorem arithmeticDampingEntranceTail_lower {η : ℝ} (hη : 0 < η) (N : ℕ) :
    (pmPowerDampedDivisorDensity η).re * ((N + 1 : ℕ) : ℝ) ^ (-η) ≤
      arithmeticDampingEntranceTail η N := by
  have hs := (hasSum_arithmeticDampingEntrance_reciprocal_tail hη N).mul_left
    ((N + 1 : ℕ) : ℝ)
  have hle := hs.summable.tsum_le_tsum (fun k => show
      ((N + 1 : ℕ) : ℝ) *
        (arithmeticDampingEntrance η (N + k + 1) / (N + k + 1 : ℕ)) ≤
          arithmeticDampingEntrance η (N + k + 1) from by
    have hk : (0 : ℝ) < (N + k + 1 : ℕ) := by positivity
    have hNk : ((N + 1 : ℕ) : ℝ) ≤ (N + k + 1 : ℕ) := by exact_mod_cast (show N + 1 ≤ N + k + 1 by omega)
    rw [← mul_div_assoc, div_le_iff₀ hk]
    nlinarith [arithmeticDampingEntrance_nonneg hη (N + k + 1)])
    (summable_arithmeticDampingEntrance_tail hη N)
  rw [hs.tsum_eq] at hle
  have hpow : ((N + 1 : ℕ) : ℝ) * ((N + 1 : ℕ) : ℝ) ^ (-1 - η) =
      ((N + 1 : ℕ) : ℝ) ^ (-η) := by
    calc
      _ = ((N + 1 : ℕ) : ℝ) ^ (1 + (-1 - η)) := by
        rw [Real.rpow_add (by positivity), Real.rpow_one]
      _ = _ := by congr 1; ring
  unfold arithmeticDampingEntranceTail
  calc
    _ = ((N + 1 : ℕ) : ℝ) *
        ((pmPowerDampedDivisorDensity η).re * ((N + 1 : ℕ) : ℝ) ^ (-1 - η)) := by
      rw [← hpow]; ring
    _ ≤ _ := hle

private theorem aet_not_summable_sq_of_lower {η c : ℝ} (hc : 0 < c)
    (hη : η ≤ 1 / 2) (f : ℕ → ℝ)
    (hf : ∀ n, c * ((n + 1 : ℕ) : ℝ) ^ (-η) ≤ f n) :
    ¬ Summable (fun n => f n ^ 2) := by
  intro hs
  have hs' : Summable (fun n : ℕ =>
      c ^ 2 * ((n + 1 : ℕ) : ℝ) ^ (-2 * η)) := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (sq_nonneg c)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (fun n => ?_) hs
    have hnonneg : 0 ≤ c * ((n + 1 : ℕ) : ℝ) ^ (-η) := by positivity
    have hsq := (sq_le_sq₀ hnonneg (hnonneg.trans (hf n))).mpr (hf n)
    have he : (c * ((n + 1 : ℕ) : ℝ) ^ (-η)) ^ 2 =
        c ^ 2 * ((n + 1 : ℕ) : ℝ) ^ (-2 * η) := by
      rw [mul_pow, ← Real.rpow_natCast (((n + 1 : ℕ) : ℝ) ^ (-η)) 2,
        ← Real.rpow_mul (Nat.cast_nonneg (n + 1))]
      norm_num only [Nat.cast_ofNat]
      rw [show (-η) * 2 = -2 * η by ring]
    rwa [he] at hsq
  have hp : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-2 * η)) :=
    (summable_mul_left_iff (pow_ne_zero 2 hc.ne')).mp hs'
  have hp' : Summable (fun n : ℕ => (n : ℝ) ^ (-2 * η)) :=
    (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-2 * η)) 1).mp hp
  have hlt : -2 * η < -1 := Real.summable_nat_rpow.mp hp'
  linarith

/-- Probability tails cannot be square-summed at or below half damping. -/
theorem not_summable_arithmeticDampingEntranceTail_sq {η : ℝ}
    (hη : 0 < η) (hhalf : η ≤ 1 / 2) :
    ¬ Summable (fun N : ℕ => arithmeticDampingEntranceTail η N ^ 2) :=
  aet_not_summable_sq_of_lower (pmPowerDampedDivisorDensity_re_pos hη) hhalf
    (arithmeticDampingEntranceTail η) (arithmeticDampingEntranceTail_lower hη)

/-- Absolute row distance on positive target states. The starting state may be zero. -/
def arithmeticDampingRowL1Error (η : ℝ) (n : ℕ) : ℝ :=
  ∑' k : ℕ, |arithmeticDampingTransition η n (k + 1) -
    arithmeticDampingEntrance η (k + 1)|

theorem summable_arithmeticDampingRowAbsError {η : ℝ} (hη : 0 < η) (n : ℕ) :
    Summable (fun k : ℕ => |arithmeticDampingTransition η n (k + 1) -
      arithmeticDampingEntrance η (k + 1)|) := by
  have hs : Summable (fun k : ℕ => arithmeticDampingTransition η n (k + 1)) := by
    apply summable_of_ne_finset_zero (s := range n)
    intro k hk
    exact arithmeticDampingTransition_eq_zero_of_lt η (by
      have := not_lt.mp (mem_range.not.mp hk)
      omega)
  exact (hs.sub (hasSum_arithmeticDampingEntrance hη).summable).abs

/-- A row supported below its starting state cannot see the entrance tail. -/
theorem arithmeticDampingEntranceTail_le_rowL1Error {η : ℝ} (hη : 0 < η) (n : ℕ) :
    arithmeticDampingEntranceTail η n ≤ arithmeticDampingRowL1Error η n := by
  apply (summable_arithmeticDampingEntrance_tail hη n).tsum_le_tsum_of_inj
    (fun k => n + k) (fun _ _ h => Nat.add_left_cancel h)
    (fun _ _ => abs_nonneg _) (fun k => ?_) (summable_arithmeticDampingRowAbsError hη n)
  rw [arithmeticDampingTransition_eq_zero_of_lt η (by omega), zero_sub, abs_neg,
    abs_of_nonneg (arithmeticDampingEntrance_nonneg hη _)]

theorem not_summable_arithmeticDampingRowL1Error_sq {η : ℝ}
    (hη : 0 < η) (hhalf : η ≤ 1 / 2) :
    ¬ Summable (fun n : ℕ => arithmeticDampingRowL1Error η n ^ 2) :=
  aet_not_summable_sq_of_lower (pmPowerDampedDivisorDensity_re_pos hη) hhalf
    (arithmeticDampingRowL1Error η) (fun n =>
      (arithmeticDampingEntranceTail_lower hη n).trans
        (arithmeticDampingEntranceTail_le_rowL1Error hη n))

/-- For positive starting states this is the usual probability total variation. -/
def arithmeticDampingTotalVariation (η : ℝ) (n : ℕ) : ℝ :=
  arithmeticDampingRowL1Error η n / 2

/-- Reindexing by `n+1` restricts the statement to probability rows. -/
theorem not_summable_arithmeticDampingTotalVariation_sq {η : ℝ}
    (hη : 0 < η) (hhalf : η ≤ 1 / 2) :
    ¬ Summable (fun n : ℕ => arithmeticDampingTotalVariation η (n + 1) ^ 2) := by
  intro hs
  have hs' : Summable (fun n : ℕ => arithmeticDampingRowL1Error η (n + 1) ^ 2) := by
    apply (hs.mul_left 4).congr
    intro n
    unfold arithmeticDampingTotalVariation
    ring
  exact not_summable_arithmeticDampingRowL1Error_sq hη hhalf
    ((summable_nat_add_iff 1).mp hs')

/-- The actual reciprocal observable has a square-summable omitted tail at every
positive damping, including the range excluded by absolute row control. -/
theorem summable_arithmeticDampingEntrance_reciprocal_tail_sq {η : ℝ} (hη : 0 < η) :
    Summable (fun N : ℕ => (∑' k : ℕ,
      arithmeticDampingEntrance η (N + k + 1) / (N + k + 1 : ℕ)) ^ 2) := by
  have hp : Summable (fun n : ℕ => (n : ℝ) ^ ((-1 - η) * 2)) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hs := ((summable_nat_add_iff 1).mpr hp).mul_left
    ((pmPowerDampedDivisorDensity η).re ^ 2)
  apply hs.congr
  intro N
  rw [(hasSum_arithmeticDampingEntrance_reciprocal_tail hη N).tsum_eq,
    mul_pow, ← Real.rpow_natCast (((N + 1 : ℕ) : ℝ) ^ (-1 - η)) 2,
    ← Real.rpow_mul (Nat.cast_nonneg (N + 1))]
  norm_num only [Nat.cast_ofNat]

/-- Density is at most one, directly from the entrance probability law. -/
theorem arithmeticDampingEntrance_density_le_one {η : ℝ} (hη : 0 < η) :
    (pmPowerDampedDivisorDensity η).re ≤ 1 := by
  have hs := hasSum_arithmeticDampingEntrance_reciprocal_tail hη 0
  have hle := hs.summable.tsum_le_tsum (fun k => show
      arithmeticDampingEntrance η (0 + k + 1) / (0 + k + 1 : ℕ) ≤
        arithmeticDampingEntrance η (k + 1) from by
    simp only [Nat.zero_add]
    have hk : (0 : ℝ) < (k + 1 : ℕ) := by positivity
    have hk1 : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
    rw [div_le_iff₀ hk]
    nlinarith [arithmeticDampingEntrance_nonneg hη (k + 1)])
    (hasSum_arithmeticDampingEntrance hη).summable
  rw [hs.tsum_eq, (hasSum_arithmeticDampingEntrance hη).tsum_eq] at hle
  simpa using hle

/-- A common omitted-tail majorant for all positive dampings. Its square is
summable; this assertion concerns the reciprocal observable, not the full row. -/
theorem arithmeticDampingEntrance_reciprocal_tail_le_inv {η : ℝ} (hη : 0 < η) (N : ℕ) :
    (∑' k : ℕ, arithmeticDampingEntrance η (N + k + 1) / (N + k + 1 : ℕ)) ≤
      1 / ((N + 1 : ℕ) : ℝ) := by
  rw [(hasSum_arithmeticDampingEntrance_reciprocal_tail hη N).tsum_eq]
  calc
    _ ≤ 1 * ((N + 1 : ℕ) : ℝ) ^ (-1 - η) :=
      mul_le_mul_of_nonneg_right (arithmeticDampingEntrance_density_le_one hη)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    _ ≤ ((N + 1 : ℕ) : ℝ) ^ (-1 : ℝ) := by
      rw [one_mul]
      exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N))
        (by linarith)
    _ = _ := by rw [Real.rpow_neg_one, one_div]

end
end GaloisForLFunctions.BezoutValuationIncidence
