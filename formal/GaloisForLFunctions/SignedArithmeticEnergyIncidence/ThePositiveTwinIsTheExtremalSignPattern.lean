import GaloisForLFunctions.SignedArithmeticEnergyIncidence.TheSourceIsTheDampedMoebiusResidueSeries

/-!
# The positive twin is the extremal sign pattern

The damped source is the residue series `Σ_d μ(d) d^{−η} v_d`.  Replace the Möbius coefficients by
any coefficients `a_d` with `|a_d| ≤ d^{−ε}` (`DampedCoefficients ε a`) — the class a reading that
sees only the sizes of the coefficients cannot tell apart.

* **Pointwise extremality** (`abs_residueSeries_le_abs_positiveTwin`): since every residue mode is
  nonpositive, `|Σ_d a_d v_d(n)| ≤ |Σ_d d^{−ε} v_d(n)|` at every state: the positive twin dominates
  every coefficient row of the class, the Möbius row included (`sq_orbit_le_sq_positiveTwin`).
* **The sign-blind reading has resolution exactly half damping** (`signBlind_admission_iff`): every
  row of the class has finite receiver energy iff `ε > 1/2`.  Above half damping the triangle
  inequality in `ℓ²` bounds them all (`residueSeries_partial_energy_le`); at or below it the
  positive twin itself diverges.

So an admission argument below half damping must use a property of `μ` that distinguishes it from
the all-`+1` row against the nonpositive residue modes: cancellation, not size.
-/

open Finset Filter Topology
open scoped ZeroAtInfty
open GaloisForLFunctions.BezoutValuationIncidence ArithmeticFunction

namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section
set_option autoImplicit false

/-- Coefficients of damping `ε`: `|a_d| ≤ d^{−ε}`. -/
def DampedCoefficients (ε : ℝ) (a : ℕ → ℝ) : Prop := ∀ d : ℕ, |a d| ≤ (d : ℝ) ^ (-ε)

/-- The residue series `Σ_d a_d v_d(n)`. -/
def residueSeries (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑' d : ℕ, a d * normalizedResidueProfile d n

theorem abs_coeff_mul_le {ε : ℝ} {a : ℕ → ℝ} (ha : DampedCoefficients ε a) (d n : ℕ) :
    |a d * normalizedResidueProfile d n| ≤ |(d : ℝ) ^ (-ε) * normalizedResidueProfile d n| := by
  rw [abs_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
  exact mul_le_mul_of_nonneg_right (ha d) (abs_nonneg _)

theorem summable_residueSeries {ε : ℝ} (hε : 0 < ε) {a : ℕ → ℝ} (ha : DampedCoefficients ε a)
    (n : ℕ) : Summable fun d : ℕ => a d * normalizedResidueProfile d n :=
  Summable.of_norm_bounded (summable_rpow_mul_normalizedResidueProfile hε n).abs fun d => by
    rw [Real.norm_eq_abs]; exact abs_coeff_mul_le ha d n

theorem positiveTwin_nonpos (ε : ℝ) (n : ℕ) : positiveTwin ε n ≤ 0 :=
  tsum_nonpos fun d => mul_nonpos_of_nonneg_of_nonpos
    (Real.rpow_nonneg (Nat.cast_nonneg d) _) (normalizedResidueProfile_nonpos d n)

/-- **Pointwise extremality of the positive twin.** -/
theorem abs_residueSeries_le_abs_positiveTwin {ε : ℝ} (hε : 0 < ε) {a : ℕ → ℝ}
    (ha : DampedCoefficients ε a) (n : ℕ) : |residueSeries a n| ≤ |positiveTwin ε n| := by
  have hs := summable_residueSeries hε ha n
  have ht := summable_rpow_mul_normalizedResidueProfile hε n
  have h1 : |residueSeries a n| ≤ ∑' d : ℕ, |a d * normalizedResidueProfile d n| := by
    unfold residueSeries
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hs.norm
  have h2 : ∑' d : ℕ, |a d * normalizedResidueProfile d n| ≤
      ∑' d : ℕ, |(d : ℝ) ^ (-ε) * normalizedResidueProfile d n| :=
    hs.abs.tsum_le_tsum (fun d => abs_coeff_mul_le ha d n) ht.abs
  have h3 : ∑' d : ℕ, |(d : ℝ) ^ (-ε) * normalizedResidueProfile d n| = -positiveTwin ε n := by
    unfold positiveTwin
    rw [← tsum_neg]
    refine tsum_congr fun d => ?_
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (Nat.cast_nonneg d) _)
      (normalizedResidueProfile_nonpos d n))]
  rw [abs_of_nonpos (positiveTwin_nonpos ε n)]
  linarith

/-- The Möbius row is a row of the class. -/
theorem moebius_dampedCoefficients (η : ℝ) :
    DampedCoefficients η fun d => ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-η) := by
  intro d
  rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
  have : |((moebius d : ℤ) : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]; exact_mod_cast abs_moebius_le_one
  calc |((moebius d : ℤ) : ℝ)| * (d : ℝ) ^ (-η) ≤ 1 * (d : ℝ) ^ (-η) :=
        mul_le_mul_of_nonneg_right this (Real.rpow_nonneg (Nat.cast_nonneg d) _)
    _ = _ := one_mul _

/-- **The Möbius source is pointwise dominated by its positive twin.** -/
theorem sq_orbit_le_sq_positiveTwin {η : ℝ} (hη : 0 < η) (n : ℕ) :
    arithmeticDampingCenteredOperator hη reciprocalObservable n ^ 2 ≤ positiveTwin η n ^ 2 := by
  rw [centeredOperator_reciprocal_eq_tsum hη n]
  have h := abs_residueSeries_le_abs_positiveTwin hη (moebius_dampedCoefficients η) n
  have he : residueSeries (fun d => ((moebius d : ℤ) : ℝ) * (d : ℝ) ^ (-η)) n =
      ∑' d : ℕ, residueTerm η d n := tsum_congr fun d => rfl
  rw [he] at h
  rw [← sq_abs, ← sq_abs (positiveTwin η n)]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

/-- **Sign-blind bound at every horizon**: every row of the class has
`Σ_{m<T} (Σ_d a_d v_d(m))² ≤ (Σ_d d^{−ε} ‖v_d‖_{ℓ²})²`. -/
theorem residueSeries_partial_energy_le {ε : ℝ} (hε : 0 < ε) {a : ℕ → ℝ}
    (ha : DampedCoefficients ε a)
    (hs : Summable fun d : ℕ => (d : ℝ) ^ (-ε) *
      Real.sqrt (∑' n, normalizedResidueProfile d n ^ 2)) (T : ℕ) :
    ∑ m ∈ range T, residueSeries a m ^ 2 ≤
      (∑' d : ℕ, (d : ℝ) ^ (-ε) * Real.sqrt (∑' n, normalizedResidueProfile d n ^ 2)) ^ 2 := by
  set u := residueSeries a with hu
  set S := ∑ m ∈ range T, u m ^ 2 with hS
  set B := ∑' d : ℕ, (d : ℝ) ^ (-ε) * Real.sqrt (∑' n, normalizedResidueProfile d n ^ 2)
  have hS0 : 0 ≤ S := sum_nonneg fun m _ => sq_nonneg _
  have hexp : S = ∑' d : ℕ, ∑ m ∈ range T, u m * (a d * normalizedResidueProfile d m) := by
    rw [Summable.tsum_finsetSum (f := fun m d => u m * (a d * normalizedResidueProfile d m))
      fun m _ => (summable_residueSeries hε ha m).mul_left (u m)]
    simp only [tsum_mul_left]
    refine sum_congr rfl fun m _ => ?_
    rw [sq]
    simp only [hu, residueSeries]
  have hbound : ∀ d : ℕ, ∑ m ∈ range T, u m * (a d * normalizedResidueProfile d m) ≤
      Real.sqrt S * ((d : ℝ) ^ (-ε) * Real.sqrt (∑' n, normalizedResidueProfile d n ^ 2)) := by
    intro d
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt (range T) u
      (fun m => a d * normalizedResidueProfile d m)
    have hterm : ∑ m ∈ range T, (a d * normalizedResidueProfile d m) ^ 2 ≤
        ((d : ℝ) ^ (-ε)) ^ 2 * ∑' n, normalizedResidueProfile d n ^ 2 := by
      have hle : ∑ m ∈ range T, normalizedResidueProfile d m ^ 2 ≤
          ∑' n, normalizedResidueProfile d n ^ 2 :=
        (summable_sq_normalizedResidueProfile d).sum_le_tsum _ fun n _ => sq_nonneg _
      have ha2 : a d ^ 2 ≤ ((d : ℝ) ^ (-ε)) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (ha d) 2
      calc ∑ m ∈ range T, (a d * normalizedResidueProfile d m) ^ 2
          = a d ^ 2 * ∑ m ∈ range T, normalizedResidueProfile d m ^ 2 := by
            rw [mul_sum]; exact sum_congr rfl fun m _ => by ring
        _ ≤ ((d : ℝ) ^ (-ε)) ^ 2 * ∑' n, normalizedResidueProfile d n ^ 2 :=
            mul_le_mul ha2 hle (sum_nonneg fun m _ => sq_nonneg _) (sq_nonneg _)
    have hsq : Real.sqrt (∑ m ∈ range T, (a d * normalizedResidueProfile d m) ^ 2) ≤
        (d : ℝ) ^ (-ε) * Real.sqrt (∑' n, normalizedResidueProfile d n ^ 2) := by
      calc _ ≤ Real.sqrt (((d : ℝ) ^ (-ε)) ^ 2 * ∑' n, normalizedResidueProfile d n ^ 2) :=
            Real.sqrt_le_sqrt hterm
        _ = _ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    calc _ ≤ Real.sqrt (∑ m ∈ range T, u m ^ 2) *
          Real.sqrt (∑ m ∈ range T, (a d * normalizedResidueProfile d m) ^ 2) := hcs
      _ ≤ _ := mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)
  have hsumm : Summable fun d : ℕ => ∑ m ∈ range T, u m * (a d * normalizedResidueProfile d m) :=
    summable_sum fun m _ => (summable_residueSeries hε ha m).mul_left (u m)
  have hSB : S ≤ Real.sqrt S * B := by
    calc S = ∑' d : ℕ, ∑ m ∈ range T, u m * (a d * normalizedResidueProfile d m) := hexp
      _ ≤ ∑' d : ℕ, Real.sqrt S * ((d : ℝ) ^ (-ε) *
          Real.sqrt (∑' n, normalizedResidueProfile d n ^ 2)) :=
          hsumm.tsum_le_tsum hbound (hs.mul_left _)
      _ = _ := by rw [tsum_mul_left]
  have hroot : Real.sqrt S ≤ B := by
    rcases (Real.sqrt_nonneg S).eq_or_lt with h0 | hpos
    · rw [← h0]
      exact tsum_nonneg fun d => mul_nonneg (by positivity) (Real.sqrt_nonneg _)
    · nlinarith [Real.sq_sqrt hS0]
  calc S = Real.sqrt S ^ 2 := (Real.sq_sqrt hS0).symm
    _ ≤ B ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hroot 2

/-- **The sign-blind reading has resolution exactly half damping**: every row with
`|a_d| ≤ d^{−ε}` has finite receiver energy iff `ε > 1/2`. -/
theorem signBlind_admission_iff {ε : ℝ} (hε : 0 < ε) :
    (∀ a : ℕ → ℝ, DampedCoefficients ε a → Summable fun n => residueSeries a n ^ 2) ↔
      1 / 2 < ε := by
  constructor
  · intro h
    by_contra hle
    have hle := not_lt.mp hle
    have htwin : DampedCoefficients ε fun d => (d : ℝ) ^ (-ε) := fun d => by
      rw [abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    exact not_summable_positiveTwin hε hle (h _ htwin)
  · intro hε2 a ha
    exact summable_of_sum_range_le (fun m => sq_nonneg _)
      (residueSeries_partial_energy_le hε ha ((summable_signBlind_iff ε).mpr hε2))

end

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
