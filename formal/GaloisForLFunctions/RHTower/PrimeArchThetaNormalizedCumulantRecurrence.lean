import GaloisForLFunctions.RHTower.PrimeArchThetaAllOrderCumulant

/-!
# Normalized raw-to-logarithmic cumulant recurrence

Write `ν_j = R_j / R_0` for the normalized even moments of the positive theta-cusp source and
`M_n` for the normalized prime--archimedean logarithmic moments.  The odd-order Leibniz
expansion of `XiC' + z G XiC = 0` only pairs odd jets of `z G` with even Xi jets.  Since
`C(2n+1, 2r+1) (2r+1)! (2(n-r))! = (2n+1)!`, division by `(2n+1)! R_0` gives, for every `n`,

`M_n = (-1)^n ν_{n+1}/(2n+1)! - ∑_{r<n} (-1)^{n-r} M_r ν_{n-r}/(2(n-r))!`.

The recurrence retains every alternating mixed term; it gives no sign for the `M_n`.
-/

open Complex

namespace RHTower

noncomputable section

private theorem sum_range_two_mul_eq_pairs {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ i ∈ Finset.range (2 * m), f i = ∑ r ∈ Finset.range m, (f (2 * r) + f (2 * r + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, add_assoc]

/-- The odd-order recurrence with only the even Xi jets and odd product jets that survive parity:
`(-1)^{n+1} R_{n+1} + ∑_{r ≤ n} C(2n+1,2r+1) (2r+1)! M_r (-1)^{n-r} R_{n-r} = 0`. -/
theorem normalizedPrimeArch_oddOrder_rawMoment_identity (n : ℕ) :
    (-1) ^ (n + 1) * thetaCuspRawEvenMoment (n + 1) +
      ∑ r ∈ Finset.range (n + 1),
        (((2 * n + 1).choose (2 * r + 1) * (2 * r + 1).factorial : ℕ) : ℝ) *
          normalizedPrimeArchMoment r * ((-1) ^ (n - r) * thetaCuspRawEvenMoment (n - r)) = 0 := by
  have h := thetaCusp_allOrderCumulantRecurrence (2 * n + 1)
  have hX : thetaCuspXiJet (2 * n + 1 + 1) =
      (((-1) ^ (n + 1) * thetaCuspRawEvenMoment (n + 1) : ℝ) : ℂ) := by
    rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring, thetaCuspXiJet, if_pos (even_two_mul _),
      Nat.mul_div_cancel_left _ two_pos]
  have hterm : ∀ r ∈ Finset.range (n + 1),
      (((2 * n + 1).choose (2 * r) : ℕ) : ℂ) * thetaCuspPrimeArchProductJet (2 * r) *
          thetaCuspXiJet (2 * n + 1 - 2 * r) +
        (((2 * n + 1).choose (2 * r + 1) : ℕ) : ℂ) * thetaCuspPrimeArchProductJet (2 * r + 1) *
          thetaCuspXiJet (2 * n + 1 - (2 * r + 1)) =
      (((((2 * n + 1).choose (2 * r + 1) * (2 * r + 1).factorial : ℕ) : ℝ) *
          normalizedPrimeArchMoment r * ((-1) ^ (n - r) * thetaCuspRawEvenMoment (n - r)) : ℝ) :
        ℂ) := by
    intro r hr
    have hrn : r ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
    have h0 : thetaCuspPrimeArchProductJet (2 * r) = 0 := by
      rw [thetaCuspPrimeArchProductJet, if_neg (Nat.not_odd_iff_even.mpr (even_two_mul r))]
    have h1 : thetaCuspPrimeArchProductJet (2 * r + 1) =
        (((2 * r + 1).factorial : ℕ) : ℂ) * (normalizedPrimeArchMoment r : ℂ) := by
      rw [thetaCuspPrimeArchProductJet, if_pos (odd_two_mul_add_one r),
        show (2 * r + 1 - 1) / 2 = r by omega]
    have h2 : thetaCuspXiJet (2 * n + 1 - (2 * r + 1)) =
        (((-1) ^ (n - r) * thetaCuspRawEvenMoment (n - r) : ℝ) : ℂ) := by
      rw [show 2 * n + 1 - (2 * r + 1) = 2 * (n - r) by omega, thetaCuspXiJet,
        if_pos (even_two_mul _), Nat.mul_div_cancel_left _ two_pos]
    rw [h0, h1, h2]
    push_cast
    ring
  have hsplit := sum_range_two_mul_eq_pairs (fun i => (((2 * n + 1).choose i : ℕ) : ℂ) *
    thetaCuspPrimeArchProductJet i * thetaCuspXiJet (2 * n + 1 - i)) (n + 1)
  rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring] at hsplit
  rw [hsplit, Finset.sum_congr rfl hterm, hX] at h
  exact_mod_cast h

/-- **Normalized raw-to-logarithmic recurrence.**  For every `n`,
`M_n = (-1)^n ν_{n+1}/(2n+1)! - ∑_{r<n} (-1)^{n-r} M_r ν_{n-r}/(2(n-r))!`. -/
theorem normalizedPrimeArchMoment_eq_normalizedEvenMoment_recurrence (n : ℕ) :
    normalizedPrimeArchMoment n =
      (-1) ^ n * thetaCuspNormalizedEvenMoment (n + 1) / ((2 * n + 1).factorial : ℝ) -
        ∑ r ∈ Finset.range n, (-1) ^ (n - r) * normalizedPrimeArchMoment r *
          thetaCuspNormalizedEvenMoment (n - r) / ((2 * (n - r)).factorial : ℝ) := by
  have hS := normalizedPrimeArch_oddOrder_rawMoment_identity n
  have hR0 : 0 < thetaCuspRawEvenMoment 0 := thetaCuspRawEvenMoment_zero_pos
  have hF : (0 : ℝ) < ((2 * n + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hcoef : ∀ r ∈ Finset.range n,
      ((((2 * n + 1).choose (2 * r + 1) * (2 * r + 1).factorial : ℕ) : ℝ)) =
        ((2 * n + 1).factorial : ℝ) / ((2 * (n - r)).factorial : ℝ) := by
    intro r hr
    have hrn : r < n := Finset.mem_range.mp hr
    have hc := Nat.choose_mul_factorial_mul_factorial (show 2 * r + 1 ≤ 2 * n + 1 by omega)
    rw [show 2 * n + 1 - (2 * r + 1) = 2 * (n - r) by omega] at hc
    have hpos : (0 : ℝ) < ((2 * (n - r)).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [eq_div_iff hpos.ne', ← hc]
    push_cast
    ring
  rw [Finset.sum_range_succ, Nat.sub_self, Finset.sum_congr rfl fun r hr => by
    rw [hcoef r hr]] at hS
  have hlast : (((2 * n + 1).choose (2 * n + 1) * (2 * n + 1).factorial : ℕ) : ℝ) =
      ((2 * n + 1).factorial : ℝ) := by
    rw [Nat.choose_self, one_mul]
  rw [hlast, pow_zero, one_mul] at hS
  have hsum : ∑ r ∈ Finset.range n, (-1) ^ (n - r) * normalizedPrimeArchMoment r *
        thetaCuspNormalizedEvenMoment (n - r) / ((2 * (n - r)).factorial : ℝ) =
      (∑ r ∈ Finset.range n, ((2 * n + 1).factorial : ℝ) / ((2 * (n - r)).factorial : ℝ) *
          normalizedPrimeArchMoment r * ((-1) ^ (n - r) * thetaCuspRawEvenMoment (n - r))) /
        (((2 * n + 1).factorial : ℝ) * thetaCuspRawEvenMoment 0) := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hpos : (0 : ℝ) < ((2 * (n - r)).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    rw [thetaCuspNormalizedEvenMoment]
    field_simp
  rw [hsum, thetaCuspNormalizedEvenMoment]
  set A := ∑ r ∈ Finset.range n, ((2 * n + 1).factorial : ℝ) / ((2 * (n - r)).factorial : ℝ) *
    normalizedPrimeArchMoment r * ((-1) ^ (n - r) * thetaCuspRawEvenMoment (n - r)) with hA
  clear_value A
  field_simp
  linear_combination hS
