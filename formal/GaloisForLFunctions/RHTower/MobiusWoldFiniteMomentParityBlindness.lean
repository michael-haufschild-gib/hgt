import Mathlib.Algebra.Group.ForwardDiff

/-!
# Fixed-order Wold moments are blind to Möbius parity

On squarefree integers, the Möbius sign is `(-1) ^ omega`.  This file constructs the exact
adjacent-breadth packet that defeats every fixed collection of polynomial moments of `omega`.

The order-`n` alternating binomial packet on breadths `r, ..., r+n` annihilates every monomial of
degree below `n`, while its parity response is the nonzero value `(-1)^(n+r) 2^n`.  Splitting the
positive and negative coefficients therefore gives two positive adjacent-layer measures with
identical moments through degree `n-1` and opposite Möbius parity.

This is finite algebra only.  It does not assert that arithmetic Wold layers realize the abstract
packet with prescribed local mass.
-/

namespace RHTower

open scoped BigOperators
open Finset Function fwdDiff Polynomial

/-- Signed coefficient of the order-`n` adjacent Wold-breadth packet. -/
def woldAdjacentMomentBlindCoefficient (n k : ℕ) : ℤ :=
  (-1 : ℤ) ^ (n - k) * n.choose k

/-- Every monomial reporter below order `n` annihilates the adjacent binomial packet. -/
theorem woldAdjacentMomentBlind_monomial_eq_zero
    {n j : ℕ} (hj : j < n) (r : ℤ) :
    (∑ k ∈ Finset.range (n + 1),
      woldAdjacentMomentBlindCoefficient n k * (r + k) ^ j) = 0 := by
  have hzero := congr_fun
    (fwdDiff_iter_pow_eq_zero_of_lt (R := ℤ) hj) r
  rw [fwdDiff_iter_eq_sum_shift] at hzero
  simpa [woldAdjacentMomentBlindCoefficient, smul_eq_mul] using hzero

/-- The first visible monomial has exact response `n!`, independently of the central breadth
location. -/
theorem woldAdjacentMomentBlind_firstVisibleMoment_eq_factorial
    (n : ℕ) (r : ℤ) :
    (∑ k ∈ Finset.range (n + 1),
      woldAdjacentMomentBlindCoefficient n k * (r + k) ^ n) =
      (n.factorial : ℤ) := by
  have hfactorial := congr_fun
    (fwdDiff_iter_eq_factorial (R := ℤ) (n := n)) r
  rw [fwdDiff_iter_eq_sum_shift] at hfactorial
  simpa [woldAdjacentMomentBlindCoefficient, smul_eq_mul] using hfactorial

/-- Any fixed polynomial reporter of degree below `n` is blind to the same packet. -/
theorem woldAdjacentMomentBlind_polynomial_eq_zero
    (n : ℕ) (coeff : ℕ → ℤ) (r : ℤ) :
    (∑ k ∈ Finset.range (n + 1),
      woldAdjacentMomentBlindCoefficient n k *
        (∑ j ∈ Finset.range n, coeff j * (r + k) ^ j)) = 0 := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j hj
  have hjn : j < n := Finset.mem_range.mp hj
  calc
    (∑ k ∈ Finset.range (n + 1),
      woldAdjacentMomentBlindCoefficient n k *
        (coeff j * (r + k) ^ j)) =
        coeff j * ∑ k ∈ Finset.range (n + 1),
          woldAdjacentMomentBlindCoefficient n k * (r + k) ^ j := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k hk
            ring
    _ = 0 := by
      rw [woldAdjacentMomentBlind_monomial_eq_zero hjn]
      simp

/-- Every nontrivial adjacent packet has zero total coefficient mass.  Hence every label-blind
scalarization, which factors through total mass, erases it exactly. -/
theorem woldAdjacentMomentBlind_totalMass_eq_zero
    {n : ℕ} (hn : 0 < n) :
    (∑ k ∈ Finset.range (n + 1),
      woldAdjacentMomentBlindCoefficient n k) = 0 := by
  have hmoment :=
    woldAdjacentMomentBlind_monomial_eq_zero (n := n) (j := 0) hn (0 : ℤ)
  simpa using hmoment

/-- Constant label-blind response kills the moment-blind packet for every scalar amplitude. -/
theorem woldAdjacentMomentBlind_constantReadout_eq_zero
    {n : ℕ} (hn : 0 < n) (a : ℤ) :
    (∑ k ∈ Finset.range (n + 1),
      woldAdjacentMomentBlindCoefficient n k * a) = 0 := by
  rw [← Finset.sum_mul, woldAdjacentMomentBlind_totalMass_eq_zero hn]
  simp

/-- Möbius parity is maximally visible on the moment-blind packet: all binomial masses reinforce
with one sign instead of cancelling. -/
theorem woldAdjacentMomentBlind_parityResponse
    (n r : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      woldAdjacentMomentBlindCoefficient n k *
        (-1 : ℤ) ^ (r + k)) =
      (-1 : ℤ) ^ (n + r) * 2 ^ n := by
  calc
    _ = ∑ k ∈ Finset.range (n + 1),
        (-1 : ℤ) ^ (n + r) * n.choose k := by
          apply Finset.sum_congr rfl
          intro k hk
          have hkn : k ≤ n := by
            simpa using (Finset.mem_range.mp hk)
          have hpow :
              (-1 : ℤ) ^ (n - k) * (-1 : ℤ) ^ (r + k) =
                (-1 : ℤ) ^ (n + r) := by
            rw [← pow_add]
            congr 1
            omega
          calc
            woldAdjacentMomentBlindCoefficient n k * (-1 : ℤ) ^ (r + k) =
                ((-1 : ℤ) ^ (n - k) * (-1 : ℤ) ^ (r + k)) *
                  n.choose k := by
                    simp only [woldAdjacentMomentBlindCoefficient]
                    ring
            _ = (-1 : ℤ) ^ (n + r) * n.choose k := by rw [hpow]
    _ = (-1 : ℤ) ^ (n + r) *
        ∑ k ∈ Finset.range (n + 1), n.choose k := by
          simp only [Nat.cast_sum]
          rw [Finset.mul_sum]
    _ = _ := by
      rw [Nat.sum_range_choose]
      norm_num

/-- In particular, parity response never vanishes, although every lower-order moment does. -/
theorem woldAdjacentMomentBlind_parityResponse_ne_zero
    (n r : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      woldAdjacentMomentBlindCoefficient n k *
        (-1 : ℤ) ^ (r + k)) ≠ 0 := by
  rw [woldAdjacentMomentBlind_parityResponse]
  exact mul_ne_zero (by simp) (by positivity)

/-- **Sharp lower bound on a polynomial parity reader.**  A polynomial agreeing with Möbius
parity on `n + 1` consecutive Wold layers must have degree at least `n`. -/
theorem natDegree_ge_of_eval_eq_woldParity_on_adjacent
    (n r : ℕ) (P : ℤ[X])
    (hmatch : ∀ k ∈ Finset.range (n + 1),
      P.eval ((r + k : ℕ) : ℤ) = (-1 : ℤ) ^ (r + k)) :
    n ≤ P.natDegree := by
  by_contra hnot
  have hdeg : P.natDegree < n := Nat.lt_of_not_ge hnot
  have hzero := congr_fun
    (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hdeg) (r : ℤ)
  rw [fwdDiff_iter_eq_sum_shift] at hzero
  have hsum :
      (∑ k ∈ Finset.range (n + 1),
        woldAdjacentMomentBlindCoefficient n k *
          P.eval ((r + k : ℕ) : ℤ)) =
        (∑ k ∈ Finset.range (n + 1),
          woldAdjacentMomentBlindCoefficient n k *
            (-1 : ℤ) ^ (r + k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hmatch k hk]
  have hleft :
      (∑ k ∈ Finset.range (n + 1),
        woldAdjacentMomentBlindCoefficient n k *
          P.eval ((r + k : ℕ) : ℤ)) = 0 := by
    simpa [woldAdjacentMomentBlindCoefficient, smul_eq_mul] using hzero
  rw [hleft, woldAdjacentMomentBlind_parityResponse] at hsum
  exact (mul_ne_zero (by simp) (by positivity)) hsum.symm

/-- Rational-coefficient version of the sharp degree lower bound, used to read the exact leading
conditioning coefficient. -/
theorem natDegree_ge_of_eval_eq_woldParity_on_adjacent_rat
    (n r : ℕ) (P : ℚ[X])
    (hmatch : ∀ k ∈ Finset.range (n + 1),
      P.eval ((r + k : ℕ) : ℚ) = (-1 : ℚ) ^ (r + k)) :
    n ≤ P.natDegree := by
  by_contra hnot
  have hdeg : P.natDegree < n := Nat.lt_of_not_ge hnot
  have hzero := congr_fun
    (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hdeg) (r : ℚ)
  rw [fwdDiff_iter_eq_sum_shift] at hzero
  have hsum :
      (∑ k ∈ Finset.range (n + 1),
        (woldAdjacentMomentBlindCoefficient n k : ℚ) *
          P.eval ((r + k : ℕ) : ℚ)) =
        (∑ k ∈ Finset.range (n + 1),
          (woldAdjacentMomentBlindCoefficient n k : ℚ) *
            (-1 : ℚ) ^ (r + k)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hmatch k hk]
  have hleft :
      (∑ k ∈ Finset.range (n + 1),
        (woldAdjacentMomentBlindCoefficient n k : ℚ) *
          P.eval ((r + k : ℕ) : ℚ)) = 0 := by
    simpa [woldAdjacentMomentBlindCoefficient, smul_eq_mul] using hzero
  have hparity :
      (∑ k ∈ Finset.range (n + 1),
        (woldAdjacentMomentBlindCoefficient n k : ℚ) *
          (-1 : ℚ) ^ (r + k)) =
        (-1 : ℚ) ^ (n + r) * 2 ^ n := by
    exact_mod_cast woldAdjacentMomentBlind_parityResponse n r
  rw [hleft, hparity] at hsum
  exact (mul_ne_zero (by simp) (by positivity)) hsum.symm

/-- **Exact conditioning coefficient.**  A rational polynomial of degree at most `n` agreeing
with parity on `n + 1` consecutive Wold layers has degree exactly `n`, and its leading coefficient
times `n!` is the full parity charge `(-1)^(n+r) 2^n`. -/
theorem leadingCoeff_mul_factorial_of_eval_eq_woldParity_on_adjacent
    (n r : ℕ) (P : ℚ[X])
    (hdeg : P.natDegree ≤ n)
    (hmatch : ∀ k ∈ Finset.range (n + 1),
      P.eval ((r + k : ℕ) : ℚ) = (-1 : ℚ) ^ (r + k)) :
    P.leadingCoeff * n.factorial =
      (-1 : ℚ) ^ (n + r) * 2 ^ n := by
  have hge :=
    natDegree_ge_of_eval_eq_woldParity_on_adjacent_rat n r P hmatch
  have heq : P.natDegree = n := Nat.le_antisymm hdeg hge
  have hfd := congr_fun P.fwdDiff_iter_degree_eq_factorial (r : ℚ)
  rw [heq] at hfd
  rw [fwdDiff_iter_eq_sum_shift] at hfd
  calc
    P.leadingCoeff * n.factorial =
        ∑ k ∈ Finset.range (n + 1),
          ((-1 : ℤ) ^ (n - k) * n.choose k) •
            P.eval ((r : ℚ) + k • (1 : ℚ)) := by
              simpa [smul_eq_mul] using hfd.symm
    _ = ∑ k ∈ Finset.range (n + 1),
          (woldAdjacentMomentBlindCoefficient n k : ℚ) *
            (-1 : ℚ) ^ (r + k) := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [show (r : ℚ) + k • (1 : ℚ) =
                ((r + k : ℕ) : ℚ) by norm_num]
              rw [hmatch k hk]
              simp [woldAdjacentMomentBlindCoefficient]
    _ = (-1 : ℚ) ^ (n + r) * 2 ^ n := by
      exact_mod_cast woldAdjacentMomentBlind_parityResponse n r

/-- **Sharp breadth-seam charge.**  A degree-at-most-`n` polynomial that reads parity on `n + 1`
consecutive layers misses parity at the first adjacent layer by exactly `2^(n+1)`, with the forced
alternating sign. -/
theorem eval_next_of_eval_eq_woldParity_on_adjacent
    (n r : ℕ) (P : ℚ[X])
    (hdeg : P.natDegree ≤ n)
    (hmatch : ∀ k ∈ Finset.range (n + 1),
      P.eval ((r + k : ℕ) : ℚ) = (-1 : ℚ) ^ (r + k)) :
    P.eval ((r + n + 1 : ℕ) : ℚ) =
      (-1 : ℚ) ^ (r + n + 1) * (1 - 2 ^ (n + 1)) := by
  have hdeg' : P.natDegree < n + 1 := Nat.lt_succ_of_le hdeg
  have hzero := congr_fun
    (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hdeg') (r : ℚ)
  rw [fwdDiff_iter_eq_sum_shift] at hzero
  have hsplit :
      (∑ k ∈ Finset.range (n + 1),
          ((-1 : ℤ) ^ (n + 1 - k) * (n + 1).choose k) •
            P.eval ((r : ℚ) + k • (1 : ℚ))) +
        P.eval ((r : ℚ) + (n + 1) • (1 : ℚ)) = 0 := by
    rw [Finset.sum_range_succ] at hzero
    simpa [smul_eq_mul] using hzero
  have hknown :
      (∑ k ∈ Finset.range (n + 1),
          ((-1 : ℤ) ^ (n + 1 - k) * (n + 1).choose k) •
            P.eval ((r : ℚ) + k • (1 : ℚ))) =
        (-1 : ℚ) ^ (r + n + 1) * (2 ^ (n + 1) - 1) := by
    calc
      _ = ∑ k ∈ Finset.range (n + 1),
          ((-1 : ℤ) ^ (n + 1 - k) * (n + 1).choose k) •
            ((-1 : ℚ) ^ (r + k)) := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [show (r : ℚ) + k • (1 : ℚ) =
                ((r + k : ℕ) : ℚ) by norm_num]
              rw [hmatch k hk]
      _ = (-1 : ℚ) ^ (r + n + 1) * (2 ^ (n + 1) - 1) := by
        calc
          _ = ∑ k ∈ Finset.range (n + 1),
              (-1 : ℚ) ^ (r + n + 1) * (n + 1).choose k := by
                apply Finset.sum_congr rfl
                intro k hk
                have hkn : k ≤ n := by
                  simpa using Finset.mem_range.mp hk
                have hpow :
                    (-1 : ℚ) ^ (n + 1 - k) *
                        (-1 : ℚ) ^ (r + k) =
                      (-1 : ℚ) ^ (r + n + 1) := by
                  rw [← pow_add]
                  congr 1
                  omega
                rw [← Int.cast_smul_eq_zsmul ℚ, smul_eq_mul]
                push_cast
                change
                  (-1 : ℚ) ^ (n + 1 - k) * (n + 1).choose k *
                      (-1 : ℚ) ^ (r + k) =
                    (-1 : ℚ) ^ (r + n + 1) * (n + 1).choose k
                calc
                  (-1 : ℚ) ^ (n + 1 - k) * (n + 1).choose k *
                        (-1 : ℚ) ^ (r + k) =
                      ((-1 : ℚ) ^ (n + 1 - k) *
                        (-1 : ℚ) ^ (r + k)) * (n + 1).choose k := by ring
                  _ = _ := by rw [hpow]
          _ = (-1 : ℚ) ^ (r + n + 1) *
              ∑ k ∈ Finset.range (n + 1), (n + 1).choose k := by
                simp only [Nat.cast_sum]
                rw [Finset.mul_sum]
          _ = _ := by
            have hchoose := Nat.sum_range_choose (n + 1)
            rw [Finset.sum_range_succ] at hchoose
            norm_num at hchoose
            have hsumNat :
                (∑ k ∈ Finset.range (n + 1), (n + 1).choose k) =
                  2 ^ (n + 1) - 1 := by omega
            have hpowone : 1 ≤ 2 ^ (n + 1) := by
              simpa using Nat.one_le_pow' (n + 1) 1
            rw [hsumNat, Nat.cast_sub hpowone]
            norm_num
  rw [hknown] at hsplit
  rw [show (r : ℚ) + (n + 1) • (1 : ℚ) =
    ((r + n + 1 : ℕ) : ℚ) by push_cast; ring] at hsplit
  linarith

/-- Adjacent exact parity patches have one forced seam charge at the new endpoint. -/
theorem adjacentParityInterpolants_nextDifference
    (n r : ℕ) (P₀ P₁ : ℚ[X])
    (hdeg₀ : P₀.natDegree ≤ n)
    (hmatch₀ : ∀ k ∈ Finset.range (n + 1),
      P₀.eval ((r + k : ℕ) : ℚ) = (-1 : ℚ) ^ (r + k))
    (hmatch₁ : ∀ k ∈ Finset.range (n + 1),
      P₁.eval ((r + 1 + k : ℕ) : ℚ) = (-1 : ℚ) ^ (r + 1 + k)) :
    P₁.eval ((r + n + 1 : ℕ) : ℚ) -
        P₀.eval ((r + n + 1 : ℕ) : ℚ) =
      (-1 : ℚ) ^ (r + n + 1) * 2 ^ (n + 1) := by
  have hnew := hmatch₁ n (Finset.mem_range.mpr (Nat.lt_succ_self n))
  have hnext :=
    eval_next_of_eval_eq_woldParity_on_adjacent n r P₀ hdeg₀ hmatch₀
  rw [show r + 1 + n = r + n + 1 by omega] at hnew
  rw [hnew, hnext]
  ring

/-- Incidence multiplicity carried by the top falling-factorial channel outside a breadth patch. -/
def woldPatchExcessIncidence (r n t : ℕ) : ℕ :=
  (t - r - 1).descFactorial n

/-- Exact subset-incidence reading of the breadth-patch seam channel. -/
theorem woldPatchExcessIncidence_eq_factorial_mul_choose
    (r n t : ℕ) :
    woldPatchExcessIncidence r n t =
      n.factorial * (t - r - 1).choose n := by
  exact Nat.descFactorial_eq_factorial_mul_choose _ _

/-- The first exterior layer carries one incidence label after factorial normalization. -/
@[simp]
theorem woldPatchExcessIncidence_firstExterior
    (r n : ℕ) :
    woldPatchExcessIncidence r n (r + n + 1) = n.factorial := by
  rw [woldPatchExcessIncidence_eq_factorial_mul_choose]
  have hsub : r + n + 1 - r - 1 = n := by omega
  rw [hsub, Nat.choose_self, mul_one]

end RHTower
