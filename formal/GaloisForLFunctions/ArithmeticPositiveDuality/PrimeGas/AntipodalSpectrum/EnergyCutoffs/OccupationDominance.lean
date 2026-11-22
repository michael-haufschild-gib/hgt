import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum.EnergyCutoffs.AdjacentContrast

/-!
# Optimal replication of consecutive finite occupation counts

The unused coarse occupations count twice the sum of the odd-position
base-C digits of the square-root cutoff. Equality at the first fine shell
fixes the largest possible uniform replication factor.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum

/-- Sum of the upper base-C digits in successive base-C² digits. -/
def oddDigitSum (C X : ℕ) : ℕ := (((C^2).digits X).map (· / C)).sum

private abbrev count (t : ExceptionalTime) (j X : ℕ) := Nat.card (countingStates t j X)

private theorem heat_zero (t : ExceptionalTime) (j X : ℕ) :
    shellCutoff t j X 0 = (count t j X : ℂ) := by
  classical
  letI := Fintype.ofFinite (countingStates t j X)
  simp [shellCutoff,CopyExchange.wordHeat,heat,count,Nat.card_eq_fintype_card,tsum_fintype]

private theorem count_rec (t : ExceptionalTime) (j X : ℕ) :
    count t j X = 2*(X/(tailRadix t j).val)+count t j (X/(tailRadix t j).val) := by
  have hr (Y : ℕ) : radialCutoff Y 0 = (Y:ℂ) := by simp [radialCutoff,Nat.card_Icc]
  have h := shell_cutoff_recursion t j X 0
  simp only [heat_zero,heat,neg_zero,zero_mul,Complex.exp_zero,one_mul,hr] at h
  exact_mod_cast h

private theorem zero_count (t : ExceptionalTime) (j : ℕ) : count t j 0 = 0 := by
  simp [count,count_floor_sum]

private theorem odd_digit_step {C X : ℕ} (hC : 1 < C) (hX : 0 < X) :
    oddDigitSum C X = X/C%C + oddDigitSum C (X/C^2) := by
  rw [oddDigitSum,Nat.digits_def' (one_lt_pow₀ hC (by norm_num : (2:ℕ) ≠ 0)) hX]
  simp only [List.map_cons,List.sum_cons]
  exact congrArg (· + oddDigitSum C (X/C^2)) (by rw [pow_two,Nat.mod_mul_right_div_self])

/-- Exact number of coarse occupations left after C+1 copies of the finer cutoff. -/
theorem adjacent_count_digit_identity (t : ExceptionalTime) (j X : ℕ) :
    let C := (tailRadix t j).val
    Nat.card (countingStates t j X) =
      (C+1)*Nat.card (countingStates t (j+1) X)+2*oddDigitSum C X := by
  let C := (tailRadix t j).val
  have hC : 1 < C := radix_gt_one t j
  have hB : (tailRadix t (j+1)).val = C^2 := congrArg PNat.val (tailRadix_succ t j)
  change count t j X = (C+1)*count t (j+1) X+2*oddDigitSum C X
  induction X using Nat.strong_induction_on with
  | h X ih =>
    rcases Nat.eq_zero_or_pos X with rfl | hX
    · simp [zero_count,oddDigitSum]
    let Y := X/C
    let Z := X/C^2
    have hy : Y/C = Z := by change X/C/C = X/C^2; rw [Nat.div_div_eq_div_mul,pow_two]
    have hi := ih Z (Nat.div_lt_self hX (one_lt_pow₀ hC (by norm_num : (2:ℕ) ≠ 0)))
    have hmm := Nat.mod_add_div Y C
    rw [hy] at hmm
    have h₁ := count_rec t j X
    have h₂ := count_rec t j Y
    have h₃ := count_rec t (j+1) X
    change count t j X = 2*Y+count t j Y at h₁
    change count t j Y = 2*(Y/C)+count t j (Y/C) at h₂
    rw [hy] at h₂
    rw [hB] at h₃
    change count t (j+1) X = 2*Z+count t (j+1) Z at h₃
    rw [h₁,h₂,hi,h₃,odd_digit_step hC hX]
    change 2*Y+(2*Z+((C+1)*count t (j+1) Z+2*oddDigitSum C Z)) =
      (C+1)*(2*Z+count t (j+1) Z)+2*(Y%C+oddDigitSum C Z)
    nlinarith only [hmm]

private theorem quotient_sum_zero (C : ℕ) (hC : 0 < C) (ds : List ℕ) :
    (ds.map (·/C)).sum = 0 ↔ ∀ d ∈ ds, d < C := by
  induction ds with
  | nil => simp
  | cons d ds ih => simp [Nat.add_eq_zero_iff,Nat.div_eq_zero_iff_lt hC,ih]

/-- Equality holds precisely when every base-C² digit belongs to the lower C digits. -/
theorem adjacent_count_equality (t : ExceptionalTime) (j X : ℕ) :
    let C := (tailRadix t j).val
    Nat.card (countingStates t j X) = (C+1)*Nat.card (countingStates t (j+1) X) ↔
      ∀ d ∈ (C^2).digits X, d < C := by
  let C := (tailRadix t j).val
  have h := adjacent_count_digit_identity t j X
  change count t j X = (C+1)*count t (j+1) X+2*oddDigitSum C X at h
  change count t j X = (C+1)*count t (j+1) X ↔ _
  rw [← quotient_sum_zero C (tailRadix t j).pos]
  change _ ↔ oddDigitSum C X = 0
  omega

/-- Testing the first occupied fine shell already forces the optimal replication factor. -/
theorem adjacent_count_maximal (t : ExceptionalTime) (j k : ℕ) :
    (∀ X, k*Nat.card (countingStates t (j+1) X) ≤ Nat.card (countingStates t j X)) ↔
      k ≤ (tailRadix t j).val+1 := by
  let C := (tailRadix t j).val
  let B := (tailRadix t (j+1)).val
  have hb : 1 < B := radix_gt_one t (j+1)
  have hB : B = C^2 := congrArg PNat.val (tailRadix_succ t j)
  constructor
  · intro h
    have ho : oddDigitSum C B = 0 := by
      rw [odd_digit_step (radix_gt_one t j) (by omega : 0 < B),← hB,Nat.div_self (by omega : 0 < B)]
      have hc : 1 < C := radix_gt_one t j
      have hdiv : B/C = C := by rw [hB,pow_two,Nat.mul_div_cancel_left _ (by omega)]
      rw [hdiv,Nat.mod_self,zero_add]
      have hc₂ : 1 < C^2 := hB ▸ hb
      rw [odd_digit_step hc (X := 1) zero_lt_one]
      simp [Nat.div_eq_of_lt hc,Nat.div_eq_of_lt hc₂,oddDigitSum]
    have hf : 0 < count t (j+1) B := by
      have hh := count_rec t (j+1) B
      change count t (j+1) B = 2*(B/B)+count t (j+1) (B/B) at hh
      rw [Nat.div_self (by omega : 0 < B)] at hh
      omega
    have he := adjacent_count_digit_identity t j B
    change count t j B = (C+1)*count t (j+1) B+2*oddDigitSum C B at he
    simp only [ho,mul_zero,add_zero] at he
    exact (Nat.le_of_mul_le_mul_right (by simpa only [he] using h B) hf)
  · intro hk X
    exact (Nat.mul_le_mul_right _ hk).trans
      (by rw [adjacent_count_digit_identity t j X]; exact Nat.le_add_right _ _)

#print axioms adjacent_count_digit_identity
#print axioms adjacent_count_equality
#print axioms adjacent_count_maximal

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.AntipodalSpectrum
