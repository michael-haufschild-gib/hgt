import GaloisForLFunctions.SignedArithmeticEnergyIncidence.ChainLendingAndTrainCapacity

/-!
# Exceptional chains and their exact boundary energy

The negative of the split exceptional intersection matrix has diagonal entries
`2, …, 2, p + 2` and adjacent entries `-1`. Its square decomposition is the
identity in Lemma 3.14 of https://arxiv.org/abs/2610.40335. Here it acts on the
signed-incidence chain. Eliminating its interior gives the exact
boundary coefficient `(p² + p + 1) / p`, attained by the linear ramp.
-/

open Finset
noncomputable section
namespace GaloisForLFunctions.SignedArithmeticEnergyIncidence

/-- Positive energy of the exceptional chain of length `n + 1`. -/
def exceptionalChainEnergy (n : ℕ) (f : ℕ → ℝ) : ℝ :=
  incidenceEnergy (chainCoupling (n + 1)
    (fun k => 2 + if k = n then (n : ℝ) + 1 else 0) (fun _ => -1)) (fun k => f k)

/-- Successive increments from a pinned zero immediately before the chain. -/
def pinnedIncrement (f : ℕ → ℝ) : ℕ → ℝ
  | 0 => f 0
  | k + 1 => f (k + 1) - f k

/-- Matrix expansion of the exceptional intersection energy. -/
theorem exceptionalChainEnergy_expansion (n : ℕ) (f : ℕ → ℝ) :
    exceptionalChainEnergy n f =
      2 * ∑ k ∈ range (n + 1), f k ^ 2 -
      2 * ∑ k ∈ range n, f k * f (k + 1) + ((n : ℝ) + 1) * f n ^ 2 := by
  rw [exceptionalChainEnergy, incidenceEnergy_chainCoupling]
  simp only [add_mul, sum_add_distrib, ← mul_sum, neg_one_mul, neg_mul,
    sum_neg_distrib, ite_mul, zero_mul, sum_ite_eq', mem_range, Nat.lt_succ_self, if_true]
  ring

/-- Telescoping identifies the total increment with the terminal value. -/
theorem sum_pinnedIncrement (n : ℕ) (f : ℕ → ℝ) :
    ∑ k ∈ range (n + 1), pinnedIncrement f k = f n := by
  induction n with
  | zero => simp [pinnedIncrement]
  | succ n ih => rw [sum_range_succ, ih, pinnedIncrement]; ring

/-- The exceptional matrix is a pinned difference energy plus a terminal penalty. -/
theorem exceptionalChainEnergy_squares (n : ℕ) (f : ℕ → ℝ) :
    exceptionalChainEnergy n f =
      (∑ k ∈ range (n + 1), pinnedIncrement f k ^ 2) + ((n : ℝ) + 2) * f n ^ 2 := by
  rw [exceptionalChainEnergy_expansion]
  have h : 2 * ∑ k ∈ range (n + 1), f k ^ 2 -
      2 * ∑ k ∈ range n, f k * f (k + 1) =
      (∑ k ∈ range (n + 1), pinnedIncrement f k ^ 2) + f n ^ 2 := by
    induction n with
    | zero => simp [pinnedIncrement]; ring
    | succ n ih =>
      rw [sum_range_succ (fun k => f k ^ 2), sum_range_succ (fun k => f k * f (k + 1)),
        sum_range_succ (fun k => pinnedIncrement f k ^ 2), pinnedIncrement]
      nlinarith only [ih]
  rw [h]
  ring

/-- The original endpoint-and-differences form of the intersection identity. -/
theorem exceptionalChainEnergy_adjacent_squares (n : ℕ) (f : ℕ → ℝ) :
    exceptionalChainEnergy n f = f 0 ^ 2 +
      (∑ k ∈ range n, (f k - f (k + 1)) ^ 2) + ((n : ℝ) + 2) * f n ^ 2 := by
  rw [exceptionalChainEnergy_squares, sum_range_succ']
  simp only [pinnedIncrement]
  have h : (∑ k ∈ range n, (f (k + 1) - f k) ^ 2) =
      ∑ k ∈ range n, (f k - f (k + 1)) ^ 2 :=
    sum_congr rfl fun _ _ => by ring
  rw [h]
  ring

/-- Eliminating the interior leaves a sum of squares around the linear ramp. -/
theorem exceptionalChainEnergy_boundary_decomposition (n : ℕ) (f : ℕ → ℝ) :
    exceptionalChainEnergy n f =
      (∑ k ∈ range (n + 1), (pinnedIncrement f k - f n / ((n : ℝ) + 1)) ^ 2) +
      (((n : ℝ) + 2) + 1 / ((n : ℝ) + 1)) * f n ^ 2 := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hsum : (∑ k ∈ range (n + 1),
      (pinnedIncrement f k - f n / ((n : ℝ) + 1)) ^ 2) =
      (∑ k ∈ range (n + 1), pinnedIncrement f k ^ 2) -
      2 * (f n / ((n : ℝ) + 1)) * f n +
      ((n : ℝ) + 1) * (f n / ((n : ℝ) + 1)) ^ 2 := by
    simp_rw [sub_sq]
    simp only [sum_add_distrib, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul,
      Nat.cast_add, Nat.cast_one]
    rw [show (∑ k ∈ range (n + 1), 2 * pinnedIncrement f k * (f n / ((n : ℝ) + 1))) =
      2 * (f n / ((n : ℝ) + 1)) * ∑ k ∈ range (n + 1), pinnedIncrement f k from by
        rw [mul_sum]; exact sum_congr rfl fun _ _ => by ring, sum_pinnedIncrement]
  rw [exceptionalChainEnergy_squares, hsum]
  field_simp
  <;> ring

/-- The effective terminal coefficient is the quotient of the chain discriminant by its length. -/
theorem exceptionalChainEnergy_boundary_bound (n : ℕ) (f : ℕ → ℝ) :
    (((n : ℝ) + 2) + 1 / ((n : ℝ) + 1)) * f n ^ 2 ≤ exceptionalChainEnergy n f := by
  rw [exceptionalChainEnergy_boundary_decomposition]
  exact le_add_of_nonneg_left (sum_nonneg fun _ _ => sq_nonneg _)

/-- Equality in the terminal bound forces every pinned increment to be equal. -/
theorem exceptionalChainEnergy_boundary_eq_iff (n : ℕ) (f : ℕ → ℝ) :
    exceptionalChainEnergy n f =
      (((n : ℝ) + 2) + 1 / ((n : ℝ) + 1)) * f n ^ 2 ↔
      ∀ k ≤ n, pinnedIncrement f k = f n / ((n : ℝ) + 1) := by
  rw [exceptionalChainEnergy_boundary_decomposition, add_eq_right]
  rw [sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg
    (pinnedIncrement f k - f n / ((n : ℝ) + 1)))]
  simp only [mem_range, Nat.lt_succ_iff, sq_eq_zero_iff, sub_eq_zero]

/-- The exceptional chain is positive definite on its finite coordinate space. -/
theorem exceptionalChainEnergy_zero_iff (n : ℕ) (f : ℕ → ℝ) :
    exceptionalChainEnergy n f = 0 ↔ ∀ k ≤ n, f k = 0 := by
  constructor
  · intro h
    have hs : 0 ≤ ∑ k ∈ range (n + 1), pinnedIncrement f k ^ 2 :=
      sum_nonneg fun k _ => sq_nonneg _
    have ht : 0 ≤ ((n : ℝ) + 2) * f n ^ 2 := mul_nonneg (by positivity) (sq_nonneg _)
    have hz : (∑ k ∈ range (n + 1), pinnedIncrement f k ^ 2) = 0 := by
      rw [exceptionalChainEnergy_squares] at h
      linarith only [h, hs, ht]
    have hj : ∀ k ≤ n, pinnedIncrement f k = 0 := by
      have hh := (sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (pinnedIncrement f k))).mp hz
      intro k hk
      exact sq_eq_zero_iff.mp (hh k (mem_range.mpr (by omega)))
    intro k hk
    rw [← sum_pinnedIncrement k f]
    exact sum_eq_zero fun j h => hj j (by have := mem_range.mp h; omega)
  · intro h
    rw [exceptionalChainEnergy_expansion]
    have hs : (∑ k ∈ range (n + 1), f k ^ 2) = 0 :=
      sum_eq_zero fun k hk => by rw [h k (by have := mem_range.mp hk; omega)]; ring
    have he : (∑ k ∈ range n, f k * f (k + 1)) = 0 :=
      sum_eq_zero fun k hk => by rw [h k (by have := mem_range.mp hk; omega), zero_mul]
    rw [hs, he, h n le_rfl]
    ring

/-- The ramp with prescribed terminal value. -/
def exceptionalChainRamp (n : ℕ) (t : ℝ) (k : ℕ) : ℝ :=
  ((k : ℝ) + 1) * t / ((n : ℝ) + 1)

theorem pinnedIncrement_exceptionalChainRamp (n : ℕ) (t : ℝ) (k : ℕ) :
    pinnedIncrement (exceptionalChainRamp n t) k = t / ((n : ℝ) + 1) := by
  cases k with
  | zero => simp [pinnedIncrement, exceptionalChainRamp]
  | succ k => simp only [pinnedIncrement, exceptionalChainRamp, Nat.cast_add, Nat.cast_one]; ring

/-- The linear ramp is the unique minimizing profile at each prescribed terminal value. -/
theorem exceptionalChainEnergy_minimizers (n : ℕ) (f : ℕ → ℝ) :
    exceptionalChainEnergy n f =
      (((n : ℝ) + 2) + 1 / ((n : ℝ) + 1)) * f n ^ 2 ↔
      ∀ k ≤ n, f k = exceptionalChainRamp n (f n) k := by
  rw [exceptionalChainEnergy_boundary_eq_iff]
  constructor
  · intro h k hk
    rw [← sum_pinnedIncrement k f]
    have he : (∑ j ∈ range (k + 1), pinnedIncrement f j) =
        ∑ _j ∈ range (k + 1), f n / ((n : ℝ) + 1) :=
      sum_congr rfl fun j hj => h j (by have := mem_range.mp hj; omega)
    rw [he]
    simp only [sum_const, card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one,
      exceptionalChainRamp]
    ring
  · intro h k hk
    cases k with
    | zero =>
      rw [pinnedIncrement, h 0 (by omega)]
      simp [exceptionalChainRamp]
    | succ k =>
      rw [pinnedIncrement, h (k + 1) hk, h k (by omega)]
      simp only [exceptionalChainRamp, Nat.cast_add, Nat.cast_one]
      ring

/-- Every terminal value attains the effective boundary energy. -/
theorem exceptionalChainEnergy_ramp (n : ℕ) (t : ℝ) :
    exceptionalChainEnergy n (exceptionalChainRamp n t) =
      (((n : ℝ) + 2) + 1 / ((n : ℝ) + 1)) * t ^ 2 := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have hend : exceptionalChainRamp n t n = t := by
    unfold exceptionalChainRamp
    exact mul_div_cancel_left₀ t hn
  rw [exceptionalChainEnergy_boundary_decomposition, hend]
  simp only [pinnedIncrement_exceptionalChainRamp, sub_self, zero_pow (by omega : 2 ≠ 0),
    sum_const_zero, zero_add]

/-- Eliminating toward the opposite endpoint exposes a different boundary coefficient. -/
theorem exceptionalChainEnergy_head_decomposition (n : ℕ) (f : ℕ → ℝ) :
    exceptionalChainEnergy n f =
      (∑ k ∈ range n,
        (f (k + 1) - f k + ((n : ℝ) + 2) / ((n : ℝ) + 1) ^ 2 * f 0) ^ 2) +
      ((n : ℝ) + 2) * (f n - f 0 / ((n : ℝ) + 1) ^ 2) ^ 2 +
      (1 + ((n : ℝ) + 2) / ((n : ℝ) + 1) ^ 2) * f 0 ^ 2 := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have ht : (∑ k ∈ range n, (f (k + 1) - f k)) = f n - f 0 :=
    sum_range_sub f n
  let c := ((n : ℝ) + 2) / ((n : ℝ) + 1) ^ 2 * f 0
  have he : (∑ k ∈ range n, (f (k + 1) - f k + c) ^ 2) =
      (∑ k ∈ range n, (f k - f (k + 1)) ^ 2) +
      2 * c * (f n - f 0) + (n : ℝ) * c ^ 2 := by
    calc
      _ = ∑ k ∈ range n, ((f k - f (k + 1)) ^ 2 +
            2 * c * (f (k + 1) - f k) + c ^ 2) :=
        sum_congr rfl fun _ _ => by ring
      _ = _ := by rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ht, sum_const,
          card_range, nsmul_eq_mul]
  change exceptionalChainEnergy n f =
    (∑ k ∈ range n, (f (k + 1) - f k + c) ^ 2) + _ + _
  rw [he, exceptionalChainEnergy_adjacent_squares]
  dsimp only [c]
  field_simp
  <;> ring

/-- The effective coefficient at the first coordinate is `1 + (p + 1) / p²`. -/
theorem exceptionalChainEnergy_head_bound (n : ℕ) (f : ℕ → ℝ) :
    (1 + ((n : ℝ) + 2) / ((n : ℝ) + 1) ^ 2) * f 0 ^ 2 ≤ exceptionalChainEnergy n f := by
  rw [exceptionalChainEnergy_head_decomposition]
  have hs : 0 ≤ ∑ k ∈ range n,
      (f (k + 1) - f k + ((n : ℝ) + 2) / ((n : ℝ) + 1) ^ 2 * f 0) ^ 2 :=
    sum_nonneg fun _ _ => sq_nonneg _
  have ht : 0 ≤ ((n : ℝ) + 2) * (f n - f 0 / ((n : ℝ) + 1) ^ 2) ^ 2 :=
    mul_nonneg (by positivity) (sq_nonneg _)
  linarith only [hs, ht]

/-- The descending affine profile minimizing energy at the first coordinate. -/
def exceptionalChainHeadRamp (n : ℕ) (t : ℝ) (k : ℕ) : ℝ :=
  (1 - ((k : ℝ) * ((n : ℝ) + 2)) / ((n : ℝ) + 1) ^ 2) * t

/-- The head bound is attained for every prescribed first-coordinate value. -/
theorem exceptionalChainEnergy_head_ramp (n : ℕ) (t : ℝ) :
    exceptionalChainEnergy n (exceptionalChainHeadRamp n t) =
      (1 + ((n : ℝ) + 2) / ((n : ℝ) + 1) ^ 2) * t ^ 2 := by
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have h0 : exceptionalChainHeadRamp n t 0 = t := by simp [exceptionalChainHeadRamp]
  have hend : exceptionalChainHeadRamp n t n = t / ((n : ℝ) + 1) ^ 2 := by
    unfold exceptionalChainHeadRamp
    field_simp
    <;> ring
  have hj (k : ℕ) : exceptionalChainHeadRamp n t (k + 1) - exceptionalChainHeadRamp n t k +
      ((n : ℝ) + 2) / ((n : ℝ) + 1) ^ 2 * t = 0 := by
    simp only [exceptionalChainHeadRamp, Nat.cast_add, Nat.cast_one]
    ring
  rw [exceptionalChainEnergy_head_decomposition, h0, hend]
  simp only [hj, sub_self, zero_pow (by omega : 2 ≠ 0), sum_const_zero, mul_zero,
    add_zero, zero_add]

/-- The sharp path bound also controls the entire exceptional-chain mass. -/
theorem exceptionalChainEnergy_coercive (n : ℕ) (f : ℕ → ℝ) :
    (2 - 2 * Real.cos (Real.pi / ((n : ℝ) + 2))) *
      (∑ k ∈ range (n + 1), f k ^ 2) + ((n : ℝ) + 1) * f n ^ 2 ≤
      exceptionalChainEnergy n f := by
  rw [exceptionalChainEnergy_expansion]
  have h := uniformTrain_capacity n f
  nlinarith only [h]

#print axioms exceptionalChainEnergy_boundary_decomposition
#print axioms exceptionalChainEnergy_zero_iff
#print axioms exceptionalChainEnergy_boundary_eq_iff
#print axioms exceptionalChainEnergy_minimizers
#print axioms exceptionalChainEnergy_ramp
#print axioms exceptionalChainEnergy_head_decomposition
#print axioms exceptionalChainEnergy_head_ramp
#print axioms exceptionalChainEnergy_coercive

end GaloisForLFunctions.SignedArithmeticEnergyIncidence
