import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Intersection.SignedConductorDivisors
import GaloisForLFunctions.RHTower.QuasiRHQuotientHeadAndFiniteContactAbscissaLaw

/-!
# The finite part of a mixed integral graph intersection

Write an upper divisor by its signed endpoint jumps. A lower graph i and an
upper endpoint j meet at all ratios up to j/i. The continuum degree factors,
while the fractional part of j/i is an exact boundary correction. After paying
this correction, all pairs with the same integer quotient have a single coefficient.
-/

noncomputable section

namespace GaloisForLFunctions.SignedArithmeticCorrespondences
open ArithmeticCastelnuovoSeveri Finset _root_.RHTower
open scoped ArithmeticFunction.vonMangoldt

/-- Multiplicity at m of an upper divisor given by its jumps at j. -/
def upperDivisor (N : ℕ) (b : ℕ → ℤ) (m : ℕ) : ℤ :=
  ∑ j ∈ Icc 1 N, if m ≤ j then b j else 0

/-- Every upper divisor cut at N has an integral endpoint presentation,
including the terminal jump back to zero. -/
theorem exists_upper_endpoints (N : ℕ) (v : ℕ → ℤ) :
    ∃ b : ℕ → ℤ, ∀ m : ℕ, 1 ≤ m → upperDivisor N b m = if m ≤ N then v m else 0 := by
  let w (j : ℕ) := if j ≤ N then v j else 0
  refine ⟨fun j => w j-w (j+1), fun m hm => ?_⟩
  unfold upperDivisor
  rw [← sum_filter]
  have hset : (Icc 1 N).filter (fun j => m ≤ j) = Icc m N := by
    ext j
    simp only [mem_filter,mem_Icc]
    omega
  rw [hset]
  by_cases h : m ≤ N
  · have ht (k : ℕ) (hk : m ≤ k) :
        ∑ j ∈ Icc m k, (w j-w (j+1)) = w m - w (k+1) := by
      induction k, hk using Nat.le_induction with
      | base => simp
      | succ k hk ih =>
        rw [sum_Icc_succ_top (Nat.le_succ_of_le hk),ih]
        abel
    simpa [w,h] using ht N h
  · simp [Icc_eq_empty_of_lt (lt_of_not_ge h),h]

/-- Total signed multiplicity of pairs terminating in the same quotient cell. -/
def quotientCoefficient (X N : ℕ) (u b : ℕ → ℤ) (k : ℕ) : ℝ :=
  ∑ i ∈ Icc 1 X, ∑ j ∈ Icc 1 N, if j/i = k then (u i : ℝ)*b j else 0

/-- Product of the two endpoint degrees, obtained by integrating unit density in the ratio. -/
def poleProduct (X N : ℕ) (u b : ℕ → ℤ) : ℝ :=
  (∑ i ∈ Icc 1 X, (u i : ℝ)/i) * ∑ j ∈ Icc 1 N, (b j : ℝ)*j

/-- Signed mass between the rational endpoint and its last integral ratio. -/
def fractionalBoundary (X N : ℕ) (u b : ℕ → ℤ) : ℝ :=
  ∑ i ∈ Icc 1 X, ∑ j ∈ Icc 1 N, (u i : ℝ)*b j*((j : ℝ)/i - (j/i : ℕ))

/-- Each signed upper endpoint cuts the prime-power ratio sum at its integer quotient. -/
theorem height_eq_quotient (X N : ℕ) (u b : ℕ → ℤ) :
    signedDivisorHeight 1 X N u (upperDivisor N b) =
      ∑ i ∈ Icc 1 X, ∑ j ∈ Icc 1 N, (u i : ℝ)*b j*chebyshevPsi (j/i) := by
  rw [signedDivisorHeight_eq Nat.zero_lt_one]
  refine sum_congr rfl fun i hi => ?_
  have hi' := (mem_Icc.mp hi).1
  have hrow (q : ℕ) :
      (u i : ℝ)*(upperDivisor N b (i*q) : ℝ)*Λ q =
        ∑ j ∈ Icc 1 N, (u i : ℝ)*b j*(if q ≤ j/i then Λ q else 0) := by
    simp only [upperDivisor, Int.cast_sum, mul_sum, sum_mul]
    refine sum_congr rfl fun j _ => ?_
    by_cases h : q ≤ j/i
    · have h' : i*q ≤ j := by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hi').mp h
      simp only [if_pos h, if_pos h']
    · have h' : ¬ i*q ≤ j := fun hq => h ((Nat.le_div_iff_mul_le hi').mpr (by simpa [Nat.mul_comm] using hq))
      simp only [if_neg h, if_neg h', Int.cast_zero, mul_zero, zero_mul]
  simp_rw [hrow]
  rw [sum_comm]
  refine sum_congr rfl fun j hj => ?_
  rw [← mul_sum, ← sum_filter]
  have hset : (Icc 1 N).filter (fun q => q ≤ j/i) = Icc 1 (j/i) := by
    ext q
    simp only [mem_filter, mem_Icc]
    have hle := (Nat.div_le_self j i).trans (mem_Icc.mp hj).2
    omega
  rw [hset]
  rfl

private theorem glue_quotients (X N : ℕ) (u b : ℕ → ℤ) (F : ℕ → ℝ) :
    ∑ k ∈ range (N+1), quotientCoefficient X N u b k * F k =
      ∑ i ∈ Icc 1 X, ∑ j ∈ Icc 1 N, (u i : ℝ)*b j*F (j/i) := by
  simp only [quotientCoefficient, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun j hj => ?_
  have hj' : j/i < N+1 := Nat.lt_succ_of_le ((Nat.div_le_self j i).trans (mem_Icc.mp hj).2)
  simp [ite_mul, hj', eq_comm]

/-- The boundary-corrected signed height is exactly the Chebyshev error paired
with the glued quotient endpoints. This includes endpoints below the first contact. -/
theorem mixed_height_finite_part (X N : ℕ) (u b : ℕ → ℤ) :
    signedDivisorHeight 1 X N u (upperDivisor N b) - poleProduct X N u b +
      fractionalBoundary X N u b =
      ∑ k ∈ range (N+1), quotientCoefficient X N u b k * psiRemainder k := by
  rw [height_eq_quotient, glue_quotients]
  simp only [poleProduct, fractionalBoundary, sum_mul, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  unfold psiRemainder
  ring

private theorem single_endpoint {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    quotientCoefficient 1 m (fun _ => 1) (fun j => if j=m then 1 else 0) k =
      if m=k then 1 else 0 := by
  simp only [quotientCoefficient, Icc_self, sum_singleton, Nat.div_one, Int.cast_one, one_mul]
  have h (j : ℕ) :
      (if j=k then ((if j=m then 1 else 0 : ℤ) : ℝ) else 0) =
        if j=m then (if m=k then 1 else 0) else 0 := by
    by_cases hj : j=m
    · subst j
      simp
    · simp [hj]
  simp only [h]
  simp [hm]

/-- The optimal loss for *all* mixed integer divisors is exactly the scalar
Chebyshev loss. A single effective upper endpoint realizes every nonzero
quotient atom, with the same constant and no loss at a support boundary. -/
theorem mixed_height_budget_iff (W : ℕ → ℝ≥0) (C : ℝ≥0) :
    (∀ (X N : ℕ) (u b : ℕ → ℤ),
      |signedDivisorHeight 1 X N u (upperDivisor N b) - poleProduct X N u b +
        fractionalBoundary X N u b| ≤
        C * ∑ k ∈ range (N+1), |quotientCoefficient X N u b k| * (W k : ℝ)) ↔
      ∀ k : ℕ, 1 ≤ k → |psiRemainder k| ≤ C * (W k : ℝ) := by
  simp only [mixed_height_finite_part]
  constructor
  · intro h m hm
    have he := h 1 m (fun _ => 1) (fun j => if j=m then 1 else 0)
    simp only [single_endpoint hm] at he
    simpa [apply_ite, ite_mul] using he
  · intro h X N u b
    rw [mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k _ => ?_)
    rw [abs_mul, mul_left_comm]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    cases k with
    | zero => simp [psiRemainder, chebyshevPsi, mul_nonneg C.coe_nonneg (W 0).coe_nonneg]
    | succ k => exact h _ (Nat.succ_pos _)

/-- One constant works for every support and both integer divisors. The variation
is measured after cancellation between all pairs sharing a quotient. -/
theorem mixed_height_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X N : ℕ) (u b : ℕ → ℤ),
      |signedDivisorHeight 1 X N u (upperDivisor N b) - poleProduct X N u b +
        fractionalBoundary X N u b| ≤
      C * ∑ k ∈ range (N+1), |quotientCoefficient X N u b k| * (k : ℝ)^(zetaZeroAbscissa+ε) := by
  obtain ⟨C,hC,hbound⟩ := exists_psiRemainder_le_rpow_zetaZeroAbscissa ε hε
  exact ⟨C,hC,(mixed_height_budget_iff
    (fun k => ⟨_, Real.rpow_nonneg (Nat.cast_nonneg k) _⟩) ⟨C,hC⟩).2 hbound⟩

/-- A completed endpoint profile can have infinitely many signed jumps.
The same constant controls its pairing with the Chebyshev error at every
cutoff. The resulting series is absolutely convergent in weighted variation. -/
theorem completed_endpoint_budget (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℕ → ℝ,
      Summable (fun k => |a k|*(k : ℝ)^(zetaZeroAbscissa+ε)) →
      Summable (fun k => a k*psiRemainder k) ∧
      |∑' k, a k*psiRemainder k| ≤ C * ∑' k, |a k|*(k : ℝ)^(zetaZeroAbscissa+ε) := by
  obtain ⟨C,hC,hbound⟩ := exists_psiRemainder_le_rpow_zetaZeroAbscissa ε hε
  refine ⟨C,hC,fun a ha => ?_⟩
  have hterm (k : ℕ) : ‖a k*psiRemainder k‖ ≤ C * (|a k|*(k : ℝ)^(zetaZeroAbscissa+ε)) := by
    rw [Real.norm_eq_abs, abs_mul, mul_left_comm]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [psiRemainder, chebyshevPsi]
      simp only [Icc_eq_empty_of_lt Nat.zero_lt_one, sum_empty, Nat.cast_zero, sub_zero, abs_zero]
      exact mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)
    · exact hbound _ hk
  have hmajor := ha.mul_left C
  have hsum : Summable (fun k => a k*psiRemainder k) := Summable.of_norm_bounded hmajor hterm
  refine ⟨hsum, ?_⟩
  rw [← Real.norm_eq_abs, ← tsum_mul_left]
  exact (norm_tsum_le_tsum_norm hsum.norm).trans (hsum.norm.tsum_le_tsum hterm hmajor)

/-- The exact support of the mixed quotient coefficients lies below the largest
upper endpoint, independently of the number of lower graphs. -/
private theorem quotientCoefficient_eq_zero {N k : ℕ} (hk : N < k) (X : ℕ) (u b : ℕ → ℤ) :
    quotientCoefficient X N u b k = 0 := by
  refine sum_eq_zero fun i _ => sum_eq_zero fun j hj => ?_
  exact if_neg (ne_of_lt (((Nat.div_le_self j i).trans (mem_Icc.mp hj).2).trans_lt hk))

/-- Distance from a finite integral intersection to a prescribed infinite
endpoint profile. The right side prices only the variation left after gluing.
This gives convergence along every exhaustion approaching the same profile
in weighted variation, with one constant for both supports. -/
theorem distance_to_completed_intersection (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X N : ℕ) (u b : ℕ → ℤ) (a : ℕ → ℝ),
      Summable (fun k => |a k|*(k : ℝ)^(zetaZeroAbscissa+ε)) →
      let c := quotientCoefficient X N u b
      |signedDivisorHeight 1 X N u (upperDivisor N b) - poleProduct X N u b +
        fractionalBoundary X N u b - ∑' k, a k*psiRemainder k| ≤
        C * ∑' k, |c k-a k|*(k : ℝ)^(zetaZeroAbscissa+ε) := by
  obtain ⟨C,hC,hpair⟩ := completed_endpoint_budget ε hε
  refine ⟨C,hC,fun X N u b a ha => ?_⟩
  let c := quotientCoefficient X N u b
  have hc {k : ℕ} (hk : k ∉ range (N+1)) : c k = 0 :=
    quotientCoefficient_eq_zero (by simpa only [mem_range,not_lt,Nat.succ_le_iff] using hk) X u b
  have hcw : Summable (fun k => |c k|*(k : ℝ)^(zetaZeroAbscissa+ε)) :=
    summable_of_ne_finset_zero (s := range (N+1)) fun k hk => by simp [hc hk]
  have hce := (hpair c hcw).1
  have hae := (hpair a ha).1
  have hdiff : Summable (fun k => |c k-a k|*(k : ℝ)^(zetaZeroAbscissa+ε)) := by
    apply Summable.of_nonneg_of_le (fun k => mul_nonneg (abs_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)) _ (hcw.add ha)
    intro k
    simpa only [Pi.add_apply, ← add_mul] using
      mul_le_mul_of_nonneg_right (abs_sub (c k) (a k)) (Real.rpow_nonneg (Nat.cast_nonneg k) (zetaZeroAbscissa+ε))
  have h := (hpair (fun k => c k-a k) hdiff).2
  have he : (∑' k, c k*psiRemainder k) = ∑ k ∈ range (N+1), c k*psiRemainder k :=
    tsum_eq_sum fun k hk => by simp only [hc hk,zero_mul]
  rw [mixed_height_finite_part]
  change |(∑ k ∈ range (N+1), c k*psiRemainder k) - _| ≤ _
  rw [← he,← hce.tsum_sub hae]
  simpa only [sub_mul] using h

#print axioms distance_to_completed_intersection
#print axioms completed_endpoint_budget
#print axioms height_eq_quotient
#print axioms mixed_height_budget_iff
#print axioms mixed_height_finite_part
#print axioms mixed_height_bound

end GaloisForLFunctions.SignedArithmeticCorrespondences
