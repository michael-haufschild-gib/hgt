import GaloisForLFunctions.ExceptionalLayerTheory.TheCompletedCofactorRowRetainsThePrimeError
import GaloisForLFunctions.RHTower.MoebiusFloorSummatory
import GaloisForLFunctions.RHTower.ReciprocalSawtoothGate

/-!
# The signed prime count between two moving cutoffs

Möbius inversion represents the constant one through height `L` by a sum
of bounded floor remainders. When paired with the actual prime excess,
each remainder is a difference of two complete divisor rows whose linear
terms cancel up to one residue. This pays the part of the prime count
outside a middle interval, uniformly in both of its cutoffs.
-/

noncomputable section

open Finset ArithmeticFunction
open RHTower.Sieve

namespace GaloisForLFunctions.ExceptionalLayerTheory

private abbrev excess := vonMangoldt - (zeta : ArithmeticFunction ℝ)
private abbrev mu (d : ℕ) : ℝ := ((moebius d : ℤ) : ℝ)

private def radix (L d : ℕ) := L / d + 1

private theorem abs_nat_real (n : ℕ) : |(n : ℝ)| = n := abs_of_nonneg (Nat.cast_nonneg n)

/-- A bounded combination of Euclidean remainders, equal to one through height `L`. -/
def mobiusRemainderPrefix (L t : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 L, mu d * (((t / d) % radix L d : ℕ) : ℝ)

/-- Total cost of rounding the divisor rows. -/
def remainderMass (L : ℕ) : ℝ := ∑ d ∈ Icc 1 L, (1 + (radix L d : ℝ))

private theorem mu_bound (L d : ℕ) (hd : d ∈ Icc 1 L) : |mu d| ≤ 1 := by
  simpa only [truncAF_apply, if_pos (mem_Icc.mp hd).2, ArithmeticFunction.intCoe_apply] using
    abs_truncAF_moebius_le_one L d

theorem mobiusRemainderPrefix_eq_one {t L : ℕ} (ht : 1 ≤ t) (hL : t ≤ L) :
    mobiusRemainderPrefix L t = 1 := by
  unfold mobiusRemainderPrefix
  rw [← sum_subset (f := fun d => mu d * (((t/d) % radix L d : ℕ) : ℝ))
    (Icc_subset_Icc_right hL) (by
    intro d hd hnot
    have hgt : t < d := by
      by_contra! h
      exact hnot (mem_Icc.mpr ⟨(mem_Icc.mp hd).1, h⟩)
    simp [Nat.div_eq_of_lt hgt])]
  rw [← RHTower.moebius_floor_summatory t ht]
  apply sum_congr rfl
  intro d _
  rw [Nat.mod_eq_of_lt (show t/d < radix L d from Nat.lt_succ_of_le (Nat.div_le_div_right hL))]

private theorem abs_prefix_le (L t : ℕ) : |mobiusRemainderPrefix L t| ≤ remainderMass L := by
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro d hd
  have h : (↑((t / d) % radix L d) : ℝ) ≤ radix L d := by
    exact_mod_cast (Nat.mod_lt _ (Nat.succ_pos (L / d))).le
  rw [abs_mul, abs_nat_real]
  exact (mul_le_of_le_one_left (Nat.cast_nonneg _) (mu_bound L d hd)).trans (by linarith)

theorem remainderMass_le (L : ℕ) : remainderMass L ≤ (L : ℝ) * (L + 2) := by
  calc
    _ ≤ ∑ _d ∈ Icc 1 L, ((L : ℝ) + 2) := by
      apply sum_le_sum
      intro d _
      have h : ((L / d : ℕ) : ℝ) ≤ L := by exact_mod_cast Nat.div_le_self L d
      simp only [radix, Nat.cast_add, Nat.cast_one]
      linarith
    _ = _ := by simp; ring

private theorem excess_apply {m : ℕ} (hm : 1 ≤ m) :
    excess m = vonMangoldt m - 1 := by
  change vonMangoldt m - (zeta : ArithmeticFunction ℝ) m = _
  rw [zeta_real_apply_of_ne_zero (by omega)]

/-- Either order of summation on the complete divisor hyperbola. -/
private theorem floor_row (X d : ℕ) :
    ∑ m ∈ Icc 1 X, excess m * (((X / m / d : ℕ)) : ℝ) = completeDivisorError (X / d) := by
  let Y := X / d
  have hdiv (m : ℕ) : X / m / d = Y / m := by
    simp only [Y, Nat.div_div_eq_div_mul, Nat.mul_comm m d]
  simp_rw [hdiv]
  rw [← sum_subset (Icc_subset_Icc_right (Nat.div_le_self X d)) (f := fun m =>
    excess m * ((Y / m : ℕ) : ℝ)) (by
      intro m hm hnot
      have hgt : Y < m := by
        by_contra! h
        exact hnot (mem_Icc.mpr ⟨(mem_Icc.mp hm).1, h⟩)
      simp [Nat.div_eq_of_lt hgt])]
  have hsum (n : ℕ) : (∑ m ∈ Icc 1 n, (zeta : ArithmeticFunction ℝ) m) = n := by
    rw [sum_congr rfl (fun m hm => zeta_real_apply_of_ne_zero (Nat.ne_of_gt (mem_Icc.mp hm).1))]
    simp
  have h := RHTower.sum_Icc_mul_apply excess (zeta : ArithmeticFunction ℝ) Y
  simp_rw [hsum] at h
  rw [← h, mul_comm, RHTower.sum_Icc_mul_apply]
  apply sum_congr rfl
  intro m hm
  rw [zeta_real_apply_of_ne_zero (Nat.ne_of_gt (mem_Icc.mp hm).1), one_mul, sum_vonMangoldt_sub_zeta]

private theorem digit_row (X d q : ℕ) :
    (∑ m ∈ Icc 1 X, excess m * (((X / m / d) % q : ℕ) : ℝ)) =
      completeDivisorError (X / d) - (q : ℝ) * completeDivisorError (X / d / q) := by
  have hmod (k : ℕ) : ((k % q : ℕ) : ℝ) = k - (q : ℝ) * ((k / q : ℕ) : ℝ) := by
    have h : ((k % q : ℕ) : ℝ) + (q : ℝ) * ((k / q : ℕ) : ℝ) = k := by
      exact_mod_cast Nat.mod_add_div k q
    linarith
  simp_rw [hmod, mul_sub, mul_left_comm (excess _) (q : ℝ)]
  rw [sum_sub_distrib, ← mul_sum, floor_row]
  simp only [Nat.div_div_eq_div_mul]
  simpa only [Nat.div_div_eq_div_mul, Nat.mul_assoc] using
    congrArg (fun z => completeDivisorError (X / d) - (q : ℝ) * z) (floor_row X (d*q))

private theorem abs_digit_row (X d q : ℕ) (hq : 0 < q) :
    |completeDivisorError (X / d) - (q : ℝ) * completeDivisorError (X / d / q)| ≤
      (1 + (q : ℝ)) * (25 * Real.sqrt X + |2 * Real.eulerMascheroniConstant|) := by
  let Y := X / d
  let g := 2 * Real.eulerMascheroniConstant
  have hrem : ((Y % q : ℕ) : ℝ) + (q : ℝ) * ((Y / q : ℕ) : ℝ) = Y := by
    exact_mod_cast Nat.mod_add_div Y q
  have hcorr : completeDivisorError Y - (q : ℝ) * completeDivisorError (Y / q) =
      (completeDivisorError Y + g*Y) - (q : ℝ)*(completeDivisorError (Y/q) + g*(Y/q : ℕ)) -
        g*(Y%q : ℕ) := by linear_combination g * hrem
  have hY := Nat.div_le_self X d
  have hsmall (n : ℕ) (hn : n ≤ X) :
      |completeDivisorError n + g*n| ≤ 25 * Real.sqrt X := by
    exact (abs_completeDivisorError_add_le n).trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (by exact_mod_cast hn)) (by norm_num))
  have h₁ := hsmall Y hY
  have h₂ := hsmall (Y / q) ((Nat.div_le_self Y q).trans hY)
  have hr : ((Y % q : ℕ) : ℝ) ≤ q := by exact_mod_cast (Nat.mod_lt Y hq).le
  rw [hcorr]
  calc
    _ ≤ (|completeDivisorError Y + g*Y| + |(q : ℝ)*(completeDivisorError (Y/q) + g*(Y/q : ℕ))|) +
        |g*(Y%q : ℕ)| := (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ (25 * Real.sqrt X + (q : ℝ)*(25 * Real.sqrt X)) + |g| * q := by
      simp only [abs_mul, abs_nat_real]
      exact add_le_add (add_le_add h₁ (mul_le_mul_of_nonneg_left h₂ (Nat.cast_nonneg _)))
        (mul_le_mul_of_nonneg_left hr (abs_nonneg _))
    _ ≤ _ := by dsimp only [g]; linarith only [abs_nonneg (2 * Real.eulerMascheroniConstant)]

/-- Across all long prime variables, the Möbius remainder weight has a
square-root bound uniform in the prime horizon, with explicit cutoff cost. -/
theorem abs_mangoldt_remainder_sum_le (L X : ℕ) :
    |∑ m ∈ Icc 1 X, (vonMangoldt - (zeta : ArithmeticFunction ℝ)) m *
        mobiusRemainderPrefix L (X / m)| ≤
      remainderMass L * (25 * Real.sqrt X + |2 * Real.eulerMascheroniConstant|) := by
  simp only [mobiusRemainderPrefix, mul_sum, mul_left_comm (excess _) (mu _)]
  rw [sum_comm]
  simp_rw [← mul_sum, digit_row]
  rw [remainderMass, sum_mul]
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro d hd
  rw [abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) (mu_bound L d hd)).trans
    (abs_digit_row X d _ (Nat.succ_pos _))

/-- Prime excess on the middle interval. Both endpoints can move with the horizon. -/
def middlePrimeCount (L U X : ℕ) : ℝ :=
  ∑ m ∈ Ioc U (X / (L+1)), (vonMangoldt m - 1) * (1 - mobiusRemainderPrefix L (X/m))

private theorem sum_abs_excess (X : ℕ) :
    ∑ m ∈ Icc 1 X, |excess m| ≤ 8 * X := by
  apply le_trans _ (RHTower.sum_abs_primeSawtoothSource_le X)
  exact le_of_eq (sum_congr rfl fun m hm => congrArg abs (excess_apply (mem_Icc.mp hm).1))

/-- Uniform error from the complete divisor rows and the deleted prime head. -/
def middlePrimeErrorAllowance (L U : ℕ) (x : ℝ) : ℝ :=
  remainderMass L * (25 * Real.sqrt x + |2 * Real.eulerMascheroniConstant|) +
    (1 + remainderMass L) * (8 * U)

/-- Discarding both ends of the long-variable range leaves only the rounding
cost of the complete divisor rows and the total prime mass through `U`. -/
theorem abs_prime_error_sub_middlePrimeCount_le (L U X : ℕ) :
    |(Chebyshev.psi X - X) - middlePrimeCount L U X| ≤ middlePrimeErrorAllowance L U X := by
  let F (m : ℕ) := excess m * (1 - mobiusRemainderPrefix L (X/m))
  let S := Icc 1 X
  have hsplit := sum_filter_add_sum_filter_not S (fun m => m ≤ U) F
  have htail : ∑ m ∈ S.filter (fun m => ¬ m ≤ U), F m = middlePrimeCount L U X := by
    have hsub : Ioc U (X/(L+1)) ⊆ S.filter (fun m => ¬ m ≤ U) := by
      intro m hm
      obtain ⟨hU, hX⟩ := mem_Ioc.mp hm
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, hX.trans (Nat.div_le_self X _)⟩, by omega⟩
    rw [← sum_subset (f := F) hsub (by
      intro m hm hnot
      obtain ⟨hmS, hU⟩ := mem_filter.mp hm
      obtain ⟨hm1, hmX⟩ := mem_Icc.mp hmS
      have hlarge : X/(L+1) < m := by
        by_contra! h
        exact hnot (mem_Ioc.mpr ⟨by omega, h⟩)
      have hprod := (Nat.div_lt_iff_lt_mul (Nat.succ_pos L)).mp hlarge
      have hsmall : X / m < L+1 := (Nat.div_lt_iff_lt_mul hm1).mpr (by simpa only [Nat.mul_comm] using hprod)
      simp only [F, mobiusRemainderPrefix_eq_one ((Nat.one_le_div_iff hm1).mpr hmX)
        (show X/m ≤ L by omega), sub_self, mul_zero])]
    apply sum_congr rfl
    intro m hm
    dsimp only [F]
    rw [excess_apply (by have := (mem_Ioc.mp hm).1; omega)]
  have hhead : |∑ m ∈ S.filter (fun m => m ≤ U), F m| ≤
      (1 + remainderMass L) * (8 * U) := by
    have hsub : S.filter (fun m => m ≤ U) ⊆ Icc 1 U := fun m hm =>
      mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp hm).1).1, (mem_filter.mp hm).2⟩
    calc
      _ ≤ ∑ m ∈ S.filter (fun m => m ≤ U), |excess m| * (1 + remainderMass L) := by
        apply (abs_sum_le_sum_abs _ _).trans
        apply sum_le_sum
        intro m _
        dsimp only [F]
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
        exact (abs_sub _ _).trans (add_le_add (le_of_eq abs_one) (abs_prefix_le L _))
      _ ≤ _ := by
        rw [← sum_mul, mul_comm (1 + remainderMass L)]
        have hM : 0 ≤ remainderMass L := (abs_nonneg _).trans (abs_prefix_le L 0)
        exact mul_le_mul_of_nonneg_right ((sum_le_sum_of_subset_of_nonneg hsub
          (fun _ _ _ => abs_nonneg _)).trans (sum_abs_excess U)) (by positivity)
  have hid : (Chebyshev.psi X - X) - middlePrimeCount L U X =
      (∑ m ∈ S, excess m * mobiusRemainderPrefix L (X/m)) +
      ∑ m ∈ S.filter (fun m => m ≤ U), F m := by
    have hall : ∑ m ∈ S, F m = (Chebyshev.psi X - X) -
        ∑ m ∈ S, excess m * mobiusRemainderPrefix L (X/m) := by
      simp only [F, S, mul_sub, mul_one, sum_sub_distrib, sum_vonMangoldt_sub_zeta]
    rw [htail, hall] at hsplit
    linarith only [hsplit]
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add (abs_mangoldt_remainder_sum_le L X) hhead)

/-- The same middle-interval estimate at every restricted Vaughan width.
The bound is uniform in all four cutoffs and the horizon. -/
theorem abs_cofactorCount_sub_middle_le (V W L U N : ℕ) :
    |cofactorCountError V W N -
      ∑ d ∈ Icc 1 (min N W), typeIIShort V d * middlePrimeCount L U (N/d)| ≤
      (∑ d ∈ Icc 1 W, |typeIIShort V d|) * middlePrimeErrorAllowance L U N := by
  rw [cofactorCountError_eq, ← sum_sub_distrib]
  simp_rw [← mul_sub]
  have hM : 0 ≤ remainderMass L := (abs_nonneg _).trans (abs_prefix_le L 0)
  have hA : 0 ≤ middlePrimeErrorAllowance L U N := by
    unfold middlePrimeErrorAllowance
    positivity
  calc
    _ ≤ ∑ d ∈ Icc 1 (min N W), |typeIIShort V d| * middlePrimeErrorAllowance L U N := by
      apply (abs_sum_le_sum_abs _ _).trans
      apply sum_le_sum
      intro d _
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      apply (abs_prime_error_sub_middlePrimeCount_le L U (N/d)).trans
      unfold middlePrimeErrorAllowance
      gcongr
      exact_mod_cast Nat.div_le_self N d
    _ ≤ _ := by
      rw [← sum_mul]
      exact mul_le_mul_of_nonneg_right (sum_le_sum_of_subset_of_nonneg
        (Icc_subset_Icc_right (min_le_right N W)) (fun _ _ _ => abs_nonneg _)) hA

/-- With a square-root lower cutoff and a power-sized gap at the upper end,
the error already has the requested half-power-plus-epsilon exponent. -/
theorem abs_cofactorCount_sub_middle_power_le (V W : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    {N : ℕ} (hN : 1 ≤ N) :
    let L := ⌊(N : ℝ) ^ (ε / 2)⌋₊
    let U := ⌊Real.sqrt N⌋₊
    |cofactorCountError V W N -
      ∑ d ∈ Icc 1 (min N W), typeIIShort V d * middlePrimeCount L U (N/d)| ≤
      (∑ d ∈ Icc 1 W, |typeIIShort V d|) *
        ((107 + 3 * |2 * Real.eulerMascheroniConstant|) * (N : ℝ) ^ (1/2 + ε)) := by
  intro L U
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  let t := (N : ℝ) ^ (ε / 2)
  have ht : 1 ≤ t := Real.one_le_rpow hN' (by linarith only [hε])
  have hL : (L : ℝ) ≤ t := Nat.floor_le (zero_le_one.trans ht)
  have hU : (U : ℝ) ≤ Real.sqrt N := Nat.floor_le (Real.sqrt_nonneg _)
  have hS : 1 ≤ Real.sqrt N := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hN'
  have hp : t*t = (N : ℝ)^ε := by
    dsimp only [t]
    rw [← Real.rpow_add (by positivity : (0 : ℝ) < N)]
    congr 1
    ring
  have hM : remainderMass L ≤ 3 * (N : ℝ)^ε := by
    apply (remainderMass_le L).trans
    rw [← hp]
    calc
      _ ≤ t * (3*t) := mul_le_mul hL (by linarith) (by positivity) (zero_le_one.trans ht)
      _ = _ := by ring
  have hpower : 1 ≤ (N : ℝ)^ε := Real.one_le_rpow hN' hε
  apply (abs_cofactorCount_sub_middle_le V W L U N).trans
  apply mul_le_mul_of_nonneg_left _ (sum_nonneg fun _ _ => abs_nonneg _)
  unfold middlePrimeErrorAllowance
  have hγ := abs_nonneg (2 * Real.eulerMascheroniConstant)
  rw [Real.rpow_add (by positivity : (0 : ℝ) < N), ← Real.sqrt_eq_rpow]
  calc
    _ ≤ (3 * (N : ℝ)^ε) * ((25 + |2 * Real.eulerMascheroniConstant|) * Real.sqrt N) +
        (4 * (N : ℝ)^ε) * (8 * Real.sqrt N) := by
      apply add_le_add
      · exact mul_le_mul hM (by nlinarith only [mul_le_mul_of_nonneg_left hS hγ]) (by positivity)
          (by positivity)
      · exact mul_le_mul (by linarith only [hM, hpower]) (by gcongr) (by positivity) (by positivity)
    _ = _ := by ring

#print axioms abs_mangoldt_remainder_sum_le
#print axioms abs_cofactorCount_sub_middle_power_le

end GaloisForLFunctions.ExceptionalLayerTheory
