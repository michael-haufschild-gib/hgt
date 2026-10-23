import GaloisForLFunctions.RHTower.Sieve.SquareWindowEnergyUnderRH
import GaloisForLFunctions.RHTower.VonMangoldtMollifierPolynomialMeanSquare
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# One arithmetic pair kernel for RH and twin-prime detection

The square-window RH criterion reads a centered aggregate of von Mangoldt
pairs. The squarefree projection of the same kernel detects prime pairs
exactly; its gap-two tails express twin-prime infinitude. The aggregate
splits into the two orientations of the twin-prime slice and its complement.
-/

namespace TwinPrime

open Finset ArithmeticFunction Filter Asymptotics

noncomputable section

/-- The nonnegative von Mangoldt weight at the critical exponent. -/
def mangoldtWeight (n : ℕ) : ℝ := vonMangoldt n / Real.sqrt n

/-- The arithmetic pair kernel shared by the two observations. -/
def mangoldtPairKernel (k l : ℕ) : ℝ := mangoldtWeight k * mangoldtWeight l

/-- Squarefree projection removes every proper prime power. -/
def primePairKernel (k l : ℕ) : ℝ :=
  ((moebius k : ℝ) ^ 2 * mangoldtWeight k) *
    ((moebius l : ℝ) ^ 2 * mangoldtWeight l)

theorem mangoldtWeight_nonneg (n : ℕ) : 0 ≤ mangoldtWeight n :=
  div_nonneg vonMangoldt_nonneg (Real.sqrt_nonneg _)

theorem mangoldtPairKernel_nonneg (k l : ℕ) : 0 ≤ mangoldtPairKernel k l :=
  mul_nonneg (mangoldtWeight_nonneg k) (mangoldtWeight_nonneg l)

theorem primePairKernel_nonneg (k l : ℕ) : 0 ≤ primePairKernel k l := by
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (mangoldtWeight_nonneg k))
    (mul_nonneg (sq_nonneg _) (mangoldtWeight_nonneg l))

theorem mangoldtPairKernel_comm (k l : ℕ) :
    mangoldtPairKernel k l = mangoldtPairKernel l k := mul_comm _ _

theorem primePairKernel_comm (k l : ℕ) :
    primePairKernel k l = primePairKernel l k := mul_comm _ _

/-- The common kernel retains its one-point weight on the diagonal. -/
theorem sqrt_mangoldtPairKernel_diag (k : ℕ) :
    Real.sqrt (mangoldtPairKernel k k) = mangoldtWeight k := by
  rw [mangoldtPairKernel, ← pow_two, Real.sqrt_sq (mangoldtWeight_nonneg k)]

/-- Multiplying by the Möbius square keeps precisely the prime part of the weight. -/
theorem moebius_sq_mul_mangoldtWeight (n : ℕ) :
    (moebius n : ℝ) ^ 2 * mangoldtWeight n =
      if n.Prime then mangoldtWeight n else 0 := by
  by_cases hp : n.Prime
  · simp only [hp, if_true, moebius_apply_prime hp, Int.cast_neg, Int.cast_one,
      neg_one_sq, one_mul]
  · rw [if_neg hp]
    by_cases hn : IsPrimePow n
    · rw [moebius_apply_isPrimePow_not_prime hn hp]
      simp only [Int.cast_zero, zero_pow two_ne_zero, zero_mul]
    · simp only [mangoldtWeight, vonMangoldt_eq_zero_iff.mpr hn, zero_div, mul_zero]

theorem primePairKernel_eq_squarefree_projection (k l : ℕ) :
    primePairKernel k l =
      (moebius k : ℝ) ^ 2 * (moebius l : ℝ) ^ 2 * mangoldtPairKernel k l := by
  unfold primePairKernel mangoldtPairKernel
  ring

/-- The prime projection is an exact filter, with no prime-power error term. -/
theorem primePairKernel_eq_prime_filter (k l : ℕ) :
    primePairKernel k l =
      if k.Prime ∧ l.Prime then mangoldtPairKernel k l else 0 := by
  rw [primePairKernel, moebius_sq_mul_mangoldtWeight, moebius_sq_mul_mangoldtWeight]
  by_cases hk : k.Prime <;> by_cases hl : l.Prime <;>
    simp only [hk, hl, and_self, and_false, false_and, if_true, if_false,
      zero_mul, mul_zero, mangoldtPairKernel]

/-- Positive mass in the projected kernel is exactly a pair of primes. -/
theorem primePairKernel_pos_iff (k l : ℕ) :
    0 < primePairKernel k l ↔ k.Prime ∧ l.Prime := by
  rw [primePairKernel_eq_prime_filter]
  constructor
  · intro h
    by_contra hn
    rw [if_neg hn] at h
    exact (lt_irrefl 0) h
  · rintro ⟨hk, hl⟩
    rw [if_pos ⟨hk, hl⟩]
    have hwk : 0 < mangoldtWeight k := div_pos
      (vonMangoldt_pos_iff.mpr hk.isPrimePow)
      (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hk.pos))
    have hwl : 0 < mangoldtWeight l := div_pos
      (vonMangoldt_pos_iff.mpr hl.isPrimePow)
      (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hl.pos))
    exact mul_pos hwk hwl

/-- Gap-two mass on a finite tail, without a density or divergence requirement. -/
def twinPairKernelTail (N M : ℕ) : ℝ :=
  ∑ n ∈ Ioc N M, primePairKernel n (n + 2)

theorem twinPairKernelTail_pos_iff (N M : ℕ) :
    0 < twinPairKernelTail N M ↔
      ∃ p ∈ Ioc N M, p.Prime ∧ (p + 2).Prime := by
  rw [twinPairKernelTail, Finset.sum_pos_iff_of_nonneg
    (fun n _ => primePairKernel_nonneg n (n + 2))]
  simp only [primePairKernel_pos_iff]

/-- Twin-prime infinitude is exactly positive projected gap-two mass in every tail. -/
theorem twinPrimes_iff_pairKernel_tail_positive :
    (∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧ (p + 2).Prime) ↔
      ∀ N : ℕ, ∃ M : ℕ, 0 < twinPairKernelTail N M := by
  constructor
  · intro h N
    obtain ⟨p, hpN, hp, hp₂⟩ := h N
    exact ⟨p, (twinPairKernelTail_pos_iff N p).mpr
      ⟨p, mem_Ioc.mpr ⟨hpN, le_rfl⟩, hp, hp₂⟩⟩
  · intro h N
    obtain ⟨M, hM⟩ := h N
    obtain ⟨p, hpI, hp, hp₂⟩ := (twinPairKernelTail_pos_iff N M).mp hM
    exact ⟨p, (mem_Ioc.mp hpI).1, hp, hp₂⟩

/-- The uncentered pair term in the square-window RH energy. -/
def rhPairMass (M : ℕ) : ℝ :=
  ∑ k ∈ RHTower.squareApertureCarrier M, ∑ l ∈ RHTower.squareApertureCarrier M,
    mangoldtPairKernel k l * RHTower.squareWindowOverlapKernel M k l

/-- The RH energy reads only the common kernel and its diagonal. -/
def rhPairKernelEnergy (M : ℕ) : ℝ :=
  let c : ℝ := 2 * (1 - (Real.sqrt 2)⁻¹)
  rhPairMass M + (-2 * c) *
    (∑ k ∈ RHTower.squareApertureCarrier M,
      Real.sqrt (mangoldtPairKernel k k) * RHTower.squareWindowFirstMomentKernel M k) +
    c ^ 2 * ∑ m ∈ Icc 1 M, (m : ℝ) ^ 2

theorem rhPairKernelEnergy_eq (M : ℕ) :
    rhPairKernelEnergy M = RHTower.squareWindowCorrelationEnergy M := by
  unfold rhPairKernelEnergy
  simp_rw [sqrt_mangoldtPairKernel_diag]
  rfl

/-- The existing RH criterion, expressed through the same kernel that detects twins. -/
theorem riemannHypothesis_iff_pairKernel_energy :
    RiemannHypothesis ↔ ∀ δ : ℝ, 0 < δ →
      rhPairKernelEnergy =O[atTop] (fun M : ℕ => (M : ℝ) ^ (1 + δ)) := by
  have hfun : rhPairKernelEnergy = RHTower.squareWindowCorrelationEnergy :=
    funext rhPairKernelEnergy_eq
  rw [hfun]
  exact RHTower.Sieve.riemannHypothesis_iff_squarePrimeWindowCorrelationEnergySubpower

/-- The prime gap-two part of the RH pair mass, in one orientation. -/
def rhTwinSlice (M : ℕ) : ℝ :=
  ∑ k ∈ RHTower.squareApertureCarrier M, ∑ l ∈ RHTower.squareApertureCarrier M,
    if l = k + 2 then
      primePairKernel k l * RHTower.squareWindowOverlapKernel M k l else 0

/-- Every pair except the two orientations of prime twins. -/
def rhOtherPairMass (M : ℕ) : ℝ :=
  ∑ k ∈ RHTower.squareApertureCarrier M, ∑ l ∈ RHTower.squareApertureCarrier M,
    if k.Prime ∧ l.Prime ∧ (l = k + 2 ∨ k = l + 2) then 0 else
      mangoldtPairKernel k l * RHTower.squareWindowOverlapKernel M k l

theorem rhOtherPairMass_nonneg (M : ℕ) : 0 ≤ rhOtherPairMass M := by
  apply sum_nonneg
  intro k hk
  apply sum_nonneg
  intro l hl
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (mangoldtPairKernel_nonneg k l)
      (RHTower.squareWindowOverlapKernel_nonneg M k l)

private theorem pair_mass_partition (M k l : ℕ) :
    mangoldtPairKernel k l * RHTower.squareWindowOverlapKernel M k l =
      (if l = k + 2 then
        primePairKernel k l * RHTower.squareWindowOverlapKernel M k l else 0) +
      (if k = l + 2 then
        primePairKernel k l * RHTower.squareWindowOverlapKernel M k l else 0) +
      (if k.Prime ∧ l.Prime ∧ (l = k + 2 ∨ k = l + 2) then 0 else
        mangoldtPairKernel k l * RHTower.squareWindowOverlapKernel M k l) := by
  simp only [primePairKernel_eq_prime_filter]
  by_cases hp : k.Prime ∧ l.Prime
  · by_cases hkl : l = k + 2
    · have hlk : ¬ k = l + 2 := by omega
      have hall : k.Prime ∧ l.Prime ∧ (l = k + 2 ∨ k = l + 2) :=
        ⟨hp.1, hp.2, Or.inl hkl⟩
      simp only [if_pos hp, if_pos hkl, if_neg hlk, if_pos hall, add_zero]
    · by_cases hlk : k = l + 2
      · have hall : k.Prime ∧ l.Prime ∧ (l = k + 2 ∨ k = l + 2) :=
          ⟨hp.1, hp.2, Or.inr hlk⟩
        simp only [if_pos hp, if_neg hkl, if_pos hlk, if_pos hall, zero_add, add_zero]
      · have hall : ¬ (k.Prime ∧ l.Prime ∧ (l = k + 2 ∨ k = l + 2)) := by
          rintro ⟨_, _, h | h⟩
          · exact hkl h
          · exact hlk h
        simp only [if_pos hp, if_neg hkl, if_neg hlk, if_neg hall, zero_add]
  · have hall : ¬ (k.Prime ∧ l.Prime ∧ (l = k + 2 ∨ k = l + 2)) :=
      fun h => hp ⟨h.1, h.2.1⟩
    simp only [if_neg hp, if_neg hall, zero_mul, ite_self, zero_add]

private theorem rhTwinSlice_reverse (M : ℕ) :
    (∑ k ∈ RHTower.squareApertureCarrier M, ∑ l ∈ RHTower.squareApertureCarrier M,
      if k = l + 2 then
        primePairKernel k l * RHTower.squareWindowOverlapKernel M k l else 0) =
      rhTwinSlice M := by
  rw [Finset.sum_comm]
  unfold rhTwinSlice
  apply sum_congr rfl
  intro k hk
  apply sum_congr rfl
  intro l hl
  rw [primePairKernel_comm l k, RHTower.squareWindowOverlapKernel_comm M l k]

/-- The RH aggregate contains both orientations of twins and a nonnegative complement. -/
theorem rhPairMass_eq_twins_add_complement (M : ℕ) :
    rhPairMass M = 2 * rhTwinSlice M + rhOtherPairMass M := by
  unfold rhPairMass
  calc
    _ = ∑ k ∈ RHTower.squareApertureCarrier M, ∑ l ∈ RHTower.squareApertureCarrier M,
        ((if l = k + 2 then
          primePairKernel k l * RHTower.squareWindowOverlapKernel M k l else 0) +
        (if k = l + 2 then
          primePairKernel k l * RHTower.squareWindowOverlapKernel M k l else 0) +
        (if k.Prime ∧ l.Prime ∧ (l = k + 2 ∨ k = l + 2) then 0 else
          mangoldtPairKernel k l * RHTower.squareWindowOverlapKernel M k l)) := by
      exact sum_congr rfl fun k _ => sum_congr rfl fun l _ => pair_mass_partition M k l
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      rw [rhTwinSlice_reverse]
      change rhTwinSlice M + rhTwinSlice M + rhOtherPairMass M = _
      ring

theorem two_mul_rhTwinSlice_le_pairMass (M : ℕ) :
    2 * rhTwinSlice M ≤ rhPairMass M := by
  rw [rhPairMass_eq_twins_add_complement]
  exact le_add_of_nonneg_right (rhOtherPairMass_nonneg M)

/-- A prime-projected lag slice of the square-window pair mass. -/
def rhPrimeLagSlice (h M : ℕ) : ℝ :=
  ∑ k ∈ RHTower.squareApertureCarrier M, ∑ l ∈ RHTower.squareApertureCarrier M,
    if l = k + h then
      primePairKernel k l * RHTower.squareWindowOverlapKernel M k l else 0

theorem rhPrimeLagSlice_nonneg (h M : ℕ) : 0 ≤ rhPrimeLagSlice h M := by
  apply sum_nonneg
  intro k hk
  apply sum_nonneg
  intro l hl
  split_ifs
  · exact mul_nonneg (primePairKernel_nonneg k l)
      (RHTower.squareWindowOverlapKernel_nonneg M k l)
  · exact le_rfl

theorem primePairKernel_le (k l : ℕ) : primePairKernel k l ≤ mangoldtPairKernel k l := by
  rw [primePairKernel_eq_prime_filter]
  split_ifs
  · exact le_rfl
  · exact mangoldtPairKernel_nonneg k l

private theorem squareWindowOverlapKernel_le (M k l : ℕ) :
    RHTower.squareWindowOverlapKernel M k l ≤ (M : ℝ) := by
  unfold RHTower.squareWindowOverlapKernel
  calc
    _ ≤ ∑ _m ∈ Icc 1 M, (1 : ℝ) := by
      apply sum_le_sum
      intro m hm
      split_ifs <;> norm_num
    _ = _ := by simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]

private theorem sum_forward_square_le (S : Finset ℕ) (a : ℕ → ℝ) (h k : ℕ) :
    (∑ l ∈ S, if l = k + h then a k ^ 2 else 0) ≤ a k ^ 2 := by
  rw [sum_ite_eq']
  split_ifs
  · exact le_rfl
  · exact sq_nonneg _

private theorem sum_backward_square_le (S : Finset ℕ) (a : ℕ → ℝ) (h l : ℕ) :
    (∑ k ∈ S, if l = k + h then a l ^ 2 else 0) ≤ a l ^ 2 := by
  calc
    _ ≤ ∑ k ∈ S, if k = l - h then a l ^ 2 else 0 := by
      apply sum_le_sum
      intro k hk
      by_cases hkl : l = k + h
      · have heq : k = l - h := by omega
        rw [if_pos hkl, if_pos heq]
      · rw [if_neg hkl]
        split_ifs
        · exact sq_nonneg _
        · exact le_rfl
    _ ≤ _ := by
      rw [sum_ite_eq']
      split_ifs
      · exact le_rfl
      · exact sq_nonneg _

/-- Each index appears at most once in either coordinate of a prescribed lag. -/
theorem rhPrimeLagSlice_le_square_mass (h M : ℕ) :
    rhPrimeLagSlice h M ≤
      (M : ℝ) * ∑ n ∈ RHTower.squareApertureCarrier M, mangoldtWeight n ^ 2 := by
  let S := RHTower.squareApertureCarrier M
  have hpoint (k l : ℕ) :
      (if l = k + h then
        primePairKernel k l * RHTower.squareWindowOverlapKernel M k l else 0) ≤
      ((M : ℝ) / 2) * ((if l = k + h then mangoldtWeight k ^ 2 else 0) +
        (if l = k + h then mangoldtWeight l ^ 2 else 0)) := by
    by_cases hkl : l = k + h
    · simp only [if_pos hkl]
      have hbound := mul_le_mul (primePairKernel_le k l)
        (squareWindowOverlapKernel_le M k l)
        (RHTower.squareWindowOverlapKernel_nonneg M k l) (mangoldtPairKernel_nonneg k l)
      unfold mangoldtPairKernel at hbound
      nlinarith [mul_nonneg (sq_nonneg (mangoldtWeight k - mangoldtWeight l))
        (Nat.cast_nonneg (α := ℝ) M)]
    · simp only [if_neg hkl, zero_add, mul_zero, le_refl]
  have hdouble := sum_le_sum (s := S) fun k _ => sum_le_sum (s := S) fun l _ => hpoint k l
  simp only [mul_add, sum_add_distrib, ← mul_sum] at hdouble
  have hleft : (∑ k ∈ S, ∑ l ∈ S,
      if l = k + h then mangoldtWeight k ^ 2 else 0) ≤ ∑ k ∈ S, mangoldtWeight k ^ 2 :=
    sum_le_sum fun k _ => sum_forward_square_le S mangoldtWeight h k
  have hright : (∑ k ∈ S, ∑ l ∈ S,
      if l = k + h then mangoldtWeight l ^ 2 else 0) ≤ ∑ l ∈ S, mangoldtWeight l ^ 2 := by
    rw [sum_comm]
    exact sum_le_sum fun l _ => sum_backward_square_le S mangoldtWeight h l
  have hleft' := mul_le_mul_of_nonneg_left hleft (show 0 ≤ (M : ℝ) / 2 by positivity)
  have hright' := mul_le_mul_of_nonneg_left hright (show 0 ≤ (M : ℝ) / 2 by positivity)
  change rhPrimeLagSlice h M ≤ _ at hdouble
  change rhPrimeLagSlice h M ≤ (M : ℝ) * ∑ k ∈ S, mangoldtWeight k ^ 2
  linarith

private theorem mangoldt_square_mass_bound (M : ℕ+)
    (d : {d : ℝ // 0 < d ∧ d ≤ 1}) :
    (∑ n ∈ RHTower.squareApertureCarrier M, mangoldtWeight n ^ 2) ≤
      (5 / d.val ^ 2) * (M : ℝ) ^ (4 * d.val) := by
  have hMpos : (0 : ℝ) < M := by exact_mod_cast M.pos
  have hset : Icc 1 ((M : ℕ) ^ 2) ⊆ RHTower.squareApertureCarrier M := by
    intro n hn
    have hn' := mem_Icc.mp hn
    simp only [RHTower.squareApertureCarrier, mem_range]
    omega
  have hsum : (∑ n ∈ RHTower.squareApertureCarrier M, mangoldtWeight n ^ 2) =
      ∑ n ∈ Icc 1 ((M : ℕ) ^ 2), mangoldtWeight n ^ 2 := by
    symm
    apply sum_subset hset
    intro n hn hnnot
    have hn0 : n = 0 := by
      simp only [RHTower.squareApertureCarrier, mem_range] at hn
      simp only [mem_Icc, not_and_or, not_le] at hnnot
      omega
    subst n
    simp only [mangoldtWeight, Nat.cast_zero, Real.sqrt_zero, div_zero,
      zero_pow two_ne_zero]
  rw [hsum]
  have hterm (n : ℕ) (hn : n ∈ Icc 1 ((M : ℕ) ^ 2)) :
      mangoldtWeight n ^ 2 ≤ (M : ℝ) ^ (4 * d.val) *
        (vonMangoldt n ^ 2 * (n : ℝ) ^ (-1 - 2 * d.val)) := by
    have hnI := mem_Icc.mp hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n from hnI.1)
    have hnM : (n : ℝ) ≤ (M : ℝ) ^ 2 := by exact_mod_cast hnI.2
    have hpow := Real.rpow_le_rpow hnpos.le hnM (show 0 ≤ 2 * d.val by linarith [d.property.1])
    have hexp : ((M : ℝ) ^ 2) ^ (2 * d.val) = (M : ℝ) ^ (4 * d.val) := by
      rw [← Real.rpow_natCast (M : ℝ) 2, ← Real.rpow_mul hMpos.le]
      congr 1
      push_cast
      ring
    rw [hexp] at hpow
    have hid : mangoldtWeight n ^ 2 =
        (vonMangoldt n ^ 2 * (n : ℝ) ^ (-1 - 2 * d.val)) * (n : ℝ) ^ (2 * d.val) := by
      rw [mangoldtWeight, div_pow, Real.sq_sqrt hnpos.le, mul_assoc,
        ← Real.rpow_add hnpos, show (-1 - 2 * d.val) + 2 * d.val = -1 by ring,
        Real.rpow_neg_one, div_eq_mul_inv]
    rw [hid, mul_comm ((M : ℝ) ^ (4 * d.val))]
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hbound := RHTower.sum_vonMangoldt_sq_rpow_le d.property.1 d.property.2 ((M : ℕ) ^ 2)
  calc
    _ ≤ ∑ n ∈ Icc 1 ((M : ℕ) ^ 2), (M : ℝ) ^ (4 * d.val) *
        (vonMangoldt n ^ 2 * (n : ℝ) ^ (-1 - 2 * d.val)) := sum_le_sum hterm
    _ = (M : ℝ) ^ (4 * d.val) *
        ∑ n ∈ Icc 1 ((M : ℕ) ^ 2), vonMangoldt n ^ 2 * (n : ℝ) ^ (-1 - 2 * d.val) :=
      (mul_sum _ _ _).symm
    _ ≤ (M : ℝ) ^ (4 * d.val) * (5 / d.val ^ 2) :=
      mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hMpos.le _)
    _ = _ := mul_comm _ _

/-- Every lag has subpower mass above the aperture scale, with one constant for all lags. -/
theorem rhPrimeLagSlice_uniform_bound (ε : {ε : ℝ // 0 < ε}) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : ℕ+, ∀ h : ℕ,
      rhPrimeLagSlice h M ≤ C * (M : ℝ) ^ (1 + ε.val) := by
  let d : {d : ℝ // 0 < d ∧ d ≤ 1} :=
    ⟨min ε.val 1 / 4, by
      have hp : 0 < min ε.val 1 := lt_min ε.property (by norm_num)
      have hle : min ε.val 1 ≤ 1 := min_le_right _ _
      constructor <;> linarith⟩
  have hdpos : 0 < d.val := d.property.1
  refine ⟨5 / d.val ^ 2, by positivity, ?_⟩
  intro M h
  have hMpos : (0 : ℝ) < M := by exact_mod_cast M.pos
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast M.pos
  have hbound := rhPrimeLagSlice_le_square_mass h M
  have hmass := mul_le_mul_of_nonneg_left (mangoldt_square_mass_bound M d) hMpos.le
  have hid : (M : ℝ) * ((5 / d.val ^ 2) * (M : ℝ) ^ (4 * d.val)) =
      (5 / d.val ^ 2) * (M : ℝ) ^ (1 + 4 * d.val) := by
    rw [Real.rpow_add hMpos, Real.rpow_one]
    ring
  have hexp : 1 + 4 * d.val ≤ 1 + ε.val := by
    have hle := min_le_left ε.val 1
    dsimp [d]
    linarith
  have hmono := Real.rpow_le_rpow_of_exponent_le hMone hexp
  calc
    _ ≤ (M : ℝ) * ((5 / d.val ^ 2) * (M : ℝ) ^ (4 * d.val)) := hbound.trans hmass
    _ = (5 / d.val ^ 2) * (M : ℝ) ^ (1 + 4 * d.val) := hid
    _ ≤ _ := mul_le_mul_of_nonneg_left hmono (by positivity)

theorem rhPrimeLagSlice_isBigO (h : ℕ) (ε : {ε : ℝ // 0 < ε}) :
    rhPrimeLagSlice h =O[atTop] (fun M : ℕ => (M : ℝ) ^ (1 + ε.val)) := by
  obtain ⟨C, hC, hbound⟩ := rhPrimeLagSlice_uniform_bound ε
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with M hM
  rw [Real.norm_eq_abs, abs_of_nonneg (rhPrimeLagSlice_nonneg h M), Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg M) _)]
  exact hbound ⟨M, by omega⟩ h

/-- The entire explicit twin-prime slice already lies in the RH growth class unconditionally. -/
theorem rhTwinSlice_isBigO (ε : {ε : ℝ // 0 < ε}) :
    rhTwinSlice =O[atTop] (fun M : ℕ => (M : ℝ) ^ (1 + ε.val)) :=
  rhPrimeLagSlice_isBigO 2 ε

/-- The centered RH observation after deleting both orientations of prime twins. -/
def rhPairKernelEnergyWithoutTwins (M : ℕ) : ℝ :=
  rhPairKernelEnergy M - (rhTwinSlice M + rhTwinSlice M)

/-- Deleting the fixed-gap twin slice leaves the aggregate RH criterion unchanged. -/
theorem riemannHypothesis_iff_pairKernel_energy_without_twins :
    RiemannHypothesis ↔ ∀ δ : ℝ, 0 < δ →
      rhPairKernelEnergyWithoutTwins =O[atTop]
        (fun M : ℕ => (M : ℝ) ^ (1 + δ)) := by
  rw [riemannHypothesis_iff_pairKernel_energy]
  constructor
  · intro h δ hδ
    have hs := rhTwinSlice_isBigO ⟨δ, hδ⟩
    exact (h δ hδ).sub (hs.add hs)
  · intro h δ hδ
    have hs := rhTwinSlice_isBigO ⟨δ, hδ⟩
    have hsum := (h δ hδ).add (hs.add hs)
    have hfun : (fun M => rhPairKernelEnergyWithoutTwins M +
        (rhTwinSlice M + rhTwinSlice M)) = rhPairKernelEnergy := by
      funext M
      exact sub_add_cancel _ _
    rwa [hfun] at hsum

end

end TwinPrime
