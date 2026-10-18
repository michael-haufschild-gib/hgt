import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanMoment

/-!
# Conditional tails of energy-centered prime packets

The pronic measure has mass one and tail mass `1 / (H + 1)`. A mean-zero
prime packet therefore splits orthogonally into its finite prefix, the
constant forced by its tail mean, and an actual centered tail. Before the
first prime jump, the prefix depends only on the coefficient sum and its
logarithmic moment. These coherent contributions survive energy centering.
-/

open scoped BigOperators
open Finset ArithmeticFunction RHTower

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-- A finite real packet of energy-centered prime Ramanujan primitives. -/
def primePacketValue (S : Finset Nat.Primes) (a : Nat.Primes → ℝ) (n : ℕ) : ℝ :=
  ∑ p ∈ S, a p * pmRamanujanEnergyCenteredPrimitive p n

/-- The bilinear form of the actual energy-centered pronic Gram kernel. -/
def primePacketBilinear (S T : Finset Nat.Primes) (a b : Nat.Primes → ℝ) : ℝ :=
  ∑ p ∈ S, ∑ q ∈ T, a p * b q * pmRamanujanEnergyCenteredGram p q

/-- The pronic integral of a packet over its finite prefix. -/
def primePacketHeadMean (H : ℕ) (S : Finset Nat.Primes) (a : Nat.Primes → ℝ) : ℝ :=
  ∑ n ∈ range (H + 1), primePacketValue S a n / ((n : ℝ) * ((n : ℝ) + 1))

/-- The bilinear contribution of the finite prefix. -/
def primePacketHeadBilinear (H : ℕ) (S T : Finset Nat.Primes)
    (a b : Nat.Primes → ℝ) : ℝ :=
  ∑ n ∈ range (H + 1),
    primePacketValue S a n * primePacketValue T b n / ((n : ℝ) * ((n : ℝ) + 1))

/-- The tail after removing its conditional mean. The index starts at `H + 1`. -/
def primePacketTailResidual (H : ℕ) (S : Finset Nat.Primes)
    (a : Nat.Primes → ℝ) (n : ℕ) : ℝ :=
  primePacketValue S a (H + 1 + n) + ((H : ℝ) + 1) * primePacketHeadMean H S a

/-- An actual centered-tail inner product, independent of any proposed bound. -/
def primePacketTailBilinear (H : ℕ) (S T : Finset Nat.Primes)
    (a b : Nat.Primes → ℝ) : ℝ :=
  ∑' n : ℕ, primePacketTailResidual H S a n * primePacketTailResidual H T b n /
    (((H : ℝ) + 1 + n) * ((H : ℝ) + 1 + n + 1))

theorem hasSum_primePacketValue (S : Finset Nat.Primes) (a : Nat.Primes → ℝ) :
    HasSum (fun n : ℕ => primePacketValue S a n / ((n : ℝ) * ((n : ℝ) + 1))) 0 := by
  have hs := hasSum_sum (s := S) (fun p _ =>
    (hasSum_pmRamanujanEnergyCenteredPrimitive p.property.one_lt).mul_left (a p))
  simp only [mul_zero, sum_const_zero] at hs
  apply hs.congr_fun
  intro n
  simp only [primePacketValue, sum_div]
  exact sum_congr rfl fun p _ => by ring

theorem hasSum_primePacketBilinear (S T : Finset Nat.Primes)
    (a b : Nat.Primes → ℝ) :
    HasSum (fun n : ℕ => primePacketValue S a n * primePacketValue T b n /
      ((n : ℝ) * ((n : ℝ) + 1))) (primePacketBilinear S T a b) := by
  have hs : HasSum (fun n : ℕ => ∑ p ∈ S, ∑ q ∈ T,
      (a p * b q) * (pmRamanujanEnergyCenteredPrimitive p n *
        pmRamanujanEnergyCenteredPrimitive q n / ((n : ℝ) * ((n : ℝ) + 1))))
      (primePacketBilinear S T a b) := by
    apply hasSum_sum
    intro p _
    apply hasSum_sum
    intro q _
    exact (hasSum_pmRamanujanEnergyCenteredGram p.property.one_lt q.property.one_lt
      ).summable.hasSum.mul_left _
  apply hs.congr_fun
  intro n
  simp only [primePacketValue, sum_mul, mul_sum, sum_div]
  rw [sum_comm]
  apply sum_congr rfl
  intro p _
  exact sum_congr rfl fun q _ => by ring

private theorem hasSum_primePacketTailMass (H : ℕ) :
    HasSum (fun n : ℕ => 1 /
      (((H : ℝ) + 1 + n) * ((H : ℝ) + 1 + n + 1))) (1 / ((H : ℝ) + 1)) :=
  GaloisForLFunctions.hasSum_one_div_shift_mul_succ (by positivity)

theorem hasSum_primePacketValue_tail (H : ℕ) (S : Finset Nat.Primes)
    (a : Nat.Primes → ℝ) :
    HasSum (fun n : ℕ => primePacketValue S a (H + 1 + n) /
      (((H : ℝ) + 1 + n) * ((H : ℝ) + 1 + n + 1)))
      (-primePacketHeadMean H S a) := by
  have hs := hasSum_primePacketValue S a
  have ht := hs.summable.comp_injective (fun i j h => Nat.add_left_cancel h :
    Function.Injective (fun n : ℕ => H + 1 + n))
  have he := hs.summable.sum_add_tsum_nat_add (H + 1)
  rw [hs.tsum_eq] at he
  have he' : primePacketHeadMean H S a +
      (∑' n : ℕ, primePacketValue S a (H + 1 + n) /
        (((H : ℝ) + 1 + n) * ((H : ℝ) + 1 + n + 1))) = 0 := by
    simpa only [primePacketHeadMean, Nat.add_comm, Nat.cast_add, Nat.cast_one, add_comm] using he
  have ht' : Summable (fun n : ℕ => primePacketValue S a (H + 1 + n) /
      (((H : ℝ) + 1 + n) * ((H : ℝ) + 1 + n + 1))) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using ht
  convert ht'.hasSum using 1
  linarith

theorem hasSum_primePacketBilinear_tail (H : ℕ) (S T : Finset Nat.Primes)
    (a b : Nat.Primes → ℝ) :
    HasSum (fun n : ℕ =>
      primePacketValue S a (H + 1 + n) * primePacketValue T b (H + 1 + n) /
        (((H : ℝ) + 1 + n) * ((H : ℝ) + 1 + n + 1)))
      (primePacketBilinear S T a b - primePacketHeadBilinear H S T a b) := by
  have hs := hasSum_primePacketBilinear S T a b
  have ht := hs.summable.comp_injective (fun i j h => Nat.add_left_cancel h :
    Function.Injective (fun n : ℕ => H + 1 + n))
  have he := hs.summable.sum_add_tsum_nat_add (H + 1)
  rw [hs.tsum_eq] at he
  have he' : primePacketHeadBilinear H S T a b +
      (∑' n : ℕ, primePacketValue S a (H + 1 + n) *
        primePacketValue T b (H + 1 + n) /
          (((H : ℝ) + 1 + n) * ((H : ℝ) + 1 + n + 1))) =
      primePacketBilinear S T a b := by
    simpa only [primePacketHeadBilinear, Nat.add_comm, Nat.cast_add, Nat.cast_one,
      add_comm] using he
  have ht' : Summable (fun n : ℕ => primePacketValue S a (H + 1 + n) *
      primePacketValue T b (H + 1 + n) /
        (((H : ℝ) + 1 + n) * ((H : ℝ) + 1 + n + 1))) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one] using ht
  convert ht'.hasSum using 1
  linarith

/-- The centered tail has zero pronic mean for every cutoff and every packet. -/
theorem hasSum_primePacketTailResidual (H : ℕ) (S : Finset Nat.Primes)
    (a : Nat.Primes → ℝ) :
    HasSum (fun n : ℕ => primePacketTailResidual H S a n /
      (((H : ℝ) + 1 + n) * ((H : ℝ) + 1 + n + 1))) 0 := by
  have hs := (hasSum_primePacketValue_tail H S a).add
    ((hasSum_primePacketTailMass H).mul_left
      (((H : ℝ) + 1) * primePacketHeadMean H S a))
  have hH : (H : ℝ) + 1 ≠ 0 := by positivity
  have he : -primePacketHeadMean H S a +
      (((H : ℝ) + 1) * primePacketHeadMean H S a) * (1 / ((H : ℝ) + 1)) = 0 := by
    field_simp
    ring
  rw [he] at hs
  exact hs.congr_fun fun n => by unfold primePacketTailResidual; ring

theorem hasSum_primePacketTailBilinear (H : ℕ) (S T : Finset Nat.Primes)
    (a b : Nat.Primes → ℝ) :
    HasSum (fun n : ℕ => primePacketTailResidual H S a n *
      primePacketTailResidual H T b n /
        (((H : ℝ) + 1 + n) * ((H : ℝ) + 1 + n + 1)))
      (primePacketBilinear S T a b - primePacketHeadBilinear H S T a b -
        ((H : ℝ) + 1) * primePacketHeadMean H S a * primePacketHeadMean H T b) := by
  have hs := (((hasSum_primePacketBilinear_tail H S T a b).add
    ((hasSum_primePacketValue_tail H T b).mul_left
      (((H : ℝ) + 1) * primePacketHeadMean H S a))).add
    ((hasSum_primePacketValue_tail H S a).mul_left
      (((H : ℝ) + 1) * primePacketHeadMean H T b))).add
    ((hasSum_primePacketTailMass H).mul_left
      ((((H : ℝ) + 1) * primePacketHeadMean H S a) *
        (((H : ℝ) + 1) * primePacketHeadMean H T b)))
  have hH : (H : ℝ) + 1 ≠ 0 := by positivity
  have he : primePacketBilinear S T a b - primePacketHeadBilinear H S T a b +
      ((H : ℝ) + 1) * primePacketHeadMean H S a * (-primePacketHeadMean H T b) +
      ((H : ℝ) + 1) * primePacketHeadMean H T b * (-primePacketHeadMean H S a) +
      (((H : ℝ) + 1) * primePacketHeadMean H S a *
        (((H : ℝ) + 1) * primePacketHeadMean H T b)) * (1 / ((H : ℝ) + 1)) =
      primePacketBilinear S T a b - primePacketHeadBilinear H S T a b -
        ((H : ℝ) + 1) * primePacketHeadMean H S a * primePacketHeadMean H T b := by
    field_simp
    ring
  rw [he] at hs
  exact hs.congr_fun fun n => by unfold primePacketTailResidual; ring

/-- Exact bilinear projection onto the prefix and the forced conditional tail mean. -/
theorem primePacketBilinear_eq_head_add_tail (H : ℕ) (S T : Finset Nat.Primes)
    (a b : Nat.Primes → ℝ) :
    primePacketBilinear S T a b = primePacketHeadBilinear H S T a b +
      ((H : ℝ) + 1) * primePacketHeadMean H S a * primePacketHeadMean H T b +
        primePacketTailBilinear H S T a b := by
  have h := (hasSum_primePacketTailBilinear H S T a b).tsum_eq
  change primePacketTailBilinear H S T a b = _ at h
  linarith

theorem primePacketTailBilinear_self_nonneg (H : ℕ) (S : Finset Nat.Primes)
    (a : Nat.Primes → ℝ) : 0 ≤ primePacketTailBilinear H S S a a := by
  apply tsum_nonneg
  intro n
  exact div_nonneg (mul_self_nonneg _) (by positivity)

/-- Coherent prefix energy and its forced tail mean are unavoidable for arbitrary weights. -/
theorem primePacket_coherent_lower_bound (H : ℕ) (S : Finset Nat.Primes)
    (a : Nat.Primes → ℝ) :
    primePacketHeadBilinear H S S a a +
      ((H : ℝ) + 1) * primePacketHeadMean H S a ^ 2 ≤ primePacketBilinear S S a a := by
  have he := primePacketBilinear_eq_head_add_tail H S S a a
  have hn := primePacketTailBilinear_self_nonneg H S a
  nlinarith

/-- Restrict a prime packet to modes whose first jump lies beyond `H`. -/
def primePacketAbove (H : ℕ) (S : Finset Nat.Primes) : Finset Nat.Primes :=
  S.filter fun p => H < (p : ℕ)

def primePacketMass (S : Finset Nat.Primes) (a : Nat.Primes → ℝ) : ℝ :=
  ∑ p ∈ S, a p

def primePacketLogMoment (S : Finset Nat.Primes) (a : Nat.Primes → ℝ) : ℝ :=
  ∑ p ∈ S, a p * Real.log (p : ℕ)

/-- The finite pronic moments used by the coherent prefix. -/
def pronicPrefixMoment (H k : ℕ) : ℝ :=
  ∑ n ∈ range (H + 1), (n : ℝ) ^ k / ((n : ℝ) * ((n : ℝ) + 1))

/-- Before the first jump, every prime packet is affine in the observation index. -/
theorem primePacketValue_above_prefix (H : ℕ) (S : Finset Nat.Primes)
    (a : Nat.Primes → ℝ) (n : Fin (H + 1)) :
    primePacketValue (primePacketAbove H S) a n =
      primePacketLogMoment (primePacketAbove H S) a -
        (n.val : ℝ) * primePacketMass (primePacketAbove H S) a := by
  unfold primePacketValue primePacketLogMoment primePacketMass
  rw [mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  have hpH : H < (p : ℕ) := (mem_filter.mp hp).2
  have hnp : n.val < (p : ℕ) := by have := n.isLt; omega
  rw [pmRamanujanEnergyCenteredPrimitive, pmRamanujanPrimitive_prime p.property,
    Nat.mod_eq_of_lt hnp, vonMangoldt_apply_prime p.property]
  simp only [Complex.neg_re, Complex.natCast_re]
  ring

theorem primePacketHeadMean_above_eq (H : ℕ) (S : Finset Nat.Primes)
    (a : Nat.Primes → ℝ) :
    primePacketHeadMean H (primePacketAbove H S) a =
      pronicPrefixMoment H 0 * primePacketLogMoment (primePacketAbove H S) a -
        pronicPrefixMoment H 1 * primePacketMass (primePacketAbove H S) a := by
  simp only [primePacketHeadMean, pronicPrefixMoment, sum_mul, ← sum_sub_distrib]
  apply sum_congr rfl
  intro n hn
  rw [primePacketValue_above_prefix H S a ⟨n, mem_range.mp hn⟩]
  simp only [pow_zero, pow_one]
  ring

/-- The common-prefix bilinear form has only the mass and logarithmic-moment channels. -/
theorem primePacketHeadBilinear_above_eq (H : ℕ) (S T : Finset Nat.Primes)
    (a b : Nat.Primes → ℝ) :
    primePacketHeadBilinear H (primePacketAbove H S) (primePacketAbove H T) a b =
      pronicPrefixMoment H 0 * primePacketLogMoment (primePacketAbove H S) a *
        primePacketLogMoment (primePacketAbove H T) b -
      pronicPrefixMoment H 1 *
        (primePacketMass (primePacketAbove H S) a *
            primePacketLogMoment (primePacketAbove H T) b +
          primePacketLogMoment (primePacketAbove H S) a *
            primePacketMass (primePacketAbove H T) b) +
      pronicPrefixMoment H 2 * primePacketMass (primePacketAbove H S) a *
        primePacketMass (primePacketAbove H T) b := by
  simp only [primePacketHeadBilinear, pronicPrefixMoment, sum_mul,
    ← sum_sub_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro n hn
  rw [primePacketValue_above_prefix H S a ⟨n, mem_range.mp hn⟩,
    primePacketValue_above_prefix H T b ⟨n, mem_range.mp hn⟩]
  simp only [pow_zero, pow_one]
  ring

/-- Explicit moment lower bound for the unmodified energy-centered prime block. -/
theorem primePacket_two_moment_lower_bound (H : ℕ) (S : Finset Nat.Primes)
    (a : Nat.Primes → ℝ) :
    let A := primePacketMass (primePacketAbove H S) a
    let L := primePacketLogMoment (primePacketAbove H S) a
    pronicPrefixMoment H 0 * L ^ 2 - 2 * pronicPrefixMoment H 1 * A * L +
      pronicPrefixMoment H 2 * A ^ 2 +
      ((H : ℝ) + 1) * (pronicPrefixMoment H 0 * L - pronicPrefixMoment H 1 * A) ^ 2 ≤
      primePacketBilinear (primePacketAbove H S) (primePacketAbove H S) a a := by
  dsimp only
  have h := primePacket_coherent_lower_bound H (primePacketAbove H S) a
  rw [primePacketHeadMean_above_eq, primePacketHeadBilinear_above_eq] at h
  convert h using 1
  ring

/-- Every prime pair contains the full common-ramp contribution, even off the diagonal. -/
theorem primePair_common_prefix_lower_bound (p q : Nat.Primes) :
    (∑ n ∈ range (min (p : ℕ) (q : ℕ)), (n : ℝ) / ((n : ℝ) + 1)) -
      Real.log (p : ℕ) * Real.log (q : ℕ) ≤ pmRamanujanEnergyCenteredGram p q := by
  have hnon (n : ℕ) : 0 ≤ pmRamanujanPrimitiveGramTerm p q n := by
    rw [pmRamanujanPrimitiveGramTerm, pmRamanujanPrimitive_prime p.property,
      pmRamanujanPrimitive_prime q.property]
    simp only [Complex.neg_re, Complex.natCast_re, neg_mul_neg]
    positivity
  have hhead : (∑ n ∈ range (min (p : ℕ) (q : ℕ)),
      pmRamanujanPrimitiveGramTerm p q n) =
      ∑ n ∈ range (min (p : ℕ) (q : ℕ)), (n : ℝ) / ((n : ℝ) + 1) := by
    apply sum_congr rfl
    intro n hn
    have hnp := (mem_range.mp hn).trans_le (Nat.min_le_left (p : ℕ) (q : ℕ))
    have hnq := (mem_range.mp hn).trans_le (Nat.min_le_right (p : ℕ) (q : ℕ))
    rw [pmRamanujanPrimitiveGramTerm, pmRamanujanPrimitive_prime p.property,
      pmRamanujanPrimitive_prime q.property, Nat.mod_eq_of_lt hnp, Nat.mod_eq_of_lt hnq]
    simp only [Complex.neg_re, Complex.natCast_re, neg_mul_neg]
    by_cases hn0 : n = 0
    · simp [hn0]
    · have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
      field_simp
  have hbound := (summable_pmRamanujanPrimitiveGramTerm p.property.one_lt
    q.property.one_lt).sum_le_tsum (range (min (p : ℕ) (q : ℕ))) (fun n _ => hnon n)
  rw [hhead] at hbound
  change _ ≤ pmRamanujanPrimitiveGram p q at hbound
  rw [pmRamanujanPrimitiveGram_eq_energyCentered p.property.one_lt q.property.one_lt,
    vonMangoldt_apply_prime p.property, vonMangoldt_apply_prime q.property] at hbound
  linarith

end

end GaloisForLFunctions.BezoutValuationIncidence
