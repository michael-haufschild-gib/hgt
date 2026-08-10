import GaloisForLFunctions.HTGeometry.ZeroEstimate
import Mathlib.Analysis.PSeries

/-!
# The prime-log height source

The finitely supported integer prime-exponent lattice `Γ = ℤ^(ℙ)` carries a multiplicative
height `H(m) = ∏_p p^{|m_p|}` and a signed prime-log frequency `ℓ(m) = ∑_p m_p log p`.

`H` is submultiplicative, reflection invariant, and homogeneous of degree `q` under `m ↦ q·m`;
`ℓ` is additive and odd.  Unique factorization gives the two-sided comparison
`H(m)⁻¹ ≤ |ℓ(m)| ≤ log H(m) ≤ H(m)` for `m ≠ 0`, so the height is a scale on which the inverse of
the gapless frequency is tame.

Splitting `m` into its positive and negative prime products embeds `Γ` into pairs of positive
integers, which makes `∑_m H(m)^{-2}` a subseries of `ζ(2)²` and hence finite.
-/

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-- The finitely supported integer prime-exponent lattice `Γ = ℤ^(ℙ)`. -/
abbrev DeningerLattice := Nat.Primes →₀ ℤ

/-! ## Finite prime products -/

/-- Prime products turn addition of exponent vectors into multiplication. -/
theorem deningerPrimeProduct_add (u v : Nat.Primes →₀ ℕ) :
    primeProduct (u + v) = primeProduct u * primeProduct v := by
  unfold primeProduct
  exact Finsupp.prod_add_index' (by simp) (by intro a b₁ b₂; rw [pow_add])

/-- Prime products are monotone in the exponent vector. -/
theorem deningerPrimeProduct_mono {u v : Nat.Primes →₀ ℕ} (h : u ≤ v) :
    primeProduct u ≤ primeProduct v := by
  have hv : u + (v - u) = v := add_tsub_cancel_of_le h
  calc primeProduct u ≤ primeProduct u * primeProduct (v - u) :=
        Nat.le_mul_of_pos_right _ (primeProduct_pos _)
    _ = primeProduct (u + (v - u)) := (deningerPrimeProduct_add _ _).symm
    _ = primeProduct v := by rw [hv]

/-- Prime products of scaled exponent vectors are powers. -/
theorem deningerPrimeProduct_nsmul (q : ℕ) (u : Nat.Primes →₀ ℕ) :
    primeProduct (q • u) = primeProduct u ^ q := by
  induction q with
  | zero => simp [primeProduct]
  | succ q ih =>
      have hsucc : (q + 1) • u = q • u + u := by
        rw [succ_nsmul]
      rw [hsucc, deningerPrimeProduct_add, ih, pow_succ]

/-! ## Height and frequency -/

/-- The absolute exponent vector `p ↦ |m_p|`. -/
def deningerAbsExponent (m : Nat.Primes →₀ ℤ) : Nat.Primes →₀ ℕ :=
  m.mapRange Int.natAbs (by simp)

@[simp]
theorem deningerAbsExponent_apply (m : Nat.Primes →₀ ℤ) (p : Nat.Primes) :
    deningerAbsExponent m p = (m p).natAbs := rfl

@[simp]
theorem deningerAbsExponent_zero : deningerAbsExponent 0 = 0 := by
  ext p; simp

theorem deningerAbsExponent_neg (m : Nat.Primes →₀ ℤ) :
    deningerAbsExponent (-m) = deningerAbsExponent m := by
  ext p; simp

theorem deningerAbsExponent_add_le (m n : Nat.Primes →₀ ℤ) :
    deningerAbsExponent (m + n) ≤ deningerAbsExponent m + deningerAbsExponent n := by
  rw [Finsupp.le_def]
  intro p
  simpa using Int.natAbs_add_le (m p) (n p)

theorem deningerAbsExponent_nsmul (q : ℕ) (m : Nat.Primes →₀ ℤ) :
    deningerAbsExponent (q • m) = q • deningerAbsExponent m := by
  ext p
  simp [Int.natAbs_mul]

/-- The multiplicative height `H(m) = ∏_p p^{|m_p|}` of an exponent vector. -/
def deningerHeightNat (m : Nat.Primes →₀ ℤ) : ℕ :=
  primeProduct (deningerAbsExponent m)

/-- The multiplicative height as a real number. -/
def deningerHeight (m : Nat.Primes →₀ ℤ) : ℝ := (deningerHeightNat m : ℝ)

theorem deningerHeightNat_pos (m : Nat.Primes →₀ ℤ) : 0 < deningerHeightNat m :=
  primeProduct_pos _

theorem one_le_deningerHeight (m : Nat.Primes →₀ ℤ) : 1 ≤ deningerHeight m := by
  have h : (1 : ℕ) ≤ deningerHeightNat m := deningerHeightNat_pos m
  show (1 : ℝ) ≤ (deningerHeightNat m : ℝ)
  exact_mod_cast h

theorem deningerHeight_pos (m : Nat.Primes →₀ ℤ) : 0 < deningerHeight m :=
  lt_of_lt_of_le zero_lt_one (one_le_deningerHeight m)

@[simp]
theorem deningerHeight_zero : deningerHeight 0 = 1 := by
  simp [deningerHeight, deningerHeightNat, primeProduct]

theorem deningerHeight_neg (m : Nat.Primes →₀ ℤ) :
    deningerHeight (-m) = deningerHeight m := by
  simp [deningerHeight, deningerHeightNat, deningerAbsExponent_neg]

/-- Submultiplicativity of the height. -/
theorem deningerHeight_add_le (m n : Nat.Primes →₀ ℤ) :
    deningerHeight (m + n) ≤ deningerHeight m * deningerHeight n := by
  have hnat : deningerHeightNat (m + n) ≤ deningerHeightNat m * deningerHeightNat n := by
    unfold deningerHeightNat
    calc primeProduct (deningerAbsExponent (m + n))
        ≤ primeProduct (deningerAbsExponent m + deningerAbsExponent n) :=
          deningerPrimeProduct_mono (deningerAbsExponent_add_le m n)
      _ = primeProduct (deningerAbsExponent m) * primeProduct (deningerAbsExponent n) :=
          deningerPrimeProduct_add _ _
  calc deningerHeight (m + n) = (deningerHeightNat (m + n) : ℝ) := rfl
    _ ≤ ((deningerHeightNat m * deningerHeightNat n : ℕ) : ℝ) := by exact_mod_cast hnat
    _ = deningerHeight m * deningerHeight n := by push_cast [deningerHeight]; ring

/-- The height is homogeneous of degree `q` along `m ↦ q·m`. -/
theorem deningerHeight_nsmul (q : ℕ) (m : Nat.Primes →₀ ℤ) :
    deningerHeight (q • m) = deningerHeight m ^ q := by
  have hnat : deningerHeightNat (q • m) = deningerHeightNat m ^ q := by
    unfold deningerHeightNat
    rw [deningerAbsExponent_nsmul, deningerPrimeProduct_nsmul]
  simp [deningerHeight, hnat]

/-- The signed prime-log frequency `ℓ(m) = ∑_p m_p log p`. -/
def deningerFreq (m : Nat.Primes →₀ ℤ) : ℝ :=
  m.sum fun p z => (z : ℝ) * Real.log (p : ℕ)

@[simp]
theorem deningerFreq_zero : deningerFreq 0 = 0 := by
  simp [deningerFreq]

theorem deningerFreq_add (m n : Nat.Primes →₀ ℤ) :
    deningerFreq (m + n) = deningerFreq m + deningerFreq n := by
  refine Finsupp.sum_add_index' (by simp) ?_
  intro a b₁ b₂
  push_cast
  ring

theorem deningerFreq_neg (m : Nat.Primes →₀ ℤ) :
    deningerFreq (-m) = -deningerFreq m := by
  have h : deningerFreq (-m) + deningerFreq m = 0 := by
    rw [← deningerFreq_add]
    simp
  linarith

theorem deningerFreq_nsmul (q : ℕ) (m : Nat.Primes →₀ ℤ) :
    deningerFreq (q • m) = q * deningerFreq m := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hsucc : (q + 1) • m = q • m + m := by rw [succ_nsmul]
      rw [hsucc, deningerFreq_add, ih]
      push_cast
      ring

/-! ## The two-sided comparison of frequency and height -/

/-- The height splits as the product of the positive and negative prime parts. -/
theorem deningerHeightNat_eq_primeLogHeight (m : Nat.Primes →₀ ℤ) :
    deningerHeightNat m = primeLogHeight m := by
  have hsplit : positivePart m + negativePart m = deningerAbsExponent m := by
    ext p
    show (m p).toNat + (-(m p)).toNat = (m p).natAbs
    omega
  unfold deningerHeightNat primeLogHeight
  rw [← hsplit, deningerPrimeProduct_add]

/-- **Prime-log height bound.** The inverse height is a lower bound for the frequency. -/
theorem deningerHeight_inv_le_abs_freq {m : Nat.Primes →₀ ℤ} (hm : m ≠ 0) :
    (deningerHeight m)⁻¹ ≤ |deningerFreq m| := by
  have h := logPrime_height_bound m hm
  rw [deningerHeight, deningerHeightNat_eq_primeLogHeight]
  exact h

theorem deningerFreq_ne_zero {m : Nat.Primes →₀ ℤ} (hm : m ≠ 0) : deningerFreq m ≠ 0 := by
  intro h
  have hle := deningerHeight_inv_le_abs_freq hm
  rw [h, abs_zero] at hle
  have hpos : 0 < (deningerHeight m)⁻¹ := inv_pos.mpr (deningerHeight_pos m)
  linarith

/-- The frequency vanishes exactly at the zero exponent vector. -/
theorem deningerFreq_eq_zero_iff (m : Nat.Primes →₀ ℤ) :
    deningerFreq m = 0 ↔ m = 0 := by
  constructor
  · intro h
    by_contra hm
    exact deningerFreq_ne_zero hm h
  · intro h; rw [h, deningerFreq_zero]

/-- The frequency is bounded by the logarithmic height. -/
theorem abs_deningerFreq_le_log_height (m : Nat.Primes →₀ ℤ) :
    |deningerFreq m| ≤ Real.log (deningerHeight m) := by
  have hlog : Real.log (deningerHeight m)
      = m.sum fun p z => |(z : ℝ)| * Real.log (p : ℕ) := by
    rw [deningerHeight, deningerHeightNat, log_primeProduct]
    unfold deningerAbsExponent
    rw [Finsupp.sum_mapRange_index (by simp)]
    refine Finsupp.sum_congr ?_
    intro p _
    congr 1
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  rw [hlog, deningerFreq, Finsupp.sum, Finsupp.sum]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [abs_mul, abs_of_nonneg (Real.log_natCast_nonneg (p : ℕ))]

theorem log_deningerHeight_le_height (m : Nat.Primes →₀ ℤ) :
    Real.log (deningerHeight m) ≤ deningerHeight m := by
  have h := Real.log_le_sub_one_of_pos (deningerHeight_pos m)
  linarith

theorem abs_deningerFreq_le_height (m : Nat.Primes →₀ ℤ) :
    |deningerFreq m| ≤ deningerHeight m :=
  le_trans (abs_deningerFreq_le_log_height m) (log_deningerHeight_le_height m)

/-! ## Counting: the height is square summable in the inverse -/

/-- The positive and negative prime products of an exponent vector. -/
def deningerHeightSplit (m : Nat.Primes →₀ ℤ) : ℕ × ℕ :=
  (primeProduct (positivePart m), primeProduct (negativePart m))

theorem deningerHeightSplit_injective : Function.Injective deningerHeightSplit := by
  intro m n h
  have hpos : positivePart m = positivePart n :=
    primeProduct_injective (congrArg Prod.fst h)
  have hneg : negativePart m = negativePart n :=
    primeProduct_injective (congrArg Prod.snd h)
  have hposZ : positivePartZ m = positivePartZ n := by
    ext p
    have := congrArg (fun f : Nat.Primes →₀ ℕ => f p) hpos
    show ((m p).toNat : ℤ) = ((n p).toNat : ℤ)
    exact_mod_cast this
  have hnegZ : negativePartZ m = negativePartZ n := by
    ext p
    have := congrArg (fun f : Nat.Primes →₀ ℕ => f p) hneg
    show ((-(m p)).toNat : ℤ) = ((-(n p)).toNat : ℤ)
    exact_mod_cast this
  calc m = positivePartZ m - negativePartZ m := (positivePartZ_sub_negativePartZ m).symm
    _ = positivePartZ n - negativePartZ n := by rw [hposZ, hnegZ]
    _ = n := positivePartZ_sub_negativePartZ n

theorem deningerHeight_eq_split (m : Nat.Primes →₀ ℤ) :
    deningerHeight m
      = ((deningerHeightSplit m).1 : ℝ) * ((deningerHeightSplit m).2 : ℝ) := by
  rw [deningerHeight, deningerHeightNat_eq_primeLogHeight]
  simp [primeLogHeight, deningerHeightSplit]

/-- **The inverse height is square summable over the exponent lattice.**  The positive and
negative prime products embed the lattice into pairs of positive integers, so the series is a
subseries of `ζ(2)²`. -/
private theorem deningerHeightPair_summable :
    Summable fun q : ℕ × ℕ => (1 / ((q.1 : ℝ) ^ 2)) * (1 / ((q.2 : ℝ) ^ 2)) := by
  have hone : Summable (fun n : ℕ => 1 / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hnn : (0 : ℕ → ℝ) ≤ fun n : ℕ => 1 / (n : ℝ) ^ 2 := by
    intro n; positivity
  exact Summable.mul_of_nonneg (f := fun n : ℕ => 1 / (n : ℝ) ^ 2)
    (g := fun n : ℕ => 1 / (n : ℝ) ^ 2) hone hone hnn hnn

private theorem deningerHeightSplit_summable :
    Summable fun m : Nat.Primes →₀ ℤ =>
      (1 / (((deningerHeightSplit m).1 : ℝ) ^ 2)) *
        (1 / (((deningerHeightSplit m).2 : ℝ) ^ 2)) :=
  deningerHeightPair_summable.comp_injective deningerHeightSplit_injective

theorem deningerHeight_summable_inv_sq :
    Summable fun m : Nat.Primes →₀ ℤ => (deningerHeight m)⁻¹ ^ 2 := by
  refine deningerHeightSplit_summable.congr fun m => ?_
  rw [deningerHeight_eq_split m, mul_inv, mul_pow]
  rw [one_div, one_div, inv_pow, inv_pow]

end

end RHTower
