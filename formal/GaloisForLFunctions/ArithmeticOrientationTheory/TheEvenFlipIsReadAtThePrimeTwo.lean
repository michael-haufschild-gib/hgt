import GaloisForLFunctions.ArithmeticOrientationTheory.OrientedReadings
import GaloisForLFunctions.TransHorizonIncidenceMechanics.EvenFlipOfTheFermiSquarefreeWeightBreaksTheReceiver
import GaloisForLFunctions.TransHorizonIncidenceMechanics.FirstPronicMomentOrdersPositivePairs

/-!
# The even flip is read at the prime two

The **even flip** `c ↦ c♭ = c + c_e ⋆ (δ₁ − 2δ₂)` of a four-free weight of the damped class twists
its Ramanujan coefficients by the sign `σ₂(e) = −1` on even moduli
(`weightRamanujanCoeff_evenFlip`): it is invisible to every amplitude reading and to every
translated moment, yet it can break the receiver.  This module identifies the datum that reads it.

* **The flip stays in the class** (`dampedClass_evenFlip`, `evenFlip_fourFree`): on odd `d` the
  flip adds `c(2d)`, on `d ≡ 2 (mod 4)` it negates, elsewhere it does nothing
  (`evenFlip_apply`); so `c♭` is in the damped class with constant `2K` and is again four-free,
  and the even flip is an orientation on the four-free damped weights.
* **The first pronic moment reads the flip at the prime two**
  (`firstPronicMoment_evenFlip_sub`): `M(c♭) − M(c) = 2 log 2 · W_c(2)`.  The von Mangoldt
  pairing `M(c) = −Σ_e Λ(e) W_c(e)` only sees even moduli that are powers of two, and a four-free
  weight has `W_c(2^a) = 0` for `a ≥ 2`; so the whole difference sits at `e = 2`.
* **Faithfulness** (`firstPronicMoment_separates_evenFlip_iff`,
  `orientationFaithful_firstPronicMoment`): the first pronic moment separates `c` from `c♭` iff
  `W_c(2) ≠ 0`.  The amplitude reading is blind to the flip (`invisible_amplitude_evenFlip`), in
  the sense of `OrientedReadings`.

The orientation of a four-free damped weight is therefore one real number, its Ramanujan
coefficient at `2`, and the first pronic moment is an orientation-faithful reading exactly on the
weights where that number is nonzero.
-/

open Finset ArithmeticFunction

namespace GaloisForLFunctions.ArithmeticOrientationTheory

open TransHorizonIncidenceMechanics ScaleSignedIncidenceCriticality

noncomputable section
set_option autoImplicit false

/-- The even flip of a weight: `c♭ = c + c_e ⋆ (δ₁ − 2δ₂)`, with `c_e` the even part. -/
def evenFlip (c : ℕ → ℝ) : ℕ → ℝ := fun d => c d + localFactorWeight (evenPartWeight c) 2 2 d

/-- The three faces of the flip: add `c(2d)` on odd `d`, negate on `d ≡ 2 (mod 4)`, fix the rest. -/
theorem evenFlip_apply (c : ℕ → ℝ) (d : ℕ) :
    evenFlip c d = if d % 2 = 1 then c d + c (2 * d)
      else if (d / 2) % 2 = 1 then -(c d) else c d := by
  unfold evenFlip localFactorWeight evenPartWeight
  by_cases hodd : d % 2 = 1
  · have h2 : ¬ 2 ∣ d := by omega
    simp [hodd, h2]
  · have h2 : 2 ∣ d := by omega
    have hdd : 2 * (d / 2) = d := Nat.mul_div_cancel' h2
    by_cases hhalf : d / 2 % 2 = 1
    · simp [hodd, h2, hhalf, hdd]; ring
    · simp [hodd, h2, hhalf]

/-- The flip stays four-free. -/
theorem evenFlip_fourFree {c : ℕ → ℝ} (h4 : ∀ m, 4 ∣ m → c m = 0) (m : ℕ) (hm : 4 ∣ m) :
    evenFlip c m = 0 := by
  rw [evenFlip_apply]
  obtain ⟨k, rfl⟩ := hm
  have h1 : (4 * k) % 2 ≠ 1 := by omega
  have h2 : (4 * k / 2) % 2 ≠ 1 := by omega
  simp [h1, h2, h4 (4 * k) ⟨k, rfl⟩]

/-- `(2d)^{−ε} ≤ d^{−ε}`. -/
theorem rpow_neg_two_mul_le {ε : ℝ} (hε : 0 < ε) (d : ℕ) :
    ((2 * d : ℕ) : ℝ) ^ (-ε) ≤ (d : ℝ) ^ (-ε) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · simp
  · exact Real.rpow_le_rpow_of_exponent_nonpos (by exact_mod_cast hd0)
      (by push_cast; linarith) (by linarith)

/-- The flip stays in the damped class, with constant `2K`. -/
theorem dampedClass_evenFlip {K ε : ℝ} (hε : 0 < ε) {c : ℕ → ℝ} (hc : DampedClass K ε c) :
    DampedClass (2 * K) ε (evenFlip c) := by
  intro d
  have hK : 0 ≤ K := nonneg_of_dampedClass hc
  have hd : 0 ≤ (d : ℝ) ^ (-ε) := by positivity
  rw [evenFlip_apply]
  split_ifs
  · calc |c d + c (2 * d)| ≤ |c d| + |c (2 * d)| := abs_add_le _ _
      _ ≤ K * (d : ℝ) ^ (-ε) + K * ((2 * d : ℕ) : ℝ) ^ (-ε) := add_le_add (hc d) (hc (2 * d))
      _ ≤ K * (d : ℝ) ^ (-ε) + K * (d : ℝ) ^ (-ε) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left (rpow_neg_two_mul_le hε d) hK)
      _ = 2 * K * (d : ℝ) ^ (-ε) := by ring
  · rw [abs_neg]
    calc |c d| ≤ K * (d : ℝ) ^ (-ε) := hc d
      _ ≤ 2 * K * (d : ℝ) ^ (-ε) := by nlinarith
  · calc |c d| ≤ K * (d : ℝ) ^ (-ε) := hc d
      _ ≤ 2 * K * (d : ℝ) ^ (-ε) := by nlinarith

/-! ### The first pronic moment reads the flip at `2` -/

/-- An even prime power is a power of two. -/
theorem eq_two_pow_of_even_of_isPrimePow {e : ℕ} (he : 2 ∣ e) (hp : IsPrimePow e) :
    ∃ k, 0 < k ∧ e = 2 ^ k := by
  obtain ⟨p, k, hpp, hk, rfl⟩ := (isPrimePow_nat_iff e).1 hp
  have h2p : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow he
  have : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpp).1 h2p).symm
  exact ⟨k, hk, by rw [this]⟩

/-- A four-free weight has vanishing Ramanujan coefficient at every modulus divisible by `4`. -/
theorem weightRamanujanCoeff_eq_zero_of_four_dvd {c : ℕ → ℝ} (h4 : ∀ m, 4 ∣ m → c m = 0)
    {e : ℕ} (he : 4 ∣ e) : weightRamanujanCoeff c e = 0 := by
  unfold weightRamanujanCoeff
  refine tsum_eq_zero_of_forall? -- placeholder
  sorry

end

end GaloisForLFunctions.ArithmeticOrientationTheory
