import GaloisForLFunctions.ArithmeticOrientationTheory.OrientedReadings
import GaloisForLFunctions.TransHorizonIncidenceMechanics.EvenFlipOfTheFermiSquarefreeWeightBreaksTheReceiver
import GaloisForLFunctions.TransHorizonIncidenceMechanics.FirstPronicMomentOrdersPositivePairs

/-!
# The even flip is read at the prime two

The **even flip** `c ↦ c♭ = c + c_e ⋆ (δ₁ − 2δ₂)` of a four-free weight of the damped class twists
its Ramanujan coefficients by the sign `σ₂(e) = −1` on even moduli
(`weightRamanujanCoeff_evenFlip`): it is invisible to every amplitude reading and to every
translated moment, yet it can break the receiver.  This module identifies the datum that reads it.

* **The flip is an orientation** (`evenFlip_apply`, `evenFlip_evenFlip`, `dampedClass_evenFlip`,
  `evenFlip_fourFree`): on odd `d` the flip adds `c(2d)`, on `d ≡ 2 (mod 4)` it negates, elsewhere
  it does nothing; it is an involution, stays in the damped class with constant `2K`, and stays
  four-free.
* **The first pronic moment reads the flip at the prime two**
  (`firstPronicMoment_evenFlip_sub`): `M(c♭) − M(c) = 2 log 2 · W_c(2)`.  The von Mangoldt
  pairing `M(c) = −Σ_e Λ(e) W_c(e)` only sees even moduli that are powers of two, and a four-free
  weight has `W_c(2^a) = 0` for `a ≥ 2`; so the whole difference sits at `e = 2`.
* **Faithfulness and blindness** (`firstPronicMoment_separates_evenFlip_iff`,
  `orientationFaithful_firstPronicMoment`, `invisible_amplitude_evenFlip`): the first pronic
  moment separates `c` from `c♭` iff `W_c(2) ≠ 0`, while the amplitude reading is blind to the
  flip in the sense of `OrientedReadings`.

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

/-- The even flip is an involution. -/
theorem evenFlip_evenFlip (c : ℕ → ℝ) : evenFlip (evenFlip c) = c := by
  funext d
  rw [evenFlip_apply]
  by_cases hodd : d % 2 = 1
  · have h1 : (2 * d) % 2 ≠ 1 := by omega
    have h2 : (2 * d / 2) % 2 = 1 := by rw [Nat.mul_div_cancel_left d two_pos]; exact hodd
    rw [if_pos hodd, evenFlip_apply c d, if_pos hodd, evenFlip_apply c (2 * d), if_neg h1,
      if_pos h2]
    ring
  · rw [if_neg hodd]
    by_cases hhalf : d / 2 % 2 = 1
    · rw [if_pos hhalf, evenFlip_apply c d, if_neg hodd, if_pos hhalf, neg_neg]
    · rw [if_neg hhalf, evenFlip_apply c d, if_neg hodd, if_neg hhalf]

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
  obtain ⟨p, k, hpp, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hp
  have h2p : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow he
  have : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpp).1 h2p).symm
  exact ⟨k, hk, by rw [this]⟩

/-- A four-free weight has vanishing Ramanujan coefficient at every modulus divisible by `4`. -/
theorem weightRamanujanCoeff_eq_zero_of_four_dvd {c : ℕ → ℝ} (h4 : ∀ m, 4 ∣ m → c m = 0)
    {e : ℕ} (he : 4 ∣ e) : weightRamanujanCoeff c e = 0 := by
  unfold weightRamanujanCoeff
  have : (fun k : ℕ => c (e * k) / ((e * k : ℕ) : ℝ)) = fun _ => 0 := by
    funext k
    rw [h4 (e * k) (Dvd.dvd.mul_right he k), zero_div]
  rw [this, tsum_zero]

/-- The flip twists the Ramanujan coefficients by `σ₂`, restated for `evenFlip`. -/
theorem weightRamanujanCoeff_evenFlip' {K ε : ℝ} (hε : 0 < ε) {c : ℕ → ℝ}
    (hc : DampedClass K ε c) (h4 : ∀ m, 4 ∣ m → c m = 0) (e : ℕ) :
    weightRamanujanCoeff (evenFlip c) e = evenSign e * weightRamanujanCoeff c e :=
  weightRamanujanCoeff_evenFlip hε hc h4 e

/-- **The first pronic moment reads the even flip at the prime two**:
`M(c♭) − M(c) = 2 log 2 · W_c(2)`. -/
theorem firstPronicMoment_evenFlip_sub {K ε : ℝ} (hε : 0 < ε) {c : ℕ → ℝ}
    (hc : DampedClass K ε c) (h4 : ∀ m, 4 ∣ m → c m = 0) :
    firstPronicMoment (evenFlip c) - firstPronicMoment c =
      2 * Real.log 2 * weightRamanujanCoeff c 2 := by
  have hM : firstPronicMoment c = -∑' e : ℕ, Λ e * weightRamanujanCoeff c e :=
    (hasSum_firstPronicMoment hε hc).tsum_eq
  have hM' : firstPronicMoment (evenFlip c) =
      -∑' e : ℕ, Λ e * weightRamanujanCoeff (evenFlip c) e :=
    (hasSum_firstPronicMoment hε (dampedClass_evenFlip hε hc)).tsum_eq
  have hW := weightRamanujanCoeff_evenFlip' hε hc h4
  have hs : Summable (fun e : ℕ => Λ e * weightRamanujanCoeff c e) :=
    summable_vonMangoldt_mul_weightRamanujanCoeff hε hc
  have hs' : Summable (fun e : ℕ => Λ e * weightRamanujanCoeff (evenFlip c) e) :=
    summable_vonMangoldt_mul_weightRamanujanCoeff hε (dampedClass_evenFlip hε hc)
  rw [hM, hM', neg_sub_neg, ← hs.tsum_sub hs', tsum_eq_single 2]
  · rw [hW 2, vonMangoldt_apply_prime Nat.prime_two]
    simp only [evenSign, show (2 : ℕ) ∣ 2 from dvd_refl 2, if_true]
    ring
  · intro e he
    rw [hW e]
    by_cases h2 : 2 ∣ e
    · by_cases hΛ : Λ e = 0
      · simp [hΛ]
      · obtain ⟨k, hk, rfl⟩ := eq_two_pow_of_even_of_isPrimePow h2 (vonMangoldt_ne_zero_iff.1 hΛ)
        have hk2 : 2 ≤ k := by
          by_contra hlt
          have hk1 : k = 1 := by omega
          subst hk1
          exact he (by norm_num)
        have h4e : 4 ∣ 2 ^ k := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
          exact pow_dvd_pow 2 hk2
        rw [weightRamanujanCoeff_eq_zero_of_four_dvd h4 h4e]
        ring
    · have : evenSign e = 1 := by simp [evenSign, h2]
      rw [this]
      ring

/-- **Faithfulness criterion**: the first pronic moment separates `c` from its flip iff
`W_c(2) ≠ 0`. -/
theorem firstPronicMoment_separates_evenFlip_iff {K ε : ℝ} (hε : 0 < ε) {c : ℕ → ℝ}
    (hc : DampedClass K ε c) (h4 : ∀ m, 4 ∣ m → c m = 0) :
    firstPronicMoment (evenFlip c) ≠ firstPronicMoment c ↔ weightRamanujanCoeff c 2 ≠ 0 := by
  rw [Ne, ← sub_eq_zero, firstPronicMoment_evenFlip_sub hε hc h4]
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  constructor
  · intro h h0
    exact h (by rw [h0, mul_zero])
  · intro h h0
    exact h ((mul_eq_zero.1 h0).resolve_left (mul_pos two_pos hlog).ne')

/-! ### The orientation of four-free damped weights -/

/-- The four-free weights of the damped class at damping `ε`. -/
def FourFreeDamped (ε : ℝ) : Type :=
  {c : ℕ → ℝ // (∃ K : ℝ, DampedClass K ε c) ∧ ∀ m, 4 ∣ m → c m = 0}

/-- The even flip as an orientation of the four-free damped weights. -/
def evenFlipOrientation {ε : ℝ} (hε : 0 < ε) : Orientation (FourFreeDamped ε) where
  flip c := ⟨evenFlip c.1,
    ⟨let ⟨K, hK⟩ := c.2.1; ⟨2 * K, dampedClass_evenFlip hε hK⟩, evenFlip_fourFree c.2.2⟩⟩
  flip_flip c := Subtype.ext (evenFlip_evenFlip c.1)

/-- The amplitude reading: the absolute Ramanujan coefficients. -/
def amplitudeReading {ε : ℝ} (c : FourFreeDamped ε) : ℕ → ℝ :=
  fun e => |weightRamanujanCoeff c.1 e|

theorem abs_evenSign (e : ℕ) : |evenSign e| = 1 := by
  unfold evenSign; split_ifs <;> simp

/-- **The amplitude reading is blind to the even flip.** -/
theorem invisible_amplitude_evenFlip {ε : ℝ} (hε : 0 < ε) :
    Invisible (amplitudeReading (ε := ε)) (evenFlipOrientation hε).flip := by
  intro c
  funext e
  obtain ⟨⟨K, hK⟩, h4⟩ := c.2
  simp only [amplitudeReading, evenFlipOrientation]
  rw [weightRamanujanCoeff_evenFlip' hε hK h4 e, abs_mul, abs_evenSign, one_mul]

/-- The four-free damped weights with a nonzero Ramanujan coefficient at `2`. -/
def OrientedFourFreeDamped (ε : ℝ) : Type :=
  {c : FourFreeDamped ε // weightRamanujanCoeff c.1 2 ≠ 0}

/-- The even flip preserves the nonvanishing of `W_c(2)`, so it orients the subclass. -/
def evenFlipOrientation' {ε : ℝ} (hε : 0 < ε) : Orientation (OrientedFourFreeDamped ε) where
  flip c := ⟨(evenFlipOrientation hε).flip c.1, by
    obtain ⟨⟨K, hK⟩, h4⟩ := c.1.2
    show weightRamanujanCoeff (evenFlip c.1.1) 2 ≠ 0
    rw [weightRamanujanCoeff_evenFlip' hε hK h4 2]
    simp only [evenSign, show (2 : ℕ) ∣ 2 from dvd_refl 2, if_true, neg_one_mul, ne_eq, neg_eq_zero]
    exact c.2⟩
  flip_flip c := Subtype.ext ((evenFlipOrientation hε).flip_flip c.1)

/-- **The first pronic moment is orientation-faithful** on the weights with `W_c(2) ≠ 0`. -/
theorem orientationFaithful_firstPronicMoment {ε : ℝ} (hε : 0 < ε) :
    OrientationFaithful (fun c : OrientedFourFreeDamped ε => firstPronicMoment c.1.1)
      (evenFlipOrientation' hε).flip := by
  intro c _
  obtain ⟨⟨K, hK⟩, h4⟩ := c.1.2
  show firstPronicMoment (evenFlip c.1.1) ≠ firstPronicMoment c.1.1
  exact (firstPronicMoment_separates_evenFlip_iff hε hK h4).2 c.2

end

end GaloisForLFunctions.ArithmeticOrientationTheory
