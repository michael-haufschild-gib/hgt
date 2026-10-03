import GaloisForLFunctions.HTGeometry.ThreeFiveOrbitKorobovBound
import GaloisForLFunctions.HTGeometry.DiscreteWeylCriterion

/-!
# Equidistribution of `4ⁿ(α_{2,3} + α_{2,5})` and the parity drift

The sum `x = α₃ + α₅` of the Stoneham constants for `3` and `5` has two incommensurable forcings.
On the window `3ᵃ, 5ᵇ ≤ 2n < 3^{a+1}, 5^{b+1}` one has `4ⁿx = R(n)/(3ᵃ5ᵇ) + O(1/n)` with
`R(n + i) = 4ⁱ R(n)` (`four_pow_mul_pairStoneham`, `pairNum_add`).  On each window the digits
follow an orbit of `4` modulo `Q = 3ᵃ5ᵇ` of length at most `3ᵃ ≍ √Q`, which completion cannot
reach.

* Korobov's bound (`norm_sum_sixteen_pow_twelve_le`) gives
  `‖Σ_{window} e(k R(n)/Q)‖ ≤ C_k Q^{11/24}` (`norm_sum_window_le`).
* Summing over the geometric family of windows gives `Σ_{n<N} e(k 4ⁿx) = O_k(N^{11/12})` for every
  `k ≠ 0` (`tendsto_weylSum_pairOrbit`).
* Weyl's criterion then gives equidistribution of `{4ⁿx}` in every interval `[a, b) ⊂ (0, 1)`
  (`tendsto_card_fract_pairOrbit`).
* Hence the parity drift is `o(N)` (`tendsto_drift_pairStoneham`,
  `not_parityDriftHypothesis_pairStoneham`).
-/

open Finset Filter Topology

namespace GaloisForLFunctions.HTGeometry.StonehamPairDrift

open StonehamParityDrift StonehamPrimeDrift ThreeFiveOrbit DiscreteWeyl BinaryParityDrift

/-- The sum `α_{2,3} + α_{2,5}` of the Stoneham constants for `3` and `5`. -/
noncomputable def pairStoneham : ℝ := stonehamP 3 + stonehamP 5

/-- The orbit numerator `R(n) = 2^{2n−3ᵃ} A₃ 5ᵇ + 2^{2n−5ᵇ} A₅ 3ᵃ` on the window `(a, b)`. -/
def pairNum (a b n : ℕ) : ℕ :=
  2 ^ (2 * n - 3 ^ a) * stonehamPA 3 a * 5 ^ b + 2 ^ (2 * n - 5 ^ b) * stonehamPA 5 b * 3 ^ a

theorem pairNum_add {a b n : ℕ} (ha : 3 ^ a ≤ 2 * n) (hb : 5 ^ b ≤ 2 * n) (i : ℕ) :
    pairNum a b (n + i) = pairNum a b n * 4 ^ i := by
  unfold pairNum
  rw [show 2 * (n + i) - 3 ^ a = (2 * n - 3 ^ a) + 2 * i by omega,
    show 2 * (n + i) - 5 ^ b = (2 * n - 5 ^ b) + 2 * i by omega, pow_add, pow_add, pow_mul]
  norm_num
  ring

theorem not_dvd_pairNum {p : ℕ} (hp : p.Prime) (hp35 : p = 3 ∨ p = 5) {a b n : ℕ} (ha : 1 ≤ a)
    (hb : 1 ≤ b) : ¬ p ∣ pairNum a b n := by
  have h2 : ¬ p ∣ 2 := by rcases hp35 with rfl | rfl <;> norm_num
  intro h
  unfold pairNum at h
  rcases hp35 with rfl | rfl
  · have h3 : 3 ∣ 2 ^ (2 * n - 5 ^ b) * stonehamPA 5 b * 3 ^ a :=
      Dvd.dvd.mul_left (dvd_pow_self 3 (by omega)) _
    have h' := (Nat.dvd_add_left h3).mp h
    have hA := stonehamPA_mod (p := 3) (by norm_num) ha
    rcases (Nat.Prime.dvd_mul hp).mp h' with h' | h'
    · rcases (Nat.Prime.dvd_mul hp).mp h' with h' | h'
      · exact h2 (hp.dvd_of_dvd_pow h')
      · omega
    · exact absurd (hp.dvd_of_dvd_pow h') (by norm_num)
  · have h5 : 5 ∣ 2 ^ (2 * n - 3 ^ a) * stonehamPA 3 a * 5 ^ b :=
      Dvd.dvd.mul_left (dvd_pow_self 5 (by omega)) _
    have h' := (Nat.dvd_add_right h5).mp h
    have hA := stonehamPA_mod (p := 5) (by norm_num) hb
    rcases (Nat.Prime.dvd_mul hp).mp h' with h' | h'
    · rcases (Nat.Prime.dvd_mul hp).mp h' with h' | h'
      · exact h2 (hp.dvd_of_dvd_pow h')
      · omega
    · exact absurd (hp.dvd_of_dvd_pow h') (by norm_num)

theorem coprime_pairNum {a b n : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    Nat.Coprime (pairNum a b n) (3 ^ a * 5 ^ b) := by
  refine Nat.Coprime.mul_right (Nat.Coprime.pow_right _ ?_) (Nat.Coprime.pow_right _ ?_)
  · exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (not_dvd_pairNum Nat.prime_three (Or.inl rfl) ha hb)))
  · exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr
      (not_dvd_pairNum Nat.prime_five (Or.inr rfl) ha hb)))

/-- **The window identity.**  On the window `3ᵃ, 5ᵇ ≤ 2n < 3^{a+1}, 5^{b+1}`,
`4ⁿ (α₃ + α₅) = R(n)/(3ᵃ5ᵇ) + t` with `0 < t < 1/(4·3ᵃ) + 1/(4·5ᵇ)`. -/
theorem four_pow_mul_pairStoneham {a b n : ℕ} (ha1 : 3 ^ a ≤ 2 * n) (ha2 : 2 * n < 3 ^ (a + 1))
    (hb1 : 5 ^ b ≤ 2 * n) (hb2 : 2 * n < 5 ^ (b + 1)) :
    ∃ t : ℝ, 0 < t ∧ t < 1 / (4 * 3 ^ a) + 1 / (4 * 5 ^ b) ∧
      (4 : ℝ) ^ n * pairStoneham = (pairNum a b n : ℝ) / (3 ^ a * 5 ^ b) + t := by
  obtain ⟨t₃, h₃0, h₃1, h₃⟩ := four_pow_mul_stonehamP (p := 3) (by norm_num) (by norm_num) ha1 ha2
  obtain ⟨t₅, h₅0, h₅1, h₅⟩ := four_pow_mul_stonehamP (p := 5) (by norm_num) (by norm_num) hb1 hb2
  refine ⟨t₃ + t₅, by positivity, ?_, ?_⟩
  · push_cast at h₃1 h₅1
    have e3 : t₃ < 1 / (4 * 3 ^ a) := by rw [lt_div_iff₀ (by positivity)]; linarith
    have e5 : t₅ < 1 / (4 * 5 ^ b) := by rw [lt_div_iff₀ (by positivity)]; linarith
    linarith
  · rw [pairStoneham, mul_add, h₃, h₅]
    unfold pairNum
    push_cast
    field_simp
    ring

/-- `‖e^{ix} − 1‖ ≤ |x|`. -/
theorem norm_exp_mul_I_sub_one_le (x : ℝ) : ‖Complex.exp (x * Complex.I) - 1‖ ≤ |x| := by
  rw [mul_comm, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_two]
  have := Real.abs_sin_le_abs (x := x / 2)
  rw [abs_div, abs_two] at this
  linarith

/-- The orbit `yₙ = 4ⁿ (α₃ + α₅)`. -/
noncomputable def pairOrbit (n : ℕ) : ℝ := 4 ^ n * pairStoneham

/-- The window exponent `a(n) = ⌊log₃ 2n⌋`. -/
def logThree (n : ℕ) : ℕ := Nat.log 3 (2 * n)

/-- The window exponent `b(n) = ⌊log₅ 2n⌋`. -/
def logFive (n : ℕ) : ℕ := Nat.log 5 (2 * n)

/-- The modulus `Q(n) = 3^{a(n)} 5^{b(n)}`. -/
def pairModulus (n : ℕ) : ℕ := 3 ^ logThree n * 5 ^ logFive n

/-- The rational approximation `e(k R(n)/Q(n))` of `e(k 4ⁿ x)`. -/
noncomputable def pairPhase (k n : ℕ) : ℂ :=
  ephase (pairModulus n) ((k : ℤ) * pairNum (logThree n) (logFive n) n)

theorem logThree_spec {n : ℕ} (hn : 1 ≤ n) :
    3 ^ logThree n ≤ 2 * n ∧ 2 * n < 3 ^ (logThree n + 1) :=
  ⟨Nat.pow_log_le_self 3 (by omega), Nat.lt_pow_succ_log_self (by norm_num) _⟩

theorem logFive_spec {n : ℕ} (hn : 1 ≤ n) :
    5 ^ logFive n ≤ 2 * n ∧ 2 * n < 5 ^ (logFive n + 1) :=
  ⟨Nat.pow_log_le_self 5 (by omega), Nat.lt_pow_succ_log_self (by norm_num) _⟩

/-- **The rational approximation is good.**  `‖e(k 4ⁿ x) − e(k R(n)/Q(n))‖ ≤ 2π k / n`. -/
theorem norm_exp_sub_pairPhase_le (k : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    ‖Complex.exp (2 * Real.pi * Complex.I * k * pairOrbit n) - pairPhase k n‖
      ≤ 2 * Real.pi * k / n := by
  obtain ⟨ha1, ha2⟩ := logThree_spec hn
  obtain ⟨hb1, hb2⟩ := logFive_spec hn
  obtain ⟨t, ht0, ht1, ht⟩ := four_pow_mul_pairStoneham ha1 ha2 hb1 hb2
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have h3 : (2 * n : ℝ) < 3 * 3 ^ logThree n := by
    have : 2 * n < 3 ^ (logThree n + 1) := ha2
    rw [pow_succ] at this; exact_mod_cast (by omega : 2 * n < 3 * 3 ^ logThree n)
  have h5 : (2 * n : ℝ) < 5 * 5 ^ logFive n := by
    have : 2 * n < 5 ^ (logFive n + 1) := hb2
    rw [pow_succ] at this; exact_mod_cast (by omega : 2 * n < 5 * 5 ^ logFive n)
  have htn : t ≤ 1 / n := by
    have e3 : 1 / (4 * (3 : ℝ) ^ logThree n) ≤ 3 / (8 * n) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    have e5 : 1 / (4 * (5 : ℝ) ^ logFive n) ≤ 5 / (8 * n) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    have : 3 / (8 * (n : ℝ)) + 5 / (8 * n) = 1 / n := by field_simp; ring
    linarith
  have hsplit : Complex.exp (2 * Real.pi * Complex.I * k * pairOrbit n) =
      pairPhase k n * Complex.exp (((2 * Real.pi * k * t : ℝ)) * Complex.I) := by
    rw [pairOrbit, ht, pairPhase, ephase, ← Complex.exp_add]
    congr 1
    unfold pairModulus
    push_cast
    field_simp
  rw [hsplit, ← mul_sub_one, norm_mul, show ‖pairPhase k n‖ = 1 from norm_ephase _ _, one_mul]
  refine (norm_exp_mul_I_sub_one_le _).trans ?_
  rw [abs_of_nonneg (by positivity)]
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  calc 2 * Real.pi * k * t ≤ 2 * Real.pi * k * (1 / n) := by gcongr
    _ = 2 * Real.pi * k / n := by ring

/-! ### Window sums -/

/-- The constant of the window bound. -/
noncomputable def pairConst (k : ℕ) : ℝ :=
  2 * ((2 : ℝ) ^ 12 * 18 ^ 3 * (3 ^ 9 * 5 ^ 9 * (5 * k) ^ 2)) ^ ((1 : ℝ) / 12) *
    5 ^ ((11 : ℝ) / 24) + 1

/-- From a twelfth-power bound at scale `P = √(5Q)` to a bound by `Q^{11/24}`. -/
theorem le_of_pow_twelve_le {X M Q : ℝ} (hX : 0 ≤ X) (hM : 0 ≤ M) (hQ : 0 ≤ Q)
    (h : X ^ 12 ≤ M * Real.sqrt (5 * Q) ^ 11) :
    X ≤ M ^ ((1 : ℝ) / 12) * 5 ^ ((11 : ℝ) / 24) * Q ^ ((11 : ℝ) / 24) := by
  have h1 : X = (X ^ 12) ^ ((1 : ℝ) / 12) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX]; norm_num
  have h2 : Real.sqrt (5 * Q) ^ 11 = (5 * Q) ^ ((11 : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  rw [h1]
  calc (X ^ 12) ^ ((1 : ℝ) / 12) ≤ (M * Real.sqrt (5 * Q) ^ 11) ^ ((1 : ℝ) / 12) :=
        Real.rpow_le_rpow (by positivity) h (by norm_num)
    _ = M ^ ((1 : ℝ) / 12) * ((5 * Q) ^ ((11 : ℝ) / 2)) ^ ((1 : ℝ) / 12) := by
        rw [Real.mul_rpow hM (by positivity), h2]
    _ = M ^ ((1 : ℝ) / 12) * (5 ^ ((11 : ℝ) / 24) * Q ^ ((11 : ℝ) / 24)) := by
        rw [← Real.rpow_mul (by positivity), Real.mul_rpow (by norm_num) hQ]; norm_num
    _ = _ := by ring

/-- **Window sums.**  For `R` prime to `Q = 3ᵃ5ᵇ`, `L ≤ 3ᵃ ≤ 5^{b+1}` and `k ≥ 1`,
`‖Σ_{i<L} e(k R 4ⁱ/Q)‖ ≤ C_k Q^{11/24}`. -/
theorem norm_sum_four_orbit_le {a b k R L : ℕ} (hk : 0 < k) (hR : Nat.Coprime R (3 ^ a * 5 ^ b))
    (hL : L ≤ 3 ^ a) (h35 : 3 ^ a ≤ 5 ^ (b + 1)) :
    ‖∑ i ∈ range L, ephase (3 ^ a * 5 ^ b) ((k : ℤ) * R * 4 ^ i)‖ ≤
      pairConst k * ((3 : ℝ) ^ a * 5 ^ b) ^ ((11 : ℝ) / 24) := by
  obtain ⟨g, hg⟩ : ∃ g, g = Nat.gcd k (3 ^ a * 5 ^ b) := ⟨_, rfl⟩
  have hg0 : 0 < g := hg ▸ Nat.gcd_pos_of_pos_left _ hk
  obtain ⟨k', hk'⟩ : g ∣ k := hg ▸ Nat.gcd_dvd_left _ _
  obtain ⟨Q', hQ'⟩ : g ∣ 3 ^ a * 5 ^ b := hg ▸ Nat.gcd_dvd_right _ _
  have hcop : Nat.Coprime k' Q' := by
    have := Nat.coprime_div_gcd_div_gcd (m := k) (n := 3 ^ a * 5 ^ b) (hg ▸ hg0)
    rwa [← hg, hk', hQ', Nat.mul_div_cancel_left _ hg0, Nat.mul_div_cancel_left _ hg0] at this
  have hgk : g ≤ k := by rw [hk']; exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero
    fun h => by simp [h] at hk'; omega)
  obtain ⟨g₁, g₂, hg₁, hg₂, hg12⟩ := Nat.dvd_mul.mp (show g ∣ 3 ^ a * 5 ^ b from ⟨Q', hQ'⟩)
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hg₁
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp hg₂
  have hQ'eq : Q' = 3 ^ (a - i) * 5 ^ (b - j) := by
    have h1 : 3 ^ a * 5 ^ b = (3 ^ i * 5 ^ j) * (3 ^ (a - i) * 5 ^ (b - j)) := by
      rw [mul_mul_mul_comm, ← pow_add, ← pow_add, Nat.add_sub_cancel' hi,
        Nat.add_sub_cancel' hj]
    rw [hQ', hg12] at h1
    exact Nat.eq_of_mul_eq_mul_left (hg12 ▸ hg0) h1
  subst hQ'eq
  -- reduce the modulus
  have hred : ∀ m : ℕ, ephase (3 ^ a * 5 ^ b) ((k : ℤ) * R * 4 ^ m) =
      ephase (3 ^ (a - i) * 5 ^ (b - j)) ((k' : ℤ) * R * 4 ^ m) := by
    intro m
    have e1 : 3 ^ a * 5 ^ b = 3 ^ (a - i) * 5 ^ (b - j) * g := by rw [hQ', mul_comm]
    have e2 : (k : ℤ) * R * 4 ^ m = (g : ℤ) * ((k' : ℤ) * R * 4 ^ m) := by
      rw [hk']; push_cast; ring
    rw [e1, e2, ephase_mul_left_cancel hg0.ne']
  simp_rw [hred]
  -- the scale
  obtain ⟨Qr, hQr⟩ : ∃ Qr : ℝ, Qr = (3 : ℝ) ^ a * 5 ^ b := ⟨_, rfl⟩
  rw [← hQr]
  have hQr1 : 1 ≤ Qr := by
    rw [hQr]
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ (by norm_num))
  have hQnat : ((3 ^ a * 5 ^ b : ℕ) : ℝ) = Qr := by rw [hQr]; push_cast; ring
  have hgQ' : ((3 ^ a * 5 ^ b : ℕ) : ℝ) = g * ((3 ^ (a - i) * 5 ^ (b - j) : ℕ) : ℝ) := by
    exact_mod_cast hQ'
  have hL2 : ((L / 2 : ℕ) : ℝ) ^ 2 ≤ 5 * Qr := by
    have h1 : (L / 2) ^ 2 ≤ 3 ^ a * 3 ^ a :=
      (Nat.pow_le_pow_left ((Nat.div_le_self L 2).trans hL) 2).trans_eq (sq _)
    have h2 : 3 ^ a * 3 ^ a ≤ 5 * (3 ^ a * 5 ^ b) := by
      calc 3 ^ a * 3 ^ a ≤ 3 ^ a * 5 ^ (b + 1) := Nat.mul_le_mul_left _ h35
        _ = 5 * (3 ^ a * 5 ^ b) := by ring
    rw [← hQnat]
    exact_mod_cast h1.trans h2
  set P := Real.sqrt (5 * Qr) with hP
  have hP1 : 1 ≤ P := Real.one_le_sqrt.mpr (by linarith)
  have hk1 : (1 : ℝ) ≤ 5 * k := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hQ'P : ((3 ^ (a - i) * 5 ^ (b - j) : ℕ) : ℝ) ≤ P ^ 2 := by
    rw [hP, Real.sq_sqrt (by linarith), ← hQnat, hgQ']
    have hg1 : (1 : ℝ) ≤ g := by exact_mod_cast hg0
    have h0 : (0 : ℝ) ≤ ((3 ^ (a - i) * 5 ^ (b - j) : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hLP : ((L / 2 : ℕ) : ℝ) ≤ P := Real.le_sqrt_of_sq_le hL2
  have hLQ : ((L / 2 : ℕ) : ℝ) ^ 2 ≤ 5 * k * ((3 ^ (a - i) * 5 ^ (b - j) : ℕ) : ℝ) := by
    refine hL2.trans ?_
    rw [← hQnat, hgQ']
    have hgk' : (g : ℝ) ≤ k := by exact_mod_cast hgk
    have h0 : (0 : ℝ) ≤ ((3 ^ (a - i) * 5 ^ (b - j) : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hodd : Nat.Coprime 4 (3 ^ (a - i) * 5 ^ (b - j)) :=
    Nat.Coprime.mul_right (Nat.Coprime.pow_right _ (by norm_num))
      (Nat.Coprime.pow_right _ (by norm_num))
  have hR' : Nat.Coprime R (3 ^ (a - i) * 5 ^ (b - j)) :=
    Nat.Coprime.coprime_dvd_right (Dvd.intro_left g hQ'.symm) hR
  have hu1 : IsCoprime (((k' * R : ℕ) : ℤ)) (((3 ^ (a - i) * 5 ^ (b - j) : ℕ) : ℤ)) :=
    Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.mul_left hcop hR')
  have hu2 : IsCoprime (((4 * (k' * R) : ℕ) : ℤ)) (((3 ^ (a - i) * 5 ^ (b - j) : ℕ) : ℤ)) :=
    Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.mul_left hodd (Nat.Coprime.mul_left hcop hR'))
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = 2 ^ 12 * 18 ^ 3 * (3 ^ 9 * 5 ^ 9 * (5 * k) ^ 2) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; positivity
  have K1 := norm_sum_sixteen_pow_twelve_le hu1 hP1 hk1 hQ'P hLP hLQ
  have K2 := norm_sum_sixteen_pow_twelve_le hu2 hP1 hk1 hQ'P hLP hLQ
  rw [← hM] at K1 K2
  have B1 := le_of_pow_twelve_le (norm_nonneg _) hM0 (by linarith) K1
  have B2 := le_of_pow_twelve_le (norm_nonneg _) hM0 (by linarith) K2
  -- even and odd exponents
  have hsplit : ∑ m ∈ range L, ephase (3 ^ (a - i) * 5 ^ (b - j)) ((k' : ℤ) * R * 4 ^ m) =
      (∑ l ∈ range (L / 2), ephase (3 ^ (a - i) * 5 ^ (b - j)) (((k' * R : ℕ) : ℤ) * 16 ^ l) +
        ∑ l ∈ range (L / 2),
          ephase (3 ^ (a - i) * 5 ^ (b - j)) (((4 * (k' * R) : ℕ) : ℤ) * 16 ^ l)) +
      ∑ m ∈ range (L % 2),
        ephase (3 ^ (a - i) * 5 ^ (b - j)) ((k' : ℤ) * R * 4 ^ (2 * (L / 2) + m)) := by
    conv_lhs => rw [← Nat.div_add_mod L 2, sum_range_add, sum_range_mul_eq_sum_sum]
    congr 1
    rw [sum_range_succ, sum_range_succ, sum_range_zero, zero_add]
    congr 1 <;> refine sum_congr rfl fun l _ => ?_ <;> congr 1 <;> push_cast <;>
      rw [show (16 : ℤ) = 4 ^ 2 by norm_num, ← pow_mul] <;> ring
  rw [hsplit]
  have hrest : ‖∑ m ∈ range (L % 2),
      ephase (3 ^ (a - i) * 5 ^ (b - j)) ((k' : ℤ) * R * 4 ^ (2 * (L / 2) + m))‖ ≤ 1 := by
    refine (norm_sum_le _ _).trans ?_
    simp only [norm_ephase, sum_const, card_range, nsmul_eq_mul, mul_one]
    exact_mod_cast Nat.lt_succ_iff.mp (Nat.mod_lt L (by norm_num))
  have hQpow : 1 ≤ Qr ^ ((11 : ℝ) / 24) := Real.one_le_rpow hQr1 (by norm_num)
  calc _ ≤ (‖∑ l ∈ range (L / 2),
          ephase (3 ^ (a - i) * 5 ^ (b - j)) (((k' * R : ℕ) : ℤ) * 16 ^ l)‖ +
        ‖∑ l ∈ range (L / 2),
          ephase (3 ^ (a - i) * 5 ^ (b - j)) (((4 * (k' * R) : ℕ) : ℤ) * 16 ^ l)‖) + 1 :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) hrest)
    _ ≤ (M ^ ((1 : ℝ) / 12) * 5 ^ ((11 : ℝ) / 24) * Qr ^ ((11 : ℝ) / 24) +
        M ^ ((1 : ℝ) / 12) * 5 ^ ((11 : ℝ) / 24) * Qr ^ ((11 : ℝ) / 24)) + 1 := by
        gcongr
    _ ≤ pairConst k * Qr ^ ((11 : ℝ) / 24) := by
        rw [pairConst, ← hM]
        nlinarith

/-! ### Summation over the windows -/

theorem filter_window_eq (N a b : ℕ) :
    ({n ∈ Ico 3 N | (logThree n, logFive n) = (a, b)} : Finset ℕ) =
      Ico (max 3 (max ((3 ^ a + 1) / 2) ((5 ^ b + 1) / 2)))
        (min N (min ((3 ^ (a + 1) + 1) / 2) ((5 ^ (b + 1) + 1) / 2))) := by
  ext n
  simp only [mem_filter, mem_Ico, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨h3, hN⟩, ha, hb⟩
    obtain ⟨ha1, ha2⟩ := logThree_spec (n := n) (by omega)
    obtain ⟨hb1, hb2⟩ := logFive_spec (n := n) (by omega)
    rw [ha] at ha1 ha2
    rw [hb] at hb1 hb2
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨⟨by omega, by omega⟩, ?_, ?_⟩
    · unfold logThree
      rw [Nat.log_eq_iff (Or.inr ⟨by norm_num, by omega⟩)]
      omega
    · unfold logFive
      rw [Nat.log_eq_iff (Or.inr ⟨by norm_num, by omega⟩)]
      omega

/-- **One window.**  The sum of the rational approximations over the window `(a, b)` is bounded
by `C_k (3ᵃ5ᵇ)^{11/24}`. -/
theorem norm_sum_window_le {k : ℕ} (hk : 0 < k) (N a b : ℕ) :
    ‖∑ n ∈ Ico 3 N with (logThree n, logFive n) = (a, b), pairPhase k n‖ ≤
      pairConst k * ((3 : ℝ) ^ a * 5 ^ b) ^ ((11 : ℝ) / 24) := by
  rw [filter_window_eq]
  obtain ⟨s, hs⟩ : ∃ s, s = max 3 (max ((3 ^ a + 1) / 2) ((5 ^ b + 1) / 2)) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, e = min N (min ((3 ^ (a + 1) + 1) / 2) ((5 ^ (b + 1) + 1) / 2)) :=
    ⟨_, rfl⟩
  rw [← hs, ← he]
  have hC : 0 ≤ pairConst k * ((3 : ℝ) ^ a * 5 ^ b) ^ ((11 : ℝ) / 24) := by
    unfold pairConst; positivity
  rcases le_or_gt e s with hes | hes
  · rw [Ico_eq_empty_of_le hes, sum_empty, norm_zero]; exact hC
  have h3a : 3 ^ (a + 1) = 3 * 3 ^ a := by ring
  have h5b : 5 ^ (b + 1) = 5 * 5 ^ b := by ring
  have hs1 : (3 ^ a + 1) / 2 ≤ s := hs ▸ (le_max_left _ _).trans (le_max_right _ _)
  have hs2 : (5 ^ b + 1) / 2 ≤ s := hs ▸ (le_max_right _ _).trans (le_max_right _ _)
  have hs3 : 3 ≤ s := hs ▸ le_max_left _ _
  have he1 : e ≤ N := he ▸ min_le_left _ _
  have he2 : e ≤ (3 ^ (a + 1) + 1) / 2 := he ▸ (min_le_right _ _).trans (min_le_left _ _)
  have he3 : e ≤ (5 ^ (b + 1) + 1) / 2 := he ▸ (min_le_right _ _).trans (min_le_right _ _)
  have ha1 : 3 ^ a ≤ 2 * s := by omega
  have hb1 : 5 ^ b ≤ 2 * s := by omega
  have ha0 : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h; norm_num at he2; omega
    · exact h
  have hb0 : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · subst h; norm_num at he3; omega
    · exact h
  have hwin : ∀ n ∈ Ico s e, pairPhase k n =
      ephase (3 ^ a * 5 ^ b) ((k : ℤ) * pairNum a b n) := by
    intro n hn
    rw [mem_Ico] at hn
    have hla : logThree n = a := by
      unfold logThree
      rw [Nat.log_eq_iff (Or.inr ⟨by norm_num, by omega⟩)]
      omega
    have hlb : logFive n = b := by
      unfold logFive
      rw [Nat.log_eq_iff (Or.inr ⟨by norm_num, by omega⟩)]
      omega
    rw [pairPhase, pairModulus, hla, hlb]
  rw [sum_congr rfl hwin, sum_Ico_eq_sum_range]
  have hshift : ∀ i ∈ range (e - s), ephase (3 ^ a * 5 ^ b) ((k : ℤ) * pairNum a b (s + i)) =
      ephase (3 ^ a * 5 ^ b) ((k : ℤ) * (pairNum a b s : ℕ) * 4 ^ i) := by
    intro i _
    rw [pairNum_add ha1 hb1]
    push_cast
    ring_nf
  rw [sum_congr rfl hshift]
  exact norm_sum_four_orbit_le hk (coprime_pairNum ha0 hb0) (by omega) (by omega)

/-- `Σ_{a ≤ A} ρᵃ ≤ ρ^{A+1}/(ρ − 1)` for `ρ > 1`. -/
theorem sum_range_pow_le {ρ : ℝ} (hρ : 1 < ρ) (A : ℕ) :
    ∑ a ∈ range (A + 1), ρ ^ a ≤ ρ ^ (A + 1) / (ρ - 1) := by
  rw [geom_sum_eq hρ.ne', div_le_div_iff_of_pos_right (by linarith)]
  linarith

theorem rpow_three_five (a b : ℕ) (r : ℝ) :
    ((3 : ℝ) ^ a * 5 ^ b) ^ r = ((3 : ℝ) ^ r) ^ a * ((5 : ℝ) ^ r) ^ b := by
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast_mul (by norm_num),
    ← Real.rpow_natCast_mul (by norm_num), ← Real.rpow_mul_natCast (by norm_num),
    ← Real.rpow_mul_natCast (by norm_num), mul_comm (a : ℝ), mul_comm (b : ℝ)]

/-- The constant of the global bound. -/
noncomputable def pairGlobalConst (k : ℕ) : ℝ :=
  pairConst k * ((3 : ℝ) ^ ((11 : ℝ) / 24) / ((3 : ℝ) ^ ((11 : ℝ) / 24) - 1)) *
    ((5 : ℝ) ^ ((11 : ℝ) / 24) / ((5 : ℝ) ^ ((11 : ℝ) / 24) - 1))

/-- **All windows.**  `‖Σ_{3 ≤ n < N} e(k R(n)/Q(n))‖ ≤ C'_k (2N)^{11/12}`. -/
theorem norm_sum_pairPhase_le {k : ℕ} (hk : 0 < k) (N : ℕ) :
    ‖∑ n ∈ Ico 3 N, pairPhase k n‖ ≤ pairGlobalConst k * ((2 * N : ℕ) : ℝ) ^ ((11 : ℝ) / 12) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  set A := Nat.log 3 (2 * N)
  set B := Nat.log 5 (2 * N)
  have hmaps : ∀ n ∈ Ico 3 N, (logThree n, logFive n) ∈ range (A + 1) ×ˢ range (B + 1) := by
    intro n hn
    rw [mem_Ico] at hn
    simp only [mem_product, mem_range]
    exact ⟨Nat.lt_succ_of_le (Nat.log_mono_right (by omega)),
      Nat.lt_succ_of_le (Nat.log_mono_right (by omega))⟩
  rw [← sum_fiberwise_of_maps_to hmaps]
  set r : ℝ := (11 : ℝ) / 24
  have hr : 0 < r := by norm_num
  have ρ3 : 1 < (3 : ℝ) ^ r := Real.one_lt_rpow (by norm_num) hr
  have ρ5 : 1 < (5 : ℝ) ^ r := Real.one_lt_rpow (by norm_num) hr
  have hpk : 0 ≤ pairConst k := by unfold pairConst; positivity
  have h3A : (3 : ℝ) ^ A ≤ 2 * N := by exact_mod_cast Nat.pow_log_le_self 3 (by omega)
  have h5B : (5 : ℝ) ^ B ≤ 2 * N := by exact_mod_cast Nat.pow_log_le_self 5 (by omega)
  calc ‖∑ p ∈ range (A + 1) ×ˢ range (B + 1),
        ∑ n ∈ Ico 3 N with (logThree n, logFive n) = p, pairPhase k n‖
      ≤ ∑ p ∈ range (A + 1) ×ˢ range (B + 1),
          pairConst k * ((3 : ℝ) ^ p.1 * 5 ^ p.2) ^ r :=
        (norm_sum_le _ _).trans (sum_le_sum fun p _ => norm_sum_window_le hk N p.1 p.2)
    _ = pairConst k * ((∑ a ∈ range (A + 1), ((3 : ℝ) ^ r) ^ a) *
          ∑ b ∈ range (B + 1), ((5 : ℝ) ^ r) ^ b) := by
        rw [← mul_sum, sum_product, sum_mul_sum]
        congr 1
        refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
        exact rpow_three_five a b r
    _ ≤ pairConst k * (((3 : ℝ) ^ r) ^ (A + 1) / ((3 : ℝ) ^ r - 1) *
          (((5 : ℝ) ^ r) ^ (B + 1) / ((5 : ℝ) ^ r - 1))) := by
        gcongr
        · exact sum_range_pow_le ρ3 A
        · exact sum_range_pow_le ρ5 B
    _ = pairGlobalConst k * (((3 : ℝ) ^ A * 5 ^ B) ^ r) := by
        rw [pairGlobalConst, rpow_three_five]
        field_simp
        ring
    _ ≤ pairGlobalConst k * (((2 * N : ℕ) : ℝ) * (2 * N : ℕ)) ^ r := by
        have : 0 ≤ pairGlobalConst k := by
          unfold pairGlobalConst
          have h1 : 0 < (3 : ℝ) ^ r - 1 := by linarith
          have h2 : 0 < (5 : ℝ) ^ r - 1 := by linarith
          positivity
        gcongr
        · push_cast; exact h3A
        · push_cast; exact h5B
    _ = pairGlobalConst k * ((2 * N : ℕ) : ℝ) ^ ((11 : ℝ) / 12) := by
        rw [← sq, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num

/-! ### Weyl sums, equidistribution and the parity drift -/

theorem tendsto_inv_mul_rpow_zero (C : ℝ) :
    Tendsto (fun N : ℕ => (N : ℝ)⁻¹ * (3 + C * ((2 * N : ℕ) : ℝ) ^ ((11 : ℝ) / 12))) atTop
      (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => (N : ℝ) ^ (-((1 : ℝ) / 12))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have h := (h2.const_mul 3).add (h1.const_mul (C * 2 ^ ((11 : ℝ) / 12)))
  rw [mul_zero, mul_zero, add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have e : ((2 * N : ℕ) : ℝ) ^ ((11 : ℝ) / 12) =
      2 ^ ((11 : ℝ) / 12) * (N : ℝ) ^ ((11 : ℝ) / 12) := by
    push_cast; exact Real.mul_rpow (by norm_num) hN'.le
  have e' : (N : ℝ) ^ (-((1 : ℝ) / 12)) = (N : ℝ) ^ ((11 : ℝ) / 12) / N := by
    rw [show -((1 : ℝ) / 12) = (11 : ℝ) / 12 - 1 by norm_num, Real.rpow_sub_one hN'.ne']
  rw [e, e']
  field_simp

theorem tendsto_pairPhase_average {k : ℕ} (hk : 0 < k) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ range N, pairPhase k n) atTop (𝓝 0) := by
  refine squeeze_zero_norm' ?_ (tendsto_inv_mul_rpow_zero (pairGlobalConst k))
  filter_upwards [eventually_ge_atTop 3] with N hN
  rw [← sum_range_add_sum_Ico _ hN, norm_mul, norm_inv, Complex.norm_natCast]
  gcongr
  refine (norm_add_le _ _).trans (add_le_add ?_ (norm_sum_pairPhase_le hk N))
  refine (norm_sum_le _ _).trans ?_
  simp [pairPhase, norm_ephase]

theorem tendsto_weylSum_pairOrbit_nat {k : ℕ} (hk : 0 < k) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ *
      ∑ n ∈ range N, Complex.exp (2 * Real.pi * Complex.I * k * pairOrbit n)) atTop (𝓝 0) := by
  have herr : Tendsto (fun n : ℕ =>
      ‖Complex.exp (2 * Real.pi * Complex.I * k * pairOrbit n) - pairPhase k n‖) atTop (𝓝 0) := by
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
      ((tendsto_const_div_atTop_nhds_zero_nat (2 * Real.pi * k)))
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact norm_exp_sub_pairPhase_le k hn
  have hces := herr.cesaro
  have hE : Tendsto (fun N : ℕ => (N : ℂ)⁻¹ * ∑ n ∈ range N,
      (Complex.exp (2 * Real.pi * Complex.I * k * pairOrbit n) - pairPhase k n)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun N => ?_) hces
    rw [norm_mul, norm_inv, Complex.norm_natCast]
    gcongr
    exact norm_sum_le _ _
  have h := (tendsto_pairPhase_average hk).add hE
  rw [add_zero] at h
  refine h.congr fun N => ?_
  rw [← mul_add, ← sum_add_distrib]
  congr 1
  exact sum_congr rfl fun n _ => by ring

/-- **The Weyl sums of `4ⁿ(α₃ + α₅)` vanish on average** for every frequency `k ≠ 0`. -/
theorem tendsto_weylSum_pairOrbit (k : ℤ) (hk : k ≠ 0) :
    Tendsto (fun N : ℕ => (N : ℂ)⁻¹ *
      ∑ n ∈ range N, Complex.exp (2 * Real.pi * Complex.I * k * pairOrbit n)) atTop (𝓝 0) := by
  rcases lt_or_gt_of_ne hk with hneg | hpos
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, k = -(m : ℤ) := ⟨k.natAbs, by omega⟩
    have hm0 : 0 < m := by omega
    have h := (Complex.continuous_conj.tendsto 0).comp (tendsto_weylSum_pairOrbit_nat hm0)
    rw [map_zero] at h
    refine h.congr fun N => ?_
    simp only [Function.comp_apply, map_mul, map_inv₀, Complex.conj_natCast, map_sum]
    congr 1
    refine sum_congr rfl fun n _ => ?_
    rw [← Complex.exp_conj, hm]
    congr 1
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Complex.conj_natCast]
    push_cast
    ring
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = (m : ℤ) := ⟨k.natAbs, by omega⟩
    have hm0 : 0 < m := by omega
    simpa using tendsto_weylSum_pairOrbit_nat hm0

/-- **Equidistribution.**  For `0 < a ≤ b < 1`, the proportion of `n < N` with
`{4ⁿ(α₃ + α₅)} ∈ [a, b)` tends to `b − a`. -/
theorem tendsto_card_fract_pairOrbit {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    Tendsto (fun N : ℕ => (#{n ∈ range N | Int.fract (pairOrbit n) ∈ Set.Ico a b} : ℝ) / N)
      atTop (𝓝 (b - a)) :=
  tendsto_card_fract_mem_Ico pairOrbit tendsto_weylSum_pairOrbit ha hab hb

theorem digitWeight_floor_four_mul (f : ℝ) :
    (digitWeight ⌊4 * f⌋ : ℝ) = (if f ∈ Set.Ico (1 / 2 : ℝ) (3 / 4) then 1 else 0) -
      (if f ∈ Set.Ico (1 / 4 : ℝ) (1 / 2) then 1 else 0) := by
  have e2 : ⌊4 * f⌋ = 2 ↔ f ∈ Set.Ico (1 / 2 : ℝ) (3 / 4) := by
    rw [Int.floor_eq_iff, Set.mem_Ico]
    push_cast
    constructor <;> rintro ⟨h, h'⟩ <;> constructor <;> linarith
  have e1 : ⌊4 * f⌋ = 1 ↔ f ∈ Set.Ico (1 / 4 : ℝ) (1 / 2) := by
    rw [Int.floor_eq_iff, Set.mem_Ico]
    push_cast
    constructor <;> rintro ⟨h, h'⟩ <;> constructor <;> linarith
  simp only [digitWeight, Int.cast_sub, Int.cast_ite, Int.cast_one, Int.cast_zero, e2, e1]

theorem drift_pairStoneham_eq (N : ℕ) :
    (drift pairStoneham N : ℝ) =
      (#{n ∈ range N | Int.fract (pairOrbit n) ∈ Set.Ico (1 / 2 : ℝ) (3 / 4)} : ℝ) -
        #{n ∈ range N | Int.fract (pairOrbit n) ∈ Set.Ico (1 / 4 : ℝ) (1 / 2)} := by
  have hpt : ∀ n ∈ range N, ((digitWeight (quatDigit pairStoneham (n + 1)) : ℤ) : ℝ) =
      (if Int.fract (pairOrbit n) ∈ Set.Ico (1 / 2 : ℝ) (3 / 4) then 1 else 0) -
        (if Int.fract (pairOrbit n) ∈ Set.Ico (1 / 4 : ℝ) (1 / 2) then 1 else 0) := by
    intro n _
    rw [quatDigit_succ_eq_floor_fract]
    exact digitWeight_floor_four_mul _
  rw [drift_eq_sum_digitWeight, Int.cast_sum, sum_congr rfl hpt, sum_sub_distrib, card_filter,
    card_filter]
  push_cast
  rfl

/-- **The parity drift of `α₃ + α₅` is `o(N)`.** -/
theorem tendsto_drift_pairStoneham :
    Tendsto (fun N : ℕ => (drift pairStoneham N : ℝ) / N) atTop (𝓝 0) := by
  have h2 := tendsto_card_fract_pairOrbit (a := 1 / 2) (b := 3 / 4) (by norm_num) (by norm_num)
    (by norm_num)
  have h1 := tendsto_card_fract_pairOrbit (a := 1 / 4) (b := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num)
  have h := h2.sub h1
  rw [show (3 / 4 : ℝ) - 1 / 2 - (1 / 2 - 1 / 4) = 0 by norm_num] at h
  refine h.congr fun N => ?_
  rw [drift_pairStoneham_eq, sub_div]

/-- **The parity-drift hypothesis fails for `α₃ + α₅`.** -/
theorem not_parityDriftHypothesis_pairStoneham : ¬ ParityDriftHypothesis pairStoneham :=
  fun h => h tendsto_drift_pairStoneham

end GaloisForLFunctions.HTGeometry.StonehamPairDrift
