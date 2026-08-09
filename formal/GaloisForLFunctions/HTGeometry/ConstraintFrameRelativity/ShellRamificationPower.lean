import GaloisForLFunctions.RHTower.HighExponentShellZeroFree

/-!
# The ramification power morphism on high-exponent shells

The `r`-th power map `P_r(k) = k ^ r` is a multiplicative monoid endomorphism of `ℕ` which
carries the high-exponent shell of level `m` onto the perfect-`r`-th-power part of the shell of
level `r * m`.  The exact pullback law is

`shellIndicator (r * m) (k ^ r) = shellIndicator m k`,

a consequence of `max_p v_p (k ^ r) = r * max_p v_p k`.  Its two immediate corollaries are the
squarefree descent `shellIndicator 1 k = shellIndicator m (k ^ m)` (`shellIndicator 1` being the
squarefree indicator away from `1`) and the strictness of the inclusion of the power image in the
higher shell, witnessed by `2 ^ (r * m) * 3`.
-/

namespace HTGeometry.ConstraintFrameRelativity

open RHTower

/-! ## `MFree` through prime exponents -/

/-- `MFree j n` says every prime exponent of `n` is smaller than `j`. -/
theorem mFree_iff_forall_factorization_lt {j n : ℕ} (hn : n ≠ 0) :
    MFree j n ↔ ∀ p : ℕ, p.Prime → n.factorization p < j := by
  constructor
  · intro h p hp
    have hnd := h p hp
    rw [hp.pow_dvd_iff_le_factorization hn] at hnd
    omega
  · intro h p hp hdvd
    rw [hp.pow_dvd_iff_le_factorization hn] at hdvd
    have := h p hp
    omega

/-- The exponent of a prime in a perfect power. -/
theorem factorization_pow_apply (k r p : ℕ) :
    (k ^ r).factorization p = r * k.factorization p := by
  rw [Nat.factorization_pow]
  simp

/-! ## The exact power pullback -/

theorem mFree_pow_succ_iff {r j k : ℕ} (hr : r ≠ 0) (hk : k ≠ 0) :
    MFree (r * j + 1) (k ^ r) ↔ MFree (j + 1) k := by
  have hr' : 0 < r := Nat.pos_of_ne_zero hr
  have hkr : k ^ r ≠ 0 := pow_ne_zero _ hk
  rw [mFree_iff_forall_factorization_lt hkr, mFree_iff_forall_factorization_lt hk]
  constructor
  · intro h p hp
    have hlt := h p hp
    rw [factorization_pow_apply] at hlt
    have hle : r * k.factorization p ≤ r * j := by omega
    have := Nat.le_of_mul_le_mul_left hle hr'
    omega
  · intro h p hp
    have hle : k.factorization p ≤ j := by have := h p hp; omega
    rw [factorization_pow_apply]
    have : r * k.factorization p ≤ r * j := Nat.mul_le_mul_left _ hle
    omega

theorem mFree_pow_iff {r j k : ℕ} (hr : r ≠ 0) (hk : k ≠ 0) :
    MFree (r * j) (k ^ r) ↔ MFree j k := by
  have hr' : 0 < r := Nat.pos_of_ne_zero hr
  have hkr : k ^ r ≠ 0 := pow_ne_zero _ hk
  rw [mFree_iff_forall_factorization_lt hkr, mFree_iff_forall_factorization_lt hk]
  constructor
  · intro h p hp
    have hlt := h p hp
    rw [factorization_pow_apply] at hlt
    exact (Nat.mul_lt_mul_left hr').mp hlt
  · intro h p hp
    rw [factorization_pow_apply]
    exact (Nat.mul_lt_mul_left hr').mpr (h p hp)

/-- **Exact ramification-law pullback.**  The `r`-th power map carries the level-`m` shell
indicator to the level-`r * m` shell indicator. -/
theorem shellIndicator_pow {m r : ℕ} (hr : r ≠ 0) (k : ℕ) :
    shellIndicator (r * m) (k ^ r) = shellIndicator m k := by
  rcases eq_or_ne k 0 with rfl | hk
  · rw [zero_pow hr]
    simp
  have h1 : MFree (r * m + 1) (k ^ r) ↔ MFree (m + 1) k := mFree_pow_succ_iff hr hk
  have h2 : MFree (r * m) (k ^ r) ↔ MFree m k := mFree_pow_iff hr hk
  simp only [shellIndicator_apply, mFreeIndicator_apply]
  by_cases hA : MFree (m + 1) k <;> by_cases hB : MFree m k <;>
    simp [h1, h2, hA, hB]

/-- The power map is a monoid endomorphism of `ℕ` and the pullback law is stated for it. -/
theorem shellIndicator_powMonoidHom {m r : ℕ} (hr : r ≠ 0) (k : ℕ) :
    shellIndicator (r * m) (powMonoidHom r k) = shellIndicator m k :=
  shellIndicator_pow hr k

/-! ## Squarefree descent -/

/-- Away from `1`, `shellIndicator 1` is the squarefree indicator. -/
theorem shellIndicator_one_eq_one_iff {k : ℕ} (hk : k ≠ 0) :
    shellIndicator 1 k = 1 ↔ Squarefree k ∧ k ≠ 1 := by
  rw [shellIndicator_eq_one_iff, mFree_two_iff_squarefree]
  constructor
  · rintro ⟨hsq, hnot⟩
    refine ⟨hsq, ?_⟩
    rintro rfl
    exact hnot (mFree_one one_ne_zero)
  · rintro ⟨hsq, hne⟩
    refine ⟨hsq, ?_⟩
    intro hfree
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    exact hfree p hp (by simpa using hpd)

/-- **Squarefree pullback.**  Pulling the level-`m` shell back along `k ↦ k ^ m` returns exactly
the squarefree indicator (away from `1`). -/
theorem shellIndicator_pow_self_eq_one_iff {m k : ℕ} (hm : m ≠ 0) (hk : k ≠ 0) :
    shellIndicator m (k ^ m) = 1 ↔ Squarefree k ∧ k ≠ 1 := by
  have h : shellIndicator (m * 1) (k ^ m) = shellIndicator 1 k :=
    shellIndicator_pow (m := 1) (r := m) hm k
  rw [mul_one] at h
  rw [h]
  exact shellIndicator_one_eq_one_iff hk

/-! ## Perfect powers and the strict excess witness -/

/-- `N` is an `r`-th power. -/
def IsRPow (r N : ℕ) : Prop := ∃ k, k ^ r = N

theorem isRPow_pow (r k : ℕ) : IsRPow r (k ^ r) := ⟨k, rfl⟩

theorem isRPow_one (r : ℕ) : IsRPow r 1 := ⟨1, one_pow r⟩

/-- A number with a prime exponent not divisible by `r` is not an `r`-th power. -/
theorem not_isRPow_of_factorization_not_dvd {r N p : ℕ}
    (h : ¬ r ∣ N.factorization p) : ¬ IsRPow r N := by
  rintro ⟨k, rfl⟩
  exact h ⟨k.factorization p, factorization_pow_apply k r p⟩

/-- The exponent vector of the witness `2 ^ e * 3`. -/
theorem factorization_two_pow_mul_three (e : ℕ) :
    (2 ^ e * 3).factorization = Finsupp.single 2 e + Finsupp.single 3 1 := by
  rw [Nat.factorization_mul (by positivity) (by norm_num), Nat.factorization_pow,
    Nat.Prime.factorization (by norm_num), Nat.Prime.factorization (by norm_num)]
  ext p
  simp [Finsupp.single_apply]

theorem factorization_two_pow_mul_three_apply (e p : ℕ) :
    (2 ^ e * 3).factorization p =
      (if p = 2 then e else 0) + (if p = 3 then 1 else 0) := by
  rw [factorization_two_pow_mul_three]
  simp [Finsupp.single_apply, eq_comm]

/-- The witness lies in the level-`e` shell for every `e ≥ 1`. -/
theorem shellIndicator_two_pow_mul_three {e : ℕ} (he : e ≠ 0) :
    shellIndicator e (2 ^ e * 3) = 1 := by
  have hne : (2 ^ e * 3 : ℕ) ≠ 0 := by positivity
  rw [shellIndicator_eq_one_iff]
  constructor
  · rw [mFree_iff_forall_factorization_lt hne]
    intro p _
    rw [factorization_two_pow_mul_three_apply]
    split_ifs <;> omega
  · intro hfree
    exact hfree 2 Nat.prime_two ⟨3, by ring⟩

/-- **The power image is strictly smaller than the higher shell.**  For `r ≥ 2` the integer
`2 ^ (r * m) * 3` lies in the level-`r * m` shell but is not an `r`-th power. -/
theorem excess_witness {m r : ℕ} (hm : m ≠ 0) (hr : 2 ≤ r) :
    shellIndicator (r * m) (2 ^ (r * m) * 3) = 1 ∧ ¬ IsRPow r (2 ^ (r * m) * 3) := by
  have hrm : r * m ≠ 0 := Nat.mul_ne_zero (by omega) hm
  refine ⟨shellIndicator_two_pow_mul_three hrm, ?_⟩
  refine not_isRPow_of_factorization_not_dvd (p := 3) ?_
  rw [factorization_two_pow_mul_three_apply]
  have h1 : (if (3 : ℕ) = 2 then r * m else 0) + (if (3 : ℕ) = 3 then 1 else 0) = 1 := by
    norm_num
  rw [h1, Nat.dvd_one]
  omega

end HTGeometry.ConstraintFrameRelativity
