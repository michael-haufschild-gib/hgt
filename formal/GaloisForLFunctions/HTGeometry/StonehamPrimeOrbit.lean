import GaloisForLFunctions.HTGeometry.StonehamPrimeWindows

/-!
# The orbit of `2` modulo `pᵏ` and its two square classes

Let `p` be an odd prime such that `2` has order `p − 1` modulo `p` and `p² ∤ 2^{p−1} − 1`.  Then
`pᵏ ∣ 2ᵈ − 1 ⟺ (p − 1)p^{k−1} ∣ d` (lifting the exponent), so `j ↦ a2ʲ mod pᵏ` runs once through
the units modulo `pᵏ` (`sum_range_two_orbit_eq`).  Splitting the orbit into even and odd `j` gives,
for any weight `G` and `χ = (·/p)` with `χ(2) = −1`,

`2 Σ_{i<φ(pᵏ)/2} G(a4ⁱ mod pᵏ) = Σ_{units r} G(r) + χ(a) Σ_{units r} χ(r) G(r)`
(`two_mul_sum_four_orbit`).
-/

open Finset

namespace GaloisForLFunctions.HTGeometry.StonehamPrimeDrift

variable {p : ℕ} [hp : Fact p.Prime]

theorem dvd_two_pow_prime_sub_one_sub_one (hp2 : p ≠ 2) : p ∣ 2 ^ (p - 1) - 1 := by
  have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp.out).mpr (Ne.symm hp2)
  have := Nat.ModEq.pow_totient hcop
  rw [Nat.totient_prime hp.out] at this
  exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp this.symm

theorem not_dvd_two_pow (hp2 : p ≠ 2) (d : ℕ) : ¬ p ∣ 2 ^ d := fun h => by
  have := (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp (hp.out.dvd_of_dvd_pow h)
  exact hp2 this

/-- With `2` of order `p − 1` modulo `p`: `p ∣ 2ᵈ − 1 ⟺ (p − 1) ∣ d`. -/
theorem dvd_two_pow_sub_one_iff (hp2 : p ≠ 2)
    (hord : ∀ d < p - 1, 0 < d → ¬ p ∣ 2 ^ d - 1) {d : ℕ} :
    p ∣ 2 ^ d - 1 ↔ (p - 1) ∣ d := by
  have hF := dvd_two_pow_prime_sub_one_sub_one hp2
  constructor
  · intro h
    have h1 : 2 ^ d ≡ 1 [MOD p] :=
      ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mpr h).symm
    have hF' : 2 ^ (p - 1) ≡ 1 [MOD p] :=
      ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mpr hF).symm
    have hsplit : 2 ^ d = (2 ^ (p - 1)) ^ (d / (p - 1)) * 2 ^ (d % (p - 1)) := by
      rw [← pow_mul, ← pow_add, Nat.div_add_mod]
    have h2 : 2 ^ (d % (p - 1)) ≡ 1 [MOD p] := by
      have := (hF'.pow (d / (p - 1))).mul_right (2 ^ (d % (p - 1)))
      rw [one_pow, one_mul, ← hsplit] at this
      exact this.symm.trans h1
    by_contra hdvd
    have hr : 0 < d % (p - 1) := Nat.pos_of_ne_zero fun h0 => hdvd (Nat.dvd_of_mod_eq_zero h0)
    have hp1 : 0 < p - 1 := by have := hp.out.two_le; omega
    exact hord _ (Nat.mod_lt _ hp1) hr
      ((Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp h2.symm)
  · rintro ⟨e, rfl⟩
    rw [pow_mul]
    exact hF.trans (by simpa using Nat.sub_one_dvd_pow_sub_one (2 ^ (p - 1)) e)

theorem padicValNat_two_pow_sub_one (hp2 : p ≠ 2) (hwief : ¬ p ^ 2 ∣ 2 ^ (p - 1) - 1) {e : ℕ}
    (he : e ≠ 0) : padicValNat p (2 ^ ((p - 1) * e) - 1) = 1 + padicValNat p e := by
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by have := hp.out.two_le; omega
  have hlt : 1 < 2 ^ (p - 1) := Nat.one_lt_pow (by omega) (by norm_num)
  have hF := dvd_two_pow_prime_sub_one_sub_one hp2
  have hv1 : padicValNat p (2 ^ (p - 1) - 1) = 1 := by
    have hne : 2 ^ (p - 1) - 1 ≠ 0 := by omega
    have h1 := (padicValNat_dvd_iff_le (p := p) (n := 1) hne).mp (by rwa [pow_one])
    have h2 : ¬ 2 ≤ padicValNat p (2 ^ (p - 1) - 1) := fun h =>
      hwief ((padicValNat_dvd_iff_le hne).mpr h)
    omega
  rw [pow_mul]
  have := padicValNat.pow_sub_pow (p := p) (x := 2 ^ (p - 1)) (y := 1) hodd hlt
    (by simpa using hF) (not_dvd_two_pow hp2 _) he
  rw [one_pow] at this
  rw [this, hv1]

/-- **Lifting the exponent.**  `pᵏ ∣ 2ᵈ − 1 ⟺ (p − 1)p^{k−1} ∣ d`. -/
theorem pow_dvd_two_pow_sub_one_iff (hp2 : p ≠ 2)
    (hord : ∀ d < p - 1, 0 < d → ¬ p ∣ 2 ^ d - 1) (hwief : ¬ p ^ 2 ∣ 2 ^ (p - 1) - 1)
    {k : ℕ} (hk : 1 ≤ k) {d : ℕ} : p ^ k ∣ 2 ^ d - 1 ↔ (p - 1) * p ^ (k - 1) ∣ d := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have hne : 2 ^ d - 1 ≠ 0 := by have := Nat.one_lt_pow hd.ne' (by norm_num : 1 < 2); omega
  constructor
  · intro h
    obtain ⟨e, rfl⟩ := (dvd_two_pow_sub_one_iff hp2 hord).mp
      ((dvd_pow_self p (by omega)).trans h)
    have he : e ≠ 0 := by rintro rfl; simp at hd
    have hv := (padicValNat_dvd_iff_le hne).mp h
    rw [padicValNat_two_pow_sub_one hp2 hwief he] at hv
    exact mul_dvd_mul_left _ ((pow_dvd_pow p (by omega)).trans pow_padicValNat_dvd)
  · rintro ⟨c, rfl⟩
    have hc : c ≠ 0 := by rintro rfl; simp at hd
    rw [mul_assoc] at hne ⊢
    rw [padicValNat_dvd_iff_le hne,
      padicValNat_two_pow_sub_one hp2 hwief (mul_ne_zero (pow_ne_zero _ hp.out.ne_zero) hc),
      padicValNat.mul (pow_ne_zero _ hp.out.ne_zero) hc, padicValNat.prime_pow]
    omega

/-- **The orbit of `2` runs once through the units modulo `pᵏ`.** -/
theorem sum_range_two_orbit_eq (hp2 : p ≠ 2)
    (hord : ∀ d < p - 1, 0 < d → ¬ p ∣ 2 ^ d - 1) (hwief : ¬ p ^ 2 ∣ 2 ^ (p - 1) - 1)
    {k : ℕ} (hk : 1 ≤ k) {a : ℕ} (ha : ¬ p ∣ a) {M : Type*} [AddCommMonoid M] (F : ℕ → M) :
    ∑ j ∈ range ((p - 1) * p ^ (k - 1)), F (a * 2 ^ j % p ^ k) =
      ∑ r ∈ range (p ^ k) with (p ^ k).Coprime r, F r := by
  have hq : 0 < p ^ k := pow_pos hp.out.pos k
  have hcop : ∀ j, Nat.Coprime (p ^ k) (a * 2 ^ j) := fun j =>
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr fun h =>
      (hp.out.dvd_mul.mp h).elim ha (not_dvd_two_pow hp2 j))
  have key : ∀ i j, i < j → j < (p - 1) * p ^ (k - 1) →
      a * 2 ^ i % p ^ k = a * 2 ^ j % p ^ k → False := by
    intro i j hlt hj hij
    have hmod : a * 2 ^ i ≡ a * 2 ^ j [MOD p ^ k] := hij
    have hle : a * 2 ^ i ≤ a * 2 ^ j :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hlt.le)
    have hdvd := (Nat.modEq_iff_dvd' hle).mp hmod
    have he : a * 2 ^ j - a * 2 ^ i = a * 2 ^ i * (2 ^ (j - i) - 1) := by
      rw [Nat.mul_sub_one, mul_assoc, ← pow_add, Nat.add_sub_cancel' hlt.le]
    rw [he] at hdvd
    have h2 := (hcop i).dvd_of_dvd_mul_left hdvd
    have h3 := (pow_dvd_two_pow_sub_one_iff hp2 hord hwief hk).mp h2
    exact absurd (Nat.le_of_dvd (by omega) h3) (by omega)
  have hinj : Set.InjOn (fun j => a * 2 ^ j % p ^ k) (range ((p - 1) * p ^ (k - 1))) := by
    intro i hi j hj hij
    simp only [coe_range, Set.mem_Iio] at hi hj hij
    rcases lt_trichotomy i j with h | h | h
    · exact (key i j h hj hij).elim
    · exact h
    · exact (key j i h hi hij.symm).elim
  have himg : (range ((p - 1) * p ^ (k - 1))).image (fun j => a * 2 ^ j % p ^ k) =
      {r ∈ range (p ^ k) | (p ^ k).Coprime r} := by
    apply eq_of_subset_of_card_le
    · intro r hr
      obtain ⟨j, _, rfl⟩ := mem_image.mp hr
      rw [mem_filter, mem_range]
      refine ⟨Nat.mod_lt _ hq, ?_⟩
      rw [Nat.coprime_comm, ZMod.coprime_mod_iff_coprime, Nat.coprime_comm]
      exact hcop j
    · rw [card_image_of_injOn hinj, card_range, ← Nat.totient_eq_card_coprime,
        Nat.totient_prime_pow hp.out (by omega), mul_comm]
  rw [← himg, sum_image hinj]

/-! ### The two square classes -/

theorem legendreSym_natCast_mod {k : ℕ} (hk : 1 ≤ k) (x : ℕ) :
    legendreSym p ((x % p ^ k : ℕ) : ℤ) = legendreSym p x := by
  rw [legendreSym.mod, legendreSym.mod p x, Int.natCast_mod,
    Int.emod_emod_of_dvd _ (by exact_mod_cast dvd_pow_self p (by omega : k ≠ 0))]

theorem legendreSym_mul_two_pow (a j : ℕ) :
    legendreSym p ((a * 2 ^ j : ℕ) : ℤ) = legendreSym p a * legendreSym p 2 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, ← mul_assoc, Nat.cast_mul, legendreSym.mul, ih, pow_succ]
    push_cast
    ring

theorem legendreSym_sq_eq_one {a : ℕ} (ha : ¬ p ∣ a) : legendreSym p a ^ 2 = 1 := by
  apply legendreSym.sq_one
  rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
  exact ha

theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (P : ℕ) :
    ∑ j ∈ range (2 * P), f j = ∑ i ∈ range P, (f (2 * i) + f (2 * i + 1)) := by
  induction P with
  | zero => simp
  | succ P ih =>
    rw [show 2 * (P + 1) = 2 * P + 1 + 1 by ring, sum_range_succ, sum_range_succ, ih,
      sum_range_succ, add_assoc]

/-- **Splitting the orbit of `2` into the two square classes.** -/
theorem two_mul_sum_four_orbit (hp2 : p ≠ 2)
    (hord : ∀ d < p - 1, 0 < d → ¬ p ∣ 2 ^ d - 1) (hwief : ¬ p ^ 2 ∣ 2 ^ (p - 1) - 1)
    (h2 : legendreSym p 2 = -1) {k : ℕ} (hk : 1 ≤ k) {a : ℕ} (ha : ¬ p ∣ a) (G : ℕ → ℤ) :
    2 * ∑ i ∈ range ((p - 1) / 2 * p ^ (k - 1)), G (a * 4 ^ i % p ^ k) =
      ∑ r ∈ range (p ^ k) with (p ^ k).Coprime r, G r +
        legendreSym p a * ∑ r ∈ range (p ^ k) with (p ^ k).Coprime r, legendreSym p r * G r := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.out.odd_of_ne_two hp2)
  have h2P : (p - 1) * p ^ (k - 1) = 2 * ((p - 1) / 2 * p ^ (k - 1)) := by
    rw [← mul_assoc]; congr 1; omega
  rw [← sum_range_two_orbit_eq hp2 hord hwief hk ha G,
    ← sum_range_two_orbit_eq hp2 hord hwief hk ha (fun r => legendreSym p r * G r), h2P,
    sum_range_two_mul, sum_range_two_mul]
  have hχ : ∀ j, legendreSym p ((a * 2 ^ j % p ^ k : ℕ) : ℤ) = legendreSym p a * (-1) ^ j := by
    intro j; rw [legendreSym_natCast_mod hk, legendreSym_mul_two_pow, h2]
  have e1 : ∀ i : ℕ, a * 2 ^ (2 * i) = a * 4 ^ i := fun i => by rw [pow_mul]; norm_num
  have hχ0 : ∀ i : ℕ, legendreSym p ((a * 4 ^ i % p ^ k : ℕ) : ℤ) = legendreSym p a := by
    intro i; rw [← e1, hχ, pow_mul]; norm_num
  have hχ1 : ∀ i : ℕ, legendreSym p ((a * 2 ^ (2 * i + 1) % p ^ k : ℕ) : ℤ) =
      -legendreSym p a := by
    intro i; rw [hχ, pow_succ, pow_mul]; norm_num
  simp only [e1, hχ0, hχ1]
  set X := ∑ i ∈ range ((p - 1) / 2 * p ^ (k - 1)), G (a * 4 ^ i % p ^ k)
  set Y := ∑ i ∈ range ((p - 1) / 2 * p ^ (k - 1)), G (a * 2 ^ (2 * i + 1) % p ^ k)
  have hA : ∑ i ∈ range ((p - 1) / 2 * p ^ (k - 1)),
      (G (a * 4 ^ i % p ^ k) + G (a * 2 ^ (2 * i + 1) % p ^ k)) = X + Y := sum_add_distrib
  have hB : ∑ i ∈ range ((p - 1) / 2 * p ^ (k - 1)),
      (legendreSym p a * G (a * 4 ^ i % p ^ k) +
        -legendreSym p a * G (a * 2 ^ (2 * i + 1) % p ^ k)) =
      legendreSym p a * X - legendreSym p a * Y := by
    rw [sum_add_distrib, ← mul_sum, ← mul_sum]; ring
  rw [hA, hB]
  have hsq := legendreSym_sq_eq_one (p := p) ha
  linear_combination (-(X - Y)) * hsq

end GaloisForLFunctions.HTGeometry.StonehamPrimeDrift
