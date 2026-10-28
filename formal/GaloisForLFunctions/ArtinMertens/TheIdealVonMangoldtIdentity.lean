import Mathlib

/-!
# The ideal von Mangoldt identity

Over the rational integers Mertens' theorem starts from `log n = Σ_{p^k ∣ n} log p`. This file
proves the same identity for the integral ideals of a number field `K` and the hyperbola identity it
gives for the ideals of norm at most `x`.

* **Ideals and prime powers of bounded norm** (`idealsLe`, `primePowersLe`): the non-zero ideals
  with `N𝔞 ≤ x`, and the pairs `(𝔭, k)`, `𝔭` a non-zero prime and `k ≥ 1`, with `N𝔭^k ≤ x`.
* **Logarithm of the norm** (`log_absNorm_eq_sum`): `log N𝔞 = Σ_{𝔭 ∣ 𝔞} v_𝔭(𝔞) log N𝔭`, from the
  factorization `𝔞 = Π 𝔭^{v_𝔭(𝔞)}` and the multiplicativity of the norm.
* **Multiplicities** (`pow_dvd_iff_le_count`): `𝔭^k ∣ 𝔞` iff `k ≤ v_𝔭(𝔞)`.
* **The von Mangoldt identity** (`sum_primePowersLe_dvd_eq`): `log N𝔞 = Σ_{𝔭^k ∣ 𝔞, k ≥ 1} log N𝔭`.
* **The hyperbola identity** (`sum_log_absNorm_idealsLe_eq`):
  `Σ_{N𝔞 ≤ x} log N𝔞 = Σ_{N𝔭^k ≤ x} log N𝔭 · #{𝔟 : N𝔟 ≤ ⌊x/N𝔭^k⌋}`, since `𝔞 ↦ 𝔭^k 𝔟` is a
  bijection between the ideals `𝔟` of norm `≤ x/N𝔭^k` and the multiples of `𝔭^k` of norm `≤ x`.

This is the first step of Mertens' theorem for the prime ideals of `K`: the left side is controlled
by the number of ideals of bounded norm, the right side is a Mertens sum weighted by that same
counting function.
-/

noncomputable section

open Finset UniqueFactorizationMonoid NumberField Ideal
open scoped Classical

namespace GaloisForLFunctions.ArtinMertens

variable (K : Type*) [Field K] [NumberField K]

/-- The **non-zero integral ideals of norm `≤ x`**. -/
def idealsLe (x : ℕ) : Finset (Ideal (𝓞 K)) :=
  (Ideal.finite_setOf_absNorm_le x).toFinset.filter (· ≠ ⊥)

variable {K}

theorem mem_idealsLe {x : ℕ} {I : Ideal (𝓞 K)} :
    I ∈ idealsLe K x ↔ I ≠ ⊥ ∧ absNorm I ≤ x := by
  simp [idealsLe, and_comm]

variable (K)

/-- The **prime powers of norm `≤ x`**: pairs `(𝔭, k)` with `𝔭` a non-zero prime, `k ≥ 1`,
`N𝔭^k ≤ x`. -/
def primePowersLe (x : ℕ) : Finset (Ideal (𝓞 K) × ℕ) :=
  ((idealsLe K x) ×ˢ Icc 1 x).filter fun pk => pk.1.IsPrime ∧ absNorm pk.1 ^ pk.2 ≤ x

variable {K}

/-- A non-zero prime ideal has norm at least `2`. -/
theorem two_le_absNorm_of_isPrime {P : Ideal (𝓞 K)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    2 ≤ absNorm P := by
  have h0 : absNorm P ≠ 0 := fun h => hP0 (absNorm_eq_zero_iff.mp h)
  have h1 : absNorm P ≠ 1 := fun h => hP.ne_top (absNorm_eq_one_iff.mp h)
  omega

theorem mem_primePowersLe {x : ℕ} {P : Ideal (𝓞 K)} {k : ℕ} :
    (P, k) ∈ primePowersLe K x ↔ P.IsPrime ∧ P ≠ ⊥ ∧ 1 ≤ k ∧ absNorm P ^ k ≤ x := by
  simp only [primePowersLe, mem_filter, mem_product, mem_idealsLe, mem_Icc]
  constructor
  · rintro ⟨⟨⟨hP0, _⟩, hk1, _⟩, hP, hx⟩
    exact ⟨hP, hP0, hk1, hx⟩
  · rintro ⟨hP, hP0, hk1, hx⟩
    have h2 := two_le_absNorm_of_isPrime hP hP0
    have hle : absNorm P ≤ absNorm P ^ k := Nat.le_self_pow (by omega) _
    have hk : k ≤ x := by
      have : k < 2 ^ k := Nat.lt_two_pow_self
      have : 2 ^ k ≤ absNorm P ^ k := Nat.pow_le_pow_left h2 k
      omega
    exact ⟨⟨⟨hP0, hle.trans hx⟩, hk1, hk⟩, hP, hx⟩

/-- **The logarithm of the norm**: `log N𝔞 = Σ_{𝔭 ∣ 𝔞} v_𝔭(𝔞) log N𝔭`. -/
theorem log_absNorm_eq_sum {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) :
    Real.log (absNorm I) = ∑ P ∈ (normalizedFactors I).toFinset,
      (Multiset.count P (normalizedFactors I) : ℝ) * Real.log (absNorm P) := by
  have hprod := Ideal.prod_normalizedFactors_eq_self hI
  rw [Finset.prod_multiset_count] at hprod
  have hN : (absNorm I : ℝ) = ∏ P ∈ (normalizedFactors I).toFinset,
      (absNorm P : ℝ) ^ Multiset.count P (normalizedFactors I) := by
    conv_lhs => rw [← hprod]
    rw [map_prod, Nat.cast_prod]
    exact prod_congr rfl fun P _ => by rw [map_pow, Nat.cast_pow]
  rw [hN, Real.log_prod]
  · exact sum_congr rfl fun P _ => by rw [Real.log_pow]
  · intro P hP
    have hP0 : P ≠ ⊥ := ne_zero_of_mem_normalizedFactors (Multiset.mem_toFinset.mp hP)
    have : (absNorm P : ℝ) ≠ 0 := by exact_mod_cast fun h => hP0 (absNorm_eq_zero_iff.mp h)
    exact pow_ne_zero _ this

/-- **Multiplicities**: for a non-zero prime `𝔭`, `𝔭^k ∣ 𝔞` iff `k ≤ v_𝔭(𝔞)`. -/
theorem pow_dvd_iff_le_count {P I : Ideal (𝓞 K)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) (hI : I ≠ ⊥)
    {k : ℕ} : P ^ k ∣ I ↔ k ≤ Multiset.count P (normalizedFactors I) := by
  have hirr : Irreducible P := ((Ideal.prime_iff_isPrime hP0).mpr hP).irreducible
  rw [pow_dvd_iff_le_emultiplicity, le_emultiplicity_iff_replicate_le_normalizedFactors hirr hI,
    normalize_eq, Multiset.le_count_iff_replicate_le]

/-- **The von Mangoldt identity**: for `𝔞 ≠ 0` with `N𝔞 ≤ x`,
`Σ_{(𝔭, k) : N𝔭^k ≤ x, 𝔭^k ∣ 𝔞} log N𝔭 = log N𝔞`. -/
theorem sum_primePowersLe_dvd_eq {I : Ideal (𝓞 K)} (hI : I ≠ ⊥) {x : ℕ} (hIx : absNorm I ≤ x) :
    ∑ pk ∈ primePowersLe K x, (if pk.1 ^ pk.2 ∣ I then Real.log (absNorm pk.1) else 0) =
      Real.log (absNorm I) := by
  set T := (normalizedFactors I).toFinset
  -- the dividing prime powers are `(𝔭, k)` with `𝔭 ∣ 𝔞` and `1 ≤ k ≤ v_𝔭(𝔞)`
  have hset : (primePowersLe K x).filter (fun pk => pk.1 ^ pk.2 ∣ I) =
      (T ×ˢ Icc 1 x).filter (fun pk => pk.2 ≤ Multiset.count pk.1 (normalizedFactors I)) := by
    ext ⟨P, k⟩
    simp only [mem_filter, mem_product, mem_primePowersLe, mem_Icc, T, Multiset.mem_toFinset]
    constructor
    · rintro ⟨⟨hP, hP0, hk1, hx⟩, hdvd⟩
      have hle := (pow_dvd_iff_le_count hP hP0 hI).mp hdvd
      have hmem : P ∈ normalizedFactors I := Multiset.count_pos.mp (by omega)
      have h2 := two_le_absNorm_of_isPrime hP hP0
      have hk : k ≤ x := by
        have : k < 2 ^ k := Nat.lt_two_pow_self
        have : 2 ^ k ≤ absNorm P ^ k := Nat.pow_le_pow_left h2 k
        omega
      exact ⟨⟨hmem, hk1, hk⟩, hle⟩
    · rintro ⟨⟨hmem, hk1, hk⟩, hle⟩
      have hprime := prime_of_normalized_factor P hmem
      have hP0 : P ≠ ⊥ := ne_zero_of_mem_normalizedFactors hmem
      have hP : P.IsPrime := (Ideal.prime_iff_isPrime hP0).mp hprime
      have hdvd : P ^ k ∣ I := (pow_dvd_iff_le_count hP hP0 hI).mpr hle
      -- `N𝔭^k = N(𝔭^k)` divides `N𝔞`
      have hnorm : absNorm P ^ k ≤ x := by
        rw [← map_pow]
        refine le_trans (Nat.le_of_dvd ?_ (absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdvd))) hIx
        exact Nat.pos_of_ne_zero fun h => hI (absNorm_eq_zero_iff.mp h)
      exact ⟨⟨hP, hP0, hk1, hnorm⟩, hdvd⟩
  rw [← sum_filter, hset, sum_filter, sum_product, log_absNorm_eq_sum hI]
  refine sum_congr rfl fun P hP => ?_
  -- `v_𝔭(𝔞) ≤ x`, so the `k`-sum counts exactly `v_𝔭(𝔞)` terms
  have hmem := Multiset.mem_toFinset.mp hP
  have hprime := prime_of_normalized_factor P hmem
  have hP0 : P ≠ ⊥ := ne_zero_of_mem_normalizedFactors hmem
  have hPp : P.IsPrime := (Ideal.prime_iff_isPrime hP0).mp hprime
  set v := Multiset.count P (normalizedFactors I)
  have hv : v ≤ x := by
    have hdvd : P ^ v ∣ I := (pow_dvd_iff_le_count hPp hP0 hI).mpr le_rfl
    have h2 := two_le_absNorm_of_isPrime hPp hP0
    have hnorm : absNorm P ^ v ≤ absNorm I := by
      rw [← map_pow]
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero fun h => hI (absNorm_eq_zero_iff.mp h))
        (absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdvd))
    have : v < 2 ^ v := Nat.lt_two_pow_self
    have : 2 ^ v ≤ absNorm P ^ v := Nat.pow_le_pow_left h2 v
    omega
  rw [← sum_filter]
  have hfilt : (Icc 1 x).filter (fun k => k ≤ v) = Icc 1 v := by
    ext k
    simp only [mem_filter, mem_Icc]
    omega
  rw [hfilt]
  simp

/-- Multiples of a non-zero ideal `Q` of norm `≤ x` correspond to ideals of norm `≤ ⌊x/NQ⌋`. -/
theorem card_filter_dvd_idealsLe {Q : Ideal (𝓞 K)} (hQ : Q ≠ ⊥) (x : ℕ) :
    ((idealsLe K x).filter (fun I => Q ∣ I)).card = (idealsLe K (x / absNorm Q)).card := by
  have hNQ : 0 < absNorm Q := Nat.pos_of_ne_zero fun h => hQ (absNorm_eq_zero_iff.mp h)
  symm
  refine card_bij (fun J _ => Q * J) (fun J hJ => ?_) (fun J₁ _ J₂ _ h => ?_) (fun I hI => ?_)
  · rw [mem_idealsLe] at hJ
    rw [mem_filter, mem_idealsLe, map_mul]
    refine ⟨⟨mul_ne_zero hQ hJ.1, ?_⟩, dvd_mul_right Q J⟩
    exact (Nat.le_div_iff_mul_le hNQ).mp hJ.2 |>.trans_eq' (mul_comm _ _)
  · exact mul_left_cancel₀ hQ h
  · rw [mem_filter, mem_idealsLe] at hI
    obtain ⟨⟨hI0, hIx⟩, J, rfl⟩ := hI
    refine ⟨J, ?_, rfl⟩
    rw [mem_idealsLe]
    refine ⟨fun h => hI0 (by rw [h, Ideal.mul_bot]), ?_⟩
    rw [map_mul] at hIx
    exact (Nat.le_div_iff_mul_le hNQ).mpr (by linarith [mul_comm (absNorm Q) (absNorm J)])

/-- **The hyperbola identity**:
`Σ_{N𝔞 ≤ x} log N𝔞 = Σ_{N𝔭^k ≤ x} log N𝔭 · #{𝔟 : N𝔟 ≤ ⌊x/N𝔭^k⌋}`. -/
theorem sum_log_absNorm_idealsLe_eq (x : ℕ) :
    ∑ I ∈ idealsLe K x, Real.log (absNorm I) =
      ∑ pk ∈ primePowersLe K x,
        Real.log (absNorm pk.1) * ((idealsLe K (x / absNorm pk.1 ^ pk.2)).card : ℝ) := by
  have hrow : ∀ I ∈ idealsLe K x, Real.log (absNorm I) =
      ∑ pk ∈ primePowersLe K x, (if pk.1 ^ pk.2 ∣ I then Real.log (absNorm pk.1) else 0) := by
    intro I hI
    rw [mem_idealsLe] at hI
    exact (sum_primePowersLe_dvd_eq hI.1 hI.2).symm
  rw [sum_congr rfl hrow, sum_comm]
  refine sum_congr rfl fun pk hpk => ?_
  obtain ⟨P, k⟩ := pk
  rw [mem_primePowersLe] at hpk
  have hQ : P ^ k ≠ ⊥ := pow_ne_zero _ hpk.2.1
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_comm, card_filter_dvd_idealsLe hQ, map_pow]

end GaloisForLFunctions.ArtinMertens
