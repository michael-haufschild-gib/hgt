import GaloisForLFunctions.ArtinMertens.TheIdealVonMangoldtIdentity
import GaloisForLFunctions.RHTower.MertensFirst

/-!
# The prime ideals satisfy Chebyshev bounds

The prime-ideal Chebyshev function `ψ_K(x) = Σ_{N𝔭^k ≤ x} log N𝔭` of a number field `K` of degree
`d = [𝓞_K : ℤ]` is at most `d² ψ(x) ≤ d² (log 4 + 4) x`.

* **Norms of primes** (`absNorm_span_natCast`, `exists_prime_absNorm_eq_pow`): `N(p𝓞_K) = p^d`,
  and every non-zero prime `𝔭` lies over a rational prime `p` with `N𝔭 = p^f`, `1 ≤ f ≤ d`, since
  `N𝔭` divides `N(p𝓞_K)`.
* **Few primes over `p`** (`card_normalizedFactors_span_natCast_le`): `p𝓞_K` has at most `d` prime
  factors with multiplicity, because each has norm at least `p`.
* **Fibres** (`card_fiber_le`, `log_absNorm_le_mul_vonMangoldt`): the prime powers `𝔭^k` with
  `N𝔭^k = q` number at most `d`, and each has `log N𝔭 ≤ d Λ(q)`.
* **The Chebyshev bound** (`sum_primePowersLe_log_le`): `ψ_K(x) ≤ d² (log 4 + 4) x`.
-/

noncomputable section

open Finset UniqueFactorizationMonoid NumberField Ideal
open scoped Classical ArithmeticFunction.vonMangoldt

namespace GaloisForLFunctions.ArtinMertens

variable {K : Type*} [Field K] [NumberField K]

local notation "d" => Module.finrank ℤ (𝓞 K)

/-- `N(p𝓞_K) = p^d`. -/
theorem absNorm_span_natCast (p : ℕ) :
    absNorm (span ({(p : 𝓞 K)} : Set (𝓞 K))) = p ^ d := by
  rw [absNorm_span_singleton, show ((p : 𝓞 K)) = algebraMap ℤ (𝓞 K) (p : ℤ) by simp,
    Algebra.norm_algebraMap, Int.natAbs_pow, Int.natAbs_natCast]

/-- A non-zero prime lies over a rational prime `p` with `N𝔭 = p^f`, `1 ≤ f ≤ d`. -/
theorem exists_prime_absNorm_eq_pow {P : Ideal (𝓞 K)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    ∃ p f : ℕ, p.Prime ∧ 1 ≤ f ∧ f ≤ d ∧ absNorm P = p ^ f ∧ (p : 𝓞 K) ∈ P := by
  haveI := hP.isMaximal hP0
  obtain ⟨p, f, hf, hpP, hp, hN⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
  refine ⟨p, f, hp, hf, ?_, hN, hpP⟩
  have hdvd : absNorm P ∣ absNorm (span ({(p : 𝓞 K)} : Set (𝓞 K))) :=
    absNorm_dvd_absNorm_of_le ((span_singleton_le_iff_mem P).mpr hpP)
  rw [hN, absNorm_span_natCast] at hdvd
  exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd

/-- `p𝓞_K` has at most `d` prime factors, counted with multiplicity. -/
theorem card_normalizedFactors_span_natCast_le {p : ℕ} (hp : p.Prime) :
    Multiset.card (normalizedFactors (span ({(p : 𝓞 K)} : Set (𝓞 K)))) ≤ d := by
  set I := span ({(p : 𝓞 K)} : Set (𝓞 K))
  have hI : I ≠ ⊥ := by
    intro h
    have := absNorm_span_natCast (K := K) p
    rw [show span ({(p : 𝓞 K)} : Set (𝓞 K)) = I from rfl, h, absNorm_bot] at this
    exact pow_ne_zero _ hp.ne_zero this.symm
  -- each prime factor has norm a positive power of `p`, so at least `p`
  have hge : ∀ P ∈ normalizedFactors I, p ≤ absNorm P := by
    intro P hP
    have hP0 : P ≠ ⊥ := ne_zero_of_mem_normalizedFactors hP
    have hPp : P.IsPrime := ((Ideal.mem_normalizedFactors_iff hI).mp hP).1
    have hle : I ≤ P := ((Ideal.mem_normalizedFactors_iff hI).mp hP).2
    have hdvd : absNorm P ∣ p ^ d := by
      rw [← absNorm_span_natCast]
      exact absNorm_dvd_absNorm_of_le hle
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    have h2 := two_le_absNorm_of_isPrime hPp hP0
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hj
      omega
    rw [hj]
    exact Nat.le_self_pow hj0 p
  have hprod : absNorm I = ((normalizedFactors I).map absNorm).prod := by
    conv_lhs => rw [← Ideal.prod_normalizedFactors_eq_self hI]
    exact map_multiset_prod absNorm _
  have hlow : p ^ Multiset.card (normalizedFactors I) ≤ absNorm I := by
    rw [hprod, ← Multiset.prod_replicate]
    refine Multiset.prod_le_prod_of_rel_le ?_
    rw [Multiset.rel_replicate_left, Multiset.card_map]
    refine ⟨rfl, fun a ha => ?_⟩
    obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.mp ha
    exact hge P hP
  rw [absNorm_span_natCast] at hlow
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hlow

/-- The prime powers over a fixed `q` number at most `d`. -/
theorem card_fiber_le (x q : ℕ) :
    ((primePowersLe K x).filter (fun pk => absNorm pk.1 ^ pk.2 = q)).card ≤ d := by
  by_cases hq : ∃ pk ∈ primePowersLe K x, absNorm pk.1 ^ pk.2 = q
  · obtain ⟨⟨P₀, k₀⟩, hpk₀, hq₀⟩ := hq
    rw [mem_primePowersLe] at hpk₀
    obtain ⟨p, f, hp, hf, -, hN₀, -⟩ := exists_prime_absNorm_eq_pow hpk₀.1 hpk₀.2.1
    set I := span ({(p : 𝓞 K)} : Set (𝓞 K))
    have hI : I ≠ ⊥ := by
      intro h
      have := absNorm_span_natCast (K := K) p
      rw [show span ({(p : 𝓞 K)} : Set (𝓞 K)) = I from rfl, h, absNorm_bot] at this
      exact pow_ne_zero _ hp.ne_zero this.symm
    have hqp : q.minFac = p := by
      rw [← hq₀, hN₀, ← pow_mul]
      exact hp.pow_minFac (Nat.mul_ne_zero (by omega) (by omega))
    refine le_trans (card_le_card_of_injOn (fun pk => pk.1) (t := (normalizedFactors I).toFinset)
      ?_ ?_) ((Multiset.toFinset_card_le _).trans (card_normalizedFactors_span_natCast_le hp))
    · -- every prime in the fibre lies over `p`
      intro ⟨P, k⟩ hpk
      simp only [coe_filter, Set.mem_setOf_eq, mem_primePowersLe] at hpk
      obtain ⟨⟨hP, hP0, hk1, -⟩, hPq⟩ := hpk
      obtain ⟨p', f', hp', hf', -, hN', hp'P⟩ := exists_prime_absNorm_eq_pow hP hP0
      have hp'p : p' = p := by
        rw [← hqp, ← hPq, hN', ← pow_mul]
        exact (hp'.pow_minFac (Nat.mul_ne_zero (by omega) (by omega))).symm
      subst hp'p
      rw [Finset.mem_coe, Multiset.mem_toFinset]
      exact (Ideal.mem_normalizedFactors_iff hI).mpr ⟨hP, (span_singleton_le_iff_mem P).mpr hp'P⟩
    · -- the exponent is determined by the prime
      intro ⟨P, k⟩ hpk ⟨P', k'⟩ hpk' h
      simp only at h
      subst h
      simp only [coe_filter, Set.mem_setOf_eq, mem_primePowersLe] at hpk hpk'
      have h2 := two_le_absNorm_of_isPrime hpk.1.1 hpk.1.2.1
      have : k = k' := Nat.pow_right_injective h2 (hpk.2.trans hpk'.2.symm)
      rw [this]
  · simp only [not_exists, not_and] at hq
    rw [filter_false_of_mem hq, card_empty]
    exact Nat.zero_le _

/-- On a prime power, `log N𝔭 ≤ d Λ(N𝔭^k)`. -/
theorem log_absNorm_le_mul_vonMangoldt {P : Ideal (𝓞 K)} (hP : P.IsPrime) (hP0 : P ≠ ⊥) {k : ℕ}
    (hk : 1 ≤ k) : Real.log (absNorm P) ≤ d * Λ (absNorm P ^ k) := by
  obtain ⟨p, f, hp, hf, hfd, hN, -⟩ := exists_prime_absNorm_eq_pow hP hP0
  rw [hN, ← pow_mul, ArithmeticFunction.vonMangoldt_apply_pow (Nat.mul_ne_zero (by omega)
    (by omega)), ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow, Real.log_pow]
  have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hfd) hlog

/-- **The Chebyshev bound for prime ideals**: `ψ_K(x) ≤ d² (log 4 + 4) x`. -/
theorem sum_primePowersLe_log_le (x : ℕ) :
    ∑ pk ∈ primePowersLe K x, Real.log (absNorm pk.1) ≤ (d : ℝ) ^ 2 * ((Real.log 4 + 4) * x) := by
  -- group the prime powers by their norm `q = N𝔭^k ≤ x`
  have hmaps : ∀ pk ∈ primePowersLe K x, absNorm pk.1 ^ pk.2 ∈ Icc 1 x := by
    intro ⟨P, k⟩ hpk
    rw [mem_primePowersLe] at hpk
    have h2 := two_le_absNorm_of_isPrime hpk.1 hpk.2.1
    have hpos : 0 < absNorm P ^ k := pow_pos (by omega) k
    exact mem_Icc.mpr ⟨hpos, hpk.2.2.2⟩
  rw [← sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ q ∈ Icc 1 x, ∑ pk ∈ (primePowersLe K x).filter (fun pk => absNorm pk.1 ^ pk.2 = q),
      Real.log (absNorm pk.1) ≤ (d : ℝ) * ((d : ℝ) * Λ q) := by
    intro q _
    calc ∑ pk ∈ (primePowersLe K x).filter (fun pk => absNorm pk.1 ^ pk.2 = q),
          Real.log (absNorm pk.1)
        ≤ ∑ _pk ∈ (primePowersLe K x).filter (fun pk => absNorm pk.1 ^ pk.2 = q),
            (d : ℝ) * Λ q := by
          refine sum_le_sum fun ⟨P, k⟩ hpk => ?_
          rw [mem_filter, mem_primePowersLe] at hpk
          rw [← hpk.2]
          exact log_absNorm_le_mul_vonMangoldt hpk.1.1 hpk.1.2.1 hpk.1.2.2.1
      _ = (((primePowersLe K x).filter (fun pk => absNorm pk.1 ^ pk.2 = q)).card : ℝ) *
            ((d : ℝ) * Λ q) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (d : ℝ) * ((d : ℝ) * Λ q) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast card_fiber_le x q)
            (mul_nonneg (Nat.cast_nonneg _) ArithmeticFunction.vonMangoldt_nonneg)
  calc ∑ q ∈ Icc 1 x, ∑ pk ∈ (primePowersLe K x).filter (fun pk => absNorm pk.1 ^ pk.2 = q),
        Real.log (absNorm pk.1)
      ≤ ∑ q ∈ Icc 1 x, (d : ℝ) * ((d : ℝ) * Λ q) := sum_le_sum hfib
    _ = (d : ℝ) ^ 2 * ∑ q ∈ Icc 1 x, Λ q := by
        rw [mul_sum]
        exact sum_congr rfl fun q _ => by ring
    _ ≤ (d : ℝ) ^ 2 * ((Real.log 4 + 4) * x) :=
        mul_le_mul_of_nonneg_left (RHTower.Mertens.sum_vonMangoldt_Icc_le x) (by positivity)

end GaloisForLFunctions.ArtinMertens
