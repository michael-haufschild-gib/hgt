import GaloisForLFunctions.PrimeTorusTheory.TheOrbitEscapesProgressions

/-!
# The saving above the small primes

The saving `le_sum_primes_critical` may sit on small primes, while the size of a column sits at the top. The word sees only the ratio `x/h`, so its progression can be taken inside a residue class: `1 + Q m` is prime to `Q`.

**Theorem** (`WordSetup.le_sum_critical_coprime`). If every prime up to `z` divides `Q`, the mean distance `ρ = 1/(48 R H² (M + 1)²)` of the progression `1 + Q m`, `m < K`, gives

`Σ_{p ≤ N, p ∤ Q} (1 − cos(t log p))/√p ≥ ρ² √z / 3`, `N = 1 + Q K`,

as soon as `Λ² √(z N) ≤ K`, `N < 2^{Λ+1}`.

**Mechanism.** The distance is subadditive over prime factors, so `K ρ ≤ Σ_p A_p ‖θ_p‖`, `A_p = Σ_{m<K} v_p(1 + Q m)`. A prime power `p^a` with `p ∤ Q` divides one residue class of `m`, so `A_p ≤ 2K/p + Λ`, and `A_p ≤ Λ` for `p > K`. Cauchy–Schwarz against `Σ_p ‖θ_p‖²/√p` then pays `Σ_{p>z} p^{−3/2} ≍ 1/√z`: deleting the small primes improves the constant.

**At height `t`** (`le_sum_critical_above`). With `L = log |t|`, `ℓ = log L`, for `2 ≤ z ≤ L`,

`Σ_{z < p ≤ L⁸ 16^z} (1 − cos(t log p))/√p ≥ √z/(10¹⁰ L⁸ ℓ⁴)`.

So the saving is not carried by the primes up to `≍ log y` at length `y`, and it grows with the length, like `√(log y)`. The length is exponential in `z` because `Q` must contain every prime up to `z`: a word cannot reach the primes above `(log y)^{1+ε}` this way.
-/

open Finset Filter Topology Real

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-- The terms of a progression divisible by a prime power lie in one residue class. -/
theorem card_filter_pow_dvd_le {p Q a K : ℕ} (hp : p.Prime) (hpQ : ¬ p ∣ Q) :
    ((range K).filter fun m => p ^ a ∣ 1 + Q * m).card ≤ K / p ^ a + 1 := by
  classical
  rcases ((range K).filter fun m => p ^ a ∣ 1 + Q * m).eq_empty_or_nonempty with h | ⟨m₀, hm₀⟩
  · simp [h]
  have hr : 0 < p ^ a := pow_pos hp.pos a
  have hcop : Nat.gcd (p ^ a) Q = 1 := Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpQ)
  have hsub : ((range K).filter fun m => p ^ a ∣ 1 + Q * m) ⊆
      (range K).filter fun m => m ≡ m₀ [MOD p ^ a] := by
    intro m hm
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hm
    refine Finset.mem_filter.mpr ⟨h1, ?_⟩
    have h0 := (Finset.mem_filter.mp hm₀).2
    have hmod : 1 + Q * m ≡ 1 + Q * m₀ [MOD p ^ a] :=
      ((Nat.modEq_zero_iff_dvd).mpr h2).trans ((Nat.modEq_zero_iff_dvd).mpr h0).symm
    have h3 : Q * m ≡ Q * m₀ [MOD p ^ a] := Nat.ModEq.add_left_cancel' 1 hmod
    exact Nat.ModEq.cancel_left_of_coprime hcop h3
  refine (Finset.card_le_card hsub).trans ?_
  rw [← Nat.count_eq_card_filter_range, Nat.count_modEq_card _ hr]
  split_ifs <;> omega

/-- The total valuation of a progression at `p`. -/
def apVal (p Q K : ℕ) : ℕ := ∑ m ∈ range K, (1 + Q * m).factorization p

/-- The total valuation as a count of prime powers. -/
theorem apVal_le_sum {p Q K Λ : ℕ} (hp : p.Prime) (hpQ : ¬ p ∣ Q) (hΛ : ∀ m < K, 1 + Q * m < 2 ^ (Λ + 1)) :
    apVal p Q K ≤ ∑ a ∈ Finset.Ico 1 (Λ + 1), (K / p ^ a + 1) := by
  classical
  have hval : ∀ m ∈ range K, (1 + Q * m).factorization p =
      ∑ a ∈ Finset.Ico 1 (Λ + 1), if p ^ a ∣ 1 + Q * m then 1 else 0 := by
    intro m hm
    have hlt : 1 + Q * m < p ^ (Λ + 1) :=
      (hΛ m (Finset.mem_range.mp hm)).trans_le (Nat.pow_le_pow_left hp.two_le _)
    rw [Nat.factorization_eq_card_pow_dvd_of_lt hp (by omega) hlt, Finset.card_filter]
  unfold apVal
  rw [Finset.sum_congr rfl hval, Finset.sum_comm]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [← Finset.card_filter]
  exact card_filter_pow_dvd_le hp hpQ

/-- The geometric bound `Σ_{1 ≤ a ≤ Λ} u^a ≤ 2u` for `u ≤ ½`. -/
theorem sum_Ico_pow_le {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 2) (Λ : ℕ) :
    ∑ a ∈ Finset.Ico 1 (Λ + 1), u ^ a ≤ 2 * u - 2 * u ^ (Λ + 1) := by
  induction Λ with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    have h : u ^ (n + 1 + 1) = u * u ^ (n + 1) := by ring
    have hp : 0 ≤ u ^ (n + 1) := pow_nonneg hu0 _
    rw [h]
    nlinarith

/-- **The valuation of a prime.** `A_p ≤ 2K/p + Λ`. -/
theorem apVal_le_of_prime {p Q K Λ : ℕ} (hp : p.Prime) (hpQ : ¬ p ∣ Q)
    (hΛ : ∀ m < K, 1 + Q * m < 2 ^ (Λ + 1)) :
    (apVal p Q K : ℝ) ≤ 2 * (K : ℝ) / p + Λ := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h := apVal_le_sum hp hpQ hΛ
  have hr : (apVal p Q K : ℝ) ≤ ∑ a ∈ Finset.Ico 1 (Λ + 1), ((K : ℝ) * (1 / (p : ℝ)) ^ a + 1) := by
    have hc : ((∑ a ∈ Finset.Ico 1 (Λ + 1), (K / p ^ a + 1) : ℕ) : ℝ) ≤
        ∑ a ∈ Finset.Ico 1 (Λ + 1), ((K : ℝ) * (1 / (p : ℝ)) ^ a + 1) := by
      push_cast
      refine Finset.sum_le_sum fun a _ => ?_
      have h1 : ((K / p ^ a : ℕ) : ℝ) ≤ (K : ℝ) / ((p ^ a : ℕ) : ℝ) := Nat.cast_div_le
      push_cast at h1
      have e : (K : ℝ) * (1 / (p : ℝ)) ^ a = (K : ℝ) / (p : ℝ) ^ a := by
        rw [div_pow, one_pow]
        ring
      rw [e]
      linarith
    exact (Nat.cast_le.mpr h).trans hc
  refine hr.trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hu0 : 0 ≤ 1 / (p : ℝ) := by positivity
  have hu : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
  have hgeo := sum_Ico_pow_le hu0 hu Λ
  have hpow : 0 ≤ (1 / (p : ℝ)) ^ (Λ + 1) := pow_nonneg hu0 _
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have h1 : (K : ℝ) * ∑ a ∈ Finset.Ico 1 (Λ + 1), (1 / (p : ℝ)) ^ a ≤ (K : ℝ) * (2 * (1 / (p : ℝ))) :=
    mul_le_mul_of_nonneg_left (by linarith) hK
  have e : (K : ℝ) * (2 * (1 / (p : ℝ))) = 2 * (K : ℝ) / p := by ring
  rw [e] at h1
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
  push_cast
  linarith

/-- A prime above the length of the progression divides at most one term per power. -/
theorem apVal_le_of_gt {p Q K Λ : ℕ} (hp : p.Prime) (hpQ : ¬ p ∣ Q) (hpK : K < p)
    (hΛ : ∀ m < K, 1 + Q * m < 2 ^ (Λ + 1)) : apVal p Q K ≤ Λ := by
  refine (apVal_le_sum hp hpQ hΛ).trans ?_
  have hterm : ∀ a ∈ Finset.Ico 1 (Λ + 1), K / p ^ a + 1 ≤ 1 := by
    intro a ha
    have ha1 := (Finset.mem_Ico.mp ha).1
    have : K < p ^ a := hpK.trans_le (Nat.le_self_pow (by omega) p)
    rw [Nat.div_eq_of_lt this]
  refine (Finset.sum_le_sum hterm).trans ?_
  simp

/-- `Σ_{z < n ≤ z + N} 1/(n √n) ≤ 2 (1/√z − 1/√(z + N))`. -/
theorem sum_Ioc_inv_mul_sqrt_le {z : ℕ} (hz : 1 ≤ z) (N : ℕ) :
    ∑ n ∈ Finset.Ioc z (z + N), 1 / ((n : ℝ) * √(n : ℝ)) ≤
      2 * (1 / √(z : ℝ) - 1 / √((z + N : ℕ) : ℝ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [← add_assoc, Finset.sum_Ioc_succ_top (by omega)]
    set a : ℝ := √((z + N : ℕ) : ℝ) with ha
    set b : ℝ := √((z + N + 1 : ℕ) : ℝ) with hb
    have hzr : (1 : ℝ) ≤ ((z + N : ℕ) : ℝ) := by
      have : 1 ≤ z + N := by omega
      exact_mod_cast this
    have hapos : 0 < a := Real.sqrt_pos.mpr (by linarith)
    have hbpos : 0 < b := Real.sqrt_pos.mpr (by positivity)
    have ha2 : a * a = ((z + N : ℕ) : ℝ) := Real.mul_self_sqrt (by positivity)
    have hb2 : b * b = ((z + N + 1 : ℕ) : ℝ) := Real.mul_self_sqrt (by positivity)
    have hdiff : b * b - a * a = 1 := by
      rw [ha2, hb2]
      push_cast
      ring
    have hab : a ≤ b := by
      refine Real.sqrt_le_sqrt ?_
      push_cast
      linarith
    have hterm : 1 / (((z + N + 1 : ℕ) : ℝ) * b) ≤ 2 * (1 / a - 1 / b) := by
      rw [← hb2]
      have e : 1 / a - 1 / b = (b - a) / (a * b) := by
        field_simp
      have h2 : b - a = 1 / (a + b) := by
        field_simp
        nlinarith
      rw [e, h2, div_div, mul_div_assoc', mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
      have h4 : a * b * (a + b) ≤ 2 * (b * b * b) := by nlinarith [mul_pos hapos hbpos]
      nlinarith
    linarith

/-- The primes up to `N` not dividing `Q`. -/
def coprimePrimes (N Q : ℕ) : Finset ℕ := (range (N + 1)).filter fun p => p.Prime ∧ ¬ p ∣ Q

theorem mem_coprimePrimes {N Q p : ℕ} : p ∈ coprimePrimes N Q ↔ p ≤ N ∧ p.Prime ∧ ¬ p ∣ Q := by
  unfold coprimePrimes
  rw [Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff]

/-- A prime factor of a term of the progression does not divide `Q`. -/
theorem primeFactors_subset {Q K m : ℕ} (hm : m < K) :
    (1 + Q * m).primeFactors ⊆ coprimePrimes (1 + Q * K) Q := by
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpn := Nat.dvd_of_mem_primeFactors hp
  refine mem_coprimePrimes.mpr ⟨?_, hpp, fun hpQ => ?_⟩
  · have h1 : p ≤ 1 + Q * m := Nat.le_of_dvd (by omega) hpn
    have h2 : Q * m ≤ Q * K := Nat.mul_le_mul_left Q hm.le
    omega
  · have h1 : p ∣ Q * m := hpQ.trans (Dvd.intro _ rfl)
    have h2 : p ∣ 1 := (Nat.dvd_add_left h1).mp hpn
    exact hpp.one_lt.ne' (Nat.dvd_one.mp h2)

/-- The mean distance on the progression is carried by its prime factors. -/
theorem sum_phaseDist_ap_le (t : ℝ) (Q K : ℕ) :
    ∑ m ∈ range K, phaseDist t (1 + Q * m) ≤
      ∑ p ∈ coprimePrimes (1 + Q * K) Q, (apVal p Q K : ℝ) * phaseDist t p := by
  classical
  have hstep : ∀ m ∈ range K, phaseDist t (1 + Q * m) ≤
      ∑ p ∈ coprimePrimes (1 + Q * K) Q, ((1 + Q * m).factorization p : ℝ) * phaseDist t p := by
    intro m hm
    refine (phaseDist_le_factorization t _).trans ?_
    exact Finset.sum_le_sum_of_subset_of_nonneg (primeFactors_subset (Finset.mem_range.mp hm))
      fun p _ _ => mul_nonneg (Nat.cast_nonneg _) (phaseDist_nonneg t p)
  refine (Finset.sum_le_sum hstep).trans (le_of_eq ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  unfold apVal
  push_cast
  rw [Finset.sum_mul]

/-- The total valuation is at most `K Λ`. -/
theorem sum_apVal_le {Q K Λ : ℕ} (hΛ : ∀ m < K, 1 + Q * m < 2 ^ (Λ + 1)) (G : Finset ℕ) :
    ∑ p ∈ G, apVal p Q K ≤ K * Λ := by
  classical
  unfold apVal
  rw [Finset.sum_comm]
  have hm : ∀ m ∈ range K, ∑ p ∈ G, (1 + Q * m).factorization p ≤ Λ := by
    intro m hm
    have h1 := sum_factorization_lt (n := 1 + Q * m) (by omega) (hΛ m (Finset.mem_range.mp hm))
    refine le_trans ?_ h1
    refine Finset.sum_le_sum_of_ne_zero fun p _ hp => ?_
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr hp
  refine (Finset.sum_le_sum hm).trans ?_
  simp

/-- **The square sum of the valuations.** Deleting the primes up to `z` gains `1/√z`. -/
theorem sum_apVal_sq_le {Q K Λ z : ℕ} (hz : 1 ≤ z) (hzQ : ∀ p : ℕ, p.Prime → p ≤ z → p ∣ Q) (hK : 1 ≤ K) (hQ : 1 ≤ Q)
    (hΛ : ∀ m < K, 1 + Q * m < 2 ^ (Λ + 1))
    (hcond : (Λ : ℝ) ^ 2 * (√(z : ℝ) * √((1 + Q * K : ℕ) : ℝ)) ≤ K) :
    ∑ p ∈ coprimePrimes (1 + Q * K) Q, (apVal p Q K : ℝ) ^ 2 * √(p : ℝ) ≤ 19 * (K : ℝ) ^ 2 / √(z : ℝ) := by
  classical
  set G := coprimePrimes (1 + Q * K) Q with hG
  set N : ℕ := 1 + Q * K with hN
  have hzr : (0 : ℝ) < z := by exact_mod_cast hz
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  have hsz : 0 < √(z : ℝ) := Real.sqrt_pos.mpr hzr
  have hsK : 0 < √(K : ℝ) := Real.sqrt_pos.mpr hKr
  have hKsq : √(K : ℝ) * √(K : ℝ) = K := Real.mul_self_sqrt hKr.le
  have hKN : K ≤ N := by
    rw [hN]
    nlinarith
  have hsKN : √(K : ℝ) ≤ √(N : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hKN)
  have hΛ2 : (0 : ℝ) ≤ (Λ : ℝ) ^ 2 := by positivity
  -- The two consequences of the condition.
  have hc1 : (Λ : ℝ) ^ 2 * √(N : ℝ) * √(z : ℝ) ≤ K := by
    calc _ = (Λ : ℝ) ^ 2 * (√(z : ℝ) * √(N : ℝ)) := by ring
      _ ≤ K := hcond
  have hc2 : (Λ : ℝ) ^ 2 * √(K : ℝ) * √(z : ℝ) ≤ K := by
    refine le_trans ?_ hc1
    gcongr
  rw [← Finset.sum_filter_add_sum_filter_not G (fun p => p ≤ K)]
  -- The primes up to `K`.
  have hG1 : ∑ p ∈ G.filter (fun p => p ≤ K), (apVal p Q K : ℝ) ^ 2 * √(p : ℝ) ≤ 18 * (K : ℝ) ^ 2 / √(z : ℝ) := by
    have hterm : ∀ p ∈ G.filter (fun p => p ≤ K), (apVal p Q K : ℝ) ^ 2 * √(p : ℝ) ≤
        8 * (K : ℝ) ^ 2 * (1 / ((p : ℝ) * √(p : ℝ))) + 2 * (Λ : ℝ) ^ 2 * √(p : ℝ) := by
      intro p hp
      obtain ⟨hpG, -⟩ := Finset.mem_filter.mp hp
      obtain ⟨-, hpp, hpQ⟩ := mem_coprimePrimes.mp hpG
      have h1 := apVal_le_of_prime hpp hpQ hΛ
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have hsp : 0 < √(p : ℝ) := Real.sqrt_pos.mpr hp0
      have hss : √(p : ℝ) * √(p : ℝ) = p := Real.mul_self_sqrt hp0.le
      have h2 : (apVal p Q K : ℝ) ^ 2 ≤ 2 * (2 * (K : ℝ) / p) ^ 2 + 2 * (Λ : ℝ) ^ 2 := by
        have h3 := pow_le_pow_left₀ (Nat.cast_nonneg _) h1 2
        nlinarith [sq_nonneg (2 * (K : ℝ) / p - Λ)]
      have h4 := mul_le_mul_of_nonneg_right h2 hsp.le
      refine h4.trans (le_of_eq ?_)
      have e : (2 * (K : ℝ) / p) ^ 2 * √(p : ℝ) = 4 * (K : ℝ) ^ 2 * (1 / ((p : ℝ) * √(p : ℝ))) := by
        have : (p : ℝ) = √(p : ℝ) * √(p : ℝ) := hss.symm
        field_simp
        nlinarith
      calc (2 * (2 * (K : ℝ) / p) ^ 2 + 2 * (Λ : ℝ) ^ 2) * √(p : ℝ) =
            2 * ((2 * (K : ℝ) / p) ^ 2 * √(p : ℝ)) + 2 * (Λ : ℝ) ^ 2 * √(p : ℝ) := by ring
        _ = _ := by
            rw [e]
            ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    -- The first sum.
    have hs1 : ∑ p ∈ G.filter (fun p => p ≤ K), 1 / ((p : ℝ) * √(p : ℝ)) ≤ 2 / √(z : ℝ) := by
      have hsub : G.filter (fun p => p ≤ K) ⊆ Finset.Ioc z (z + K) := by
        intro p hp
        obtain ⟨hpG, hpK⟩ := Finset.mem_filter.mp hp
        obtain ⟨-, hpp, hpQ⟩ := mem_coprimePrimes.mp hpG
        refine Finset.mem_Ioc.mpr ⟨?_, by omega⟩
        by_contra hle
        exact hpQ (hzQ p hpp (not_lt.mp hle))
      have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (f := fun p : ℕ => 1 / ((p : ℝ) * √(p : ℝ))) fun p _ _ => by positivity
      have h2 := sum_Ioc_inv_mul_sqrt_le hz K
      have h3 : (0 : ℝ) ≤ 1 / √((z + K : ℕ) : ℝ) := by positivity
      have e : 2 / √(z : ℝ) = 2 * (1 / √(z : ℝ)) := by ring
      rw [e]
      linarith
    -- The second sum.
    have hs2 : ∑ p ∈ G.filter (fun p => p ≤ K), √(p : ℝ) ≤ (K : ℝ) * √(K : ℝ) := by
      have hsub : G.filter (fun p => p ≤ K) ⊆ Finset.Icc 1 K := by
        intro p hp
        obtain ⟨hpG, hpK⟩ := Finset.mem_filter.mp hp
        obtain ⟨-, hpp, -⟩ := mem_coprimePrimes.mp hpG
        exact Finset.mem_Icc.mpr ⟨hpp.pos, hpK⟩
      have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub
        (f := fun p : ℕ => √(p : ℝ)) fun p _ _ => Real.sqrt_nonneg _
      refine h1.trans ?_
      have h2 : ∀ p ∈ Finset.Icc 1 K, √(p : ℝ) ≤ √(K : ℝ) := fun p hp =>
        Real.sqrt_le_sqrt (by exact_mod_cast (Finset.mem_Icc.mp hp).2)
      have h3 := Finset.sum_le_card_nsmul _ _ _ h2
      simpa using h3
    have ht1 : 8 * (K : ℝ) ^ 2 * ∑ p ∈ G.filter (fun p => p ≤ K), 1 / ((p : ℝ) * √(p : ℝ)) ≤
        16 * (K : ℝ) ^ 2 / √(z : ℝ) := by
      have := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ 8 * (K : ℝ) ^ 2)
      refine this.trans (le_of_eq ?_)
      ring
    have ht2 : 2 * (Λ : ℝ) ^ 2 * ∑ p ∈ G.filter (fun p => p ≤ K), √(p : ℝ) ≤ 2 * (K : ℝ) ^ 2 / √(z : ℝ) := by
      have h1 := mul_le_mul_of_nonneg_left hs2 (by positivity : (0 : ℝ) ≤ 2 * (Λ : ℝ) ^ 2)
      refine h1.trans ?_
      rw [le_div_iff₀ hsz]
      have := mul_le_mul_of_nonneg_left hc2 (by positivity : (0 : ℝ) ≤ 2 * (K : ℝ))
      nlinarith
    have e : 18 * (K : ℝ) ^ 2 / √(z : ℝ) = 16 * (K : ℝ) ^ 2 / √(z : ℝ) + 2 * (K : ℝ) ^ 2 / √(z : ℝ) := by ring
    rw [e]
    exact add_le_add ht1 ht2
  -- The primes above `K`.
  have hG2 : ∑ p ∈ G.filter (fun p => ¬ p ≤ K), (apVal p Q K : ℝ) ^ 2 * √(p : ℝ) ≤ (K : ℝ) ^ 2 / √(z : ℝ) := by
    have hterm : ∀ p ∈ G.filter (fun p => ¬ p ≤ K), (apVal p Q K : ℝ) ^ 2 * √(p : ℝ) ≤
        (Λ : ℝ) * √(N : ℝ) * (apVal p Q K : ℝ) := by
      intro p hp
      obtain ⟨hpG, hpK⟩ := Finset.mem_filter.mp hp
      obtain ⟨hpN, hpp, hpQ⟩ := mem_coprimePrimes.mp hpG
      have h1 : (apVal p Q K : ℝ) ≤ Λ := by
        exact_mod_cast apVal_le_of_gt hpp hpQ (not_le.mp hpK) hΛ
      have h2 : √(p : ℝ) ≤ √(N : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hpN)
      have h0 : (0 : ℝ) ≤ apVal p Q K := Nat.cast_nonneg _
      calc (apVal p Q K : ℝ) ^ 2 * √(p : ℝ) = (apVal p Q K : ℝ) * √(p : ℝ) * (apVal p Q K : ℝ) := by ring
        _ ≤ (Λ : ℝ) * √(N : ℝ) * (apVal p Q K : ℝ) :=
            mul_le_mul_of_nonneg_right (mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Nat.cast_nonneg _)) h0
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    have hsum : ∑ p ∈ G.filter (fun p => ¬ p ≤ K), (apVal p Q K : ℝ) ≤ (K : ℝ) * Λ := by
      have := sum_apVal_le hΛ (G.filter fun p => ¬ p ≤ K)
      exact_mod_cast this
    have h1 := mul_le_mul_of_nonneg_left hsum (mul_nonneg (Nat.cast_nonneg Λ) (Real.sqrt_nonneg (N : ℝ)))
    refine h1.trans ?_
    rw [le_div_iff₀ hsz]
    have := mul_le_mul_of_nonneg_left hc1 hKr.le
    nlinarith
  have e : 19 * (K : ℝ) ^ 2 / √(z : ℝ) = 18 * (K : ℝ) ^ 2 / √(z : ℝ) + (K : ℝ) ^ 2 / √(z : ℝ) := by ring
  rw [e]
  exact add_le_add hG1 hG2

/-- **The saving above the small primes**, for a word. -/
theorem WordSetup.le_sum_critical_coprime {H R : ℝ} {M k N₁ Q K Λ z : ℕ} {c : ℕ → ℤ} {t : ℝ}
    (S : WordSetup H R M k N₁ c t) (hK : 6 * M + 6 ≤ K) (hQ : 1 ≤ Q) (hz : 1 ≤ z)
    (hzQ : ∀ p : ℕ, p.Prime → p ≤ z → p ∣ Q) (hΛ : ∀ m < K, 1 + Q * m < 2 ^ (Λ + 1))
    (hcond : (Λ : ℝ) ^ 2 * (√(z : ℝ) * √((1 + Q * K : ℕ) : ℝ)) ≤ K) :
    (1 / (48 * R * H ^ 2 * ((M : ℝ) + 1) ^ 2)) ^ 2 * √(z : ℝ) / 3 ≤
      ∑ p ∈ coprimePrimes (1 + Q * K) Q, (1 - Real.cos (t * Real.log p)) / √(p : ℝ) := by
  set G := coprimePrimes (1 + Q * K) Q with hG
  set ρ : ℝ := 1 / (48 * R * H ^ 2 * ((M : ℝ) + 1) ^ 2) with hρ
  have hH0 : 0 < H := by linarith [S.one_le_H]
  have hR0 : 0 < R := by linarith [S.one_le_R]
  have hρ0 : 0 < ρ := by
    rw [hρ]
    positivity
  have hK1 : 1 ≤ K := by omega
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK1
  have hzr : (0 : ℝ) < z := by exact_mod_cast hz
  have hsz : 0 < √(z : ℝ) := Real.sqrt_pos.mpr hzr
  -- The mean distance on the progression.
  have hmean : (K : ℝ) * ρ ≤ ∑ m ∈ range K, phaseDist t (1 + Q * m) := by
    have h := S.le_sum_rotDist_ap 0 (q := Q) (r := 1) hQ hQ hK
    have e : (K : ℝ) * ρ = (K : ℝ) / (48 * R * H ^ 2 * ((M : ℝ) + 1) ^ 2) := by
      rw [hρ]
      ring
    rw [e]
    refine h.trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun m _ => rotDist_zero t _
  have hupper := sum_phaseDist_ap_le t Q K
  set D : ℝ := ∑ p ∈ G, phaseDist t p ^ 2 / √(p : ℝ) with hD
  have hDnn : 0 ≤ D := Finset.sum_nonneg fun p _ => by positivity
  -- Cauchy–Schwarz.
  have hcs : (∑ p ∈ G, (apVal p Q K : ℝ) * phaseDist t p) ^ 2 ≤
      (∑ p ∈ G, (apVal p Q K : ℝ) ^ 2 * √(p : ℝ)) * D := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun p _ => by positivity)
      (fun p _ => by positivity) fun p hp => le_of_eq ?_
    have hpp := (mem_coprimePrimes.mp hp).2.1
    have hsp : 0 < √(p : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hpp.pos)
    field_simp
  have hbound := sum_apVal_sq_le hz hzQ hK1 hQ hΛ hcond
  have hsum0 : 0 ≤ ∑ p ∈ G, (apVal p Q K : ℝ) * phaseDist t p := by
    exact Finset.sum_nonneg fun p _ => mul_nonneg (Nat.cast_nonneg _) (phaseDist_nonneg t p)
  have hsq : ((K : ℝ) * ρ) ^ 2 ≤ 19 * (K : ℝ) ^ 2 / √(z : ℝ) * D := by
    have h1 : ((K : ℝ) * ρ) ^ 2 ≤ (∑ p ∈ G, (apVal p Q K : ℝ) * phaseDist t p) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (hmean.trans hupper) 2
    exact h1.trans (hcs.trans (mul_le_mul_of_nonneg_right hbound hDnn))
  have hDlow : ρ ^ 2 * √(z : ℝ) / 19 ≤ D := by
    have hK2 : (0 : ℝ) < (K : ℝ) ^ 2 := by positivity
    rw [div_le_iff₀ (by norm_num)]
    have e : ((K : ℝ) * ρ) ^ 2 = (K : ℝ) ^ 2 * ρ ^ 2 := by ring
    have e2 : 19 * (K : ℝ) ^ 2 / √(z : ℝ) * D = (K : ℝ) ^ 2 * (19 * D / √(z : ℝ)) := by ring
    rw [e, e2] at hsq
    have h3 := le_of_mul_le_mul_left hsq hK2
    rw [le_div_iff₀ hsz] at h3
    linarith
  have hcol : 8 * D ≤ ∑ p ∈ G, (1 - Real.cos (t * Real.log p)) / √(p : ℝ) := by
    rw [hD, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have hpp := (mem_coprimePrimes.mp hp).2.1
    have hsp : 0 < √(p : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hpp.pos)
    have h1 := eight_mul_sq_le_one_sub_cos (t * Real.log p / (2 * π))
    have e : 2 * π * (t * Real.log p / (2 * π)) = t * Real.log p := by
      field_simp
    rw [e] at h1
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right h1 hsp.le
  have hpos : 0 ≤ ρ ^ 2 * √(z : ℝ) := by positivity
  linarith

/-- The size of the progression above `z`. -/
theorem HeightSize.above_size {L ℓ : ℝ} (h : HeightSize L ℓ) {M z A Q : ℕ} (hM2 : (M : ℝ) ≤ 6 * L ^ 2 * ℓ + 1)
    (hzL : (z : ℝ) ≤ L) (hA2 : (A : ℝ) ≤ 101 * ℓ) (hQ : (Q : ℝ) ≤ 4 ^ z) :
    ((1 + Q * (8 * (M + 1) + 2 * z * Q * (A + 8 * z) ^ 4) : ℕ) : ℝ) ≤ L ^ 8 * 16 ^ z := by
  have hL := h.hundred_le
  have h100 := h.log_le
  have hML : (M : ℝ) + 1 ≤ L ^ 3 := by linarith [h.M_add_two_le hM2]
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have hz0 : (0 : ℝ) ≤ z := Nat.cast_nonneg z
  have hQ0 : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  have hL0 : (0 : ℝ) < L := by linarith
  have hΛ : (A : ℝ) + 8 * z ≤ 10 * L := by linarith
  have hΛ4 : ((A : ℝ) + 8 * z) ^ 4 ≤ (10 * L) ^ 4 := pow_le_pow_left₀ (by positivity) hΛ 4
  have h4 : (1 : ℝ) ≤ 4 ^ z := one_le_pow₀ (by norm_num)
  set Y : ℝ := (4 : ℝ) ^ z with hY
  have h16 : (16 : ℝ) ^ z = Y ^ 2 := by
    rw [hY, ← pow_mul, mul_comm, pow_mul]
    norm_num
  have hL3 : (10 : ℝ) ^ 6 ≤ L ^ 3 := by
    have := pow_le_pow_left₀ (by norm_num) hL 3
    norm_num at this ⊢
    linarith
  have hL5 : L ^ 3 ≤ L ^ 5 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hK : 8 * ((M : ℝ) + 1) + 2 * z * Q * ((A : ℝ) + 8 * z) ^ 4 ≤ 20008 * (L ^ 5 * Y) := by
    have h1 : 2 * (z : ℝ) * Q * ((A : ℝ) + 8 * z) ^ 4 ≤ 2 * L * Y * (10 * L) ^ 4 := by
      gcongr
    have e : 2 * L * Y * (10 * L) ^ 4 = 20000 * (L ^ 5 * Y) := by ring
    rw [e] at h1
    have h2 : L ^ 3 ≤ L ^ 5 * Y := by
      calc L ^ 3 ≤ L ^ 5 * 1 := by linarith
        _ ≤ L ^ 5 * Y := mul_le_mul_of_nonneg_left h4 (by positivity)
    linarith
  push_cast
  have hprod : (Q : ℝ) * (8 * ((M : ℝ) + 1) + 2 * z * Q * ((A : ℝ) + 8 * z) ^ 4) ≤ Y * (20008 * (L ^ 5 * Y)) :=
    mul_le_mul hQ hK (by positivity) (by positivity)
  have e2 : Y * (20008 * (L ^ 5 * Y)) = 20008 * (L ^ 5 * Y ^ 2) := by ring
  rw [e2] at hprod
  rw [h16]
  have hpos : (1 : ℝ) ≤ L ^ 5 * Y ^ 2 :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith)) (one_le_pow₀ h4)
  have e3 : L ^ 8 * Y ^ 2 = L ^ 3 * (L ^ 5 * Y ^ 2) := by ring
  rw [e3]
  have hfin : (20009 : ℝ) * (L ^ 5 * Y ^ 2) ≤ L ^ 3 * (L ^ 5 * Y ^ 2) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  linarith

/-- The size above `z`, against the number of prime factors. -/
theorem HeightSize.above_two_pow {L ℓ N : ℝ} (h : HeightSize L ℓ) {z A : ℕ} (hA : 100 * ℓ ≤ A)
    (hN : N ≤ L ^ 8 * 16 ^ z) : N < 2 ^ (A + 8 * z + 1) := by
  have hexp := h.exp_eq
  have hℓ := h.one_le
  have ha := Real.log_two_gt_d9
  have hL8 : L ^ 8 ≤ (2 : ℝ) ^ A := by
    have h2 : (2 : ℝ) ^ A = Real.exp ((A : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    have h3 : L ^ 8 = Real.exp (8 * ℓ) := by
      rw [← hexp, ← Real.exp_nat_mul]
      norm_num
    rw [h2, h3]
    refine Real.exp_le_exp.mpr ?_
    have h4 : (A : ℝ) * 0.69 ≤ (A : ℝ) * Real.log 2 :=
      mul_le_mul_of_nonneg_left (by linarith) (Nat.cast_nonneg A)
    nlinarith
  have h16 : (16 : ℝ) ^ z ≤ (2 : ℝ) ^ (8 * z) := by
    have e : (16 : ℝ) = 2 ^ 4 := by norm_num
    rw [e, ← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have h3 : L ^ 8 * 16 ^ z ≤ (2 : ℝ) ^ (A + 8 * z) := by
    rw [pow_add]
    exact mul_le_mul hL8 h16 (by positivity) (by positivity)
  have h4 : (2 : ℝ) ^ (A + 8 * z) < 2 ^ (A + 8 * z + 1) := by
    rw [pow_succ]
    have : (0 : ℝ) < 2 ^ (A + 8 * z) := by positivity
    linarith
  linarith

/-- **The saving above the small primes.** With `L = log |t|`, `ℓ = log L`, for `1 ≤ z ≤ L`, `Σ_{z < p ≤ L⁸ 16^z} (1 − cos(t log p))/√p ≥ √z/(10¹⁰ L⁸ ℓ⁴)`. -/
theorem le_sum_critical_above :
    ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ t : ℝ, T₀ ≤ |t| → ∀ z : ℕ, 1 ≤ z → (z : ℝ) ≤ Real.log |t| →
      √(z : ℝ) / (10 ^ 10 * Real.log |t| ^ 8 * Real.log (Real.log |t|) ^ 4) ≤
        ∑ p ∈ (range (⌊Real.log |t| ^ 8 * 16 ^ z⌋₊ + 1)).filter (fun p => p.Prime ∧ z < p),
          (1 - Real.cos (t * Real.log p)) / √(p : ℝ) := by
  obtain ⟨T₀, hT₀, hsize⟩ := eventually_heightSize
  refine ⟨T₀, hT₀, fun t ht z hz hzL => ?_⟩
  have h := hsize t ht
  have htpos : 0 < |t| := lt_of_lt_of_le hT₀ ht
  have hexp : Real.exp (Real.log |t|) = |t| := Real.exp_log htpos
  generalize Real.log |t| = L at h hexp hzL ⊢
  generalize Real.log L = ℓ at h ⊢
  have hL := h.hundred_le
  have hℓ := h.one_le
  have h100 := h.log_le
  have hM1 : 6 * L ^ 2 * ℓ ≤ (⌈6 * L ^ 2 * ℓ⌉₊ : ℝ) := Nat.le_ceil _
  have hM2 : ((⌈6 * L ^ 2 * ℓ⌉₊ : ℕ) : ℝ) ≤ 6 * L ^ 2 * ℓ + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hk1 : L ≤ (⌈L⌉₊ : ℝ) := Nat.le_ceil _
  have hk2 : ((⌈L⌉₊ : ℕ) : ℝ) ≤ L + 1 := (Nat.ceil_lt_add_one (by linarith)).le
  have hN1 : ((⌊L / 2⌋₊ : ℕ) : ℝ) ≤ L / 2 := Nat.floor_le (by linarith)
  have hN2 : L / 2 - 1 ≤ ((⌊L / 2⌋₊ : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one (L / 2)
    linarith
  have hN3 : 1 ≤ ⌊L / 2⌋₊ := Nat.le_floor (by push_cast; linarith)
  obtain ⟨c, S⟩ := h.exists_setup hexp hM1 hM2 hk1 hk2 hN1 hN2 hN3
  generalize ⌈6 * L ^ 2 * ℓ⌉₊ = M at S hM1 hM2
  have hA : 100 * ℓ ≤ (⌈100 * ℓ⌉₊ : ℝ) := Nat.le_ceil _
  have hA2 : ((⌈100 * ℓ⌉₊ : ℕ) : ℝ) ≤ 101 * ℓ := by
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 100 * ℓ)
    linarith
  generalize ⌈100 * ℓ⌉₊ = A at hA hA2
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = primorial z := ⟨_, rfl⟩
  have hQ1 : 1 ≤ Q := by
    rw [hQdef]
    exact primorial_pos z
  have hQ4 : (Q : ℝ) ≤ 4 ^ z := by
    rw [hQdef]
    exact_mod_cast primorial_le_four_pow z
  obtain ⟨Λ, hΛdef⟩ : ∃ Λ, Λ = A + 8 * z := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K, K = 8 * (M + 1) + 2 * z * Q * Λ ^ 4 := ⟨_, rfl⟩
  have hsize' := h.above_size (M := M) (z := z) (A := A) (Q := Q) hM2 hzL hA2 hQ4
  rw [← hΛdef, ← hKdef] at hsize'
  have hpow := h.above_two_pow (z := z) hA hsize'
  rw [← hΛdef] at hpow
  have hNlt : 1 + Q * K < 2 ^ (Λ + 1) := by exact_mod_cast hpow
  have hK : 6 * M + 6 ≤ K := by
    rw [hKdef]
    omega
  have hK1 : 1 ≤ K := by omega
  have hzQ : ∀ p : ℕ, p.Prime → p ≤ z → p ∣ Q := fun p hp hpz => by
    rw [hQdef]
    exact (hp.dvd_primorial_iff).mpr hpz
  have hΛm : ∀ m < K, 1 + Q * m < 2 ^ (Λ + 1) := by
    intro m hm
    have : Q * m ≤ Q * K := Nat.mul_le_mul_left Q hm.le
    omega
  have hzr : (0 : ℝ) < z := by exact_mod_cast hz
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK1
  have hQr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ1
  -- The condition on the length.
  have hcond : (Λ : ℝ) ^ 2 * (√(z : ℝ) * √((1 + Q * K : ℕ) : ℝ)) ≤ K := by
    have hNle : ((1 + Q * K : ℕ) : ℝ) ≤ 2 * (Q : ℝ) * K := by
      push_cast
      have hK1r : (1 : ℝ) ≤ K := by exact_mod_cast hK1
      have := one_le_mul_of_one_le_of_one_le hQr hK1r
      linarith
    have hKge : 2 * (z : ℝ) * Q * (Λ : ℝ) ^ 4 ≤ K := by
      rw [hKdef]
      push_cast
      have : (0 : ℝ) ≤ (M : ℝ) + 1 := by positivity
      linarith
    refine (pow_le_pow_iff_left₀ (by positivity) hKr.le two_ne_zero).mp ?_
    have e : ((Λ : ℝ) ^ 2 * (√(z : ℝ) * √((1 + Q * K : ℕ) : ℝ))) ^ 2 =
        (Λ : ℝ) ^ 4 * ((z : ℝ) * ((1 + Q * K : ℕ) : ℝ)) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hzr.le, Real.sq_sqrt (Nat.cast_nonneg _)]
      ring
    rw [e]
    have h1 : (Λ : ℝ) ^ 4 * ((z : ℝ) * ((1 + Q * K : ℕ) : ℝ)) ≤ (Λ : ℝ) ^ 4 * ((z : ℝ) * (2 * (Q : ℝ) * K)) := by
      gcongr
    have h2 : (Λ : ℝ) ^ 4 * ((z : ℝ) * (2 * (Q : ℝ) * K)) = (2 * (z : ℝ) * Q * (Λ : ℝ) ^ 4) * K := by ring
    rw [h2] at h1
    have h3 := mul_le_mul_of_nonneg_right hKge hKr.le
    nlinarith
  have hmain := S.le_sum_critical_coprime hK hQ1 hz hzQ hΛm hcond
  -- The primes of the sum.
  have hsub : coprimePrimes (1 + Q * K) Q ⊆
      (range (⌊L ^ 8 * 16 ^ z⌋₊ + 1)).filter (fun p => p.Prime ∧ z < p) := by
    intro p hp
    obtain ⟨hpN, hpp, hpQ⟩ := mem_coprimePrimes.mp hp
    refine Finset.mem_filter.mpr ⟨?_, hpp, ?_⟩
    · refine Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor ?_))
      have : (p : ℝ) ≤ ((1 + Q * K : ℕ) : ℝ) := by exact_mod_cast hpN
      exact this.trans hsize'
    · by_contra hle
      exact hpQ (hzQ p hpp (not_lt.mp hle))
  have hsum := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun p : ℕ => (1 - Real.cos (t * Real.log p)) / √(p : ℝ)) fun p _ _ =>
      div_nonneg (by linarith [Real.cos_le_one (t * Real.log p)]) (Real.sqrt_nonneg _)
  refine le_trans ?_ (hmain.trans hsum)
  -- The constant.
  have hMl : (M : ℝ) + 1 ≤ 8 * (L ^ 2 * ℓ) := by
    have : (1 : ℝ) ≤ L ^ 2 * ℓ := by nlinarith
    nlinarith
  have hLpos : 0 < L := by linarith
  have hℓpos : 0 < ℓ := by linarith
  have hsz : 0 < √(z : ℝ) := Real.sqrt_pos.mpr hzr
  have hM1r : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have hsq : (48 * (16 : ℝ) * 1 ^ 2 * ((M : ℝ) + 1) ^ 2) ^ 2 ≤ 2415919104 * (L ^ 8 * ℓ ^ 4) := by
    have h1 : ((M : ℝ) + 1) ^ 4 ≤ (8 * (L ^ 2 * ℓ)) ^ 4 := pow_le_pow_left₀ hM1r.le hMl 4
    have e1 : (48 * (16 : ℝ) * 1 ^ 2 * ((M : ℝ) + 1) ^ 2) ^ 2 = 589824 * ((M : ℝ) + 1) ^ 4 := by ring
    have e2 : (8 * (L ^ 2 * ℓ)) ^ 4 = 4096 * (L ^ 8 * ℓ ^ 4) := by ring
    rw [e1]
    rw [e2] at h1
    linarith
  have e : (1 / (48 * (16 : ℝ) * 1 ^ 2 * ((M : ℝ) + 1) ^ 2)) ^ 2 * √(z : ℝ) / 3 =
      √(z : ℝ) / (3 * (48 * (16 : ℝ) * 1 ^ 2 * ((M : ℝ) + 1) ^ 2) ^ 2) := by
    field_simp
  rw [e]
  refine div_le_div_of_nonneg_left hsz.le (by positivity) ?_
  have hnn : 0 < L ^ 8 * ℓ ^ 4 := by positivity
  have e3 : (10 : ℝ) ^ 10 * L ^ 8 * ℓ ^ 4 = 10 ^ 10 * (L ^ 8 * ℓ ^ 4) := by ring
  rw [e3]
  linarith

end

end GaloisForLFunctions.PrimeTorusTheory
