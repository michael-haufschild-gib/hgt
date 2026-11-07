import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.SmoothCompensationOfTheLargePrimes

/-!
# The letters of a compensated stencil are smooth

On `k ≤ y²` the compensated letters vanish as soon as a large prime divides `k`. So only prime powers `q^e` with `q ≤ 2y + 2` can separate `r` from a point `s ≡ r`
modulo a power of two.

If `r ≡ s` modulo a power of two above `y²`, then the near parts at `r` and `s` differ by at most the sum, over the prime powers `Q` that do not divide `r − s`, of
the defect `D_Q = Σ_{Q ∣ k} |c(k)|`.

The defects are controlled in the weighted form `Σ_Q Q D_Q ≲ y³`, up to logarithms: the number of prime powers is about `y`, each carries `T = y²`, and the compensation
adds only `gcd(Q, d_P)/d_P`, which is `1/d_P` unless `Q` meets one of the few primes of `d_P`, where the coprime factors of `d_P` cap the gcd at `2y + 2`.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

variable {y : ℕ} {d : ℕ → ℕ}

/-- **Large primes are not letters.** -/
theorem compCoeff_eq_zero (hc : IsCompensation y d) {P k : ℕ} (hP : P ∈ largePrimes y) (hPk : P ∣ k)
    (hk0 : 0 < k) (hkT : k ≤ y * y) : compCoeff y d k = 0 := by
  obtain ⟨⟨hP1, hP2⟩, hPp⟩ := mem_largePrimes.mp hP
  obtain ⟨b, rfl⟩ := hPk
  have hb0 : 0 < b := Nat.pos_of_mul_pos_left hk0
  have hb : b < 2 * y + 2 := by
    by_contra hge
    push Not at hge
    have h1 : (2 * y + 2) * (2 * y + 2) ≤ P * b := Nat.mul_le_mul hP1.le hge
    have h2 : y * y < (2 * y + 2) * (2 * y + 2) := Nat.mul_self_lt_mul_self (by omega)
    omega
  have hbP : ¬ P ∣ b := fun h => by
    have := Nat.le_of_dvd hb0 h
    omega
  have hcop : Nat.Coprime P b := (Nat.Prime.coprime_iff_not_dvd hPp).mpr hbP
  have hμ : ArithmeticFunction.moebius (P * b) = -ArithmeticFunction.moebius b := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop,
      ArithmeticFunction.moebius_apply_prime hPp]
    ring
  have hsum1 : ∑ P' ∈ largePrimes y, (if P' ∣ P * b then ArithmeticFunction.moebius (P * b / P') else 0) =
      ArithmeticFunction.moebius b := by
    rw [sum_eq_single_of_mem P hP]
    · rw [if_pos (dvd_mul_right P b), Nat.mul_div_cancel_left b hPp.pos]
    · intro P' hP' hne
      obtain ⟨⟨h1, -⟩, h3⟩ := mem_largePrimes.mp hP'
      rw [if_neg]
      intro hdiv
      rcases (Nat.Prime.dvd_mul h3).mp hdiv with h4 | h4
      · exact hne ((Nat.prime_dvd_prime_iff_eq h3 hPp).mp h4)
      · have := Nat.le_of_dvd hb0 h4
        omega
  have hsum2 : ∑ P' ∈ largePrimes y, (if d P' ∣ P * b then ArithmeticFunction.moebius (P * b / d P') else 0) = 0 := by
    refine sum_eq_zero fun P' hP' => ?_
    rw [if_neg]
    intro hdiv
    obtain ⟨m, t, hmt, hm, ht, -⟩ := hc.split P' hP'
    have hlt := hc.lt P' hP'
    have hP'1 := (mem_largePrimes.mp hP').1.1
    have hd0 : 0 < d P' := by omega
    have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => by
      rw [hmt, h, zero_mul] at hd0
      exact lt_irrefl _ hd0
    have ht0 : 0 < t := Nat.pos_of_ne_zero fun h => by
      rw [hmt, h, mul_zero] at hd0
      exact lt_irrefl _ hd0
    have hcm : Nat.Coprime (d P') P := by
      rw [hmt]
      refine Nat.Coprime.mul_left ?_ ?_
      · refine ((Nat.Prime.coprime_iff_not_dvd hPp).mpr fun h => ?_).symm
        have := Nat.le_of_dvd hm0 h
        omega
      · refine ((Nat.Prime.coprime_iff_not_dvd hPp).mpr fun h => ?_).symm
        have := Nat.le_of_dvd ht0 h
        omega
    have hdb := hcm.dvd_of_dvd_mul_left hdiv
    have := Nat.le_of_dvd hb0 hdb
    omega
  rw [compCoeff, hμ, hsum1, hsum2]
  ring

/-- The size of a letter. -/
theorem abs_compCoeff_le (hc : IsCompensation y d) {k : ℕ} (hk0 : 0 < k) (hkT : k ≤ y * y) :
    |(compCoeff y d k : ℝ)| ≤ 1 + ∑ P ∈ largePrimes y, (if d P ∣ k then (1 : ℝ) else 0) := by
  have hsum0 : 0 ≤ ∑ P ∈ largePrimes y, (if d P ∣ k then (1 : ℝ) else 0) :=
    sum_nonneg fun _ _ => by split_ifs <;> norm_num
  by_cases hex : ∃ P ∈ largePrimes y, P ∣ k
  · obtain ⟨P, hP, hPk⟩ := hex
    rw [compCoeff_eq_zero hc hP hPk hk0 hkT]
    simp only [Int.cast_zero, abs_zero]
    linarith
  · push Not at hex
    have hmid : ∑ P ∈ largePrimes y, (if P ∣ k then ArithmeticFunction.moebius (k / P) else 0) = 0 :=
      sum_eq_zero fun P hP => if_neg (hex P hP)
    have hval : (compCoeff y d k : ℝ) = (ArithmeticFunction.moebius k : ℝ) -
        ∑ P ∈ largePrimes y, (if d P ∣ k then (ArithmeticFunction.moebius (k / d P) : ℝ) else 0) := by
      rw [compCoeff, hmid, add_zero]
      push_cast
      rfl
    rw [hval]
    refine (abs_sub _ _).trans (add_le_add ?_ ((abs_sum_le_sum_abs _ _).trans (sum_le_sum fun P _ => ?_)))
    · exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    · split_ifs
      · exact_mod_cast ArithmeticFunction.abs_moebius_le_one
      · simp

/-- The odd prime powers up to `y²` over the primes up to `2y + 2`, as pairs `(q, e)`. -/
def compPairs (y : ℕ) : Finset (ℕ × ℕ) :=
  (((Icc 3 (2 * y + 2)).filter Nat.Prime) ×ˢ Icc 1 (Nat.log 2 (y * y))).filter fun x => x.1 ^ x.2 ≤ y * y

/-- The defect of a modulus `Q`: the mass of the letters it divides. -/
def compDefect (y : ℕ) (d : ℕ → ℕ) (Q : ℕ) : ℕ :=
  ∑ k ∈ Icc 2 (y * y), if Q ∣ k then (compCoeff y d k).natAbs else 0

theorem cast_compDefect (Q : ℕ) : (compDefect y d Q : ℝ) =
    ∑ k ∈ Icc 2 (y * y), if Q ∣ k then |(compCoeff y d k : ℝ)| else 0 := by
  rw [compDefect]
  push_cast
  refine sum_congr rfl fun k _ => ?_
  split_ifs
  · rw [Nat.cast_natAbs, Int.cast_abs]
  · rfl

/-- **The deficit law.** If `r ≡ s` modulo a power of two above `y²`, the near parts differ by at most the defects of the prime powers not dividing `r − s`. -/
theorem abs_compNear_sub_le_defects (hc : IsCompensation y d) {g r s : ℕ} (hTG : y * y ≤ 2 ^ g) (hsr : s ≤ r)
    (hmod : 2 ^ g ∣ r - s) :
    |compNear y d r - compNear y d s| ≤
      ∑ x ∈ compPairs y, if x.1 ^ x.2 ∣ r - s then 0 else (compDefect y d (x.1 ^ x.2) : ℝ) := by
  classical
  have hterm : ∀ k ∈ Icc 2 (y * y),
      |(-(compCoeff y d k : ℝ) / k) * ((r % k : ℕ) : ℝ) - (-(compCoeff y d k : ℝ) / k) * ((s % k : ℕ) : ℝ)| ≤
        ∑ x ∈ compPairs y, if x.1 ^ x.2 ∣ r - s then 0 else
          (if x.1 ^ x.2 ∣ k then |(compCoeff y d k : ℝ)| else 0) := by
    intro k hk
    obtain ⟨hk2, hkT⟩ := mem_Icc.mp hk
    have hnn : ∀ x ∈ compPairs y, (0 : ℝ) ≤ if x.1 ^ x.2 ∣ r - s then 0 else
        (if x.1 ^ x.2 ∣ k then |(compCoeff y d k : ℝ)| else 0) := fun x _ => by
      split_ifs
      · exact le_rfl
      · exact abs_nonneg _
      · exact le_rfl
    by_cases hdvd : k ∣ r - s
    · have hm : s % k = r % k := (Nat.modEq_iff_dvd' hsr).mpr hdvd
      rw [hm, sub_self, abs_zero]
      exact sum_nonneg hnn
    by_cases hc0 : compCoeff y d k = 0
    · have hz : (-(compCoeff y d k : ℝ) / k) = 0 := by simp [hc0]
      rw [hz, zero_mul, zero_mul, sub_self, abs_zero]
      exact sum_nonneg hnn
    -- A prime power of `k` fails, and it lies among the pairs.
    rw [Nat.dvd_iff_prime_pow_dvd_dvd] at hdvd
    push Not at hdvd
    obtain ⟨p, e, hp, hpk, hpr⟩ := hdvd
    have he : e ≠ 0 := fun h => hpr (by simp [h])
    have hk0 : 0 < k := by omega
    have hpe : p ^ e ≤ k := Nat.le_of_dvd hk0 hpk
    have hpdvd : p ∣ k := (dvd_pow_self p he).trans hpk
    have hpk' : p ≤ k := Nat.le_of_dvd hk0 hpdvd
    have hp2 : p ≠ 2 := by
      rintro rfl
      refine hpr ((pow_dvd_pow 2 ?_).trans hmod)
      have h1 : 2 ^ e ≤ 2 ^ g := hpe.trans (hkT.trans hTG)
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    have hpy : p ≤ 2 * y + 2 := by
      by_contra hgt
      push Not at hgt
      exact hc0 (compCoeff_eq_zero hc (mem_largePrimes.mpr ⟨⟨hgt, hpk'.trans hkT⟩, hp⟩) hpdvd hk0 hkT)
    have hmem : (p, e) ∈ compPairs y := by
      simp only [compPairs, mem_filter, mem_product, mem_Icc]
      refine ⟨⟨⟨⟨hp3, hpy⟩, hp⟩, Nat.pos_of_ne_zero he, ?_⟩, hpe.trans hkT⟩
      refine Nat.le_log_of_pow_le (by norm_num) ?_
      exact (Nat.pow_le_pow_left hp.two_le e).trans (hpe.trans hkT)
    have hsingle := single_le_sum hnn hmem
    simp only at hsingle
    rw [if_neg hpr, if_pos hpk] at hsingle
    refine le_trans ?_ hsingle
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
    have h1 : ((r % k : ℕ) : ℝ) ≤ k := by exact_mod_cast (Nat.mod_lt r hk0).le
    have h2 : ((s % k : ℕ) : ℝ) ≤ k := by exact_mod_cast (Nat.mod_lt s hk0).le
    have h3 : (0 : ℝ) ≤ ((r % k : ℕ) : ℝ) := Nat.cast_nonneg _
    have h4 : (0 : ℝ) ≤ ((s % k : ℕ) : ℝ) := Nat.cast_nonneg _
    have hdiff : |((r % k : ℕ) : ℝ) - ((s % k : ℕ) : ℝ)| ≤ k := by
      rw [abs_le]
      constructor <;> linarith
    rw [← mul_sub, abs_mul, abs_div, abs_neg, abs_of_pos hkR]
    have h0 := abs_nonneg (compCoeff y d k : ℝ)
    calc |(compCoeff y d k : ℝ)| / k * |((r % k : ℕ) : ℝ) - ((s % k : ℕ) : ℝ)|
        ≤ |(compCoeff y d k : ℝ)| / k * k := by gcongr
      _ = _ := by field_simp
  rw [compNear, compNear, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hterm).trans (le_of_eq ?_))
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  split_ifs
  · simp
  · rw [cast_compDefect]

/-- The size of a modulus times the letters it divides. -/
private lemma mul_card_dvd_le {Q a T : ℕ} (hQ : 0 < Q) (ha : 0 < a) :
    (Q : ℝ) * (((Ioc 0 T).filter fun k => Q ∣ k ∧ a ∣ k).card : ℝ) ≤
      (T : ℝ) * (Nat.gcd Q a : ℝ) / a := by
  have hl : 0 < Nat.lcm Q a := Nat.lcm_pos hQ ha
  have hset : (Ioc 0 T).filter (fun k => Q ∣ k ∧ a ∣ k) = (Ioc 0 T).filter (fun k => Nat.lcm Q a ∣ k) := by
    refine filter_congr fun k _ => ?_
    exact (Nat.lcm_dvd_iff).symm
  rw [hset, Nat.Ioc_filter_dvd_card_eq_div]
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hlR : (0 : ℝ) < Nat.lcm Q a := by exact_mod_cast hl
  have hg : ((Nat.gcd Q a : ℕ) : ℝ) * (Nat.lcm Q a : ℝ) = Q * a := by
    exact_mod_cast Nat.gcd_mul_lcm Q a
  have h1 : ((T / Nat.lcm Q a : ℕ) : ℝ) ≤ (T : ℝ) / Nat.lcm Q a := Nat.cast_div_le
  have hQR : (0 : ℝ) ≤ Q := Nat.cast_nonneg Q
  calc (Q : ℝ) * ((T / Nat.lcm Q a : ℕ) : ℝ) ≤ Q * ((T : ℝ) / Nat.lcm Q a) := by gcongr
    _ = _ := by
        field_simp
        linear_combination (-(T : ℝ)) * hg

/-- The defect, weighted by its modulus. -/
private lemma mul_compDefect_le (hc : IsCompensation y d) {Q : ℕ} (hQ : 0 < Q) :
    (Q : ℝ) * (compDefect y d Q : ℝ) ≤ ((y * y : ℕ) : ℝ) +
      ∑ P ∈ largePrimes y, ((y * y : ℕ) : ℝ) * (Nat.gcd Q (d P) : ℝ) / d P := by
  classical
  have hQR : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hsub : Icc 2 (y * y) ⊆ Ioc 0 (y * y) := by
    intro k hk
    obtain ⟨h1, h2⟩ := mem_Icc.mp hk
    exact mem_Ioc.mpr ⟨by omega, h2⟩
  have hD : (compDefect y d Q : ℝ) ≤ (((Ioc 0 (y * y)).filter fun k => Q ∣ k).card : ℝ) +
      ∑ P ∈ largePrimes y, (((Ioc 0 (y * y)).filter fun k => Q ∣ k ∧ d P ∣ k).card : ℝ) := by
    rw [cast_compDefect]
    have hstep : ∀ k ∈ Ioc 0 (y * y), (if Q ∣ k then |(compCoeff y d k : ℝ)| else 0) ≤
        (if Q ∣ k then (1 : ℝ) else 0) + ∑ P ∈ largePrimes y, (if Q ∣ k ∧ d P ∣ k then (1 : ℝ) else 0) := by
      intro k hk
      obtain ⟨hk0, hkT⟩ := mem_Ioc.mp hk
      by_cases hq : Q ∣ k
      · simp only [hq, if_true, true_and]
        exact abs_compCoeff_le hc hk0 hkT
      · simp only [hq, if_false, false_and]
        simp
    calc _ ≤ ∑ k ∈ Ioc 0 (y * y), if Q ∣ k then |(compCoeff y d k : ℝ)| else 0 :=
          sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => by
            split_ifs
            · exact abs_nonneg _
            · exact le_rfl
      _ ≤ _ := sum_le_sum hstep
      _ = _ := by
          rw [sum_add_distrib, sum_comm]
          congr 1
          · rw [← sum_filter]
            simp
          · refine sum_congr rfl fun P _ => ?_
            rw [← sum_filter]
            simp
  have hfirst : (Q : ℝ) * (((Ioc 0 (y * y)).filter fun k => Q ∣ k).card : ℝ) ≤ ((y * y : ℕ) : ℝ) := by
    rw [Nat.Ioc_filter_dvd_card_eq_div]
    have h1 : ((y * y / Q : ℕ) : ℝ) ≤ ((y * y : ℕ) : ℝ) / Q := Nat.cast_div_le
    calc (Q : ℝ) * ((y * y / Q : ℕ) : ℝ) ≤ Q * (((y * y : ℕ) : ℝ) / Q) := by gcongr
      _ = _ := by field_simp
  have hsecond : ∀ P ∈ largePrimes y,
      (Q : ℝ) * (((Ioc 0 (y * y)).filter fun k => Q ∣ k ∧ d P ∣ k).card : ℝ) ≤
        ((y * y : ℕ) : ℝ) * (Nat.gcd Q (d P) : ℝ) / d P := fun P hP =>
    mul_card_dvd_le hQ (lt_of_le_of_lt (Nat.zero_le P) (hc.lt P hP))
  calc (Q : ℝ) * (compDefect y d Q : ℝ)
      ≤ Q * ((((Ioc 0 (y * y)).filter fun k => Q ∣ k).card : ℝ) +
          ∑ P ∈ largePrimes y, (((Ioc 0 (y * y)).filter fun k => Q ∣ k ∧ d P ∣ k).card : ℝ)) :=
        mul_le_mul_of_nonneg_left hD hQR.le
    _ = (Q : ℝ) * (((Ioc 0 (y * y)).filter fun k => Q ∣ k).card : ℝ) +
          ∑ P ∈ largePrimes y, (Q : ℝ) * (((Ioc 0 (y * y)).filter fun k => Q ∣ k ∧ d P ∣ k).card : ℝ) := by
        rw [mul_add, mul_sum]
    _ ≤ _ := add_le_add hfirst (sum_le_sum hsecond)

/-- The gcd of a prime power with a product of two coprime small factors is small. -/
private lemma gcd_pow_mul_le {q e m t : ℕ} (hq : q.Prime) (hmt : Nat.Coprime m t) (hm : 0 < m) (ht : 0 < t) {b : ℕ}
    (hmb : m ≤ b) (htb : t ≤ b) : Nat.gcd (q ^ e) (m * t) ≤ b := by
  rw [Nat.Coprime.gcd_mul (q ^ e) hmt]
  by_cases hqt : q ∣ t
  · have hqm : ¬ q ∣ m := fun h => by
      have := Nat.Coprime.eq_one_of_dvd (hmt.coprime_dvd_left h) hqt
      exact hq.one_lt.ne' this
    have h1 : Nat.gcd (q ^ e) m = 1 := Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqm)
    rw [h1, one_mul]
    exact (Nat.le_of_dvd ht (Nat.gcd_dvd_right _ _)).trans htb
  · have h1 : Nat.gcd (q ^ e) t = 1 := Nat.Coprime.pow_left e ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqt)
    rw [h1, mul_one]
    exact (Nat.le_of_dvd hm (Nat.gcd_dvd_right _ _)).trans hmb

private lemma card_compPairs_le : ((compPairs y).card : ℝ) ≤ ((2 * y + 2 : ℕ) : ℝ) * (Nat.log 2 (y * y) : ℝ) := by
  have h1 : (compPairs y).card ≤ (2 * y + 2) * Nat.log 2 (y * y) := by
    refine (card_filter_le _ _).trans ?_
    rw [card_product, Nat.card_Icc]
    refine Nat.mul_le_mul ((card_filter_le _ _).trans ?_) (by omega)
    rw [Nat.card_Icc]
    omega
  exact_mod_cast h1

/-- Few pairs meet a given integer. -/
private lemma card_pairs_dvd_le {D : ℕ} (hD : 0 < D) :
    (((compPairs y).filter fun x => x.1 ∣ D).card : ℝ) ≤ (Nat.log 2 D : ℝ) * (Nat.log 2 (y * y) : ℝ) := by
  classical
  have hsub : (compPairs y).filter (fun x => x.1 ∣ D) ⊆
      ((Icc 3 (2 * y + 2)).filter fun q => q.Prime ∧ q ∣ D) ×ˢ Icc 1 (Nat.log 2 (y * y)) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := mem_filter.mp hx
    simp only [compPairs, mem_filter, mem_product, mem_Icc] at hx1 ⊢
    exact ⟨⟨hx1.1.1.1, hx1.1.1.2, hx2⟩, hx1.1.2⟩
  have hprimes : ((Icc 3 (2 * y + 2)).filter fun q => q.Prime ∧ q ∣ D).card ≤ Nat.log 2 D := by
    obtain ⟨S, hS⟩ : ∃ S, S = (Icc 3 (2 * y + 2)).filter fun q => q.Prime ∧ q ∣ D := ⟨_, rfl⟩
    rw [← hS]
    have hdvd : ∏ q ∈ S, q ∣ D := Finset.prod_primes_dvd D
      (fun q hq => by
        rw [hS] at hq
        exact (mem_filter.mp hq).2.1.prime)
      fun q hq => by
        rw [hS] at hq
        exact (mem_filter.mp hq).2.2
    have hpow : 2 ^ S.card ≤ ∏ q ∈ S, q := by
      refine Finset.pow_card_le_prod S (fun q => q) 2 fun q hq => ?_
      rw [hS] at hq
      exact (mem_filter.mp hq).2.1.two_le
    exact Nat.le_log_of_pow_le (by norm_num) (hpow.trans (Nat.le_of_dvd hD hdvd))
  have h2 := card_le_card hsub
  rw [card_product, Nat.card_Icc] at h2
  have h3 : ((compPairs y).filter fun x => x.1 ∣ D).card ≤ Nat.log 2 D * Nat.log 2 (y * y) :=
    h2.trans (Nat.mul_le_mul hprimes (by omega))
  exact_mod_cast h3

/-- The compensation stays within a factor of two of the prime. -/
theorem IsCompensation.le_two_mul (hc : IsCompensation y d) (hy : 4 ≤ y) {P : ℕ} (hP : P ∈ largePrimes y) :
    d P ≤ 2 * P := by
  have hyR : (4 : ℝ) ≤ y := by exact_mod_cast hy
  have h1 := hc.le P hP
  have h2 : 4 / (y : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]
    exact hyR
  have hPR : (0 : ℝ) ≤ P := Nat.cast_nonneg P
  have h3 : (d P : ℝ) ≤ 2 * P := by
    calc (d P : ℝ) ≤ P * (1 + 4 / (y : ℝ)) := h1
      _ ≤ P * 2 := mul_le_mul_of_nonneg_left (by linarith) hPR
      _ = 2 * P := mul_comm _ _
  exact_mod_cast h3

/-- The sum of `1/d_P`. -/
theorem sum_inv_compensation_le (hc : IsCompensation y d) :
    ∑ P ∈ largePrimes y, 1 / (d P : ℝ) ≤ 1 + Real.log ((y * y : ℕ) : ℝ) := by
  refine le_trans ?_ (primeHarmonic_le (y * y))
  rw [primeHarmonic]
  have hsub : largePrimes y ⊆ primesUpTo (y * y) := by
    intro P hP
    obtain ⟨⟨-, h2⟩, h3⟩ := mem_largePrimes.mp hP
    exact mem_primesUpTo.mpr ⟨h3, h2⟩
  refine le_trans (sum_le_sum fun P hP => ?_)
    (sum_le_sum_of_subset_of_nonneg hsub fun P _ _ => by positivity)
  have h0 := (mem_largePrimes.mp hP).2.pos
  have hlt := hc.lt P hP
  exact one_div_le_one_div_of_le (by exact_mod_cast h0) (by exact_mod_cast hlt.le)

/-- The total weighted defect. -/
def compWeighted (y : ℕ) (d : ℕ → ℕ) : ℝ :=
  ∑ x ∈ compPairs y, ((x.1 ^ x.2 : ℕ) : ℝ) * (compDefect y d (x.1 ^ x.2) : ℝ)

/-- The bound for the letters' mass and the weighted defect. -/
def compBound (y : ℕ) : ℝ :=
  ((y * y : ℕ) : ℝ) * ((2 * y + 2 : ℕ) : ℝ) * ((Nat.log 2 (y * y) : ℝ) + 1) * ((Nat.log 2 (y * y) : ℝ) + 3) *
    (2 + Real.log ((y * y : ℕ) : ℝ))

/-- **The weighted defect is about `y³`.** -/
theorem compWeighted_le (hc : IsCompensation y d) (hy : 4 ≤ y) : compWeighted y d ≤ compBound y := by
  classical
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ((y * y : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = (Nat.log 2 (y * y) : ℝ) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = ((2 * y + 2 : ℕ) : ℝ) := ⟨_, rfl⟩
  have hT0 : 0 ≤ T := hT ▸ Nat.cast_nonneg _
  have hl0 : 0 ≤ l := hl ▸ Nat.cast_nonneg _
  have hb0 : 0 ≤ b := hb ▸ Nat.cast_nonneg _
  have hy1 : 1 ≤ y := by omega
  have hTR : (1 : ℝ) ≤ T := by
    rw [hT]
    exact_mod_cast Nat.mul_pos hy1 hy1
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hTR
  -- The sum of the gcds over the pairs, at a fixed compensation.
  have hgcd : ∀ P ∈ largePrimes y, ∑ x ∈ compPairs y, ((Nat.gcd (x.1 ^ x.2) (d P) : ℕ) : ℝ) ≤
      b * l * (l + 2) := by
    intro P hP
    obtain ⟨m, t, hmt, hm, ht, hco⟩ := hc.split P hP
    have hd0 : 0 < d P := lt_of_le_of_lt (Nat.zero_le P) (hc.lt P hP)
    have hm0 : 0 < m := Nat.pos_of_ne_zero fun h => by
      rw [hmt, h, zero_mul] at hd0
      exact lt_irrefl _ hd0
    have ht0 : 0 < t := Nat.pos_of_ne_zero fun h => by
      rw [hmt, h, mul_zero] at hd0
      exact lt_irrefl _ hd0
    have hterm : ∀ x ∈ compPairs y, ((Nat.gcd (x.1 ^ x.2) (d P) : ℕ) : ℝ) ≤
        1 + (if x.1 ∣ d P then b else 0) := by
      intro x hx
      have hq : x.1.Prime := by
        simp only [compPairs, mem_filter, mem_product] at hx
        exact hx.1.1.2
      by_cases hqd : x.1 ∣ d P
      · rw [if_pos hqd]
        have h1 : Nat.gcd (x.1 ^ x.2) (d P) ≤ 2 * y + 2 := by
          rw [hmt]
          exact gcd_pow_mul_le hq hco hm0 ht0 hm ht
        have h2 : ((Nat.gcd (x.1 ^ x.2) (d P) : ℕ) : ℝ) ≤ b := by
          rw [hb]
          exact_mod_cast h1
        linarith
      · rw [if_neg hqd, add_zero]
        have h1 : Nat.gcd (x.1 ^ x.2) (d P) = 1 :=
          Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqd)
        rw [h1]
        simp
    refine (sum_le_sum hterm).trans ?_
    rw [sum_add_distrib, ← sum_filter, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul, mul_one]
    have h1 : ((compPairs y).card : ℝ) ≤ b * l := by
      rw [hb, hl]
      exact card_compPairs_le
    have h2 := card_pairs_dvd_le (y := y) hd0
    have h3 : Nat.log 2 (d P) ≤ Nat.log 2 (y * y) + 1 := by
      have hle : d P ≤ 2 * (y * y) := (hc.le_two_mul hy hP).trans
        (Nat.mul_le_mul_left 2 (mem_largePrimes.mp hP).1.2)
      have hmono := Nat.log_mono_right (b := 2) hle
      have hstep : Nat.log 2 (2 * (y * y)) = Nat.log 2 (y * y) + 1 := by
        rw [mul_comm, Nat.log_mul_base (by norm_num) (Nat.mul_pos (by omega) (by omega)).ne']
      omega
    have h4 : ((Nat.log 2 (d P) : ℕ) : ℝ) ≤ l + 1 := by
      rw [hl]
      exact_mod_cast h3
    have h5 : (((compPairs y).filter fun x => x.1 ∣ d P).card : ℝ) ≤ (l + 1) * l := by
      refine h2.trans ?_
      rw [← hl]
      exact mul_le_mul_of_nonneg_right h4 hl0
    have h6 : (((compPairs y).filter fun x => x.1 ∣ d P).card : ℝ) * b ≤ (l + 1) * l * b :=
      mul_le_mul_of_nonneg_right h5 hb0
    calc _ ≤ b * l + (l + 1) * l * b := by linarith
      _ = b * l * (l + 2) := by ring
  -- The sum over pairs.
  have hstep : compWeighted y d ≤ T * (b * l) + ∑ P ∈ largePrimes y, T * (b * l * (l + 2)) / d P := by
    rw [compWeighted]
    have hterm : ∀ x ∈ compPairs y, ((x.1 ^ x.2 : ℕ) : ℝ) * (compDefect y d (x.1 ^ x.2) : ℝ) ≤
        T + ∑ P ∈ largePrimes y, T * ((Nat.gcd (x.1 ^ x.2) (d P) : ℕ) : ℝ) / d P := by
      intro x hx
      have hq : x.1.Prime := by
        simp only [compPairs, mem_filter, mem_product] at hx
        exact hx.1.1.2
      have h := mul_compDefect_le hc (Q := x.1 ^ x.2) (pow_pos hq.pos _)
      rw [← hT] at h
      exact h
    refine (sum_le_sum hterm).trans ?_
    rw [sum_add_distrib, sum_const, nsmul_eq_mul, sum_comm]
    refine add_le_add ?_ (sum_le_sum fun P hP => ?_)
    · have h1 : ((compPairs y).card : ℝ) ≤ b * l := by
        rw [hb, hl]
        exact card_compPairs_le
      calc ((compPairs y).card : ℝ) * T ≤ (b * l) * T := mul_le_mul_of_nonneg_right h1 hT0
        _ = _ := by ring
    · have hd0 : (0 : ℝ) < d P := by
        exact_mod_cast lt_of_le_of_lt (Nat.zero_le P) (hc.lt P hP)
      rw [← sum_div, ← mul_sum]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hgcd P hP) hT0) hd0.le
  refine hstep.trans ?_
  have hinv := sum_inv_compensation_le hc
  rw [← hT] at hinv
  have hsum : ∑ P ∈ largePrimes y, T * (b * l * (l + 2)) / d P ≤ T * (b * l * (l + 2)) * (1 + Real.log T) := by
    have e : ∑ P ∈ largePrimes y, T * (b * l * (l + 2)) / d P =
        T * (b * l * (l + 2)) * ∑ P ∈ largePrimes y, 1 / (d P : ℝ) := by
      rw [mul_sum]
      exact sum_congr rfl fun P _ => by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hinv (by positivity)
  rw [compBound, ← hT, ← hl, ← hb]
  have hX : 0 ≤ T * b := by positivity
  have hmain : T * (b * l) + T * (b * l * (l + 2)) * (1 + Real.log T) ≤
      T * b * (l + 1) * (l + 3) * (2 + Real.log T) := by
    have h1 : l * (l + 2) ≤ (l + 1) * (l + 3) := by
      have e : (l + 1) * (l + 3) = l * (l + 2) + (2 * l + 3) := by ring
      linarith
    have h2 : l ≤ (l + 1) * (l + 3) := by
      have e : (l + 1) * (l + 3) = l + (l * l + 3 * l + 3) := by ring
      have := mul_self_nonneg l
      linarith
    have h3 : T * b * l * (1 : ℝ) ≤ T * b * ((l + 1) * (l + 3)) * 1 := by
      rw [mul_one, mul_one]
      exact mul_le_mul_of_nonneg_left h2 hX
    have h4 : T * b * (l * (l + 2)) * (1 + Real.log T) ≤ T * b * ((l + 1) * (l + 3)) * (1 + Real.log T) := by
      have h5 := mul_le_mul_of_nonneg_left h1 hX
      exact mul_le_mul_of_nonneg_right h5 (by linarith)
    calc T * (b * l) + T * (b * l * (l + 2)) * (1 + Real.log T)
        = T * b * l * 1 + T * b * (l * (l + 2)) * (1 + Real.log T) := by ring
      _ ≤ T * b * ((l + 1) * (l + 3)) * 1 + T * b * ((l + 1) * (l + 3)) * (1 + Real.log T) := add_le_add h3 h4
      _ = _ := by ring
  linarith

/-- **The mass of the letters is about `y²`.** -/
theorem compMass_le (hc : IsCompensation y d) (hy : 4 ≤ y) : compMass y d ≤ compBound y := by
  classical
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ((y * y : ℕ) : ℝ) := ⟨_, rfl⟩
  have hy1 : 1 ≤ y := by omega
  have hTR : (1 : ℝ) ≤ T := by
    rw [hT]
    exact_mod_cast Nat.mul_pos hy1 hy1
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hTR
  have hsub : Icc 2 (y * y) ⊆ Ioc 0 (y * y) := by
    intro k hk
    obtain ⟨h1, h2⟩ := mem_Icc.mp hk
    exact mem_Ioc.mpr ⟨by omega, h2⟩
  have h1 : compMass y d ≤ ∑ k ∈ Ioc 0 (y * y), |(compCoeff y d k : ℝ)| :=
    sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => abs_nonneg _
  have h2 : ∑ k ∈ Ioc 0 (y * y), |(compCoeff y d k : ℝ)| ≤
      T + ∑ P ∈ largePrimes y, T / d P := by
    have hstep : ∀ k ∈ Ioc 0 (y * y), |(compCoeff y d k : ℝ)| ≤
        1 + ∑ P ∈ largePrimes y, (if d P ∣ k then (1 : ℝ) else 0) := fun k hk =>
      abs_compCoeff_le hc (mem_Ioc.mp hk).1 (mem_Ioc.mp hk).2
    refine (sum_le_sum hstep).trans ?_
    rw [sum_add_distrib, sum_comm]
    refine add_le_add ?_ (sum_le_sum fun P hP => ?_)
    · simp [hT]
    · rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
      have hd0 : 0 < d P := lt_of_le_of_lt (Nat.zero_le P) (hc.lt P hP)
      rw [Nat.Ioc_filter_dvd_card_eq_div, hT]
      exact Nat.cast_div_le
  have h3 := sum_inv_compensation_le hc
  rw [← hT] at h3
  have h4 : ∑ P ∈ largePrimes y, T / d P ≤ T * (1 + Real.log T) := by
    have e : ∑ P ∈ largePrimes y, T / d P = T * ∑ P ∈ largePrimes y, 1 / (d P : ℝ) := by
      rw [mul_sum]
      exact sum_congr rfl fun P _ => by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left h3 (by linarith)
  refine h1.trans (h2.trans ?_)
  rw [compBound, ← hT]
  have hb : (1 : ℝ) ≤ ((2 * y + 2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : 1 ≤ 2 * y + 2)
  have hl0 : (0 : ℝ) ≤ (Nat.log 2 (y * y) : ℝ) := Nat.cast_nonneg _
  have hprod : (1 : ℝ) ≤ ((2 * y + 2 : ℕ) : ℝ) * ((Nat.log 2 (y * y) : ℝ) + 1) * ((Nat.log 2 (y * y) : ℝ) + 3) := by
    have h5 : (1 : ℝ) ≤ ((Nat.log 2 (y * y) : ℝ) + 1) * ((Nat.log 2 (y * y) : ℝ) + 3) :=
      one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
    calc (1 : ℝ) = 1 * 1 := by ring
      _ ≤ ((2 * y + 2 : ℕ) : ℝ) * (((Nat.log 2 (y * y) : ℝ) + 1) * ((Nat.log 2 (y * y) : ℝ) + 3)) :=
          mul_le_mul hb h5 zero_le_one (by linarith)
      _ = _ := by ring
  have hT0 : 0 ≤ T := by linarith
  have h6 : T * (2 + Real.log T) ≤ T * ((2 * y + 2 : ℕ) : ℝ) * ((Nat.log 2 (y * y) : ℝ) + 1) * ((Nat.log 2 (y * y) : ℝ) + 3) * (2 + Real.log T) := by
    have h7 : T * 1 ≤ T * (((2 * y + 2 : ℕ) : ℝ) * ((Nat.log 2 (y * y) : ℝ) + 1) * ((Nat.log 2 (y * y) : ℝ) + 3)) :=
      mul_le_mul_of_nonneg_left hprod hT0
    have h8 := mul_le_mul_of_nonneg_right h7 (by linarith : 0 ≤ 2 + Real.log T)
    calc T * (2 + Real.log T) = T * 1 * (2 + Real.log T) := by ring
      _ ≤ _ := h8
      _ = _ := by ring
  have e : T * (1 + Real.log T) + T = T * (2 + Real.log T) := by ring
  linarith

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
