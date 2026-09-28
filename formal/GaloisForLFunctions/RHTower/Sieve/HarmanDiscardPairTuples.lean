import GaloisForLFunctions.RHTower.Sieve.HarmanDiscardedTails

/-!
# The discarded pair tail as prime counts over prime tuples

An integer `m < q⁴` whose prime factors are all at least `q` is `1`, a prime, a product of two
primes or a product of three primes; each shape is detected through its smallest prime factors
(`rho_le_shapes`).  Summing the discarded pair tail `D₂(n)` over a window `(a, b]` and substituting
`n = q₁ q₂ m` turns it into prime counts in the windows `(a/d, b/d]`, `d = q₁ q₂`, `q₁ q₂ p`,
`q₁ q₂ p p'` (`sum_Ioc_harmanDiscardPairSum_le`).
-/

namespace RHTower.Sieve

open Finset

/-- The two-prime shapes `m = p · r`, `q ≤ p ≤ r`, counted through `p`. -/
def roughTwoShape (m q : ℕ) : ℕ :=
  ((Finset.Icc q m).filter (fun p => p.Prime ∧ p ∣ m ∧ (m / p).Prime ∧ p ≤ m / p)).card

/-- The three-prime shapes `m = p · p' · r`, `q ≤ p ≤ p' ≤ r`, counted through `(p, p')`. -/
def roughThreeShape (m q : ℕ) : ℕ :=
  (((Finset.Icc q m) ×ˢ (Finset.Icc q m)).filter (fun pp => pp.1.Prime ∧ pp.2.Prime ∧
    pp.1 ≤ pp.2 ∧ pp.1 * pp.2 ∣ m ∧ (m / (pp.1 * pp.2)).Prime ∧ pp.2 ≤ m / (pp.1 * pp.2))).card

theorem rho_le_shapes {m q : ℕ} (hm : m < q ^ 4) :
    rho m q ≤ (if m = 1 then 1 else 0) + (if m.Prime ∧ q ≤ m then 1 else 0)
      + roughTwoShape m q + roughThreeShape m q := by
  by_cases hρ : rho m q = 0
  · rw [hρ]; exact Nat.zero_le _
  have hρ1 : rho m q = 1 := by have := rho_le_one m q; omega
  rw [hρ1]
  obtain ⟨hm0, hall⟩ := rho_eq_one_iff.1 hρ1
  have hge : ∀ p, p.Prime → p ∣ m → q ≤ p := fun p hp hpm =>
    hall p (Nat.mem_primeFactors.2 ⟨hp, hpm, by omega⟩)
  by_cases h1 : m = 1
  · simp only [h1, if_true]; omega
  have hm2 : 2 ≤ m := by omega
  set p := m.minFac with hp
  have hpp : p.Prime := Nat.minFac_prime h1
  have hpm : p ∣ m := Nat.minFac_dvd m
  have hqp : q ≤ p := hge p hpp hpm
  set m1 := m / p with hm1
  have hmm1 : m = p * m1 := (Nat.mul_div_cancel' hpm).symm
  by_cases h2 : m1 = 1
  · have : m.Prime := by rw [hmm1, h2, mul_one]; exact hpp
    have hqm : q ≤ m := hqp.trans (Nat.le_of_dvd (by omega) hpm)
    simp only [h1, if_false, this, hqm, and_self, if_true]; omega
  have hm1pos : 0 < m1 := by
    rcases Nat.eq_zero_or_pos m1 with h | h
    · rw [h, mul_zero] at hmm1; omega
    · exact h
  set p1 := m1.minFac with hp1
  have hp1p : p1.Prime := Nat.minFac_prime h2
  have hp1m1 : p1 ∣ m1 := Nat.minFac_dvd m1
  have hp1m : p1 ∣ m := hmm1 ▸ Dvd.dvd.mul_left hp1m1 p
  have hpp1 : p ≤ p1 := Nat.minFac_le_of_dvd hp1p.two_le hp1m
  set m2 := m1 / p1 with hm2
  have hm1m2 : m1 = p1 * m2 := (Nat.mul_div_cancel' hp1m1).symm
  by_cases h3 : m2 = 1
  · -- two-prime shape
    have hm1prime : m1.Prime := by rw [hm1m2, h3, mul_one]; exact hp1p
    have hpm1 : p ≤ m1 := by rw [hm1m2, h3, mul_one]; exact hpp1
    have hmem : p ∈ (Finset.Icc q m).filter (fun p => p.Prime ∧ p ∣ m ∧ (m / p).Prime ∧ p ≤ m / p) := by
      refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hqp, Nat.le_of_dvd (by omega) hpm⟩,
        hpp, hpm, ?_, ?_⟩
      · rw [← hm1]; exact hm1prime
      · rw [← hm1]; exact hpm1
    have : 1 ≤ roughTwoShape m q := Finset.card_pos.2 ⟨p, hmem⟩
    omega
  have hm2pos : 0 < m2 := by
    rcases Nat.eq_zero_or_pos m2 with h | h
    · rw [h, mul_zero] at hm1m2; omega
    · exact h
  set p2 := m2.minFac with hp2
  have hp2p : p2.Prime := Nat.minFac_prime h3
  have hp2m2 : p2 ∣ m2 := Nat.minFac_dvd m2
  have hp2m1 : p2 ∣ m1 := hm1m2 ▸ Dvd.dvd.mul_left hp2m2 p1
  have hp1p2 : p1 ≤ p2 := Nat.minFac_le_of_dvd hp2p.two_le hp2m1
  set m3 := m2 / p2 with hm3
  have hm2m3 : m2 = p2 * m3 := (Nat.mul_div_cancel' hp2m2).symm
  by_cases h4 : m3 = 1
  · -- three-prime shape
    have hpp1m : p * p1 ∣ m := by
      rw [hmm1, hm1m2]; exact ⟨m2, by ring⟩
    have hdiv : m / (p * p1) = m2 := by
      rw [hmm1, hm1m2, show p * (p1 * m2) = (p * p1) * m2 by ring,
        Nat.mul_div_cancel_left _ (Nat.mul_pos hpp.pos hp1p.pos)]
    have hm2prime : m2.Prime := by rw [hm2m3, h4, mul_one]; exact hp2p
    have hp1m2 : p1 ≤ m2 := by rw [hm2m3, h4, mul_one]; exact hp1p2
    have hqp1 : q ≤ p1 := hqp.trans hpp1
    have hmpos : 0 < m := by omega
    have hmem : (p, p1) ∈ ((Finset.Icc q m) ×ˢ (Finset.Icc q m)).filter (fun pp =>
        pp.1.Prime ∧ pp.2.Prime ∧ pp.1 ≤ pp.2 ∧ pp.1 * pp.2 ∣ m ∧
        (m / (pp.1 * pp.2)).Prime ∧ pp.2 ≤ m / (pp.1 * pp.2)) := by
      refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨hqp,
        Nat.le_of_dvd hmpos hpm⟩, Finset.mem_Icc.2 ⟨hqp1, Nat.le_of_dvd hmpos hp1m⟩⟩,
        hpp, hp1p, hpp1, hpp1m, ?_, ?_⟩
      · simp only; rw [hdiv]; exact hm2prime
      · simp only; rw [hdiv]; exact hp1m2
    have : 1 ≤ roughThreeShape m q := Finset.card_pos.2 ⟨(p, p1), hmem⟩
    omega
  · -- four or more prime factors: impossible below `q⁴`
    exfalso
    have hm3pos : 0 < m3 := by
      rcases Nat.eq_zero_or_pos m3 with h | h
      · rw [h, mul_zero] at hm2m3; omega
      · exact h
    have hp3 : m3.minFac.Prime := Nat.minFac_prime h4
    have hp3m : m3.minFac ∣ m := by
      rw [hmm1, hm1m2, hm2m3]; exact Dvd.dvd.mul_left (Dvd.dvd.mul_left
        (Dvd.dvd.mul_left (Nat.minFac_dvd m3) p2) p1) p
    have hq3 : q ≤ m3 := (hge _ hp3 hp3m).trans (Nat.minFac_le hm3pos)
    have hq2 : q ≤ p2 := hqp.trans (hpp1.trans hp1p2)
    have hq1 : q ≤ p1 := hqp.trans hpp1
    have : q ^ 4 ≤ m := by
      rw [hmm1, hm1m2, hm2m3, pow_succ, pow_succ, pow_succ, pow_one]
      calc q * q * q * q ≤ p * p1 * p2 * m3 := by gcongr
        _ = p * (p1 * (p2 * m3)) := by ring
    omega

/-- Summing a function of `n/d` over the multiples of `d` in `(a, b]`. -/
theorem sum_Ioc_dvd_eq {a b d : ℕ} (hd : 0 < d) (f : ℕ → ℕ) :
    ∑ n ∈ Finset.Ioc a b, (if d ∣ n then f (n / d) else 0) = ∑ m ∈ Finset.Ioc (a / d) (b / d), f m := by
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_nbij' (fun m => d * m) (fun n => n / d) ?_ ?_ ?_ ?_ ?_
  · intro m hm
    simp only [Finset.mem_Ioc] at hm
    simp only [Finset.mem_filter, Finset.mem_Ioc]
    refine ⟨⟨?_, ?_⟩, dvd_mul_right d m⟩
    · have := (Nat.div_lt_iff_lt_mul hd).1 hm.1; linarith [mul_comm m d]
    · have := (Nat.le_div_iff_mul_le hd).1 hm.2; linarith [mul_comm m d]
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
    simp only [Finset.mem_Ioc]
    obtain ⟨⟨h1, h2⟩, k, rfl⟩ := hn
    rw [Nat.mul_div_cancel_left k hd]
    exact ⟨(Nat.div_lt_iff_lt_mul hd).2 (by linarith [mul_comm k d]),
      (Nat.le_div_iff_mul_le hd).2 (by linarith [mul_comm k d])⟩
  · intro m _; exact Nat.mul_div_cancel_left m hd
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hn
    exact Nat.mul_div_cancel' hn.2
  · intro m _; rw [Nat.mul_div_cancel_left m hd]

/-- The inadmissible prime pairs `z ≤ q₂ < q₁ < Q` with `q₁ ≥ D` or `q₁ q₂⁴ ≥ E`. -/
def harmanDiscardPairSet (z Q D E : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Ico z Q) ×ˢ (Finset.Ico z Q)).filter (fun qq => qq.1.Prime ∧ qq.2.Prime ∧
    qq.2 < qq.1 ∧ ¬ (qq.1 < D ∧ qq.1 * qq.2 ^ (4 : ℕ) < E))

theorem harmanDiscardPairSum_eq {z Q D E n : ℕ} :
    harmanDiscardPairSum z Q D E n = ∑ qq ∈ harmanDiscardPairSet z Q D E,
      (if qq.1 * qq.2 ∣ n then rho (n / (qq.1 * qq.2)) qq.2 else 0) := by
  unfold harmanDiscardPairSum harmanDiscardPairSet
  rw [Finset.sum_filter, Finset.sum_product]
  unfold primeWindow
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl (fun q₁ hq₁ => ?_)
  rw [Finset.sum_filter, Finset.sum_filter]
  by_cases hq₁n : q₁.Prime ∧ q₁ ∣ n
  · rw [if_pos hq₁n]
    have hq₁0 : 0 < q₁ := hq₁n.1.pos
    have hQ : q₁ < Q := (Finset.mem_Ico.1 hq₁).2
    rw [← Finset.sum_subset (Finset.Ico_subset_Ico_right hQ.le) (fun q₂ hq₂ hq₂' => ?_)]
    · refine Finset.sum_congr rfl (fun q₂ hq₂ => ?_)
      have hq₂1 : q₂ < q₁ := (Finset.mem_Ico.1 hq₂).2
      have hdvd : q₂ ∣ n / q₁ ↔ q₁ * q₂ ∣ n := Nat.dvd_div_iff_mul_dvd hq₁n.2
      by_cases hq₂p : q₂.Prime
      · by_cases hadm : q₁ < D ∧ q₁ * q₂ ^ (4 : ℕ) < E
        · simp [hq₂p, hadm, hq₁n.1]
        · by_cases hd : q₁ * q₂ ∣ n
          · simp [hq₂p, hadm, hq₁n.1, hq₂1, hd, hdvd.2 hd, Nat.div_div_eq_div_mul]
          · have : ¬ q₂ ∣ n / q₁ := fun h => hd (hdvd.1 h)
            simp [hq₂p, hadm, hd, this]
      · simp [hq₂p]
    · have : ¬ q₂ < q₁ := fun h => hq₂' (Finset.mem_Ico.2 ⟨(Finset.mem_Ico.1 hq₂).1, h⟩)
      simp [this]
  · rw [if_neg hq₁n]
    symm
    refine Finset.sum_eq_zero (fun q₂ _ => ?_)
    by_cases hq₁p : q₁.Prime
    · have hnd : ¬ q₁ ∣ n := fun h => hq₁n ⟨hq₁p, h⟩
      split_ifs with h1 h2 <;> try rfl
      exact absurd (dvd_trans (dvd_mul_right q₁ q₂) h2) hnd
    · split_ifs with h1 <;> try rfl
      exact absurd h1.1 hq₁p

/-- Primes `r` in `(a, b]` with `r ≥ r₀`. -/
def primeCountAbove (a b r₀ : ℕ) : ℕ := ((Finset.Ioc a b).filter (fun r => r.Prime ∧ r₀ ≤ r)).card

theorem sum_Ioc_prime_indicator_eq {a b q : ℕ} :
    ∑ m ∈ Finset.Ioc a b, (if m.Prime ∧ q ≤ m then 1 else 0) = primeCountAbove a b q := by
  rw [primeCountAbove, Finset.card_filter]

theorem sum_Ioc_roughTwoShape_eq {a b q : ℕ} :
    ∑ m ∈ Finset.Ioc a b, roughTwoShape m q =
      ∑ p ∈ (Finset.Icc q b).filter Nat.Prime, primeCountAbove (a / p) (b / p) p := by
  unfold roughTwoShape primeCountAbove
  simp_rw [Finset.card_filter]
  have hext : ∀ m ∈ Finset.Ioc a b,
      (∑ p ∈ Finset.Icc q m, if p.Prime ∧ p ∣ m ∧ (m / p).Prime ∧ p ≤ m / p then (1 : ℕ) else 0)
        = ∑ p ∈ Finset.Icc q b, if p.Prime ∧ p ∣ m ∧ (m / p).Prime ∧ p ≤ m / p then (1 : ℕ) else 0 := by
    intro m hm
    have hmb : m ≤ b := (Finset.mem_Ioc.1 hm).2
    refine Finset.sum_subset (Finset.Icc_subset_Icc le_rfl hmb) (fun p hp hpm => ?_)
    have hm0 : 0 < m := by have := (Finset.mem_Ioc.1 hm).1; omega
    rw [if_neg]
    rintro ⟨-, hdvd, -⟩
    exact hpm (Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hp).1, Nat.le_of_dvd hm0 hdvd⟩)
  rw [Finset.sum_congr rfl hext, Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  split_ifs with hpp
  · have hp0 : 0 < p := hpp.pos
    rw [← sum_Ioc_dvd_eq hp0 (fun r => if r.Prime ∧ p ≤ r then (1 : ℕ) else 0)]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    by_cases hd : p ∣ m
    · simp [hd, hpp]
    · simp [hd]
  · exact Finset.sum_eq_zero (fun m _ => by simp [hpp])

theorem sum_Ioc_roughThreeShape_eq {a b q : ℕ} :
    ∑ m ∈ Finset.Ioc a b, roughThreeShape m q =
      ∑ pp ∈ ((Finset.Icc q b) ×ˢ (Finset.Icc q b)).filter
          (fun pp => pp.1.Prime ∧ pp.2.Prime ∧ pp.1 ≤ pp.2),
        primeCountAbove (a / (pp.1 * pp.2)) (b / (pp.1 * pp.2)) pp.2 := by
  unfold roughThreeShape primeCountAbove
  simp_rw [Finset.card_filter]
  have hext : ∀ m ∈ Finset.Ioc a b,
      (∑ pp ∈ (Finset.Icc q m) ×ˢ (Finset.Icc q m), if pp.1.Prime ∧ pp.2.Prime ∧ pp.1 ≤ pp.2 ∧
          pp.1 * pp.2 ∣ m ∧ (m / (pp.1 * pp.2)).Prime ∧ pp.2 ≤ m / (pp.1 * pp.2) then (1 : ℕ) else 0)
        = ∑ pp ∈ (Finset.Icc q b) ×ˢ (Finset.Icc q b), if pp.1.Prime ∧ pp.2.Prime ∧
          pp.1 ≤ pp.2 ∧ pp.1 * pp.2 ∣ m ∧ (m / (pp.1 * pp.2)).Prime ∧
          pp.2 ≤ m / (pp.1 * pp.2) then (1 : ℕ) else 0 := by
    intro m hm
    have hmb : m ≤ b := (Finset.mem_Ioc.1 hm).2
    have hm0 : 0 < m := by have := (Finset.mem_Ioc.1 hm).1; omega
    refine Finset.sum_subset (Finset.product_subset_product (Finset.Icc_subset_Icc le_rfl hmb)
      (Finset.Icc_subset_Icc le_rfl hmb)) (fun pp hp hpm => ?_)
    rw [if_neg]
    rintro ⟨hp1, hp2, -, hdvd, -⟩
    apply hpm
    have h1 : pp.1 ∣ m := dvd_trans (dvd_mul_right _ _) hdvd
    have h2 : pp.2 ∣ m := dvd_trans (dvd_mul_left _ _) hdvd
    rw [Finset.mem_product] at hp ⊢
    exact ⟨Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hp.1).1, Nat.le_of_dvd hm0 h1⟩,
      Finset.mem_Icc.2 ⟨(Finset.mem_Icc.1 hp.2).1, Nat.le_of_dvd hm0 h2⟩⟩
  rw [Finset.sum_congr rfl hext, Finset.sum_comm, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun pp hp => ?_)
  split_ifs with hpp
  · have hp0 : 0 < pp.1 * pp.2 := Nat.mul_pos hpp.1.pos hpp.2.1.pos
    rw [← sum_Ioc_dvd_eq hp0 (fun r => if r.Prime ∧ pp.2 ≤ r then (1 : ℕ) else 0)]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    by_cases hd : pp.1 * pp.2 ∣ m
    · simp [hd, hpp]
    · simp [hd]
  · refine Finset.sum_eq_zero (fun m _ => if_neg ?_)
    rintro ⟨h1, h2, h3, -⟩
    exact hpp ⟨h1, h2, h3⟩

/-- The prime-tuple bound for one inadmissible pair: the rough cofactor `m` of `n = q₁ q₂ m` is `1`,
a prime `≥ q₂`, or a product of two or three primes `≥ q₂`. -/
def harmanPairTupleBound (a b q₂ : ℕ) : ℕ :=
  (if 1 ∈ Finset.Ioc a b then 1 else 0) + primeCountAbove a b q₂
    + ∑ p ∈ (Finset.Icc q₂ b).filter Nat.Prime, primeCountAbove (a / p) (b / p) p
    + ∑ pp ∈ ((Finset.Icc q₂ b) ×ˢ (Finset.Icc q₂ b)).filter
        (fun pp => pp.1.Prime ∧ pp.2.Prime ∧ pp.1 ≤ pp.2),
      primeCountAbove (a / (pp.1 * pp.2)) (b / (pp.1 * pp.2)) pp.2

/-- **The discarded pair tail over a window**, bounded by prime counts over prime tuples. -/
theorem sum_Ioc_harmanDiscardPairSum_le {z Q D E a b : ℕ}
    (hsmall : ∀ qq ∈ harmanDiscardPairSet z Q D E, b / (qq.1 * qq.2) < qq.2 ^ 4) :
    ∑ n ∈ Finset.Ioc a b, harmanDiscardPairSum z Q D E n ≤
      ∑ qq ∈ harmanDiscardPairSet z Q D E,
        harmanPairTupleBound (a / (qq.1 * qq.2)) (b / (qq.1 * qq.2)) qq.2 := by
  simp_rw [harmanDiscardPairSum_eq]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum (fun qq hqq => ?_)
  have hd : 0 < qq.1 * qq.2 := by
    simp only [harmanDiscardPairSet, Finset.mem_filter] at hqq
    exact Nat.mul_pos hqq.2.1.pos hqq.2.2.1.pos
  rw [sum_Ioc_dvd_eq hd (fun m => rho m qq.2)]
  calc ∑ m ∈ Finset.Ioc (a / (qq.1 * qq.2)) (b / (qq.1 * qq.2)), rho m qq.2
      ≤ ∑ m ∈ Finset.Ioc (a / (qq.1 * qq.2)) (b / (qq.1 * qq.2)),
          ((if m = 1 then 1 else 0) + (if m.Prime ∧ qq.2 ≤ m then 1 else 0)
            + roughTwoShape m qq.2 + roughThreeShape m qq.2) := by
        refine Finset.sum_le_sum (fun m hm => rho_le_shapes ?_)
        exact lt_of_le_of_lt (Finset.mem_Ioc.1 hm).2 (hsmall qq hqq)
    _ = harmanPairTupleBound (a / (qq.1 * qq.2)) (b / (qq.1 * qq.2)) qq.2 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
          sum_Ioc_prime_indicator_eq, sum_Ioc_roughTwoShape_eq, sum_Ioc_roughThreeShape_eq,
          Finset.sum_ite_eq']
        rfl

end RHTower.Sieve
