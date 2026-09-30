import GaloisForLFunctions.RHTower.RobinInequalityKFree

/-!
# Landau's theorem for `n/φ(n)` and the primorial side of Nicolas's criterion

Nicolas's criterion reads RH ⇔ `N_k/φ(N_k) > e^γ log log N_k` for every primorial `N_k`. This
module proves the unconditional statements about `n/φ(n) = ∏_{p∣n}(1 − 1/p)^{−1}`
(`div_totient_eq_prod`) that follow from Mertens' third theorem.

* **Landau (1903).** `limsup n/(φ(n) log log n) = e^γ`: eventually
  `n/φ(n) ≤ (e^γ + ε) log log n` (`eventually_div_totient_le_landau`), and the primorial powers attain
  `(e^γ − ε) log log n` (`frequently_div_totient_ge_landau`).
* **Only near-primorials can satisfy Nicolas's inequality.** For every `δ > 0`, eventually every `n`
  whose missing primes `p ≤ log n`, `p ∤ n`, have harmonic mass `≥ δ` satisfies
  `n/φ(n) < e^γ log log n` (`eventually_div_totient_lt_of_missing`). This follows from
  `n/φ(n) ≤ (∏_{p≤N}(1−1/p))^{−1} e^{−Σ_{p≤N, p∤n} 1/p} (1+1/N)^{|S_{>N}|}`
  (`div_totient_le_mertens_missing`).
-/

open ArithmeticFunction Filter Finset

namespace RHTower

noncomputable section

/-- `n/φ(n) = ∏_{p ∣ n} (1 − 1/p)^{−1}`. -/
theorem div_totient_eq_prod {n : ℕ} (hn : n ≠ 0) :
    (n : ℝ) / (n.totient : ℝ) = ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ))⁻¹ := by
  have h := Nat.totient_mul_prod_primeFactors n
  have hpr : ∀ p ∈ n.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hφ : (0 : ℝ) < n.totient := by exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn)
  have hR : (n.totient : ℝ) * ∏ p ∈ n.primeFactors, (p : ℝ) =
      (n : ℝ) * ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
    have := congrArg (fun k : ℕ => (k : ℝ)) h
    push_cast at this
    rw [this]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.cast_sub (hpr p hp).one_lt.le]; simp
  have hP : (0 : ℝ) < ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := Finset.prod_pos fun p hp => by
    have : (2 : ℝ) ≤ p := by exact_mod_cast (hpr p hp).two_le
    linarith
  have e : ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ))⁻¹ =
      (∏ p ∈ n.primeFactors, (p : ℝ)) / ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hpr p hp).ne_zero
    field_simp
  rw [e, div_eq_div_iff hφ.ne' hP.ne']
  linarith

/-- **The Mertens bound with the missing primes.** -/
theorem div_totient_le_mertens_missing {n N : ℕ} (hn : n ≠ 0) (hN : 1 ≤ N) :
    (n : ℝ) / (n.totient : ℝ) ≤ (mertensPrimeProduct N)⁻¹ *
      Real.exp (-∑ p ∈ ((Finset.Icc 0 N).filter Nat.Prime).filter (fun p => ¬ p ∣ n),
        1 / (p : ℝ)) *
      (1 + 1 / (N : ℝ)) ^ (n.primeFactors.filter (N < ·)).card := by
  rw [div_totient_eq_prod hn, ← Finset.prod_filter_mul_prod_filter_not n.primeFactors (· ≤ N)]
  have hpr : ∀ p ∈ n.primeFactors, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors hp
  have hfilt : n.primeFactors.filter (fun p => ¬ p ≤ N) = n.primeFactors.filter (N < ·) := by
    ext p; simp [not_le]
  rw [hfilt]
  set P := (Finset.Icc 0 N).filter Nat.Prime with hP
  set S := n.primeFactors.filter (· ≤ N) with hS
  set M := P.filter (fun p => ¬ p ∣ n) with hM
  have hPS : P = S ∪ M := by
    ext p
    simp only [hP, hS, hM, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc,
      Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨h0, hpN⟩, hp⟩
      by_cases hd : p ∣ n
      · exact Or.inl ⟨⟨hp, hd, hn⟩, hpN⟩
      · exact Or.inr ⟨⟨⟨h0, hpN⟩, hp⟩, hd⟩
    · rintro (⟨⟨hp, _, _⟩, hpN⟩ | ⟨⟨⟨h0, hpN⟩, hp⟩, _⟩)
      · exact ⟨⟨Nat.zero_le _, hpN⟩, hp⟩
      · exact ⟨⟨h0, hpN⟩, hp⟩
  have hdisj : Disjoint S M := by
    rw [Finset.disjoint_left]
    intro p hpS hpM
    exact (Finset.mem_filter.mp hpM).2 (Nat.dvd_of_mem_primeFactors (Finset.mem_filter.mp hpS).1)
  have hMpr : ∀ p ∈ M, p.Prime := fun p hp => (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have hsplit : (mertensPrimeProduct N)⁻¹ =
      (∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹) * ∏ p ∈ M, (1 - 1 / (p : ℝ))⁻¹ := by
    rw [inv_mertensPrimeProduct_eq, ← hP, hPS, Finset.prod_union hdisj]
  have hMpos : 0 < ∏ p ∈ M, (1 - 1 / (p : ℝ))⁻¹ := Finset.prod_pos fun p hp =>
    lt_of_lt_of_le zero_lt_one (one_le_inv_one_sub_inv (hMpr p hp))
  have hSeq : ∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹ =
      (mertensPrimeProduct N)⁻¹ * ∏ p ∈ M, (1 - 1 / (p : ℝ)) := by
    rw [hsplit, mul_assoc, ← Finset.prod_mul_distrib]
    have : ∏ p ∈ M, (1 - 1 / (p : ℝ))⁻¹ * (1 - 1 / (p : ℝ)) = 1 := by
      refine Finset.prod_eq_one fun p hp => ?_
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hMpr p hp).two_le
      have : 1 - 1 / (p : ℝ) ≠ 0 := by
        have : 1 / (p : ℝ) ≤ 1 / 2 := by gcongr
        linarith
      exact inv_mul_cancel₀ this
    rw [this, mul_one]
  have hexp : ∏ p ∈ M, (1 - 1 / (p : ℝ)) ≤ Real.exp (-∑ p ∈ M, 1 / (p : ℝ)) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_le_prod (fun p hp => ?_) (fun p _ => ?_)
    · have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hMpr p hp).two_le
      have : 1 / (p : ℝ) ≤ 1 / 2 := by gcongr
      linarith
    · have := Real.add_one_le_exp (-(1 / (p : ℝ))); linarith
  have hM0 : 0 ≤ (mertensPrimeProduct N)⁻¹ := inv_nonneg.mpr (mertensPrimeProduct_pos N).le
  have h1 : ∏ p ∈ S, (1 - 1 / (p : ℝ))⁻¹ ≤ (mertensPrimeProduct N)⁻¹ *
      Real.exp (-∑ p ∈ M, 1 / (p : ℝ)) := by
    rw [hSeq]; exact mul_le_mul_of_nonneg_left hexp hM0
  have h2 : ∏ p ∈ n.primeFactors.filter (N < ·), (1 - 1 / (p : ℝ))⁻¹ ≤
      (1 + 1 / (N : ℝ)) ^ (n.primeFactors.filter (N < ·)).card := prod_inv_gt_le hN
  exact mul_le_mul h1 h2 (Finset.prod_nonneg fun p hp =>
    le_trans zero_le_one (one_le_inv_one_sub_inv (hpr p (Finset.mem_filter.mp hp).1)))
    (by positivity)

/-- **Only near-primorials can satisfy Nicolas's inequality.** For every `δ > 0`, eventually every
`n` whose missing primes `p ≤ log n` have harmonic mass `≥ δ` satisfies `n/φ(n) < e^γ log log n`. -/
theorem eventually_div_totient_lt_of_missing {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, δ ≤ ∑ p ∈ ((Finset.Icc 0 ⌊Real.log n⌋₊).filter Nat.Prime).filter
        (fun p => ¬ p ∣ n), 1 / (p : ℝ) →
      (n : ℝ) / (n.totient : ℝ) < Real.exp Real.eulerMascheroniConstant * Real.log (Real.log n) := by
  set E := Real.exp Real.eulerMascheroniConstant with hE
  have hE0 : 0 < E := Real.exp_pos _
  set q := Real.exp (-δ) with hq
  have hq1 : q < 1 := by rw [hq]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hq0 : 0 < q := Real.exp_pos _
  set η := (1 - q) / 4 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  filter_upwards [eventually_sigma_div_le hη0] with n ⟨hn16, hll, hbound⟩ hdef
  have hn0 : n ≠ 0 := by omega
  have hN := two_le_floor_log hn16
  have hσ := div_totient_le_mertens_missing hn0 (by omega : 1 ≤ ⌊Real.log n⌋₊)
  have hexp : Real.exp (-∑ p ∈ ((Finset.Icc 0 ⌊Real.log n⌋₊).filter Nat.Prime).filter
      (fun p => ¬ p ∣ n), 1 / (p : ℝ)) ≤ q := Real.exp_le_exp.mpr (by linarith)
  have hσ' : (n : ℝ) / (n.totient : ℝ) ≤ q * ((1 + η) ^ 2 * E * Real.log (Real.log n)) := by
    refine hσ.trans ?_
    calc (mertensPrimeProduct ⌊Real.log n⌋₊)⁻¹ *
          Real.exp (-∑ p ∈ ((Finset.Icc 0 ⌊Real.log n⌋₊).filter Nat.Prime).filter
            (fun p => ¬ p ∣ n), 1 / (p : ℝ)) *
          (1 + 1 / (⌊Real.log n⌋₊ : ℝ)) ^ (n.primeFactors.filter (⌊Real.log n⌋₊ < ·)).card
        ≤ (mertensPrimeProduct ⌊Real.log n⌋₊)⁻¹ * q *
          (1 + 1 / (⌊Real.log n⌋₊ : ℝ)) ^ (n.primeFactors.filter (⌊Real.log n⌋₊ < ·)).card := by
          have hM0 : 0 ≤ (mertensPrimeProduct ⌊Real.log n⌋₊)⁻¹ :=
            inv_nonneg.mpr (mertensPrimeProduct_pos _).le
          gcongr
      _ = q * ((mertensPrimeProduct ⌊Real.log n⌋₊)⁻¹ *
          (1 + 1 / (⌊Real.log n⌋₊ : ℝ)) ^ (n.primeFactors.filter (⌊Real.log n⌋₊ < ·)).card) := by
          ring
      _ ≤ q * ((1 + η) ^ 2 * E * Real.log (Real.log n)) :=
          mul_le_mul_of_nonneg_left hbound hq0.le
  have hc : q * ((1 + η) ^ 2 * E) < E := by
    have h1 : q * (1 + η) ^ 2 < 1 := by
      have hη1 : η ≤ 1 / 4 := by rw [hη]; linarith
      have e : q * (1 + η) ^ 2 = q + q * η * (2 + η) := by ring
      have h2 : q * η * (2 + η) ≤ η * (9 / 4) := by
        have := mul_le_mul_of_nonneg_left (show 2 + η ≤ 9 / 4 by linarith) hη0.le
        nlinarith
      rw [e]
      have : η * (9 / 4) < 1 - q := by rw [hη]; nlinarith
      linarith
    have := mul_lt_mul_of_pos_right h1 hE0
    nlinarith
  calc (n : ℝ) / (n.totient : ℝ) ≤ q * ((1 + η) ^ 2 * E * Real.log (Real.log n)) := hσ'
    _ = (q * ((1 + η) ^ 2 * E)) * Real.log (Real.log n) := by ring
    _ < E * Real.log (Real.log n) := mul_lt_mul_of_pos_right hc hll

/-- **Landau's theorem, upper half.** For every `ε > 0`, eventually
`n/φ(n) ≤ (e^γ + ε) log log n`. -/
theorem eventually_div_totient_le_landau {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) / (n.totient : ℝ) ≤
      (Real.exp Real.eulerMascheroniConstant + ε) * Real.log (Real.log n) := by
  set E := Real.exp Real.eulerMascheroniConstant with hE
  have hE0 : 0 < E := Real.exp_pos _
  set η := min 1 (ε / (4 * E)) with hη
  have hη0 : 0 < η := lt_min one_pos (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : η ≤ ε / (4 * E) := min_le_right _ _
  filter_upwards [eventually_sigma_div_le hη0] with n ⟨hn16, hll, hbound⟩
  have hn0 : n ≠ 0 := by omega
  have hN := two_le_floor_log hn16
  refine (div_totient_le_mertens_missing hn0 (by omega : 1 ≤ ⌊Real.log n⌋₊)).trans ?_
  have hexp : Real.exp (-∑ p ∈ ((Finset.Icc 0 ⌊Real.log n⌋₊).filter Nat.Prime).filter
      (fun p => ¬ p ∣ n), 1 / (p : ℝ)) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_nonpos]
    exact Finset.sum_nonneg fun p _ => by positivity
  have hc : (1 + η) ^ 2 * E ≤ E + ε := by
    have h1 : (1 + η) ^ 2 ≤ 1 + 3 * η := by nlinarith
    have h2 : E * (3 * η) ≤ 3 * ε / 4 := by
      have := mul_le_mul_of_nonneg_left hηε hE0.le
      rw [show E * (ε / (4 * E)) = ε / 4 by field_simp] at this
      linarith
    nlinarith
  have hM0 : 0 ≤ (mertensPrimeProduct ⌊Real.log n⌋₊)⁻¹ :=
    inv_nonneg.mpr (mertensPrimeProduct_pos _).le
  have hB0 : 0 ≤ (1 + 1 / (⌊Real.log n⌋₊ : ℝ)) ^
      (n.primeFactors.filter (⌊Real.log n⌋₊ < ·)).card := by positivity
  calc (mertensPrimeProduct ⌊Real.log n⌋₊)⁻¹ *
        Real.exp (-∑ p ∈ ((Finset.Icc 0 ⌊Real.log n⌋₊).filter Nat.Prime).filter
          (fun p => ¬ p ∣ n), 1 / (p : ℝ)) *
        (1 + 1 / (⌊Real.log n⌋₊ : ℝ)) ^ (n.primeFactors.filter (⌊Real.log n⌋₊ < ·)).card
      ≤ (mertensPrimeProduct ⌊Real.log n⌋₊)⁻¹ * 1 *
        (1 + 1 / (⌊Real.log n⌋₊ : ℝ)) ^ (n.primeFactors.filter (⌊Real.log n⌋₊ < ·)).card := by
        gcongr
    _ ≤ (1 + η) ^ 2 * E * Real.log (Real.log n) := by rw [mul_one]; exact hbound
    _ ≤ (E + ε) * Real.log (Real.log n) := by gcongr

/-- `σ(n)/n ≤ n/φ(n)`. -/
theorem sigma_div_le_div_totient {n : ℕ} (hn : n ≠ 0) :
    ((sigma 1 n : ℕ) : ℝ) / n ≤ (n : ℝ) / (n.totient : ℝ) := by
  rw [sigma_div_eq_prod hn, div_totient_eq_prod hn]
  exact Finset.prod_le_prod (fun p hp => local_factor_nonneg (Nat.prime_of_mem_primeFactors hp))
    (fun p hp => local_factor_le (Nat.prime_of_mem_primeFactors hp))

/-- `n/φ(n)` at the primorial powers is the inverse Mertens product. -/
theorem div_totient_primorialPow (y m : ℕ) (hm : 1 ≤ m) :
    ((primorialPow y m : ℕ) : ℝ) / ((primorialPow y m).totient : ℝ) =
      (mertensPrimeProduct y)⁻¹ := by
  have hn0 : primorialPow y m ≠ 0 := (primorialPow_pos y m).ne'
  rw [div_totient_eq_prod hn0, inv_mertensPrimeProduct_eq]
  congr 1
  unfold primorialPow
  rw [Finset.prod_pow, Nat.primeFactors_pow _ (by omega),
    Nat.primeFactors_prod fun p hp => (Finset.mem_filter.mp hp).2]

/-- **Landau's theorem, lower half.** For every `ε > 0` there are arbitrarily large `n` with
`n/φ(n) ≥ (e^γ − ε) log log n`; with the upper half, `limsup n/(φ(n) log log n) = e^γ`. -/
theorem frequently_div_totient_ge_landau {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ n : ℕ in atTop, (Real.exp Real.eulerMascheroniConstant - ε) * Real.log (Real.log n) ≤
      (n : ℝ) / (n.totient : ℝ) := by
  have hG := frequently_sigma_ge_gronwall hε
  rw [Filter.frequently_atTop] at hG ⊢
  intro n₀
  obtain ⟨n, hn, hσ⟩ := hG (max n₀ 1)
  refine ⟨n, le_trans (le_max_left _ _) hn, ?_⟩
  have hn0 : n ≠ 0 := by have := le_trans (le_max_right n₀ 1) hn; omega
  have hnr : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  refine le_trans ?_ (sigma_div_le_div_totient hn0)
  rw [le_div_iff₀ hnr]
  linarith

end

end RHTower
