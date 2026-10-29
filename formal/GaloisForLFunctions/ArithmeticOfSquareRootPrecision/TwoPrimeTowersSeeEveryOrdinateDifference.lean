import GaloisForLFunctions.RHTower.Matveev.EffectiveBaker
import GaloisForLFunctions.RHTower.LiouvillePointReachability

/-!
# Two prime towers see every ordinate difference at polynomial precision

The tower of a prime `p` reads an ordinate difference `Δ = γ − γ'` of two zeros through the phase
`Δ log p` modulo `2π`; it is blind to `Δ` exactly when `Δ log p ∈ 2πℤ` (aliasing). Two towers are
blind together only if `Δ = 0`. How *close* can `Δ` come to both aliasing lattices? This is a
question about the precision of linear forms in two prime logarithms, and three precisions occur.

* **Integrality** (`liouville_separation`): `p^a ≠ q^b`, so
  `|a log p − b log q| ≥ 1 / max(p^a, q^b)`, exponentially small in the height.
* **Transcendence** (`exists_baker_separation`, from the corpus's effective Baker theorem):
  `|k₁ log q − k₂ log p| ≥ c (2 + |k₁| + |k₂|)^{−C}`, polynomial in the height.
* **Dirichlet** (`exists_small_two_prime_form`): some `0 < k₁ ≤ n` has
  `|k₁ log q − k₂ log p| ≤ log p / (n + 1)`; polynomial decay is the true shape.

**The two-prime non-aliasing law** (`two_prime_alias_bound`, `two_prime_alias_bound_in_Δ`). Writing
`e_p = Δ log p − 2πk₁`, `e_q = Δ log q − 2πk₂`, one has
`2π (k₁ log q − k₂ log p) = e_q log p − e_p log q`, hence for distinct primes there are `c, C > 0` with

`|e_p| log q + |e_q| log p ≥ c · min(|Δ|, (2 + |Δ|)^{−C})`

for every real `Δ` and all integers `k₁, k₂`. Two towers certify every pair of ordinates of height
`≤ T` with margin polynomial in `T`; integrality alone gives only `e^{−O(T)}`.
-/

noncomputable section

open Real

namespace GaloisForLFunctions.ArithmeticOfSquareRootPrecision

variable {p q : ℕ}

/-- `p^a ≠ q^b` for distinct primes unless `a = b = 0`. -/
theorem pow_ne_pow_of_prime_ne (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {a b : ℕ}
    (hab : a ≠ 0 ∨ b ≠ 0) : p ^ a ≠ q ^ b := by
  intro h
  rcases hab with ha | hb
  · have hd : p ∣ q ^ b := h ▸ dvd_pow_self p ha
    exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp (hp.dvd_of_dvd_pow hd))
  · have hd : q ∣ p ^ a := h.symm ▸ dvd_pow_self q hb
    exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).mp (hq.dvd_of_dvd_pow hd)).symm

/-- **Liouville separation**: `|a log p − b log q| ≥ 1 / max(p^a, q^b)` for distinct primes and
`(a, b) ≠ (0, 0)`. Integrality gives a separation exponentially small in the height. -/
theorem liouville_separation (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {a b : ℕ}
    (hab : a ≠ 0 ∨ b ≠ 0) :
    1 / (max ((p ^ a : ℕ) : ℝ) ((q ^ b : ℕ) : ℝ)) ≤ |(a : ℝ) * Real.log p - b * Real.log q| := by
  have hne := pow_ne_pow_of_prime_ne hp hq hpq hab
  have hA : (0 : ℝ) < (p ^ a : ℕ) := by exact_mod_cast pow_pos hp.pos a
  have hB : (0 : ℝ) < (q ^ b : ℕ) := by exact_mod_cast pow_pos hq.pos b
  have hla : (a : ℝ) * Real.log p = Real.log ((p ^ a : ℕ) : ℝ) := by push_cast; rw [Real.log_pow]
  have hlb : (b : ℝ) * Real.log q = Real.log ((q ^ b : ℕ) : ℝ) := by push_cast; rw [Real.log_pow]
  rw [hla, hlb]
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have hsep := RHTower.log_sep_of_int_lt hA (by exact_mod_cast hlt : ((p ^ a : ℕ) : ℝ) + 1 ≤ (q ^ b : ℕ))
    rw [max_eq_right (by exact_mod_cast hlt.le), abs_sub_comm]
    exact hsep.trans (le_abs_self _)
  · have hsep := RHTower.log_sep_of_int_lt hB (by exact_mod_cast hlt : ((q ^ b : ℕ) : ℝ) + 1 ≤ (p ^ a : ℕ))
    rw [max_eq_left (by exact_mod_cast hlt.le)]
    exact hsep.trans (le_abs_self _)

/-- **Baker separation** for two primes: `|k₁ log q − k₂ log p| ≥ c (2 + |k₁| + |k₂|)^{−C}` for
`(k₁, k₂) ≠ (0, 0)`. -/
theorem exists_baker_separation (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ k₁ k₂ : ℤ, (k₁ ≠ 0 ∨ k₂ ≠ 0) →
      c * (2 + (|(k₁ : ℝ)| + |(k₂ : ℝ)|)) ^ (-C) ≤ |(k₁ : ℝ) * Real.log q - k₂ * Real.log p| := by
  have hinj : Function.Injective ![q, p] := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  have hpr : ∀ i, (![q, p] i).Prime := by intro i; fin_cases i <;> simpa
  obtain ⟨c, C, hc, hC, hbound⟩ := RHTower.Matveev.effectiveBakerBound_holds ![q, p] hinj hpr
  refine ⟨c, C, hc, hC, fun k₁ k₂ hk => ?_⟩
  have hν : (![k₁, -k₂] : Fin 2 → ℤ) ≠ 0 := by
    intro h0
    rcases hk with h1 | h2
    · exact h1 (by simpa using congrFun h0 0)
    · exact h2 (by simpa using congrFun h0 1)
  have h := hbound ![k₁, -k₂] hν
  have hform : RHTower.Matveev.primeLogForm ![q, p] ![k₁, -k₂] =
      (k₁ : ℝ) * Real.log q - k₂ * Real.log p := by
    simp [RHTower.Matveev.primeLogForm, Fin.sum_univ_two]; ring
  have hheight : (RHTower.Matveev.coeffHeight ![k₁, -k₂] : ℝ) = |(k₁ : ℝ)| + |(k₂ : ℝ)| := by
    simp [RHTower.Matveev.coeffHeight, Fin.sum_univ_two, Nat.cast_natAbs]
  rw [hform, hheight] at h
  exact h

/-- **Dirichlet**: polynomial decay is attained. For every `n ≥ 1` some `0 < k₁ ≤ n` has
`|k₁ log q − k₂ log p| ≤ log p / (n + 1)`. -/
theorem exists_small_two_prime_form (hp : 1 < p) {n : ℕ} (hn : 0 < n) :
    ∃ k₁ k₂ : ℤ, 0 < k₁ ∧ k₁ ≤ n ∧
      |(k₁ : ℝ) * Real.log q - k₂ * Real.log p| ≤ Real.log p / (n + 1) := by
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp)
  obtain ⟨j, k, hk0, hkn, hjk⟩ := Real.exists_int_int_abs_mul_sub_le (Real.log q / Real.log p) hn
  refine ⟨k, j, hk0, hkn, ?_⟩
  have he : (k : ℝ) * Real.log q - j * Real.log p =
      ((k : ℝ) * (Real.log q / Real.log p) - j) * Real.log p := by field_simp
  rw [he, abs_mul, abs_of_pos hlp, div_eq_mul_inv (Real.log p), mul_comm (Real.log p)]
  exact mul_le_mul_of_nonneg_right (by simpa [one_div] using hjk) hlp.le

/-- The elimination identity `2π (k₁ log q − k₂ log p) = e_q log p − e_p log q`. -/
theorem two_pi_mul_form_eq (Δ : ℝ) (k₁ k₂ : ℤ) :
    2 * π * ((k₁ : ℝ) * Real.log q - k₂ * Real.log p) =
      (Δ * Real.log q - 2 * π * k₂) * Real.log p - (Δ * Real.log p - 2 * π * k₁) * Real.log q := by
  ring

/-- **The two-prime non-aliasing law**, for given aliasing integers. -/
theorem two_prime_alias_bound (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (Δ : ℝ) (k₁ k₂ : ℤ), (k₁ ≠ 0 ∨ k₂ ≠ 0) →
      2 * π * c * (2 + (|(k₁ : ℝ)| + |(k₂ : ℝ)|)) ^ (-C) ≤
        |Δ * Real.log p - 2 * π * k₁| * Real.log q + |Δ * Real.log q - 2 * π * k₂| * Real.log p := by
  obtain ⟨c, C, hc, hC, hsep⟩ := exists_baker_separation hp hq hpq
  refine ⟨c, C, hc, hC, fun Δ k₁ k₂ hk => ?_⟩
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  have h1 := hsep k₁ k₂ hk
  have h2 : 2 * π * |(k₁ : ℝ) * Real.log q - k₂ * Real.log p| ≤
      |Δ * Real.log p - 2 * π * k₁| * Real.log q + |Δ * Real.log q - 2 * π * k₂| * Real.log p := by
    have := abs_sub (( Δ * Real.log q - 2 * π * k₂) * Real.log p)
      ((Δ * Real.log p - 2 * π * k₁) * Real.log q)
    rw [← two_pi_mul_form_eq Δ k₁ k₂, abs_mul, abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 2 * π),
      abs_of_pos hlp, abs_of_pos hlq] at this
    linarith
  calc 2 * π * c * (2 + (|(k₁ : ℝ)| + |(k₂ : ℝ)|)) ^ (-C)
      = 2 * π * (c * (2 + (|(k₁ : ℝ)| + |(k₂ : ℝ)|)) ^ (-C)) := by ring
    _ ≤ 2 * π * |(k₁ : ℝ) * Real.log q - k₂ * Real.log p| :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ _ := h2

/-- **Two towers see every ordinate difference at polynomial precision.** For distinct primes there
are `c, C > 0` such that for every real `Δ` and all integers `k₁, k₂`,
`|Δ log p − 2πk₁| log q + |Δ log q − 2πk₂| log p ≥ c · min(|Δ|, (2 + |Δ|)^{−C})`. -/
theorem two_prime_alias_bound_in_Δ (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (Δ : ℝ) (k₁ k₂ : ℤ),
      c * min |Δ| ((2 + |Δ|) ^ (-C)) ≤
        |Δ * Real.log p - 2 * π * k₁| * Real.log q + |Δ * Real.log q - 2 * π * k₂| * Real.log p := by
  obtain ⟨c₀, C, hc₀, hC, hbound⟩ := two_prime_alias_bound hp hq hpq
  have hlp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq.one_lt)
  have hl2p : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num) (by exact_mod_cast hp.two_le)
  have hl2q : Real.log 2 ≤ Real.log q := Real.log_le_log (by norm_num) (by exact_mod_cast hq.two_le)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set L := 2 + Real.log p + Real.log q with hL
  have hL1 : 1 ≤ L := by rw [hL]; linarith
  set c := min (Real.log 2 * Real.log 2) (min (2 * π * c₀ * L ^ (-C)) (Real.log 2)) with hcdef
  have hcpos : 0 < c := lt_min (by positivity) (lt_min (by positivity) hl2)
  refine ⟨c, C, hcpos, hC, fun Δ k₁ k₂ => ?_⟩
  set D := |Δ * Real.log p - 2 * π * k₁| * Real.log q + |Δ * Real.log q - 2 * π * k₂| * Real.log p
  have hD0 : 0 ≤ D := by positivity
  have hpow1 : (2 + |Δ|) ^ (-C) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg Δ]) (by linarith)
  have hmin_le : min |Δ| ((2 + |Δ|) ^ (-C)) ≤ (2 + |Δ|) ^ (-C) := min_le_right _ _
  have hmin_nonneg : 0 ≤ min |Δ| ((2 + |Δ|) ^ (-C)) :=
    le_min (abs_nonneg Δ) (Real.rpow_nonneg (by positivity) _)
  by_cases h0 : k₁ = 0 ∧ k₂ = 0
  · -- no aliasing integers: the defect is `2 |Δ| log p log q`
    obtain ⟨rfl, rfl⟩ := h0
    have hD : D = 2 * (|Δ| * Real.log p * Real.log q) := by
      simp only [D, Int.cast_zero, mul_zero, sub_zero, abs_mul, abs_of_pos hlp, abs_of_pos hlq]
      ring
    have hc1 : c ≤ Real.log 2 * Real.log 2 := min_le_left _ _
    have : c * min |Δ| ((2 + |Δ|) ^ (-C)) ≤ Real.log 2 * Real.log 2 * |Δ| :=
      mul_le_mul hc1 (min_le_left _ _) hmin_nonneg (by positivity)
    rw [hD]
    nlinarith [abs_nonneg Δ, mul_le_mul hl2p hl2q hl2.le hlp.le]
  · have hk : k₁ ≠ 0 ∨ k₂ ≠ 0 := by tauto
    by_cases hsmall : |(k₁ : ℝ)| ≤ |Δ| * Real.log p + 1 ∧ |(k₂ : ℝ)| ≤ |Δ| * Real.log q + 1
    · -- bounded heights: Baker
      have hb := hbound Δ k₁ k₂ hk
      have hheight : 2 + (|(k₁ : ℝ)| + |(k₂ : ℝ)|) ≤ L * (2 + |Δ|) := by
        rw [hL]; nlinarith [abs_nonneg Δ, hsmall.1, hsmall.2]
      have hpos : 0 < 2 + (|(k₁ : ℝ)| + |(k₂ : ℝ)|) := by positivity
      have hmono : (L * (2 + |Δ|)) ^ (-C) ≤ (2 + (|(k₁ : ℝ)| + |(k₂ : ℝ)|)) ^ (-C) :=
        Real.rpow_le_rpow_of_nonpos hpos hheight (by linarith)
      rw [Real.mul_rpow (by linarith) (by positivity)] at hmono
      have hc2 : c ≤ 2 * π * c₀ * L ^ (-C) := (min_le_right _ _).trans (min_le_left _ _)
      calc c * min |Δ| ((2 + |Δ|) ^ (-C)) ≤ 2 * π * c₀ * L ^ (-C) * (2 + |Δ|) ^ (-C) :=
            mul_le_mul hc2 hmin_le hmin_nonneg (by positivity)
        _ = 2 * π * c₀ * (L ^ (-C) * (2 + |Δ|) ^ (-C)) := by ring
        _ ≤ 2 * π * c₀ * (2 + (|(k₁ : ℝ)| + |(k₂ : ℝ)|)) ^ (-C) :=
            mul_le_mul_of_nonneg_left hmono (by positivity)
        _ ≤ D := hb
    · -- a large aliasing integer: one phase defect is at least `1`
      have hc3 : c ≤ Real.log 2 := (min_le_right _ _).trans (min_le_right _ _)
      have hbig : Real.log 2 ≤ D := by
        rcases not_and_or.mp hsmall with h1 | h2
        · have h1' : |Δ| * Real.log p + 1 < |(k₁ : ℝ)| := not_le.mp h1
          have he : 1 ≤ |Δ * Real.log p - 2 * π * k₁| := by
            have := abs_sub_abs_le_abs_sub (2 * π * (k₁ : ℝ)) (Δ * Real.log p)
            rw [abs_mul (2 * π), abs_of_pos (by positivity : 0 < 2 * π), abs_mul, abs_of_pos hlp,
              abs_sub_comm] at this
            nlinarith [Real.pi_gt_three, abs_nonneg (k₁ : ℝ)]
          have := mul_le_mul he hl2q hl2.le (abs_nonneg _)
          nlinarith [abs_nonneg (Δ * Real.log q - 2 * π * k₂)]
        · have h2' : |Δ| * Real.log q + 1 < |(k₂ : ℝ)| := not_le.mp h2
          have he : 1 ≤ |Δ * Real.log q - 2 * π * k₂| := by
            have := abs_sub_abs_le_abs_sub (2 * π * (k₂ : ℝ)) (Δ * Real.log q)
            rw [abs_mul (2 * π), abs_of_pos (by positivity : 0 < 2 * π), abs_mul, abs_of_pos hlq,
              abs_sub_comm] at this
            nlinarith [Real.pi_gt_three, abs_nonneg (k₂ : ℝ)]
          have := mul_le_mul he hl2p hl2.le (abs_nonneg _)
          nlinarith [abs_nonneg (Δ * Real.log p - 2 * π * k₁)]
      calc c * min |Δ| ((2 + |Δ|) ^ (-C)) ≤ Real.log 2 * 1 :=
            mul_le_mul hc3 (hmin_le.trans hpow1) hmin_nonneg hl2.le
        _ ≤ D := by linarith

end GaloisForLFunctions.ArithmeticOfSquareRootPrecision
