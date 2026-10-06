import GaloisForLFunctions.RHTower.Sieve.TwistedSelbergGcdLogForms
import GaloisForLFunctions.RHTower.Sieve.LinearMollifierGcdForms
import GaloisForLFunctions.RHTower.FareySawtoothMeanSquare

/-!
# Twisted gcd forms of the linear mollifier

For coprime `a, b ≥ 1` and the linear mollifier `b(h) = μ(h) log(N/h)/log N`,

`S₀(a,b) = Σ_{h,k ≤ N} b(h)b(k)(ha,kb)/(hk)`,
`S₁(a,b) = Σ_{h,k ≤ N} b(h)b(k)(ha,kb)/(hk) · log((ha,kb)²/(hk))`.

* **Radical reduction** (`gcd_mul_eq_gcd_mul_radical`): for squarefree `m, n`,
  `(ma, nb) = (m·rad a, n·rad b)`, so the twisted Selberg coefficients depend on `a, b` only
  through their radicals.
* **Splitting** (`twistForm₀_mul_log_sq`, `twistForm₁_mul_log_sq`): with `L = log N`,
  `L² S₀ = Q(1,1)` and `L² S₁ = 2G(1,1) + Q(2,1) + Q(1,2) − 2L Q(1,1)`.
* **Cancellation** (`tendsto_twistForm₀_mul_log`, `tendsto_twistForm₁`): if `(a, b) ≠ (1, 1)`,
  `S₀ log N → 0` and `S₁ → 0`.
* **Envelopes** (`exists_twistForm_envelope`): `|S₀| log N ≤ M K(a,b)` and
  `|S₁| ≤ M (1 + log ab) K(a,b)` for all coprime `a, b`, with
  `K(a,b) = d(ab) d(a) d(b) 2^{ω(a)+ω(b)}`.
* **The gcd sum** (`sum_gcd_mul_div_le`):
  `Σ_{h,k ≤ N} (ha,kb)/(hk) ≤ d(ab)(1 + log N)²(1 + log(Nab))` (Gauss's identity
  `(x,y) = Σ_{f | x, f | y} φ(f)`, and `f | ha ⟺ f/(f,a) | h`).
-/

open ArithmeticFunction Finset Filter Topology UniqueFactorizationMonoid
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section

/-! ## Radical reduction -/

theorem factorization_radical_eq (n p : ℕ) :
    (radical n).factorization p = if p ∈ n.primeFactors then 1 else 0 := by
  have hle := (squarefree_radical (a := n)).natFactorization_le_one p
  have hmem : p ∈ (radical n).primeFactors ↔ p ∈ n.primeFactors := by
    rw [Nat.primeFactors_radical]
  rw [← Nat.support_factorization, Finsupp.mem_support_iff] at hmem
  split_ifs with h
  · have := hmem.mpr h
    omega
  · by_contra h'
    exact h (hmem.mp h')

theorem factorization_ne_zero_iff_mem_primeFactors (n p : ℕ) :
    n.factorization p ≠ 0 ↔ p ∈ n.primeFactors := by
  rw [← Nat.support_factorization, Finsupp.mem_support_iff]

/-- **Radical reduction of the twisted gcd.** For squarefree `m, n` and coprime `a, b`,
`(ma, nb) = (m·rad a, n·rad b)`. -/
theorem gcd_mul_eq_gcd_mul_radical {a b m n : ℕ} (hab : Nat.Coprime a b) (ha : a ≠ 0)
    (hb : b ≠ 0) (hm : Squarefree m) (hn : Squarefree n) :
    Nat.gcd (m * a) (n * b) = Nat.gcd (m * radical a) (n * radical b) := by
  have hm0 : m ≠ 0 := hm.ne_zero
  have hn0 : n ≠ 0 := hn.ne_zero
  have hra : radical a ≠ 0 := radical_ne_zero
  have hrb : radical b ≠ 0 := radical_ne_zero
  apply Nat.eq_of_factorization_eq (Nat.gcd_pos_of_pos_left _ (by positivity)).ne'
    (Nat.gcd_pos_of_pos_left _ (by positivity)).ne'
  intro p
  rw [Nat.factorization_gcd (by positivity) (by positivity),
    Nat.factorization_gcd (by positivity) (by positivity), Finsupp.inf_apply, Finsupp.inf_apply,
    Nat.factorization_mul hm0 ha, Nat.factorization_mul hn0 hb, Nat.factorization_mul hm0 hra,
    Nat.factorization_mul hn0 hrb, Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply,
    Finsupp.add_apply, factorization_radical_eq, factorization_radical_eq]
  have h1 := hm.natFactorization_le_one p
  have h2 := hn.natFactorization_le_one p
  have hcop : min (a.factorization p) (b.factorization p) = 0 := by
    have := congrArg (fun f => f p) (Nat.factorization_gcd ha hb)
    simp only [hab.gcd_eq_one, Nat.factorization_one, Finsupp.coe_zero, Pi.zero_apply,
      Finsupp.inf_apply] at this
    exact this.symm
  have hpa := factorization_ne_zero_iff_mem_primeFactors a p
  have hpb := factorization_ne_zero_iff_mem_primeFactors b p
  split_ifs with h3 h4 h4
  · exact absurd hcop (by have := hpa.mpr h3; have := hpb.mpr h4; show min _ _ ≠ 0; omega)
  · have : b.factorization p = 0 := by by_contra h; exact h4 (hpb.mp h)
    have := hpa.mpr h3
    show min _ _ = min _ _
    omega
  · have : a.factorization p = 0 := by by_contra h; exact h3 (hpa.mp h)
    have := hpb.mpr h4
    show min _ _ = min _ _
    omega
  · have : a.factorization p = 0 := by by_contra h; exact h3 (hpa.mp h)
    have : b.factorization p = 0 := by by_contra h; exact h4 (hpb.mp h)
    show min _ _ = min _ _
    omega

theorem twistedOriginalCoeff_radical {a b : ℕ} (hab : Nat.Coprime a b) (ha : a ≠ 0) (hb : b ≠ 0)
    (m n : ℕ) : twistedOriginalCoeff a b m n = twistedOriginalCoeff (radical a) (radical b) m n := by
  unfold twistedOriginalCoeff
  by_cases hm : Squarefree m
  · by_cases hn : Squarefree n
    · rw [gcd_mul_eq_gcd_mul_radical hab ha hb hm hn]
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]
      simp
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hm]
    simp

theorem twistedGcdLogCoeff_radical {a b : ℕ} (hab : Nat.Coprime a b) (ha : a ≠ 0) (hb : b ≠ 0)
    (m n : ℕ) : twistedGcdLogCoeff a b m n = twistedGcdLogCoeff (radical a) (radical b) m n := by
  unfold twistedGcdLogCoeff
  rw [twistedOriginalCoeff_radical hab ha hb]
  by_cases hm : Squarefree m
  · by_cases hn : Squarefree n
    · rw [gcd_mul_eq_gcd_mul_radical hab ha hb hm hn]
    · unfold twistedOriginalCoeff
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]
      simp
  · unfold twistedOriginalCoeff
    rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hm]
    simp

theorem twistedLogMonomial_radical {a b : ℕ} (hab : Nat.Coprime a b) (ha : a ≠ 0) (hb : b ≠ 0)
    (i j N : ℕ) :
    twistedLogMonomial a b i j N = twistedLogMonomial (radical a) (radical b) i j N := by
  unfold twistedLogMonomial
  simp_rw [twistedOriginalCoeff_radical hab ha hb]

theorem twistedGcdLogMonomial_radical {a b : ℕ} (hab : Nat.Coprime a b) (ha : a ≠ 0)
    (hb : b ≠ 0) (i j N : ℕ) :
    twistedGcdLogMonomial a b i j N = twistedGcdLogMonomial (radical a) (radical b) i j N := by
  unfold twistedGcdLogMonomial
  simp_rw [twistedGcdLogCoeff_radical hab ha hb]

theorem coprime_radical {a b : ℕ} (hab : Nat.Coprime a b) : Nat.Coprime (radical a) (radical b) :=
  Nat.Coprime.coprime_dvd_left radical_dvd_self (Nat.Coprime.coprime_dvd_right radical_dvd_self hab)

theorem radical_ne_one_or {a b : ℕ} (hab1 : 1 < a ∨ 1 < b) : radical a ≠ 1 ∨ radical b ≠ 1 := by
  rcases hab1 with h | h
  · left; rw [Ne, Nat.radical_eq_one_iff]; omega
  · right; rw [Ne, Nat.radical_eq_one_iff]; omega

/-- The arithmetic size `K(a,b) = d(ab) d(b) d(a) 2^{ω(b)} 2^{ω(a)}` of the twisted envelopes. -/
def twistSize (a b : ℕ) : ℝ :=
  ((a * b).divisors.card : ℝ) * ((b.divisors.card : ℝ) * a.divisors.card) *
    ((2 : ℝ) ^ b.primeFactors.card * 2 ^ a.primeFactors.card)

theorem twistSize_nonneg (a b : ℕ) : 0 ≤ twistSize a b := by unfold twistSize; positivity

theorem card_divisors_radical_le {n : ℕ} (hn : n ≠ 0) :
    ((radical n).divisors.card : ℝ) ≤ n.divisors.card := by
  exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hn radical_dvd_self)

theorem twistSize_radical_le {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    twistSize (radical a) (radical b) ≤ twistSize a b := by
  unfold twistSize
  rw [Nat.primeFactors_radical, Nat.primeFactors_radical]
  have hab : a * b ≠ 0 := Nat.mul_ne_zero ha hb
  have h1 : (((radical a) * (radical b)).divisors.card : ℝ) ≤ (a * b).divisors.card := by
    exact_mod_cast Finset.card_le_card (Nat.divisors_subset_of_dvd hab
      (Nat.mul_dvd_mul radical_dvd_self radical_dvd_self))
  have h2 := card_divisors_radical_le hb
  have h3 := card_divisors_radical_le ha
  have h4 : (0 : ℝ) ≤ ((radical b).divisors.card : ℝ) * (radical a).divisors.card := by positivity
  have h5 : (0 : ℝ) ≤ (2 : ℝ) ^ b.primeFactors.card * 2 ^ a.primeFactors.card := by positivity
  have h6 : (0 : ℝ) ≤ ((radical a * radical b).divisors.card : ℝ) := by positivity
  exact mul_le_mul_of_nonneg_right (mul_le_mul h1 (mul_le_mul h2 h3 (by positivity)
    (by positivity)) h4 (by positivity)) h5

theorem log_radical_mul_le {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Real.log ((radical a * radical b : ℕ) : ℝ) ≤ Real.log ((a * b : ℕ) : ℝ) := by
  have hr : 0 < radical a * radical b := Nat.mul_pos (Nat.radical_pos a) (Nat.radical_pos b)
  have hle : radical a * radical b ≤ a * b := Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Nat.mul_ne_zero ha hb)) (Nat.mul_dvd_mul radical_dvd_self radical_dvd_self)
  exact Real.log_le_log (by exact_mod_cast hr) (by exact_mod_cast hle)

/-! ## The twisted mollifier forms -/

/-- `S₀(a,b) = Σ_{h,k ≤ N} b(h)b(k)(ha,kb)/(hk)`. -/
def twistForm₀ (N a b : ℕ) : ℝ :=
  ∑ h ∈ Icc 1 N, ∑ k ∈ Icc 1 N,
    linearMollifierCoeff N h * linearMollifierCoeff N k * ((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) /
      ((h : ℝ) * (k : ℝ))

/-- `S₁(a,b) = Σ_{h,k ≤ N} b(h)b(k)(ha,kb)/(hk) · log((ha,kb)²/(hk))`. -/
def twistForm₁ (N a b : ℕ) : ℝ :=
  ∑ h ∈ Icc 1 N, ∑ k ∈ Icc 1 N,
    linearMollifierCoeff N h * linearMollifierCoeff N k * ((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) /
      ((h : ℝ) * (k : ℝ)) *
        Real.log (((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) ^ 2 / ((h : ℝ) * (k : ℝ)))

theorem twistForm_term_eq {N a b h k : ℕ} :
    linearMollifierCoeff N h * linearMollifierCoeff N k * ((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) /
      ((h : ℝ) * (k : ℝ)) =
    twistedOriginalCoeff a b h k * (Real.log ((N : ℝ) / (h : ℝ)) * Real.log ((N : ℝ) / (k : ℝ))) /
      Real.log N ^ 2 := by
  unfold linearMollifierCoeff twistedOriginalCoeff
  rcases eq_or_ne (Real.log N) 0 with hL | hL
  · simp [hL]
  rcases eq_or_ne (h : ℝ) 0 with hh | hh
  · simp [hh]
  rcases eq_or_ne (k : ℝ) 0 with hk | hk
  · simp [hk]
  field_simp

/-- `L² S₀ = Q(1,1)`. -/
theorem twistForm₀_mul_log_sq {N : ℕ} (hN : 2 ≤ N) (a b : ℕ) :
    twistForm₀ N a b * Real.log N ^ 2 = twistedLogMonomial a b 1 1 N := by
  have hL : Real.log N ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  rw [twistedLogMonomial, twistForm₀, Finset.sum_mul]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [twistForm_term_eq]
  field_simp

/-- `log((ha,kb)²/(hk)) = 2 log(ha,kb) + log(N/h) + log(N/k) − 2 log N`. -/
theorem log_twistGcd_sq_div_eq {N a b h k : ℕ} (hN : 0 < N) (ha : 0 < a) (hh : 0 < h)
    (hk : 0 < k) :
    Real.log (((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) ^ 2 / ((h : ℝ) * (k : ℝ))) =
      2 * Real.log ((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) + Real.log ((N : ℝ) / (h : ℝ)) +
        Real.log ((N : ℝ) / (k : ℝ)) - 2 * Real.log N := by
  have hg : (0 : ℝ) < ((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) := by
    exact_mod_cast Nat.gcd_pos_of_pos_left _ (Nat.mul_pos hh ha)
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.log_div (by positivity) (by positivity), Real.log_pow, Real.log_mul hhR.ne' hkR.ne',
    Real.log_div hNR.ne' hhR.ne', Real.log_div hNR.ne' hkR.ne']
  push_cast
  ring

/-- `L² S₁ = 2G(1,1) + Q(2,1) + Q(1,2) − 2L Q(1,1)`. -/
theorem twistForm₁_mul_log_sq {N a b : ℕ} (hN : 2 ≤ N) (ha : 0 < a) :
    twistForm₁ N a b * Real.log N ^ 2 =
      2 * twistedGcdLogMonomial a b 1 1 N + twistedLogMonomial a b 2 1 N +
        twistedLogMonomial a b 1 2 N - 2 * Real.log N * twistedLogMonomial a b 1 1 N := by
  have hL : Real.log N ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  rw [twistedLogMonomial, twistedLogMonomial, twistedLogMonomial, twistedGcdLogMonomial,
    twistForm₁, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun h hh => ?_
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hh0 : 0 < h := (Finset.mem_Icc.mp hh).1
  have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
  rw [twistForm_term_eq, log_twistGcd_sq_div_eq (N := N) (by omega) ha hh0 hk0, twistedGcdLogCoeff,
    show ∀ x y : ℝ, x / Real.log N ^ 2 * y * Real.log N ^ 2 = x * y from fun x y => by
      field_simp]
  ring

/-! ## Cancellation and envelopes -/

/-- **`S₀(a,b) log N → 0`** for coprime `(a, b) ≠ (1, 1)`. -/
theorem tendsto_twistForm₀_mul_log {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    (hab1 : 1 < a ∨ 1 < b) :
    Tendsto (fun N : ℕ => twistForm₀ N a b * Real.log N) atTop (𝓝 0) := by
  have h := tendsto_twistedLogMonomial_div (coprime_radical hab) squarefree_radical
    squarefree_radical (radical_ne_one_or hab1) 0 0
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hL : Real.log N ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  rw [← twistedLogMonomial_radical hab ha.ne' hb.ne', ← twistForm₀_mul_log_sq hN]
  field_simp
  ring

/-- **`S₁(a,b) → 0`** for coprime `(a, b) ≠ (1, 1)`. -/
theorem tendsto_twistForm₁ {a b : ℕ} (hab : Nat.Coprime a b) (ha : 0 < a) (hb : 0 < b)
    (hab1 : 1 < a ∨ 1 < b) :
    Tendsto (fun N : ℕ => twistForm₁ N a b) atTop (𝓝 0) := by
  have hr := coprime_radical hab
  have hr1 := radical_ne_one_or hab1
  have hG := tendsto_twistedGcdLogMonomial_div hr squarefree_radical squarefree_radical hr1 0 0
  have h21 := tendsto_twistedLogMonomial_div hr squarefree_radical squarefree_radical hr1 1 0
  have h12 := tendsto_twistedLogMonomial_div hr squarefree_radical squarefree_radical hr1 0 1
  have h11 := tendsto_twistedLogMonomial_div hr squarefree_radical squarefree_radical hr1 0 0
  have hsum := (((hG.const_mul 2).add h21).add h12).sub (h11.const_mul 2)
  simp only [mul_zero, add_zero, sub_zero] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N hN
  have hL : Real.log N ≠ 0 := (Real.log_pos (by exact_mod_cast hN)).ne'
  have hm := twistForm₁_mul_log_sq (a := a) (b := b) hN ha
  rw [twistedGcdLogMonomial_radical hab ha.ne' hb.ne', twistedLogMonomial_radical hab ha.ne' hb.ne',
    twistedLogMonomial_radical hab ha.ne' hb.ne', twistedLogMonomial_radical hab ha.ne' hb.ne']
    at hm
  rw [show twistForm₁ N a b = (twistForm₁ N a b * Real.log N ^ 2) / Real.log N ^ 2 by
    field_simp, hm]
  field_simp
  ring

/-- **Uniform envelopes** of the twisted mollifier forms. -/
theorem exists_twistForm_envelope :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ N : ℕ in atTop, ∀ a b : ℕ, Nat.Coprime a b → 0 < a → 0 < b →
      |twistForm₀ N a b| * Real.log N ≤ M * twistSize a b ∧
        |twistForm₁ N a b| ≤ M * ((1 + Real.log ((a * b : ℕ) : ℝ)) * twistSize a b) := by
  obtain ⟨M₁₁, hM₁₁, h₁₁⟩ := exists_abs_twistedLogMonomial_le 0 0
  obtain ⟨M₂₁, hM₂₁, h₂₁⟩ := exists_abs_twistedLogMonomial_le 1 0
  obtain ⟨M₁₂, hM₁₂, h₁₂⟩ := exists_abs_twistedLogMonomial_le 0 1
  obtain ⟨MG, hMG, hG⟩ := exists_abs_twistedGcdLogMonomial_le 0 0
  refine ⟨M₁₁ + M₂₁ + M₁₂ + 2 * MG + 2 * M₁₁, by positivity, ?_⟩
  filter_upwards [h₁₁, h₂₁, h₁₂, hG, eventually_ge_atTop 3] with N e₁₁ e₂₁ e₁₂ eG hN a b hab ha hb
  have hL1 : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
    exact (Real.exp_one_lt_d9.trans (by norm_num : (2.7182818286 : ℝ) < 3)).le.trans h3
  have hL0 : 0 < Real.log N := by linarith
  have hr := coprime_radical hab
  have hK := twistSize_radical_le ha.ne' hb.ne'
  have hK0 := twistSize_nonneg (radical a) (radical b)
  have hℓ := log_radical_mul_le ha.ne' hb.ne'
  have hr1 : 1 ≤ radical a * radical b :=
    Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero radical_ne_zero radical_ne_zero)
  have hℓ0 : 0 ≤ Real.log ((radical a * radical b : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hr1)
  have q₁₁ := e₁₁ _ _ hr squarefree_radical squarefree_radical
  have q₂₁ := e₂₁ _ _ hr squarefree_radical squarefree_radical
  have q₁₂ := e₁₂ _ _ hr squarefree_radical squarefree_radical
  have g₁₁ := eG _ _ hr squarefree_radical squarefree_radical
  rw [← twistedLogMonomial_radical hab ha.ne' hb.ne'] at q₁₁ q₂₁ q₁₂
  rw [← twistedGcdLogMonomial_radical hab ha.ne' hb.ne'] at g₁₁
  change |twistedLogMonomial a b 1 1 N| ≤ M₁₁ * twistSize (radical a) (radical b) *
    Real.log N ^ 1 at q₁₁
  change |twistedLogMonomial a b 2 1 N| ≤ M₂₁ * twistSize (radical a) (radical b) *
    Real.log N ^ 2 at q₂₁
  change |twistedLogMonomial a b 1 2 N| ≤ M₁₂ * twistSize (radical a) (radical b) *
    Real.log N ^ 2 at q₁₂
  change |twistedGcdLogMonomial a b 1 1 N| ≤ MG * ((1 + Real.log ((radical a * radical b : ℕ) : ℝ))
    * twistSize (radical a) (radical b)) * Real.log N ^ 2 at g₁₁
  have hN2 : 2 ≤ N := by omega
  have hS₀ : |twistForm₀ N a b| * Real.log N = |twistedLogMonomial a b 1 1 N| / Real.log N := by
    rw [← twistForm₀_mul_log_sq hN2, abs_mul, abs_of_pos (pow_pos hL0 2)]
    field_simp
  have hS₁ : |twistForm₁ N a b| = |2 * twistedGcdLogMonomial a b 1 1 N +
      twistedLogMonomial a b 2 1 N + twistedLogMonomial a b 1 2 N -
        2 * Real.log N * twistedLogMonomial a b 1 1 N| / Real.log N ^ 2 := by
    rw [← twistForm₁_mul_log_sq hN2 ha, abs_mul, abs_of_pos (pow_pos hL0 2)]
    field_simp
  have hM : 0 ≤ M₁₁ + M₂₁ + M₁₂ + 2 * MG + 2 * M₁₁ := by positivity
  constructor
  · rw [hS₀, div_le_iff₀ hL0]
    calc |twistedLogMonomial a b 1 1 N| ≤ M₁₁ * twistSize (radical a) (radical b) *
          Real.log N ^ 1 := q₁₁
      _ ≤ (M₁₁ + M₂₁ + M₁₂ + 2 * MG + 2 * M₁₁) * twistSize a b * Real.log N := by
          rw [pow_one]
          gcongr
          linarith
  · rw [hS₁, div_le_iff₀ (pow_pos hL0 2)]
    have hab1 : (1 : ℝ) ≤ 1 + Real.log ((a * b : ℕ) : ℝ) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ ((a * b : ℕ) : ℝ) by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero ha.ne' hb.ne'))
      linarith
    have hK' : 0 ≤ twistSize a b := twistSize_nonneg a b
    calc |2 * twistedGcdLogMonomial a b 1 1 N + twistedLogMonomial a b 2 1 N +
          twistedLogMonomial a b 1 2 N - 2 * Real.log N * twistedLogMonomial a b 1 1 N|
        ≤ 2 * |twistedGcdLogMonomial a b 1 1 N| + |twistedLogMonomial a b 2 1 N| +
            |twistedLogMonomial a b 1 2 N| + 2 * Real.log N * |twistedLogMonomial a b 1 1 N| := by
          have := abs_sub (2 * twistedGcdLogMonomial a b 1 1 N + twistedLogMonomial a b 2 1 N +
            twistedLogMonomial a b 1 2 N) (2 * Real.log N * twistedLogMonomial a b 1 1 N)
          have h2 := abs_add_le (2 * twistedGcdLogMonomial a b 1 1 N + twistedLogMonomial a b 2 1 N)
            (twistedLogMonomial a b 1 2 N)
          have h3 := abs_add_le (2 * twistedGcdLogMonomial a b 1 1 N) (twistedLogMonomial a b 2 1 N)
          rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at *
          rw [abs_of_pos hL0] at this
          linarith
      _ ≤ 2 * (MG * ((1 + Real.log ((a * b : ℕ) : ℝ)) * twistSize a b) * Real.log N ^ 2) +
            M₂₁ * twistSize a b * Real.log N ^ 2 + M₁₂ * twistSize a b * Real.log N ^ 2 +
            2 * Real.log N * (M₁₁ * twistSize a b * Real.log N ^ 1) := by
          gcongr
          · exact g₁₁.trans (by gcongr)
          · exact q₂₁.trans (by gcongr)
          · exact q₁₂.trans (by gcongr)
          · exact q₁₁.trans (by gcongr)
      _ ≤ (M₁₁ + M₂₁ + M₁₂ + 2 * MG + 2 * M₁₁) *
            ((1 + Real.log ((a * b : ℕ) : ℝ)) * twistSize a b) * Real.log N ^ 2 := by
          have hx : 0 ≤ twistSize a b * Real.log N ^ 2 := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hab1 hx, hMG, hM₁₁, hM₂₁, hM₁₂]

/-! ## The gcd sum -/

theorem sum_Ioc_gcd_div_le {q F : ℕ} (hq : 1 ≤ q) :
    ∑ f ∈ Ioc 0 F, ((Nat.gcd f q : ℕ) : ℝ) / f ≤ q.divisors.card * (1 + Real.log F) := by
  have hexp : ∀ f ∈ Ioc 0 F, ((Nat.gcd f q : ℕ) : ℝ) / f =
      ∑ e ∈ Ioc 0 q, if e ∣ q ∧ e ∣ f then (Nat.totient e : ℝ) * (1 / (f : ℝ)) else 0 := by
    intro f _
    rw [Nat.gcd_comm, natCast_gcd_eq_sum_totient hq le_rfl, Finset.sum_div]
    refine Finset.sum_congr rfl fun e _ => ?_
    split_ifs
    · rw [mul_one_div]
    · rw [zero_div]
  rw [Finset.sum_congr rfl hexp, Finset.sum_comm]
  have hlog : 0 ≤ 1 + Real.log F := by have := Real.log_natCast_nonneg F; linarith
  calc ∑ e ∈ Ioc 0 q, ∑ f ∈ Ioc 0 F,
        (if e ∣ q ∧ e ∣ f then (Nat.totient e : ℝ) * (1 / (f : ℝ)) else 0)
      ≤ ∑ e ∈ Ioc 0 q, if e ∣ q then 1 + Real.log F else 0 := by
        refine Finset.sum_le_sum fun e he => ?_
        have he1 : 1 ≤ e := (mem_Ioc.mp he).1
        have he0 : (0 : ℝ) < e := by exact_mod_cast he1
        split_ifs with heq
        · calc ∑ f ∈ Ioc 0 F, (if e ∣ q ∧ e ∣ f then (Nat.totient e : ℝ) * (1 / (f : ℝ)) else 0)
              = (Nat.totient e : ℝ) * ∑ f ∈ (Ioc 0 F).filter (fun f => e ∣ f), 1 / (f : ℝ) := by
                rw [Finset.mul_sum, Finset.sum_filter]
                refine Finset.sum_congr rfl fun f _ => ?_
                by_cases hf : e ∣ f
                · rw [if_pos ⟨heq, hf⟩, if_pos hf]
                · simp [hf]
            _ ≤ (Nat.totient e : ℝ) * ((1 + Real.log F) / e) :=
                mul_le_mul_of_nonneg_left (sum_filter_dvd_one_div_le he1) (by positivity)
            _ ≤ e * ((1 + Real.log F) / e) :=
                mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.totient_le e) (by positivity)
            _ = 1 + Real.log F := by field_simp
        · exact le_of_eq (Finset.sum_eq_zero fun f _ => by rw [if_neg (fun h => heq h.1)])
    _ = q.divisors.card * (1 + Real.log F) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        congr 2

/-- `Σ_{h ≤ N, f | hc} 1/h ≤ (1 + log N)(f, c)/f`. -/
theorem sum_Icc_dvd_mul_one_div_le {N f c : ℕ} (hf : 1 ≤ f) :
    ∑ h ∈ Icc 1 N, (if f ∣ h * c then 1 / (h : ℝ) else 0) ≤
      (1 + Real.log N) * (Nat.gcd f c : ℝ) / f := by
  set g := Nat.gcd f c with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left c hf
  have hgf : g ∣ f := Nat.gcd_dvd_left f c
  set f' := f / g with hf'
  have hf'1 : 1 ≤ f' := Nat.div_pos (Nat.le_of_dvd hf hgf) hg0
  have hcop : Nat.Coprime f' (c / g) := Nat.coprime_div_gcd_div_gcd hg0
  calc ∑ h ∈ Icc 1 N, (if f ∣ h * c then 1 / (h : ℝ) else 0)
      ≤ ∑ h ∈ (Ioc 0 N).filter (fun h => f' ∣ h), 1 / (h : ℝ) := by
        rw [Finset.sum_filter, show Icc 1 N = Ioc 0 N by ext; simp only [mem_Icc, mem_Ioc]; omega]
        refine Finset.sum_le_sum fun h hh => ?_
        by_cases hd : f ∣ h * c
        · rw [if_pos hd, if_pos]
          have h1 : f' * g ∣ h * (c / g * g) := by
            rw [Nat.div_mul_cancel hgf, Nat.div_mul_cancel (Nat.gcd_dvd_right f c)]; exact hd
          rw [← mul_assoc] at h1
          have h2 : f' ∣ h * (c / g) := Nat.dvd_of_mul_dvd_mul_right hg0 h1
          exact hcop.dvd_of_dvd_mul_right h2
        · rw [if_neg hd]
          split_ifs <;> [positivity; exact le_rfl]
    _ ≤ (1 + Real.log N) / f' := sum_filter_dvd_one_div_le hf'1
    _ = (1 + Real.log N) * (g : ℝ) / f := by
        rw [hf', Nat.cast_div hgf (by exact_mod_cast hg0.ne')]
        have : (g : ℝ) ≠ 0 := by exact_mod_cast hg0.ne'
        have : (f : ℝ) ≠ 0 := by exact_mod_cast (by omega : f ≠ 0)
        field_simp

/-- **The twisted gcd sum.** `Σ_{h,k ≤ N} (ha,kb)/(hk) ≤ d(ab)(1 + log N)²(1 + log(Nab))`. -/
theorem sum_gcd_mul_div_le {a b : ℕ} (hab : Nat.Coprime a b) (ha : 1 ≤ a) (hb : 1 ≤ b) (N : ℕ) :
    ∑ h ∈ Icc 1 N, ∑ k ∈ Icc 1 N, ((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) / ((h : ℝ) * k) ≤
      (a * b).divisors.card * (1 + Real.log N) ^ 2 * (1 + Real.log ((N * a * b : ℕ) : ℝ)) := by
  set F := N * a * b with hF
  have hexp : ∀ h ∈ Icc 1 N, ∀ k ∈ Icc 1 N,
      ((Nat.gcd (h * a) (k * b) : ℕ) : ℝ) / ((h : ℝ) * k) =
        ∑ f ∈ Ioc 0 F, (Nat.totient f : ℝ) *
          ((if f ∣ h * a then 1 / (h : ℝ) else 0) * (if f ∣ k * b then 1 / (k : ℝ) else 0)) := by
    intro h hh k _
    have hh1 : 1 ≤ h * a := Nat.mul_pos (mem_Icc.mp hh).1 ha
    have hhF : h * a ≤ F := by
      rw [hF, mul_assoc, mul_comm a b, ← mul_assoc]
      exact (Nat.mul_le_mul_right a (mem_Icc.mp hh).2).trans (Nat.le_mul_of_pos_right _ hb)
        |>.trans (le_of_eq (by ring))
    rw [natCast_gcd_eq_sum_totient hh1 hhF, Finset.sum_div]
    refine Finset.sum_congr rfl fun f _ => ?_
    by_cases h1 : f ∣ h * a <;> by_cases h2 : f ∣ k * b
    · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_pos h2, one_div_mul_one_div, mul_one_div]
    · rw [if_neg (fun h => h2 h.2), if_neg h2]; simp
    · rw [if_neg (fun h => h1 h.1), if_neg h1]; simp
    · rw [if_neg (fun h => h1 h.1), if_neg h1]; simp
  rw [Finset.sum_congr rfl fun h hh => Finset.sum_congr rfl fun k hk => hexp h hh k hk]
  rw [Finset.sum_congr rfl fun h _ => Finset.sum_comm, Finset.sum_comm]
  have hlogN : 0 ≤ 1 + Real.log N := by have := Real.log_natCast_nonneg N; linarith
  have hab' : 1 ≤ a * b := Nat.mul_pos ha hb
  calc ∑ f ∈ Ioc 0 F, ∑ h ∈ Icc 1 N, ∑ k ∈ Icc 1 N, (Nat.totient f : ℝ) *
          ((if f ∣ h * a then 1 / (h : ℝ) else 0) * (if f ∣ k * b then 1 / (k : ℝ) else 0))
      = ∑ f ∈ Ioc 0 F, (Nat.totient f : ℝ) *
          ((∑ h ∈ Icc 1 N, if f ∣ h * a then 1 / (h : ℝ) else 0) *
            ∑ k ∈ Icc 1 N, if f ∣ k * b then 1 / (k : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun f _ => ?_
        rw [Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ∑ f ∈ Ioc 0 F, (1 + Real.log N) ^ 2 * (((Nat.gcd f (a * b) : ℕ) : ℝ) / f) := by
        refine Finset.sum_le_sum fun f hf => ?_
        have hf1 : 1 ≤ f := (mem_Ioc.mp hf).1
        have hf0 : (0 : ℝ) < f := by exact_mod_cast hf1
        have hA := sum_Icc_dvd_mul_one_div_le (N := N) (c := a) hf1
        have hB := sum_Icc_dvd_mul_one_div_le (N := N) (c := b) hf1
        have hA0 : 0 ≤ ∑ h ∈ Icc 1 N, (if f ∣ h * a then 1 / (h : ℝ) else 0) :=
          Finset.sum_nonneg fun h _ => by split_ifs <;> positivity
        have hB0 : 0 ≤ ∑ k ∈ Icc 1 N, (if f ∣ k * b then 1 / (k : ℝ) else 0) :=
          Finset.sum_nonneg fun h _ => by split_ifs <;> positivity
        have hphi : (Nat.totient f : ℝ) ≤ f := by exact_mod_cast Nat.totient_le f
        have hgab : ((Nat.gcd f (a * b) : ℕ) : ℝ) =
            ((Nat.gcd f a : ℕ) : ℝ) * ((Nat.gcd f b : ℕ) : ℝ) := by
          rw [Nat.Coprime.gcd_mul f hab]; push_cast; ring
        calc (Nat.totient f : ℝ) * ((∑ h ∈ Icc 1 N, if f ∣ h * a then 1 / (h : ℝ) else 0) *
              ∑ k ∈ Icc 1 N, if f ∣ k * b then 1 / (k : ℝ) else 0)
            ≤ f * (((1 + Real.log N) * (Nat.gcd f a : ℝ) / f) *
                ((1 + Real.log N) * (Nat.gcd f b : ℝ) / f)) :=
              mul_le_mul hphi (mul_le_mul hA hB hB0 (by positivity)) (by positivity) hf0.le
          _ = (1 + Real.log N) ^ 2 * (((Nat.gcd f (a * b) : ℕ) : ℝ) / f) := by
              rw [hgab]; field_simp
    _ = (1 + Real.log N) ^ 2 * ∑ f ∈ Ioc 0 F, ((Nat.gcd f (a * b) : ℕ) : ℝ) / f := by
        rw [Finset.mul_sum]
    _ ≤ (1 + Real.log N) ^ 2 * ((a * b).divisors.card * (1 + Real.log F)) :=
        mul_le_mul_of_nonneg_left (sum_Ioc_gcd_div_le hab') (by positivity)
    _ = _ := by ring

end

end RHTower.Sieve
