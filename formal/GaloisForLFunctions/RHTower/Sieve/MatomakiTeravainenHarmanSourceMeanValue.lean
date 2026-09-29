import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenLargeAmplifierSetMeanSquare
import GaloisForLFunctions.RHTower.Sieve.SiftedPolyMeanSquare
import GaloisForLFunctions.RHTower.Sieve.LorentzianLSeriesLine
import GaloisForLFunctions.RHTower.Sieve.DivisorSquareSum

/-!
# Mean values of the Harman source polynomial

`P(s) = ∑_{Y/2 < n ≤ 4Y} ρ⁻(n) n^{-s}` is supported on `z`-rough integers, `z = X^{2/11}`, with
`|ρ⁻| ≤ 156`.  Two mean values are proved:

* **the sifted mean value** (the non-`U` input of Matomäki–Teräväinen (5.2)): the improved mean
  value theorem with the pair sieve over `(2, X^{1/1000}]` at Rankin level `X^{36/1000}` and the
  Brun–Titchmarsh count at level `X^{1/10}` give
  `∫_{-T}^{T}|∑ S(n) n^{-1-it}|² ≪ T/(Y log X) + (log X)^{-2}` for `1 ≤ T ≤ X` and any
  coefficients `|S| ≤ 156` on `(Y/2, 4Y]` free of primes below `X^{1/10}`, in particular for `P`;
* **the product mean value** `∫_{-T}^{T}|P₁(1+it)P(1+it)|² ≤ 156²·8·(10πe + 10πT/(PY))`: each
  coefficient of `P₁P` has at most one term, since a `z`-rough cofactor fixes the small prime.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **The one-line mean square in the frequency variable.**  For finitely supported `a`,
`∫_{-T}^{T} |L(a, 1+it)|² dt = 2π ∫_{-T/2π}^{T/2π} |∑ a_n n^{-1} n^{2πiw}|² dw`. -/
theorem integral_Icc_normSq_LSeries_eq_logPoly {a : ℕ → ℂ} {s : Finset ℕ} (hs0 : 0 ∉ s)
    (hsupp : ∀ n, a n ≠ 0 → n ∈ s) {T : ℝ} (hT : 0 ≤ T) :
    ∫ t in Set.Icc (-T) T, ‖LSeries a (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 =
      2 * Real.pi * ∫ w in Set.Icc (-(T / (2 * Real.pi))) (T / (2 * Real.pi)),
        ‖logPoly (fun n => a n * ((((n : ℝ) ^ (-(1 : ℝ)) : ℝ)) : ℂ)) s w‖ ^ 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  set g : ℝ → ℝ := fun w =>
    ‖logPoly (fun n => a n * ((((n : ℝ) ^ (-(1 : ℝ)) : ℝ)) : ℂ)) s w‖ ^ 2 with hg
  have hpt : ∀ t : ℝ, ‖LSeries a (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 =
      g ((-1 / (2 * Real.pi)) * t) := by
    intro t
    rw [LSeries_eq_logPoly_of_support hs0 hsupp 1 t, hg]
    congr 3
    ring
  simp_rw [hpt]
  have hT' : 0 ≤ T / (2 * Real.pi) := by positivity
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_comp_mul_left (fun w => g w) (by positivity : (-1 / (2 * Real.pi)) ≠ 0)]
  have h1 : -1 / (2 * Real.pi) * -T = T / (2 * Real.pi) := by ring
  have h2 : -1 / (2 * Real.pi) * T = -(T / (2 * Real.pi)) := by ring
  rw [h1, h2, intervalIntegral.integral_symm, smul_eq_mul]
  field_simp
  ring

/-- **The Rankin remainder of the pair sieve.**  `∑_{e ∣ ∏_{P₁<p≤h} p, e ≤ z} 2·6^{ω(e)} ≤
2 z e^{6c₂} (log h)^6`. -/
theorem sum_rangePrimorial_rankin_le (P₁ h : ℕ) (hh : 2 ≤ h) {z : ℝ} (hz : 0 ≤ z) :
    ∑ e ∈ (rangePrimorial P₁ h).divisors,
        (if ((e : ℕ) : ℝ) ≤ z then 2 * 6 ^ e.primeFactors.card else 0) ≤
      2 * z * (Real.exp (6 * mertensSecondUpperConst) * (Real.log h) ^ (6 : ℝ)) := by
  classical
  have hstep : ∀ e ∈ (rangePrimorial P₁ h).divisors,
      (if ((e : ℕ) : ℝ) ≤ z then (2 : ℝ) * 6 ^ e.primeFactors.card else 0) ≤
        2 * z * ((6 : ℝ) ^ e.primeFactors.card / e) := by
    intro e he
    have hepos : 0 < e := Nat.pos_of_mem_divisors he
    have heR : (0 : ℝ) < e := by exact_mod_cast hepos
    have hpow : (0 : ℝ) < (6 : ℝ) ^ e.primeFactors.card := by positivity
    split_ifs with hez
    · rw [mul_div_assoc', le_div_iff₀ heR]
      nlinarith
    · positivity
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum, sum_divisors_pow_card_primeFactors_div_eq_prod
    (rangePrimorial_squarefree P₁ h) 6]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hsub : (rangePrimorial P₁ h).primeFactors ⊆ Nat.primesLE h := by
    rw [rangePrimorial, Nat.primeFactors_prod (fun p hp => rangePrimes_prime hp)]
    intro p hp
    rw [rangePrimes, Finset.mem_filter, Finset.mem_Icc] at hp
    exact Nat.mem_primesLE.2 ⟨hp.1.2, hp.2⟩
  refine le_trans (Finset.prod_le_prod_of_subset_of_one_le hsub (fun p _ => by positivity)
    fun p _ _ => ?_) (prod_one_add_primesLE_le hh (by norm_num))
  have : (0 : ℝ) ≤ 6 / (p : ℝ) := by positivity
  linarith

/-- An integer with no prime factor `≤ z` is coprime to `z#`. -/
theorem coprime_primorial_of_rough {zd n : ℕ} (h : ∀ p, p.Prime → p ≤ zd → ¬ p ∣ n) :
    Nat.Coprime (primorial zd) n := by
  refine Nat.coprime_of_dvd fun k hk hkd => h k hk ?_
  have hmem : k ∈ (primorial zd).primeFactors :=
    Nat.mem_primeFactors.2 ⟨hk, hkd, (primorial_pos zd).ne'⟩
  rw [primeFactors_primorial_eq] at hmem
  exact (Nat.mem_primesLE.1 hmem).1

/-- The Harman source is free of primes below `z`. -/
theorem harmanSource_rough {z Q D E Y m : ℕ} (hm : mtHarmanProposition22SourceAF z Q D E Y m ≠ 0)
    {q : ℕ} (hq : q.Prime) (hqz : q < z) : ¬ q ∣ m := by
  intro hqm
  apply hm
  obtain ⟨hm0, -, -⟩ := mtRealIntervalAF_scaleSupported _ _ _ hm
  rw [mtHarmanProposition22SourceAF, mtRealIntervalAF_apply_of_pos _ _ _ hm0,
    rhoMinus_eq_zero_of_dvd hq hqm hqz]
  simp

/-- The Harman source is bounded by `156` when `4Y < z⁶`. -/
theorem norm_harmanSource_le {z Q D E Y : ℕ} (hz : 2 ≤ z) (hYz : 4 * Y < z ^ 6) (m : ℕ) :
    ‖mtHarmanProposition22SourceAF z Q D E Y m‖ ≤ 156 := by
  by_cases hm : mtHarmanProposition22SourceAF z Q D E Y m = 0
  · rw [hm, norm_zero]; norm_num
  obtain ⟨hm0, -, hhi⟩ := mtRealIntervalAF_scaleSupported _ _ _ hm
  have hm6 : m < z ^ 6 := by
    have : m ≤ 4 * Y := by exact_mod_cast (show (m : ℝ) ≤ ((4 * Y : ℕ) : ℝ) by push_cast; exact hhi)
    omega
  have hρ := abs_rhoMinus_le_of_lt_pow (Q := Q) (D := D) (E := E) hz hm0 hm6
  rw [mtHarmanProposition22SourceAF, mtRealIntervalAF_apply_of_pos _ _ _ hm0]
  split_ifs
  · rw [Complex.norm_intCast]; exact_mod_cast hρ
  · simp

/-- **The sifted mean value theorem for rough bounded coefficients.**  Let `S` be supported on
`(Y/2, 4Y]`, free of primes below `z`, and bounded by `156`.  With the pair sieve over `(2, h]` at
Rankin level `z_r ≥ h^{36}`, and the Brun–Titchmarsh count at level `Y_d ≤ z_d < z`:
`∫_{-T}^{T} |∑ S(n) n^{-1-it}|² ≤ 2π (5T/4)(312/Y)² (D + 2(2e·K·4Y/E² + K·R))`,
`K = ⌈12Y/T⌉`, `E = exp(S(h) − S(2))`, `R` the Rankin remainder, `D` the diagonal count. -/
theorem integral_normSq_LSeries_rough_le {S : ℕ → ℂ} {z Y : ℕ} {T : ℝ} {hs : ℕ} {zr : ℝ}
    {Yd zd : ℕ} (hS : ∀ n, S n ≠ 0 → 0 < n ∧ (Y : ℝ) / 2 < n ∧ (n : ℝ) ≤ 4 * Y)
    (hSrough : ∀ n, S n ≠ 0 → ∀ p, p.Prime → p < z → ¬ p ∣ n) (hSb : ∀ n, ‖S n‖ ≤ 156)
    (hY : 1 ≤ Y) (hT : 1 ≤ T)
    (hh : 2 ≤ hs) (hhz : hs < z) (hlev : ((hs : ℝ)) ^ (18 : ℝ) ≤ Real.sqrt zr) (hzr : 1 ≤ zr)
    (hlog : 20 * mertensFirstConst ≤ Real.log hs) (hzd : zd < z) (hYd : 1 ≤ Yd) (hYdzd : Yd ≤ zd)
    (hzd2 : 2 ≤ zd) (hlogYd : 0 < Real.log Yd) :
    ∫ t in Set.Icc (-T) T, ‖LSeries S (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 ≤
      2 * Real.pi * ((5 * T / 4) * (312 / (Y : ℝ)) ^ 2 *
        ((2 * (((4 * Y : ℕ) : ℝ) - ((Y / 2 : ℕ) : ℝ)) / Real.log Yd
            + ((Yd * Yd : ℕ) : ℝ) * (Real.exp (4 * mertensSecondUpperConst) * (Real.log zd) ^ (4 : ℝ)))
          + 2 * (2 * Real.exp 1 * (⌈12 * (Y : ℝ) / T⌉₊ : ℝ) * ((4 * Y : ℕ) : ℝ)
                / (Real.exp (mertensS hs - mertensS 2)) ^ (2 : ℕ)
              + (⌈12 * (Y : ℝ) / T⌉₊ : ℝ) * ∑ e ∈ (rangePrimorial 2 hs).divisors,
                  (if ((e : ℕ) : ℝ) ≤ zr then 2 * 6 ^ e.primeFactors.card else 0)))) := by
  classical
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY
  have hT0 : 0 < T := by linarith
  set s := (Finset.Icc 1 (4 * Y)).filter (fun n => S n ≠ 0) with hsdef
  have hsupp : ∀ n, S n ≠ 0 → n ∈ s := by
    intro n hn
    obtain ⟨hn0, hlo, hhi⟩ := hS n hn
    refine Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hn0, ?_⟩, hn⟩
    exact_mod_cast (show (n : ℝ) ≤ ((4 * Y : ℕ) : ℝ) by push_cast; exact hhi)
  have hs0 : (0 : ℕ) ∉ s := by simp [hsdef]
  rw [integral_Icc_normSq_LSeries_eq_logPoly hs0 hsupp hT0.le]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  -- the values on the support
  have hval : ∀ n ∈ s, S n ≠ 0 ∧ (Y : ℝ) / 2 < n ∧ (n : ℝ) ≤ 4 * Y := by
    intro n hn
    have hSn := (Finset.mem_filter.1 hn).2
    obtain ⟨-, hlo, hhi⟩ := hS n hSn
    exact ⟨hSn, hlo, hhi⟩
  have hrough : ∀ n ∈ s, ∀ p, p.Prime → p < z → ¬ p ∣ n := fun n hn =>
    hSrough n (hval n hn).1
  have hsC1 : ∀ n ∈ s, 1 ≤ n ∧ n ≤ 4 * Y ∧ ∀ p ∈ rangePrimes 2 hs, ¬ p ∣ n := by
    intro n hn
    obtain ⟨hn1, hnY⟩ := Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1
    refine ⟨hn1, hnY, fun p hp => hrough n hn p (rangePrimes_prime hp) ?_⟩
    rw [rangePrimes, Finset.mem_filter, Finset.mem_Icc] at hp
    omega
  have haC1 : ∀ n ∈ s, ‖S n * ((((n : ℝ) ^ (-(1 : ℝ)) : ℝ)) : ℂ)‖ ≤ 312 / (Y : ℝ) := by
    intro n hn
    obtain ⟨-, hlo, -⟩ := hval n hn
    have hn0 : 0 < n := (Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1).1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    have hSval : ‖S n‖ ≤ 156 := hSb n
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), Real.rpow_neg_one]
    calc ‖S n‖ * (n : ℝ)⁻¹ ≤ 156 * (2 / (Y : ℝ)) := by
          apply mul_le_mul hSval _ (by positivity) (by norm_num)
          rw [inv_le_comm₀ hnR (by positivity), inv_div]
          linarith
      _ = 312 / (Y : ℝ) := by ring
  have hδ : 2 * Real.pi * (1 / T) * (T / (2 * Real.pi)) ≤ 1 := by
    field_simp; exact le_rfl
  have hK : 3 * (((4 * Y : ℕ) : ℝ)) * (1 / T) ≤ (⌈12 * (Y : ℝ) / T⌉₊ : ℝ) := by
    refine le_trans (le_of_eq ?_) (Nat.le_ceil _)
    push_cast; ring
  have hC1 := integral_normSq_logPoly_sifted_le (fun n => S n * ((((n : ℝ) ^ (-(1 : ℝ)) : ℝ)) : ℂ))
    s (N := 4 * Y) (h := hs) (K := ⌈12 * (Y : ℝ) / T⌉₊) (P₁ := 2) (B := 312 / (Y : ℝ))
    (δ := 1 / T) (W := T / (2 * Real.pi)) (z := zr) hsC1 haC1 (by positivity)
    (by rw [div_le_one hT0]; exact hT) hδ hK le_rfl hzr hh hh hlev hlog
  have hinv : 5 / (4 * (1 / T)) = 5 * T / 4 := by field_simp
  rw [hinv] at hC1
  refine hC1.trans ?_
  -- the diagonal count
  have hcard : (s.card : ℝ) ≤ 2 * (((4 * Y : ℕ) : ℝ) - ((Y / 2 : ℕ) : ℝ)) / Real.log Yd
      + ((Yd * Yd : ℕ) : ℝ) * (Real.exp (4 * mertensSecondUpperConst) * (Real.log zd) ^ (4 : ℝ)) := by
    have hsub : s ⊆ {n ∈ Finset.Ioc (Y / 2) (4 * Y) | Nat.Coprime (primorial zd) n} := by
      intro n hn
      obtain ⟨-, hlo, hhi⟩ := hval n hn
      refine Finset.mem_filter.2 ⟨Finset.mem_Ioc.2 ⟨?_, ?_⟩, ?_⟩
      · have h1 : ((Y / 2 : ℕ) : ℝ) ≤ (Y : ℝ) / 2 := by
          rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
          exact_mod_cast Nat.div_mul_le_self Y 2
        exact_mod_cast h1.trans_lt hlo
      · exact (Finset.mem_Icc.1 (Finset.mem_filter.1 hn).1).2
      · exact coprime_primorial_of_rough fun p hp hpz => hrough n hn p hp (by omega)
    have h := card_coprime_Ioc_le_explicit (Y / 2) (4 * Y) zd Yd (by omega) hYd hYdzd hzd2 hlogYd
    exact (Nat.cast_le.2 (Finset.card_le_card hsub)).trans h
  have hpos : 0 ≤ 5 * T / 4 * (312 / (Y : ℝ)) ^ 2 := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hpos
  linarith

/-- The prime polynomial `P₁(1+it) = ∑_{p ∈ B} p^{-1-it}` as a one-line value. -/
theorem sum_primeSet_eq_LSeries {B : Finset ℕ} (hB0 : 0 ∉ B) (t : ℝ) :
    ∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)) =
      LSeries (fun n => if n ∈ B then (1 : ℂ) else 0) (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I) := by
  classical
  rw [LSeries, tsum_eq_sum (s := B)]
  · refine Finset.sum_congr rfl fun n hn => ?_
    have hn0 : n ≠ 0 := fun h => hB0 (h ▸ hn)
    rw [LSeries.term_def, if_neg hn0, if_pos hn, one_div, Complex.cpow_neg]
  · intro n hn
    rcases eq_or_ne n 0 with rfl | hn0
    · rw [LSeries.term_def, if_pos rfl]
    · rw [LSeries.term_def, if_neg hn0, if_neg hn, zero_div]

/-- **The product of the prime and source polynomials has bounded coefficients.**  If
`n = pm = p'm'` with `p ≠ p'` in `B` and `m, m'` `z`-rough, then `p' ∣ m`, impossible below `z`;
so each coefficient of `P₁ P` has at most one term. -/
theorem norm_convolution_primeSet_source_le {B : Finset ℕ} (hBp : ∀ p ∈ B, p.Prime) {z : ℕ}
    (hBz : ∀ p ∈ B, p < z) {b : ℕ → ℂ} (hb : ∀ m, b m ≠ 0 → ∀ q, q.Prime → q < z → ¬ q ∣ m)
    {M : ℝ} (hbM : ∀ m, ‖b m‖ ≤ M) (n : ℕ) :
    ‖LSeries.convolution (fun n => if n ∈ B then (1 : ℂ) else 0) b n‖ ≤ M := by
  classical
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hbM 0)
  rw [LSeries.convolution_def]
  set f : ℕ × ℕ → ℂ := fun x => (if x.1 ∈ B then (1 : ℂ) else 0) * b x.2 with hf
  show ‖∑ x ∈ n.divisorsAntidiagonal, f x‖ ≤ M
  by_cases hex : ∃ x ∈ n.divisorsAntidiagonal, f x ≠ 0
  · obtain ⟨x₀, hx₀, hfx₀⟩ := hex
    have huniq : ∀ x ∈ n.divisorsAntidiagonal, x ≠ x₀ → f x = 0 := by
      intro x hx hne
      by_contra hfx
      have hx1 : x.1 ∈ B := by by_contra h; exact hfx (by simp [hf, h])
      have hx01 : x₀.1 ∈ B := by by_contra h; exact hfx₀ (by simp [hf, h])
      have hbx : b x.2 ≠ 0 := by intro h; exact hfx (by simp [hf, h])
      have hbx₀ : b x₀.2 ≠ 0 := by intro h; exact hfx₀ (by simp [hf, h])
      have hn := (Nat.mem_divisorsAntidiagonal.1 hx).1
      have hn₀ := (Nat.mem_divisorsAntidiagonal.1 hx₀).1
      by_cases h1 : x.1 = x₀.1
      · apply hne
        have hp0 : 0 < x.1 := (hBp _ hx1).pos
        have h2 : x.2 = x₀.2 := by
          have : x.1 * x.2 = x.1 * x₀.2 := by rw [hn, h1, hn₀]
          exact Nat.eq_of_mul_eq_mul_left hp0 this
        exact Prod.ext h1 h2
      · -- `x₀.1` divides `x.1 * x.2`, hence `x.2`
        have hdvd : x₀.1 ∣ x.1 * x.2 := by rw [hn, ← hn₀]; exact dvd_mul_right _ _
        have hp₀ := hBp _ hx01
        rcases (Nat.Prime.dvd_mul hp₀).1 hdvd with h | h
        · have := (Nat.prime_dvd_prime_iff_eq hp₀ (hBp _ hx1)).1 h
          exact h1 this.symm
        · exact hb x.2 hbx x₀.1 hp₀ (hBz _ hx01) h
    rw [Finset.sum_eq_single_of_mem x₀ hx₀ huniq]
    have hx01 : x₀.1 ∈ B := by by_contra h; exact hfx₀ (by simp [hf, h])
    simp only [hf, if_pos hx01, one_mul]
    exact hbM _
  · push Not at hex
    rw [Finset.sum_eq_zero hex, norm_zero]
    exact hM0

/-- **The mean value of `P₁ P`.**  `∫_{-T}^{T} |P₁(1+it) P(1+it)|² ≤ 156²·8·(10πe + 10πT/(PY))`. -/
theorem integral_normSq_primeSet_mul_harmanSource_le {B : Finset ℕ} (hBp : ∀ p ∈ B, p.Prime)
    {P : ℝ} (hP : 1 ≤ P) (hB : ∀ p ∈ B, P < p ∧ (p : ℝ) ≤ 2 * P) {z Q D E Y : ℕ} (hz : 2 ≤ z)
    (hBz : ∀ p ∈ B, p < z) (hY : 1 ≤ Y) (hYz : 4 * Y < z ^ 6) {T : ℝ} (hT : 1 ≤ T) :
    ∫ t in Set.Icc (-T) T,
        ‖(∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) *
          LSeries (fun n => mtHarmanProposition22SourceAF z Q D E Y n)
            (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 ≤
      156 ^ 2 * 8 * (10 * Real.pi * Real.exp 1 + 10 * Real.pi * T / (P * Y)) := by
  classical
  set a : ℕ → ℂ := fun n => if n ∈ B then (1 : ℂ) else 0 with ha
  set b : ℕ → ℂ := fun n => mtHarmanProposition22SourceAF z Q D E Y n with hb
  have hP0 : 0 < P := by linarith
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY
  have hB0 : (0 : ℕ) ∉ B := fun h => (hBp 0 h).ne_zero rfl
  have hsa : ∀ n, a n ≠ 0 → n ∈ Finset.Icc 1 ⌊2 * P⌋₊ := by
    intro n hn
    have hnB : n ∈ B := by by_contra h; exact hn (by simp [ha, h])
    refine Finset.mem_Icc.2 ⟨(hBp n hnB).pos, Nat.le_floor (hB n hnB).2⟩
  have hsb : ∀ n, b n ≠ 0 → n ∈ Finset.Icc 1 (4 * Y) := by
    intro n hn
    obtain ⟨hn0, -, hhi⟩ := mtRealIntervalAF_scaleSupported _ _ _ hn
    exact Finset.mem_Icc.2 ⟨hn0, by exact_mod_cast (show (n : ℝ) ≤ ((4 * Y : ℕ) : ℝ) by
      push_cast; exact hhi)⟩
  have hsc : ∀ n, LSeries.convolution a b n ≠ 0 → n ∈ Finset.Icc 1 (⌊2 * P⌋₊ * (4 * Y)) :=
    fun n hn => convolution_mem_Icc_of_support_mul hsa hsb hn
  -- the rough cofactor
  have hbrough : ∀ m, b m ≠ 0 → ∀ q, q.Prime → q < z → ¬ q ∣ m :=
    fun m hm q hq hqz => harmanSource_rough hm hq hqz
  have hbM : ∀ m, ‖b m‖ ≤ 156 := norm_harmanSource_le hz hYz
  have hcM := norm_convolution_primeSet_source_le hBp hBz hbrough hbM
  -- lower end of the support
  have hclo : ∀ n, LSeries.convolution a b n ≠ 0 → P * Y / 2 < n := by
    intro n hn
    rw [LSeries.convolution_def] at hn
    obtain ⟨x, hx, hxne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hn
    have hx1 : x.1 ∈ B := by by_contra h; exact hxne (by simp [ha, h])
    have hbx : b x.2 ≠ 0 := by intro h; exact hxne (by simp [h])
    obtain ⟨-, hlo, -⟩ := mtRealIntervalAF_scaleSupported _ _ _ hbx
    have hn := (Nat.mem_divisorsAntidiagonal.1 hx).1
    have hp := (hB _ hx1).1
    have : (n : ℝ) = (x.1 : ℝ) * (x.2 : ℝ) := by rw [← hn]; push_cast; ring
    rw [this]
    have hY2 : 0 ≤ (Y : ℝ) / 2 := by positivity
    calc P * Y / 2 = P * ((Y : ℝ) / 2) := by ring
      _ < (x.1 : ℝ) * (x.2 : ℝ) := mul_lt_mul' hp.le hlo hY2 (by linarith)
  -- the product is one polynomial
  have hval : ∀ t : ℝ, (∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) *
      LSeries b (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I) =
      perronPoly (LSeries.convolution a b) (⌊2 * P⌋₊ * (4 * Y)) 1 t := by
    intro t
    rw [sum_primeSet_eq_LSeries hB0, ← LSeries_convolution' (LSeriesSummable_of_support hsa _)
      (LSeriesSummable_of_support hsb _), perronPoly_eq_LSeries_of_support hsc]
  simp_rw [hval]
  have hN₀ : 0 < P * Y / 2 := by positivity
  refine (integral_normSq_perronPoly_le_of_lower_support _ _ hN₀ hT hclo).trans ?_
  have hsum : ∑ n ∈ Finset.Icc 1 (⌊2 * P⌋₊ * (4 * Y)), ‖LSeries.convolution a b n‖ ^ 2 ≤
      156 ^ 2 * (8 * P * Y) := by
    calc ∑ n ∈ Finset.Icc 1 (⌊2 * P⌋₊ * (4 * Y)), ‖LSeries.convolution a b n‖ ^ 2
        ≤ ∑ _n ∈ Finset.Icc 1 (⌊2 * P⌋₊ * (4 * Y)), (156 : ℝ) ^ 2 :=
          Finset.sum_le_sum fun n _ => pow_le_pow_left₀ (norm_nonneg _) (hcM n) 2
      _ = 156 ^ 2 * ((⌊2 * P⌋₊ * (4 * Y) : ℕ) : ℝ) := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]; push_cast; ring
      _ ≤ 156 ^ 2 * (8 * P * Y) := by
          gcongr
          push_cast
          have := Nat.floor_le (by positivity : (0 : ℝ) ≤ 2 * P)
          nlinarith
  have hpre : 0 ≤ 5 * Real.pi * Real.exp 1 / (P * Y / 2) + 5 * Real.pi / 2 * T / (P * Y / 2) ^ 2 := by
    have : 0 ≤ T := by linarith
    positivity
  calc (5 * Real.pi * Real.exp 1 / (P * Y / 2) + 5 * Real.pi / 2 * T / (P * Y / 2) ^ 2) *
        ∑ n ∈ Finset.Icc 1 (⌊2 * P⌋₊ * (4 * Y)), ‖LSeries.convolution a b n‖ ^ 2
      ≤ (5 * Real.pi * Real.exp 1 / (P * Y / 2) + 5 * Real.pi / 2 * T / (P * Y / 2) ^ 2) *
          (156 ^ 2 * (8 * P * Y)) := mul_le_mul_of_nonneg_left hsum hpre
    _ = _ := by field_simp; ring

/-- **The pair-sieve saving.**  `exp(S(N) − S(2))² ≥ c₀ (log N)²`. -/
theorem exists_exp_mertensS_sub_sq_ge :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ N : ℕ, 2 ≤ N →
      c₀ * Real.log N ^ 2 ≤ (Real.exp (mertensS N - mertensS 2)) ^ (2 : ℕ) := by
  set c₁ : ℝ := (2 * mertensFirstConst + 1 / 2) / Real.log 2 with hc₁
  have h2 := abs_mertensS_sub_logLog_sub_const_le (le_refl 2)
  set C₂ : ℝ := logLog 2 + meisselMertensConst + (2 * mertensFirstConst + 1 / 2) / Real.log 2
    with hC₂
  have hS2 : mertensS 2 ≤ C₂ := by
    have := (abs_le.1 h2).2
    push_cast at this
    rw [hC₂]; linarith
  set c₅ : ℝ := C₂ - meisselMertensConst + c₁ with hc₅
  refine ⟨Real.exp (-(2 * c₅)), Real.exp_pos _, fun N hN => ?_⟩
  have hlow := logLog_sub_le_mertensS hN
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hdiff : logLog N - c₅ ≤ mertensS N - mertensS 2 := by
    rw [hc₅, hc₁] at *; linarith
  have hexp : Real.log N * Real.exp (-c₅) ≤ Real.exp (mertensS N - mertensS 2) := by
    calc Real.log N * Real.exp (-c₅) = Real.exp (logLog N - c₅) := by
          rw [sub_eq_add_neg, Real.exp_add, logLog, Real.exp_log hlogN]
      _ ≤ _ := Real.exp_le_exp.2 hdiff
  have hsq := pow_le_pow_left₀ (by positivity) hexp 2
  calc Real.exp (-(2 * c₅)) * Real.log N ^ 2 = (Real.log N * Real.exp (-c₅)) ^ 2 := by
        rw [mul_pow, ← Real.exp_nat_mul]; push_cast; ring_nf
    _ ≤ _ := hsq

/-- The constant of the sifted mean value theorem. -/
def siftedMeanValueConst (c₀ : ℝ) : ℝ :=
  2 * Real.pi * (5 / 4) * 312 ^ 2 * (161 + 13 * (16 * Real.exp 1 * (4 * 10 ^ 6 / c₀))) + 1

/-- **Collecting the sifted bound.**  With the diagonal `≤ 161Y/L`, the saving `E² ≥ c₀(L/2000)²`,
`K ≤ 12Y/T + 1`, and the remainder `2π(5/4)312²·2(12/Y + T/Y²)·R ≤ 1/L²`, the explicit sifted
mean value is `≤ C(T/(YL) + 1/L²)`. -/
theorem siftedMeanValue_collect_le {T Y L Dg E2 K Rm c₀ : ℝ} (hc₀ : 0 < c₀) (hT : 1 ≤ T)
    (hY : 0 < Y) (hL : 1 ≤ L) (hDg : Dg ≤ 161 * Y / L) (hE2 : c₀ * (L / 2000) ^ 2 ≤ E2)
    (hK : K ≤ 12 * Y / T + 1) (hRm0 : 0 ≤ Rm)
    (hRm : 2 * Real.pi * (5 / 4) * 312 ^ 2 * (2 * ((12 / Y + T / Y ^ 2) * Rm)) ≤ 1 / L ^ 2) :
    2 * Real.pi * ((5 * T / 4) * (312 / Y) ^ 2 * (Dg + 2 * (2 * Real.exp 1 * K * (4 * Y) / E2
        + K * Rm))) ≤
      siftedMeanValueConst c₀ * (T / (Y * L) + 1 / L ^ 2) := by
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < L := by linarith
  have hE20 : 0 < E2 := lt_of_lt_of_le (by positivity) hE2
  set A : ℝ := 2 * Real.pi * (5 / 4) * 312 ^ 2 with hA
  have hA0 : 0 < A := by positivity
  have hsplit : 2 * Real.pi * ((5 * T / 4) * (312 / Y) ^ 2 * (Dg + 2 * (2 * Real.exp 1 * K * (4 * Y) / E2
        + K * Rm))) =
      A * (T / Y ^ 2 * Dg) + A * (16 * Real.exp 1 * (T / Y * K) / E2) +
        A * (2 * (T / Y ^ 2 * K * Rm)) := by
    rw [hA]; field_simp; ring
  rw [hsplit]
  -- the diagonal
  have h1 : T / Y ^ 2 * Dg ≤ 161 * (T / (Y * L)) := by
    calc T / Y ^ 2 * Dg ≤ T / Y ^ 2 * (161 * Y / L) := by gcongr
      _ = 161 * (T / (Y * L)) := by field_simp
  -- the shifted pairs
  have hTK : T / Y * K ≤ 12 + T / Y := by
    calc T / Y * K ≤ T / Y * (12 * Y / T + 1) := by gcongr
      _ = 12 + T / Y := by field_simp
  have hinvE : 1 / E2 ≤ 4 * 10 ^ 6 / c₀ / L ^ 2 := by
    calc 1 / E2 ≤ 1 / (c₀ * (L / 2000) ^ 2) := one_div_le_one_div_of_le (by positivity) hE2
      _ = 4 * 10 ^ 6 / c₀ / L ^ 2 := by field_simp; ring
  have h2 : 16 * Real.exp 1 * (T / Y * K) / E2 ≤
      16 * Real.exp 1 * (4 * 10 ^ 6 / c₀) * (12 / L ^ 2 + T / (Y * L)) := by
    have hTYL : T / Y / L ^ 2 ≤ T / (Y * L) := by
      have hL1 : 1 / L ≤ 1 := by rw [div_le_one hL0]; exact hL
      calc T / Y / L ^ 2 = T / (Y * L) * (1 / L) := by field_simp
        _ ≤ T / (Y * L) * 1 := by gcongr
        _ = T / (Y * L) := mul_one _
    calc 16 * Real.exp 1 * (T / Y * K) / E2 = 16 * Real.exp 1 * (T / Y * K) * (1 / E2) := by ring
      _ ≤ 16 * Real.exp 1 * (12 + T / Y) * (4 * 10 ^ 6 / c₀ / L ^ 2) := by gcongr
      _ = 16 * Real.exp 1 * (4 * 10 ^ 6 / c₀) * (12 / L ^ 2 + T / Y / L ^ 2) := by ring
      _ ≤ 16 * Real.exp 1 * (4 * 10 ^ 6 / c₀) * (12 / L ^ 2 + T / (Y * L)) := by gcongr
  -- the remainder
  have h3 : A * (2 * (T / Y ^ 2 * K * Rm)) ≤ 1 / L ^ 2 := by
    refine le_trans ?_ hRm
    refine mul_le_mul_of_nonneg_left ?_ hA0.le
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    have : T / Y ^ 2 * K ≤ 12 / Y + T / Y ^ 2 := by
      calc T / Y ^ 2 * K ≤ T / Y ^ 2 * (12 * Y / T + 1) := by gcongr
        _ = 12 / Y + T / Y ^ 2 := by field_simp
    exact mul_le_mul_of_nonneg_right this hRm0
  have hq : 0 ≤ T / (Y * L) := by positivity
  have hq2 : 0 ≤ 1 / L ^ 2 := by positivity
  have hB : 0 ≤ 16 * Real.exp 1 * (4 * 10 ^ 6 / c₀) := by positivity
  calc A * (T / Y ^ 2 * Dg) + A * (16 * Real.exp 1 * (T / Y * K) / E2) +
        A * (2 * (T / Y ^ 2 * K * Rm))
      ≤ A * (161 * (T / (Y * L))) +
          A * (16 * Real.exp 1 * (4 * 10 ^ 6 / c₀) * (12 / L ^ 2 + T / (Y * L))) + 1 / L ^ 2 := by
        gcongr
    _ ≤ siftedMeanValueConst c₀ * (T / (Y * L) + 1 / L ^ 2) := by
        have hconst : siftedMeanValueConst c₀ =
            A * (161 + 13 * (16 * Real.exp 1 * (4 * 10 ^ 6 / c₀))) + 1 := by
          rw [siftedMeanValueConst, hA]
        rw [hconst]
        set B' := 16 * Real.exp 1 * (4 * 10 ^ 6 / c₀) with hB'
        set q := T / (Y * L) with hq'
        set q2 := 1 / L ^ 2 with hq2'
        have e1 : 12 / L ^ 2 = 12 * q2 := by rw [hq2']; ring
        rw [e1]
        nlinarith [mul_nonneg hA0.le hq, mul_nonneg hA0.le hq2, mul_nonneg (mul_nonneg hA0.le hB) hq,
          mul_nonneg (mul_nonneg hA0.le hB) hq2]

/-- `⌊X^θ⌋` has logarithm at least `(θ/2) log X` once `X^θ ≥ 4`. -/
theorem half_log_le_log_floor_rpow {X θ : ℝ} (hX : 1 < X) (h4 : 4 ≤ X ^ θ) :
    θ / 2 * Real.log X ≤ Real.log (⌊X ^ θ⌋₊ : ℝ) := by
  set y := X ^ θ with hy
  have hy0 : 0 < y := by linarith
  have hfl : y / 2 ≤ (⌊y⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one y
    linarith
  have hsq : Real.sqrt y ≤ y / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hlog : Real.log (Real.sqrt y) ≤ Real.log (⌊y⌋₊ : ℝ) :=
    Real.log_le_log (Real.sqrt_pos.2 hy0) (hsq.trans hfl)
  rw [Real.log_sqrt hy0.le, hy, Real.log_rpow (by linarith)] at hlog
  linarith

/-- The diagonal of the sifted bound at the Brun–Titchmarsh level `⌊X^{1/10}⌋`. -/
theorem harmanSource_diagonal_le {X : ℝ} {Y : ℕ} (hX1 : 1 < X) (hL1 : 1 ≤ Real.log X)
    (h10 : 4 ≤ X ^ (1 / 10 : ℝ))
    (hpoly5 : Real.exp (4 * mertensSecondUpperConst) * (1 + Real.log (24 * X)) ^ 5 ≤
      X ^ (79 / 100 : ℝ))
    (hY99 : X ^ (99 / 100 : ℝ) ≤ Y) :
    2 * (4 * (Y : ℝ) - ((Y / 2 : ℕ) : ℝ)) / Real.log (⌊X ^ (1 / 10 : ℝ)⌋₊ : ℝ) +
        ((⌊X ^ (1 / 10 : ℝ)⌋₊ * ⌊X ^ (1 / 10 : ℝ)⌋₊ : ℕ) : ℝ) *
          (Real.exp (4 * mertensSecondUpperConst) *
            (Real.log (⌊X ^ (1 / 10 : ℝ)⌋₊ : ℝ)) ^ (4 : ℝ)) ≤
      161 * Y / Real.log X := by
  have hX0 : 0 < X := by linarith
  set L := Real.log X with hLdef
  have hL0 : 0 < L := by linarith
  set zd := ⌊X ^ (1 / 10 : ℝ)⌋₊ with hzddef
  have hzdlog := half_log_le_log_floor_rpow (θ := 1 / 10) hX1 h10
  rw [← hzddef, ← hLdef] at hzdlog
  have hzdlogpos : 0 < Real.log zd := by nlinarith
  have hYpos : (0 : ℝ) < Y := lt_of_lt_of_le (by positivity) hY99
  have hlin : 2 * (4 * (Y : ℝ) - ((Y / 2 : ℕ) : ℝ)) ≤ 8 * Y := by
    nlinarith [Nat.cast_nonneg (α := ℝ) (Y / 2)]
  have hd1 : 2 * (4 * (Y : ℝ) - ((Y / 2 : ℕ) : ℝ)) / Real.log zd ≤ 160 * Y / L := by
    rw [div_le_div_iff₀ hzdlogpos hL0]
    nlinarith
  have hzdX : (zd : ℝ) ≤ X ^ (1 / 10 : ℝ) := Nat.floor_le (by positivity)
  have hX10 : X ^ (1 / 10 : ℝ) ≤ X := by
    calc X ^ (1 / 10 : ℝ) ≤ X ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hX1.le (by norm_num)
      _ = X := Real.rpow_one X
  have hzdpos : (0 : ℝ) < zd := Nat.cast_pos.2 (Nat.floor_pos.2 (by linarith))
  have hzdlogX : Real.log zd ≤ L := Real.log_le_log hzdpos (hzdX.trans hX10)
  have hL24 : L ≤ 1 + Real.log (24 * X) := by
    rw [hLdef, Real.log_mul (by norm_num) hX0.ne']
    have : 0 ≤ Real.log 24 := Real.log_nonneg (by norm_num)
    linarith
  have hsq : ((zd * zd : ℕ) : ℝ) ≤ X ^ (1 / 5 : ℝ) := by
    push_cast
    calc (zd : ℝ) * zd ≤ X ^ (1 / 10 : ℝ) * X ^ (1 / 10 : ℝ) := by gcongr
      _ = X ^ (1 / 5 : ℝ) := by rw [← Real.rpow_add hX0]; norm_num
  have hlog4 : (Real.log zd) ^ (4 : ℝ) ≤ L ^ 4 := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact pow_le_pow_left₀ hzdlogpos.le hzdlogX 4
  have hpol : Real.exp (4 * mertensSecondUpperConst) * L ^ 5 ≤ X ^ (79 / 100 : ℝ) := by
    refine le_trans ?_ hpoly5
    gcongr
  have hsplit : X ^ (99 / 100 : ℝ) = X ^ (1 / 5 : ℝ) * X ^ (79 / 100 : ℝ) := by
    rw [← Real.rpow_add hX0]; norm_num
  have hd2 : ((zd * zd : ℕ) : ℝ) * (Real.exp (4 * mertensSecondUpperConst) *
      (Real.log zd) ^ (4 : ℝ)) ≤ Y / L := by
    rw [le_div_iff₀ hL0]
    calc ((zd * zd : ℕ) : ℝ) * (Real.exp (4 * mertensSecondUpperConst) * (Real.log zd) ^ (4 : ℝ)) * L
        ≤ X ^ (1 / 5 : ℝ) * (Real.exp (4 * mertensSecondUpperConst) * L ^ 4) * L := by gcongr
      _ = X ^ (1 / 5 : ℝ) * (Real.exp (4 * mertensSecondUpperConst) * L ^ 5) := by ring
      _ ≤ X ^ (1 / 5 : ℝ) * X ^ (79 / 100 : ℝ) := by gcongr
      _ = X ^ (99 / 100 : ℝ) := hsplit.symm
      _ ≤ Y := hY99
  have : 160 * (Y : ℝ) / L + Y / L = 161 * Y / L := by ring
  linarith

/-- The Rankin remainder of the sifted bound at `h = ⌊X^{1/1000}⌋`, `z_r = h^{36}`. -/
theorem harmanSource_remainder_le {X T : ℝ} {Y : ℕ} (hX1 : 1 < X) (hL1 : 1 ≤ Real.log X)
    (h1000 : 4 ≤ X ^ (1 / 1000 : ℝ)) (hT : 1 ≤ T) (hTX : T ≤ X) (hY99 : X ^ (99 / 100 : ℝ) ≤ Y)
    (hpoly8 : 52 * (2 * Real.pi * (5 / 4) * 312 ^ 2) * Real.exp (6 * mertensSecondUpperConst) *
      (1 + Real.log (24 * X)) ^ 8 ≤ X ^ (944 / 1000 : ℝ)) :
    2 * Real.pi * (5 / 4) * 312 ^ 2 * (2 * ((12 / (Y : ℝ) + T / (Y : ℝ) ^ 2) *
      ∑ e ∈ (rangePrimorial 2 ⌊X ^ (1 / 1000 : ℝ)⌋₊).divisors,
        (if ((e : ℕ) : ℝ) ≤ ((⌊X ^ (1 / 1000 : ℝ)⌋₊ : ℕ) : ℝ) ^ (36 : ℝ)
          then 2 * 6 ^ e.primeFactors.card else 0))) ≤ 1 / Real.log X ^ 2 := by
  have hX0 : 0 < X := by linarith
  set L := Real.log X with hLdef
  have hL0 : 0 < L := by linarith
  set A : ℝ := 2 * Real.pi * (5 / 4) * 312 ^ 2 with hA
  have hA0 : 0 < A := by positivity
  set hs := ⌊X ^ (1 / 1000 : ℝ)⌋₊ with hsdef
  have hs3 : 3 ≤ hs := by
    have : (3 : ℝ) ≤ X ^ (1 / 1000 : ℝ) := by linarith
    exact Nat.le_floor (by exact_mod_cast this)
  have hsR : (3 : ℝ) ≤ hs := by exact_mod_cast hs3
  have hYpos : (0 : ℝ) < Y := lt_of_lt_of_le (by positivity) hY99
  have hXr : ∀ {a b : ℝ}, a ≤ b → X ^ a ≤ X ^ b := fun h => Real.rpow_le_rpow_of_exponent_le hX1.le h
  have hRm := sum_rangePrimorial_rankin_le 2 hs (by omega) (z := ((hs : ℕ) : ℝ) ^ (36 : ℝ))
    (by positivity)
  have hsX : (hs : ℝ) ≤ X := (Nat.floor_le (by positivity)).trans (by
    calc X ^ (1 / 1000 : ℝ) ≤ X ^ (1 : ℝ) := hXr (by norm_num)
      _ = X := Real.rpow_one X)
  have hlogs : Real.log hs ≤ L := Real.log_le_log (by positivity) hsX
  have hzrX : ((hs : ℕ) : ℝ) ^ (36 : ℝ) ≤ X ^ (36 / 1000 : ℝ) := by
    calc ((hs : ℕ) : ℝ) ^ (36 : ℝ) ≤ (X ^ (1 / 1000 : ℝ)) ^ (36 : ℝ) :=
          Real.rpow_le_rpow (by positivity) (Nat.floor_le (by positivity)) (by norm_num)
      _ = X ^ (36 / 1000 : ℝ) := by rw [← Real.rpow_mul hX0.le]; norm_num
  have hlog6 : (Real.log hs) ^ (6 : ℝ) ≤ L ^ 6 := by
    rw [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    exact pow_le_pow_left₀ (Real.log_nonneg (by linarith)) hlogs 6
  have hRm' : ∑ e ∈ (rangePrimorial 2 hs).divisors,
      (if ((e : ℕ) : ℝ) ≤ ((hs : ℕ) : ℝ) ^ (36 : ℝ) then 2 * 6 ^ e.primeFactors.card else 0) ≤
      2 * X ^ (36 / 1000 : ℝ) * (Real.exp (6 * mertensSecondUpperConst) * L ^ 6) := by
    refine hRm.trans ?_
    gcongr
  have hRm0 : 0 ≤ ∑ e ∈ (rangePrimorial 2 hs).divisors,
      (if ((e : ℕ) : ℝ) ≤ ((hs : ℕ) : ℝ) ^ (36 : ℝ) then (2 : ℝ) * 6 ^ e.primeFactors.card else 0) :=
    Finset.sum_nonneg fun e _ => by split_ifs <;> positivity
  have hY2 : X ^ (198 / 100 : ℝ) ≤ (Y : ℝ) ^ 2 := by
    calc X ^ (198 / 100 : ℝ) = (X ^ (99 / 100 : ℝ)) ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
      _ ≤ (Y : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hY99 2
  have hXm : 0 < X ^ (-(98 / 100 : ℝ)) := by positivity
  have e1 : 12 / (Y : ℝ) ≤ 12 * X ^ (-(98 / 100 : ℝ)) := by
    have h1 : X ^ (-(98 / 100 : ℝ)) * X ^ (99 / 100 : ℝ) ≥ 1 := by
      rw [← Real.rpow_add hX0]; exact Real.one_le_rpow hX1.le (by norm_num)
    rw [div_le_iff₀ hYpos]
    nlinarith
  have e2 : T / (Y : ℝ) ^ 2 ≤ X ^ (-(98 / 100 : ℝ)) := by
    have hX198 : X ≤ X ^ (-(98 / 100 : ℝ)) * X ^ (198 / 100 : ℝ) := by
      rw [← Real.rpow_add hX0]
      calc X = X ^ (1 : ℝ) := (Real.rpow_one X).symm
        _ ≤ X ^ (-(98 / 100) + 198 / 100 : ℝ) := hXr (by norm_num)
    rw [div_le_iff₀ (by positivity)]
    calc T ≤ X := hTX
      _ ≤ X ^ (-(98 / 100 : ℝ)) * X ^ (198 / 100 : ℝ) := hX198
      _ ≤ X ^ (-(98 / 100 : ℝ)) * (Y : ℝ) ^ 2 := by gcongr
  have hfac : 12 / (Y : ℝ) + T / (Y : ℝ) ^ 2 ≤ 13 * X ^ (-(98 / 100 : ℝ)) := by linarith
  have hL24 : L ≤ 1 + Real.log (24 * X) := by
    rw [hLdef, Real.log_mul (by norm_num) hX0.ne']
    have : 0 ≤ Real.log 24 := Real.log_nonneg (by norm_num)
    linarith
  have hpol : 52 * A * Real.exp (6 * mertensSecondUpperConst) * L ^ 8 ≤ X ^ (944 / 1000 : ℝ) := by
    refine le_trans ?_ hpoly8
    gcongr
  have hXsplit : X ^ (-(98 / 100 : ℝ)) * X ^ (36 / 1000 : ℝ) = X ^ (-(944 / 1000 : ℝ)) := by
    rw [← Real.rpow_add hX0]; norm_num
  have hXinv : X ^ (944 / 1000 : ℝ) * X ^ (-(944 / 1000 : ℝ)) = 1 := by
    rw [← Real.rpow_add hX0]; norm_num
  have hfac0 : 0 ≤ 12 / (Y : ℝ) + T / (Y : ℝ) ^ 2 := by
    have : 0 ≤ T := by linarith
    positivity
  calc A * (2 * ((12 / (Y : ℝ) + T / (Y : ℝ) ^ 2) * ∑ e ∈ (rangePrimorial 2 hs).divisors,
        (if ((e : ℕ) : ℝ) ≤ ((hs : ℕ) : ℝ) ^ (36 : ℝ) then 2 * 6 ^ e.primeFactors.card else 0)))
      ≤ A * (2 * ((13 * X ^ (-(98 / 100 : ℝ))) *
          (2 * X ^ (36 / 1000 : ℝ) * (Real.exp (6 * mertensSecondUpperConst) * L ^ 6)))) := by
        gcongr
    _ = 52 * A * Real.exp (6 * mertensSecondUpperConst) * L ^ 6 *
          (X ^ (-(98 / 100 : ℝ)) * X ^ (36 / 1000 : ℝ)) := by ring
    _ = 52 * A * Real.exp (6 * mertensSecondUpperConst) * L ^ 6 * X ^ (-(944 / 1000 : ℝ)) := by
        rw [hXsplit]
    _ ≤ 1 / L ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        have hXn : 0 < X ^ (-(944 / 1000 : ℝ)) := by positivity
        calc 52 * A * Real.exp (6 * mertensSecondUpperConst) * L ^ 6 * X ^ (-(944 / 1000 : ℝ)) * L ^ 2
            = (52 * A * Real.exp (6 * mertensSecondUpperConst) * L ^ 8) * X ^ (-(944 / 1000 : ℝ)) := by
              ring
          _ ≤ X ^ (944 / 1000 : ℝ) * X ^ (-(944 / 1000 : ℝ)) := by gcongr
          _ = 1 := hXinv

/-- **The sifted mean value theorem, eventual form.**  For coefficients `S` supported on
`(Y/2, 4Y]`, free of primes below `z > X^{1/10}` and bounded by `156`:
`∫_{-T}^{T} |∑ S(n) n^{-1-it}|² dt ≤ C (T/(Y log X) + (log X)^{-2})` for `1 ≤ T ≤ X`,
`X^{0.99} ≤ Y ≤ X`. -/
theorem eventually_integral_normSq_LSeries_rough_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in Filter.atTop, ∀ (S : ℕ → ℂ) (z Y : ℕ),
      X ^ (1 / 10 : ℝ) < z →
      (∀ n, S n ≠ 0 → 0 < n ∧ (Y : ℝ) / 2 < n ∧ (n : ℝ) ≤ 4 * Y) →
      (∀ n, S n ≠ 0 → ∀ p, p.Prime → p < z → ¬ p ∣ n) → (∀ n, ‖S n‖ ≤ 156) →
      X ^ (99 / 100 : ℝ) ≤ Y → (Y : ℝ) ≤ X → ∀ T : ℝ, 1 ≤ T → T ≤ X →
        ∫ t in Set.Icc (-T) T, ‖LSeries S (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 ≤
          C * (T / (Y * Real.log X) + 1 / Real.log X ^ 2) := by
  obtain ⟨c₀, hc₀, hE⟩ := exists_exp_mertensS_sub_sq_ge
  have hC0 : 0 < siftedMeanValueConst c₀ := by unfold siftedMeanValueConst; positivity
  refine ⟨siftedMeanValueConst c₀, hC0, ?_⟩
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (max 1 (40000 * mertensFirstConst)),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 1000)).eventually_ge_atTop 4,
    eventually_polylog_le_rpow 5 (C := Real.exp (4 * mertensSecondUpperConst)) (κ := 79 / 100)
      (by positivity) (by norm_num),
    eventually_polylog_le_rpow 8
      (C := 52 * (2 * Real.pi * (5 / 4) * 312 ^ 2) * Real.exp (6 * mertensSecondUpperConst))
      (κ := 944 / 1000) (by positivity) (by norm_num),
    Filter.eventually_gt_atTop (1 : ℝ)] with X hL h1000 hpoly5 hpoly8 hX1
  intro S z Y hzX hS hSrough hSb hYlo hYhi T hT hTX
  have hX0 : 0 < X := by linarith
  have hL1 : 1 ≤ Real.log X := le_trans (le_max_left _ _) hL
  have hXr : ∀ {a b : ℝ}, a ≤ b → X ^ a ≤ X ^ b := fun h => Real.rpow_le_rpow_of_exponent_le hX1.le h
  have hYpos : (0 : ℝ) < Y := lt_of_lt_of_le (by positivity) hYlo
  have hY1 : 1 ≤ Y := by
    exact_mod_cast (show (1 : ℝ) ≤ Y from le_trans (Real.one_le_rpow hX1.le (by norm_num)) hYlo)
  have h10 : (4 : ℝ) ≤ X ^ (1 / 10 : ℝ) := le_trans h1000 (hXr (by norm_num))
  have h1000z : X ^ (1 / 1000 : ℝ) < (z : ℝ) := lt_of_le_of_lt (hXr (by norm_num)) hzX
  set hs := ⌊X ^ (1 / 1000 : ℝ)⌋₊ with hsdef
  have hslog := half_log_le_log_floor_rpow (θ := 1 / 1000) hX1 h1000
  rw [← hsdef] at hslog
  have hs3 : 3 ≤ hs := by
    have : (3 : ℝ) ≤ X ^ (1 / 1000 : ℝ) := by linarith
    exact Nat.le_floor (by exact_mod_cast this)
  have hsz : hs < z := by
    have h1 : (hs : ℝ) ≤ X ^ (1 / 1000 : ℝ) := Nat.floor_le (by positivity)
    have : (hs : ℝ) < (z : ℝ) := lt_of_le_of_lt h1 h1000z
    exact_mod_cast this
  have hslog20 : 20 * mertensFirstConst ≤ Real.log hs := by
    have := le_max_right 1 (40000 * mertensFirstConst)
    have hm := mertensFirstConst_nonneg
    nlinarith
  set zd := ⌊X ^ (1 / 10 : ℝ)⌋₊ with hzddef
  have hzdlog := half_log_le_log_floor_rpow (θ := 1 / 10) hX1 h10
  rw [← hzddef] at hzdlog
  have hzd2 : 2 ≤ zd := Nat.le_floor (by norm_num; linarith)
  have hzdz : zd < z := by
    have h1 : (zd : ℝ) ≤ X ^ (1 / 10 : ℝ) := Nat.floor_le (by positivity)
    have : (zd : ℝ) < (z : ℝ) := lt_of_le_of_lt h1 hzX
    exact_mod_cast this
  have hzdlogpos : 0 < Real.log zd := by nlinarith
  set zr : ℝ := (hs : ℝ) ^ (36 : ℝ) with hzrdef
  have hsR : (3 : ℝ) ≤ hs := by exact_mod_cast hs3
  have hzr1 : 1 ≤ zr := Real.one_le_rpow (by linarith) (by norm_num)
  have hlev : ((hs : ℝ)) ^ (18 : ℝ) ≤ Real.sqrt zr := by
    rw [hzrdef, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]; norm_num
  have hmain := integral_normSq_LSeries_rough_le (T := T) hS hSrough hSb hY1 hT (by omega) hsz hlev
    hzr1 hslog20 hzdz (by omega) le_rfl hzd2 hzdlogpos
  refine hmain.trans ?_
  rw [show ((4 * Y : ℕ) : ℝ) = 4 * (Y : ℝ) by push_cast; ring]
  have hDg := harmanSource_diagonal_le hX1 hL1 h10 hpoly5 hYlo
  have hRem := harmanSource_remainder_le hX1 hL1 h1000 hT hTX hYlo hpoly8
  have hsave : c₀ * (Real.log X / 2000) ^ 2 ≤ (Real.exp (mertensS hs - mertensS 2)) ^ (2 : ℕ) := by
    have h := hE hs (by omega)
    have hls : Real.log X / 2000 ≤ Real.log hs := by linarith
    calc c₀ * (Real.log X / 2000) ^ 2 ≤ c₀ * Real.log hs ^ 2 := by gcongr
      _ ≤ _ := h
  have hK : (⌈12 * (Y : ℝ) / T⌉₊ : ℝ) ≤ 12 * Y / T + 1 := by
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 12 * (Y : ℝ) / T)
    linarith
  have hRm0 : 0 ≤ ∑ e ∈ (rangePrimorial 2 hs).divisors,
      (if ((e : ℕ) : ℝ) ≤ zr then (2 : ℝ) * 6 ^ e.primeFactors.card else 0) :=
    Finset.sum_nonneg fun e _ => by split_ifs <;> positivity
  exact siftedMeanValue_collect_le (L := Real.log X)
    (Dg := 2 * (4 * (Y : ℝ) - ((Y / 2 : ℕ) : ℝ)) / Real.log zd +
      ((zd * zd : ℕ) : ℝ) * (Real.exp (4 * mertensSecondUpperConst) * (Real.log zd) ^ (4 : ℝ)))
    (E2 := (Real.exp (mertensS hs - mertensS 2)) ^ (2 : ℕ)) (K := (⌈12 * (Y : ℝ) / T⌉₊ : ℝ))
    (Rm := ∑ e ∈ (rangePrimorial 2 hs).divisors,
      (if ((e : ℕ) : ℝ) ≤ zr then (2 : ℝ) * 6 ^ e.primeFactors.card else 0))
    hc₀ hT hYpos hL1 hDg hsave hK hRm0 hRem

/-- **The non-`U` input: the sifted mean value theorem for the Harman polynomial.**
`∫_{-T}^{T} |P(1+it)|² dt ≤ C (T/(Y log X) + (log X)^{-2})` for `1 ≤ T ≤ X`, `X^{0.99} ≤ Y ≤ X`,
uniformly in the Harman parameters `Q, D, E`. -/
theorem eventually_integral_normSq_LSeries_harmanSource_le :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ X : ℝ in Filter.atTop, ∀ (Q D E Y : ℕ), X ^ (99 / 100 : ℝ) ≤ Y →
      (Y : ℝ) ≤ X → ∀ T : ℝ, 1 ≤ T → T ≤ X →
        ∫ t in Set.Icc (-T) T,
            ‖LSeries (fun n => mtHarmanProposition22SourceAF (mtProposition22ZNat X) Q D E Y n)
              (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 ≤
          C * (T / (Y * Real.log X) + 1 / Real.log X ^ 2) := by
  obtain ⟨C, hC, hev⟩ := eventually_integral_normSq_LSeries_rough_le
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev, (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 11)).eventually_ge_atTop 5,
    Filter.eventually_gt_atTop (1 : ℝ)] with X hX h11 hX1
  intro Q D E Y hYlo hYhi T hT hTX
  have hX0 : 0 < X := by linarith
  set z := mtProposition22ZNat X with hzdef
  have hzR : X ^ (2 / 11 : ℝ) ≤ (z : ℝ) := Nat.le_ceil _
  have h110 : X ^ (1 / 10 : ℝ) < X ^ (2 / 11 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt hX1 (by norm_num)
  have h11' : X ^ (1 / 11 : ℝ) ≤ X ^ (2 / 11 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hX1.le (by norm_num)
  have hz2 : 2 ≤ z := by
    have : (2 : ℝ) ≤ (z : ℝ) := by linarith
    exact_mod_cast this
  have hz6 : 4 * Y < z ^ 6 := by
    have h12 : X ^ (12 / 11 : ℝ) ≤ (z : ℝ) ^ 6 := by
      calc X ^ (12 / 11 : ℝ) = (X ^ (2 / 11 : ℝ)) ^ 6 := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]; norm_num
        _ ≤ (z : ℝ) ^ 6 := pow_le_pow_left₀ (by positivity) hzR 6
    have h4X : 4 * X < X ^ (12 / 11 : ℝ) := by
      have hs : X ^ (12 / 11 : ℝ) = X ^ (1 / 11 : ℝ) * X := by
        rw [← Real.rpow_add_one hX0.ne']; norm_num
      rw [hs]; nlinarith
    have : (4 * Y : ℝ) < (z : ℝ) ^ 6 := by linarith
    exact_mod_cast this
  exact hX _ z Y (lt_of_lt_of_le h110 hzR)
    (fun n hn => mtRealIntervalAF_scaleSupported _ _ _ hn)
    (fun n hn p hp hpz => harmanSource_rough hn hp hpz) (norm_harmanSource_le hz2 hz6)
    hYlo hYhi T hT hTX

end

end RHTower.Sieve
