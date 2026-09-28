import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTwistedFourthMoments

/-!
# One height window of the Type-I case of Matomäki–Teräväinen (5.3)

On a set `E ⊆ [T/2, T]` where the amplifier satisfies `1 ≤ λ|𝓜|`, the arithmetic–geometric mean
inequality `λ|𝓜||F₁|²|F₂|² ≤ λ(ν|F₂|⁴|𝓜|² + ν⁻¹|F₁|⁴)/2`, optimised in `ν`, gives
`∫_E |F₁F₂|² ≤ λ √(I₁ I₂)` for any bounds `I₁ ≥ ∫|F₁|⁴`, `I₂ ≥ ∫|F₂|⁴|𝓜|²`.  The first is the mean
value theorem for `F₁²`; the second is the Deshouillers–Iwaniec bound against the amplifier.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **The arithmetic–geometric mean split.** -/
theorem setIntegral_normSq_mul_le_sqrt {F₁ F₂ G : ℝ → ℂ} (hF₁ : Continuous F₁)
    (hF₂ : Continuous F₂) (hG : Continuous G) {E : Set ℝ} (hE : MeasurableSet E) {a b lam I₁ I₂ : ℝ}
    (hab : a ≤ b) (hEab : E ⊆ Set.Icc a b) (hlam0 : 0 ≤ lam) (hlam : ∀ t ∈ E, 1 ≤ lam * ‖G t‖)
    (hI₁ : (∫ t in a..b, ‖F₁ t‖ ^ (4 : ℕ)) ≤ I₁)
    (hI₂ : (∫ t in a..b, ‖F₂ t‖ ^ (4 : ℕ) * ‖G t‖ ^ (2 : ℕ)) ≤ I₂) (hI₁0 : 0 < I₁) (hI₂0 : 0 < I₂) :
    ∫ t in E, ‖F₁ t * F₂ t‖ ^ (2 : ℕ) ≤ lam * Real.sqrt (I₁ * I₂) := by
  set ν : ℝ := Real.sqrt (I₁ / I₂) with hν
  have hν0 : 0 < ν := Real.sqrt_pos.2 (div_pos hI₁0 hI₂0)
  set g : ℝ → ℝ := fun t => lam * ((ν * (‖F₂ t‖ ^ (4 : ℕ) * ‖G t‖ ^ (2 : ℕ)) +
    ν⁻¹ * ‖F₁ t‖ ^ (4 : ℕ)) / 2) with hg
  have hgc : Continuous g := by
    rw [hg]
    exact continuous_const.mul (((continuous_const.mul ((hF₂.norm.pow 4).mul (hG.norm.pow 2))).add
      (continuous_const.mul (hF₁.norm.pow 4))).div_const 2)
  have hLint : IntegrableOn (fun t => ‖F₁ t * F₂ t‖ ^ (2 : ℕ)) E :=
    (((hF₁.mul hF₂).norm).pow 2).integrableOn_Icc.mono_set hEab
  have hgint : IntegrableOn g (Set.Icc a b) := hgc.integrableOn_Icc
  have hpt : ∀ t ∈ E, ‖F₁ t * F₂ t‖ ^ (2 : ℕ) ≤ g t := by
    intro t ht
    have h1 := hlam t ht
    set x := ‖F₂ t‖ ^ (2 : ℕ) * ‖G t‖ with hx
    set y := ‖F₁ t‖ ^ (2 : ℕ) with hy
    have hx0 : 0 ≤ x := by positivity
    have hy0 : 0 ≤ y := by positivity
    have hamgm : x * y ≤ (ν * x ^ 2 + ν⁻¹ * y ^ 2) / 2 := by
      have : 0 ≤ (ν * x - y) ^ 2 / ν := by positivity
      have hexp : (ν * x ^ 2 + ν⁻¹ * y ^ 2) / 2 - x * y = (ν * x - y) ^ 2 / (2 * ν) := by
        field_simp; ring
      have : 0 ≤ (ν * x - y) ^ 2 / (2 * ν) := by positivity
      linarith
    have hxy : ‖F₁ t * F₂ t‖ ^ (2 : ℕ) ≤ lam * (x * y) := by
      rw [hx, hy, norm_mul, mul_pow]
      have hG0 : 0 ≤ ‖F₂ t‖ ^ (2 : ℕ) * ‖F₁ t‖ ^ (2 : ℕ) := by positivity
      calc ‖F₁ t‖ ^ 2 * ‖F₂ t‖ ^ 2 ≤ ‖F₁ t‖ ^ 2 * ‖F₂ t‖ ^ 2 * (lam * ‖G t‖) :=
            le_mul_of_one_le_right (by positivity) h1
        _ = lam * (‖F₂ t‖ ^ 2 * ‖G t‖ * ‖F₁ t‖ ^ 2) := by ring
    calc ‖F₁ t * F₂ t‖ ^ (2 : ℕ) ≤ lam * (x * y) := hxy
      _ ≤ lam * ((ν * x ^ 2 + ν⁻¹ * y ^ 2) / 2) := mul_le_mul_of_nonneg_left hamgm hlam0
      _ = g t := by rw [hg, hx, hy]; ring
  have hstep1 : ∫ t in E, ‖F₁ t * F₂ t‖ ^ (2 : ℕ) ≤ ∫ t in E, g t :=
    setIntegral_mono_on hLint (hgint.mono_set hEab) hE hpt
  have hg0 : ∀ t, 0 ≤ g t := fun t => by rw [hg]; positivity
  have hstep2 : ∫ t in E, g t ≤ ∫ t in Set.Icc a b, g t :=
    setIntegral_mono_set hgint (Filter.Eventually.of_forall fun t => hg0 t)
      (Filter.Eventually.of_forall hEab)
  have hIcc : ∫ t in Set.Icc a b, g t = ∫ t in a..b, g t := by
    rw [intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]
  have hint₁ : IntervalIntegrable (fun t => ‖F₁ t‖ ^ (4 : ℕ)) volume a b :=
    (hF₁.norm.pow 4).intervalIntegrable _ _
  have hint₂ : IntervalIntegrable (fun t => ‖F₂ t‖ ^ (4 : ℕ) * ‖G t‖ ^ (2 : ℕ)) volume a b :=
    ((hF₂.norm.pow 4).mul (hG.norm.pow 2)).intervalIntegrable _ _
  have hval : ∫ t in a..b, g t = lam * (((ν * ∫ t in a..b, ‖F₂ t‖ ^ (4 : ℕ) * ‖G t‖ ^ (2 : ℕ)) +
      ν⁻¹ * ∫ t in a..b, ‖F₁ t‖ ^ (4 : ℕ)) / 2) := by
    rw [hg]
    simp only
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_div,
      intervalIntegral.integral_add (hint₂.const_mul _) (hint₁.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hfinal : lam * (((ν * ∫ t in a..b, ‖F₂ t‖ ^ (4 : ℕ) * ‖G t‖ ^ (2 : ℕ)) +
      ν⁻¹ * ∫ t in a..b, ‖F₁ t‖ ^ (4 : ℕ)) / 2) ≤ lam * Real.sqrt (I₁ * I₂) := by
    refine mul_le_mul_of_nonneg_left ?_ hlam0
    have hνI : ν * I₂ = Real.sqrt (I₁ * I₂) := by
      have h : Real.sqrt (I₁ * I₂) = Real.sqrt (I₁ / I₂) * I₂ := by
        rw [show I₁ * I₂ = I₁ / I₂ * I₂ ^ 2 by field_simp, Real.sqrt_mul (div_pos hI₁0 hI₂0).le,
          Real.sqrt_sq hI₂0.le]
      rw [hν, h]
    have hνI' : ν⁻¹ * I₁ = Real.sqrt (I₁ * I₂) := by
      have hsq : Real.sqrt (I₁ / I₂) * Real.sqrt (I₁ * I₂) = I₁ := by
        rw [← Real.sqrt_mul (div_pos hI₁0 hI₂0).le]
        rw [show I₁ / I₂ * (I₁ * I₂) = I₁ ^ 2 by field_simp]
        exact Real.sqrt_sq hI₁0.le
      rw [hν]
      field_simp
      linarith
    have h2 : ν * ∫ t in a..b, ‖F₂ t‖ ^ (4 : ℕ) * ‖G t‖ ^ (2 : ℕ) ≤ ν * I₂ :=
      mul_le_mul_of_nonneg_left hI₂ hν0.le
    have h1 : ν⁻¹ * ∫ t in a..b, ‖F₁ t‖ ^ (4 : ℕ) ≤ ν⁻¹ * I₁ :=
      mul_le_mul_of_nonneg_left hI₁ (inv_nonneg.2 hν0.le)
    linarith
  calc ∫ t in E, ‖F₁ t * F₂ t‖ ^ (2 : ℕ) ≤ ∫ t in E, g t := hstep1
    _ ≤ ∫ t in Set.Icc a b, g t := hstep2
    _ = ∫ t in a..b, g t := hIcc
    _ = _ := hval
    _ ≤ _ := hfinal

/-- The polylogarithm exponent `2^{2(2K+1)} − 1` of the fourth-moment bound. -/
def fourthMomentExponent (K : ℕ) : ℕ := 2 ^ (2 * (2 * K + 1)) - 1

/-- The fourth-moment bound `800 L^e (1 + T/M²)`, `L = 1 + log(16M²)`, `e = 2^{2(2K+1)} − 1`. -/
def fourthMomentBound (K : ℕ) (M T : ℝ) : ℝ :=
  800 * (1 + Real.log (16 * M ^ 2)) ^ fourthMomentExponent K * (1 + T / M ^ 2)

theorem fourthMomentBound_pos (K : ℕ) {M T : ℝ} (hM : 1 / 2 ≤ M) (hT : 0 ≤ T) :
    0 < fourthMomentBound K M T := by
  have hM0 : 0 < M := by linarith
  have hL : 0 < 1 + Real.log (16 * M ^ 2) := by
    have := Real.log_nonneg (by nlinarith : (1 : ℝ) ≤ 16 * M ^ 2); linarith
  unfold fourthMomentBound
  have h1 : 0 < 1 + T / M ^ 2 := by positivity
  exact mul_pos (mul_pos (by norm_num) (pow_pos hL _)) h1

/-- **The fourth moment of a dyadic divisor-bounded polynomial** (mean value theorem for its
square): for `F` supported on `(M, 2M]` with `|F(n)| ≤ d(n)^K`,
`∫_{-T}^{T} |∑ F(n) n^{-1-it}|⁴ ≤ 800 L^e (1 + T/M²)`, `L = 1 + log(16M²)`, `e = 2^{2(2K+1)} − 1`. -/
theorem integral_normSq_perronPoly_fourth_le (F : ArithmeticFunction ℂ) {M T : ℝ} {K : ℕ}
    (hM : 1 / 2 ≤ M) (hT : 1 ≤ T) (hF : MTRealScaleSupported F M (2 * M))
    (hFb : MTUniformDivisorBounded K fun n => F n) :
    (∫ t in Set.Icc (-T) T, ‖perronPoly (fun n => F n) ⌈2 * M⌉₊ 1 t‖ ^ (4 : ℕ)) ≤
      fourthMomentBound K M T := by
  classical
  unfold fourthMomentBound fourthMomentExponent
  set K₀ := ⌈2 * M⌉₊ with hK₀
  have hM0 : 0 < M := by linarith
  have hK₀le : (K₀ : ℝ) ≤ 4 * M := by
    have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ 2 * M)
    rw [hK₀]; linarith
  have hK₀1 : 1 ≤ K₀ := Nat.one_le_iff_ne_zero.2 (by rw [hK₀]; positivity)
  have hsuppF : ∀ n, F n ≠ 0 → n ∈ Finset.Icc 1 K₀ := fun n hn => by
    obtain ⟨hn0, _, hhi⟩ := hF hn
    exact Finset.mem_Icc.2 ⟨hn0, Nat.cast_le.1 (hhi.trans (Nat.le_ceil _)) |> fun h => by
      exact_mod_cast h⟩
  obtain ⟨hsq, hpoly⟩ := perronPoly_pow_arithmeticFunction F hsuppF 1 0 2
  have hpt : ∀ t, ‖perronPoly (fun n => F n) K₀ 1 t‖ ^ (4 : ℕ) =
      ‖LSeries (fun n => (F ^ 2) n) (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ (2 : ℕ) := by
    intro t
    have h2 := (perronPoly_pow_arithmeticFunction F hsuppF 1 t 2).2
    rw [← perronPoly_eq_LSeries_of_support hsq, h2, norm_pow, ← pow_mul]
  have hcoef : MTUniformDivisorBounded (2 * K + 1) fun n => (F ^ 2) n := by
    have := hFb.arithmeticFunction_mul hFb
    rw [← sq] at this
    simpa [two_mul] using this
  have hsupp2 : MTRealScaleSupported (F ^ (1 + 1)) (M ^ (1 + 1)) ((2 * M) ^ (1 + 1)) :=
    @MTRealScaleSupported.pow_succ _ _ _ hF hM0.le 1
  simp_rw [hpt]
  have hs0 : (0 : ℕ) ∉ Finset.Icc 1 (K₀ ^ 2) := by simp
  refine (integral_Icc_normSq_LSeries_le_general_affine hs0 hsq 1 hT).trans ?_
  set e := 2 ^ (2 * (2 * K + 1)) - 1 with he
  set L := 1 + Real.log (16 * M ^ 2) with hL
  have hN : 1 ≤ K₀ ^ 2 := Nat.one_le_pow _ _ hK₀1
  have hNle : ((K₀ ^ 2 : ℕ) : ℝ) ≤ 16 * M ^ 2 := by push_cast; nlinarith
  have hsum := sum_card_divisors_pow_le_polylog (2 * (2 * K + 1)) (K₀ ^ 2) hN
  have hlogN : 1 + Real.log ((K₀ ^ 2 : ℕ) : ℝ) ≤ L := by
    rw [hL]; gcongr
  have hlog0 : 0 ≤ 1 + Real.log ((K₀ ^ 2 : ℕ) : ℝ) := by
    have := Real.log_nonneg (by exact_mod_cast hN : (1 : ℝ) ≤ ((K₀ ^ 2 : ℕ) : ℝ)); linarith
  have hsum' : ∑ n ∈ Finset.Icc 1 (K₀ ^ 2), ((n.divisors.card : ℝ) ^ (2 * (2 * K + 1))) ≤
      16 * M ^ 2 * L ^ e := by
    refine hsum.trans ?_
    exact mul_le_mul hNle (pow_le_pow_left₀ hlog0 hlogN _) (by positivity) (by positivity)
  -- each coefficient term
  have hterm : ∀ n ∈ Finset.Icc 1 (K₀ ^ 2),
      ‖(F ^ 2) n * ((((n : ℝ) ^ (-(1 : ℝ)) : ℝ)) : ℂ)‖ ^ 2 ≤
        (n.divisors.card : ℝ) ^ (2 * (2 * K + 1)) / M ^ 4 := by
    intro n hn
    have hn1 := (Finset.mem_Icc.1 hn).1
    by_cases hc : (F ^ 2) n = 0
    · rw [hc, zero_mul, norm_zero, show (0 : ℝ) ^ 2 = 0 by norm_num]; positivity
    obtain ⟨_, hlo, _⟩ := hsupp2 hc
    have hb := hcoef (by omega : 0 < n)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), Real.rpow_neg_one, mul_pow]
    have hlo' : M ^ 2 < (n : ℝ) := by simpa using hlo
    calc ‖(F ^ 2) n‖ ^ 2 * ((n : ℝ)⁻¹) ^ 2 ≤ ((n.divisors.card : ℝ) ^ (2 * K + 1)) ^ 2 *
          ((M ^ 2)⁻¹) ^ 2 := by
          gcongr
      _ = (n.divisors.card : ℝ) ^ (2 * (2 * K + 1)) / M ^ 4 := by
          rw [← pow_mul, mul_comm (2 * K + 1) 2]; field_simp
  have hterm' : ∀ n ∈ Finset.Icc 1 (K₀ ^ 2),
      (n : ℝ) * ‖(F ^ 2) n * ((((n : ℝ) ^ (-(1 : ℝ)) : ℝ)) : ℂ)‖ ^ 2 ≤
        (n.divisors.card : ℝ) ^ (2 * (2 * K + 1)) / M ^ 2 := by
    intro n hn
    have hn1 := (Finset.mem_Icc.1 hn).1
    by_cases hc : (F ^ 2) n = 0
    · rw [hc, zero_mul, norm_zero, show (0 : ℝ) ^ 2 = 0 by norm_num, mul_zero]; positivity
    obtain ⟨_, hlo, hhi⟩ := hsupp2 hc
    have hb := hcoef (by omega : 0 < n)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), Real.rpow_neg_one, mul_pow]
    have hlo' : M ^ 2 < (n : ℝ) := by simpa using hlo
    have hd : (0 : ℝ) ≤ (n.divisors.card : ℝ) ^ (2 * (2 * K + 1)) := by positivity
    calc (n : ℝ) * (‖(F ^ 2) n‖ ^ 2 * ((n : ℝ)⁻¹) ^ 2)
        = ‖(F ^ 2) n‖ ^ 2 * (n : ℝ)⁻¹ := by field_simp
      _ ≤ ((n.divisors.card : ℝ) ^ (2 * K + 1)) ^ 2 * (M ^ 2)⁻¹ := by
          gcongr
      _ = (n.divisors.card : ℝ) ^ (2 * (2 * K + 1)) / M ^ 2 := by
          rw [← pow_mul, mul_comm (2 * K + 1) 2]; field_simp
  have hConst : generalMeanSquareConst (fun n => (F ^ 2) n) (Finset.Icc 1 (K₀ ^ 2)) 1 ≤
      5 * Real.pi * Real.exp 1 * (16 * L ^ e) := by
    rw [generalMeanSquareConst]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ∑ n ∈ Finset.Icc 1 (K₀ ^ 2), (n : ℝ) * ‖(F ^ 2) n * ((((n : ℝ) ^ (-(1 : ℝ)) : ℝ)) : ℂ)‖ ^ 2
        ≤ ∑ n ∈ Finset.Icc 1 (K₀ ^ 2), (n.divisors.card : ℝ) ^ (2 * (2 * K + 1)) / M ^ 2 :=
          Finset.sum_le_sum hterm'
      _ = (∑ n ∈ Finset.Icc 1 (K₀ ^ 2), (n.divisors.card : ℝ) ^ (2 * (2 * K + 1))) / M ^ 2 := by
          rw [Finset.sum_div]
      _ ≤ 16 * M ^ 2 * L ^ e / M ^ 2 := by gcongr
      _ = 16 * L ^ e := by field_simp
  have hRate : generalMeanSquareRate (fun n => (F ^ 2) n) (Finset.Icc 1 (K₀ ^ 2)) 1 ≤
      5 * Real.pi / 2 * (16 * L ^ e / M ^ 2) := by
    rw [generalMeanSquareRate]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ∑ n ∈ Finset.Icc 1 (K₀ ^ 2), ‖(F ^ 2) n * ((((n : ℝ) ^ (-(1 : ℝ)) : ℝ)) : ℂ)‖ ^ 2
        ≤ ∑ n ∈ Finset.Icc 1 (K₀ ^ 2), (n.divisors.card : ℝ) ^ (2 * (2 * K + 1)) / M ^ 4 :=
          Finset.sum_le_sum hterm
      _ = (∑ n ∈ Finset.Icc 1 (K₀ ^ 2), (n.divisors.card : ℝ) ^ (2 * (2 * K + 1))) / M ^ 4 := by
          rw [Finset.sum_div]
      _ ≤ 16 * M ^ 2 * L ^ e / M ^ 4 := by gcongr
      _ = 16 * L ^ e / M ^ 2 := by field_simp
  have hLe0 : 0 ≤ L ^ e := by
    have : 0 ≤ L := by
      rw [hL]; have := Real.log_nonneg (by nlinarith : (1 : ℝ) ≤ 16 * M ^ 2); linarith
    positivity
  have hpi : Real.pi ≤ 3.15 := by linarith [Real.pi_lt_d2]
  have he1 : Real.exp 1 ≤ 2.72 := by linarith [Real.exp_one_lt_d9]
  have hT0 : 0 ≤ T := by linarith
  calc generalMeanSquareConst (fun n => (F ^ 2) n) (Finset.Icc 1 (K₀ ^ 2)) 1 +
        generalMeanSquareRate (fun n => (F ^ 2) n) (Finset.Icc 1 (K₀ ^ 2)) 1 * T
      ≤ 5 * Real.pi * Real.exp 1 * (16 * L ^ e) + 5 * Real.pi / 2 * (16 * L ^ e / M ^ 2) * T := by
        gcongr
    _ ≤ 800 * L ^ e * (1 + T / M ^ 2) := by
        have h1 : 5 * Real.pi * Real.exp 1 * (16 * L ^ e) ≤ 800 * L ^ e := by
          have hpe : Real.pi * Real.exp 1 ≤ 3.15 * 2.72 :=
            mul_le_mul hpi he1 (Real.exp_pos 1).le (by norm_num)
          have h60 : 5 * Real.pi * Real.exp 1 ≤ 50 := by
            calc 5 * Real.pi * Real.exp 1 = 5 * (Real.pi * Real.exp 1) := by ring
              _ ≤ 5 * (3.15 * 2.72) := by gcongr
              _ ≤ 50 := by norm_num
          have hLe' : 0 ≤ 16 * L ^ e := by positivity
          calc 5 * Real.pi * Real.exp 1 * (16 * L ^ e) ≤ 50 * (16 * L ^ e) :=
                mul_le_mul_of_nonneg_right h60 hLe'
            _ ≤ 800 * L ^ e := by nlinarith only [hLe']
        have h2 : 5 * Real.pi / 2 * (16 * L ^ e / M ^ 2) * T ≤ 800 * L ^ e * (T / M ^ 2) := by
          have : 5 * Real.pi / 2 * 16 ≤ 800 := by linarith only [hpi]
          have hq : 0 ≤ L ^ e * (T / M ^ 2) := by positivity
          calc 5 * Real.pi / 2 * (16 * L ^ e / M ^ 2) * T = (5 * Real.pi / 2 * 16) * (L ^ e * (T / M ^ 2)) := by
                ring
            _ ≤ 800 * (L ^ e * (T / M ^ 2)) := mul_le_mul_of_nonneg_right this hq
            _ = _ := by ring
        nlinarith

/-- The short Type-I factor `∑_{m ∼ M₁} α_m m^{-1-it}`. -/
def mtTypeIShortFactor {X Y δ ε : ℝ} (data : MTTypeIPieceData X Y δ ε) (t : ℝ) : ℂ :=
  perronPoly (fun n => mtRealIntervalAF data.α data.M₁ (2 * data.M₁) n) ⌈2 * data.M₁⌉₊ 1 t

/-- The long Type-I factor `∑_{M₂ < m ≤ (1+δ)M₂} m^{-1-it}`. -/
def mtTypeILongFactor {X Y δ ε : ℝ} (data : MTTypeIPieceData X Y δ ε) (t : ℝ) : ℂ :=
  perronPoly (fun n => mtRealIntervalAF (fun _ => (1 : ℂ)) data.M₂ ((1 + δ) * data.M₂) n)
    ⌈(1 + δ) * data.M₂⌉₊ 1 t

theorem continuous_mtTypeIShortFactor {X Y δ ε : ℝ} (data : MTTypeIPieceData X Y δ ε) :
    Continuous (mtTypeIShortFactor data) := continuous_perronPoly _ _ 1

theorem continuous_mtTypeILongFactor {X Y δ ε : ℝ} (data : MTTypeIPieceData X Y δ ε) :
    Continuous (mtTypeILongFactor data) := continuous_perronPoly _ _ 1

/-- **One height window of the Type-I case, given Deshouillers–Iwaniec.** -/
theorem setIntegral_typeI_window_le (hDI : MTDeshouillersIwaniecBound) {η : ℝ} (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ {X Y δ ε : ℝ} (data : MTTypeIPieceData X Y δ ε)
      {B : Finset ℕ} {P εU T : ℝ} {k K : ℕ} {E : Set ℝ},
      MTUniformDivisorBounded 5 data.α → 1 / 2 ≤ data.M₁ → 0 ≤ δ →
      1 ≤ ⌊data.M₂⌋₊ → ⌊data.M₂⌋₊ < ⌊(1 + δ) * data.M₂⌋₊ →
      ⌊(1 + δ) * data.M₂⌋₊ ≤ 2 * ⌊data.M₂⌋₊ →
      (∀ p ∈ B, p.Prime) → (∀ p ∈ B, P < p ∧ (p : ℝ) ≤ 2 * P) → 2 ≤ P → 1 ≤ k →
      (2 * P) ^ k ≤ K → 2 ≤ T → (2 * P) ^ k ≤ T ^ (1 / 5 : ℝ) → 0 ≤ εU →
      MeasurableSet E → E ⊆ Set.Icc (T / 2) T →
      (∀ t ∈ E, P ^ (-εU / 10) ≤
        ‖∑ p ∈ B, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖) →
      ∫ t in E, ‖mtTypeIShortFactor data t * mtTypeILongFactor data t‖ ^ (2 : ℕ) ≤
        (k.factorial : ℝ) * (P ^ k) ^ (εU / 10) *
          Real.sqrt (fourthMomentBound 5 data.M₁ T *
            ((k + 1) * C * T ^ η * (16 * T / (((⌊data.M₂⌋₊ : ℕ) : ℝ) ^ (2 : ℕ) * P ^ k) +
                4 / (T ^ (3 : ℕ) * P ^ k)) * (2 * (P + 1) ^ k / (P ^ k * k.factorial)))) := by
  obtain ⟨C, hC, hamp⟩ := integral_unitBlock_fourth_amplifier_le hDI hη
  refine ⟨C, hC, ?_⟩
  intro X Y δ ε data B P εU T k K E hα hM₁ hδ hN1 hNN' hN' hBp hB hP hk hK hT hT5 hεU hEm hET hS
  have hT0 : 0 < T := by linarith
  have hP1 : 1 ≤ P := by linarith
  -- the long factor is the natural unit block
  have hlong : ∀ t, mtTypeILongFactor data t =
      mtWattUnitBlock ⌊data.M₂⌋₊ ⌊(1 + δ) * data.M₂⌋₊ t := by
    intro t
    have hM₂0 : 0 ≤ data.M₂ := data.M₂_pos.le
    exact perronPoly_mtRealUnitInterval_eq_mtWattUnitBlock hM₂0 (by positivity) t
  -- the amplifier lower bound, square-rooted
  set G : ℝ → ℂ := fun t => perronPoly (primeSetAmplifierCoeff B k) K 1 t with hGdef
  have hlam : ∀ t ∈ E, 1 ≤ (k.factorial : ℝ) * (P ^ k) ^ (εU / 10) * ‖G t‖ := by
    intro t ht
    have h := one_le_amplifier_perronPoly (X := (K : ℝ)) hBp hP1 hB hk hK (hS t ht)
    rw [Nat.floor_natCast] at h
    have hx : 0 ≤ (k.factorial : ℝ) * (P ^ k) ^ (εU / 10) * ‖G t‖ := by positivity
    have hsq : ((k.factorial : ℝ) * (P ^ k) ^ (εU / 10) * ‖G t‖) ^ 2 =
        (k.factorial : ℝ) ^ 2 * (P ^ k) ^ (εU / 5) * ‖G t‖ ^ 2 := by
      have ha : ((P ^ k) ^ (εU / 10)) ^ 2 = (P ^ k) ^ (εU / 5) := by
        rw [← Real.rpow_mul_natCast (by positivity)]
        norm_num [div_mul_eq_mul_div]
        ring_nf
      rw [mul_pow, mul_pow, ha]
    nlinarith [hsq, h]
  -- the fourth moment of the short factor
  have hshortSupp : MTRealScaleSupported (mtRealIntervalAF data.α data.M₁ (2 * data.M₁))
      data.M₁ (2 * data.M₁) := mtRealIntervalAF_scaleSupported _ _ _
  have hI₁ : (∫ t in (T / 2)..T, ‖mtTypeIShortFactor data t‖ ^ (4 : ℕ)) ≤
      fourthMomentBound 5 data.M₁ T := by
    have hfull : (∫ t in Set.Icc (-T) T, ‖mtTypeIShortFactor data t‖ ^ (4 : ℕ)) ≤
        fourthMomentBound 5 data.M₁ T :=
      integral_normSq_perronPoly_fourth_le (mtRealIntervalAF data.α data.M₁ (2 * data.M₁))
        hM₁ (by linarith : (1 : ℝ) ≤ T) hshortSupp (hα.realInterval _ _)
    have hsub : (∫ t in (T / 2)..T, ‖mtTypeIShortFactor data t‖ ^ (4 : ℕ)) ≤
        ∫ t in Set.Icc (-T) T, ‖mtTypeIShortFactor data t‖ ^ (4 : ℕ) := by
      rw [intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc]
      exact setIntegral_mono_set ((continuous_mtTypeIShortFactor data).norm.pow 4).integrableOn_Icc
        (Filter.Eventually.of_forall fun t => by positivity)
        (Filter.Eventually.of_forall (Set.Icc_subset_Icc (by linarith) le_rfl))
    exact hsub.trans hfull
  -- the amplified Deshouillers–Iwaniec bound for the long factor
  have hI₂ : (∫ t in (T / 2)..T, ‖mtTypeILongFactor data t‖ ^ (4 : ℕ) * ‖G t‖ ^ (2 : ℕ)) ≤
      (k + 1) * C * T ^ η * (16 * T / (((⌊data.M₂⌋₊ : ℕ) : ℝ) ^ (2 : ℕ) * P ^ k) +
        4 / (T ^ (3 : ℕ) * P ^ k)) * (2 * (P + 1) ^ k / (P ^ k * k.factorial)) := by
    simp_rw [hlong]
    exact hamp hBp hB hP hk hK hN1 hNN' hN' hT hT5
  have hPk : 0 < P ^ k := by positivity
  have hI₁0 : 0 < fourthMomentBound 5 data.M₁ T := fourthMomentBound_pos 5 hM₁ hT0.le
  have hI₂0 : 0 < (k + 1) * C * T ^ η * (16 * T / (((⌊data.M₂⌋₊ : ℕ) : ℝ) ^ (2 : ℕ) * P ^ k) +
      4 / (T ^ (3 : ℕ) * P ^ k)) * (2 * (P + 1) ^ k / (P ^ k * k.factorial)) := by
    have hN : (0 : ℝ) < ((⌊data.M₂⌋₊ : ℕ) : ℝ) := by exact_mod_cast hN1
    have hf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
    positivity
  exact setIntegral_normSq_mul_le_sqrt (continuous_mtTypeIShortFactor data)
    (continuous_mtTypeILongFactor data) (continuous_perronPoly _ _ 1) hEm (by linarith) hET
    (by positivity) hlam hI₁ hI₂ hI₁0 hI₂0

end

end RHTower.Sieve
