import GaloisForLFunctions.ArithmeticCorrelationGeometry.SuccessorCorrelationsArePureGaugeCharge
import GaloisForLFunctions.TransThresholdPairCorrelation.CoalescentPrimeReductionAndParitySieve

/-!
# The coalescent surplus is pure gauge charge

The signed close-prime-pair statistic `primeCoalSum` of the bandwidth-`4/3` certificate
(`TransThresholdPairCorrelation`) is a pair form over distinct primes `n ≠ m` with
`|log(n/m)| ≤ θ₀`. Twisting the primes by a gauge point `x` multiplies the pair `(n, m)` by
`χ_x(n) χ̄_x(m)` (`twistedPrimeCoalSum`); the gauge point `0` is the actual statistic
(`twistedPrimeCoalSum_zero`). Every twist has the same prime moduli and the same value on every
multiplicatively coincident monomial as the primes themselves.

* **Prime pairs have distinct ratios** (`eq_of_prime_cross_mul_eq`). For primes `n ≠ m` and
  `n' ≠ m'`, `n m' = m n'` forces `(n, m) = (n', m')`.
* **Mean zero and diagonal variance** (`integral_twistedPrimeCoalSum`,
  `integral_normSq_twistedPrimeCoalSum`). The gauge mean of the twisted statistic vanishes, and its
  gauge mean square is the sum of the squared pair weights.
* **The variance is small** (`integral_normSq_twistedPrimeCoalSum_le`). With `|g| ≤ L` and
  `|Ω̂| ≤ M₀`, the gauge mean square is at most `(LM₀/π)² · 8 θ₀ (log X)⁴ (1 + log X)`. At bandwidth
  `4/3` and aperture `θ₀ = T^{−1+η}` the normalised surplus has gauge mean square
  `≤ (1536/π²)(log T)³ T^{1+η}` (`eventually_integral_normSq_twistedPrimeCoalescentSurplus_le`), which
  is `o(N(T, 2T)²)` for every `η < 1` (`twistedPrimeCoalescentSurplus_meanSquare_isLittleO`).
* **Almost every twist meets every budget** (`tendsto_gaugeHaar_large_twistedSurplus`). For every
  `δ > 0` the Haar measure of the twists whose surplus exceeds `δ N(T, 2T)` tends to zero.

So the budget `β < 5/36` of the open problem holds, with `β = 0`, for Haar-almost every gauge twist
of the primes, and these twists share every multiplicative statistic of the primes. Whatever the
actual surplus is, it is a property of the single gauge point `0`: its proof must use arithmetic
that distinguishes the primes from their twists — the additive (singular-series) structure of
prime pairs, not their multiplicative statistics.
-/

open MeasureTheory Finset Filter Topology
open scoped ComplexConjugate ArithmeticFunction

open Zeta23 Zeta23.PrimeSide
open RHTower (params43 paramsValidFam_params43 eventually_l_bounds localHypsCoreW_eventually_fam
  eventually_log_pow_rpow_le)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCorrelationGeometry

open HTGeometry TransThresholdPairCorrelation

/-! ### Distinct prime pairs have distinct ratios -/

/-- **Prime pairs have distinct ratios.** -/
theorem eq_of_prime_cross_mul_eq {n m n' m' : ℕ} (hn : n.Prime) (hm : m.Prime) (hn' : n'.Prime)
    (hnm : n ≠ m) (h : n * m' = m * n') : n = n' ∧ m = m' := by
  have hdvd : n ∣ m * n' := ⟨m', h.symm⟩
  rcases (Nat.Prime.dvd_mul hn).mp hdvd with hd | hd
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hn hm).mp hd) hnm
  · have hnn' := (Nat.prime_dvd_prime_iff_eq hn hn').mp hd
    subst hnn'
    refine ⟨rfl, ?_⟩
    have := Nat.eq_of_mul_eq_mul_left hn.pos (h.trans (mul_comm m n))
    exact this.symm

@[simp] theorem twist_zero (n : ℕ) : twist 0 n = 1 := by
  rw [twist, torusCharacter_apply]
  exact Finset.prod_eq_one fun i _ => by
    simp only [Pi.zero_apply]
    exact fourier_eval_zero _

/-! ### The twisted coalescent statistic -/

/-- The weight of the pair `(n, m)` in `primeCoalSum`. -/
def coalWeight (Ω g : ℝ → ℝ) (θ₀ : ℝ) (n m : ℕ) : ℝ :=
  if n.Prime ∧ m.Prime ∧ n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀
  then (1 / Real.pi) * (acoef n * acoef m * g (Real.log m) *
    cosTransform Ω (Real.log n - Real.log m)) else 0

/-- The twisted prime coalescent pair sum: each pair carries the gauge character
`χ_x(n) χ̄_x(m)`. -/
def twistedPrimeCoalSum (Ω g : ℝ → ℝ) (X θ₀ : ℝ) (x : GaugeTorus) : ℂ :=
  ∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
    (coalWeight Ω g θ₀ n m : ℂ) * (twist x n * conj (twist x m))

theorem primeCoalSum_eq_sum_coalWeight (Ω g : ℝ → ℝ) (X θ₀ : ℝ) :
    primeCoalSum Ω g X θ₀ = ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, coalWeight Ω g θ₀ n m := by
  rw [primeCoalSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coalWeight]
  split_ifs <;> simp

/-- **The gauge point `0` is the actual statistic.** -/
theorem twistedPrimeCoalSum_zero (Ω g : ℝ → ℝ) (X θ₀ : ℝ) :
    twistedPrimeCoalSum Ω g X θ₀ 0 = (primeCoalSum Ω g X θ₀ : ℂ) := by
  rw [twistedPrimeCoalSum, primeCoalSum_eq_sum_coalWeight]
  push_cast
  simp

theorem twistedPrimeCoalSum_eq_pairForm (Ω g : ℝ → ℝ) (X θ₀ : ℝ) (x : GaugeTorus) :
    twistedPrimeCoalSum Ω g X θ₀ x =
      pairForm (primeRange X ×ˢ primeRange X) (fun q => (coalWeight Ω g θ₀ q.1 q.2 : ℂ)) x := by
  rw [twistedPrimeCoalSum, pairForm, Finset.sum_product]

theorem continuous_twistedPrimeCoalSum (Ω g : ℝ → ℝ) (X θ₀ : ℝ) :
    Continuous (twistedPrimeCoalSum Ω g X θ₀) := by
  have h : twistedPrimeCoalSum Ω g X θ₀ =
      pairForm (primeRange X ×ˢ primeRange X) (fun q => (coalWeight Ω g θ₀ q.1 q.2 : ℂ)) :=
    funext (twistedPrimeCoalSum_eq_pairForm Ω g X θ₀)
  rw [h]
  exact continuous_pairForm _ _

theorem pos_of_mem_primeRange {X : ℝ} {n : ℕ} (hn : n ∈ primeRange X) : n ≠ 0 := by
  have := (Finset.mem_Ioc.mp hn).1
  omega

theorem pos_of_mem_primeRange_product {X : ℝ} {q : ℕ × ℕ}
    (hq : q ∈ primeRange X ×ˢ primeRange X) : q.1 ≠ 0 ∧ q.2 ≠ 0 := by
  obtain ⟨h1, h2⟩ := Finset.mem_product.mp hq
  exact ⟨pos_of_mem_primeRange h1, pos_of_mem_primeRange h2⟩

theorem prime_of_coalWeight_ne_zero {Ω g : ℝ → ℝ} {θ₀ : ℝ} {n m : ℕ}
    (h : coalWeight Ω g θ₀ n m ≠ 0) : n.Prime ∧ m.Prime ∧ n ≠ m := by
  rw [coalWeight] at h
  split_ifs at h with hc
  · exact ⟨hc.1, hc.2.1, hc.2.2.1⟩
  · exact absurd rfl h

/-- **The twisted coalescent statistic has gauge mean zero.** -/
theorem integral_twistedPrimeCoalSum (Ω g : ℝ → ℝ) (X θ₀ : ℝ) :
    ∫ x, twistedPrimeCoalSum Ω g X θ₀ x ∂gaugeHaar = 0 := by
  simp_rw [twistedPrimeCoalSum_eq_pairForm]
  rw [integral_pairForm fun q hq => pos_of_mem_primeRange_product hq]
  refine Finset.sum_eq_zero fun q hq => ?_
  have hdiag := (Finset.mem_filter.mp hq).2
  by_contra hne
  exact (prime_of_coalWeight_ne_zero (fun h => hne (by rw [h]; simp))).2.2 hdiag

/-- **The gauge mean square of the twisted statistic is the sum of squared pair weights.** -/
theorem integral_normSq_twistedPrimeCoalSum (Ω g : ℝ → ℝ) (X θ₀ : ℝ) :
    ∫ x, ‖twistedPrimeCoalSum Ω g X θ₀ x‖ ^ 2 ∂gaugeHaar =
      ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, coalWeight Ω g θ₀ n m ^ 2 := by
  have hcov := integral_pairForm_mul_conj (S := primeRange X ×ˢ primeRange X)
    (fun q hq => pos_of_mem_primeRange_product hq) (fun q => (coalWeight Ω g θ₀ q.1 q.2 : ℂ))
  have hinner : ∀ q ∈ primeRange X ×ˢ primeRange X,
      (∑ q' ∈ primeRange X ×ˢ primeRange X, if q.1 * q'.2 = q.2 * q'.1 then
        (coalWeight Ω g θ₀ q.1 q.2 : ℂ) * conj (coalWeight Ω g θ₀ q'.1 q'.2 : ℂ) else 0) =
      ((coalWeight Ω g θ₀ q.1 q.2 ^ 2 : ℝ) : ℂ) := by
    intro q hq
    by_cases hw0 : coalWeight Ω g θ₀ q.1 q.2 = 0
    · rw [hw0]
      simp
    · rw [Finset.sum_eq_single q]
      · rw [if_pos (mul_comm _ _), Complex.conj_ofReal]
        push_cast
        ring
      · intro q' _ hne
        by_cases hw0' : coalWeight Ω g θ₀ q'.1 q'.2 = 0
        · simp [hw0']
        · rw [if_neg]
          intro hc
          have hP := prime_of_coalWeight_ne_zero hw0
          have hP' := prime_of_coalWeight_ne_zero hw0'
          obtain ⟨h1, h2⟩ := eq_of_prime_cross_mul_eq hP.1 hP.2.1 hP'.1 hP.2.2 hc
          exact hne (Prod.ext h1.symm h2.symm)
      · exact fun h => absurd hq h
  rw [Finset.sum_congr rfl hinner] at hcov
  simp_rw [← twistedPrimeCoalSum_eq_pairForm, Complex.mul_conj, Complex.normSq_eq_norm_sq] at hcov
  rw [integral_complex_ofReal] at hcov
  have hcov' : ∫ x, ‖twistedPrimeCoalSum Ω g X θ₀ x‖ ^ 2 ∂gaugeHaar =
      ∑ q ∈ primeRange X ×ˢ primeRange X, coalWeight Ω g θ₀ q.1 q.2 ^ 2 := by
    exact_mod_cast hcov
  rw [hcov', Finset.sum_product]

/-! ### The size of the gauge variance -/

theorem coalWeight_sq_le {Ω g : ℝ → ℝ} {X θ₀ L M₀ : ℝ} (hX : 1 ≤ X) (hθ : θ₀ ≤ 1 / 2)
    (hg : ∀ y, |g y| ≤ L) (hΩ : ∀ θ, |cosTransform Ω θ| ≤ M₀) {n m : ℕ}
    (hn : n ∈ primeRange X) (hm : m ∈ primeRange X) :
    coalWeight Ω g θ₀ n m ^ 2 ≤
      (L * M₀ / Real.pi) ^ 2 * (Real.sqrt 2 * Real.log X * (Λ n : ℝ) / n) *
        (if n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀ then acoef n * acoef m else 0) := by
  have hπ := Real.pi_pos
  rw [coalWeight]
  split_ifs with h1 h2
  · have ha : 0 ≤ acoef n * acoef m := mul_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
    have hb := acoef_mul_acoef_le_of_coalescent hX hn hm h2.2 hθ
    have hgL := hg (Real.log m)
    have hΩM := hΩ (Real.log n - Real.log m)
    have hL0 : 0 ≤ L := (abs_nonneg _).trans hgL
    have hM0 : 0 ≤ M₀ := (abs_nonneg _).trans hΩM
    have habs : |1 / Real.pi * (acoef n * acoef m * g (Real.log m) *
        cosTransform Ω (Real.log n - Real.log m))| ≤ L * M₀ / Real.pi * (acoef n * acoef m) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg ha, abs_of_pos (by positivity : 0 < 1 / Real.pi)]
      have := mul_le_mul hgL hΩM (abs_nonneg _) hL0
      calc 1 / Real.pi * (acoef n * acoef m * |g (Real.log m)| *
            |cosTransform Ω (Real.log n - Real.log m)|)
          = 1 / Real.pi * (acoef n * acoef m) * (|g (Real.log m)| *
            |cosTransform Ω (Real.log n - Real.log m)|) := by ring
        _ ≤ 1 / Real.pi * (acoef n * acoef m) * (L * M₀) :=
          mul_le_mul_of_nonneg_left this (by positivity)
        _ = L * M₀ / Real.pi * (acoef n * acoef m) := by ring
    have hsq := sq_le_sq' (neg_le_of_abs_le habs) (le_of_abs_le habs)
    calc _ ≤ (L * M₀ / Real.pi * (acoef n * acoef m)) ^ 2 := hsq
      _ = (L * M₀ / Real.pi) ^ 2 * (acoef n * acoef m) * (acoef n * acoef m) := by ring
      _ ≤ (L * M₀ / Real.pi) ^ 2 * (Real.sqrt 2 * Real.log X * (Λ n : ℝ) / n) *
          (acoef n * acoef m) := by
        refine mul_le_mul_of_nonneg_right ?_ ha
        exact mul_le_mul_of_nonneg_left hb (by positivity)
  · exact absurd ⟨h1.2.2.1, h1.2.2.2⟩ h2
  · rw [zero_pow two_ne_zero]
    have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
    have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have ha : 0 ≤ acoef n * acoef m := mul_nonneg
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
      (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (by positivity)) ha
  · rw [zero_pow two_ne_zero, mul_zero]

/-- The prime-power mass `Σ_{n ≤ X} Λ(n)²/n` is at most `(log X)² (1 + log X)`. -/
theorem sum_vonMangoldt_sq_div_le {X : ℝ} (hX : 1 ≤ X) :
    ∑ n ∈ primeRange X, (Λ n : ℝ) ^ 2 / n ≤ Real.log X ^ 2 * (1 + Real.log X) := by
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
  have hterm : ∀ n ∈ primeRange X, (Λ n : ℝ) ^ 2 / n ≤ Real.log X ^ 2 * (1 / (n : ℝ)) := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Ioc.mp hn).1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnX : (n : ℝ) ≤ X :=
      (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans (Nat.floor_le (by linarith))
    have hΛ : (Λ n : ℝ) ≤ Real.log X :=
      ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hn0 hnX)
    have hΛ0 : (0 : ℝ) ≤ Λ n := ArithmeticFunction.vonMangoldt_nonneg
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hΛ0 hΛ 2) (by positivity)
  have hharm : ∑ n ∈ primeRange X, 1 / (n : ℝ) ≤ 1 + Real.log X := by
    have h := harmonic_le_one_add_log ⌊X⌋₊
    rw [_root_.harmonic_eq_sum_Icc] at h
    push_cast at h
    have hIoc : primeRange X = Finset.Icc 1 ⌊X⌋₊ := by
      ext n; simp [primeRange, Finset.mem_Ioc, Finset.mem_Icc, Nat.one_le_iff_ne_zero,
        Nat.pos_iff_ne_zero]
    rw [hIoc]
    have hfl : Real.log ⌊X⌋₊ ≤ Real.log X := by
      rcases Nat.eq_zero_or_pos ⌊X⌋₊ with h0 | h0
      · rw [h0, Nat.cast_zero, Real.log_zero]; exact hlog
      · exact Real.log_le_log (by exact_mod_cast h0) (Nat.floor_le (by linarith))
    simp only [one_div] at h ⊢
    linarith
  calc _ ≤ ∑ n ∈ primeRange X, Real.log X ^ 2 * (1 / (n : ℝ)) := Finset.sum_le_sum hterm
    _ = Real.log X ^ 2 * ∑ n ∈ primeRange X, 1 / (n : ℝ) := (Finset.mul_sum _ _ _).symm
    _ ≤ Real.log X ^ 2 * (1 + Real.log X) := mul_le_mul_of_nonneg_left hharm (by positivity)

/-- **The gauge variance of the coalescent statistic is small.** -/
theorem integral_normSq_twistedPrimeCoalSum_le {Ω g : ℝ → ℝ} {X θ₀ L M₀ : ℝ} (hX : 1 ≤ X)
    (hθ0 : 0 ≤ θ₀) (hθ : θ₀ ≤ 1 / 2) (hg : ∀ y, |g y| ≤ L) (hΩ : ∀ θ, |cosTransform Ω θ| ≤ M₀) :
    ∫ x, ‖twistedPrimeCoalSum Ω g X θ₀ x‖ ^ 2 ∂gaugeHaar ≤
      (L * M₀ / Real.pi) ^ 2 * (8 * θ₀ * Real.log X ^ 4 * (1 + Real.log X)) := by
  classical
  rw [integral_normSq_twistedPrimeCoalSum]
  have hπ := Real.pi_pos
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
  have hrow : ∀ n ∈ primeRange X, ∑ m ∈ primeRange X, coalWeight Ω g θ₀ n m ^ 2 ≤
      (L * M₀ / Real.pi) ^ 2 * (8 * θ₀ * Real.log X ^ 2 * ((Λ n : ℝ) ^ 2 / n)) := by
    intro n hn
    have hc0 : 0 ≤ (L * M₀ / Real.pi) ^ 2 * (Real.sqrt 2 * Real.log X * (Λ n : ℝ) / n) := by
      have := ArithmeticFunction.vonMangoldt_nonneg (n := n)
      positivity
    calc _ ≤ ∑ m ∈ primeRange X, (L * M₀ / Real.pi) ^ 2 *
          (Real.sqrt 2 * Real.log X * (Λ n : ℝ) / n) *
          (if n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀ then acoef n * acoef m else 0) :=
          Finset.sum_le_sum fun m hm => coalWeight_sq_le hX hθ hg hΩ hn hm
      _ = (L * M₀ / Real.pi) ^ 2 * (Real.sqrt 2 * Real.log X * (Λ n : ℝ) / n) *
          ∑ m ∈ (primeRange X).filter (fun m => n ≠ m ∧ |Real.log n - Real.log m| ≤ θ₀),
            acoef n * acoef m := by
          rw [Finset.sum_filter, Finset.mul_sum]
      _ ≤ (L * M₀ / Real.pi) ^ 2 * (Real.sqrt 2 * Real.log X * (Λ n : ℝ) / n) *
          (4 * Real.sqrt 2 * Real.log X * θ₀ * (Λ n : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_coalescent_partners_acoef_le hX hθ0 hθ hn) hc0
      _ = (L * M₀ / Real.pi) ^ 2 * (8 * θ₀ * Real.log X ^ 2 * ((Λ n : ℝ) ^ 2 / n)) := by
          have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
          rw [mul_assoc, show Real.sqrt 2 * Real.log X * (Λ n : ℝ) / n *
              (4 * Real.sqrt 2 * Real.log X * θ₀ * (Λ n : ℝ)) =
              (Real.sqrt 2 * Real.sqrt 2) * (4 * θ₀ * Real.log X ^ 2 * ((Λ n : ℝ) ^ 2 / n)) by
            ring, h2]
          ring
  calc _ ≤ ∑ n ∈ primeRange X, (L * M₀ / Real.pi) ^ 2 *
        (8 * θ₀ * Real.log X ^ 2 * ((Λ n : ℝ) ^ 2 / n)) := Finset.sum_le_sum hrow
    _ = (L * M₀ / Real.pi) ^ 2 * (8 * θ₀ * Real.log X ^ 2) *
        ∑ n ∈ primeRange X, (Λ n : ℝ) ^ 2 / n := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => by ring
    _ ≤ (L * M₀ / Real.pi) ^ 2 * (8 * θ₀ * Real.log X ^ 2) *
        (Real.log X ^ 2 * (1 + Real.log X)) :=
        mul_le_mul_of_nonneg_left (sum_vonMangoldt_sq_div_le hX) (by positivity)
    _ = _ := by ring

/-! ### Bandwidth `4/3` -/

/-- The twisted prime coalescent surplus at height `T`, normalised as `primeCoalescentSurplus`. -/
def twistedPrimeCoalescentSurplus (u : ℝ → ℝ) (η T : ℝ) (x : GaugeTorus) : ℂ :=
  twistedPrimeCoalSum (profileΩ u T) (params43.localFun T).g (params43.X T) (T ^ (-1 + η)) x /
    ((params43.a T * params43.L T) ^ 2 : ℝ)

theorem twistedPrimeCoalescentSurplus_zero (u : ℝ → ℝ) (η T : ℝ) :
    twistedPrimeCoalescentSurplus u η T 0 = (primeCoalescentSurplus u η T : ℂ) := by
  rw [twistedPrimeCoalescentSurplus, twistedPrimeCoalSum_zero, primeCoalescentSurplus]
  push_cast
  rfl

theorem continuous_twistedPrimeCoalescentSurplus (u : ℝ → ℝ) (η T : ℝ) :
    Continuous (twistedPrimeCoalescentSurplus u η T) :=
  (continuous_twistedPrimeCoalSum _ _ _ _).div_const _

/-- **The gauge mean square of the normalised surplus at bandwidth `4/3`.** -/
theorem eventually_integral_normSq_twistedPrimeCoalescentSurplus_le {ε₁ : ℝ} {u : ℝ → ℝ}
    (hu : WindowProfile ε₁ u) {η : ℝ} (hη1 : η < 1) :
    ∀ᶠ T in atTop, ∫ x, ‖twistedPrimeCoalescentSurplus u η T x‖ ^ 2 ∂gaugeHaar ≤
      (1536 / Real.pi ^ 2) * Real.log T ^ 3 * T ^ (1 + η) := by
  have hP := paramsValidFam_params43
  obtain ⟨TL, hTL⟩ := localHypsCoreW_eventually_fam hP
  have htend : Tendsto (fun T : ℝ => T ^ (-1 + η)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by linarith : 0 < -(-1 + η))
      |>.congr' (Eventually.of_forall fun T => by rw [neg_neg])
  filter_upwards [eventually_ge_atTop (max TL 4096), eventually_l_bounds,
    htend.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
    with T hTmax ⟨hlog1, _, _, _⟩ hθhalf
  have hπ := Real.pi_pos
  have hTLT : TL ≤ T := (le_max_left _ _).trans hTmax
  have hT0 : 0 < T := by linarith [(le_max_right _ _).trans hTmax]
  have hF := hTL T hTLT
  have hL8 : 8 ≤ params43.L T := hF.eight_le_L
  have ha2 : 1 / 2 ≤ params43.a T := hF.b_ge_half.trans hF.b_le_a
  have hXL : params43.X T = Real.exp (params43.L T) := rfl
  have hlogX : Real.log (params43.X T) = params43.L T := by rw [hXL, Real.log_exp]
  have hX1 : 1 ≤ params43.X T := by rw [hXL]; exact Real.one_le_exp (by linarith)
  have hθ0 : 0 < T ^ (-1 + η) := Real.rpow_pos_of_pos hT0 _
  have hg : ∀ y, |(params43.localFun T).g y| ≤ params43.L T := fun y => by
    rw [abs_of_nonneg (hF.g_nonneg y)]
    have h := (hF.g_le_Aphi y).trans (hF.Aphi_le y)
    have hL_eq : (params43.toSetting T).L = params43.L T := rfl
    rw [hL_eq] at h
    exact h.trans (max_le (by linarith [abs_nonneg y]) (by linarith))
  -- the cosine transform of the window is at most `T`
  set s₀ := T + ε₁ * T with hs₀
  set s₁ := 2 * T - ε₁ * T with hs₁
  have hε8 := hu.le
  have hs : s₀ ≤ s₁ := by rw [hs₀, hs₁]; nlinarith only [hε8, hT0]
  have hΩc : Continuous (profileΩ u T) := (contDiff_profileΩ hu T 0).continuous
  have hΩ0 : ∀ τ, 0 ≤ profileΩ u T τ := fun τ => by unfold profileΩ; positivity
  have hΩ1 : ∀ τ, profileΩ u T τ ≤ 1 := fun τ => by
    unfold profileΩ; exact pow_le_one₀ (hu.nonneg _) (hu.le_one _)
  have hΩS : ∀ τ, τ ∉ Set.Icc s₀ s₁ → profileΩ u T τ = 0 := fun τ hτ => by
    unfold profileΩ; rw [profileU_eq_zero hu hT0 hτ]; norm_num
  have hΩi : Integrable (profileΩ u T) := by
    have h := integrable_window_mul hΩc hΩS (h := fun _ => (1 : ℝ)) continuous_const
    simpa using h
  have hIΩ : ∫ τ, profileΩ u T τ ≤ T := by
    have h := integral_window_mul_le hs hΩc hΩ1 hΩS (h := fun _ => (1 : ℝ)) continuous_const
      (fun _ _ => zero_le_one) (C := 1) (fun _ _ => le_rfl)
    simp only [mul_one, one_mul] at h
    have hεT0 := mul_pos hu.pos hT0
    exact h.trans (by linarith)
  have hΩ : ∀ θ, |cosTransform (profileΩ u T) θ| ≤ T := by
    intro θ
    unfold cosTransform
    refine (abs_integral_le_integral_abs).trans
      ((integral_mono (integrable_window_mul_cos hΩi θ).abs hΩi fun τ => ?_).trans hIΩ)
    rw [abs_mul, abs_of_nonneg (hΩ0 τ)]
    exact mul_le_of_le_one_right (hΩ0 τ) (Real.abs_cos_le_one _)
  have hvar := integral_normSq_twistedPrimeCoalSum_le hX1 hθ0.le hθhalf hg hΩ
  rw [hlogX] at hvar
  -- normalisation
  have hden : (1 / 16 : ℝ) * params43.L T ^ 4 ≤ ((params43.a T * params43.L T) ^ 2) ^ 2 := by
    have h1 : 1 / 2 * params43.L T ≤ params43.a T * params43.L T :=
      mul_le_mul_of_nonneg_right ha2 (by linarith)
    have h2 : (1 / 2 * params43.L T) ^ 4 ≤ (params43.a T * params43.L T) ^ 4 :=
      pow_le_pow_left₀ (by linarith) h1 4
    nlinarith only [h2]
  have hden0 : 0 < ((params43.a T * params43.L T) ^ 2) ^ 2 := by positivity
  have hnorm : ∀ x, ‖twistedPrimeCoalescentSurplus u η T x‖ ^ 2 =
      ‖twistedPrimeCoalSum (profileΩ u T) (params43.localFun T).g (params43.X T)
        (T ^ (-1 + η)) x‖ ^ 2 / ((params43.a T * params43.L T) ^ 2) ^ 2 := by
    intro x
    rw [twistedPrimeCoalescentSurplus, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity), div_pow]
  simp_rw [hnorm]
  rw [integral_div]
  have hL_le : params43.L T ≤ 2 * Real.log T := by
    have : params43.L T = 4 / 3 * Zeta23.l T := rfl
    linarith
  rw [div_le_iff₀ hden0]
  have hrpow : T ^ (2 : ℝ) * T ^ (-1 + η) = T ^ (1 + η) := by
    rw [← Real.rpow_add hT0]; ring_nf
  have hT2 : T ^ 2 = T ^ (2 : ℝ) := by norm_cast
  calc _ ≤ (params43.L T * T / Real.pi) ^ 2 *
        (8 * T ^ (-1 + η) * params43.L T ^ 4 * (1 + params43.L T)) := hvar
    _ = (128 / Real.pi ^ 2) * params43.L T ^ 2 * (1 + params43.L T) * (T ^ 2 * T ^ (-1 + η)) *
        ((1 / 16 : ℝ) * params43.L T ^ 4) := by
        field_simp
        ring
    _ ≤ (128 / Real.pi ^ 2) * params43.L T ^ 2 * (1 + params43.L T) * (T ^ 2 * T ^ (-1 + η)) *
        ((params43.a T * params43.L T) ^ 2) ^ 2 :=
        mul_le_mul_of_nonneg_left hden (by positivity)
    _ ≤ (1536 / Real.pi ^ 2) * Real.log T ^ 3 * T ^ (1 + η) *
        ((params43.a T * params43.L T) ^ 2) ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ hden0.le
        rw [hT2, hrpow]
        have hLsq : params43.L T ^ 2 ≤ (2 * Real.log T) ^ 2 :=
          pow_le_pow_left₀ (by linarith) hL_le 2
        have h1L : 1 + params43.L T ≤ 3 * Real.log T := by linarith
        have hTη : 0 ≤ T ^ (1 + η) := (Real.rpow_pos_of_pos hT0 _).le
        calc (128 / Real.pi ^ 2) * params43.L T ^ 2 * (1 + params43.L T) * T ^ (1 + η)
            ≤ (128 / Real.pi ^ 2) * (2 * Real.log T) ^ 2 * (3 * Real.log T) * T ^ (1 + η) := by
              gcongr
          _ = (1536 / Real.pi ^ 2) * Real.log T ^ 3 * T ^ (1 + η) := by ring

/-- **The gauge root-mean-square of the surplus is `o(N(T, 2T))`.** For every `η < 1` and `ε > 0`,
eventually the gauge mean square of the twisted surplus is at most `ε N(T, 2T)²`. -/
theorem twistedPrimeCoalescentSurplus_meanSquare_isLittleO {ε₁ : ℝ} {u : ℝ → ℝ}
    (hu : WindowProfile ε₁ u) {η : ℝ} (hη1 : η < 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop, ∫ x, ‖twistedPrimeCoalescentSurplus u η T x‖ ^ 2 ∂gaugeHaar ≤
      ε * (Ncount T (2 * T) : ℝ) ^ 2 := by
  have hπ := Real.pi_pos
  have hK : 0 ≤ (1536 / Real.pi ^ 2) * (64 * Real.pi ^ 2) := by positivity
  have hrate := eventually_log_pow_rpow_le 1 hη1 hK hε
  filter_upwards [eventually_integral_normSq_twistedPrimeCoalescentSurplus_le hu hη1,
    eventually_T_mul_log_div_eight_pi_le_Ncount, hrate, eventually_l_bounds,
    eventually_ge_atTop (1 : ℝ)] with T hvar hNlow hrt ⟨hlog1, _, _, _⟩ hT1
  have hT0 : 0 < T := by linarith
  have hrpow : T ^ (1 + η) = T * T ^ η := by
    rw [Real.rpow_add hT0, Real.rpow_one]
  have hNlow0 : 0 ≤ T * Real.log T / (8 * Real.pi) := by
    have := Real.log_nonneg hT1
    positivity
  calc _ ≤ (1536 / Real.pi ^ 2) * Real.log T ^ 3 * T ^ (1 + η) := hvar
    _ = ((1536 / Real.pi ^ 2) * (64 * Real.pi ^ 2) * Real.log T ^ 1 * T ^ η) *
        (T * Real.log T ^ 2) / (64 * Real.pi ^ 2) := by
        rw [hrpow]; field_simp
    _ ≤ (ε * T) * (T * Real.log T ^ 2) / (64 * Real.pi ^ 2) := by
        gcongr
    _ = ε * (T * Real.log T / (8 * Real.pi)) ^ 2 := by field_simp; ring
    _ ≤ ε * (Ncount T (2 * T) : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hNlow0 hNlow 2) hε.le

/-- **Almost every twist of the primes meets every budget.** For every `δ > 0` the Haar measure of
the gauge twists whose surplus exceeds `δ N(T, 2T)` tends to zero. -/
theorem tendsto_gaugeHaar_large_twistedSurplus {ε₁ : ℝ} {u : ℝ → ℝ} (hu : WindowProfile ε₁ u)
    {η : ℝ} (hη1 : η < 1) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun T => gaugeHaar.real
      {x | δ * (Ncount T (2 * T) : ℝ) ≤ ‖twistedPrimeCoalescentSurplus u η T x‖}) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hev := twistedPrimeCoalescentSurplus_meanSquare_isLittleO hu hη1
    (by positivity : 0 < ε / 2 * δ ^ 2)
  obtain ⟨T₀, hT₀⟩ := (hev.and (eventually_T_mul_log_div_eight_pi_le_Ncount.and
    (eventually_ge_atTop (2 : ℝ)))).exists_forall_of_atTop
  refine ⟨T₀, fun T hT => ?_⟩
  obtain ⟨hvar, hNlow, hT2⟩ := hT₀ T hT
  have hπ := Real.pi_pos
  have hN0 : 0 < (Ncount T (2 * T) : ℝ) := by
    have hlog : 0 < Real.log T := Real.log_pos (by linarith)
    have : 0 < T * Real.log T / (8 * Real.pi) := by positivity
    linarith
  set c := δ * (Ncount T (2 * T) : ℝ) with hc
  have hc0 : 0 < c := by positivity
  have hint : Integrable (fun x => ‖twistedPrimeCoalescentSurplus u η T x‖ ^ 2) gaugeHaar :=
    ((continuous_twistedPrimeCoalescentSurplus u η T).norm.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hsub : {x | c ≤ ‖twistedPrimeCoalescentSurplus u η T x‖} ⊆
      {x | c ^ 2 ≤ ‖twistedPrimeCoalescentSurplus u η T x‖ ^ 2} := fun x hx =>
    pow_le_pow_left₀ hc0.le hx 2
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (Eventually.of_forall fun x => sq_nonneg _)
    hint (c ^ 2)
  have hmeas : gaugeHaar.real {x | c ≤ ‖twistedPrimeCoalescentSurplus u η T x‖} ≤
      gaugeHaar.real {x | c ^ 2 ≤ ‖twistedPrimeCoalescentSurplus u η T x‖ ^ 2} :=
    measureReal_mono hsub
  have hpos : 0 ≤ gaugeHaar.real {x | c ≤ ‖twistedPrimeCoalescentSurplus u η T x‖} :=
    measureReal_nonneg
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hpos]
  have hc2 : 0 < c ^ 2 := by positivity
  have hbound : gaugeHaar.real {x | c ^ 2 ≤ ‖twistedPrimeCoalescentSurplus u η T x‖ ^ 2} ≤
      ε / 2 := by
    rw [← mul_le_mul_iff_of_pos_left hc2]
    calc _ ≤ ∫ x, ‖twistedPrimeCoalescentSurplus u η T x‖ ^ 2 ∂gaugeHaar := hmarkov
      _ ≤ ε / 2 * δ ^ 2 * (Ncount T (2 * T) : ℝ) ^ 2 := hvar
      _ = c ^ 2 * (ε / 2) := by rw [hc]; ring
  linarith

end GaloisForLFunctions.ArithmeticCorrelationGeometry
