import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenAllIntervalFactorization
import GaloisForLFunctions.HTGeometry.IntervalMeanSquareMoment
import GaloisForLFunctions.RHTower.Sieve.RealWindowCompareBound
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPrimeHarmanMeanSquare

/-!
# The Perron window comparison for the all-interval `E₃` sum

Matomäki–Teräväinen §7.  The short window `(x, x+h]` and the long window `(x, x+h₁]` of the `E₃`
sum are compared through Perron's formula for the coefficients of `P₁(s)P₂(s)P(s)`: the difference
of the short sum and `H/H₁` times the long sum is the integral of `|P₁P₂P(1+it)|` against the
window-comparison kernel, plus four truncation errors.  The integral is split into

* `|t| ≤ T₀`, where the kernel is `≤ 2H·T₀H₁/A` and `|P₁P₂P| ≤ 4992`;
* `T₀ ≤ |t| ≤ T₁ = x/h`, where the kernel is `≤ 2H`;
* `T₁ ≤ |t| ≤ T₁2^J`, split dyadically, where the kernel is `≤ 4(A+H₁)/t`,

and on `|t| ≥ T₀` the mass `∫_{T₀}^{T}|P₁P₂P|` is bounded by Cauchy–Schwarz against a one-sided
mean square of `P₁P` (the claim (5.2)) and a two-sided mean square of `P₂`, each affine in the
height.  The result is the deterministic error bound
`(3 + 8J)√(αβ) h + 26000 T₀² h h₁/x + 10400 h (log 8x)²(1 + log 8x)/2^J`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- **Dyadic assembly of a kernel integral against a cumulative mass bound.**  If
`∫_{T₀}^{T} f ≤ B(1 + T/T₁)` for every `T ≥ T₀`, the kernel is at most `κ₀` on `[T₀, T₁]` and at
most `C/t` beyond `T₁`, then `∫_{T₀}^{T₁ 2^J} f k ≤ 2Bκ₀ + 3JBC/T₁`: on `[T₁ 2^j, T₁ 2^{j+1}]` the
kernel is `≤ C/(T₁ 2^j)` and the mass is `≤ B(1 + 2^{j+1})`. -/
theorem integral_mul_kernel_dyadic_le {f k : ℝ → ℝ} {T₀ T₁ B κ₀ C : ℝ} (J : ℕ)
    (hT₀ : 0 < T₀) (hT₀₁ : T₀ ≤ T₁) (hfc : Continuous f) (hkc : Continuous k)
    (hf0 : ∀ t, 0 ≤ f t) (hk0 : ∀ t, 0 ≤ k t) (hklow : ∀ t ∈ Set.Icc T₀ T₁, k t ≤ κ₀)
    (hkhigh : ∀ t, T₁ ≤ t → k t ≤ C / t)
    (hG : ∀ T, T₀ ≤ T → T ≤ T₁ * 2 ^ J → ∫ t in T₀..T, f t ≤ B * (1 + T / T₁)) :
    ∫ t in T₀..(T₁ * 2 ^ J), f t * k t ≤ 2 * B * κ₀ + J * (3 * B * C / T₁) := by
  have hT₁ : 0 < T₁ := lt_of_lt_of_le hT₀ hT₀₁
  have hfk : Continuous fun t => f t * k t := hfc.mul hkc
  have hJ1 : T₁ ≤ T₁ * 2 ^ J := le_mul_of_one_le_right hT₁.le (one_le_pow₀ (by norm_num))
  have hB0 : 0 ≤ B := by
    have h := hG T₀ le_rfl (hT₀₁.trans hJ1)
    rw [intervalIntegral.integral_same] at h
    exact (mul_nonneg_iff_of_pos_right (by positivity : (0 : ℝ) < 1 + T₀ / T₁)).1 h
  have hκ0 : 0 ≤ κ₀ := (hk0 T₀).trans (hklow T₀ ⟨le_rfl, hT₀₁⟩)
  have hC0 : 0 ≤ C := by
    have h := (hk0 T₁).trans (hkhigh T₁ le_rfl)
    exact (div_nonneg_iff.1 h).elim (fun h => h.1) fun h => absurd h.2 (not_le.2 hT₁)
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hfk.intervalIntegrable (μ := volume) T₀ T₁) (hfk.intervalIntegrable T₁ (T₁ * 2 ^ J))]
  have hfirst : ∫ t in T₀..T₁, f t * k t ≤ 2 * B * κ₀ := by
    calc ∫ t in T₀..T₁, f t * k t ≤ ∫ t in T₀..T₁, f t * κ₀ := by
          refine intervalIntegral.integral_mono_on hT₀₁ (hfk.intervalIntegrable _ _)
            ((hfc.mul continuous_const).intervalIntegrable _ _) fun t ht => ?_
          exact mul_le_mul_of_nonneg_left (hklow t ht) (hf0 t)
      _ = (∫ t in T₀..T₁, f t) * κ₀ := intervalIntegral.integral_mul_const _ _
      _ ≤ (B * (1 + T₁ / T₁)) * κ₀ := mul_le_mul_of_nonneg_right (hG T₁ hT₀₁ hJ1) hκ0
      _ = 2 * B * κ₀ := by rw [div_self hT₁.ne']; ring
  have hsplit := GaloisForLFunctions.HTGeometry.integral_mul_kernel_le_sum_dyadic hT₁ hC0 hf0
    (M := J) (G := k) (fun t ht _ => hkhigh t ht) (fun m _ => hfc.intervalIntegrable _ _)
    (fun m _ => hfk.intervalIntegrable _ _)
  have hpiece : ∀ m ∈ Finset.range J,
      (C / (T₁ * 2 ^ m)) * ∫ t in (T₁ * 2 ^ m)..(T₁ * 2 ^ (m + 1)), f t ≤ 3 * B * C / T₁ := by
    intro m hmJ
    have hmJ' : T₁ * 2 ^ (m + 1) ≤ T₁ * 2 ^ J :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num)
        (Nat.succ_le_of_lt (Finset.mem_range.1 hmJ))) hT₁.le
    have hj : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    have hlo : T₁ ≤ T₁ * 2 ^ m := le_mul_of_one_le_right hT₁.le hj
    have hle : T₁ * 2 ^ m ≤ T₁ * 2 ^ (m + 1) := by
      rw [pow_succ]; nlinarith
    calc (C / (T₁ * 2 ^ m)) * ∫ t in (T₁ * 2 ^ m)..(T₁ * 2 ^ (m + 1)), f t
        ≤ (C / (T₁ * 2 ^ m)) * ∫ t in T₀..(T₁ * 2 ^ (m + 1)), f t := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact intervalIntegral.integral_mono_interval (hT₀₁.trans hlo) hle le_rfl
            (Filter.Eventually.of_forall hf0) (hfc.intervalIntegrable _ _)
      _ ≤ (C / (T₁ * 2 ^ m)) * (B * (1 + T₁ * 2 ^ (m + 1) / T₁)) :=
          mul_le_mul_of_nonneg_left (hG _ (hT₀₁.trans (hlo.trans hle)) hmJ') (by positivity)
      _ = B * C / T₁ * (1 / 2 ^ m + 2) := by
          field_simp
          ring
      _ ≤ B * C / T₁ * 3 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have : 1 / (2 : ℝ) ^ m ≤ 1 := by
            rw [div_le_one (by positivity)]; exact hj
          linarith
      _ = 3 * B * C / T₁ := by ring
  have hdy := Finset.sum_le_sum hpiece
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hdy
  linarith

/-- **Cauchy–Schwarz against two affine mean squares.**  If `∫_{[T₀,T]}|A|² ≤ α(1 + T/T₁)` and
`∫_{[-T,T]}|P|² ≤ β(1 + T/T₁)`, then `∫_{T₀}^{T}|AP| ≤ √(αβ)(1 + T/T₁)`. -/
theorem integral_norm_mul_le_of_meanSquares {A P : ℝ → ℂ} (hA : Continuous A) (hP : Continuous P)
    {T₀ T₁ α β : ℝ} (hT₀ : 0 ≤ T₀) (hT₁ : 0 < T₁) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    {T : ℝ} (hT : T₀ ≤ T) (hAb : ∫ t in Set.Icc T₀ T, ‖A t‖ ^ 2 ≤ α * (1 + T / T₁))
    (hPb : ∫ t in Set.Icc (-T) T, ‖P t‖ ^ 2 ≤ β * (1 + T / T₁)) :
    ∫ t in T₀..T, ‖A t * P t‖ ≤ Real.sqrt (α * β) * (1 + T / T₁) := by
  have hcs := GaloisForLFunctions.HTGeometry.integral_norm_mul_norm_le_sqrt_mul_sqrt hA hP hT
  simp_rw [norm_mul]
  refine hcs.trans ?_
  have hconv : ∀ g : ℝ → ℝ, ∫ t in T₀..T, g t = ∫ t in Set.Icc T₀ T, g t := fun g => by
    rw [intervalIntegral.integral_of_le hT, integral_Icc_eq_integral_Ioc]
  rw [hconv, hconv]
  have hq : 0 ≤ 1 + T / T₁ := by have : 0 ≤ T := hT₀.trans hT; positivity
  have h2 : ∫ t in Set.Icc T₀ T, ‖P t‖ ^ 2 ≤ β * (1 + T / T₁) := by
    refine le_trans ?_ hPb
    refine setIntegral_mono_set ?_ ?_ ?_
    · exact (hP.norm.pow 2).integrableOn_Icc
    · exact Filter.Eventually.of_forall fun t => by positivity
    · exact (Set.Icc_subset_Icc (by linarith) le_rfl).eventuallyLE
  calc Real.sqrt (∫ t in Set.Icc T₀ T, ‖A t‖ ^ 2) * Real.sqrt (∫ t in Set.Icc T₀ T, ‖P t‖ ^ 2)
      ≤ Real.sqrt (α * (1 + T / T₁)) * Real.sqrt (β * (1 + T / T₁)) := by
        gcongr
    _ = Real.sqrt (α * β) * (1 + T / T₁) := by
        rw [← Real.sqrt_mul (by positivity), show α * (1 + T / T₁) * (β * (1 + T / T₁)) =
          (α * β) * (1 + T / T₁) ^ 2 by ring, Real.sqrt_mul (by positivity), Real.sqrt_sq hq]

/-- **The symmetric kernel integral.**  For `|F|` even and `k` even, bounded by `κ_l` on
`[-T₀, T₀]` where `|F| ≤ F_s`, by `κ₀` on `[T₀, T₁]` and by `C/t` beyond `T₁`, and a cumulative
mass bound `∫_{T₀}^{T}|F| ≤ B(1 + T/T₁)`:
`∫_{-T₁2^J}^{T₁2^J} |F| k ≤ 2(2Bκ₀ + 3JBC/T₁) + 2T₀ F_s κ_l`. -/
theorem integral_norm_mul_kernel_symm_le {F : ℝ → ℂ} {k : ℝ → ℝ} (hFc : Continuous F)
    (hkc : Continuous k) (hFeven : ∀ t, ‖F (-t)‖ = ‖F t‖) (hkeven : ∀ t, k (-t) = k t)
    (hk0 : ∀ t, 0 ≤ k t) {T₀ T₁ B κl κ₀ C Fs : ℝ} (J : ℕ) (hT₀ : 0 < T₀) (hT₀₁ : T₀ ≤ T₁)
    (hsup : ∀ t ∈ Set.Icc (-T₀) T₀, ‖F t‖ ≤ Fs) (hkl : ∀ t ∈ Set.Icc (-T₀) T₀, k t ≤ κl)
    (hklow : ∀ t ∈ Set.Icc T₀ T₁, k t ≤ κ₀) (hkhigh : ∀ t, T₁ ≤ t → k t ≤ C / t)
    (hG : ∀ T, T₀ ≤ T → T ≤ T₁ * 2 ^ J → ∫ t in T₀..T, ‖F t‖ ≤ B * (1 + T / T₁)) :
    ∫ t in (-(T₁ * 2 ^ J))..(T₁ * 2 ^ J), ‖F t‖ * k t ≤
      2 * (2 * B * κ₀ + J * (3 * B * C / T₁)) + 2 * T₀ * (Fs * κl) := by
  have hpos := integral_mul_kernel_dyadic_le (f := fun t => ‖F t‖) J hT₀ hT₀₁ hFc.norm hkc
    (fun t => norm_nonneg _) hk0 hklow hkhigh hG
  have hneg : ∫ t in T₀..(T₁ * 2 ^ J), ‖F (-t)‖ * k (-t) ≤
      2 * B * κ₀ + J * (3 * B * C / T₁) := by
    simp_rw [hFeven, hkeven]; exact hpos
  have hlow : ∫ t in (-T₀)..T₀, ‖F t‖ * k t ≤ 2 * T₀ * (Fs * κl) := by
    have hle : -T₀ ≤ T₀ := by linarith
    calc ∫ t in (-T₀)..T₀, ‖F t‖ * k t ≤ ∫ _t in (-T₀)..T₀, Fs * κl := by
          refine intervalIntegral.integral_mono_on hle
            ((hFc.norm.mul hkc).intervalIntegrable _ _) intervalIntegrable_const fun t ht => ?_
          have hFs : 0 ≤ Fs := (norm_nonneg _).trans (hsup t ht)
          exact mul_le_mul (hsup t ht) (hkl t ht) (hk0 t) hFs
      _ = 2 * T₀ * (Fs * κl) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  exact GaloisForLFunctions.HTGeometry.integral_symm_le_of_flanks (F := fun t => ‖F t‖)
    hFc.norm hkc hpos hneg hlow

/-- **The kernel integral against the window-comparison kernel.**  With `t₀ = 1`, the kernel is
`≤ 2H(T₀H₁/A)` on `[-T₀, T₀]`, `≤ 2H` everywhere and `≤ 4(A + H₁)/t` beyond `1`. -/
theorem integral_norm_mul_windowCompareKernel_le {F : ℝ → ℂ} (hFc : Continuous F)
    (hFeven : ∀ t, ‖F (-t)‖ = ‖F t‖) {A H H₁ T₀ T₁ B Fs : ℝ} (J : ℕ) (hA : 0 < A) (hH : 0 ≤ H)
    (hH₁ : 0 < H₁) (hT₀ : 0 < T₀) (hT₀₁ : T₀ ≤ T₁) (hT₁ : 1 ≤ T₁)
    (hsup : ∀ t ∈ Set.Icc (-T₀) T₀, ‖F t‖ ≤ Fs)
    (hG : ∀ T, T₀ ≤ T → T ≤ T₁ * 2 ^ J → ∫ t in T₀..T, ‖F t‖ ≤ B * (1 + T / T₁)) :
    ∫ t in (-(T₁ * 2 ^ J))..(T₁ * 2 ^ J), ‖F t‖ * windowCompareKernel A H H₁ 1 t ≤
      2 * (2 * B * (2 * H) + J * (3 * B * (4 * (A + H₁)) / T₁))
        + 2 * T₀ * (Fs * (2 * H * (T₀ * H₁ / A))) := by
  refine integral_norm_mul_kernel_symm_le hFc (continuous_windowCompareKernel one_pos) hFeven
    (fun t => by simp only [windowCompareKernel, abs_neg])
    (windowCompareKernel_nonneg hA hH hH₁.le one_pos) J hT₀ hT₀₁ hsup ?_ ?_ ?_ hG
  · intro t ht
    refine windowCompareKernel_le_of_low hA hH hH₁ ?_
    have : T₀ * H₁ / A * A / H₁ = T₀ := by field_simp
    rw [this, abs_le]
    exact ⟨ht.1, ht.2⟩
  · intro t _
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  · intro t ht
    exact windowCompareKernel_le_div one_pos (hT₁.trans ht)

/-- The `E₃` coefficients are bounded by `S (log₂ M)²` when the cofactor support lies in
`[1, N]` and `p₁p₂N ≤ M`. -/
theorem norm_mtAllIntervalCoeff_le_of_le {B₁ B₂ : Finset ℕ} (hB₁ : ∀ p ∈ B₁, p.Prime)
    (hB₂ : ∀ p ∈ B₂, p.Prime) {s : ℕ → ℂ} {S : ℝ} {N M : ℕ} (hS : ∀ m, ‖s m‖ ≤ S)
    (hs0 : s 0 = 0) (hsN : ∀ m, N < m → s m = 0) (hM : ∀ p₁ ∈ B₁, ∀ p₂ ∈ B₂, p₁ * p₂ * N ≤ M)
    (n : ℕ) : ‖mtAllIntervalCoeff B₁ B₂ s n‖ ≤ S * (Nat.log 2 M : ℝ) ^ 2 := by
  have hS0 : 0 ≤ S := (norm_nonneg _).trans (hS 0)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have : mtAllIntervalCoeff B₁ B₂ s 0 = 0 := by
      unfold mtAllIntervalCoeff; simp [hs0]
    rw [this, norm_zero]; positivity
  by_cases hnM : n ≤ M
  · refine (norm_mtAllIntervalCoeff_le hB₁ hB₂ hS hn).trans ?_
    have : Nat.log 2 n ≤ Nat.log 2 M := Nat.log_mono_right hnM
    gcongr
  · have : mtAllIntervalCoeff B₁ B₂ s n = 0 := by
      unfold mtAllIntervalCoeff
      refine Finset.sum_eq_zero fun p₁ hp₁ => Finset.sum_eq_zero fun p₂ hp₂ => ?_
      split_ifs with hd
      · apply hsN
        by_contra hle
        rw [not_lt] at hle
        have : n ≤ p₁ * p₂ * N := by
          calc n = p₁ * p₂ * (n / (p₁ * p₂)) := (Nat.mul_div_cancel' hd).symm
            _ ≤ p₁ * p₂ * N := Nat.mul_le_mul_left _ hle
        exact hnM (this.trans (hM p₁ hp₁ p₂ hp₂))
      · rfl
    rw [this, norm_zero]; positivity

/-- **The window comparison for the `E₃` sum.**  The short window sum minus `H/H₁` times the long
one is bounded by the Perron integral of `P₁P₂P` against the comparison kernel plus the four
truncation errors, with coefficient bound `156 (log₂ M)²`. -/
theorem abs_mtAllIntervalSumOn_compare_le {B₁ B₂ : Finset ℕ} (hB₁ : ∀ p ∈ B₁, p.Prime)
    (hB₂ : ∀ p ∈ B₂, p.Prime) {z Q D E Y M : ℕ} {x h h₁ T t₀ : ℝ}
    (hz : 2 ≤ z) (hYz : 4 * Y < z ^ 6) (hx : 0 ≤ x) (hh : 1 ≤ h) (hhh₁ : h ≤ h₁) (hT : 0 < T)
    (ht₀ : 0 < t₀)
    (hrange : ∀ p₁ ∈ B₁,
      ∀ p₂ ∈ B₂, ∀ m ∈ Finset.Ioc (⌊x⌋₊ / (p₁ * p₂)) (⌊x + h₁⌋₊ / (p₁ * p₂)),
        (Y : ℝ) / 2 < m ∧ (m : ℝ) ≤ 4 * Y)
    (hM : ∀ p₁ ∈ B₁,
      ∀ p₂ ∈ B₂, p₁ * p₂ * (4 * Y) ≤ M)
    (hM₁ : ⌊x + h₁⌋₊ ≤ M)
    (hlow : t₀ ≤ ((⌊x⌋₊ : ℝ) + 1 / 2) / ((⌊x + h₁⌋₊ - ⌊x⌋₊ : ℕ) : ℝ)) :
    |mtAllIntervalSumOn B₁ B₂ z Q D E x h -
        (((⌊x + h⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) / ((⌊x + h₁⌋₊ - ⌊x⌋₊ : ℕ) : ℝ)) *
          mtAllIntervalSumOn B₁ B₂ z Q D E x h₁|
      ≤ (1 / (2 * Real.pi)) *
          (∫ t in (-T)..T, ‖perronPoly (mtAllIntervalCoeff
              (B₁)
              (B₂)
              (fun n => mtHarmanProposition22SourceAF z Q D E Y n)) M 1 t‖ *
            windowCompareKernel ((⌊x⌋₊ : ℝ) + 1 / 2) ((⌊x + h⌋₊ - ⌊x⌋₊ : ℕ) : ℝ)
              ((⌊x + h₁⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) t₀ t)
        + (perronNearError (156 * (Nat.log 2 M : ℝ) ^ 2) M ⌊x + h⌋₊ 1 T
            + perronNearError (156 * (Nat.log 2 M : ℝ) ^ 2) M ⌊x⌋₊ 1 T
          + (((⌊x + h⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) / ((⌊x + h₁⌋₊ - ⌊x⌋₊ : ℕ) : ℝ)) *
            (perronNearError (156 * (Nat.log 2 M : ℝ) ^ 2) M ⌊x + h₁⌋₊ 1 T
              + perronNearError (156 * (Nat.log 2 M : ℝ) ^ 2) M ⌊x⌋₊ 1 T)) := by
  classical
  have hS : ∀ m, ‖(fun n => mtHarmanProposition22SourceAF z Q D E Y n) m‖ ≤ 156 :=
    norm_harmanSource_le hz hYz
  have hs0 : (fun n => mtHarmanProposition22SourceAF z Q D E Y n) 0 = 0 :=
    ArithmeticFunction.map_zero
  have hsN : ∀ m, 4 * Y < m → (fun n => mtHarmanProposition22SourceAF z Q D E Y n) m = 0 := by
    intro m hm
    by_contra hne
    obtain ⟨-, -, hhi⟩ := mtRealIntervalAF_scaleSupported _ _ _ hne
    have : m ≤ 4 * Y := by
      exact_mod_cast (show (m : ℝ) ≤ ((4 * Y : ℕ) : ℝ) by push_cast; exact hhi)
    omega
  have hK := norm_mtAllIntervalCoeff_le_of_le hB₁ hB₂ hS hs0 hsN hM
  have hxh : ⌊x + h⌋₊ ≤ ⌊x + h₁⌋₊ := Nat.floor_mono (by linarith)
  have hrange_h : ∀ p₁ ∈ B₁,
      ∀ p₂ ∈ B₂, ∀ m ∈ Finset.Ioc (⌊x⌋₊ / (p₁ * p₂)) (⌊x + h⌋₊ / (p₁ * p₂)),
        (Y : ℝ) / 2 < m ∧ (m : ℝ) ≤ 4 * Y := fun p₁ hp₁ p₂ hp₂ m hm =>
    hrange p₁ hp₁ p₂ hp₂ m (Finset.mem_Ioc.2 ⟨(Finset.mem_Ioc.1 hm).1,
      (Finset.mem_Ioc.1 hm).2.trans (Nat.div_le_div_right hxh)⟩)
  have e1 := mtAllIntervalSumOn_eq_sum_coeff (fun p hp => (hB₁ p hp).pos)
    (fun p hp => (hB₂ p hp).pos) (z := z) (Q := Q) (D := D) (E := E) hx
    (by linarith : (0 : ℝ) ≤ h) hrange_h
  have e2 := mtAllIntervalSumOn_eq_sum_coeff (fun p hp => (hB₁ p hp).pos)
    (fun p hp => (hB₂ p hp).pos) (z := z) (Q := Q) (D := D) (E := E) hx
    (by linarith : (0 : ℝ) ≤ h₁) hrange
  have hHpos : 0 < ((⌊x + h⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) := by
    have h1 : (⌊x⌋₊ : ℝ) + 1 ≤ x + h := by have := Nat.floor_le hx; linarith
    have h2 : ⌊x⌋₊ + 1 ≤ ⌊x + h⌋₊ := Nat.le_floor (by push_cast; exact h1)
    have : 0 < ⌊x + h⌋₊ - ⌊x⌋₊ := by omega
    exact_mod_cast this
  have hHle : ((⌊x + h⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) ≤ ((⌊x + h₁⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) := by
    have : ⌊x + h⌋₊ - ⌊x⌋₊ ≤ ⌊x + h₁⌋₊ - ⌊x⌋₊ := by omega
    exact_mod_cast this
  have hmain := norm_realWindowSum_compare_le hK hT hx (by linarith) (by linarith)
    (hxh.trans hM₁) hM₁ hHpos hHle ht₀ hlow
  rw [← e1, ← e2, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs] at hmain
  exact hmain

/-- Membership in the primes of `(⌊P⌋, ⌊2P⌋]`. -/
theorem mem_primes_Ioc_floor_iff {P : ℝ} (hP : 0 ≤ P) {p : ℕ} :
    p ∈ (Finset.Ioc ⌊P⌋₊ ⌊2 * P⌋₊).filter Nat.Prime ↔ p.Prime ∧ P < p ∧ (p : ℝ) ≤ 2 * P := by
  rw [Finset.mem_filter, Finset.mem_Ioc, Nat.floor_lt hP, Nat.le_floor_iff (by linarith)]
  tauto

/-- The Harman source polynomial is bounded on the line `σ = 1`: `|∑_{n ≤ 4Y} s(n) n^{-1-it}| ≤ 1248`
since `|s| ≤ 156` and `s` lives on `(Y/2, 4Y]`. -/
theorem norm_perronPoly_harmanSource_le {z Q D E Y : ℕ} (hz : 2 ≤ z) (hYz : 4 * Y < z ^ 6)
    (hY : 1 ≤ Y) (t : ℝ) :
    ‖perronPoly (fun n => mtHarmanProposition22SourceAF z Q D E Y n) (4 * Y) 1 t‖ ≤ 1248 := by
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast hY
  have hterm : ∀ n ∈ Finset.Icc 1 (4 * Y),
      ‖mtHarmanProposition22SourceAF z Q D E Y n *
        (n : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖ ≤ 312 / (Y : ℝ) := by
    intro n hn
    have hn0 : 0 < n := (Finset.mem_Icc.1 hn).1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn0]
    have hre : (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)).re = -1 := by simp
    rw [hre, Real.rpow_neg_one]
    by_cases hS : mtHarmanProposition22SourceAF z Q D E Y n = 0
    · rw [hS, norm_zero, zero_mul]; positivity
    obtain ⟨-, hlo, -⟩ := mtRealIntervalAF_scaleSupported _ _ _ hS
    calc ‖mtHarmanProposition22SourceAF z Q D E Y n‖ * (n : ℝ)⁻¹ ≤ 156 * (2 / (Y : ℝ)) := by
          apply mul_le_mul (norm_harmanSource_le hz hYz n) _ (by positivity) (by norm_num)
          rw [inv_le_comm₀ hnR (by positivity), inv_div]
          linarith
      _ = 312 / (Y : ℝ) := by ring
  calc ‖perronPoly (fun n => mtHarmanProposition22SourceAF z Q D E Y n) (4 * Y) 1 t‖
      ≤ ∑ n ∈ Finset.Icc 1 (4 * Y), ‖mtHarmanProposition22SourceAF z Q D E Y n *
          (n : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖ := by
        unfold perronPoly
        exact norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 (4 * Y), 312 / (Y : ℝ) := Finset.sum_le_sum hterm
    _ = 1248 := by
        rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
        push_cast
        field_simp
        ring

/-- **The geometry of the `E₃` windows.**  With `X = √(xP₁)`, `R = √(x/P₁)/2` (so `P₁R = X/2` and
`x/X = X/P₁`), `Y = ⌊X/P₁⌋ - 1` and `h₁ ≤ x/2`, every cofactor `m` of a window `(x, x+h₁]` with `p₁ ∈ (P₁, 2P₁]`, `p₂ ∈ (R, 2R]` lies in
`(Y/2, 4Y]`, and `p₁p₂·4Y ≤ 8x`. -/
theorem mtAllInterval_window_geometry {B₁ B₂ : Finset ℕ} {x P₁ h₁ : ℝ} (hx : 1 ≤ x)
    (hP : 2 ≤ P₁) (hXP : 8 * P₁ ≤ Real.sqrt (x * P₁)) (hh₁ : 0 ≤ h₁) (hh₁x : h₁ ≤ x / 2)
    (hB₁ : ∀ p ∈ B₁, P₁ < p ∧ (p : ℝ) ≤ 2 * P₁)
    (hB₂ : ∀ p ∈ B₂, Real.sqrt (x / P₁) / 2 < p ∧ (p : ℝ) ≤ 2 * (Real.sqrt (x / P₁) / 2)) :
    (∀ p₁ ∈ B₁,
      ∀ p₂ ∈ B₂,
      ∀ m ∈ Finset.Ioc (⌊x⌋₊ / (p₁ * p₂)) (⌊x + h₁⌋₊ / (p₁ * p₂)),
        ((⌊Real.sqrt (x * P₁) / P₁⌋₊ - 1 : ℕ) : ℝ) / 2 < m ∧
          (m : ℝ) ≤ 4 * ((⌊Real.sqrt (x * P₁) / P₁⌋₊ - 1 : ℕ) : ℝ)) ∧
    (∀ p₁ ∈ B₁,
      ∀ p₂ ∈ B₂,
      p₁ * p₂ * (4 * (⌊Real.sqrt (x * P₁) / P₁⌋₊ - 1)) ≤ ⌊8 * x⌋₊) := by
  have hx0 : 0 < x := by linarith
  have hP0 : 0 < P₁ := by linarith
  set X := Real.sqrt (x * P₁) with hXdef
  set R := Real.sqrt (x / P₁) / 2 with hRdef
  have hX0 : 0 < X := Real.sqrt_pos.2 (by positivity)
  have hXsq : X ^ 2 = x * P₁ := Real.sq_sqrt (by positivity)
  have hRX : R * X = x / 2 := by
    rw [hRdef, hXdef, div_mul_eq_mul_div, ← Real.sqrt_mul (by positivity)]
    rw [show x / P₁ * (x * P₁) = x ^ 2 by field_simp]
    rw [Real.sqrt_sq hx0.le]
  have hR0 : 0 < R := by
    have : 0 < Real.sqrt (x / P₁) := Real.sqrt_pos.2 (by positivity)
    rw [hRdef]; positivity
  have hPR : P₁ * R = X / 2 := by
    have : P₁ * R * X = X ^ 2 / 2 := by rw [mul_assoc, hRX, hXsq]; ring
    field_simp at this ⊢
    nlinarith [this]
  set V := X / P₁ with hVdef
  have hV8 : 8 ≤ V := by rw [hVdef, le_div_iff₀ hP0]; linarith
  have hxX : x / X = V := by
    rw [hVdef, div_eq_div_iff hX0.ne' hP0.ne']
    nlinarith [hXsq]
  have hfl1 : 1 ≤ ⌊V⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hYR : ((⌊V⌋₊ - 1 : ℕ) : ℝ) = (⌊V⌋₊ : ℝ) - 1 := by
    rw [Nat.cast_sub hfl1]; norm_num
  have hflV : (⌊V⌋₊ : ℝ) ≤ V := Nat.floor_le (by linarith)
  have hVfl : V < (⌊V⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one V
  -- the prime ranges
  have hq : ∀ p₁ ∈ B₁,
      ∀ p₂ ∈ B₂,
      X / 2 < (p₁ : ℝ) * p₂ ∧ (p₁ : ℝ) * p₂ ≤ 2 * X := by
    intro p₁ hp₁ p₂ hp₂
    obtain ⟨h1l, h1u⟩ := hB₁ p₁ hp₁
    obtain ⟨h2l, h2u⟩ := hB₂ p₂ hp₂
    constructor
    · calc X / 2 = P₁ * R := hPR.symm
        _ < (p₁ : ℝ) * p₂ := mul_lt_mul'' h1l h2l hP0.le hR0.le
    · calc (p₁ : ℝ) * p₂ ≤ (2 * P₁) * (2 * R) :=
            mul_le_mul h1u h2u (Nat.cast_nonneg _) (by linarith)
        _ = 2 * X := by rw [show 2 * P₁ * (2 * R) = 4 * (P₁ * R) by ring, hPR]; ring
  refine ⟨?_, ?_⟩
  · intro p₁ hp₁ p₂ hp₂ m hm
    obtain ⟨hqlo, hqhi⟩ := hq p₁ hp₁ p₂ hp₂
    have hq0 : (0 : ℝ) < (p₁ : ℝ) * p₂ := by linarith
    have hqN : 0 < p₁ * p₂ := by exact_mod_cast hq0
    obtain ⟨hml, hmu⟩ := Finset.mem_Ioc.1 hm
    rw [Nat.div_lt_iff_lt_mul hqN] at hml
    rw [Nat.le_div_iff_mul_le hqN] at hmu
    have hml' : x < (m : ℝ) * ((p₁ : ℝ) * p₂) := by
      have h1 : ⌊x⌋₊ + 1 ≤ m * (p₁ * p₂) := hml
      have h2 : ((⌊x⌋₊ : ℝ) + 1) ≤ (m : ℝ) * ((p₁ : ℝ) * p₂) := by exact_mod_cast h1
      have h3 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
      linarith
    have hmu' : (m : ℝ) * ((p₁ : ℝ) * p₂) ≤ x + h₁ := by
      have h1 : ((m * (p₁ * p₂) : ℕ) : ℝ) ≤ (⌊x + h₁⌋₊ : ℝ) := by exact_mod_cast hmu
      push_cast at h1
      exact h1.trans (Nat.floor_le (by linarith))
    rw [hYR]
    constructor
    · -- `m > x/(p₁p₂) ≥ x/(2X) = V/2 > (⌊V⌋ - 1)/2`
      have : x / (2 * X) < m := by
        rw [div_lt_iff₀ (by positivity)]
        calc x < (m : ℝ) * ((p₁ : ℝ) * p₂) := hml'
          _ ≤ (m : ℝ) * (2 * X) := mul_le_mul_of_nonneg_left hqhi (Nat.cast_nonneg _)
      have hx2X : x / (2 * X) = V / 2 := by rw [← hxX]; field_simp
      linarith
    · -- `m ≤ (x+h₁)/(p₁p₂) < 2(x+h₁)/X ≤ 3V ≤ 4(⌊V⌋ - 1)`
      have hm3 : (m : ℝ) * (X / 2) ≤ x + h₁ := by
        calc (m : ℝ) * (X / 2) ≤ (m : ℝ) * ((p₁ : ℝ) * p₂) :=
              mul_le_mul_of_nonneg_left hqlo.le (Nat.cast_nonneg _)
          _ ≤ x + h₁ := hmu'
      have hmV : (m : ℝ) ≤ 3 * V := by
        have hxV : x = V * X := by rw [← hxX]; field_simp
        have : (m : ℝ) * (X / 2) ≤ (3 * V) * (X / 2) := by nlinarith
        exact le_of_mul_le_mul_right this (by positivity)
      linarith
  · intro p₁ hp₁ p₂ hp₂
    obtain ⟨-, hqhi⟩ := hq p₁ hp₁ p₂ hp₂
    refine Nat.le_floor ?_
    have hfl : ((⌊V⌋₊ - 1 : ℕ) : ℝ) ≤ V := by rw [hYR]; linarith
    push_cast [Nat.cast_sub hfl1]
    have hY0 : (0 : ℝ) ≤ (⌊V⌋₊ : ℝ) - 1 := by
      have : (1 : ℝ) ≤ ⌊V⌋₊ := by exact_mod_cast hfl1
      linarith
    calc (p₁ : ℝ) * p₂ * (4 * ((⌊V⌋₊ : ℝ) - 1)) ≤ (2 * X) * (4 * V) := by
          apply mul_le_mul hqhi (by linarith) (by positivity) (by positivity)
      _ = 8 * x := by
          rw [hVdef]; field_simp; nlinarith [hXsq]

/-- `log₂ ⌊8x⌋ ≤ (3/2) log(8x)`. -/
theorem natLog_floor_le {x : ℝ} (hx : 1 ≤ x) :
    (Nat.log 2 ⌊8 * x⌋₊ : ℝ) ≤ 3 / 2 * Real.log (8 * x) := by
  have hM : ⌊8 * x⌋₊ ≠ 0 := (Nat.floor_pos.2 (by linarith)).ne'
  have hpow := Nat.pow_log_le_self 2 hM
  have h1 : (2 : ℝ) ^ (Nat.log 2 ⌊8 * x⌋₊) ≤ 8 * x := by
    have : ((2 ^ (Nat.log 2 ⌊8 * x⌋₊) : ℕ) : ℝ) ≤ (⌊8 * x⌋₊ : ℝ) := by exact_mod_cast hpow
    push_cast at this
    exact this.trans (Nat.floor_le (by linarith))
  have h2 := Real.log_le_log (by positivity) h1
  rw [Real.log_pow] at h2
  have hl2 := Real.log_two_gt_d9
  have hL : 0 ≤ Real.log (8 * x) := Real.log_nonneg (by linarith)
  nlinarith

/-- One Perron truncation error of the `E₃` comparison: with `M = ⌊8x⌋`, `K = 156 (log₂ M)²` and
`1 ≤ N ≤ 2x`, `E(K, M, N, T) ≤ 2600 x (log 8x)²(1 + log 8x)/T`. -/
theorem perronNearError_mtAllInterval_le {x T : ℝ} {N : ℕ} (hx : 1 ≤ x) (hT : 0 < T)
    (hN1 : 1 ≤ N) (hN : (N : ℝ) ≤ 2 * x) :
    perronNearError (156 * (Nat.log 2 ⌊8 * x⌋₊ : ℝ) ^ 2) ⌊8 * x⌋₊ N 1 T ≤
      2600 * x * Real.log (8 * x) ^ 2 * (1 + Real.log (8 * x)) / T := by
  have hL : 0 ≤ Real.log (8 * x) := Real.log_nonneg (by linarith)
  have hK : 156 * (Nat.log 2 ⌊8 * x⌋₊ : ℝ) ^ 2 ≤ 351 * Real.log (8 * x) ^ 2 := by
    have h := natLog_floor_le hx
    have h0 : (0 : ℝ) ≤ Nat.log 2 ⌊8 * x⌋₊ := Nat.cast_nonneg _
    nlinarith
  have hM : Real.log (⌊8 * x⌋₊ : ℝ) ≤ Real.log (8 * x) :=
    Real.log_le_log (by exact_mod_cast Nat.floor_pos.2 (by linarith)) (Nat.floor_le (by linarith))
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNl : Real.log (N : ℝ) ≤ Real.log (8 * x) := Real.log_le_log hN0 (by linarith)
  have hlogs : 5 * (1 + Real.log (⌊8 * x⌋₊ : ℝ)) + 4 * (1 + Real.log (N : ℝ)) ≤
      9 * (1 + Real.log (8 * x)) := by linarith
  have hlogs0 : 0 ≤ 5 * (1 + Real.log (⌊8 * x⌋₊ : ℝ)) + 4 * (1 + Real.log (N : ℝ)) := by
    have : 0 ≤ Real.log (⌊8 * x⌋₊ : ℝ) :=
      Real.log_nonneg (by exact_mod_cast Nat.floor_pos.2 (by linarith))
    have : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN1)
    linarith
  unfold perronNearError
  rw [Real.rpow_one, div_le_div_iff₀ (by positivity) hT]
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hNh : (N : ℝ) + 1 / 2 ≤ 5 / 2 * x := by linarith
  calc 156 * (Nat.log 2 ⌊8 * x⌋₊ : ℝ) ^ 2 * ((N : ℝ) + 1 / 2) *
        (5 * (1 + Real.log (⌊8 * x⌋₊ : ℝ)) + 4 * (1 + Real.log (N : ℝ))) * T
      ≤ 351 * Real.log (8 * x) ^ 2 * (5 / 2 * x) * (9 * (1 + Real.log (8 * x))) * T := by
        gcongr
    _ ≤ 2600 * x * Real.log (8 * x) ^ 2 * (1 + Real.log (8 * x)) * (Real.pi * T) := by
        have hZ : 0 ≤ x * Real.log (8 * x) ^ 2 * (1 + Real.log (8 * x)) * T := by positivity
        have hpi' : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
        have := mul_le_mul_of_nonneg_left hpi'.le hZ
        nlinarith

/-- **Collecting the `E₃` comparison error.**  With `x ≥ 3`, `1 ≤ h ≤ h₁ ≤ x/2`, `H ≤ h + 1`,
`H₁ ≤ h₁ + 1`, `x - 1/2 ≤ A ≤ x + 1/2` and `T₁ = x/h`, the kernel integral bound and the four
truncation errors at height `T₁ 2^J` add up to
`(3 + 8J) B h + 26000 T₀² h h₁/x + 10400 h (log 8x)²(1 + log 8x)/2^J`. -/
theorem mtAllInterval_error_collect {x h h₁ A H H₁ B T₀ E₁ E₂ E₃ E₄ ρ : ℝ} (J : ℕ) (hx : 3 ≤ x)
    (hh : 1 ≤ h) (hhh₁ : h ≤ h₁) (hh₁x : h₁ ≤ x / 2) (hH : H ≤ h + 1)
    (hH₁0 : 0 ≤ H₁) (hH₁ : H₁ ≤ h₁ + 1) (hA : x - 1 / 2 ≤ A) (hA' : A ≤ x + 1 / 2) (hB : 0 ≤ B)
    (hT₀ : 0 < T₀) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hE : ∀ E ∈ ({E₁, E₂, E₃, E₄} : Set ℝ),
      E ≤ 2600 * x * Real.log (8 * x) ^ 2 * (1 + Real.log (8 * x)) / (x / h * 2 ^ J)) :
    (1 / (2 * Real.pi)) * (2 * (2 * B * (2 * H) + J * (3 * B * (4 * (A + H₁)) / (x / h)))
        + 2 * T₀ * (4992 * (2 * H * (T₀ * H₁ / A))))
      + (E₁ + E₂ + ρ * (E₃ + E₄)) ≤
      (3 + 8 * J) * B * h + 26000 * T₀ ^ 2 * h * h₁ / x
        + 10400 * h * Real.log (8 * x) ^ 2 * (1 + Real.log (8 * x)) / 2 ^ J := by
  have hx0 : 0 < x := by linarith
  have hh0 : 0 < h := by linarith
  have hA0 : 0 < A := by linarith
  have hpi : 3 < Real.pi := Real.pi_gt_three
  have hpi0 : 0 < Real.pi := Real.pi_pos
  set Q := Real.log (8 * x) ^ 2 * (1 + Real.log (8 * x)) with hQ
  have hQ0 : 0 ≤ Q := by
    have : 0 ≤ Real.log (8 * x) := Real.log_nonneg (by linarith)
    positivity
  have hEb : ∀ E ∈ ({E₁, E₂, E₃, E₄} : Set ℝ), E ≤ 2600 * h * Q / 2 ^ J := by
    intro E hE'
    refine (hE E hE').trans (le_of_eq ?_)
    rw [hQ]; field_simp
  have h1 := hEb E₁ (by simp)
  have h2 := hEb E₂ (by simp)
  have h3 := hEb E₃ (by simp)
  have h4 := hEb E₄ (by simp)
  have hq0 : 0 ≤ 2600 * h * Q / 2 ^ J := by positivity
  have hnear : E₁ + E₂ + ρ * (E₃ + E₄) ≤ 10400 * h * Q / 2 ^ J := by
    have hE34 : E₃ + E₄ ≤ 2 * (2600 * h * Q / 2 ^ J) := by linarith
    have hρE : ρ * (E₃ + E₄) ≤ 2 * (2600 * h * Q / 2 ^ J) := by
      rcases le_or_gt 0 (E₃ + E₄) with hpos | hneg
      · calc ρ * (E₃ + E₄) ≤ 1 * (E₃ + E₄) := mul_le_mul_of_nonneg_right hρ1 hpos
          _ ≤ _ := by linarith
      · have : ρ * (E₃ + E₄) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hρ0 hneg.le
        linarith
    have : 10400 * h * Q / 2 ^ J = 4 * (2600 * h * Q / 2 ^ J) := by ring
    linarith
  -- the three kernel pieces
  have hk1 : (1 / (2 * Real.pi)) * (2 * (2 * B * (2 * H))) ≤ 3 * B * h := by
    rw [show (1 / (2 * Real.pi)) * (2 * (2 * B * (2 * H))) = 4 * B * H / Real.pi by
      field_simp; ring]
    rw [div_le_iff₀ hpi0]
    have h1 : B * H ≤ B * (2 * h) := mul_le_mul_of_nonneg_left (by linarith) hB
    have hBh : 0 ≤ B * h := mul_nonneg hB hh0.le
    have h2 := mul_le_mul_of_nonneg_left hpi.le hBh
    nlinarith
  have hk2 : (1 / (2 * Real.pi)) * (2 * (J * (3 * B * (4 * (A + H₁)) / (x / h)))) ≤
      8 * J * B * h := by
    have hAH : A + H₁ ≤ 2 * x := by linarith
    have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg _
    rw [show (1 / (2 * Real.pi)) * (2 * (J * (3 * B * (4 * (A + H₁)) / (x / h)))) =
      12 * J * B * (A + H₁) * h / (Real.pi * x) by field_simp; ring]
    rw [div_le_iff₀ (by positivity)]
    have : J * B * (A + H₁) ≤ J * B * (2 * x) :=
      mul_le_mul_of_nonneg_left hAH (by positivity)
    have hJB : 0 ≤ J * B * x * h := by positivity
    nlinarith
  have hk3 : (1 / (2 * Real.pi)) * (2 * T₀ * (4992 * (2 * H * (T₀ * H₁ / A)))) ≤
      26000 * T₀ ^ 2 * h * h₁ / x := by
    have hHh : H ≤ 2 * h := by linarith
    have hH₁h : H₁ ≤ 2 * h₁ := by linarith
    have hAx : x / 2 ≤ A := by linarith
    rw [show (1 / (2 * Real.pi)) * (2 * T₀ * (4992 * (2 * H * (T₀ * H₁ / A)))) =
      9984 * T₀ ^ 2 * (H * H₁) / (Real.pi * A) by field_simp; ring]
    rw [div_le_div_iff₀ (by positivity) hx0]
    have hHH : H * H₁ ≤ (2 * h) * (2 * h₁) := mul_le_mul hHh hH₁h hH₁0 (by linarith)
    have hT2 : 0 ≤ T₀ ^ 2 := by positivity
    have e1 : 9984 * T₀ ^ 2 * (H * H₁) * x ≤ 9984 * T₀ ^ 2 * (4 * h * h₁) * x := by
      have := mul_le_mul_of_nonneg_left hHH (by positivity : (0 : ℝ) ≤ 9984 * T₀ ^ 2)
      nlinarith
    have e2 : 9984 * T₀ ^ 2 * (4 * h * h₁) * x ≤ 26000 * T₀ ^ 2 * h * h₁ * (Real.pi * A) := by
      have hpA : 2 * x ≤ Real.pi * A := by
        have := mul_le_mul_of_nonneg_right hpi.le hA0.le
        linarith
      have hThh : 0 ≤ T₀ ^ 2 * h * h₁ :=
        mul_nonneg (mul_nonneg (sq_nonneg _) hh0.le) (by linarith)
      have := mul_le_mul_of_nonneg_left hpA hThh
      nlinarith
    linarith
  have hsplit : (1 / (2 * Real.pi)) * (2 * (2 * B * (2 * H) + J * (3 * B * (4 * (A + H₁)) / (x / h)))
        + 2 * T₀ * (4992 * (2 * H * (T₀ * H₁ / A)))) =
      (1 / (2 * Real.pi)) * (2 * (2 * B * (2 * H))) +
        (1 / (2 * Real.pi)) * (2 * (J * (3 * B * (4 * (A + H₁)) / (x / h)))) +
        (1 / (2 * Real.pi)) * (2 * T₀ * (4992 * (2 * H * (T₀ * H₁ / A)))) := by ring
  rw [hsplit]
  have : (3 + 8 * (J : ℝ)) * B * h = 3 * B * h + 8 * J * B * h := by ring
  rw [this]
  have hQe : 10400 * h * Q / 2 ^ J =
      10400 * h * Real.log (8 * x) ^ 2 * (1 + Real.log (8 * x)) / 2 ^ J := by rw [hQ]; ring
  linarith

/-- **The deterministic `E₃` window comparison.**  Let `X = √(xP₁)`, `R = √(x/P₁)/2`,
`Y = ⌊X/P₁⌋ - 1`, `T₁ = x/h`.  If `P₁ · P` has the one-sided mean square `α(1 + T/T₁)` above `T₀`
and `P₂` the two-sided mean square `β(1 + T/T₁)`, for all heights up to `T₁ 2^J`, then the short
window sum is `H/H₁` times the long one up to
`(3 + 8J)√(αβ) h + 26000 T₀² h h₁/x + 10400 h (log 8x)²(1 + log 8x)/2^J`, for any sets `B₁` of
primes in `(P₁, 2P₁]` and `B₂` of primes in `(R, 2R]`. -/
theorem abs_mtAllIntervalSumOn_compare_le_of_meanSquares {B₁ B₂ : Finset ℕ} {z Q D E : ℕ}
    {x P₁ h h₁ T₀ α β : ℝ} (J : ℕ) (hx : 3 ≤ x) (hP : 2 ≤ P₁)
    (hXP : 8 * P₁ ≤ Real.sqrt (x * P₁)) (hh : 1 ≤ h) (hhh₁ : h ≤ h₁) (hh₁x : h₁ ≤ x / 2)
    (hB₁ : ∀ p ∈ B₁, p.Prime ∧ P₁ < p ∧ (p : ℝ) ≤ 2 * P₁)
    (hB₂ : ∀ p ∈ B₂, p.Prime ∧ Real.sqrt (x / P₁) / 2 < p ∧
      (p : ℝ) ≤ 2 * (Real.sqrt (x / P₁) / 2)) (hz : 2 ≤ z)
    (hYz : 4 * (⌊Real.sqrt (x * P₁) / P₁⌋₊ - 1) < z ^ 6)
    (hT₀ : 0 < T₀) (hT₀₁ : T₀ ≤ x / h) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hA : ∀ T, T₀ ≤ T → T ≤ x / h * 2 ^ J →
      ∫ t in Set.Icc T₀ T, ‖(∑ p ∈ B₁,
          (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) *
        LSeries (fun n => mtHarmanProposition22SourceAF z Q D E (⌊Real.sqrt (x * P₁) / P₁⌋₊ - 1) n)
          (((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)‖ ^ 2 ≤ α * (1 + T / (x / h)))
    (hB : ∀ T, T₀ ≤ T → T ≤ x / h * 2 ^ J →
      ∫ t in Set.Icc (-T) T, ‖∑ p ∈ B₂,
          (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖ ^ 2 ≤ β * (1 + T / (x / h))) :
    |mtAllIntervalSumOn B₁ B₂ z Q D E x h -
        (((⌊x + h⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) / ((⌊x + h₁⌋₊ - ⌊x⌋₊ : ℕ) : ℝ)) *
          mtAllIntervalSumOn B₁ B₂ z Q D E x h₁|
      ≤ (3 + 8 * J) * Real.sqrt (α * β) * h + 26000 * T₀ ^ 2 * h * h₁ / x
        + 10400 * h * Real.log (8 * x) ^ 2 * (1 + Real.log (8 * x)) / 2 ^ J := by
  classical
  have hx0 : 0 < x := by linarith
  have hh0 : 0 < h := by linarith
  have hP0 : 0 < P₁ := by linarith
  set R := Real.sqrt (x / P₁) / 2 with hRdef
  set Y := ⌊Real.sqrt (x * P₁) / P₁⌋₊ - 1 with hYdef
  set s : ℕ → ℂ := fun n => mtHarmanProposition22SourceAF z Q D E Y n with hsdef
  set T₁ := x / h with hT₁def
  have hT₁1 : 1 ≤ T₁ := by rw [hT₁def, le_div_iff₀ hh0]; linarith
  have hT₁0 : 0 < T₁ := by linarith
  -- scales
  have hR1 : 1 ≤ R := by
    have hX0 : 0 < Real.sqrt (x * P₁) := Real.sqrt_pos.2 (by positivity)
    have hRX : R * Real.sqrt (x * P₁) = x / 2 := by
      rw [hRdef, div_mul_eq_mul_div, ← Real.sqrt_mul (by positivity),
        show x / P₁ * (x * P₁) = x ^ 2 by field_simp, Real.sqrt_sq hx0.le]
    have hXx : Real.sqrt (x * P₁) ≤ x / 2 := by
      rw [Real.sqrt_le_left (by positivity)]
      have hsq := Real.sq_sqrt (show 0 ≤ x * P₁ by positivity)
      have h64 := pow_le_pow_left₀ (by positivity) hXP 2
      rw [hsq] at h64
      have hPx : 64 * P₁ ≤ x := by nlinarith
      nlinarith
    have hRX' : R * Real.sqrt (x * P₁) ≥ 1 * Real.sqrt (x * P₁) := by rw [hRX]; linarith
    exact le_of_mul_le_mul_right hRX' hX0
  have hY1 : 1 ≤ Y := by
    have hV : (8 : ℝ) ≤ Real.sqrt (x * P₁) / P₁ := by rw [le_div_iff₀ hP0]; linarith
    have : 8 ≤ ⌊Real.sqrt (x * P₁) / P₁⌋₊ := Nat.le_floor (by exact_mod_cast hV)
    omega
  obtain ⟨hrange, hM⟩ := mtAllInterval_window_geometry (by linarith) hP hXP
    (by linarith : (0 : ℝ) ≤ h₁) hh₁x (fun p hp => (hB₁ p hp).2) (fun p hp => (hB₂ p hp).2)
  have hM₁ : ⌊x + h₁⌋₊ ≤ ⌊8 * x⌋₊ := Nat.floor_mono (by linarith)
  -- the long window length
  have hfx : (x - 1) < (⌊x⌋₊ : ℝ) := by have := Nat.lt_floor_add_one x; linarith
  have hfx' : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  have hH₁le : ((⌊x + h₁⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) ≤ h₁ + 1 := by
    have hle : ⌊x⌋₊ ≤ ⌊x + h₁⌋₊ := Nat.floor_mono (by linarith)
    rw [Nat.cast_sub hle]
    have : (⌊x + h₁⌋₊ : ℝ) ≤ x + h₁ := Nat.floor_le (by linarith)
    linarith
  have hHle : ((⌊x + h⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) ≤ h + 1 := by
    have hle : ⌊x⌋₊ ≤ ⌊x + h⌋₊ := Nat.floor_mono (by linarith)
    rw [Nat.cast_sub hle]
    have : (⌊x + h⌋₊ : ℝ) ≤ x + h := Nat.floor_le (by linarith)
    linarith
  have hH₁pos : 0 < ((⌊x + h₁⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) := by
    have h2 : ⌊x⌋₊ + 1 ≤ ⌊x + h₁⌋₊ := Nat.le_floor (by push_cast; linarith)
    have : 0 < ⌊x + h₁⌋₊ - ⌊x⌋₊ := by omega
    exact_mod_cast this
  have hlow : (1 : ℝ) ≤ ((⌊x⌋₊ : ℝ) + 1 / 2) / ((⌊x + h₁⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) := by
    rw [le_div_iff₀ hH₁pos]; linarith
  have hT : 0 < T₁ * 2 ^ J := by positivity
  have hcomp := abs_mtAllIntervalSumOn_compare_le (fun p hp => (hB₁ p hp).1)
    (fun p hp => (hB₂ p hp).1) (Q := Q) (D := D) (E := E) (T := T₁ * 2 ^ J) hz hYz hx0.le hh hhh₁ hT one_pos hrange hM hM₁ hlow
  refine hcomp.trans ?_
  -- the polynomial
  have hB₁p : ∀ p ∈ B₁, 0 < p := fun p hp => (hB₁ p hp).1.pos
  have hB₂p : ∀ p ∈ B₂, 0 < p := fun p hp => (hB₂ p hp).1.pos
  have hsupp : ∀ m, s m ≠ 0 → m ∈ Finset.Icc 1 (4 * Y) := by
    intro m hm
    obtain ⟨hm0, -, hhi⟩ := mtRealIntervalAF_scaleSupported _ _ _ hm
    exact Finset.mem_Icc.2 ⟨hm0, by
      exact_mod_cast (show (m : ℝ) ≤ ((4 * Y : ℕ) : ℝ) by push_cast; exact hhi)⟩
  have hfac : ∀ t, perronPoly (mtAllIntervalCoeff B₁ B₂ s) ⌊8 * x⌋₊ 1 t =
      ((∑ p ∈ B₁, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) * perronPoly s (4 * Y) 1 t) *
        (∑ p ∈ B₂, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) := by
    intro t
    rw [perronPoly_mtAllIntervalCoeff hB₁p hB₂p hsupp hM t]
    ring
  set F : ℝ → ℂ := fun t => perronPoly (mtAllIntervalCoeff B₁ B₂ s) ⌊8 * x⌋₊ 1 t with hFdef
  have hFc : Continuous F := continuous_perronPoly _ _ _
  have hFeven : ∀ t, ‖F (-t)‖ = ‖F t‖ := fun t =>
    norm_perronPoly_neg (conj_mtAllIntervalCoeff fun m => conj_mtHarmanProposition22SourceAF _ _ _ _ _ m)
      _ _ t
  have hB₁facts : ∀ p ∈ B₁, P₁ < p ∧ (p : ℝ) ≤ 2 * P₁ := fun p hp => (hB₁ p hp).2
  have hB₂facts : ∀ p ∈ B₂, R < p ∧ (p : ℝ) ≤ 2 * R := fun p hp => (hB₂ p hp).2
  have hsup : ∀ t ∈ Set.Icc (-T₀) T₀, ‖F t‖ ≤ 4992 := by
    intro t _
    rw [hFdef]
    dsimp only
    rw [hfac t, norm_mul, norm_mul]
    have h1 := norm_primeSetPoly_le_two (fun p hp => (hB₁ p hp).1) (by linarith) hB₁facts t
    have h2 := norm_primeSetPoly_le_two (fun p hp => (hB₂ p hp).1) hR1 hB₂facts t
    have h3 := norm_perronPoly_harmanSource_le (Q := Q) (D := D) (E := E) hz hYz hY1 t
    calc ‖∑ p ∈ B₁, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖ * ‖perronPoly s (4 * Y) 1 t‖ *
          ‖∑ p ∈ B₂, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))‖ ≤ 2 * 1248 * 2 := by
          gcongr
      _ = 4992 := by norm_num
  have hAc : Continuous fun t : ℝ =>
      (∑ p ∈ B₁, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) * perronPoly s (4 * Y) 1 t :=
    (continuous_primeSetPoly B₁ (fun h => by simpa using hB₁p 0 h)).mul (continuous_perronPoly _ _ _)
  have hPc : Continuous fun t : ℝ => ∑ p ∈ B₂, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I)) :=
    continuous_primeSetPoly B₂ (fun h => by simpa using hB₂p 0 h)
  have hG : ∀ T, T₀ ≤ T → T ≤ T₁ * 2 ^ J → ∫ t in T₀..T, ‖F t‖ ≤
      Real.sqrt (α * β) * (1 + T / T₁) := by
    intro T hT hTJ
    have hA' : ∫ t in Set.Icc T₀ T, ‖(∑ p ∈ B₁, (p : ℂ) ^ (-(((1 : ℝ) : ℂ) + (t : ℝ) * Complex.I))) *
        perronPoly s (4 * Y) 1 t‖ ^ 2 ≤ α * (1 + T / T₁) := by
      have := hA T hT hTJ
      simp_rw [perronPoly_eq_LSeries_of_support hsupp]
      exact this
    have hcs := integral_norm_mul_le_of_meanSquares hAc hPc hT₀.le hT₁0 hα hβ hT hA'
      (hB T hT hTJ)
    refine le_of_eq_of_le ?_ hcs
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hFdef]
    rw [hfac t]
  have hint := integral_norm_mul_windowCompareKernel_le (A := (⌊x⌋₊ : ℝ) + 1 / 2)
    (H := ((⌊x + h⌋₊ - ⌊x⌋₊ : ℕ) : ℝ)) (H₁ := ((⌊x + h₁⌋₊ - ⌊x⌋₊ : ℕ) : ℝ)) hFc hFeven J
    (by positivity) (Nat.cast_nonneg _) hH₁pos hT₀ hT₀₁ hT₁1 hsup hG
  have hE : ∀ E ∈ ({perronNearError (156 * (Nat.log 2 ⌊8 * x⌋₊ : ℝ) ^ 2) ⌊8 * x⌋₊ ⌊x + h⌋₊ 1 (T₁ * 2 ^ J),
      perronNearError (156 * (Nat.log 2 ⌊8 * x⌋₊ : ℝ) ^ 2) ⌊8 * x⌋₊ ⌊x⌋₊ 1 (T₁ * 2 ^ J),
      perronNearError (156 * (Nat.log 2 ⌊8 * x⌋₊ : ℝ) ^ 2) ⌊8 * x⌋₊ ⌊x + h₁⌋₊ 1 (T₁ * 2 ^ J),
      perronNearError (156 * (Nat.log 2 ⌊8 * x⌋₊ : ℝ) ^ 2) ⌊8 * x⌋₊ ⌊x⌋₊ 1 (T₁ * 2 ^ J)} : Set ℝ),
      E ≤ 2600 * x * Real.log (8 * x) ^ 2 * (1 + Real.log (8 * x)) / (x / h * 2 ^ J) := by
    have hfl1 : ∀ y : ℝ, 1 ≤ y → y ≤ 2 * x → 1 ≤ ⌊y⌋₊ ∧ ((⌊y⌋₊ : ℕ) : ℝ) ≤ 2 * x := fun y hy1 hy2 =>
      ⟨Nat.le_floor (by exact_mod_cast hy1), (Nat.floor_le (by linarith)).trans hy2⟩
    intro E hE'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hE'
    rcases hE' with rfl | rfl | rfl | rfl
    · obtain ⟨a1, a2⟩ := hfl1 (x + h) (by linarith) (by linarith)
      exact perronNearError_mtAllInterval_le (by linarith) hT a1 a2
    · obtain ⟨a1, a2⟩ := hfl1 x (by linarith) (by linarith)
      exact perronNearError_mtAllInterval_le (by linarith) hT a1 a2
    · obtain ⟨a1, a2⟩ := hfl1 (x + h₁) (by linarith) (by linarith)
      exact perronNearError_mtAllInterval_le (by linarith) hT a1 a2
    · obtain ⟨a1, a2⟩ := hfl1 x (by linarith) (by linarith)
      exact perronNearError_mtAllInterval_le (by linarith) hT a1 a2
  have hρ0 : 0 ≤ ((⌊x + h⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) / ((⌊x + h₁⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) := by positivity
  have hρ1 : ((⌊x + h⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) / ((⌊x + h₁⌋₊ - ⌊x⌋₊ : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one hH₁pos]
    have : ⌊x + h⌋₊ ≤ ⌊x + h₁⌋₊ := Nat.floor_mono (by linarith)
    have : ⌊x + h⌋₊ - ⌊x⌋₊ ≤ ⌊x + h₁⌋₊ - ⌊x⌋₊ := by omega
    exact_mod_cast this
  have hcol := mtAllInterval_error_collect (A := (⌊x⌋₊ : ℝ) + 1 / 2) J hx hh hhh₁ hh₁x hHle
    (Nat.cast_nonneg _) hH₁le (by linarith) (by linarith) (Real.sqrt_nonneg (α * β)) hT₀ hρ0 hρ1 hE
  have hint' := mul_le_mul_of_nonneg_left hint (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))
  simp only [hFdef] at hint'
  rw [← hT₁def] at hcol
  linarith

end

end RHTower.Sieve
