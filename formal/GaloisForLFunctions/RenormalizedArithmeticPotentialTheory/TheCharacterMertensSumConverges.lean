import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.CharactersAreInvisibleToPolarMatching
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartIsTwiceTheMertensLimit
import GaloisForLFunctions.RHTower.DirichletCharacterUnsmoothing
import GaloisForLFunctions.RHTower.WeilFullConeSquareRootScaleRigidity

/-!
# The character Mertens sum converges

Mertens' theorem for characters (`exists_norm_charMertensSum_le`) bounds
`A_χ(y) = Σ_{t ≤ y} χ(t)Λ(t)/t`; the finite part of a character gauge needs its limit. The prime
number theorem for characters, `ψ(x, χ) = O(x e^{−ρ (log x)^{1/10}})`
(`RHTower.exists_characterChebyshevPsi_power_log`), supplies it.

* **Abel summation** (`charMertensSum_eq_abel`):
  `A_χ(N) = ψ(N, χ)/(N + 1) + Σ_{n ≤ N} ψ(n, χ)/(n(n + 1))`.
* **Decay beats every power of the logarithm** (`exp_neg_mul_rpow_tenth_le`):
  `e^{−ρ L^{1/10}} ≤ 4 · 20!/ρ^{20} · (1 + L)^{−2}` for `L ≥ 1`, so the Abel series is dominated by
  `Σ 1/(n (1 + log n)²) < ∞` (`summable_charPsi_div`).
* **Convergence** (`tendsto_charMertensSum`): for `χ ≠ 1`, `A_χ(y) → α_χ = Σ_n ψ(n, χ)/(n(n + 1))`.
* **The finite part of a character gauge** (`exists_abs_charGaugeForm_stepProfile_finitePart_le`):
  for a real character `χ ≠ 1` mod a prime `ℓ`, the gauge `ε(n) = χ(n')` has a convergent Mertens
  sum, `A_ε(y) → α_ε = Re α_χ + Σ_{k ≥ 1} log ℓ/ℓ^k`, and on uniform step profiles
  `P_N(εx) = 2α_ε |x|² + o(mass)`.

So a character gauge has matching coefficient `0` and finite part `2α_ε`: its horizon form is a
scalar `2α_ε` on the uniform profiles, read off the Mertens limit of the character, the value of
`−L′/L(1, χ)` corrected by the powers of `ℓ`.
-/

noncomputable section

open Finset Filter Topology
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics

variable {q : ℕ}

/-- **Abel summation**: `A_χ(N) = ψ(N, χ)/(N + 1) + Σ_{n ≤ N} ψ(n, χ)/(n(n + 1))`. -/
theorem charMertensSum_eq_abel (χ : DirichletCharacter ℂ q) (N : ℕ) :
    charMertensSum χ N = RHTower.characterChebyshevPsi χ N / ((N + 1 : ℕ) : ℂ) +
      ∑ n ∈ Icc 1 N, RHTower.characterChebyshevPsi χ n / ((n * (n + 1) : ℕ) : ℂ) := by
  induction N with
  | zero => simp [charMertensSum, RHTower.characterChebyshevPsi]
  | succ N ih =>
    have hA : charMertensSum χ (N + 1) = charMertensSum χ N +
        χ ((N + 1 : ℕ) : ZMod q) * ((Λ (N + 1) / (N + 1 : ℕ) : ℝ) : ℂ) := by
      rw [charMertensSum, charMertensSum, sum_Icc_succ_top (by omega)]
    have hψ : RHTower.characterChebyshevPsi χ (N + 1) = RHTower.characterChebyshevPsi χ N +
        χ ((N + 1 : ℕ) : ZMod q) * ((Λ (N + 1) : ℝ) : ℂ) := by
      rw [RHTower.characterChebyshevPsi, RHTower.characterChebyshevPsi, sum_Icc_succ_top (by omega)]
    rw [hA, ih, sum_Icc_succ_top (by omega), hψ]
    have h1 : ((N : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero N
    have h2 : ((N : ℂ) + 1 + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (N + 1)
    push_cast
    field_simp
    ring

/-- **Subexponential decay beats `(log)^{−2}`**: `e^{−ρ L^{1/10}} ≤ 4 · 20!/ρ^{20}/(1 + L)²` for
`L ≥ 1`, since `e^t ≥ t^{20}/20!`. -/
theorem exp_neg_mul_rpow_tenth_le {ρ L : ℝ} (hρ : 0 < ρ) (hL : 1 ≤ L) :
    Real.exp (-(ρ * L ^ ((1 : ℝ) / 10))) ≤
      4 * (Nat.factorial 20 : ℝ) / ρ ^ 20 / (1 + L) ^ 2 := by
  have hL0 : 0 ≤ L := by linarith
  have ht : 0 ≤ ρ * L ^ ((1 : ℝ) / 10) := by positivity
  have hpow : (ρ * L ^ ((1 : ℝ) / 10)) ^ 20 = ρ ^ 20 * L ^ 2 := by
    rw [mul_pow, ← Real.rpow_natCast (L ^ ((1 : ℝ) / 10)), ← Real.rpow_mul hL0]
    norm_num
  have hexp := Real.pow_div_factorial_le_exp _ ht 20
  rw [hpow] at hexp
  have hf : (0 : ℝ) < Nat.factorial 20 := by exact_mod_cast Nat.factorial_pos 20
  have hρ20 : 0 < ρ ^ 20 := by positivity
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by positivity)]
  refine le_trans ?_ hexp
  rw [inv_div, div_div_eq_mul_div, div_le_div_iff₀ (by positivity) hf]
  have h2 : (1 + L) ^ 2 ≤ 4 * L ^ 2 := by nlinarith
  have := mul_le_mul_of_nonneg_left h2 (le_of_lt (mul_pos hρ20 hf))
  nlinarith

/-- **The Abel series is absolutely summable** for `χ ≠ 1`. -/
theorem summable_charPsi_div [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Summable (fun n : ℕ => RHTower.characterChebyshevPsi χ n / ((n * (n + 1) : ℕ) : ℂ)) := by
  obtain ⟨ρ, C, x₀, hρ, hC, -, hψ⟩ := RHTower.exists_characterChebyshevPsi_power_log hχ
  set K := 4 * (Nat.factorial 20 : ℝ) / ρ ^ 20 with hK
  have hK0 : 0 ≤ K := by positivity
  refine Summable.of_norm_bounded_eventually_nat
    ((RHTower.summable_invLogWeight (le_refl 2)).mul_left (C * K)) ?_
  filter_upwards [eventually_ge_atTop (max ⌈x₀⌉₊ 3)] with n hn
  have hn3 : 3 ≤ n := (le_max_right _ _).trans hn
  have hnx : x₀ ≤ n := (Nat.le_ceil x₀).trans (by exact_mod_cast (le_max_left _ _).trans hn)
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn3
  have hb := hψ n hnx
  rw [Nat.floor_natCast] at hb
  have hL : 1 ≤ Real.log n := by
    have h3 := Real.log_le_log (by norm_num) hn'
    have := Real.log_three_gt_d9
    norm_num at this
    linarith
  have he := exp_neg_mul_rpow_tenth_le hρ hL
  set e := Real.exp (-(ρ * Real.log n ^ ((1 : ℝ) / 10)))
  have hn0 : (0 : ℝ) < n := by linarith
  rw [norm_div, Complex.norm_natCast, RHTower.invLogWeight]
  push_cast
  calc ‖RHTower.characterChebyshevPsi χ n‖ / ((n : ℝ) * (n + 1))
      ≤ C * n * e / ((n : ℝ) * (n + 1)) := div_le_div_of_nonneg_right hb (by positivity)
    _ = C * e / (n + 1) := by field_simp
    _ ≤ C * e / n := div_le_div_of_nonneg_left (by positivity) hn0 (by linarith)
    _ ≤ C * (K / (1 + Real.log n) ^ 2) / n :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left he hC) hn0.le
    _ = C * K * ((n : ℝ) * (1 + Real.log n) ^ 2)⁻¹ := by
        have : (1 + Real.log n) ^ 2 ≠ 0 := by positivity
        field_simp

/-- The **character Mertens limit** `α_χ = Σ_n ψ(n, χ)/(n(n + 1))`. -/
def charMertensLimit (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑' n : ℕ, RHTower.characterChebyshevPsi χ n / ((n * (n + 1) : ℕ) : ℂ)

/-- **The character Mertens sum converges**: `A_χ(y) → α_χ` for `χ ≠ 1`. -/
theorem tendsto_charMertensSum [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Tendsto (charMertensSum χ) atTop (𝓝 (charMertensLimit χ)) := by
  have hsum := summable_charPsi_div χ hχ
  -- the partial sums of the Abel series
  have hpart : Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N,
      RHTower.characterChebyshevPsi χ n / ((n * (n + 1) : ℕ) : ℂ)) atTop
      (𝓝 (charMertensLimit χ)) := by
    have h := hsum.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
    refine h.congr fun N => ?_
    exact sum_range_succ_eq_sum_Icc (f := fun n =>
      RHTower.characterChebyshevPsi χ n / ((n * (n + 1) : ℕ) : ℂ))
      (by simp [RHTower.characterChebyshevPsi]) N
  -- the boundary term `ψ(N, χ)/(N + 1)` vanishes
  obtain ⟨ρ, C, x₀, hρ, hC, -, hψ⟩ := RHTower.exists_characterChebyshevPsi_power_log hχ
  set K := 4 * (Nat.factorial 20 : ℝ) / ρ ^ 20 with hK
  have hK0 : 0 ≤ K := by positivity
  have hlog : Tendsto (fun N : ℕ => C * K / (1 + Real.log N) ^ 2) atTop (𝓝 0) := by
    refine tendsto_const_nhds.div_atTop ?_
    exact (tendsto_pow_atTop two_ne_zero).comp (tendsto_atTop_add_const_left _ 1
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop))
  have hbdry : Tendsto (fun N : ℕ => RHTower.characterChebyshevPsi χ N / ((N + 1 : ℕ) : ℂ))
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlog
    filter_upwards [eventually_ge_atTop (max ⌈x₀⌉₊ 3)] with N hN
    have hN3 : 3 ≤ N := (le_max_right _ _).trans hN
    have hNx : x₀ ≤ N := (Nat.le_ceil x₀).trans (by exact_mod_cast (le_max_left _ _).trans hN)
    have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    have hb := hψ N hNx
    rw [Nat.floor_natCast] at hb
    have hL : 1 ≤ Real.log N := by
      have h3 := Real.log_le_log (by norm_num) hN'
      have := Real.log_three_gt_d9
      norm_num at this
      linarith
    have he := exp_neg_mul_rpow_tenth_le hρ hL
    have hN0 : (0 : ℝ) < N := by linarith
    rw [norm_div, Complex.norm_natCast]
    push_cast
    calc ‖RHTower.characterChebyshevPsi χ N‖ / ((N : ℝ) + 1)
        ≤ C * N * Real.exp (-(ρ * Real.log N ^ ((1 : ℝ) / 10))) / N :=
          div_le_div₀ (by positivity) hb hN0 (by linarith)
      _ = C * Real.exp (-(ρ * Real.log N ^ ((1 : ℝ) / 10))) := by field_simp
      _ ≤ C * (K / (1 + Real.log N) ^ 2) := mul_le_mul_of_nonneg_left he hC
      _ = C * K / (1 + Real.log N) ^ 2 := by ring
  have h := hbdry.add hpart
  rw [zero_add] at h
  exact h.congr fun N => (charMertensSum_eq_abel χ N).symm

/-! ### The finite part of a character gauge -/

variable {ℓ : ℕ}

/-- The powers of `ℓ` up to `y`: `Σ_{t ≤ y, ℓ ∣ t} Λ(t)/t`. -/
def primePowerMertens (ℓ y : ℕ) : ℝ := ∑ t ∈ Icc 1 y, (if ℓ ∣ t then Λ t / t else 0)

theorem gaugeMertensSum_charGauge_eq (hℓ : ℓ.Prime) (χ : DirichletCharacter ℂ ℓ) (y : ℕ) :
    gaugeMertensSum (charGauge χ) y = (charMertensSum χ y).re + primePowerMertens ℓ y := by
  rw [gaugeMertensSum, charMertensSum, Complex.re_sum, primePowerMertens, ← sum_add_distrib]
  refine sum_congr rfl fun t _ => ?_
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  rw [charGauge_mul_vonMangoldt hℓ χ t]
  split_ifs <;> ring

/-- The powers of `ℓ` contribute a convergent Mertens sum. -/
theorem tendsto_primePowerMertens (hℓ : ℓ.Prime) :
    Tendsto (primePowerMertens ℓ) atTop (𝓝 (⨆ y, primePowerMertens ℓ y)) := by
  refine tendsto_atTop_ciSup (monotone_nat_of_le_succ fun y => ?_) ⟨Real.log ℓ / ((ℓ : ℝ) - 1), ?_⟩
  · rw [primePowerMertens, primePowerMertens, sum_Icc_succ_top (by omega)]
    have : 0 ≤ (if ℓ ∣ y + 1 then Λ (y + 1) / ((y + 1 : ℕ) : ℝ) else 0) := by
      split_ifs
      · exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _)
      · exact le_rfl
    linarith
  · rintro _ ⟨y, rfl⟩
    exact sum_dvd_vonMangoldt_div_le hℓ (Icc 1 y)

/-- **The finite part of a character gauge**: for a real character `χ ≠ 1` mod a prime `ℓ`, the
gauge `ε(n) = χ(n')` has `A_ε(y) → α_ε = Re α_χ + Σ_{k ≥ 1} log ℓ/ℓ^k`, and for every `η > 0`
there is `C` with `|P_N(εx) − 2α_ε|x|²| ≤ Σ_{i,j} |c_i| |c_j| (η H_{min(M_i, M_j)} + C)` on uniform
step profiles. -/
theorem exists_abs_charGaugeForm_stepProfile_finitePart_le (hℓ : ℓ.Prime)
    (χ : DirichletCharacter ℂ ℓ) (hχ : χ ≠ 1) (hreal : ∀ a, (χ a).im = 0) :
    Tendsto (gaugeMertensSum (charGauge χ)) atTop
        (𝓝 ((charMertensLimit χ).re + ⨆ y, primePowerMertens ℓ y)) ∧
      ∀ η > 0, ∃ C : ℝ, ∀ {k N : ℕ} (c : Fin k → ℝ) (M : Fin k → ℕ), (∀ i, 1 ≤ M i) →
        (∀ i, M i ≤ N) →
        |atomicWeilForm N (fun n => charGauge χ n * stepProfile c M n) -
            2 * ((charMertensLimit χ).re + ⨆ y, primePowerMertens ℓ y) *
              ∑ n ∈ Icc 1 N, stepProfile c M n ^ 2| ≤
          ∑ i, ∑ j, |c i| * |c j| * (η * harmonicSum (min (M i) (M j)) + C) := by
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hlim : Tendsto (gaugeMertensSum (charGauge χ)) atTop
      (𝓝 ((charMertensLimit χ).re + ⨆ y, primePowerMertens ℓ y)) := by
    have h := ((Complex.continuous_re.tendsto _).comp (tendsto_charMertensSum χ hχ)).add
      (tendsto_primePowerMertens hℓ)
    exact h.congr fun y => (gaugeMertensSum_charGauge_eq hℓ χ y).symm
  refine ⟨hlim, fun η hη => ?_⟩
  -- matching coefficient `0`: the Mertens error is the Mertens sum itself
  have hE : Tendsto (gaugeMertensError (charGauge χ) 0) atTop
      (𝓝 ((charMertensLimit χ).re + ⨆ y, primePowerMertens ℓ y)) :=
    hlim.congr fun y => by simp [gaugeMertensError]
  obtain ⟨C, hC⟩ := exists_abs_gaugeForm_stepProfile_finitePart_le
    (charGauge_isSignGauge hℓ χ hreal) (by simp : |(0 : ℝ)| ≤ 1) hE hη
  refine ⟨C, fun c M hM1 hM => ?_⟩
  have h := hC c M hM1 hM
  rwa [zero_mul, sub_zero] at h

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
