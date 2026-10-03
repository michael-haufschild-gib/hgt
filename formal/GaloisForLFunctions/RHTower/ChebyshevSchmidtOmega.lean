import GaloisForLFunctions.RHTower.WeilLagFunctionOmega
import GaloisForLFunctions.RHTower.WeilLagFunctionFrontier
import GaloisForLFunctions.RHTower.PoleSelfEnergyLimit

/-!
# Schmidt's oscillation theorem: `ψ(x) - x = Ω±(√x)`

The genus-kernel prime error is a tail integral of the Chebyshev error `E = ψ - id`:

```text
E_g(n) = -n ∫_n^∞ E(t) t^{-2} dt - log 2π + S(n),      0 ≤ S(n) ≤ 1.
```

A one-sided bound `E(t) ≥ -c√t` on `[x₀, ∞)` gives `E_g(n) ≤ 2c√n + 1 - log 2π`, and `E(t) ≤ c√t`
gives `E_g(n) ≥ -2c√n - log 2π`.  The unconditional law `genusKernelError_omega_pm`
(`E_g(n) > (P - ε)√n` and `E_g(n) ≤ -η√n` infinitely often, `P = 2 + γ - log 4π`) excludes both
for small `c`, so unconditionally

```text
ψ(x) - x < -c√x   and   ψ(x) - x > c√x   for arbitrarily large x.
```

In particular `ψ(x) - x ≠ o(√x)`: the Riemann-hypothesis error `O(√x log²x)` is sharp up to the
logarithms.
-/

open MeasureTheory Set Filter Topology Asymptotics
open scoped Chebyshev

namespace RHTower

noncomputable section

/-- **The genus-kernel error as a tail integral of the Chebyshev error.** -/
theorem genusKernelError_eq_tail {n : ℕ} (hn : 1 ≤ n) :
    genusKernelError n = -((n : ℝ) * ∫ t in Ioi (n : ℝ), chebyshevError t / t ^ 2)
      - Real.log (2 * Real.pi) + trivialZeroSeriesReal n := by
  have hx : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hdev := mertensDeviation_eq hx
  rw [Nat.floor_natCast, ← mertensSum_eq_Icc_zero] at hdev
  have hE : chebyshevError n = ψ n - n := rfl
  have h1 : (n : ℝ) * (mertensSum n - Real.log n + Real.eulerMascheroniConstant)
      = chebyshevError n - n * ∫ t in Ioi (n : ℝ), chebyshevError t / t ^ 2 := by
    rw [hdev]; field_simp
  unfold genusKernelError
  rw [h1, hE]
  ring

/-- `∫_n^∞ √t/t² dt = 2/√n`. -/
theorem integral_Ioi_sqrt_div_sq {n : ℝ} (hn : 0 < n) :
    ∫ t in Ioi n, Real.sqrt t / t ^ 2 = 2 / Real.sqrt n := by
  have heq : EqOn (fun t : ℝ => Real.sqrt t / t ^ 2) (fun t => t ^ (-(3 : ℝ) / 2)) (Ioi n) := by
    intro t ht
    have ht0 : 0 < t := lt_trans hn ht
    simp only
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast t 2, ← Real.rpow_sub ht0]
    norm_num
  rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_Ioi_rpow_of_lt (by norm_num) hn,
    Real.sqrt_eq_rpow, show (-(3 : ℝ) / 2 + 1) = -(1 / 2) by norm_num, Real.rpow_neg hn.le]
  have hp : 0 < n ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hn _
  field_simp

theorem integrableOn_Ioi_sqrt_div_sq {n : ℝ} (hn : 0 < n) :
    IntegrableOn (fun t : ℝ => Real.sqrt t / t ^ 2) (Ioi n) := by
  have heq : EqOn (fun t : ℝ => t ^ (-(3 : ℝ) / 2)) (fun t => Real.sqrt t / t ^ 2) (Ioi n) := by
    intro t ht
    have ht0 : 0 < t := lt_trans hn ht
    simp only
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast t 2, ← Real.rpow_sub ht0]
    norm_num
  exact (integrableOn_Ioi_rpow_of_lt (by norm_num) hn).congr_fun heq measurableSet_Ioi

/-- A lower bound `E(t) ≥ -c√t` beyond `x₀` bounds the tail integral below by `-2c/√n`. -/
theorem tail_integral_ge_of_lower {c x₀ n : ℝ} (hn1 : 1 ≤ n) (hx₀ : x₀ ≤ n)
    (h : ∀ t, x₀ ≤ t → -(c * Real.sqrt t) ≤ chebyshevError t) :
    -(c * (2 / Real.sqrt n)) ≤ ∫ t in Ioi n, chebyshevError t / t ^ 2 := by
  have hn0 : 0 < n := by linarith
  have hint : IntegrableOn (fun t : ℝ => chebyshevError t / t ^ 2) (Ioi n) :=
    integrableOn_chebyshevError_div_sq.mono_set (Ioi_subset_Ioi hn1)
  have hint2 : IntegrableOn (fun t : ℝ => -c * (Real.sqrt t / t ^ 2)) (Ioi n) :=
    (integrableOn_Ioi_sqrt_div_sq hn0).const_mul (-c)
  have hmono := setIntegral_mono_on hint2 hint measurableSet_Ioi (fun t ht => by
    have ht0 : 0 < t := lt_trans hn0 ht
    have h1 := h t (le_trans hx₀ (le_of_lt ht))
    have h2 : -c * (Real.sqrt t / t ^ 2) = -(c * Real.sqrt t) / t ^ 2 := by ring
    rw [h2]
    exact div_le_div_of_nonneg_right h1 (by positivity))
  rw [integral_const_mul, integral_Ioi_sqrt_div_sq hn0] at hmono
  linarith

/-- An upper bound `E(t) ≤ c√t` beyond `x₀` bounds the tail integral above by `2c/√n`. -/
theorem tail_integral_le_of_upper {c x₀ n : ℝ} (hn1 : 1 ≤ n) (hx₀ : x₀ ≤ n)
    (h : ∀ t, x₀ ≤ t → chebyshevError t ≤ c * Real.sqrt t) :
    ∫ t in Ioi n, chebyshevError t / t ^ 2 ≤ c * (2 / Real.sqrt n) := by
  have hn0 : 0 < n := by linarith
  have hint : IntegrableOn (fun t : ℝ => chebyshevError t / t ^ 2) (Ioi n) :=
    integrableOn_chebyshevError_div_sq.mono_set (Ioi_subset_Ioi hn1)
  have hint2 : IntegrableOn (fun t : ℝ => c * (Real.sqrt t / t ^ 2)) (Ioi n) :=
    (integrableOn_Ioi_sqrt_div_sq hn0).const_mul c
  have hmono := setIntegral_mono_on hint hint2 measurableSet_Ioi (fun t ht => by
    have ht0 : 0 < t := lt_trans hn0 ht
    have h1 := h t (le_trans hx₀ (le_of_lt ht))
    have h2 : c * (Real.sqrt t / t ^ 2) = c * Real.sqrt t / t ^ 2 := by ring
    rw [h2]
    exact div_le_div_of_nonneg_right h1 (by positivity))
  rw [integral_const_mul, integral_Ioi_sqrt_div_sq hn0] at hmono
  exact hmono

theorem one_lt_log_two_pi : 1 < Real.log (2 * Real.pi) := by
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  have := Real.exp_one_lt_d9
  have := Real.pi_gt_three
  linarith

/-- `n · (2c/√n) = 2c√n`. -/
theorem nat_mul_two_div_sqrt {c n : ℝ} (hn : 0 < n) :
    n * (c * (2 / Real.sqrt n)) = 2 * c * Real.sqrt n := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  have h1 : n / Real.sqrt n = Real.sqrt n := Real.div_sqrt
  calc n * (c * (2 / Real.sqrt n)) = 2 * c * (n / Real.sqrt n) := by ring
    _ = 2 * c * Real.sqrt n := by rw [h1]

/-- **`ψ(x) - x = Ω₋(√x)`.**  With `P = 2 + γ - log 4π > 0`, `ψ(x) - x < -(P/4)√x` for arbitrarily
large `x`. -/
theorem frequently_chebyshevError_lt_neg_sqrt :
    ∃ᶠ x : ℝ in atTop, chebyshevError x < -(poleSharpConstant / 4 * Real.sqrt x) := by
  have hP := poleSharpConstant_pos
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hcon
  have hlow : ∀ t, x₀ ≤ t → -(poleSharpConstant / 4 * Real.sqrt t) ≤ chebyshevError t :=
    fun t ht => le_of_not_gt (hx₀ t ht)
  have hfreq := (genusKernelError_omega_pm.1 (poleSharpConstant / 2) (by linarith)).and_eventually
    (eventually_ge_atTop (max ⌈x₀⌉₊ 1))
  obtain ⟨n, hn, hnx⟩ := hfreq.exists
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hnx
  have hnx₀ : x₀ ≤ n := le_trans (Nat.le_ceil x₀) (by exact_mod_cast le_trans (le_max_left _ _) hnx)
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := by linarith
  have htail := tail_integral_ge_of_lower hn1' hnx₀ hlow
  have hmul := mul_le_mul_of_nonneg_left htail hn0.le
  rw [mul_neg, nat_mul_two_div_sqrt hn0] at hmul
  have hS := trivialZeroSeriesReal_le_one hn1'
  have hlog := one_lt_log_two_pi
  rw [genusKernelError_eq_tail hn1] at hn
  have hsq : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  nlinarith

/-- **`ψ(x) - x = Ω₊(√x)`.** -/
theorem exists_frequently_sqrt_lt_chebyshevError :
    ∃ c : ℝ, 0 < c ∧ ∃ᶠ x : ℝ in atTop, c * Real.sqrt x < chebyshevError x := by
  obtain ⟨η, hη, hfreq⟩ := genusKernelError_omega_pm.2
  refine ⟨η / 4, by linarith, ?_⟩
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hcon
  have hup : ∀ t, x₀ ≤ t → chebyshevError t ≤ η / 4 * Real.sqrt t :=
    fun t ht => le_of_not_gt (hx₀ t ht)
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hbig := hsqrt.eventually_gt_atTop (2 * Real.log (2 * Real.pi) / η)
  obtain ⟨n, ⟨hn, hnx⟩, hnbig⟩ :=
    ((hfreq.and_eventually (eventually_ge_atTop (max ⌈x₀⌉₊ 1))).and_eventually hbig).exists
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hnx
  have hnx₀ : x₀ ≤ n := le_trans (Nat.le_ceil x₀) (by exact_mod_cast le_trans (le_max_left _ _) hnx)
  have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < n := by linarith
  have htail := tail_integral_le_of_upper hn1' hnx₀ hup
  have hmul := mul_le_mul_of_nonneg_left htail hn0.le
  rw [nat_mul_two_div_sqrt hn0] at hmul
  have hS := trivialZeroSeriesReal_nonneg hn1'
  rw [genusKernelError_eq_tail hn1] at hn
  have hbig' : 2 * Real.log (2 * Real.pi) < η * Real.sqrt n := by
    rw [div_lt_iff₀ hη] at hnbig; linarith
  nlinarith

/-- **Schmidt's oscillation theorem.**  For some `c > 0`, `ψ(x) - x < -c√x` and `ψ(x) - x > c√x`
each hold for arbitrarily large `x`. -/
theorem chebyshevPsi_sub_omega_pm :
    ∃ c : ℝ, 0 < c ∧ (∃ᶠ x : ℝ in atTop, ψ x - x < -(c * Real.sqrt x))
      ∧ ∃ᶠ x : ℝ in atTop, c * Real.sqrt x < ψ x - x := by
  obtain ⟨cp, hcp, hplus⟩ := exists_frequently_sqrt_lt_chebyshevError
  have hP := poleSharpConstant_pos
  refine ⟨min (poleSharpConstant / 4) cp, lt_min (by linarith) hcp, ?_, ?_⟩
  · refine frequently_chebyshevError_lt_neg_sqrt.mono fun x hx => ?_
    have hs := Real.sqrt_nonneg x
    have := mul_le_mul_of_nonneg_right (min_le_left (poleSharpConstant / 4) cp) hs
    unfold chebyshevError at hx
    linarith
  · refine hplus.mono fun x hx => ?_
    have hs := Real.sqrt_nonneg x
    have := mul_le_mul_of_nonneg_right (min_le_right (poleSharpConstant / 4) cp) hs
    unfold chebyshevError at hx
    linarith

/-- **The square-root barrier.**  `ψ(x) - x` is not `o(√x)`. -/
theorem not_chebyshevPsi_sub_isLittleO_sqrt :
    ¬ (fun x : ℝ => ψ x - x) =o[atTop] fun x => Real.sqrt x := by
  intro h
  obtain ⟨c, hc, -, hplus⟩ := chebyshevPsi_sub_omega_pm
  have hb := h.bound (half_pos hc)
  obtain ⟨x, hx, hb'⟩ := (hplus.and_eventually hb).exists
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg x)] at hb'
  have hs := Real.sqrt_nonneg x
  have habs := le_abs_self (ψ x - x)
  nlinarith

end

end RHTower
