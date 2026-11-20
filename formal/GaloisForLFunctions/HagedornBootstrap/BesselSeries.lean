import GaloisForLFunctions.HagedornBootstrap.CardyWeight
import GaloisForLFunctions.RHTower.BesselIZeroODE
import GaloisForLFunctions.RHTower.BesselJZeroEnvelope

/-!
# The corpus Bessel functions are the Cardy kernel

The corpus defines `I₀` and `J₀` by their integral representations
`I₀(u) = (1/π)∫₀^π cosh(u sin θ) dθ` and `J₀(u) = (1/π)∫₀^π cos(u sin θ) dθ`. Integrating the
power series of `cosh` and `cos` term by term with Wallis' formula
`∫₀^π sin^{2n} = π (2n)!/(4ⁿ (n!)²)` gives their power series

  `I₀(u) = Σ (u/2)^{2n}/(n!)²`,    `J₀(u) = Σ (−1)ⁿ (u/2)^{2n}/(n!)²`.

Hence both are values of the one entire function of the product `αt` behind the bootstrap,
`K_α(t) = Σ (4π²αt)ⁿ/(n!)²`: the Cardy kernel is `K_α(t) = I₀(4π√(αt))`, and the planar Fourier
kernel of the bootstrap is `J₀(4π√(st)) = K_{−s}(t)`. This is the eigen-identity's continuation
`s ↦ −α` from the Fourier kernel to the Cardy kernel. The corpus `I₀` inherits the Laplace
identity `2π∫₀^∞ I₀(4π√(αt)) e^{−2πβt} dt = β⁻¹ e^{2πα/β}`.
-/

noncomputable section

open Real Set MeasureTheory Finset

namespace GaloisForLFunctions.HagedornBootstrap

/-- `∏_{i<n} (2i + 1)/(2i + 2) = (2n)!/(4ⁿ (n!)²)`. -/
theorem prod_wallis (n : ℕ) :
    ∏ i ∈ range n, (2 * (i : ℝ) + 1) / (2 * i + 2) =
      ((2 * n).factorial : ℝ) / (4 ^ n * (n.factorial : ℝ) ^ 2) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, ih, show 2 * (n + 1) = (2 * n + 1) + 1 by ring, Nat.factorial_succ,
      Nat.factorial_succ (2 * n), Nat.factorial_succ n]
    have h1 : ((n.factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
    push_cast
    field_simp
    ring

/-- **Wallis' formula:** `∫₀^π sin^{2n} = π (2n)!/(4ⁿ (n!)²)`. -/
theorem integral_sin_pow_two_mul (n : ℕ) :
    ∫ x in (0 : ℝ)..π, Real.sin x ^ (2 * n) =
      π * (((2 * n).factorial : ℝ) / (4 ^ n * (n.factorial : ℝ) ^ 2)) := by
  rw [integral_sin_pow_even, prod_wallis]

theorem summable_sq_pow_div_factorial_two_mul (x : ℝ) :
    Summable fun n : ℕ => (x ^ 2) ^ n / ((2 * n).factorial : ℝ) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (Real.summable_pow_div_factorial (x ^ 2))
  apply div_le_div_of_nonneg_left (by positivity) (by exact_mod_cast Nat.factorial_pos n)
  exact_mod_cast Nat.factorial_le (by omega)

/-- **Termwise integration** of an even power series in `u sin θ` over `[0, π]`. -/
theorem integral_tsum_sin_pow (a : ℕ → ℝ) (u : ℝ) (ha : ∀ n, |a n| ≤ 1 / ((2 * n).factorial : ℝ)) :
    ∫ θ in (0 : ℝ)..π, ∑' n, a n * (u * Real.sin θ) ^ (2 * n) =
      ∑' n, a n * u ^ (2 * n) * (π * (((2 * n).factorial : ℝ) / (4 ^ n * (n.factorial : ℝ) ^ 2))) := by
  set F : ℕ → ℝ → ℝ := fun n θ => a n * (u * Real.sin θ) ^ (2 * n) with hF
  have hcont : ∀ n, Continuous (F n) := fun n => by simp only [hF]; fun_prop
  have hint : ∀ n, Integrable (F n) (volume.restrict (Ioc 0 π)) := fun n =>
    (hcont n).integrableOn_Ioc
  -- each term is bounded by `(u²)ⁿ/(2n)!` on a set of measure `π`
  have hbound : ∀ n, ∫ θ in Ioc 0 π, ‖F n θ‖ ≤ π * ((u ^ 2) ^ n / ((2 * n).factorial : ℝ)) := by
    intro n
    have hpt : ∀ θ, ‖F n θ‖ ≤ (u ^ 2) ^ n / ((2 * n).factorial : ℝ) := by
      intro θ
      simp only [hF, Real.norm_eq_abs, abs_mul, abs_pow]
      have hs : |Real.sin θ| ≤ 1 := Real.abs_sin_le_one θ
      have hs2 : |Real.sin θ| ^ 2 ≤ 1 := by nlinarith [abs_nonneg (Real.sin θ)]
      have h1 : (|u| * |Real.sin θ|) ^ (2 * n) ≤ (u ^ 2) ^ n := by
        rw [pow_mul]
        apply pow_le_pow_left₀ (by positivity)
        rw [mul_pow, sq_abs]
        calc u ^ 2 * |Real.sin θ| ^ 2 ≤ u ^ 2 * 1 := mul_le_mul_of_nonneg_left hs2 (sq_nonneg u)
          _ = u ^ 2 := mul_one _
      calc |a n| * (|u| * |Real.sin θ|) ^ (2 * n) ≤ 1 / ((2 * n).factorial : ℝ) * (u ^ 2) ^ n :=
            mul_le_mul (ha n) h1 (by positivity) (by positivity)
        _ = (u ^ 2) ^ n / ((2 * n).factorial : ℝ) := by ring
    calc ∫ θ in Ioc 0 π, ‖F n θ‖ ≤ ∫ θ in Ioc 0 π, (u ^ 2) ^ n / ((2 * n).factorial : ℝ) :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun θ => norm_nonneg _)
            (integrable_const _) (Filter.Eventually.of_forall hpt)
      _ = π * ((u ^ 2) ^ n / ((2 * n).factorial : ℝ)) := by
          rw [setIntegral_const, Real.volume_real_Ioc_of_le Real.pi_pos.le, smul_eq_mul, sub_zero]
  have hsum : Summable fun n => ∫ θ in Ioc 0 π, ‖F n θ‖ :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun θ => norm_nonneg _) hbound
      ((summable_sq_pow_div_factorial_two_mul u).mul_left π)
  rw [intervalIntegral.integral_of_le Real.pi_pos.le, ← integral_tsum_of_summable_integral_norm hint hsum]
  congr 1; funext n
  simp only [hF]
  rw [← intervalIntegral.integral_of_le Real.pi_pos.le, intervalIntegral.integral_const_mul]
  simp_rw [mul_pow]
  rw [intervalIntegral.integral_const_mul, integral_sin_pow_two_mul]
  ring

/-- The coefficient bookkeeping `(1/π)·uⁿ/(2n)!·π(2n)!/(4ⁿ(n!)²) = (u/2)^{2n}/(n!)²`. -/
theorem bessel_coeff (u : ℝ) (n : ℕ) :
    1 / π * (1 / ((2 * n).factorial : ℝ) * u ^ (2 * n) *
      (π * (((2 * n).factorial : ℝ) / (4 ^ n * (n.factorial : ℝ) ^ 2)))) =
      (u / 2) ^ (2 * n) / (n.factorial : ℝ) ^ 2 := by
  have hπ : π ≠ 0 := Real.pi_ne_zero
  have h1 : ((2 * n).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h2 : ((n.factorial : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  rw [div_pow, pow_mul (2 : ℝ), show (2 : ℝ) ^ 2 = 4 by norm_num]
  field_simp

/-- **The corpus `I₀` is its power series:** `I₀(u) = Σ (u/2)^{2n}/(n!)²`. -/
theorem besselI0_eq_tsum (u : ℝ) :
    RHTower.besselI0 u = ∑' n : ℕ, (u / 2) ^ (2 * n) / (n.factorial : ℝ) ^ 2 := by
  unfold RHTower.besselI0
  have hc : ∀ θ, Real.cosh (u * Real.sin θ) =
      ∑' n : ℕ, 1 / ((2 * n).factorial : ℝ) * (u * Real.sin θ) ^ (2 * n) := fun θ => by
    rw [Real.cosh_eq_tsum]; congr 1; funext n; ring
  simp_rw [hc]
  rw [integral_tsum_sin_pow _ u (fun n => by rw [abs_of_pos (by positivity)])]
  rw [← tsum_mul_left]
  congr 1; funext n
  exact bessel_coeff u n

/-- **The corpus `J₀` is its power series:** `J₀(u) = Σ (−1)ⁿ (u/2)^{2n}/(n!)²`. -/
theorem besselJ0_eq_tsum (u : ℝ) :
    RHTower.besselJ0 u = ∑' n : ℕ, (-1) ^ n * ((u / 2) ^ (2 * n) / (n.factorial : ℝ) ^ 2) := by
  unfold RHTower.besselJ0
  have hc : ∀ θ, Real.cos (u * Real.sin θ) =
      ∑' n : ℕ, (-1) ^ n / ((2 * n).factorial : ℝ) * (u * Real.sin θ) ^ (2 * n) := fun θ => by
    rw [← (Real.hasSum_cos _).tsum_eq]; congr 1; funext n; ring
  simp_rw [hc]
  rw [integral_tsum_sin_pow _ u (fun n => by
    rw [abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos (by positivity)])]
  rw [← tsum_mul_left]
  congr 1; funext n
  rw [← bessel_coeff u n]
  ring

/-- `(4π√(αt)/2)^{2n} = (4π²αt)ⁿ` for `αt ≥ 0`. -/
theorem cardy_argument_pow {α t : ℝ} (h : 0 ≤ α * t) (n : ℕ) :
    (4 * π * √(α * t) / 2) ^ (2 * n) = (4 * π ^ 2 * α * t) ^ n := by
  rw [pow_mul]
  congr 1
  rw [show (4 * π * √(α * t) / 2) ^ 2 = 4 * π ^ 2 * √(α * t) ^ 2 by ring, Real.sq_sqrt h]
  ring

/-- **The Cardy kernel is the corpus `I₀`:** `K_α(t) = I₀(4π√(αt))`. -/
theorem cardyKernel_eq_besselI0 {α t : ℝ} (hα : 0 ≤ α) (ht : 0 ≤ t) :
    cardyKernel α t = RHTower.besselI0 (4 * π * √(α * t)) := by
  rw [besselI0_eq_tsum]
  unfold cardyKernel
  congr 1; funext n
  rw [cardy_argument_pow (by positivity)]

/-- **The Fourier kernel is the Cardy kernel at negative `α`:** `J₀(4π√(st)) = K_{−s}(t)`. -/
theorem besselJ0_eq_cardyKernel_neg {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    RHTower.besselJ0 (4 * π * √(s * t)) = cardyKernel (-s) t := by
  rw [besselJ0_eq_tsum]
  unfold cardyKernel
  congr 1; funext n
  have hneg : (4 * π ^ 2 * -s * t) ^ n = (-1) ^ n * (4 * π ^ 2 * s * t) ^ n := by
    rw [show 4 * π ^ 2 * -s * t = -(4 * π ^ 2 * s * t) by ring, neg_pow]
  rw [cardy_argument_pow (by positivity), hneg]
  ring

/-- The corpus `I₀` inherits the Laplace identity of the Cardy kernel. -/
theorem laplace_besselI0 {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) :
    2 * π * ∫ t in Ioi 0, RHTower.besselI0 (4 * π * √(α * t)) * Real.exp (-(2 * π * β * t)) =
      β⁻¹ * Real.exp (2 * π * α / β) := by
  rw [← laplace_cardyKernel hα hβ]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  rw [cardyKernel_eq_besselI0 hα (mem_Ioi.mp ht).le]

end GaloisForLFunctions.HagedornBootstrap
