import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Convex.Mul
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The Cardy kernel, the Cardy weight, and the vacuum as a Cardy continuum

The Cardy kernel is `K_α(t) = I₀(4π√(αt)) = Σ (4π²αt)ⁱ/(i!)²` (the identification with the
corpus Bessel series is in `CardyKernelBessel`). Its Laplace transform is

  `2π ∫₀^∞ K_α(t) e^{−2πβt} dt = β⁻¹ e^{2πα/β}`     (`α ≥ 0, β > 0`).

With `a = (c − 1)/24`, the Cardy weight `V = K_a − 2K_{a−1} + K_{a−2}` (`a ≥ 2`) has the series
`Σ (4π²t)ᵏ/(k!)² (aᵏ − 2(a − 1)ᵏ + (a − 2)ᵏ)` with nonnegative coefficients (convexity of `xᵏ`),
so `V(t) ≥ 8π⁴t²`, and the `S`-image of the vacuum character is the Cardy continuum:

  `β⁻¹ e^{2πa/β} (1 − e^{−2π/β})² = 2π ∫₀^∞ V(t) e^{−2πβt} dt`.

Consequences for any functional `g` with `g·V` integrable: the vacuum value
`g_vac = −2π ∫ g V` is `≤ 0` when `g ≥ 0` (no bound reaches below the BTZ threshold), and if
`g_vac ≥ 0` the negative part carries at least half of the Cardy-weighted mass.
-/

noncomputable section

open Real Set MeasureTheory Filter

namespace GaloisForLFunctions.HagedornBootstrap

/-- Transport a sum along pointwise equal terms and an equal value. -/
private theorem hasSum_congr_aux {f g : ℕ → ℝ} {a b : ℝ} (h : HasSum g b) (hf : ∀ n, f n = g n)
    (hab : a = b) : HasSum f a := by
  rw [funext hf, hab]; exact h

/-! ### The Cardy kernel -/

/-- The Cardy kernel `K_α(t) = I₀(4π√(αt)) = Σ (4π²αt)ⁱ/(i!)²`. -/
def cardyKernel (α t : ℝ) : ℝ := ∑' i : ℕ, (4 * π ^ 2 * α * t) ^ i / (i.factorial : ℝ) ^ 2

theorem summable_cardyTerm (x : ℝ) :
    Summable fun i : ℕ => x ^ i / (i.factorial : ℝ) ^ 2 := by
  refine Summable.of_norm_bounded (Real.summable_pow_div_factorial |x|) fun i => ?_
  have hf : (1 : ℝ) ≤ i.factorial := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero i)
  rw [Real.norm_eq_abs, abs_div, abs_pow, abs_of_pos (by positivity : (0 : ℝ) < (i.factorial : ℝ) ^ 2), sq]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (le_mul_of_one_le_left (by positivity) hf)

/-- `K_α(t) = Σ (4π²αt)ⁱ/(i!)²`. -/
theorem hasSum_cardyKernel {α t : ℝ} (_hα : 0 ≤ α) (_ht : 0 ≤ t) :
    HasSum (fun i : ℕ => (4 * π ^ 2 * α * t) ^ i / (i.factorial : ℝ) ^ 2) (cardyKernel α t) :=
  (summable_cardyTerm _).hasSum

theorem cardyKernel_nonneg {α t : ℝ} (hα : 0 ≤ α) (ht : 0 ≤ t) : 0 ≤ cardyKernel α t :=
  (hasSum_cardyKernel hα ht).nonneg fun i => by positivity

/-! ### Laplace transforms -/

theorem integrableOn_pow_mul_exp_neg (k : ℕ) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-(r * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (k : ℝ)) (b := r)
    (by have := k.cast_nonneg (α := ℝ); linarith) le_rfl hr
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp [Real.rpow_natCast, Real.rpow_one, neg_mul]

/-- `∫₀^∞ tᵏ e^{−rt} dt = k!/r^{k+1}`. -/
theorem integral_pow_mul_exp_neg (k : ℕ) {r : ℝ} (hr : 0 < r) :
    ∫ t in Ioi 0, t ^ k * Real.exp (-(r * t)) = k.factorial / r ^ (k + 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (k : ℝ) + 1) (r := r) (by positivity) hr
  rw [Real.Gamma_nat_eq_factorial] at h
  have hc : ∫ t in Ioi 0, t ^ k * Real.exp (-(r * t)) =
      ∫ t in Ioi (0 : ℝ), t ^ ((k : ℝ) + 1 - 1) * Real.exp (-(r * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp [Real.rpow_natCast]
  rw [hc, h]
  have e : (1 / r) ^ ((k : ℝ) + 1) = 1 / r ^ (k + 1) := by
    rw [show ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast, one_div_pow]
  rw [e]
  field_simp

/-- **The Laplace transform of the Cardy kernel:** `2π∫₀^∞ K_α e^{−2πβt} = β⁻¹ e^{2πα/β}`. -/
theorem laplace_cardyKernel {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 < β) :
    2 * π * ∫ t in Ioi 0, cardyKernel α t * Real.exp (-(2 * π * β * t)) =
      β⁻¹ * Real.exp (2 * π * α / β) := by
  set r := 2 * π * β with hr
  have hr0 : 0 < r := by positivity
  set c : ℕ → ℝ := fun i => (4 * π ^ 2 * α) ^ i / (i.factorial : ℝ) ^ 2 with hc
  set F : ℕ → ℝ → ℝ := fun i t => c i * (t ^ i * Real.exp (-(r * t))) with hF
  have hFint : ∀ i, Integrable (F i) (volume.restrict (Ioi 0)) := fun i =>
    (integrableOn_pow_mul_exp_neg i hr0).const_mul (c i)
  have hFval : ∀ i, ∫ t in Ioi 0, F i t = c i * (i.factorial / r ^ (i + 1)) := fun i => by
    simp only [hF]; rw [integral_const_mul, integral_pow_mul_exp_neg i hr0]
  have hFnorm : ∀ i, ∫ t in Ioi 0, ‖F i t‖ = ∫ t in Ioi 0, F i t := fun i => by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have : 0 ≤ F i t := by
      simp only [hF, hc]; have := (mem_Ioi.mp ht).le; positivity
    exact Real.norm_of_nonneg this
  -- the coefficient series is `r⁻¹ Σ (4π²α/r)ⁱ/i!`
  have hcoef : ∀ i, c i * (i.factorial / r ^ (i + 1)) = r⁻¹ * ((4 * π ^ 2 * α / r) ^ i / i.factorial) := by
    intro i
    have hf : (i.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos i).ne'
    simp only [hc]
    rw [div_pow]
    field_simp
    ring
  have hexp : HasSum (fun i : ℕ => (4 * π ^ 2 * α / r) ^ i / i.factorial)
      (Real.exp (4 * π ^ 2 * α / r)) := by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp _
  have hsumI : HasSum (fun i => ∫ t in Ioi 0, F i t) (r⁻¹ * Real.exp (4 * π ^ 2 * α / r)) := by
    simp_rw [hFval, hcoef]; exact hexp.mul_left r⁻¹
  have hswap := integral_tsum_of_summable_integral_norm hFint
    (by simp_rw [hFnorm]; exact hsumI.summable)
  rw [hsumI.tsum_eq] at hswap
  have hpt : ∫ t in Ioi 0, (∑' i, F i t) = ∫ t in Ioi 0, cardyKernel α t * Real.exp (-(r * t)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht0 := (mem_Ioi.mp ht).le
    have hk := (hasSum_cardyKernel hα ht0).mul_right (Real.exp (-(r * t)))
    rw [← hk.tsum_eq]
    congr 1; funext i
    simp only [hF, hc]
    rw [mul_pow]; ring
  rw [hpt] at hswap
  rw [show (fun t => cardyKernel α t * Real.exp (-(2 * π * β * t))) =
    fun t => cardyKernel α t * Real.exp (-(r * t)) from rfl, ← hswap]
  have hπ : π ≠ 0 := Real.pi_ne_zero
  rw [hr, show 4 * π ^ 2 * α / (2 * π * β) = 2 * π * α / β by field_simp; ring]
  field_simp

/-! ### The Cardy weight -/

/-- The second difference `aᵏ − 2(a − 1)ᵏ + (a − 2)ᵏ`. -/
def secondDiffPow (a : ℝ) (k : ℕ) : ℝ := a ^ k - 2 * (a - 1) ^ k + (a - 2) ^ k

/-- Convexity of `xᵏ` on `[0, ∞)`: the second difference is nonnegative for `a ≥ 2`. -/
theorem secondDiffPow_nonneg {a : ℝ} (ha : 2 ≤ a) (k : ℕ) : 0 ≤ secondDiffPow a k := by
  have hc := (convexOn_pow (𝕜 := ℝ) k).2 (show a - 2 ∈ Ici (0 : ℝ) from by simp; linarith)
    (show a ∈ Ici (0 : ℝ) from by simp; linarith) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hc
  rw [show 1 / 2 * (a - 2) + 1 / 2 * a = a - 1 by ring] at hc
  unfold secondDiffPow
  linarith

theorem secondDiffPow_two (a : ℝ) : secondDiffPow a 2 = 2 := by unfold secondDiffPow; ring

/-- The Cardy weight `V = K_a − 2K_{a−1} + K_{a−2}`. -/
def cardyWeight (a t : ℝ) : ℝ := cardyKernel a t - 2 * cardyKernel (a - 1) t + cardyKernel (a - 2) t

/-- `V(t) = Σ (4π²t)ᵏ/(k!)² (aᵏ − 2(a − 1)ᵏ + (a − 2)ᵏ)`. -/
theorem hasSum_cardyWeight {a t : ℝ} (ha : 2 ≤ a) (ht : 0 ≤ t) :
    HasSum (fun k : ℕ => (4 * π ^ 2 * t) ^ k / (k.factorial : ℝ) ^ 2 * secondDiffPow a k)
      (cardyWeight a t) := by
  have h1 := hasSum_cardyKernel (by linarith : (0 : ℝ) ≤ a) ht
  have h2 := hasSum_cardyKernel (by linarith : (0 : ℝ) ≤ a - 1) ht
  have h3 := hasSum_cardyKernel (by linarith : (0 : ℝ) ≤ a - 2) ht
  refine hasSum_congr_aux ((h1.sub (h2.mul_left 2)).add h3) (fun k => ?_) rfl
  have hfac : ∀ α : ℝ, (4 * π ^ 2 * α * t) ^ k = (4 * π ^ 2 * t) ^ k * α ^ k := fun α => by
    rw [show 4 * π ^ 2 * α * t = (4 * π ^ 2 * t) * α by ring, mul_pow]
  unfold secondDiffPow
  rw [hfac a, hfac (a - 1), hfac (a - 2)]
  ring

/-- **The Cardy weight is at least `8π⁴t²`.** -/
theorem cardyWeight_ge {a t : ℝ} (ha : 2 ≤ a) (ht : 0 ≤ t) : 8 * π ^ 4 * t ^ 2 ≤ cardyWeight a t := by
  have hs := hasSum_cardyWeight ha ht
  have hle := le_hasSum hs 2 (fun k _ => by
    have := secondDiffPow_nonneg ha k; positivity)
  rw [secondDiffPow_two] at hle
  norm_num [Nat.factorial] at hle
  nlinarith [hle]

theorem cardyWeight_nonneg {a t : ℝ} (ha : 2 ≤ a) (ht : 0 ≤ t) : 0 ≤ cardyWeight a t :=
  le_trans (by positivity) (cardyWeight_ge ha ht)

/-- The Cardy weight increases with `t`. -/
theorem cardyWeight_mono {a s t : ℝ} (ha : 2 ≤ a) (hs : 0 ≤ s) (hst : s ≤ t) :
    cardyWeight a s ≤ cardyWeight a t := by
  refine hasSum_le (fun k => ?_) (hasSum_cardyWeight ha hs) (hasSum_cardyWeight ha (hs.trans hst))
  have := secondDiffPow_nonneg ha k
  have : (4 * π ^ 2 * s) ^ k ≤ (4 * π ^ 2 * t) ^ k :=
    pow_le_pow_left₀ (by positivity) (by nlinarith [Real.pi_pos]) k
  gcongr

/-- **The vacuum is a Cardy continuum:**
`β⁻¹ e^{2πa/β}(1 − e^{−2π/β})² = 2π∫₀^∞ V(t) e^{−2πβt} dt`. -/
theorem vacuum_eq_cardy_continuum {a β : ℝ} (ha : 2 ≤ a) (hβ : 0 < β) :
    β⁻¹ * Real.exp (2 * π * a / β) * (1 - Real.exp (-(2 * π / β))) ^ 2 =
      2 * π * ∫ t in Ioi 0, cardyWeight a t * Real.exp (-(2 * π * β * t)) := by
  have hr : 0 < 2 * π * β := by positivity
  have hi : ∀ α : ℝ, 0 ≤ α → Integrable (fun t => cardyKernel α t * Real.exp (-(2 * π * β * t)))
      (volume.restrict (Ioi 0)) := by
    intro α hα
    -- dominated by the termwise-integrable series: integrable since the Laplace integral converges
    by_contra hni
    have h0 := integral_undef hni
    have := laplace_cardyKernel hα hβ
    rw [h0, mul_zero] at this
    have : 0 < β⁻¹ * Real.exp (2 * π * α / β) := by positivity
    linarith
  have e : (fun t => cardyWeight a t * Real.exp (-(2 * π * β * t))) =
      fun t => cardyKernel a t * Real.exp (-(2 * π * β * t)) -
        2 * (cardyKernel (a - 1) t * Real.exp (-(2 * π * β * t))) +
        cardyKernel (a - 2) t * Real.exp (-(2 * π * β * t)) := by
    funext t; unfold cardyWeight; ring
  have i1 := hi a (by linarith)
  have i2 := hi (a - 1) (by linarith)
  have i3 := hi (a - 2) (by linarith)
  have i12 : Integrable (fun t => cardyKernel a t * Real.exp (-(2 * π * β * t)) -
      2 * (cardyKernel (a - 1) t * Real.exp (-(2 * π * β * t)))) (volume.restrict (Ioi 0)) :=
    i1.sub (i2.const_mul 2)
  rw [e, integral_add i12 i3, integral_sub i1 (i2.const_mul 2), integral_const_mul]
  have l1 := laplace_cardyKernel (by linarith : (0 : ℝ) ≤ a) hβ
  have l2 := laplace_cardyKernel (by linarith : (0 : ℝ) ≤ a - 1) hβ
  have l3 := laplace_cardyKernel (by linarith : (0 : ℝ) ≤ a - 2) hβ
  have e2 : Real.exp (2 * π * (a - 1) / β) = Real.exp (2 * π * a / β) * Real.exp (-(2 * π / β)) := by
    rw [← Real.exp_add]; congr 1; ring
  have e3 : Real.exp (2 * π * (a - 2) / β) = Real.exp (2 * π * a / β) * Real.exp (-(2 * π / β)) ^ 2 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  rw [e2] at l2
  rw [e3] at l3
  linear_combination -l1 + 2 * l2 - l3

/-! ### Functionals against the Cardy weight -/

/-- **No bound below the BTZ threshold.** A functional `g ≥ 0` has vacuum value
`−2π∫ g V ≤ 0`. -/
theorem vacuum_value_nonpos_of_nonneg {a : ℝ} (ha : 2 ≤ a) {g : ℝ → ℝ}
    (hg : ∀ t, 0 ≤ t → 0 ≤ g t) :
    -(2 * π * ∫ t in Ioi 0, g t * cardyWeight a t) ≤ 0 := by
  have : 0 ≤ ∫ t in Ioi 0, g t * cardyWeight a t :=
    setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (hg t (mem_Ioi.mp ht).le) (cardyWeight_nonneg ha (mem_Ioi.mp ht).le)
  have : 0 ≤ 2 * π * ∫ t in Ioi 0, g t * cardyWeight a t := by positivity
  linarith

/-- **The half-mass condition.** If `∫ g dμ ≤ 0` then the negative part of `g` carries at least
half of the total mass `∫ |g| dμ`. -/
theorem half_mass_of_integral_nonpos {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : α → ℝ} (hg : Integrable g μ) (h : ∫ x, g x ∂μ ≤ 0) :
    (∫ x, |g x| ∂μ) / 2 ≤ ∫ x, max (-g x) 0 ∂μ := by
  have hpos : ∫ x, |g x| ∂μ = ∫ x, max (g x) 0 ∂μ + ∫ x, max (-g x) 0 ∂μ := by
    rw [← integral_add hg.pos_part hg.neg_part]
    congr 1; funext x
    rcases le_total 0 (g x) with hx | hx
    · rw [abs_of_nonneg hx, max_eq_left hx, max_eq_right (by linarith)]; ring
    · rw [abs_of_nonpos hx, max_eq_right hx, max_eq_left (by linarith)]; ring
  have hsplit : ∫ x, g x ∂μ = ∫ x, max (g x) 0 ∂μ - ∫ x, max (-g x) 0 ∂μ := by
    rw [← integral_sub hg.pos_part hg.neg_part]
    congr 1; funext x
    rcases le_total 0 (g x) with hx | hx
    · rw [max_eq_left hx, max_eq_right (by linarith)]; ring
    · rw [max_eq_right hx, max_eq_left (by linarith)]; ring
  linarith

end GaloisForLFunctions.HagedornBootstrap
