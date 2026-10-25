import GaloisForLFunctions.HTGeometry.HamburgerGeneralFrequencies
import GaloisForLFunctions.HTGeometry.HamburgerSquareSummable
import GaloisForLFunctions.HTGeometry.ClockSeriesIntegral
import GaloisForLFunctions.RHTower.BeurlingSystemGibbsGauge
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Rigidity of Riemann's functional equation for Beurling systems, generalized frequencies, and Borel measures

Suppose a generalized theta series `θ(x) = Σ a_n e^{-π λ_n² x}` with frequencies `λ_n ≥ 1` and
`Σ ‖a_n‖ / λ_n² < ∞` satisfies Riemann's self-dual transformation law

`θ(x) = x^{-1/2} θ(1/x) + α + β x^{-1/2}`   for all `x > 0`.

Evaluating at `x = 1` immediately gives polar balance `α + β = 0`. On `Re t > 0`, Hamburger's
Laplace identity (`FreqHamburger.freqSeries_eq_of_freqTheta_relation`) equates the partial-fraction
series `L(t) = Σ a_n t / (π(λ_n² + t²))` with `F(t) + α / (π t) + β`, where
`F(t) = Σ a_n e^{-2π λ_n t}`.

Pairing `t = ε + iτ` with `t̄ = ε - iτ` against the Fejér tent weight `1 - τ` on `τ ∈ [0, 1]` and
sending `ε → 0⁺` eliminates `L` completely because every pole `λ_n ≥ 1` lies outside `[0, 1)` and
the linear vanishing of `1 - τ` at `τ = 1` cancels the boundary Cauchy kernel at `λ_n = 1`:

* `∫₀¹ (1 - τ) (L(ε + iτ) + L(ε - iτ)) dτ → 0`;
* `∫₀¹ (1 - τ) (F(ε + iτ) + F(ε - iτ)) dτ → Σ a_n (sin(π λ_n) / (π λ_n))²`;
* `∫₀¹ (1 - τ) (α/(π(ε + iτ)) + α/(π(ε - iτ)) + 2β) dτ → α + β`.

This yields the exact **Fejér–tent spectral gap identity**
`Σ a_n (sin(π λ_n) / (π λ_n))² = -(α + β) = 0` for arbitrary complex coefficients `a_n` without
any separation hypothesis on `λ_n`.

When the coefficients are real and nonnegative, every summand is nonnegative, so `sin(π λ_n) = 0`
on the support: every active frequency is a positive integer `m ∈ ℕ₊`. Grouping by `m ∈ ℕ₊`
reduces `θ` to an ordinary `ℕ₊`-frequency theta series, where `coeff_eq_of_coeffTheta_relation_of_sq`
forces every positive integer to appear with constant total weight `-2α`.

For any countable discrete Beurling generalized prime system `B : RHTower.BeurlingSystem` whose
completed zeta function satisfies Riemann's degree-one reflection law:
1. the empty product `0 : Multiset B.Label` has norm `1`, automatically forcing `α = -1/2` and
   `β = 1/2` (no entire degree-one Beurling Euler product exists);
2. every positive integer occurs as `B.intNorm g` for a unique generalized integer `g`, so
   `beurlingZeta B s = riemannZeta s` on `Re s > 1`;
3. `B.Label` admits a norm-preserving bijection onto the rational primes `{p : ℕ // Nat.Prime p}`.

More generally, in Section 4, for any s-finite nonnegative Borel measure `ν` supported on `[1, ∞)`
with `∫_{u ≥ 1} (1 / u²) dν(u) < ∞` whose theta integral `θ_ν(x) = ∫_{u ≥ 1} e^{-π u² x} dν(u)`
satisfies the self-dual relation `θ_ν(x) = x^{-1/2} θ_ν(1/x) + α + β x^{-1/2}`, Fubini's theorem
and parametric differentiation extend the Laplace and Fejér–tent identities directly to `ν`:
`∫_{u ≥ 1} (sin(π u) / (π u))² dν(u) = 0`, so `ν` is purely atomic on `ℕ₊` with uniform atom mass
`-2α` at every positive integer `m ≥ 1` (and `ν = Σ_{m ≥ 1} δ_m` when `ν.real {1} = 1`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped BigOperators Interval

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## Section 1: The Fejér–tent kernels on `[0, 1]` and the complex spectral gap law -/

/-- Polar balance: any self-dual theta relation `θ(x) = x^{-1/2} θ(1/x) + α + β x^{-1/2}` evaluated
at `x = 1` forces `α + β = 0`. -/
theorem add_eq_zero_of_self_dual_theta {θ : ℝ → ℂ} {α β : ℂ}
    (htheta : ∀ x : ℝ, 0 < x →
      θ x = (x : ℂ) ^ (-(1 / 2 : ℂ)) * θ x⁻¹ + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ))) :
    α + β = 0 := by
  have h1 := htheta 1 one_pos
  rw [Complex.ofReal_one, Complex.one_cpow, inv_one, one_mul, mul_one] at h1
  linear_combination -h1

/-- Symmetric Cauchy kernel combination: `(ε + i u)⁻¹ + (ε - i u)⁻¹ = 2ε / (ε² + u²)` for `ε > 0`. -/
theorem inv_add_mul_I_add_inv_sub_mul_I {ε : ℝ} (hε : 0 < ε) (u : ℝ) :
    1 / ((ε : ℂ) + (u : ℂ) * I) + 1 / ((ε : ℂ) - (u : ℂ) * I) =
      ((2 * ε / (ε ^ 2 + u ^ 2) : ℝ) : ℂ) := by
  have h1 : (ε : ℂ) + (u : ℂ) * I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have h2 : (ε : ℂ) - (u : ℂ) * I ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  have hd : (ε ^ 2 + u ^ 2 : ℝ) ≠ 0 := by positivity
  have hdC : ((ε ^ 2 + u ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd
  rw [Complex.ofReal_div]
  field_simp [h1, h2, hdC]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Partial-fraction sum at conjugate vertical points `ε ± iτ`. -/
theorem partialFraction_conj_pair {l ε τ : ℝ} (hε : 0 < ε) :
    ((ε : ℂ) + (τ : ℂ) * I) /
        ((Real.pi : ℂ) * ((l : ℂ) ^ 2 + ((ε : ℂ) + (τ : ℂ) * I) ^ 2)) +
      ((ε : ℂ) - (τ : ℂ) * I) /
        ((Real.pi : ℂ) * ((l : ℂ) ^ 2 + ((ε : ℂ) - (τ : ℂ) * I) ^ 2)) =
      (((1 / Real.pi) * (ε / (ε ^ 2 + (l - τ) ^ 2) + ε / (ε ^ 2 + (l + τ) ^ 2)) : ℝ) : ℂ) := by
  set t : ℂ := (ε : ℂ) + (τ : ℂ) * I
  set t' : ℂ := (ε : ℂ) - (τ : ℂ) * I
  have hp1 : (ε : ℂ) + ((τ - l : ℝ) : ℂ) * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hp2 : (ε : ℂ) + ((τ + l : ℝ) : ℂ) * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hm1 : (ε : ℂ) - ((τ - l : ℝ) : ℂ) * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hm2 : (ε : ℂ) - ((τ + l : ℝ) : ℂ) * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hfac1 : (l : ℂ) ^ 2 + t ^ 2 =
      ((ε : ℂ) + ((τ - l : ℝ) : ℂ) * I) * ((ε : ℂ) + ((τ + l : ℝ) : ℂ) * I) := by
    simp only [t]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hfac2 : (l : ℂ) ^ 2 + t' ^ 2 =
      ((ε : ℂ) - ((τ - l : ℝ) : ℂ) * I) * ((ε : ℂ) - ((τ + l : ℝ) : ℂ) * I) := by
    simp only [t']
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsplit1 : t / ((l : ℂ) ^ 2 + t ^ 2) =
      (1 / ((ε : ℂ) + ((τ - l : ℝ) : ℂ) * I) + 1 / ((ε : ℂ) + ((τ + l : ℝ) : ℂ) * I)) / 2 := by
    rw [hfac1, one_div_add_one_div hp1 hp2, div_div, div_eq_div_iff (mul_ne_zero hp1 hp2)
      (mul_ne_zero (mul_ne_zero hp1 hp2) two_ne_zero)]
    simp only [t]
    push_cast
    ring
  have hsplit2 : t' / ((l : ℂ) ^ 2 + t' ^ 2) =
      (1 / ((ε : ℂ) - ((τ - l : ℝ) : ℂ) * I) + 1 / ((ε : ℂ) - ((τ + l : ℝ) : ℂ) * I)) / 2 := by
    rw [hfac2, one_div_add_one_div hm1 hm2, div_div, div_eq_div_iff (mul_ne_zero hm1 hm2)
      (mul_ne_zero (mul_ne_zero hm1 hm2) two_ne_zero)]
    simp only [t']
    push_cast
    ring
  have hcalc :
      t / ((Real.pi : ℂ) * ((l : ℂ) ^ 2 + t ^ 2)) +
        t' / ((Real.pi : ℂ) * ((l : ℂ) ^ 2 + t' ^ 2)) =
      (1 / (2 * (Real.pi : ℂ))) *
        ((1 / ((ε : ℂ) + ((τ - l : ℝ) : ℂ) * I) + 1 / ((ε : ℂ) - ((τ - l : ℝ) : ℂ) * I)) +
         (1 / ((ε : ℂ) + ((τ + l : ℝ) : ℂ) * I) + 1 / ((ε : ℂ) - ((τ + l : ℝ) : ℂ) * I))) := by
    rw [div_mul_eq_div_div, div_mul_eq_div_div, div_right_comm _ (Real.pi : ℂ),
      div_right_comm t' (Real.pi : ℂ), hsplit1, hsplit2]
    ring
  rw [hcalc, inv_add_mul_I_add_inv_sub_mul_I hε (τ - l),
    inv_add_mul_I_add_inv_sub_mul_I hε (τ + l)]
  have hsub : (τ - l) ^ 2 = (l - τ) ^ 2 := by ring
  have hadd : (τ + l) ^ 2 = (l + τ) ^ 2 := by ring
  rw [hsub, hadd]
  push_cast
  field_simp [hπ]

/-- Conjugate vertical pair of exponentials: `e^{-2π l (ε + iτ)} + e^{-2π l (ε - iτ)}`. -/
theorem exp_conj_pair (l ε τ : ℝ) :
    cexp (-(2 * Real.pi * (l : ℂ) * ((ε : ℂ) + (τ : ℂ) * I))) +
      cexp (-(2 * Real.pi * (l : ℂ) * ((ε : ℂ) - (τ : ℂ) * I))) =
      ((2 * Real.exp (-(2 * Real.pi * l * ε)) * Real.cos (2 * Real.pi * l * τ) : ℝ) : ℂ) := by
  have he1 : -(2 * (Real.pi : ℂ) * (l : ℂ) * ((ε : ℂ) + (τ : ℂ) * I)) =
      ((-(2 * Real.pi * l * ε) : ℝ) : ℂ) + (((-(2 * Real.pi * l * τ)) : ℝ) : ℂ) * I := by
    push_cast; ring
  have he2 : -(2 * (Real.pi : ℂ) * (l : ℂ) * ((ε : ℂ) - (τ : ℂ) * I)) =
      ((-(2 * Real.pi * l * ε) : ℝ) : ℂ) + (((2 * Real.pi * l * τ) : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [he1, he2, Complex.exp_add, Complex.exp_add, ← mul_add,
    Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

/-- The 1D Fejér-tent partial-fraction kernel at frequency `l` and abscissa `ε`. -/
def tentSeriesKernel (l ε τ : ℝ) : ℝ :=
  (1 - τ) * (1 / Real.pi) * (ε / (ε ^ 2 + (l - τ) ^ 2) + ε / (ε ^ 2 + (l + τ) ^ 2))

/-- The 1D Fejér-tent dual cosine kernel at frequency `l` and abscissa `ε`. -/
def tentDualKernel (l ε τ : ℝ) : ℝ :=
  (1 - τ) * (2 * Real.exp (-(2 * Real.pi * l * ε)) * Real.cos (2 * Real.pi * l * τ))

/-- The 1D Fejér-tent origin-pole kernel at abscissa `ε`. -/
def tentPoleKernel (ε τ : ℝ) : ℝ :=
  (1 - τ) * (2 / Real.pi) * (ε / (ε ^ 2 + τ ^ 2))

/-- Uniform `O(1/l²)` bound on `tentSeriesKernel` for `l ≥ 1`, `0 < ε ≤ 1`, `τ ∈ [0, 1]`. -/
theorem tentSeriesKernel_nonneg_and_le {l ε τ : ℝ} (hl : 1 ≤ l) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    0 ≤ tentSeriesKernel l ε τ ∧ tentSeriesKernel l ε τ ≤ (5 / Real.pi) / l ^ 2 := by
  have h1τ : 0 ≤ 1 - τ := by linarith
  have hnn : 0 ≤ tentSeriesKernel l ε τ := by
    unfold tentSeriesKernel
    positivity
  refine ⟨hnn, ?_⟩
  have hterm2 : (1 - τ) * (ε / (ε ^ 2 + (l + τ) ^ 2)) ≤ 1 / l ^ 2 := by
    have hlpos : 0 < l ^ 2 := by positivity
    have hden : l ^ 2 ≤ ε ^ 2 + (l + τ) ^ 2 := by nlinarith [sq_nonneg ε]
    have hnum : (1 - τ) * ε ≤ 1 := by nlinarith
    calc (1 - τ) * (ε / (ε ^ 2 + (l + τ) ^ 2))
        = ((1 - τ) * ε) / (ε ^ 2 + (l + τ) ^ 2) := by ring
      _ ≤ 1 / l ^ 2 := div_le_div₀ zero_le_one hnum hlpos hden
  have hterm1 : (1 - τ) * (ε / (ε ^ 2 + (l - τ) ^ 2)) ≤ 4 / l ^ 2 := by
    rcases le_or_gt l 2 with hl2 | hl2
    · set u : ℝ := l - τ
      have hdpos : 0 < ε ^ 2 + u ^ 2 := by positivity
      have hamgm : (1 - τ) * ε ≤ (ε ^ 2 + u ^ 2) / 2 := by
        have hu : 1 - τ ≤ u := by simp [u]; linarith
        nlinarith [sq_nonneg (ε - u)]
      have hhalf : (1 - τ) * (ε / (ε ^ 2 + u ^ 2)) ≤ 1 / 2 := by
        rw [← mul_div_assoc, div_le_div_iff₀ hdpos two_pos]
        linarith
      have hhalf4 : (1 / 2 : ℝ) ≤ 4 / l ^ 2 := by
        rw [div_le_div_iff₀ two_pos (by positivity)]
        nlinarith
      exact hhalf.trans hhalf4
    · have hlτ : l / 2 ≤ l - τ := by linarith
      have hden : l ^ 2 / 4 ≤ ε ^ 2 + (l - τ) ^ 2 := by nlinarith [sq_nonneg ε]
      have hnum : (1 - τ) * ε ≤ 1 := by nlinarith
      calc (1 - τ) * (ε / (ε ^ 2 + (l - τ) ^ 2))
          = ((1 - τ) * ε) / (ε ^ 2 + (l - τ) ^ 2) := by ring
        _ ≤ 1 / (l ^ 2 / 4) := div_le_div₀ zero_le_one hnum (by positivity) hden
        _ = 4 / l ^ 2 := by ring
  unfold tentSeriesKernel
  calc (1 - τ) * (1 / Real.pi) * (ε / (ε ^ 2 + (l - τ) ^ 2) + ε / (ε ^ 2 + (l + τ) ^ 2))
      = (1 / Real.pi) * ((1 - τ) * (ε / (ε ^ 2 + (l - τ) ^ 2)) +
          (1 - τ) * (ε / (ε ^ 2 + (l + τ) ^ 2))) := by ring
    _ ≤ (1 / Real.pi) * (4 / l ^ 2 + 1 / l ^ 2) :=
        mul_le_mul_of_nonneg_left (add_le_add hterm1 hterm2) (by positivity)
    _ = (5 / Real.pi) / l ^ 2 := by ring

theorem continuous_tentSeriesKernel_tau (l : ℝ) {ε : ℝ} (hε : ε ≠ 0) :
    Continuous (tentSeriesKernel l ε) := by
  unfold tentSeriesKernel
  refine ((continuous_const.sub continuous_id).mul continuous_const).mul ?_
  refine (continuous_const.div (by fun_prop) fun τ => ?_).add
    (continuous_const.div (by fun_prop) fun τ => ?_)
  · nlinarith [sq_pos_of_ne_zero hε, sq_nonneg (l - τ)]
  · nlinarith [sq_pos_of_ne_zero hε, sq_nonneg (l + τ)]

/-- As `ε → 0⁺`, the Fejér-tent integral of `tentSeriesKernel l ε` on `[0, 1]` vanishes for every
`l ≥ 1`. -/
theorem tendsto_integral_tentSeriesKernel {l : ℝ} (hl : 1 ≤ l) :
    Tendsto (fun ε : ℝ => ∫ τ in (0 : ℝ)..1, tentSeriesKernel l ε τ) (𝓝[>] 0) (𝓝 0) := by
  simp only [intervalIntegral.integral_of_le zero_le_one]
  suffices h : Tendsto (fun ε : ℝ => ∫ τ in Ioc (0 : ℝ) 1, tentSeriesKernel l ε τ)
      (𝓝[>] 0) (𝓝 (∫ _τ in Ioc (0 : ℝ) 1, (0 : ℝ))) by
    simpa only [integral_zero] using h
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (fun _ => (5 / Real.pi) / l ^ 2) ?_ ?_ ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
    exact (continuous_tentSeriesKernel_tau l hε.1.ne').aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun τ hτ => ?_)
    have hb := tentSeriesKernel_nonneg_and_le hl hε.1 hε.2.le hτ.1.le hτ.2
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2
  · exact integrableOn_const (by simp)
  · rw [ae_restrict_iff' measurableSet_Ioc]
    have h1 : ∀ᵐ τ : ℝ, τ ≠ 1 := ae_iff.mpr (by simp)
    filter_upwards [h1] with τ hne hmem
    have hτ1 : τ < 1 := lt_of_le_of_ne hmem.2 hne
    have hpos1 : (0 : ℝ) < (0 : ℝ) ^ 2 + (l - τ) ^ 2 := by nlinarith
    have hpos2 : (0 : ℝ) < (0 : ℝ) ^ 2 + (l + τ) ^ 2 := by nlinarith [hmem.1]
    have hcont : ContinuousAt (fun ε : ℝ => tentSeriesKernel l ε τ) 0 := by
      unfold tentSeriesKernel
      refine ContinuousAt.mul continuousAt_const ?_
      exact (continuousAt_id.div (by fun_prop) hpos1.ne').add
        (continuousAt_id.div (by fun_prop) hpos2.ne')
    have hval : tentSeriesKernel l 0 τ = 0 := by simp [tentSeriesKernel]
    exact (hval ▸ hcont.tendsto).mono_left nhdsWithin_le_nhds

/-- Exact evaluation of the Fejér-tent cosine integral `∫₀¹ tentDualKernel l ε τ dτ`. -/
theorem integral_tentDualKernel {l : ℝ} (hl : 1 ≤ l) (ε : ℝ) :
    (∫ τ in (0 : ℝ)..1, tentDualKernel l ε τ) =
      Real.exp (-(2 * Real.pi * l * ε)) * (Real.sin (Real.pi * l) / (Real.pi * l)) ^ 2 := by
  set ω : ℝ := 2 * Real.pi * l
  have hω : 0 < ω := by
    have : 0 < l := lt_of_lt_of_le one_pos hl
    positivity
  set P : ℝ → ℝ := fun τ => (1 - τ) * Real.sin (ω * τ) / ω - Real.cos (ω * τ) / ω ^ 2
  have hderiv : ∀ τ : ℝ, HasDerivAt P ((1 - τ) * Real.cos (ω * τ)) τ := by
    intro τ
    have hd1 : HasDerivAt (fun x : ℝ => 1 - x) (0 - 1) τ :=
      (hasDerivAt_const τ (1 : ℝ)).sub (hasDerivAt_id τ)
    have hd2 : HasDerivAt (fun x : ℝ => Real.sin (ω * x)) (Real.cos (ω * τ) * (ω * 1)) τ :=
      (Real.hasDerivAt_sin (ω * τ)).comp τ ((hasDerivAt_id τ).const_mul ω)
    have hd3 : HasDerivAt (fun x : ℝ => Real.cos (ω * x)) (-Real.sin (ω * τ) * (ω * 1)) τ :=
      (Real.hasDerivAt_cos (ω * τ)).comp τ ((hasDerivAt_id τ).const_mul ω)
    refine (((hd1.mul hd2).div_const ω).sub (hd3.div_const (ω ^ 2))).congr_deriv ?_
    field_simp [hω.ne']
    ring
  have hint : IntervalIntegrable (fun τ : ℝ => (1 - τ) * Real.cos (ω * τ)) volume 0 1 :=
    Continuous.intervalIntegrable (by fun_prop) 0 1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hderiv τ) hint
  have hrew : (fun τ : ℝ => tentDualKernel l ε τ) =
      fun τ : ℝ => (2 * Real.exp (-(2 * Real.pi * l * ε))) * ((1 - τ) * Real.cos (ω * τ)) := by
    funext τ
    simp only [tentDualKernel, ω]
    ring
  rw [hrew, intervalIntegral.integral_const_mul, hftc]
  have hP : P 1 - P 0 = (1 - Real.cos ω) / ω ^ 2 := by
    simp only [P, sub_self, zero_mul, zero_div, zero_sub, sub_zero, mul_zero, Real.sin_zero,
      Real.cos_zero, mul_one]
    ring
  rw [hP]
  have hθ : Real.pi * l ≠ 0 := by
    have : 0 < l := lt_of_lt_of_le one_pos hl
    exact (mul_pos Real.pi_pos this).ne'
  have hsin2 : 1 - Real.cos ω = 2 * Real.sin (Real.pi * l) ^ 2 := by
    have hω2 : ω = 2 * (Real.pi * l) := by simp [ω]; ring
    rw [hω2]
    linarith [Real.cos_two_mul (Real.pi * l), Real.sin_sq_add_cos_sq (Real.pi * l)]
  have htrig : 2 * ((1 - Real.cos ω) / ω ^ 2) =
      (Real.sin (Real.pi * l) / (Real.pi * l)) ^ 2 := by
    rw [hsin2]
    simp only [ω]
    field_simp [hθ]
  calc 2 * Real.exp (-(2 * Real.pi * l * ε)) * ((1 - Real.cos ω) / ω ^ 2)
      = Real.exp (-(2 * Real.pi * l * ε)) * (2 * ((1 - Real.cos ω) / ω ^ 2)) := by ring
    _ = Real.exp (-(2 * Real.pi * l * ε)) * (Real.sin (Real.pi * l) / (Real.pi * l)) ^ 2 := by
          rw [htrig]

theorem abs_integral_tentDualKernel_le {l ε : ℝ} (hl : 1 ≤ l) (hε : 0 < ε) :
    |∫ τ in (0 : ℝ)..1, tentDualKernel l ε τ| ≤ 1 / (Real.pi ^ 2 * l ^ 2) := by
  rw [integral_tentDualKernel hl ε, abs_of_nonneg (by positivity)]
  have hexp : Real.exp (-(2 * Real.pi * l * ε)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hl0 : 0 < l := lt_of_lt_of_le one_pos hl
    have hp : 0 < 2 * Real.pi * l * ε := by positivity
    linarith
  have hsin : Real.sin (Real.pi * l) ^ 2 ≤ 1 := by
    have hb := abs_le.mp (Real.abs_sin_le_one (Real.pi * l))
    nlinarith
  calc Real.exp (-(2 * Real.pi * l * ε)) * (Real.sin (Real.pi * l) / (Real.pi * l)) ^ 2
      ≤ 1 * (Real.sin (Real.pi * l) / (Real.pi * l)) ^ 2 :=
        mul_le_mul_of_nonneg_right hexp (sq_nonneg _)
    _ = Real.sin (Real.pi * l) ^ 2 / (Real.pi ^ 2 * l ^ 2) := by ring
    _ ≤ 1 / (Real.pi ^ 2 * l ^ 2) := by gcongr

theorem tendsto_integral_tentDualKernel {l : ℝ} (hl : 1 ≤ l) :
    Tendsto (fun ε : ℝ => ∫ τ in (0 : ℝ)..1, tentDualKernel l ε τ) (𝓝[>] 0)
      (𝓝 ((Real.sin (Real.pi * l) / (Real.pi * l)) ^ 2)) := by
  simp_rw [integral_tentDualKernel hl]
  have hcont : ContinuousAt
      (fun ε : ℝ => Real.exp (-(2 * Real.pi * l * ε)) *
        (Real.sin (Real.pi * l) / (Real.pi * l)) ^ 2) 0 := by fun_prop
  have h0 : Real.exp (-(2 * Real.pi * l * (0 : ℝ))) *
      (Real.sin (Real.pi * l) / (Real.pi * l)) ^ 2 =
      (Real.sin (Real.pi * l) / (Real.pi * l)) ^ 2 := by simp
  exact (h0 ▸ hcont.tendsto).mono_left nhdsWithin_le_nhds

/-- As `ε → 0⁺`, the Fejér-tent origin-pole kernel `tentPoleKernel ε` integrates to `1` on `[0, 1]`. -/
theorem tendsto_integral_tentPoleKernel :
    Tendsto (fun ε : ℝ => ∫ τ in (0 : ℝ)..1, tentPoleKernel ε τ) (𝓝[>] 0) (𝓝 1) := by
  have h1 : Tendsto (fun ε : ℝ => (2 / Real.pi) * Real.arctan (1 / ε)) (𝓝[>] 0) (𝓝 1) := by
    have hinv : Tendsto (fun ε : ℝ => 1 / ε) (𝓝[>] 0) atTop := by
      simpa [one_div] using tendsto_inv_nhdsGT_zero
    have hatan : Tendsto (fun ε : ℝ => Real.arctan (1 / ε)) (𝓝[>] 0) (𝓝 (Real.pi / 2)) :=
      (Real.tendsto_arctan_atTop.mono_right inf_le_left).comp hinv
    have hmul := hatan.const_mul (2 / Real.pi)
    have hval : (2 / Real.pi) * (Real.pi / 2) = 1 := by
      field_simp [Real.pi_ne_zero]
    rwa [hval] at hmul
  have h2 : Tendsto (fun ε : ℝ => ∫ τ in (0 : ℝ)..1, τ * ε / (ε ^ 2 + τ ^ 2)) (𝓝[>] 0) (𝓝 0) := by
    simp only [intervalIntegral.integral_of_le zero_le_one]
    suffices h : Tendsto (fun ε : ℝ => ∫ τ in Ioc (0 : ℝ) 1, τ * ε / (ε ^ 2 + τ ^ 2))
        (𝓝[>] 0) (𝓝 (∫ _τ in Ioc (0 : ℝ) 1, (0 : ℝ))) by
      simpa only [integral_zero] using h
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun _ => (1 / 2 : ℝ)) ?_ ?_ ?_ ?_
    · filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
      refine Continuous.aestronglyMeasurable ?_
      exact (continuous_id.mul continuous_const).div (by fun_prop) fun τ => by
        nlinarith [sq_pos_of_ne_zero hε.1.ne', sq_nonneg τ]
    · filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
      refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun τ hτ => ?_)
      have hnn : 0 ≤ τ * ε / (ε ^ 2 + τ ^ 2) := by
        have := hτ.1; have := hε.1; positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnn, div_le_div_iff₀ (by positivity) two_pos]
      nlinarith [sq_nonneg (ε - τ)]
    · exact integrableOn_const (by simp)
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun τ hτ => ?_)
      have hpos : (0 : ℝ) < (0 : ℝ) ^ 2 + τ ^ 2 := by have := hτ.1; positivity
      have hcont : ContinuousAt (fun ε : ℝ => τ * ε / (ε ^ 2 + τ ^ 2)) 0 :=
        (continuousAt_const.mul continuousAt_id).div (by fun_prop) hpos.ne'
      have h0 : τ * (0 : ℝ) / ((0 : ℝ) ^ 2 + τ ^ 2) = 0 := by simp
      exact (h0 ▸ hcont.tendsto).mono_left nhdsWithin_le_nhds
  have hcomb : Tendsto (fun ε : ℝ =>
      (2 / Real.pi) * Real.arctan (1 / ε) -
        (2 / Real.pi) * ∫ τ in (0 : ℝ)..1, τ * ε / (ε ^ 2 + τ ^ 2)) (𝓝[>] 0) (𝓝 1) := by
    simpa using h1.sub (h2.const_mul (2 / Real.pi))
  refine hcomb.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
  have hε0 : 0 < ε := hε.1
  have hderiv : ∀ τ : ℝ, HasDerivAt (fun x : ℝ => Real.arctan (x / ε)) (ε / (ε ^ 2 + τ ^ 2)) τ := by
    intro τ
    refine ((Real.hasDerivAt_arctan (τ / ε)).comp τ ((hasDerivAt_id τ).div_const ε)).congr_deriv ?_
    have hd1 : 1 + (τ / ε) ^ 2 ≠ 0 := by positivity
    have hd2 : ε ^ 2 + τ ^ 2 ≠ 0 := by positivity
    field_simp [hε0.ne', hd1, hd2]
  have hint1 : IntervalIntegrable (fun τ : ℝ => ε / (ε ^ 2 + τ ^ 2)) volume 0 1 :=
    Continuous.intervalIntegrable
      (continuous_const.div (by fun_prop) fun τ => by nlinarith [sq_nonneg τ]) 0 1
  have hint2 : IntervalIntegrable (fun τ : ℝ => τ * ε / (ε ^ 2 + τ ^ 2)) volume 0 1 :=
    Continuous.intervalIntegrable
      ((continuous_id.mul continuous_const).div (by fun_prop) fun τ => by nlinarith [sq_nonneg τ])
      0 1
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hderiv τ) hint1
  rw [zero_div, Real.arctan_zero, sub_zero] at hftc
  have hsplit : (fun τ : ℝ => tentPoleKernel ε τ) =
      fun τ : ℝ => (2 / Real.pi) * (ε / (ε ^ 2 + τ ^ 2)) -
        (2 / Real.pi) * (τ * ε / (ε ^ 2 + τ ^ 2)) := by
    funext τ
    unfold tentPoleKernel
    ring
  rw [hsplit, intervalIntegral.integral_sub (hint1.const_mul _) (hint2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hftc]

/-- Lower bound on `‖l² + (ε + iσ)²‖` for `l ≥ 1`, `0 < ε ≤ 1`, `|σ| ≤ 1`. -/
theorem norm_sq_add_vertical_sq_ge {l ε σ : ℝ} (hl : 1 ≤ l) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hσ : |σ| ≤ 1) :
    min (1 / 2) (ε ^ 2 / 4) * l ^ 2 ≤ ‖(l : ℂ) ^ 2 + ((ε : ℂ) + (σ : ℂ) * I) ^ 2‖ := by
  rcases le_or_gt l 2 with hl2 | hl2
  · have hfac : (l : ℂ) ^ 2 + ((ε : ℂ) + (σ : ℂ) * I) ^ 2 =
        ((ε : ℂ) + ((σ - l : ℝ) : ℂ) * I) * ((ε : ℂ) + ((σ + l : ℝ) : ℂ) * I) := by
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    have hre1 : ε ≤ ‖(ε : ℂ) + ((σ - l : ℝ) : ℂ) * I‖ := by
      have := Complex.abs_re_le_norm ((ε : ℂ) + ((σ - l : ℝ) : ℂ) * I)
      simpa [abs_of_pos hε0] using this
    have hre2 : ε ≤ ‖(ε : ℂ) + ((σ + l : ℝ) : ℂ) * I‖ := by
      have := Complex.abs_re_le_norm ((ε : ℂ) + ((σ + l : ℝ) : ℂ) * I)
      simpa [abs_of_pos hε0] using this
    have hl4 : l ^ 2 ≤ 4 := by nlinarith
    rw [hfac, norm_mul]
    calc min (1 / 2) (ε ^ 2 / 4) * l ^ 2 ≤ (ε ^ 2 / 4) * l ^ 2 :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg l)
      _ ≤ (ε ^ 2 / 4) * 4 := mul_le_mul_of_nonneg_left hl4 (by positivity)
      _ = ε * ε := by ring
      _ ≤ ‖(ε : ℂ) + ((σ - l : ℝ) : ℂ) * I‖ * ‖(ε : ℂ) + ((σ + l : ℝ) : ℂ) * I‖ :=
          mul_le_mul hre1 hre2 hε0.le (norm_nonneg _)
  · have h1 : ‖(l : ℂ) ^ 2‖ = l ^ 2 := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have h2 : ‖((ε : ℂ) + (σ : ℂ) * I) ^ 2‖ ≤ 2 := by
      rw [norm_pow]
      have hreim : ‖(ε : ℂ) + (σ : ℂ) * I‖ ^ 2 = ε ^ 2 + σ ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]
        simp
        ring
      rw [hreim]
      have hσb := abs_le.mp hσ
      have hσ2 : σ ^ 2 ≤ 1 := by nlinarith
      nlinarith
    have htri := norm_sub_le ((l : ℂ) ^ 2 + ((ε : ℂ) + (σ : ℂ) * I) ^ 2)
      (((ε : ℂ) + (σ : ℂ) * I) ^ 2)
    rw [add_sub_cancel_right, h1] at htri
    calc min (1 / 2) (ε ^ 2 / 4) * l ^ 2 ≤ (1 / 2) * l ^ 2 :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg l)
      _ ≤ l ^ 2 - 2 := by nlinarith
      _ ≤ ‖(l : ℂ) ^ 2 + ((ε : ℂ) + (σ : ℂ) * I) ^ 2‖ := by linarith

/-- **The Fejér–tent spectral gap identity (Laplace form).**
If `freqSeries a lam t = η * freqDual b mu t + α / (π t) + β` on `Re t > 0` for arbitrary complex
weights `a, b` and frequencies `lam n ≥ 1`, `mu n ≥ 1`, then
`η * Σ b_n (sin(π μ_n) / (π μ_n))² + α + β = 0`. -/
theorem tsum_sin_sq_div_sq_eq_neg_add_of_freqSeries_eq
    {a b : ℕ → ℂ} {lam mu : ℕ → ℝ} {η α β : ℂ}
    (hlam : ∀ n, 1 ≤ lam n) (hmu : ∀ n, 1 ≤ mu n)
    (ha : Summable fun n => ‖a n‖ / lam n ^ 2)
    (hb : Summable fun n => ‖b n‖ / mu n ^ 2)
    (heq : ∀ {t : ℂ}, 0 < t.re →
      FreqHamburger.freqSeries a lam t = η * FreqHamburger.freqDual b mu t + α / (Real.pi * t) + β) :
    η * (∑' n : ℕ, b n * (((Real.sin (Real.pi * mu n) / (Real.pi * mu n)) ^ 2 : ℝ) : ℂ)) +
      α + β = 0 := by
  set IL : ℝ → ℂ := fun ε =>
    ∑' n : ℕ, a n * ((∫ τ in (0 : ℝ)..1, tentSeriesKernel (lam n) ε τ : ℝ) : ℂ)
  set IR : ℝ → ℂ := fun ε =>
    η * (∑' n : ℕ, b n * ((∫ τ in (0 : ℝ)..1, tentDualKernel (mu n) ε τ : ℝ) : ℂ)) +
      α * ((∫ τ in (0 : ℝ)..1, tentPoleKernel ε τ : ℝ) : ℂ) + β
  have hIL_lim : Tendsto IL (𝓝[>] 0) (𝓝 0) := by
    have hz : (∑' _n : ℕ, (0 : ℂ)) = 0 := tsum_zero
    rw [← hz]
    refine tendsto_tsum_of_dominated_convergence
      (ha.mul_left (5 / Real.pi)) (fun n => ?_) ?_
    · have h := (Complex.continuous_ofReal.tendsto 0).comp
        (tendsto_integral_tentSeriesKernel (hlam n))
      simpa using h.const_mul (a n)
    · filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε n
      have hbd : ∀ τ ∈ Ι (0 : ℝ) 1, ‖tentSeriesKernel (lam n) ε τ‖ ≤ (5 / Real.pi) / lam n ^ 2 := by
        intro τ hτ
        rw [uIoc_of_le zero_le_one] at hτ
        have hb0 := tentSeriesKernel_nonneg_and_le (hlam n) hε.1 hε.2.le hτ.1.le hτ.2
        rw [Real.norm_eq_abs, abs_of_nonneg hb0.1]
        exact hb0.2
      have hint := intervalIntegral.norm_integral_le_of_norm_le_const hbd
      rw [sub_zero, abs_one, mul_one] at hint
      rw [norm_mul, Complex.norm_real]
      calc ‖a n‖ * ‖∫ τ in (0 : ℝ)..1, tentSeriesKernel (lam n) ε τ‖
          ≤ ‖a n‖ * ((5 / Real.pi) / lam n ^ 2) :=
            mul_le_mul_of_nonneg_left hint (norm_nonneg _)
        _ = (5 / Real.pi) * (‖a n‖ / lam n ^ 2) := by ring
  have hIR_lim : Tendsto IR (𝓝[>] 0)
      (𝓝 (η * (∑' n : ℕ, b n * (((Real.sin (Real.pi * mu n) / (Real.pi * mu n)) ^ 2 : ℝ) : ℂ)) +
        α + β)) := by
    have hdual : Tendsto
        (fun ε : ℝ => ∑' n : ℕ, b n * ((∫ τ in (0 : ℝ)..1, tentDualKernel (mu n) ε τ : ℝ) : ℂ))
        (𝓝[>] 0)
        (𝓝 (∑' n : ℕ, b n * (((Real.sin (Real.pi * mu n) / (Real.pi * mu n)) ^ 2 : ℝ) : ℂ))) := by
      refine tendsto_tsum_of_dominated_convergence
        (hb.mul_left (1 / Real.pi ^ 2)) (fun n => ?_) ?_
      · have h := (Complex.continuous_ofReal.tendsto _).comp
          (tendsto_integral_tentDualKernel (hmu n))
        exact h.const_mul (b n)
      · filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε n
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc ‖b n‖ * |∫ τ in (0 : ℝ)..1, tentDualKernel (mu n) ε τ|
            ≤ ‖b n‖ * (1 / (Real.pi ^ 2 * mu n ^ 2)) :=
              mul_le_mul_of_nonneg_left (abs_integral_tentDualKernel_le (hmu n) hε.1) (norm_nonneg _)
          _ = (1 / Real.pi ^ 2) * (‖b n‖ / mu n ^ 2) := by ring
    have hpole : Tendsto (fun ε : ℝ => α * ((∫ τ in (0 : ℝ)..1, tentPoleKernel ε τ : ℝ) : ℂ))
        (𝓝[>] 0) (𝓝 α) := by
      have h := ((Complex.continuous_ofReal.tendsto 1).comp tendsto_integral_tentPoleKernel).const_mul α
      simpa using h
    exact ((hdual.const_mul η).add hpole).add tendsto_const_nhds
  have hILIReq : IL =ᶠ[𝓝[>] 0] IR := by
    filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
    have hε0 : 0 < ε := hε.1
    have hε1 : ε ≤ 1 := hε.2.le
    have hpt : ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 →
        ((1 - τ : ℝ) : ℂ) *
          (FreqHamburger.freqSeries a lam ((ε : ℂ) + (τ : ℂ) * I) +
           FreqHamburger.freqSeries a lam ((ε : ℂ) - (τ : ℂ) * I)) =
        η * (((1 - τ : ℝ) : ℂ) *
          (FreqHamburger.freqDual b mu ((ε : ℂ) + (τ : ℂ) * I) +
           FreqHamburger.freqDual b mu ((ε : ℂ) - (τ : ℂ) * I))) +
        α * ((tentPoleKernel ε τ : ℝ) : ℂ) +
        ((2 * (1 - τ) : ℝ) : ℂ) * β := by
      intro τ hτ0 hτ1
      have hre1 : 0 < ((ε : ℂ) + (τ : ℂ) * I).re := by simp [hε0]
      have hre2 : 0 < ((ε : ℂ) - (τ : ℂ) * I).re := by simp [hε0]
      rw [heq hre1, heq hre2]
      have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have hcauchy : α / ((Real.pi : ℂ) * ((ε : ℂ) + (τ : ℂ) * I)) +
          α / ((Real.pi : ℂ) * ((ε : ℂ) - (τ : ℂ) * I)) =
          (α / (Real.pi : ℂ)) *
            (1 / ((ε : ℂ) + (τ : ℂ) * I) + 1 / ((ε : ℂ) - (τ : ℂ) * I)) := by
        simp only [div_mul_eq_div_div]
        ring
      have hgrp : ((1 - τ : ℝ) : ℂ) *
            (η * FreqHamburger.freqDual b mu ((ε : ℂ) + (τ : ℂ) * I) +
              α / ((Real.pi : ℂ) * ((ε : ℂ) + (τ : ℂ) * I)) + β +
            (η * FreqHamburger.freqDual b mu ((ε : ℂ) - (τ : ℂ) * I) +
              α / ((Real.pi : ℂ) * ((ε : ℂ) - (τ : ℂ) * I)) + β)) =
          η * (((1 - τ : ℝ) : ℂ) *
            (FreqHamburger.freqDual b mu ((ε : ℂ) + (τ : ℂ) * I) +
              FreqHamburger.freqDual b mu ((ε : ℂ) - (τ : ℂ) * I))) +
          ((1 - τ : ℝ) : ℂ) *
            (α / ((Real.pi : ℂ) * ((ε : ℂ) + (τ : ℂ) * I)) +
              α / ((Real.pi : ℂ) * ((ε : ℂ) - (τ : ℂ) * I))) +
          2 * ((1 - τ : ℝ) : ℂ) * β := by ring
      rw [hgrp, hcauchy, inv_add_mul_I_add_inv_sub_mul_I hε0 τ]
      unfold tentPoleKernel
      push_cast
      field_simp [hπ]
    have hL_sum : ∀ τ : ℝ, 0 ≤ τ → τ ≤ 1 →
        ((1 - τ : ℝ) : ℂ) *
          (FreqHamburger.freqSeries a lam ((ε : ℂ) + (τ : ℂ) * I) +
           FreqHamburger.freqSeries a lam ((ε : ℂ) - (τ : ℂ) * I)) =
        ∑' n : ℕ, a n * ((tentSeriesKernel (lam n) ε τ : ℝ) : ℂ) := by
      intro τ hτ0 hτ1
      set c₀ : ℝ := min (1 / 2) (ε ^ 2 / 4)
      have hc₀ : 0 < c₀ := lt_min (by norm_num) (by positivity)
      have hsum_sign : ∀ σ : ℝ, |σ| ≤ 1 → Summable fun n : ℕ =>
          a n * ((ε : ℂ) + (σ : ℂ) * I) /
            ((Real.pi : ℂ) * ((lam n : ℂ) ^ 2 + ((ε : ℂ) + (σ : ℂ) * I) ^ 2)) := by
        intro σ hσ
        refine Summable.of_norm ((ha.mul_left (2 / (Real.pi * c₀))).of_nonneg_of_le
          (fun _ => norm_nonneg _) fun n => ?_)
        have hden := norm_sq_add_vertical_sq_ge (hlam n) hε0 hε1 hσ
        have hlpos : 0 < lam n := lt_of_lt_of_le one_pos (hlam n)
        have htop : ‖(ε : ℂ) + (σ : ℂ) * I‖ ≤ 2 := by
          refine (norm_add_le _ _).trans ?_
          simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_I, mul_one,
            abs_of_pos hε0]
          linarith
        rw [norm_div, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos, div_le_iff₀ (mul_pos Real.pi_pos
            (lt_of_lt_of_le (by positivity : 0 < c₀ * lam n ^ 2) hden))]
        calc ‖a n‖ * ‖(ε : ℂ) + (σ : ℂ) * I‖ ≤ ‖a n‖ * 2 :=
              mul_le_mul_of_nonneg_left htop (norm_nonneg _)
          _ = (2 / (Real.pi * c₀)) * (‖a n‖ / lam n ^ 2) * (Real.pi * (c₀ * lam n ^ 2)) := by
              field_simp
          _ ≤ (2 / (Real.pi * c₀)) * (‖a n‖ / lam n ^ 2) *
                (Real.pi * ‖(lam n : ℂ) ^ 2 + ((ε : ℂ) + (σ : ℂ) * I) ^ 2‖) := by gcongr
      have hs1 := hsum_sign τ (by rw [abs_of_nonneg hτ0]; exact hτ1)
      have hs2 : Summable fun n : ℕ => a n * ((ε : ℂ) - (τ : ℂ) * I) /
          ((Real.pi : ℂ) * ((lam n : ℂ) ^ 2 + ((ε : ℂ) - (τ : ℂ) * I) ^ 2)) := by
        simpa [sub_eq_add_neg] using hsum_sign (-τ) (by rw [abs_neg, abs_of_nonneg hτ0]; exact hτ1)
      rw [FreqHamburger.freqSeries, FreqHamburger.freqSeries, ← hs1.tsum_add hs2, ← tsum_mul_left]
      refine tsum_congr fun n => ?_
      have hpair := partialFraction_conj_pair (l := lam n) (τ := τ) hε0
      have hrew : a n * ((ε : ℂ) + (τ : ℂ) * I) /
            ((Real.pi : ℂ) * ((lam n : ℂ) ^ 2 + ((ε : ℂ) + (τ : ℂ) * I) ^ 2)) +
          a n * ((ε : ℂ) - (τ : ℂ) * I) /
            ((Real.pi : ℂ) * ((lam n : ℂ) ^ 2 + ((ε : ℂ) - (τ : ℂ) * I) ^ 2)) =
          a n * (((ε : ℂ) + (τ : ℂ) * I) /
              ((Real.pi : ℂ) * ((lam n : ℂ) ^ 2 + ((ε : ℂ) + (τ : ℂ) * I) ^ 2)) +
            ((ε : ℂ) - (τ : ℂ) * I) /
              ((Real.pi : ℂ) * ((lam n : ℂ) ^ 2 + ((ε : ℂ) - (τ : ℂ) * I) ^ 2))) := by ring
      rw [hrew, hpair]
      unfold tentSeriesKernel
      push_cast
      ring
    have hD_sum : ∀ τ : ℝ,
        ((1 - τ : ℝ) : ℂ) *
          (FreqHamburger.freqDual b mu ((ε : ℂ) + (τ : ℂ) * I) +
           FreqHamburger.freqDual b mu ((ε : ℂ) - (τ : ℂ) * I)) =
        ∑' n : ℕ, b n * ((tentDualKernel (mu n) ε τ : ℝ) : ℂ) := by
      intro τ
      have hsum_exp : ∀ σ : ℝ, Summable fun n : ℕ =>
          b n * cexp (-(2 * Real.pi * (mu n : ℂ) * ((ε : ℂ) + (σ : ℂ) * I))) := by
        intro σ
        refine Summable.of_norm ((hb.mul_left (1 / (2 * Real.pi ^ 2 * ε ^ 2))).of_nonneg_of_le
          (fun _ => norm_nonneg _) fun n => ?_)
        have hmpos : 0 < mu n := lt_of_lt_of_le one_pos (hmu n)
        have hre : (-(2 * (Real.pi : ℂ) * (mu n : ℂ) * ((ε : ℂ) + (σ : ℂ) * I))).re =
            -(2 * Real.pi * mu n * ε) := by simp [mul_re]
        rw [norm_mul, Complex.norm_exp, hre]
        have hy : 0 < 2 * Real.pi * mu n * ε := by positivity
        calc ‖b n‖ * Real.exp (-(2 * Real.pi * mu n * ε))
            ≤ ‖b n‖ * (2 / (2 * Real.pi * mu n * ε) ^ 2) :=
              mul_le_mul_of_nonneg_left (exp_neg_le_two_div_sq hy) (norm_nonneg _)
          _ = (1 / (2 * Real.pi ^ 2 * ε ^ 2)) * (‖b n‖ / mu n ^ 2) := by field_simp
      have hd1 := hsum_exp τ
      have hd2 : Summable fun n : ℕ =>
          b n * cexp (-(2 * Real.pi * (mu n : ℂ) * ((ε : ℂ) - (τ : ℂ) * I))) := by
        simpa [sub_eq_add_neg] using hsum_exp (-τ)
      rw [FreqHamburger.freqDual, FreqHamburger.freqDual, ← hd1.tsum_add hd2, ← tsum_mul_left]
      refine tsum_congr fun n => ?_
      have hexp := exp_conj_pair (mu n) ε τ
      have hrew : b n * cexp (-(2 * Real.pi * (mu n : ℂ) * ((ε : ℂ) + (τ : ℂ) * I))) +
          b n * cexp (-(2 * Real.pi * (mu n : ℂ) * ((ε : ℂ) - (τ : ℂ) * I))) =
          b n * (cexp (-(2 * Real.pi * (mu n : ℂ) * ((ε : ℂ) + (τ : ℂ) * I))) +
            cexp (-(2 * Real.pi * (mu n : ℂ) * ((ε : ℂ) - (τ : ℂ) * I)))) := by ring
      rw [hrew, hexp]
      unfold tentDualKernel
      push_cast
      ring
    have hIL_int : IL ε = ∫ τ in (0 : ℝ)..1,
        ∑' n : ℕ, a n * ((tentSeriesKernel (lam n) ε τ : ℝ) : ℂ) := by
      simp only [IL]
      have hex := tsum_intervalIntegral_of_bound (a := 0) (b := 1)
        (f := fun n τ => a n * ((tentSeriesKernel (lam n) ε τ : ℝ) : ℂ))
        (M := fun n => (5 / Real.pi) * (‖a n‖ / lam n ^ 2))
        (fun n => continuous_const.mul
          (Complex.continuous_ofReal.comp (continuous_tentSeriesKernel_tau (lam n) hε0.ne')))
        (fun n τ hτ => by
          rw [uIoc_of_le zero_le_one] at hτ
          have hb0 := tentSeriesKernel_nonneg_and_le (hlam n) hε0 hε1 hτ.1.le hτ.2
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb0.1]
          calc ‖a n‖ * tentSeriesKernel (lam n) ε τ ≤ ‖a n‖ * ((5 / Real.pi) / lam n ^ 2) :=
                mul_le_mul_of_nonneg_left hb0.2 (norm_nonneg _)
            _ = (5 / Real.pi) * (‖a n‖ / lam n ^ 2) := by ring)
        (ha.mul_left _)
      rw [← hex]
      refine tsum_congr fun n => ?_
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
    have hID_int : (∑' n : ℕ, b n * ((∫ τ in (0 : ℝ)..1, tentDualKernel (mu n) ε τ : ℝ) : ℂ)) =
        ∫ τ in (0 : ℝ)..1, ∑' n : ℕ, b n * ((tentDualKernel (mu n) ε τ : ℝ) : ℂ) := by
      have hex := tsum_intervalIntegral_of_bound (a := 0) (b := 1)
        (f := fun n τ => b n * ((tentDualKernel (mu n) ε τ : ℝ) : ℂ))
        (M := fun n => (1 / (Real.pi ^ 2 * ε ^ 2)) * (‖b n‖ / mu n ^ 2))
        (fun n => by unfold tentDualKernel; fun_prop)
        (fun n τ hτ => by
          rw [uIoc_of_le zero_le_one] at hτ
          have hmpos : 0 < mu n := lt_of_lt_of_le one_pos (hmu n)
          have hy : 0 < 2 * Real.pi * mu n * ε := by positivity
          have h1τ : |1 - τ| ≤ 1 := by rw [abs_of_nonneg (by linarith [hτ.2])]; linarith [hτ.1]
          have hcos : |Real.cos (2 * Real.pi * mu n * τ)| ≤ 1 := Real.abs_cos_le_one _
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          have hker : |tentDualKernel (mu n) ε τ| ≤
              2 * Real.exp (-(2 * Real.pi * mu n * ε)) := by
            unfold tentDualKernel
            rw [abs_mul, abs_mul,
              abs_of_pos (by positivity : 0 < 2 * Real.exp (-(2 * Real.pi * mu n * ε)))]
            calc |1 - τ| * (2 * Real.exp (-(2 * Real.pi * mu n * ε)) *
                  |Real.cos (2 * Real.pi * mu n * τ)|)
                ≤ 1 * (2 * Real.exp (-(2 * Real.pi * mu n * ε)) * 1) := by gcongr
              _ = 2 * Real.exp (-(2 * Real.pi * mu n * ε)) := by ring
          calc ‖b n‖ * |tentDualKernel (mu n) ε τ|
              ≤ ‖b n‖ * (2 * Real.exp (-(2 * Real.pi * mu n * ε))) :=
                mul_le_mul_of_nonneg_left hker (norm_nonneg _)
            _ ≤ ‖b n‖ * (2 * (2 / (2 * Real.pi * mu n * ε) ^ 2)) :=
                mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left (exp_neg_le_two_div_sq hy) zero_le_two) (norm_nonneg _)
            _ = (1 / (Real.pi ^ 2 * ε ^ 2)) * (‖b n‖ / mu n ^ 2) := by field_simp)
        (hb.mul_left _)
      rw [← hex]
      refine tsum_congr fun n => ?_
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal]
    have hβ_int : (∫ τ in (0 : ℝ)..1, ((2 * (1 - τ) : ℝ) : ℂ) * β) = β := by
      have hd : ∀ τ : ℝ, HasDerivAt (fun x : ℝ => 2 * x - x ^ 2) (2 * (1 - τ)) τ := by
        intro τ
        have h1 : HasDerivAt (fun x : ℝ => 2 * x) (2 * 1) τ := (hasDerivAt_id τ).const_mul 2
        have h2 : HasDerivAt (fun x : ℝ => x ^ 2) ((2 : ℕ) * τ ^ (2 - 1)) τ := hasDerivAt_pow 2 τ
        exact (h1.sub h2).congr_deriv (by norm_num; ring)
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hd τ)
        (Continuous.intervalIntegrable (by fun_prop) 0 1)
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal, hftc]
      norm_num
    have hcontD : Continuous fun τ : ℝ =>
        ∑' n : ℕ, b n * ((tentDualKernel (mu n) ε τ : ℝ) : ℂ) := by
      simp_rw [← hD_sum]
      have hcD := (FreqHamburger.differentiableOn_freqDual hmu hb).continuousOn
      have hc1 : Continuous fun τ : ℝ => FreqHamburger.freqDual b mu ((ε : ℂ) + (τ : ℂ) * I) :=
        hcD.comp_continuous (by fun_prop) fun τ => by simp [hε0]
      have hc2 : Continuous fun τ : ℝ => FreqHamburger.freqDual b mu ((ε : ℂ) - (τ : ℂ) * I) :=
        hcD.comp_continuous (by fun_prop) fun τ => by simp [hε0]
      exact (by fun_prop : Continuous fun τ : ℝ => ((1 - τ : ℝ) : ℂ)).mul (hc1.add hc2)
    have hintD : IntervalIntegrable
        (fun τ : ℝ => η * ∑' n : ℕ, b n * ((tentDualKernel (mu n) ε τ : ℝ) : ℂ)) volume 0 1 :=
      (hcontD.intervalIntegrable 0 1).const_mul η
    have hintP : IntervalIntegrable
        (fun τ : ℝ => α * ((tentPoleKernel ε τ : ℝ) : ℂ)) volume 0 1 := by
      refine Continuous.intervalIntegrable ?_ 0 1
      unfold tentPoleKernel
      refine continuous_const.mul (Complex.continuous_ofReal.comp ?_)
      exact ((continuous_const.sub continuous_id).mul continuous_const).mul
        (continuous_const.div (by fun_prop) fun τ => by nlinarith [sq_nonneg τ])
    have hintB : IntervalIntegrable
        (fun τ : ℝ => ((2 * (1 - τ) : ℝ) : ℂ) * β) volume 0 1 :=
      Continuous.intervalIntegrable (by fun_prop) 0 1
    have hcongr : (∫ τ in (0 : ℝ)..1,
          ∑' n : ℕ, a n * ((tentSeriesKernel (lam n) ε τ : ℝ) : ℂ)) =
        ∫ τ in (0 : ℝ)..1,
          ((η * ∑' n : ℕ, b n * ((tentDualKernel (mu n) ε τ : ℝ) : ℂ)) +
            α * ((tentPoleKernel ε τ : ℝ) : ℂ) +
            ((2 * (1 - τ) : ℝ) : ℂ) * β) := by
      refine intervalIntegral.integral_congr fun τ hτ => ?_
      rw [uIcc_of_le zero_le_one] at hτ
      rw [← hL_sum τ hτ.1 hτ.2, ← hD_sum τ]
      exact hpt τ hτ.1 hτ.2
    rw [hIL_int, hcongr, intervalIntegral.integral_add (hintD.add hintP) hintB,
      intervalIntegral.integral_add hintD hintP, intervalIntegral.integral_const_mul,
      ← hID_int, intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, hβ_int]
  exact tendsto_nhds_unique (hIL_lim.congr' hILIReq) hIR_lim |>.symm

/-- **The Fejér–tent spectral gap identity for `freqTheta`.**
For arbitrary complex coefficients `a_n` and frequencies `lam n ≥ 1` with `Σ ‖a_n‖ / λ_n² < ∞`,
Riemann's self-dual theta relation forces `α + β = 0` and
`Σ a_n (sin(π λ_n) / (π λ_n))² = 0`. -/
theorem tsum_sin_sq_div_sq_eq_zero_of_freqTheta_relation
    {a : ℕ → ℂ} {lam : ℕ → ℝ} {α β : ℂ}
    (hlam : ∀ n, 1 ≤ lam n) (ha : Summable fun n => ‖a n‖ / lam n ^ 2)
    (htheta : ∀ x : ℝ, 0 < x → FreqHamburger.freqTheta a lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * FreqHamburger.freqTheta a lam x⁻¹ + α +
        β * (x : ℂ) ^ (-(1 / 2 : ℂ))) :
    α + β = 0 ∧
      (∑' n : ℕ, a n * (((Real.sin (Real.pi * lam n) / (Real.pi * lam n)) ^ 2 : ℝ) : ℂ)) = 0 := by
  have hαβ : α + β = 0 := add_eq_zero_of_self_dual_theta htheta
  have hlap : ∀ {t : ℂ}, 0 < t.re →
      FreqHamburger.freqSeries a lam t =
        (1 : ℂ) * FreqHamburger.freqDual a lam t + α / (Real.pi * t) + β := by
    intro t ht
    rw [one_mul]
    exact FreqHamburger.freqSeries_eq_of_freqTheta_relation hlam ha htheta ht
  have hgap := tsum_sin_sq_div_sq_eq_neg_add_of_freqSeries_eq hlam hlam ha ha hlap
  rw [one_mul] at hgap
  exact ⟨hαβ, by linear_combination hgap - hαβ⟩

/-! ## Section 2: Integer-frequency quantization and uniqueness of `ζ` -/

/-- **Integer-frequency quantization.**
If `w : ℕ → ℝ` is nonnegative, `lam n ≥ 1`, `Σ w_n / λ_n² < ∞`, and `freqTheta (w ·) lam` satisfies
Riemann's self-dual theta relation, then every frequency carrying positive weight is a positive
integer. -/
theorem exists_nat_pos_eq_of_nonneg_of_freqTheta_relation
    {w : ℕ → ℝ} {lam : ℕ → ℝ} {α β : ℂ}
    (hw : ∀ n, 0 ≤ w n) (hlam : ∀ n, 1 ≤ lam n)
    (hsum : Summable fun n => w n / lam n ^ 2)
    (htheta : ∀ x : ℝ, 0 < x →
      FreqHamburger.freqTheta (fun n => (w n : ℂ)) lam x =
        (x : ℂ) ^ (-(1 / 2 : ℂ)) * FreqHamburger.freqTheta (fun n => (w n : ℂ)) lam x⁻¹ + α +
          β * (x : ℂ) ^ (-(1 / 2 : ℂ)))
    {n : ℕ} (hwn : w n ≠ 0) :
    ∃ m : ℕ, 1 ≤ m ∧ lam n = (m : ℝ) := by
  have ha : Summable fun k => ‖(w k : ℂ)‖ / lam k ^ 2 := by
    refine hsum.congr fun k => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw k)]
  have hzero := (tsum_sin_sq_div_sq_eq_zero_of_freqTheta_relation hlam ha htheta).2
  have hs_real : Summable fun k : ℕ => w k * (Real.sin (Real.pi * lam k) / (Real.pi * lam k)) ^ 2 := by
    refine (hsum.mul_left (1 / Real.pi ^ 2)).of_nonneg_of_le
      (fun k => mul_nonneg (hw k) (sq_nonneg _)) fun k => ?_
    have hsin : Real.sin (Real.pi * lam k) ^ 2 ≤ 1 := by
      have hb := abs_le.mp (Real.abs_sin_le_one (Real.pi * lam k))
      nlinarith
    calc w k * (Real.sin (Real.pi * lam k) / (Real.pi * lam k)) ^ 2
        = w k * (Real.sin (Real.pi * lam k) ^ 2 / (Real.pi ^ 2 * lam k ^ 2)) := by ring
      _ ≤ w k * (1 / (Real.pi ^ 2 * lam k ^ 2)) := by
          gcongr
          exact hw k
      _ = (1 / Real.pi ^ 2) * (w k / lam k ^ 2) := by ring
  have htsum_real : (∑' k : ℕ, w k * (Real.sin (Real.pi * lam k) / (Real.pi * lam k)) ^ 2) = 0 := by
    have hcast : (((∑' k : ℕ, w k *
        (Real.sin (Real.pi * lam k) / (Real.pi * lam k)) ^ 2 : ℝ)) : ℂ) = 0 := by
      rw [Complex.ofReal_tsum]
      simpa only [Complex.ofReal_mul] using hzero
    exact_mod_cast hcast
  have hle := hs_real.sum_le_tsum ({n} : Finset ℕ)
    (fun k _ => mul_nonneg (hw k) (sq_nonneg _))
  rw [Finset.sum_singleton, htsum_real] at hle
  have hterm0 : w n * (Real.sin (Real.pi * lam n) / (Real.pi * lam n)) ^ 2 = 0 :=
    le_antisymm hle (mul_nonneg (hw n) (sq_nonneg _))
  have hsq0 : (Real.sin (Real.pi * lam n) / (Real.pi * lam n)) ^ 2 = 0 :=
    (mul_eq_zero.mp hterm0).resolve_left hwn
  have hdiv0 : Real.sin (Real.pi * lam n) / (Real.pi * lam n) = 0 := sq_eq_zero_iff.mp hsq0
  have hlpos : 0 < lam n := lt_of_lt_of_le one_pos (hlam n)
  have hπl : Real.pi * lam n ≠ 0 := (mul_pos Real.pi_pos hlpos).ne'
  have hsin0 : Real.sin (Real.pi * lam n) = 0 := (div_eq_zero_iff.mp hdiv0).resolve_right hπl
  obtain ⟨z, hz⟩ := Real.sin_eq_zero_iff.mp hsin0
  have hlamz : lam n = (z : ℝ) := by
    apply mul_left_cancel₀ Real.pi_ne_zero
    linarith
  have hz1 : (1 : ℤ) ≤ z := by
    have : (1 : ℝ) ≤ (z : ℝ) := hlamz ▸ hlam n
    exact_mod_cast this
  refine ⟨z.toNat, by omega, ?_⟩
  have hznat : ((z.toNat : ℤ) : ℝ) = (z : ℝ) := by
    congr 1
    exact Int.toNat_of_nonneg (by omega)
  rw [hlamz, ← hznat]
  norm_cast

/-- Aggregated real weight on the integer frequency `m`. -/
def aggRealCoeff (w : ℕ → ℝ) (lam : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑' n : ℕ, if lam n = (m : ℝ) then w n else 0

/-- Aggregated complex weight on the integer frequency `m`. -/
def aggCoeff (w : ℕ → ℝ) (lam : ℕ → ℝ) (m : ℕ) : ℂ :=
  ((aggRealCoeff w lam m : ℝ) : ℂ)

/-- Fiberwise regrouping of any summable series supported on positive-integer frequencies `lam n`. -/
theorem tsum_mul_eq_tsum_aggCoeff_mul {w : ℕ → ℝ} {lam : ℕ → ℝ} {φ : ℝ → ℂ}
    (_hw : ∀ n, 0 ≤ w n)
    (hint : ∀ n, w n ≠ 0 → ∃ m : ℕ, 1 ≤ m ∧ lam n = (m : ℝ))
    (_hwsum : ∀ m : ℕ, Summable fun n : ℕ => if lam n = ((m + 1 : ℕ) : ℝ) then w n else 0)
    (hφ : Summable fun n : ℕ => ‖(w n : ℂ) * φ (lam n)‖) :
    (∑' n : ℕ, (w n : ℂ) * φ (lam n)) =
      ∑' m : ℕ, aggCoeff w lam (m + 1) * φ ((m : ℝ) + 1) := by
  set g : ℕ → ℕ := fun n => ⌊lam n⌋₊ - 1
  have hgn : ∀ n : ℕ, w n ≠ 0 → lam n = ((g n + 1 : ℕ) : ℝ) := by
    intro n hwn
    obtain ⟨m, hm1, hm⟩ := hint n hwn
    have hfl : ⌊lam n⌋₊ = m := by rw [hm]; exact Nat.floor_natCast m
    have hgm : g n + 1 = m := by simp only [g, hfl]; omega
    rw [hm, ← hgm]
  have hite : ∀ m n : ℕ,
      (if g n = m then w n else 0) = if lam n = ((m + 1 : ℕ) : ℝ) then w n else 0 := by
    intro m n
    by_cases hwn : w n = 0
    · simp [hwn]
    · have hl := hgn n hwn
      have hiff : g n = m ↔ lam n = ((m + 1 : ℕ) : ℝ) := by
        rw [hl]
        norm_cast
        omega
      by_cases h : g n = m
      · rw [if_pos h, if_pos (hiff.mp h)]
      · rw [if_neg h, if_neg (mt hiff.mpr h)]
  have hterm : ∀ n : ℕ, (w n : ℂ) * φ (lam n) = (w n : ℂ) * φ (((g n + 1 : ℕ) : ℝ)) := by
    intro n
    by_cases hwn : w n = 0
    · simp [hwn]
    · rw [hgn n hwn]
  have hsumC : Summable fun n : ℕ => (w n : ℂ) * φ (((g n + 1 : ℕ) : ℝ)) :=
    (hφ.congr fun n => by rw [hterm n]).of_norm
  have hsig : Summable fun p : Σ m : ℕ, {n : ℕ // g n = m} =>
      (w (p.2 : ℕ) : ℂ) * φ (((g (p.2 : ℕ) + 1 : ℕ) : ℝ)) :=
    ((Equiv.sigmaFiberEquiv g).summable_iff
      (f := fun n => (w n : ℂ) * φ (((g n + 1 : ℕ) : ℝ)))).2 hsumC
  calc (∑' n : ℕ, (w n : ℂ) * φ (lam n))
      = ∑' n : ℕ, (w n : ℂ) * φ (((g n + 1 : ℕ) : ℝ)) := tsum_congr hterm
    _ = ∑' p : Σ m : ℕ, {n : ℕ // g n = m},
          (w (p.2 : ℕ) : ℂ) * φ (((g (p.2 : ℕ) + 1 : ℕ) : ℝ)) :=
        ((Equiv.sigmaFiberEquiv g).tsum_eq
          (fun n => (w n : ℂ) * φ (((g n + 1 : ℕ) : ℝ)))).symm
    _ = ∑' m : ℕ, ∑' j : {n : ℕ // g n = m},
          (w (j : ℕ) : ℂ) * φ (((g (j : ℕ) + 1 : ℕ) : ℝ)) := hsig.tsum_sigma
    _ = ∑' m : ℕ, aggCoeff w lam (m + 1) * φ ((m : ℝ) + 1) := by
        refine tsum_congr fun m => ?_
        have hj : ∀ j : {n : ℕ // g n = m},
            (w (j : ℕ) : ℂ) * φ (((g (j : ℕ) + 1 : ℕ) : ℝ)) =
              (w (j : ℕ) : ℂ) * φ ((m : ℝ) + 1) := by
          intro j
          rw [j.2]
          push_cast
          rfl
        rw [tsum_congr hj, tsum_mul_right]
        congr 1
        rw [aggCoeff, aggRealCoeff, ← Complex.ofReal_tsum]
        congr 1
        change (∑' j : ({n : ℕ | g n = m} : Set ℕ), w j) = _
        rw [tsum_subtype ({n : ℕ | g n = m}) w]
        refine tsum_congr fun n => ?_
        simp only [Set.indicator_apply, Set.mem_setOf_eq]
        exact hite m n

theorem summable_ite_of_sq {w : ℕ → ℝ} {lam : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (hsum : Summable fun n => w n / lam n ^ 2) (m : ℕ) :
    Summable fun n : ℕ => if lam n = ((m + 1 : ℕ) : ℝ) then w n else 0 := by
  refine (hsum.mul_left (((m + 1 : ℕ) : ℝ) ^ 2)).of_nonneg_of_le
    (fun n => by split_ifs <;> linarith [hw n]) fun n => ?_
  split_ifs with h
  · rw [h]
    have hm : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) ^ 2 := by positivity
    field_simp
    rfl
  · exact mul_nonneg (sq_nonneg _) (div_nonneg (hw n) (sq_nonneg _))

theorem summable_aggCoeff_sq {w : ℕ → ℝ} {lam : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n)
    (hint : ∀ n, w n ≠ 0 → ∃ m : ℕ, 1 ≤ m ∧ lam n = (m : ℝ))
    (hsum : Summable fun n => w n / lam n ^ 2) :
    Summable fun m : ℕ => ‖aggCoeff w lam (m + 1)‖ / ((m : ℝ) + 1) ^ (2 : ℝ) := by
  set g : ℕ → ℕ := fun n => ⌊lam n⌋₊ - 1
  have hgn : ∀ n : ℕ, w n ≠ 0 → lam n = ((g n + 1 : ℕ) : ℝ) := by
    intro n hwn
    obtain ⟨m, _, hm⟩ := hint n hwn
    have hfl : ⌊lam n⌋₊ = m := by rw [hm]; exact Nat.floor_natCast m
    have hgm : g n + 1 = m := by simp only [g, hfl]; omega
    rw [hm, ← hgm]
  have hite : ∀ m n : ℕ,
      (if g n = m then w n else 0) = if lam n = ((m + 1 : ℕ) : ℝ) then w n else 0 := by
    intro m n
    by_cases hwn : w n = 0
    · simp [hwn]
    · rw [hgn n hwn]
      norm_cast
      by_cases h : g n = m <;> simp [h]
  have hsum' : Summable fun n : ℕ => w n / (((g n + 1 : ℕ) : ℝ) ^ 2) := by
    refine hsum.congr fun n => ?_
    by_cases hwn : w n = 0
    · simp [hwn]
    · rw [hgn n hwn]
  have hsig : Summable fun p : Σ m : ℕ, {n : ℕ // g n = m} =>
      w (p.2 : ℕ) / (((g (p.2 : ℕ) + 1 : ℕ) : ℝ) ^ 2) :=
    ((Equiv.sigmaFiberEquiv g).summable_iff
      (f := fun n => w n / (((g n + 1 : ℕ) : ℝ) ^ 2))).2 hsum'
  refine hsig.sigma.congr fun m => ?_
  have hnn : 0 ≤ aggRealCoeff w lam (m + 1) :=
    tsum_nonneg fun n => by split_ifs <;> linarith [hw n]
  rw [aggCoeff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn,
    show ((m : ℝ) + 1) ^ (2 : ℝ) = (((m + 1 : ℕ) : ℝ) ^ 2) by push_cast; norm_cast]
  have hj : ∀ j : {n : ℕ // g n = m},
      w (j : ℕ) / (((g (j : ℕ) + 1 : ℕ) : ℝ) ^ 2) =
        w (j : ℕ) * ((((m + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
    intro j
    rw [j.2, div_eq_mul_inv]
  rw [tsum_congr hj, tsum_mul_right, ← div_eq_mul_inv]
  congr 1
  rw [aggRealCoeff]
  change (∑' j : ({n : ℕ | g n = m} : Set ℕ), w j) = _
  rw [tsum_subtype ({n : ℕ | g n = m}) w]
  exact tsum_congr fun n => by simp only [Set.indicator_apply, Set.mem_setOf_eq, hite m n]

/-- **Hamburger's theorem for nonnegative generalized-frequency theta series.**
If `w : ℕ → ℝ` is nonnegative, `lam n ≥ 1`, `Σ w_n / λ_n² < ∞`, and `freqTheta (w ·) lam` satisfies
Riemann's self-dual theta relation, then every positive integer `m + 1` carries constant total
weight `aggCoeff w lam (m + 1) = -(2 * α)`. -/
theorem aggCoeff_eq_neg_two_mul_of_nonneg_freqTheta_relation
    {w : ℕ → ℝ} {lam : ℕ → ℝ} {α β : ℂ}
    (hw : ∀ n, 0 ≤ w n) (hlam : ∀ n, 1 ≤ lam n)
    (hsum : Summable fun n => w n / lam n ^ 2)
    (htheta : ∀ x : ℝ, 0 < x →
      FreqHamburger.freqTheta (fun n => (w n : ℂ)) lam x =
        (x : ℂ) ^ (-(1 / 2 : ℂ)) * FreqHamburger.freqTheta (fun n => (w n : ℂ)) lam x⁻¹ + α +
          β * (x : ℂ) ^ (-(1 / 2 : ℂ)))
    (m : ℕ) :
    aggCoeff w lam (m + 1) = -(2 * α) := by
  have hint : ∀ n, w n ≠ 0 → ∃ k : ℕ, 1 ≤ k ∧ lam n = (k : ℝ) :=
    fun n hwn => exists_nat_pos_eq_of_nonneg_of_freqTheta_relation hw hlam hsum htheta hwn
  have ha : Summable fun n => ‖(w n : ℂ)‖ / lam n ^ 2 :=
    hsum.congr fun n => by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw n)]
  have hθeq : ∀ x : ℝ, 0 < x →
      FreqHamburger.freqTheta (fun n => (w n : ℂ)) lam x = coeffTheta (aggCoeff w lam) x := by
    intro x hx
    unfold FreqHamburger.freqTheta coeffTheta
    exact tsum_mul_eq_tsum_aggCoeff_mul
      (φ := fun u : ℝ => ((Real.exp (-Real.pi * u ^ 2 * x) : ℝ) : ℂ))
      hw hint (summable_ite_of_sq hw hsum)
      (FreqHamburger.summable_norm_thetaTerm hlam ha hx)
  have hagg_sum := summable_aggCoeff_sq hw hint hsum
  have hagg_theta : ∀ x : ℝ, 0 < x →
      coeffTheta (aggCoeff w lam) x =
        (1 : ℂ) * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta (aggCoeff w lam) x⁻¹) + α +
          β * (x : ℂ) ^ (-(1 / 2 : ℂ)) := by
    intro x hx
    rw [one_mul, ← hθeq x hx, ← hθeq x⁻¹ (inv_pos.mpr hx)]
    exact htheta x hx
  exact coeff_eq_of_coeffTheta_relation_of_sq hagg_sum hagg_sum hagg_theta m

/-- The generalized Dirichlet series `Σ a_n λ_n^{-s}`. -/
def freqDirichlet (a : ℕ → ℂ) (lam : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, a n / (lam n : ℂ) ^ s

theorem norm_freqTheta_le_rpow {a : ℕ → ℂ} {lam : ℕ → ℝ} (hlam : ∀ n, 1 ≤ lam n)
    {x b : ℝ} (hx : 0 < x) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (ha : Summable fun n : ℕ => ‖a n‖ / lam n ^ (2 * b)) :
    ‖FreqHamburger.freqTheta a lam x‖ ≤
      (Real.pi * x) ^ (-b) * ∑' n : ℕ, ‖a n‖ / lam n ^ (2 * b) := by
  have hterm : ∀ n : ℕ,
      ‖a n * ((Real.exp (-Real.pi * lam n ^ 2 * x) : ℝ) : ℂ)‖ ≤
        (Real.pi * x) ^ (-b) * (‖a n‖ / lam n ^ (2 * b)) := by
    intro n
    have hl : 0 < lam n := lt_of_lt_of_le one_pos (hlam n)
    have hy : 0 < Real.pi * lam n ^ 2 * x := by positivity
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      show -Real.pi * lam n ^ 2 * x = -(Real.pi * lam n ^ 2 * x) by ring]
    have h1 := exp_neg_le_rpow_neg_of_le_one hy hb0 hb1
    have h2 : (Real.pi * lam n ^ 2 * x) ^ (-b) =
        (Real.pi * x) ^ (-b) * (lam n ^ (2 * b))⁻¹ := by
      rw [show Real.pi * lam n ^ 2 * x = (Real.pi * x) * lam n ^ 2 by ring,
        Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
        ← Real.rpow_mul hl.le, show ((2 : ℕ) : ℝ) * -b = -(2 * b) by push_cast; ring,
        Real.rpow_neg hl.le]
    calc ‖a n‖ * Real.exp (-(Real.pi * lam n ^ 2 * x))
        ≤ ‖a n‖ * (Real.pi * lam n ^ 2 * x) ^ (-b) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = (Real.pi * x) ^ (-b) * (‖a n‖ / lam n ^ (2 * b)) := by rw [h2, div_eq_mul_inv]; ring
  have hs := (ha.mul_left ((Real.pi * x) ^ (-b))).of_nonneg_of_le (fun _ => norm_nonneg _) hterm
  unfold FreqHamburger.freqTheta
  refine (norm_tsum_le_tsum_norm hs).trans ?_
  rw [← tsum_mul_left]
  exact hs.tsum_le_tsum hterm (ha.mul_left _)

theorem mellinConvergent_freqTheta {a : ℕ → ℂ} {lam : ℕ → ℝ} (hlam : ∀ n, 1 ≤ lam n)
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a n‖ / lam n ^ σ)
    {w : ℂ} (hw1 : 1 / 2 < w.re) (hw2 : w.re < 1) :
    MellinConvergent (FreqHamburger.freqTheta a lam) w := by
  set b : ℝ := (w.re + 1 / 2) / 2 with hb
  have hb0 : 0 ≤ b := by rw [hb]; linarith
  have hb1 : b ≤ 1 := by rw [hb]; linarith
  have hsb : Summable fun n : ℕ => ‖a n‖ / lam n ^ (2 * b) := ha _ (by rw [hb]; linarith)
  have hs1 : Summable fun n : ℕ => ‖a n‖ / lam n ^ (2 * (1 : ℝ)) := ha _ (by norm_num)
  have hs2 : Summable fun n : ℕ => ‖a n‖ / lam n ^ 2 :=
    hs1.congr fun n => by rw [mul_one, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  refine mellinConvergent_of_isBigO_rpow (a := 1) (b := b)
    ((FreqHamburger.continuousOn_freqTheta hlam hs2).locallyIntegrableOn measurableSet_Ioi)
    ?_ hw2 ?_ (by rw [hb]; linarith)
  · refine Asymptotics.IsBigO.of_bound
      (Real.pi ^ (-(1 : ℝ)) * ∑' n : ℕ, ‖a n‖ / lam n ^ (2 * (1 : ℝ))) ?_
    filter_upwards [eventually_gt_atTop 0] with x hx
    have h := norm_freqTheta_le_rpow hlam hx zero_le_one le_rfl hs1
    rw [Real.mul_rpow Real.pi_pos.le hx.le] at h
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx _)]
    calc ‖FreqHamburger.freqTheta a lam x‖
        ≤ Real.pi ^ (-(1 : ℝ)) * x ^ (-(1 : ℝ)) *
            ∑' n : ℕ, ‖a n‖ / lam n ^ (2 * (1 : ℝ)) := h
      _ = _ := by ring
  · refine Asymptotics.IsBigO.of_bound
      (Real.pi ^ (-b) * ∑' n : ℕ, ‖a n‖ / lam n ^ (2 * b)) ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : (0 : ℝ) < x := hx
    have h := norm_freqTheta_le_rpow hlam hx0 hb0 hb1 hsb
    rw [Real.mul_rpow Real.pi_pos.le hx0.le] at h
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
    calc ‖FreqHamburger.freqTheta a lam x‖
        ≤ Real.pi ^ (-b) * x ^ (-b) * ∑' n : ℕ, ‖a n‖ / lam n ^ (2 * b) := h
      _ = _ := by ring

theorem mellin_freqTheta {a : ℕ → ℂ} {lam : ℕ → ℝ} (hlam : ∀ n, 1 ≤ lam n)
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a n‖ / lam n ^ σ)
    {s : ℂ} (hs : 1 < s.re) :
    mellin (FreqHamburger.freqTheta a lam) (s / 2) = Complex.Gammaℝ s * freqDirichlet a lam s := by
  have hs2 : Summable fun n : ℕ => ‖a n‖ / lam n ^ 2 :=
    (ha 2 (by norm_num)).congr fun n => by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hF : ∀ t ∈ Ioi (0 : ℝ), HasSum (fun n : ℕ => if lam n = 0 then 0 else
      a n * ((Real.exp (-Real.pi * lam n ^ 2 * t) : ℝ) : ℂ))
      (FreqHamburger.freqTheta a lam t) := by
    intro t ht
    have hne : ∀ n : ℕ, lam n ≠ 0 := fun n => (lt_of_lt_of_le one_pos (hlam n)).ne'
    simp only [hne, if_false]
    exact (FreqHamburger.summable_norm_thetaTerm hlam hs2 ht).of_norm.hasSum
  have hsum : Summable fun n : ℕ => ‖a n‖ / |lam n| ^ s.re := by
    refine (ha s.re hs).congr fun n => ?_
    rw [abs_of_pos (lt_of_lt_of_le one_pos (hlam n))]
  have h := hasSum_mellin_pi_mul_sq (a := a) (r := lam) (by linarith) hF hsum
  rw [← h.tsum_eq, freqDirichlet, ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [abs_of_pos (lt_of_lt_of_le one_pos (hlam n)), mul_div_assoc]

/-- Converse theta relation for generalized Dirichlet series on `[1, ∞)`. -/
theorem freqTheta_relation_of_completed_functional_equation
    {a : ℕ → ℂ} {lam : ℕ → ℝ} {E : ℂ → ℂ} {α β : ℂ} {C : ℝ}
    (hlam : ∀ n, 1 ≤ lam n)
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a n‖ / lam n ^ σ)
    (hE : DifferentiableOn ℂ E (verticalStrip (-1 / 2) (3 / 2)))
    (hdecay : ∀ s ∈ verticalStrip (-1 / 2) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2))
    (hR : ∀ s : ℂ, s.re = 3 / 2 → Complex.Gammaℝ s * freqDirichlet a lam s =
      E s + (α * Complex.Gammaℝ s + β * Complex.Gammaℝ (s - 1)))
    (hL : ∀ s : ℂ, s.re = -1 / 2 → Complex.Gammaℝ (1 - s) * freqDirichlet a lam (1 - s) =
      E s + (α * Complex.Gammaℝ s + β * Complex.Gammaℝ (s - 1)))
    {x : ℝ} (hx : 0 < x) :
    FreqHamburger.freqTheta a lam x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * FreqHamburger.freqTheta a lam x⁻¹ + α +
        β * (x : ℂ) ^ (-(1 / 2 : ℂ)) := by
  have hs2 : Summable fun n : ℕ => ‖a n‖ / lam n ^ 2 :=
    (ha 2 (by norm_num)).congr fun n => by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h := converse_theta_relation (ε := 1)
    (FreqHamburger.continuousOn_freqTheta hlam hs2)
    (FreqHamburger.continuousOn_freqTheta hlam hs2)
    (mellinConvergent_freqTheta hlam ha (by norm_num) (by norm_num))
    (mellinConvergent_freqTheta hlam ha (by norm_num) (by norm_num))
    hE hdecay
    (fun s hs => by rw [mellin_freqTheta hlam ha (by rw [hs]; norm_num)]; exact hR s hs)
    (fun s hs => by
      rw [one_mul, mellin_freqTheta hlam ha (s := 1 - s) (by simp [hs]; norm_num)]
      exact hL s hs)
    hx
  simpa only [one_mul] using h

theorem coeffDirichlet_const_one_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    coeffDirichlet (fun _ => 1) s = riemannZeta s := by
  have hzeta := zeta_eq_tsum_one_div_nat_cpow hs
  have hs0 : s ≠ 0 := by intro h; rw [h] at hs; norm_num at hs
  have hsummable : Summable fun n : ℕ => 1 / (n : ℂ) ^ s :=
    (Complex.summable_one_div_nat_cpow (p := s)).mpr hs
  rw [hzeta, hsummable.tsum_eq_zero_add, Nat.cast_zero, Complex.zero_cpow hs0, div_zero, zero_add,
    coeffDirichlet]
  refine tsum_congr fun n => ?_
  push_cast
  rfl

/-- **Uniqueness of `ζ` among nonnegative generalized Dirichlet series on `[1, ∞)`.**
If `w : ℕ → ℝ` is nonnegative, `lam n ≥ 1`, `Σ w_n λ_n^{-σ} < ∞` for `σ > 1`, the unit frequency
carries total weight `1` (`aggRealCoeff w lam 1 = 1`), and `Γ_ℝ(s) Σ w_n λ_n^{-s}` satisfies
Riemann's degree-one completed functional equation, then `α = -1/2`, `β = 1/2`, every active
frequency is a positive integer, every positive integer has total weight `1`, and the generalized
Dirichlet series equals `riemannZeta s` on `Re s > 1`. -/
theorem freqDirichlet_eq_riemannZeta_of_completed_functional_equation
    {w : ℕ → ℝ} {lam : ℕ → ℝ} {E : ℂ → ℂ} {α β : ℂ} {C : ℝ}
    (hw : ∀ n, 0 ≤ w n) (hlam : ∀ n, 1 ≤ lam n)
    (hwsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => w n / lam n ^ σ)
    (hone : aggRealCoeff w lam 1 = 1)
    (hE : DifferentiableOn ℂ E (verticalStrip (-1 / 2) (3 / 2)))
    (hdecay : ∀ s ∈ verticalStrip (-1 / 2) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2))
    (hR : ∀ s : ℂ, s.re = 3 / 2 →
      Complex.Gammaℝ s * freqDirichlet (fun n => (w n : ℂ)) lam s =
        E s + (α * Complex.Gammaℝ s + β * Complex.Gammaℝ (s - 1)))
    (hL : ∀ s : ℂ, s.re = -1 / 2 →
      Complex.Gammaℝ (1 - s) * freqDirichlet (fun n => (w n : ℂ)) lam (1 - s) =
        E s + (α * Complex.Gammaℝ s + β * Complex.Gammaℝ (s - 1))) :
    α = -1 / 2 ∧ β = 1 / 2 ∧
      (∀ n, w n ≠ 0 → ∃ m : ℕ, 1 ≤ m ∧ lam n = (m : ℝ)) ∧
      (∀ m : ℕ, aggRealCoeff w lam (m + 1) = 1) ∧
      (∀ s : ℂ, 1 < s.re → freqDirichlet (fun n => (w n : ℂ)) lam s = riemannZeta s) := by
  have ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖(w n : ℂ)‖ / lam n ^ σ :=
    fun σ hσ => (hwsum σ hσ).congr fun n => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw n)]
  have hsum2 : Summable fun n : ℕ => w n / lam n ^ 2 :=
    (hwsum 2 (by norm_num)).congr fun n => by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have htheta : ∀ x : ℝ, 0 < x →
      FreqHamburger.freqTheta (fun n => (w n : ℂ)) lam x =
        (x : ℂ) ^ (-(1 / 2 : ℂ)) * FreqHamburger.freqTheta (fun n => (w n : ℂ)) lam x⁻¹ + α +
          β * (x : ℂ) ^ (-(1 / 2 : ℂ)) :=
    fun x hx => freqTheta_relation_of_completed_functional_equation hlam ha hE hdecay hR hL hx
  have hαβ : α + β = 0 := add_eq_zero_of_self_dual_theta htheta
  have hint : ∀ n, w n ≠ 0 → ∃ m : ℕ, 1 ≤ m ∧ lam n = (m : ℝ) :=
    fun n hwn => exists_nat_pos_eq_of_nonneg_of_freqTheta_relation hw hlam hsum2 htheta hwn
  have haggC : ∀ m : ℕ, aggCoeff w lam (m + 1) = -(2 * α) :=
    aggCoeff_eq_neg_two_mul_of_nonneg_freqTheta_relation hw hlam hsum2 htheta
  have hagg0 : aggCoeff w lam 1 = 1 := by simp [aggCoeff, hone]
  have hα : α = -1 / 2 := by
    have h0 := haggC 0
    rw [zero_add, hagg0] at h0
    linear_combination h0 / 2
  have hβ : β = 1 / 2 := by linear_combination hαβ - hα
  have hagg1 : ∀ m : ℕ, aggRealCoeff w lam (m + 1) = 1 := by
    intro m
    have hm := haggC m
    rw [hα] at hm
    have hm' : ((aggRealCoeff w lam (m + 1) : ℝ) : ℂ) = 1 := by
      rw [← aggCoeff, hm]
      norm_num
    exact_mod_cast hm'
  refine ⟨hα, hβ, hint, hagg1, fun s hs => ?_⟩
  have hdir_norm : Summable fun n : ℕ => ‖(w n : ℂ) * (1 / (lam n : ℂ) ^ s)‖ := by
    refine (ha s.re hs).congr fun n => ?_
    have hlpos : 0 < lam n := lt_of_lt_of_le one_pos (hlam n)
    rw [norm_mul, one_div, norm_inv, Complex.norm_cpow_eq_rpow_re_of_pos hlpos, div_eq_mul_inv]
  have hregroup := tsum_mul_eq_tsum_aggCoeff_mul (φ := fun u : ℝ => 1 / (u : ℂ) ^ s)
    hw hint (summable_ite_of_sq hw hsum2) hdir_norm
  have hlhs : freqDirichlet (fun n => (w n : ℂ)) lam s =
      ∑' n : ℕ, (w n : ℂ) * (1 / (lam n : ℂ) ^ s) := by
    unfold freqDirichlet
    exact tsum_congr fun n => div_eq_mul_one_div _ _
  rw [hlhs, hregroup, ← coeffDirichlet_const_one_eq_riemannZeta hs, coeffDirichlet]
  refine tsum_congr fun m => ?_
  rw [aggCoeff, hagg1 m, Complex.ofReal_one, one_mul]

/-! ## Section 3: Complete categorical rigidity of countable Beurling prime systems -/

/-- The theta series of a discrete Beurling generalized prime system. -/
def beurlingTheta (B : RHTower.BeurlingSystem) (x : ℝ) : ℂ :=
  ∑' g : B.Integer, ((Real.exp (-Real.pi * B.intNorm g ^ 2 * x) : ℝ) : ℂ)

/-- The zeta function `Σ_g |g|^{-s}` of a discrete Beurling generalized prime system. -/
def beurlingZeta (B : RHTower.BeurlingSystem) (s : ℂ) : ℂ :=
  ∑' g : B.Integer, (1 : ℂ) / (B.intNorm g : ℂ) ^ s

/-- In any Beurling system, the empty multiset `0` is the unique generalized integer of norm `1`. -/
theorem intNorm_eq_one_iff (B : RHTower.BeurlingSystem) (g : B.Integer) :
    B.intNorm g = 1 ↔ g = 0 := by
  classical
  refine ⟨fun h => ?_, fun h => by rw [h, B.intNorm_zero]⟩
  by_contra hg0
  obtain ⟨p, hp⟩ := Multiset.exists_mem_of_ne_zero hg0
  have hcons : g = p ::ₘ g.erase p := (Multiset.cons_erase hp).symm
  have hprod : B.intNorm g = B.labelNorm p * B.intNorm (g.erase p) := by
    conv_lhs => rw [hcons]
    rw [← Multiset.singleton_add, B.intNorm_add, B.intNorm_singleton]
  have hp1 : 1 < B.labelNorm p := B.one_lt_labelNorm p
  have hge1 : 1 ≤ B.intNorm (g.erase p) := B.one_le_intNorm _
  nlinarith

/-- **Complete categorical rigidity of countable Beurling systems.**
Let `B : RHTower.BeurlingSystem` have countable label type, with `Σ_g |g|^{-σ} < ∞` for every
`σ > 1`, and suppose `Γ_ℝ(s) beurlingZeta B s` satisfies Riemann's degree-one reflection law on
`-1/2 ≤ Re s ≤ 3/2`. Then:
1. the polar coefficients are automatically forced to be `α = -1/2` and `β = 1/2` (in particular,
   no entire degree-one Beurling Euler product exists);
2. every generalized integer has a positive integer norm, and every positive integer `m ≥ 1`
   occurs as `B.intNorm g` for a unique `g : B.Integer`;
3. `beurlingZeta B s = riemannZeta s` for all `Re s > 1`;
4. `B.Label` admits a norm-preserving bijection onto the rational primes `{p : ℕ // Nat.Prime p}`. -/
theorem beurlingSystem_rigidity_of_completed_functional_equation
    (B : RHTower.BeurlingSystem) [Countable B.Label]
    {E : ℂ → ℂ} {α β : ℂ} {C : ℝ}
    (hBsum : ∀ σ : ℝ, 1 < σ → Summable fun g : B.Integer => 1 / B.intNorm g ^ σ)
    (hE : DifferentiableOn ℂ E (verticalStrip (-1 / 2) (3 / 2)))
    (hdecay : ∀ s ∈ verticalStrip (-1 / 2) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2))
    (hR : ∀ s : ℂ, s.re = 3 / 2 →
      Complex.Gammaℝ s * beurlingZeta B s =
        E s + (α * Complex.Gammaℝ s + β * Complex.Gammaℝ (s - 1)))
    (hL : ∀ s : ℂ, s.re = -1 / 2 →
      Complex.Gammaℝ (1 - s) * beurlingZeta B (1 - s) =
        E s + (α * Complex.Gammaℝ s + β * Complex.Gammaℝ (s - 1))) :
    α = -1 / 2 ∧ β = 1 / 2 ∧
      (∀ g : B.Integer, ∃ m : ℕ, 1 ≤ m ∧ B.intNorm g = (m : ℝ)) ∧
      (∀ m : ℕ, 1 ≤ m → ∃! g : B.Integer, B.intNorm g = (m : ℝ)) ∧
      (∀ s : ℂ, 1 < s.re → beurlingZeta B s = riemannZeta s) ∧
      Nonempty {e : B.Label ≃ {p : ℕ // Nat.Prime p} //
        ∀ l : B.Label, B.labelNorm l = ((e l : ℕ) : ℝ)} := by
  classical
  obtain ⟨f, hf⟩ := Countable.exists_injective_nat B.Integer
  set w : ℕ → ℝ := fun n => if ∃ g : B.Integer, f g = n then 1 else 0
  set lam : ℕ → ℝ := fun n =>
    if h : ∃ g : B.Integer, f g = n then B.intNorm (Classical.choose h) else 1
  have hwf : ∀ g : B.Integer, w (f g) = 1 := fun g => if_pos ⟨g, rfl⟩
  have hlamf : ∀ g : B.Integer, lam (f g) = B.intNorm g := by
    intro g
    have hex : ∃ g' : B.Integer, f g' = f g := ⟨g, rfl⟩
    simp only [lam, dif_pos hex]
    rw [hf (Classical.choose_spec hex)]
  have hw0 : ∀ n : ℕ, n ∉ range f → w n = 0 := by
    intro n hn
    exact if_neg hn
  have hw_nn : ∀ n : ℕ, 0 ≤ w n := fun n => by simp only [w]; split_ifs <;> norm_num
  have hlam1 : ∀ n : ℕ, 1 ≤ lam n := by
    intro n
    simp only [lam]
    split_ifs with h
    · exact B.one_le_intNorm _
    · exact le_rfl
  have hwsum : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => w n / lam n ^ σ := by
    intro σ hσ
    have hcomp : ((fun n : ℕ => w n / lam n ^ σ) ∘ f) =
        fun g : B.Integer => 1 / B.intNorm g ^ σ := by
      funext g
      dsimp only [Function.comp_apply]
      rw [hwf g, hlamf g]
    refine (Function.Injective.summable_iff hf ?_).mp ?_
    · intro n hn
      simp [hw0 n hn]
    · rw [hcomp]
      exact hBsum σ hσ
  have hZeq : ∀ s : ℂ, beurlingZeta B s = freqDirichlet (fun n => (w n : ℂ)) lam s := by
    intro s
    unfold beurlingZeta freqDirichlet
    have hinj := Function.Injective.tsum_eq hf
      (f := fun n : ℕ => (w n : ℂ) / (lam n : ℂ) ^ s) fun n hn => by
      by_contra hnr
      exact hn (by simp [hw0 n hnr])
    rw [← hinj]
    refine tsum_congr fun g => ?_
    rw [hwf g, hlamf g, Complex.ofReal_one]
  have hone : aggRealCoeff w lam 1 = 1 := by
    unfold aggRealCoeff
    rw [tsum_eq_single (f 0)]
    · rw [hlamf 0, B.intNorm_zero, Nat.cast_one, if_pos rfl, hwf 0]
    · intro n hn0
      split_ifs with hln
      · by_cases hmem : ∃ g : B.Integer, f g = n
        · obtain ⟨g, rfl⟩ := hmem
          rw [hlamf g, Nat.cast_one, intNorm_eq_one_iff] at hln
          exact False.elim (hn0 (congrArg f hln))
        · exact hw0 n hmem
      · rfl
  have hR' : ∀ s : ℂ, s.re = 3 / 2 →
      Complex.Gammaℝ s * freqDirichlet (fun n => (w n : ℂ)) lam s =
        E s + (α * Complex.Gammaℝ s + β * Complex.Gammaℝ (s - 1)) := by
    intro s hs; rw [← hZeq s]; exact hR s hs
  have hL' : ∀ s : ℂ, s.re = -1 / 2 →
      Complex.Gammaℝ (1 - s) * freqDirichlet (fun n => (w n : ℂ)) lam (1 - s) =
        E s + (α * Complex.Gammaℝ s + β * Complex.Gammaℝ (s - 1)) := by
    intro s hs; rw [← hZeq (1 - s)]; exact hL s hs
  obtain ⟨hα, hβ, hint, hagg1, hzeta⟩ :=
    freqDirichlet_eq_riemannZeta_of_completed_functional_equation
      hw_nn hlam1 hwsum hone hE hdecay hR' hL'
  have hg_int : ∀ g : B.Integer, ∃ m : ℕ, 1 ≤ m ∧ B.intNorm g = (m : ℝ) := by
    intro g
    have h := hint (f g) (by rw [hwf g]; exact one_ne_zero)
    rwa [hlamf g] at h
  have hm_uniq : ∀ m : ℕ, 1 ≤ m → ∃! g : B.Integer, B.intNorm g = (m : ℝ) := by
    intro m hm1
    have hm_pred : (m - 1) + 1 = m := by omega
    have hagg_m : aggRealCoeff w lam m = 1 := hm_pred ▸ hagg1 (m - 1)
    have htsum_g : (∑' g : B.Integer, if B.intNorm g = (m : ℝ) then (1 : ℝ) else 0) = 1 := by
      have hinj := Function.Injective.tsum_eq hf
        (f := fun n : ℕ => if lam n = (m : ℝ) then w n else 0) fun n hn => by
        by_contra hnr
        exact hn (by simp [hw0 n hnr])
      have hcongr : (∑' g : B.Integer, if lam (f g) = (m : ℝ) then w (f g) else 0) =
          ∑' g : B.Integer, if B.intNorm g = (m : ℝ) then (1 : ℝ) else 0 :=
        tsum_congr fun g => by rw [hlamf g, hwf g]
      rw [← hcongr, hinj]
      exact hagg_m
    have hsum_ind : Summable fun g : B.Integer =>
        if B.intNorm g = (m : ℝ) then (1 : ℝ) else 0 := by
      have hs2 : Summable fun g : B.Integer => 1 / B.intNorm g ^ 2 :=
        (hBsum 2 (by norm_num)).congr fun g => by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      refine (hs2.mul_left ((m : ℝ) ^ 2)).of_nonneg_of_le
        (fun g => by split_ifs <;> norm_num) fun g => ?_
      split_ifs with h
      · rw [h]
        have hmpos : (0 : ℝ) < (m : ℝ) ^ 2 := by
          have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
          positivity
        field_simp
        rfl
      · positivity
    have hex : ∃ g : B.Integer, B.intNorm g = (m : ℝ) := by
      by_contra hnone
      push Not at hnone
      have hz : (∑' g : B.Integer, if B.intNorm g = (m : ℝ) then (1 : ℝ) else 0) = 0 := by
        simp [hnone]
      linarith
    obtain ⟨g₀, hg₀⟩ := hex
    refine ⟨g₀, hg₀, fun g₁ hg₁ => ?_⟩
    by_contra hne
    have hle := hsum_ind.sum_le_tsum ({g₀, g₁} : Finset B.Integer)
      (fun g _ => by split_ifs <;> norm_num)
    rw [Finset.sum_pair (Ne.symm hne), if_pos hg₀, if_pos hg₁, htsum_g] at hle
    linarith
  -- Construct the norm-preserving bijection `B.Label ≃ {p : ℕ // Nat.Prime p}`
  have hp_prime : ∀ l : B.Label, ∃ p : ℕ, Nat.Prime p ∧ B.labelNorm l = (p : ℝ) := by
    intro l
    obtain ⟨q, hq1, hq⟩ := hg_int {l}
    rw [B.intNorm_singleton] at hq
    have hq2 : 2 ≤ q := by
      have hl1 : (1 : ℝ) < B.labelNorm l := B.one_lt_labelNorm l
      have : (1 : ℝ) < (q : ℝ) := hq ▸ hl1
      have hqgt : 1 < q := by exact_mod_cast this
      omega
    refine ⟨q, ?_, hq⟩
    rw [Nat.prime_def]
    refine ⟨hq2, fun a hdvd => ?_⟩
    obtain ⟨b, rfl⟩ := hdvd
    by_cases ha1 : a = 1
    · exact Or.inl ha1
    by_cases hb1 : b = 1
    · exact Or.inr (by rw [hb1, mul_one])
    exfalso
    have ha0 : a ≠ 0 := by intro h; subst h; simp at hq2
    have hb0 : b ≠ 0 := by intro h; subst h; simp at hq2
    have ha2 : 2 ≤ a := by omega
    have hb2 : 2 ≤ b := by omega
    obtain ⟨ga, hga, -⟩ := hm_uniq a (by omega)
    obtain ⟨gb, hgb, -⟩ := hm_uniq b (by omega)
    have hga0 : ga ≠ 0 := by
      intro h0
      rw [h0, B.intNorm_zero] at hga
      have : (1 : ℝ) = (a : ℝ) := hga
      have : 1 = a := by exact_mod_cast this
      omega
    have hgb0 : gb ≠ 0 := by
      intro h0
      rw [h0, B.intNorm_zero] at hgb
      have : (1 : ℝ) = (b : ℝ) := hgb
      have : 1 = b := by exact_mod_cast this
      omega
    have hprod : B.intNorm (ga + gb) = ((a * b : ℕ) : ℝ) := by
      rw [B.intNorm_add, hga, hgb]
      push_cast
      rfl
    have hsing : B.intNorm ({l} : B.Integer) = ((a * b : ℕ) : ℝ) := by
      rwa [B.intNorm_singleton]
    have heq_ms : ga + gb = {l} :=
      (hm_uniq (a * b) (by omega)).unique hprod hsing
    have hcard := congrArg Multiset.card heq_ms
    rw [Multiset.card_add, Multiset.card_singleton] at hcard
    have hca : 1 ≤ ga.card := Nat.one_le_iff_ne_zero.mpr (Multiset.card_eq_zero.not.mpr hga0)
    have hcb : 1 ≤ gb.card := Nat.one_le_iff_ne_zero.mpr (Multiset.card_eq_zero.not.mpr hgb0)
    omega
  set toP : B.Label → {p : ℕ // Nat.Prime p} := fun l =>
    ⟨Classical.choose (hp_prime l), (Classical.choose_spec (hp_prime l)).1⟩
  have htoP_norm : ∀ l : B.Label, B.labelNorm l = ((toP l : ℕ) : ℝ) :=
    fun l => (Classical.choose_spec (hp_prime l)).2
  have hbij : Function.Bijective toP := by
    refine ⟨fun l₁ l₂ heq => ?_, fun ⟨p, hp⟩ => ?_⟩
    · have hn1 : B.intNorm ({l₁} : B.Integer) = ((toP l₁ : ℕ) : ℝ) := by
        rw [B.intNorm_singleton, htoP_norm l₁]
      have hn2 : B.intNorm ({l₂} : B.Integer) = ((toP l₁ : ℕ) : ℝ) := by
        rw [B.intNorm_singleton, htoP_norm l₂, heq]
      have hms := (hm_uniq (toP l₁) (toP l₁).2.one_lt.le).unique hn1 hn2
      have hmem : l₁ ∈ ({l₂} : Multiset B.Label) := hms ▸ Multiset.mem_singleton_self l₁
      exact Multiset.mem_singleton.mp hmem
    · obtain ⟨g, hg, -⟩ := hm_uniq p hp.one_lt.le
      have hg0 : g ≠ 0 := by
        intro h0
        rw [h0, B.intNorm_zero] at hg
        have : 1 = p := by exact_mod_cast hg
        exact hp.ne_one this.symm
      obtain ⟨l, hl⟩ := Multiset.exists_mem_of_ne_zero hg0
      have hcons : g = l ::ₘ g.erase l := (Multiset.cons_erase hl).symm
      have hfac : (p : ℝ) = ((toP l : ℕ) : ℝ) * B.intNorm (g.erase l) := by
        rw [← hg]
        conv_lhs => rw [hcons]
        rw [← Multiset.singleton_add, B.intNorm_add, B.intNorm_singleton, htoP_norm l]
      obtain ⟨b, _, hb⟩ := hg_int (g.erase l)
      rw [hb] at hfac
      have hdvd : (toP l : ℕ) ∣ p := ⟨b, by exact_mod_cast hfac⟩
      have heqp : (toP l : ℕ) = p :=
        (hp.eq_one_or_self_of_dvd _ hdvd).resolve_left (toP l).2.ne_one
      exact ⟨l, Subtype.ext heqp⟩
  refine ⟨hα, hβ, hg_int, hm_uniq, fun s hs => (hZeq s).trans (hzeta s hs),
    ⟨⟨Equiv.ofBijective toP hbij, fun l => htoP_norm l⟩⟩⟩

/-! ## Section 4: Nonnegative Borel measure rigidity on `[1, ∞)` -/

/-- The theta integral of a Borel measure `ν` on `[1, ∞)`:
`θ_ν(x) = ∫_{u ≥ 1} e^{-π u² x} dν(u)`. -/
def measureTheta (ν : Measure ℝ) (x : ℝ) : ℂ :=
  ∫ u in Ici (1 : ℝ), ((Real.exp (-Real.pi * u ^ 2 * x) : ℝ) : ℂ) ∂ν

/-- Equivalence of `measureTheta` with the complex exponential integral on `[1, ∞)`. -/
theorem measureTheta_eq_integral_cexp (ν : Measure ℝ) (x : ℝ) :
    measureTheta ν x = ∫ u in Ici (1 : ℝ), cexp (-Real.pi * (u : ℂ) ^ 2 * x) ∂ν := by
  unfold measureTheta
  refine setIntegral_congr_fun measurableSet_Ici fun u _ => ?_
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- The partial-fraction integral `L_ν(t) = ∫_{u ≥ 1} t / (π(u² + t²)) dν(u)`. -/
def measureSeries (ν : Measure ℝ) (t : ℂ) : ℂ :=
  ∫ u in Ici (1 : ℝ), t / ((Real.pi : ℂ) * ((u : ℂ) ^ 2 + t ^ 2)) ∂ν

/-- The dual Laplace integral `F_ν(t) = ∫_{u ≥ 1} e^{-2π u t} dν(u)`. -/
def measureDual (ν : Measure ℝ) (t : ℂ) : ℂ :=
  ∫ u in Ici (1 : ℝ), cexp (-(2 * Real.pi * (u : ℂ) * t)) ∂ν

/-- Cubic exponential decay bound `e^{-y} ≤ 27 / y³` for `y > 0`, used to dominate the `t`-derivative
of `e^{-2π u t}` by `C / u²` on `[1, ∞)`. -/
theorem exp_neg_le_twentySeven_div_cube {y : ℝ} (hy : 0 < y) :
    Real.exp (-y) ≤ 27 / y ^ 3 := by
  have h1 : y / 3 ≤ Real.exp (y / 3) := by linarith [Real.add_one_le_exp (y / 3)]
  have h2 : (y / 3) ^ 3 ≤ Real.exp (y / 3) ^ 3 := pow_le_pow_left₀ (by positivity) h1 3
  have h3 : Real.exp (y / 3) ^ 3 = Real.exp y := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have h4 : y ^ 3 / 27 ≤ Real.exp y := by
    calc y ^ 3 / 27 = (y / 3) ^ 3 := by ring
      _ ≤ Real.exp (y / 3) ^ 3 := h2
      _ = Real.exp y := h3
  rw [Real.exp_neg, ← one_div, div_le_div_iff₀ (Real.exp_pos y) (by positivity)]
  linarith

/-- **Laplace identity on `(0, ∞)` for `measureTheta`.**
For any s-finite Borel measure `ν` with `∫_{u ≥ 1} (1 / u²) dν(u) < ∞` whose theta integral
satisfies `θ_ν(x) = x^{-1/2} θ_ν(1/x) + α + β x^{-1/2}` on `(0, ∞)`, for every real `t > 0`,
`measureSeries ν t = measureDual ν t + α / (π t) + β`. -/
theorem measureSeries_eq_of_measureTheta_relation_ofReal (ν : Measure ℝ) [SFinite ν]
    (hint : IntegrableOn (fun u : ℝ => 1 / u ^ 2) (Ici 1) ν) {α β : ℂ}
    (htheta : ∀ x : ℝ, 0 < x →
      measureTheta ν x =
        (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ)))
    {t : ℝ} (ht : 0 < t) :
    measureSeries ν t = measureDual ν t + α / (Real.pi * t) + β := by
  set μ₁ : Measure ℝ := ν.restrict (Ici 1)
  set μ₂ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  set e : ℝ → ℂ := fun x => ((Real.exp (-(Real.pi * t ^ 2) * x) : ℝ) : ℂ) with he_def
  have hB : 0 < Real.pi * t ^ 2 := by positivity
  have he_int : Integrable e μ₂ := (integrableOn_Ioi_exp_neg_mul hB).ofReal
  have hhe_eq : ∀ x ∈ Ioi (0 : ℝ), (x : ℂ) ^ (-(1 / 2 : ℂ)) * e x =
      ((x ^ ((1 / 2 : ℝ) - 1) * Real.exp (-((Real.pi * t ^ 2) * x)) : ℝ) : ℂ) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [he_def, Complex.ofReal_mul, Complex.ofReal_cpow hx0.le]
    push_cast
    ring_nf
  have hhe_int : Integrable (fun x : ℝ => (x : ℂ) ^ (-(1 / 2 : ℂ)) * e x) μ₂ := by
    have h : IntegrableOn (fun x : ℝ => x ^ ((1 / 2 : ℝ) - 1) *
        Real.exp (-(Real.pi * t ^ 2) * x ^ (1 : ℝ))) (Ioi 0) :=
      integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) le_rfl hB
    have h' : IntegrableOn (fun x : ℝ => ((x ^ ((1 / 2 : ℝ) - 1) *
        Real.exp (-((Real.pi * t ^ 2) * x)) : ℝ) : ℂ)) (Ioi 0) := by
      have := Integrable.ofReal (𝕜 := ℂ) h
      simp only [Real.rpow_one, neg_mul] at this
      exact this
    exact IntegrableOn.congr_fun h' (fun x hx => (hhe_eq x hx).symm) measurableSet_Ioi
  -- First Fubini swap: `∫_{x > 0} θ_ν(x) e^{-π t² x} dx = ∫_{u ≥ 1} 1 / (π(u² + t²)) dν(u)`
  set G₁ : ℝ → ℝ → ℂ := fun x u =>
    ((Real.exp (-(Real.pi * (u ^ 2 + t ^ 2)) * x) : ℝ) : ℂ) with hG₁_def
  have hG₁_meas : AEStronglyMeasurable (Function.uncurry G₁) (μ₂.prod μ₁) :=
    (by unfold G₁ Function.uncurry; fun_prop : Continuous (Function.uncurry G₁)).aestronglyMeasurable
  have hG₁_int : Integrable (Function.uncurry G₁) (μ₂.prod μ₁) := by
    rw [integrable_prod_iff' hG₁_meas]
    refine ⟨Eventually.of_forall fun u => ?_, ?_⟩
    · exact (integrableOn_Ioi_exp_neg_mul (by positivity : 0 < Real.pi * (u ^ 2 + t ^ 2))).ofReal
    · have hnorm₁ : (fun u : ℝ => ∫ x, ‖G₁ x u‖ ∂μ₂) =
          fun u : ℝ => 1 / (Real.pi * (u ^ 2 + t ^ 2)) := funext fun u => by
        have hk : 0 < Real.pi * (u ^ 2 + t ^ 2) := by positivity
        have hpt : (fun x : ℝ => ‖G₁ x u‖) =
            fun x : ℝ => Real.exp (-(Real.pi * (u ^ 2 + t ^ 2)) * x) := by
          funext x
          rw [hG₁_def, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        rw [hpt]
        exact integral_Ioi_exp_neg_mul hk
      dsimp only [Function.uncurry]
      rw [hnorm₁]
      refine (hint.const_mul (1 / Real.pi)).mono'
        (continuous_const.div (by fun_prop) fun u => by positivity).aestronglyMeasurable
        ((ae_restrict_iff' measurableSet_Ici).mpr (Eventually.of_forall fun u hu => ?_))
      have hk : 0 < Real.pi * (u ^ 2 + t ^ 2) := by positivity
      have hu0 : 0 < u := lt_of_lt_of_le one_pos hu
      rw [Real.norm_eq_abs, abs_of_pos (div_pos one_pos hk), div_le_iff₀ hk]
      calc (1 : ℝ) = (1 / Real.pi) * (1 / u ^ 2) * (Real.pi * u ^ 2) := by field_simp
        _ ≤ (1 / Real.pi) * (1 / u ^ 2) * (Real.pi * (u ^ 2 + t ^ 2)) := by
            gcongr
            nlinarith [sq_nonneg t]
  have hswap₁ := integral_integral_swap hG₁_int
  have hG₁_lhs : (∫ x, (∫ u, G₁ x u ∂μ₁) ∂μ₂) = ∫ x, measureTheta ν x * e x ∂μ₂ := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [measureTheta, ← integral_mul_const]
    refine setIntegral_congr_fun measurableSet_Ici fun u _ => ?_
    rw [hG₁_def, he_def, ← Complex.ofReal_mul, ← Real.exp_add]
    congr 1
    ring_nf
  have hG₁_rhs : (t : ℂ) * (∫ u, (∫ x, G₁ x u ∂μ₂) ∂μ₁) = measureSeries ν t := by
    rw [measureSeries, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ici fun u _ => ?_
    have hk : 0 < Real.pi * (u ^ 2 + t ^ 2) := by positivity
    rw [hG₁_def, integral_complex_ofReal, integral_Ioi_exp_neg_mul hk]
    push_cast
    ring
  -- Second Fubini swap: `∫_{x > 0} x^{-1/2} θ_ν(1/x) e^{-π t² x} dx = (1 / t) measureDual ν t`
  set G₂ : ℝ → ℝ → ℂ := fun x u =>
    ((x ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * u ^ 2 / x) - Real.pi * t ^ 2 * x) : ℝ) : ℂ)
    with hG₂_def
  have hG₂_meas : AEStronglyMeasurable (Function.uncurry G₂) (μ₂.prod μ₁) := by
    refine Measurable.aestronglyMeasurable ?_
    have hm1 : Measurable fun p : ℝ × ℝ => p.1 ^ (-(1 / 2 : ℝ)) := measurable_fst.pow_const _
    have hm2 : Measurable fun p : ℝ × ℝ =>
        Real.exp (-(Real.pi * p.2 ^ 2 / p.1) - Real.pi * t ^ 2 * p.1) :=
      Real.measurable_exp.comp
        (((measurable_const.mul (measurable_snd.pow_const 2)).div measurable_fst).neg.sub
          (measurable_const.mul measurable_fst))
    exact Complex.measurable_ofReal.comp (hm1.mul hm2)
  have hG₂_int : Integrable (Function.uncurry G₂) (μ₂.prod μ₁) := by
    rw [integrable_prod_iff' hG₂_meas]
    refine ⟨(ae_restrict_iff' measurableSet_Ici).mpr (Eventually.of_forall fun u hu => ?_), ?_⟩
    · exact (integrableOn_rpow_neg_half_mul_exp_theta_dual (lt_of_lt_of_le one_pos hu) ht).ofReal
    · have hnorm₂_ae : (fun u : ℝ => ∫ x, ‖G₂ x u‖ ∂μ₂) =ᵐ[μ₁]
          fun u : ℝ => 1 / t * Real.exp (-(2 * Real.pi * u * t)) := by
        refine (ae_restrict_iff' measurableSet_Ici).mpr (Eventually.of_forall fun u hu => ?_)
        have hu0 : 0 < u := lt_of_lt_of_le one_pos hu
        have hpt : ∀ x ∈ Ioi (0 : ℝ), ‖G₂ x u‖ =
            x ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * u ^ 2 / x) - Real.pi * t ^ 2 * x) := by
          intro x hx
          have hx0 : (0 : ℝ) < x := hx
          rw [hG₂_def, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        dsimp only [μ₂]
        rw [setIntegral_congr_fun measurableSet_Ioi hpt]
        exact integral_rpow_neg_half_mul_exp_theta_dual hu0 ht
      refine Integrable.congr ?_ hnorm₂_ae.symm
      refine (hint.const_mul (1 / (2 * Real.pi ^ 2 * t ^ 3))).mono'
        (by fun_prop : Continuous fun u : ℝ =>
          1 / t * Real.exp (-(2 * Real.pi * u * t))).aestronglyMeasurable
        ((ae_restrict_iff' measurableSet_Ici).mpr (Eventually.of_forall fun u hu => ?_))
      have hu0 : 0 < u := lt_of_lt_of_le one_pos hu
      have hy : 0 < 2 * Real.pi * u * t := by positivity
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
      calc 1 / t * Real.exp (-(2 * Real.pi * u * t))
          ≤ 1 / t * (2 / (2 * Real.pi * u * t) ^ 2) :=
            mul_le_mul_of_nonneg_left (exp_neg_le_two_div_sq hy) (by positivity)
        _ = (1 / (2 * Real.pi ^ 2 * t ^ 3)) * (1 / u ^ 2) := by field_simp
  have hG₂_slice_eq : ∀ x ∈ Ioi (0 : ℝ),
      (∫ u, G₂ x u ∂μ₁) = (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ * e x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    have hcpow : (x : ℂ) ^ (-(1 / 2 : ℂ)) = ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hx0.le]
      push_cast
      ring_nf
    rw [measureTheta, ← integral_const_mul, ← integral_mul_const]
    dsimp only [μ₁]
    refine setIntegral_congr_fun measurableSet_Ici fun u _ => ?_
    rw [hG₂_def, he_def, hcpow]
    dsimp only
    rw [show -(Real.pi * u ^ 2 / x) - Real.pi * t ^ 2 * x =
      -Real.pi * u ^ 2 * x⁻¹ + -(Real.pi * t ^ 2) * x by ring, Real.exp_add]
    push_cast
    ring
  have hD_int : Integrable (fun x : ℝ => (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ * e x) μ₂ :=
    hG₂_int.integral_prod_left.congr
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall hG₂_slice_eq))
  have hswap₂ := integral_integral_swap hG₂_int
  have hG₂_lhs : (∫ x, (∫ u, G₂ x u ∂μ₁) ∂μ₂) =
      ∫ x, (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ * e x ∂μ₂ :=
    setIntegral_congr_fun measurableSet_Ioi hG₂_slice_eq
  have hG₂_rhs : (∫ u, (∫ x, G₂ x u ∂μ₂) ∂μ₁) = (1 / (t : ℂ)) * measureDual ν t := by
    rw [measureDual, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ici fun u hu => ?_
    have hu0 : 0 < u := lt_of_lt_of_le one_pos hu
    rw [hG₂_def, integral_complex_ofReal, integral_rpow_neg_half_mul_exp_theta_dual hu0 ht]
    push_cast
    ring
  have hI0 : ∫ x, e x ∂μ₂ = ((1 / (Real.pi * t ^ 2) : ℝ) : ℂ) := by
    rw [he_def, integral_complex_ofReal, integral_Ioi_exp_neg_mul hB]
  have hIh : ∫ x, (x : ℂ) ^ (-(1 / 2 : ℂ)) * e x ∂μ₂ = ((1 / t : ℝ) : ℂ) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hhe_eq, integral_complex_ofReal,
      integral_Ioi_rpow_neg_half_mul_exp_neg_mul_sq ht]
  have hpt : ∀ x ∈ Ioi (0 : ℝ), measureTheta ν x * e x =
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ * e x +
        (α * e x + β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * e x)) := fun x hx => by
    rw [htheta x hx]
    ring
  have hsplit : ∫ x, measureTheta ν x * e x ∂μ₂ =
      (∫ x, (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ * e x ∂μ₂) +
        (α * ∫ x, e x ∂μ₂) + β * ∫ x, (x : ℂ) ^ (-(1 / 2 : ℂ)) * e x ∂μ₂ := by
    have h1 : (∫ x, ((x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ * e x +
        (α * e x + β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * e x))) ∂μ₂) =
        (∫ x, (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ * e x ∂μ₂) +
          ∫ x, (α * e x + β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * e x)) ∂μ₂ :=
      integral_add hD_int ((he_int.const_mul α).add (hhe_int.const_mul β))
    have h2 : (∫ x, (α * e x + β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * e x)) ∂μ₂) =
        (∫ x, α * e x ∂μ₂) + ∫ x, β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * e x) ∂μ₂ :=
      integral_add (he_int.const_mul α) (hhe_int.const_mul β)
    have hcongr_pt : (∫ x, measureTheta ν x * e x ∂μ₂) =
        ∫ x, ((x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ * e x +
          (α * e x + β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * e x))) ∂μ₂ :=
      setIntegral_congr_fun measurableSet_Ioi hpt
    rw [hcongr_pt, h1, h2, integral_const_mul, integral_const_mul]
    ring
  have hL : (∫ u, (∫ x, G₁ x u ∂μ₂) ∂μ₁) =
      (1 / (t : ℂ)) * measureDual ν t +
        α * ((1 / (Real.pi * t ^ 2) : ℝ) : ℂ) + β * ((1 / t : ℝ) : ℂ) := by
    rw [← hswap₁, hG₁_lhs, hsplit, ← hG₂_lhs, hswap₂, hG₂_rhs, hI0, hIh]
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [← hG₁_rhs, hL]
  push_cast
  field_simp [ht0, hπ]

/-- `measureSeries ν` is holomorphic on the open right half-plane `{t : ℂ | 0 < t.re}`. -/
theorem differentiableOn_measureSeries (ν : Measure ℝ)
    (hint : IntegrableOn (fun u : ℝ => 1 / u ^ 2) (Ici 1) ν) :
    DifferentiableOn ℂ (measureSeries ν) {t : ℂ | 0 < t.re} := by
  intro t₀ ht₀
  have h0 : 0 < t₀.re := ht₀
  set δ : ℝ := t₀.re / 2 with hδ
  set R : ℝ := ‖t₀‖ + δ with hR
  set c : ℝ := min (3 / 4) ((t₀.re / 2) ^ 2 / (4 * (‖t₀‖ + t₀.re / 2) ^ 2)) with hc
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hRpos : 0 < R := by rw [hR]; linarith [norm_nonneg t₀]
  have hcpos : 0 < c := lt_min (by norm_num) (by positivity)
  set μ₁ : Measure ℝ := ν.restrict (Ici 1)
  set F : ℂ → ℝ → ℂ := fun t u => t / ((Real.pi : ℂ) * ((u : ℂ) ^ 2 + t ^ 2))
  set F' : ℂ → ℝ → ℂ := fun t u =>
    ((u : ℂ) ^ 2 - t ^ 2) / ((Real.pi : ℂ) * ((u : ℂ) ^ 2 + t ^ 2) ^ 2)
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hden_ne : ∀ t : ℂ, 0 < t.re → ∀ u : ℝ, (u : ℂ) ^ 2 + t ^ 2 ≠ 0 := by
    intro t htre u hzero
    have hfac : (u : ℂ) ^ 2 + t ^ 2 = (t - (u : ℂ) * I) * (t + (u : ℂ) * I) := by
      ring_nf; rw [Complex.I_sq]; ring
    rw [hfac, mul_eq_zero] at hzero
    rcases hzero with h1 | h2
    · have := congrArg Complex.re h1; simp at this; linarith
    · have := congrArg Complex.re h2; simp at this; linarith
  have hball_re : ∀ t ∈ Metric.ball t₀ δ, δ < t.re ∧ ‖t‖ ≤ R := by
    intro t ht
    rw [Metric.mem_ball, dist_eq_norm] at ht
    have h1 := abs_re_le_norm (t - t₀)
    rw [sub_re, abs_le] at h1
    have hn := norm_le_norm_add_norm_sub' t t₀
    have hrev : ‖t - t₀‖ = ‖t₀ - t‖ := norm_sub_rev _ _
    exact ⟨by linarith [h1.1], by rw [hR]; linarith⟩
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ₁)
    (F := F) (F' := F') (s := Metric.ball t₀ δ)
    (bound := fun u : ℝ => ((1 + R ^ 2) / (Real.pi * c ^ 2)) * (1 / u ^ 2))
    (Metric.ball_mem_nhds t₀ hδpos) ?_ ?_ ?_ ?_ (hint.const_mul _) ?_
  · exact hderiv.2.differentiableAt.differentiableWithinAt
  · filter_upwards [Metric.ball_mem_nhds t₀ hδpos] with t ht
    have htre : 0 < t.re := hδpos.trans (hball_re t ht).1
    exact (continuous_const.div
      (continuous_const.mul ((Complex.continuous_ofReal.pow 2).add continuous_const))
      fun u => mul_ne_zero hπ (hden_ne t htre u)).aestronglyMeasurable
  · have ht0_ball : t₀ ∈ Metric.ball t₀ δ := Metric.mem_ball_self hδpos
    refine (hint.const_mul (R / (Real.pi * c))).mono'
      (continuous_const.div
        (continuous_const.mul ((Complex.continuous_ofReal.pow 2).add continuous_const))
        fun u => mul_ne_zero hπ (hden_ne t₀ h0 u)).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ici).mpr (Eventually.of_forall fun u hu => ?_))
    rw [mem_Ici] at hu
    have hu0 : 0 ≤ u := by linarith
    have hu_pos : 0 < u := lt_of_lt_of_le one_pos hu
    have hden := FreqHamburger.norm_sq_add_sq_ge_on_ball h0 ht0_ball hu0
    have ht0R : ‖t₀‖ ≤ R := (hball_re t₀ ht0_ball).2
    have hpos : 0 < c * u ^ 2 := by positivity
    simp only [F]
    rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      div_le_iff₀ (mul_pos Real.pi_pos (lt_of_lt_of_le hpos hden))]
    calc ‖t₀‖ ≤ R := ht0R
      _ = (R / (Real.pi * c)) * (1 / u ^ 2) * (Real.pi * (c * u ^ 2)) := by field_simp
      _ ≤ (R / (Real.pi * c)) * (1 / u ^ 2) * (Real.pi * ‖(u : ℂ) ^ 2 + t₀ ^ 2‖) := by gcongr
  · exact (((Complex.continuous_ofReal.pow 2).sub continuous_const).div
      (continuous_const.mul (((Complex.continuous_ofReal.pow 2).add continuous_const).pow 2))
      fun u => mul_ne_zero hπ (pow_ne_zero 2 (hden_ne t₀ h0 u))).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ici).mpr (Eventually.of_forall fun u hu t ht => ?_)
    rw [mem_Ici] at hu
    have hu0 : 0 ≤ u := by linarith
    have hu_pos : 0 < u := lt_of_lt_of_le one_pos hu
    have hden := FreqHamburger.norm_sq_add_sq_ge_on_ball h0 ht hu0
    have htR : ‖t‖ ≤ R := (hball_re t ht).2
    have hpos : 0 < c * u ^ 2 := by positivity
    have hden_sq : c ^ 2 * u ^ 4 ≤ ‖(u : ℂ) ^ 2 + t ^ 2‖ ^ 2 := by
      have hsq := pow_le_pow_left₀ hpos.le hden 2
      linarith [show (c * u ^ 2) ^ 2 = c ^ 2 * u ^ 4 by ring]
    have hnum : ‖(u : ℂ) ^ 2 - t ^ 2‖ ≤ (1 + R ^ 2) * u ^ 2 := by
      have hn1 : ‖(u : ℂ) ^ 2‖ = u ^ 2 := by
        rw [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
      have hn2 : ‖t ^ 2‖ ≤ R ^ 2 := by
        rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg t) htR 2
      have htri := norm_sub_le ((u : ℂ) ^ 2) (t ^ 2)
      rw [hn1] at htri
      have hu2 : 1 ≤ u ^ 2 := by nlinarith
      nlinarith
    simp only [F']
    rw [norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      div_le_iff₀ (mul_pos Real.pi_pos (lt_of_lt_of_le (by positivity : 0 < c ^ 2 * u ^ 4) hden_sq))]
    calc ‖(u : ℂ) ^ 2 - t ^ 2‖ ≤ (1 + R ^ 2) * u ^ 2 := hnum
      _ = ((1 + R ^ 2) / (Real.pi * c ^ 2)) * (1 / u ^ 2) * (Real.pi * (c ^ 2 * u ^ 4)) := by
          field_simp
      _ ≤ ((1 + R ^ 2) / (Real.pi * c ^ 2)) * (1 / u ^ 2) *
            (Real.pi * ‖(u : ℂ) ^ 2 + t ^ 2‖ ^ 2) := by gcongr
  · refine (ae_restrict_iff' measurableSet_Ici).mpr (Eventually.of_forall fun u _ t ht => ?_)
    have htre : 0 < t.re := hδpos.trans (hball_re t ht).1
    have hd_ne := hden_ne t htre u
    have hd_num : HasDerivAt (fun z : ℂ => z) 1 t := hasDerivAt_id t
    have hd_den : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) * ((u : ℂ) ^ 2 + z ^ 2))
        ((Real.pi : ℂ) * (0 + (2 : ℕ) * t ^ (2 - 1))) t :=
      (((hasDerivAt_const t ((u : ℂ) ^ 2)).add (hasDerivAt_pow 2 t)).const_mul (Real.pi : ℂ))
    refine (hd_num.div hd_den (mul_ne_zero hπ hd_ne)).congr_deriv ?_
    simp only [F']
    field_simp [hπ, hd_ne]
    ring

/-- `measureDual ν` is holomorphic on the open right half-plane `{t : ℂ | 0 < t.re}`. -/
theorem differentiableOn_measureDual (ν : Measure ℝ)
    (hint : IntegrableOn (fun u : ℝ => 1 / u ^ 2) (Ici 1) ν) :
    DifferentiableOn ℂ (measureDual ν) {t : ℂ | 0 < t.re} := by
  intro t₀ ht₀
  have h0 : 0 < t₀.re := ht₀
  set δ : ℝ := t₀.re / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set μ₁ : Measure ℝ := ν.restrict (Ici 1)
  set F : ℂ → ℝ → ℂ := fun t u => cexp (-(2 * Real.pi * (u : ℂ) * t))
  set F' : ℂ → ℝ → ℂ := fun t u =>
    (-(2 * (Real.pi : ℂ) * (u : ℂ))) * cexp (-(2 * Real.pi * (u : ℂ) * t))
  have hball_re : ∀ t ∈ Metric.ball t₀ δ, δ < t.re := by
    intro t ht
    rw [Metric.mem_ball, dist_eq_norm] at ht
    have h1 := abs_re_le_norm (t - t₀)
    rw [sub_re, abs_le] at h1
    linarith [h1.1]
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ₁)
    (F := F) (F' := F') (s := Metric.ball t₀ δ)
    (bound := fun u : ℝ => (27 / (4 * Real.pi ^ 2 * δ ^ 3)) * (1 / u ^ 2))
    (Metric.ball_mem_nhds t₀ hδpos) ?_ ?_ ?_ ?_ (hint.const_mul _) ?_
  · exact hderiv.2.differentiableAt.differentiableWithinAt
  · exact Eventually.of_forall fun t => (by unfold F; fun_prop : Continuous (F t)).aestronglyMeasurable
  · refine (hint.const_mul (1 / (2 * Real.pi ^ 2 * t₀.re ^ 2))).mono'
      (by unfold F; fun_prop : Continuous (F t₀)).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ici).mpr (Eventually.of_forall fun u hu => ?_))
    have hu_pos : 0 < u := lt_of_lt_of_le one_pos hu
    have hy : 0 < 2 * Real.pi * u * t₀.re := by positivity
    have hre : (-(2 * (Real.pi : ℂ) * (u : ℂ) * t₀)).re = -(2 * Real.pi * u * t₀.re) := by
      simp [mul_re]
    simp only [F]
    rw [Complex.norm_exp, hre]
    calc Real.exp (-(2 * Real.pi * u * t₀.re))
        ≤ 2 / (2 * Real.pi * u * t₀.re) ^ 2 := exp_neg_le_two_div_sq hy
      _ = (1 / (2 * Real.pi ^ 2 * t₀.re ^ 2)) * (1 / u ^ 2) := by field_simp
  · exact (by unfold F'; fun_prop : Continuous (F' t₀)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ici).mpr (Eventually.of_forall fun u hu t ht => ?_)
    have hu_pos : 0 < u := lt_of_lt_of_le one_pos hu
    have htre : δ < t.re := hball_re t ht
    have hy : 0 < 2 * Real.pi * u * δ := by positivity
    have hre : (-(2 * (Real.pi : ℂ) * (u : ℂ) * t)).re = -(2 * Real.pi * u * t.re) := by
      simp [mul_re]
    have hexp_le : Real.exp (-(2 * Real.pi * u * t.re)) ≤ Real.exp (-(2 * Real.pi * u * δ)) := by
      rw [Real.exp_le_exp, neg_le_neg_iff]
      gcongr
    simp only [F']
    rw [norm_mul, norm_neg, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
      abs_of_pos hu_pos, Complex.norm_exp, hre]
    calc 2 * Real.pi * u * Real.exp (-(2 * Real.pi * u * t.re))
        ≤ 2 * Real.pi * u * Real.exp (-(2 * Real.pi * u * δ)) :=
          mul_le_mul_of_nonneg_left hexp_le (by positivity)
      _ ≤ 2 * Real.pi * u * (27 / (2 * Real.pi * u * δ) ^ 3) :=
          mul_le_mul_of_nonneg_left (exp_neg_le_twentySeven_div_cube hy) (by positivity)
      _ = (27 / (4 * Real.pi ^ 2 * δ ^ 3)) * (1 / u ^ 2) := by field_simp; ring
  · refine (ae_restrict_iff' measurableSet_Ici).mpr (Eventually.of_forall fun u _ t _ => ?_)
    have hlin : HasDerivAt (fun z : ℂ => -(2 * (Real.pi : ℂ) * (u : ℂ) * z))
        (-(2 * (Real.pi : ℂ) * (u : ℂ) * 1)) t :=
      ((hasDerivAt_id t).const_mul (2 * (Real.pi : ℂ) * (u : ℂ))).neg
    refine (Complex.hasDerivAt_exp _ |>.comp t hlin).congr_deriv ?_
    simp only [F']
    ring

/-- **Complex Laplace identity on `Re t > 0` for `measureTheta`.** -/
theorem measureSeries_eq_of_measureTheta_relation (ν : Measure ℝ) [SFinite ν]
    (hint : IntegrableOn (fun u : ℝ => 1 / u ^ 2) (Ici 1) ν) {α β : ℂ}
    (htheta : ∀ x : ℝ, 0 < x →
      measureTheta ν x =
        (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ)))
    {t : ℂ} (ht : 0 < t.re) :
    measureSeries ν t = measureDual ν t + α / (Real.pi * t) + β := by
  set U : Set ℂ := {z : ℂ | 0 < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hf : AnalyticOnNhd ℂ (measureSeries ν) U :=
    (differentiableOn_measureSeries ν hint).analyticOnNhd hUo
  have hg : AnalyticOnNhd ℂ
      (fun z : ℂ => measureDual ν z + α / (Real.pi * z) + β) U := by
    refine DifferentiableOn.analyticOnNhd ?_ hUo
    refine ((differentiableOn_measureDual ν hint).add ?_).add (differentiableOn_const _)
    refine DifferentiableOn.div (differentiableOn_const _) (by fun_prop) fun z hz => ?_
    have hz' : 0 < z.re := hz
    refine mul_ne_zero (by exact_mod_cast Real.pi_ne_zero) fun h => ?_
    rw [h, zero_re] at hz'
    exact lt_irrefl _ hz'
  have h1U : (1 : ℂ) ∈ U := by simp [hU]
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ),
      measureSeries ν z = measureDual ν z + α / (Real.pi * z) + β := by
    set u : ℕ → ℂ := fun k => ((1 + 1 / ((k : ℝ) + 1) : ℝ) : ℂ) with hu
    have hlim : Tendsto u atTop (𝓝[≠] (1 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun k => ?_⟩
      · have h := (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (1 : ℝ)
        rw [add_zero] at h
        have h2 := (Complex.continuous_ofReal.tendsto 1).comp h
        rw [Complex.ofReal_one] at h2
        exact h2
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, hu]
        intro h
        have hr : (1 : ℝ) + 1 / ((k : ℝ) + 1) = 1 := by exact_mod_cast h
        have hp : 0 < 1 / ((k : ℝ) + 1) := by positivity
        linarith
    have hev : ∀ᶠ k : ℕ in atTop,
        measureSeries ν (u k) = measureDual ν (u k) + α / (Real.pi * u k) + β :=
      Eventually.of_forall fun k => by
        rw [hu]
        exact measureSeries_eq_of_measureTheta_relation_ofReal ν hint htheta
          (t := 1 + 1 / ((k : ℝ) + 1)) (by positivity)
    exact hlim.frequently hev.frequently
  have hconn : IsPreconnected U :=
    (convex_halfSpace_gt Complex.reCLM.isLinear 0).isPreconnected
  exact hf.eqOn_of_preconnected_of_frequently_eq hg hconn h1U hfreq ht

/-- **Fejér–tent spectral gap identity for `measureTheta`.**
For any s-finite Borel measure `ν` with `∫_{u ≥ 1} (1 / u²) dν(u) < ∞` satisfying Riemann's
self-dual theta relation, `α + β = 0` and `∫_{u ≥ 1} (sin(π u) / (π u))² dν(u) = 0`. -/
theorem integral_sin_sq_div_sq_eq_zero_of_measureTheta_relation (ν : Measure ℝ) [SFinite ν]
    (hint : IntegrableOn (fun u : ℝ => 1 / u ^ 2) (Ici 1) ν) {α β : ℂ}
    (htheta : ∀ x : ℝ, 0 < x →
      measureTheta ν x =
        (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ))) :
    α + β = 0 ∧
      (∫ u in Ici (1 : ℝ), (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 ∂ν) = 0 := by
  have hαβ := add_eq_zero_of_self_dual_theta htheta
  refine ⟨hαβ, ?_⟩
  set μ₁ : Measure ℝ := ν.restrict (Ici 1)
  set IL : ℝ → ℂ := fun ε =>
    ∫ u, ((∫ τ in (0 : ℝ)..1, tentSeriesKernel u ε τ : ℝ) : ℂ) ∂μ₁
  set ID : ℝ → ℂ := fun ε =>
    ∫ u, ((∫ τ in (0 : ℝ)..1, tentDualKernel u ε τ : ℝ) : ℂ) ∂μ₁
  set IP : ℝ → ℂ := fun ε =>
    α * ((∫ τ in (0 : ℝ)..1, tentPoleKernel ε τ : ℝ) : ℂ) + β
  -- Limit `IL ε → 0` as `ε → 0⁺`
  have hIL_lim : Tendsto IL (𝓝[>] 0) (𝓝 0) := by
    have hz : (∫ _u : ℝ, (0 : ℂ) ∂μ₁) = 0 := by simp
    simp only [IL]
    rw [← hz]
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun u => (5 / Real.pi) * (1 / u ^ 2)) ?_ ?_ (hint.const_mul _) ?_
    · filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
      have hε0 : 0 < ε := hε.1
      have hcont : Continuous fun u : ℝ =>
          ((∫ τ in (0 : ℝ)..1, tentSeriesKernel u ε τ : ℝ) : ℂ) := by
        refine Complex.continuous_ofReal.comp ?_
        rw [continuous_iff_continuousAt]
        intro u₀
        have hc : Continuous (Function.uncurry fun u τ : ℝ => tentSeriesKernel u ε τ) := by
          unfold tentSeriesKernel Function.uncurry
          refine (((continuous_const.sub continuous_snd).mul continuous_const).mul ?_)
          exact (continuous_const.div (by fun_prop) fun p => by
              nlinarith [sq_pos_of_ne_zero hε0.ne', sq_nonneg (p.1 - p.2)]).add
            (continuous_const.div (by fun_prop) fun p => by
              nlinarith [sq_pos_of_ne_zero hε0.ne', sq_nonneg (p.1 + p.2)])
        simp_rw [intervalIntegral.integral_of_le zero_le_one]
        have hM : ∀ u ∈ Metric.ball u₀ 1, ∀ τ : ℝ, |tentSeriesKernel u ε τ| ≤
            (2 / (Real.pi * ε)) * (|1 - τ| + 1) := by
          intro u _ τ
          unfold tentSeriesKernel
          have hd1 : ε / (ε ^ 2 + (u - τ) ^ 2) ≤ 1 / ε := by
            rw [div_le_div_iff₀ (by nlinarith [sq_pos_of_ne_zero hε0.ne', sq_nonneg (u - τ)]) hε0]
            nlinarith [sq_nonneg (u - τ)]
          have hd2 : ε / (ε ^ 2 + (u + τ) ^ 2) ≤ 1 / ε := by
            rw [div_le_div_iff₀ (by nlinarith [sq_pos_of_ne_zero hε0.ne', sq_nonneg (u + τ)]) hε0]
            nlinarith [sq_nonneg (u + τ)]
          have hsum_pos : 0 ≤ ε / (ε ^ 2 + (u - τ) ^ 2) + ε / (ε ^ 2 + (u + τ) ^ 2) := by
            positivity
          rw [abs_mul, abs_mul, abs_of_pos (by positivity : 0 < 1 / Real.pi), abs_of_nonneg hsum_pos]
          calc |1 - τ| * (1 / Real.pi) *
                (ε / (ε ^ 2 + (u - τ) ^ 2) + ε / (ε ^ 2 + (u + τ) ^ 2))
              ≤ |1 - τ| * (1 / Real.pi) * (1 / ε + 1 / ε) :=
                mul_le_mul_of_nonneg_left (add_le_add hd1 hd2) (by positivity)
            _ = (2 / (Real.pi * ε)) * |1 - τ| := by ring
            _ ≤ (2 / (Real.pi * ε)) * (|1 - τ| + 1) :=
                mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        exact continuousAt_of_dominated (bound := fun τ => (2 / (Real.pi * ε)) * (|1 - τ| + 1))
          (Eventually.of_forall fun u =>
            (continuous_tentSeriesKernel_tau u hε0.ne').aestronglyMeasurable.restrict)
          (by filter_upwards [Metric.ball_mem_nhds u₀ one_pos] with u hu
              exact Eventually.of_forall fun τ => by
                rw [Real.norm_eq_abs]; exact hM u hu τ)
          ((Continuous.integrableOn_Ioc (by fun_prop)))
          (Eventually.of_forall fun τ => (hc.comp (continuous_id.prodMk continuous_const)).continuousAt)
      exact hcont.aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
      refine (ae_restrict_iff' measurableSet_Ici).mpr (Eventually.of_forall fun u hu => ?_)
      have hnn : 0 ≤ ∫ τ in (0 : ℝ)..1, tentSeriesKernel u ε τ :=
        intervalIntegral.integral_nonneg zero_le_one fun τ hτ =>
          (tentSeriesKernel_nonneg_and_le hu hε.1 hε.2.le hτ.1 hτ.2).1
      have hle : (∫ τ in (0 : ℝ)..1, tentSeriesKernel u ε τ) ≤ (5 / Real.pi) * (1 / u ^ 2) := by
        calc (∫ τ in (0 : ℝ)..1, tentSeriesKernel u ε τ)
            ≤ ∫ _τ in (0 : ℝ)..1, (5 / Real.pi) / u ^ 2 :=
              intervalIntegral.integral_mono_on zero_le_one
                ((continuous_tentSeriesKernel_tau u hε.1.ne').intervalIntegrable 0 1)
                intervalIntegrable_const
                fun τ hτ => (tentSeriesKernel_nonneg_and_le hu hε.1 hε.2.le hτ.1 hτ.2).2
          _ = (5 / Real.pi) * (1 / u ^ 2) := by simp [div_eq_mul_inv, mul_assoc]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
      exact hle
    · refine (ae_restrict_iff' measurableSet_Ici).mpr (Eventually.of_forall fun u hu => ?_)
      have h0_c : (0 : ℂ) = ((0 : ℝ) : ℂ) := Complex.ofReal_zero.symm
      rw [h0_c]
      exact (Complex.continuous_ofReal.tendsto 0).comp (tendsto_integral_tentSeriesKernel hu)
  -- Limit `ID ε + IP ε → ∫ (sin(π u)/(π u))² dν + (α + β)` as `ε → 0⁺`
  have hID_lim : Tendsto ID (𝓝[>] 0)
      (𝓝 (∫ u, (((Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 : ℝ) : ℂ) ∂μ₁)) := by
    simp only [ID]
    refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
      (fun u => (1 / Real.pi ^ 2) * (1 / u ^ 2)) ?_ ?_ (hint.const_mul _) ?_
    · filter_upwards [Ioo_mem_nhdsGT one_pos] with ε _
      refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ici
      intro u hu
      have hval : ∀ v ∈ Ici (1 : ℝ),
          ((∫ τ in (0 : ℝ)..1, tentDualKernel v ε τ : ℝ) : ℂ) =
            ((Real.exp (-(2 * Real.pi * v * ε)) *
              (Real.sin (Real.pi * v) / (Real.pi * v)) ^ 2 : ℝ) : ℂ) :=
        fun v hv => congrArg Complex.ofReal (integral_tentDualKernel hv ε)
      refine ContinuousWithinAt.congr ?_ hval (hval u hu)
      have hu0 : (Real.pi * u) ≠ 0 := (mul_pos Real.pi_pos (lt_of_lt_of_le one_pos hu)).ne'
      have hc_at : ContinuousAt (fun v : ℝ => Real.exp (-(2 * Real.pi * v * ε)) *
          (Real.sin (Real.pi * v) / (Real.pi * v)) ^ 2) u :=
        (by fun_prop : Continuous fun v : ℝ => Real.exp (-(2 * Real.pi * v * ε))).continuousAt.mul
          (((by fun_prop : Continuous fun v : ℝ => Real.sin (Real.pi * v)).continuousAt.div
            (by fun_prop : Continuous fun v : ℝ => Real.pi * v).continuousAt hu0).pow 2)
      exact (Complex.continuous_ofReal.continuousAt.comp hc_at).continuousWithinAt
    · filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
      refine (ae_restrict_iff' measurableSet_Ici).mpr (Eventually.of_forall fun u hu => ?_)
      rw [Complex.norm_real, Real.norm_eq_abs]
      calc |∫ τ in (0 : ℝ)..1, tentDualKernel u ε τ|
          ≤ 1 / (Real.pi ^ 2 * u ^ 2) := abs_integral_tentDualKernel_le hu hε.1
        _ = (1 / Real.pi ^ 2) * (1 / u ^ 2) := by ring
    · refine (ae_restrict_iff' measurableSet_Ici).mpr (Eventually.of_forall fun u hu => ?_)
      exact (Complex.continuous_ofReal.tendsto _).comp (tendsto_integral_tentDualKernel hu)
  have hIP_lim : Tendsto IP (𝓝[>] 0) (𝓝 (α + β)) := by
    have hp := (Complex.continuous_ofReal.tendsto 1).comp tendsto_integral_tentPoleKernel
    simpa [IP] using (hp.const_mul α).add_const β
  -- For every `ε ∈ (0, 1)`, Fubini's theorem equates `IL ε = ID ε + IP ε`
  have hILIReq : IL =ᶠ[𝓝[>] 0] fun ε => ID ε + IP ε := by
    filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
    have hε0 : 0 < ε := hε.1
    have hε1 : ε ≤ 1 := hε.2.le
    have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    -- Fubini swap for `IL ε`
    have hswapL : IL ε = ∫ τ in (0 : ℝ)..1,
        ((1 - τ : ℝ) : ℂ) *
          (measureSeries ν ((ε : ℂ) + (τ : ℂ) * I) +
           measureSeries ν ((ε : ℂ) - (τ : ℂ) * I)) := by
      have hintL_prod : Integrable
          (Function.uncurry fun τ u : ℝ => ((tentSeriesKernel u ε τ : ℝ) : ℂ))
          ((volume.restrict (uIoc 0 1)).prod μ₁) := by
        have hc1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (uIoc 0 1) volume :=
          integrableOn_const (by rw [uIoc_of_le zero_le_one, Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
        have hdom := hc1.mul_prod (hint.const_mul (5 / Real.pi))
        refine hdom.mono' ?_ ?_
        · refine (Complex.continuous_ofReal.comp ?_).aestronglyMeasurable
          simp only [tentSeriesKernel]
          refine (((continuous_const.sub continuous_fst).mul continuous_const).mul ?_)
          exact (continuous_const.div (by fun_prop) fun p => by
              nlinarith [sq_pos_of_ne_zero hε0.ne', sq_nonneg (p.2 - p.1)]).add
            (continuous_const.div (by fun_prop) fun p => by
              nlinarith [sq_pos_of_ne_zero hε0.ne', sq_nonneg (p.2 + p.1)])
        · rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_uIoc.prod measurableSet_Ici)]
          refine Eventually.of_forall fun p hp => ?_
          have hτ : p.1 ∈ Ioc (0 : ℝ) 1 := by simpa [uIoc_of_le zero_le_one] using hp.1
          have hb := tentSeriesKernel_nonneg_and_le hp.2 hε0 hε1 hτ.1.le hτ.2
          simp only [Function.uncurry, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1,
            one_mul]
          calc tentSeriesKernel p.2 ε p.1 ≤ (5 / Real.pi) / p.2 ^ 2 := hb.2
            _ = (5 / Real.pi) * (1 / p.2 ^ 2) := by ring
      have hsw := (intervalIntegral_integral_swap hintL_prod).symm
      have hIL_rew : IL ε = ∫ u, (∫ τ in (0 : ℝ)..1, ((tentSeriesKernel u ε τ : ℝ) : ℂ)) ∂μ₁ := by
        simp only [IL]
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        dsimp only
        exact (intervalIntegral.integral_ofReal).symm
      rw [hIL_rew, hsw]
      refine intervalIntegral.integral_congr fun τ hτ => ?_
      rw [uIcc_of_le zero_le_one] at hτ
      have hsum_sign : ∀ σ : ℝ, |σ| ≤ 1 → Integrable
          (fun u : ℝ => ((ε : ℂ) + (σ : ℂ) * I) /
            ((Real.pi : ℂ) * ((u : ℂ) ^ 2 + ((ε : ℂ) + (σ : ℂ) * I) ^ 2))) μ₁ := by
        intro σ hσ
        set c₀ : ℝ := min (1 / 2) (ε ^ 2 / 4)
        have hc₀ : 0 < c₀ := lt_min (by norm_num) (by positivity)
        have hden_ne : ∀ u : ℝ, (u : ℂ) ^ 2 + ((ε : ℂ) + (σ : ℂ) * I) ^ 2 ≠ 0 := by
          intro u hz
          have hfac : (u : ℂ) ^ 2 + ((ε : ℂ) + (σ : ℂ) * I) ^ 2 =
              ((ε : ℂ) + ((σ - u : ℝ) : ℂ) * I) * ((ε : ℂ) + ((σ + u : ℝ) : ℂ) * I) := by
            push_cast; ring_nf; rw [Complex.I_sq]; ring
          rw [hfac, mul_eq_zero] at hz
          rcases hz with h1 | h2
          · have := congrArg Complex.re h1; simp at this; linarith
          · have := congrArg Complex.re h2; simp at this; linarith
        refine (hint.const_mul (2 / (Real.pi * c₀))).mono'
          (continuous_const.div
            (continuous_const.mul ((Complex.continuous_ofReal.pow 2).add continuous_const))
            fun u => mul_ne_zero hπ (hden_ne u)).aestronglyMeasurable
          ((ae_restrict_iff' measurableSet_Ici).mpr (Eventually.of_forall fun u hu => ?_))
        have hden := norm_sq_add_vertical_sq_ge hu hε0 hε1 hσ
        have hu_pos : 0 < u := lt_of_lt_of_le one_pos hu
        have htop : ‖(ε : ℂ) + (σ : ℂ) * I‖ ≤ 2 := by
          refine (norm_add_le _ _).trans ?_
          simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_I, mul_one,
            abs_of_pos hε0]
          linarith
        rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
          div_le_iff₀ (mul_pos Real.pi_pos (lt_of_lt_of_le (by positivity : 0 < c₀ * u ^ 2) hden))]
        calc ‖(ε : ℂ) + (σ : ℂ) * I‖ ≤ 2 := htop
          _ = (2 / (Real.pi * c₀)) * (1 / u ^ 2) * (Real.pi * (c₀ * u ^ 2)) := by field_simp
          _ ≤ (2 / (Real.pi * c₀)) * (1 / u ^ 2) *
                (Real.pi * ‖(u : ℂ) ^ 2 + ((ε : ℂ) + (σ : ℂ) * I) ^ 2‖) := by gcongr
      have hs1 := hsum_sign τ (by rw [abs_of_nonneg hτ.1]; exact hτ.2)
      have hs2 : Integrable (fun u : ℝ => ((ε : ℂ) - (τ : ℂ) * I) /
          ((Real.pi : ℂ) * ((u : ℂ) ^ 2 + ((ε : ℂ) - (τ : ℂ) * I) ^ 2))) μ₁ := by
        simpa [sub_eq_add_neg] using hsum_sign (-τ)
          (by rw [abs_neg, abs_of_nonneg hτ.1]; exact hτ.2)
      rw [measureSeries, measureSeries, ← integral_add hs1 hs2, ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ici fun u _ => ?_
      rw [partialFraction_conj_pair (l := u) (τ := τ) hε0]
      unfold tentSeriesKernel
      push_cast
      ring
    -- Fubini swap for `ID ε`
    have hswapD : ID ε = ∫ τ in (0 : ℝ)..1,
        ((1 - τ : ℝ) : ℂ) *
          (measureDual ν ((ε : ℂ) + (τ : ℂ) * I) +
           measureDual ν ((ε : ℂ) - (τ : ℂ) * I)) := by
      have hintD_prod : Integrable
          (Function.uncurry fun τ u : ℝ => ((tentDualKernel u ε τ : ℝ) : ℂ))
          ((volume.restrict (uIoc 0 1)).prod μ₁) := by
        have hc1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (uIoc 0 1) volume :=
          integrableOn_const (by rw [uIoc_of_le zero_le_one, Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
        have hdom := hc1.mul_prod (hint.const_mul (1 / (Real.pi ^ 2 * ε ^ 2)))
        refine hdom.mono' ?_ ?_
        · unfold tentDualKernel Function.uncurry
          fun_prop
        · rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_uIoc.prod measurableSet_Ici)]
          refine Eventually.of_forall fun p hp => ?_
          have hτ : p.1 ∈ Ioc (0 : ℝ) 1 := by simpa [uIoc_of_le zero_le_one] using hp.1
          have hu_pos : 0 < p.2 := lt_of_lt_of_le one_pos hp.2
          have hy : 0 < 2 * Real.pi * p.2 * ε := by positivity
          have h1τ : |1 - p.1| ≤ 1 := by rw [abs_of_nonneg (by linarith [hτ.2])]; linarith [hτ.1]
          have hcos : |Real.cos (2 * Real.pi * p.2 * p.1)| ≤ 1 := Real.abs_cos_le_one _
          simp only [Function.uncurry, Complex.norm_real, Real.norm_eq_abs, one_mul]
          have hker : |tentDualKernel p.2 ε p.1| ≤ 2 * Real.exp (-(2 * Real.pi * p.2 * ε)) := by
            unfold tentDualKernel
            rw [abs_mul, abs_mul,
              abs_of_pos (by positivity : 0 < 2 * Real.exp (-(2 * Real.pi * p.2 * ε)))]
            calc |1 - p.1| * (2 * Real.exp (-(2 * Real.pi * p.2 * ε)) *
                  |Real.cos (2 * Real.pi * p.2 * p.1)|)
                ≤ 1 * (2 * Real.exp (-(2 * Real.pi * p.2 * ε)) * 1) := by gcongr
              _ = 2 * Real.exp (-(2 * Real.pi * p.2 * ε)) := by ring
          calc |tentDualKernel p.2 ε p.1|
              ≤ 2 * Real.exp (-(2 * Real.pi * p.2 * ε)) := hker
            _ ≤ 2 * (2 / (2 * Real.pi * p.2 * ε) ^ 2) :=
                mul_le_mul_of_nonneg_left (exp_neg_le_two_div_sq hy) zero_le_two
            _ = (1 / (Real.pi ^ 2 * ε ^ 2)) * (1 / p.2 ^ 2) := by field_simp
      have hsw := (intervalIntegral_integral_swap hintD_prod).symm
      have hID_rew : ID ε = ∫ u, (∫ τ in (0 : ℝ)..1, ((tentDualKernel u ε τ : ℝ) : ℂ)) ∂μ₁ := by
        simp only [ID]
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        dsimp only
        exact (intervalIntegral.integral_ofReal).symm
      rw [hID_rew, hsw]
      refine intervalIntegral.integral_congr fun τ _ => ?_
      have hsum_exp : ∀ σ : ℝ, Integrable
          (fun u : ℝ => cexp (-(2 * Real.pi * (u : ℂ) * ((ε : ℂ) + (σ : ℂ) * I)))) μ₁ := by
        intro σ
        refine (hint.const_mul (1 / (2 * Real.pi ^ 2 * ε ^ 2))).mono'
          (by fun_prop : Continuous fun u : ℝ =>
            cexp (-(2 * Real.pi * (u : ℂ) * ((ε : ℂ) + (σ : ℂ) * I)))).aestronglyMeasurable
          ((ae_restrict_iff' measurableSet_Ici).mpr (Eventually.of_forall fun u hu => ?_))
        have hu_pos : 0 < u := lt_of_lt_of_le one_pos hu
        have hy : 0 < 2 * Real.pi * u * ε := by positivity
        have hre : (-(2 * (Real.pi : ℂ) * (u : ℂ) * ((ε : ℂ) + (σ : ℂ) * I))).re =
            -(2 * Real.pi * u * ε) := by simp [mul_re]
        rw [Complex.norm_exp, hre]
        calc Real.exp (-(2 * Real.pi * u * ε))
            ≤ 2 / (2 * Real.pi * u * ε) ^ 2 := exp_neg_le_two_div_sq hy
          _ = (1 / (Real.pi ^ 2 * ε ^ 2 * 2)) * (1 / u ^ 2) := by field_simp
          _ = (1 / (2 * Real.pi ^ 2 * ε ^ 2)) * (1 / u ^ 2) := by ring
      have hd1 := hsum_exp τ
      have hd2 : Integrable
          (fun u : ℝ => cexp (-(2 * Real.pi * (u : ℂ) * ((ε : ℂ) - (τ : ℂ) * I)))) μ₁ := by
        simpa [sub_eq_add_neg] using hsum_exp (-τ)
      rw [measureDual, measureDual, ← integral_add hd1 hd2, ← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ici fun u _ => ?_
      rw [exp_conj_pair u ε τ]
      unfold tentDualKernel
      push_cast
      ring
    -- Pointwise Laplace identity on `[0, 1]`
    have hpt : ∀ τ : ℝ,
        ((1 - τ : ℝ) : ℂ) *
          (measureSeries ν ((ε : ℂ) + (τ : ℂ) * I) +
           measureSeries ν ((ε : ℂ) - (τ : ℂ) * I)) =
        ((1 - τ : ℝ) : ℂ) *
          (measureDual ν ((ε : ℂ) + (τ : ℂ) * I) +
           measureDual ν ((ε : ℂ) - (τ : ℂ) * I)) +
        α * ((tentPoleKernel ε τ : ℝ) : ℂ) +
        ((2 * (1 - τ) : ℝ) : ℂ) * β := by
      intro τ
      have hre1 : 0 < ((ε : ℂ) + (τ : ℂ) * I).re := by simp [hε0]
      have hre2 : 0 < ((ε : ℂ) - (τ : ℂ) * I).re := by simp [hε0]
      rw [measureSeries_eq_of_measureTheta_relation ν hint htheta hre1,
        measureSeries_eq_of_measureTheta_relation ν hint htheta hre2]
      have hcauchy :
          ((1 - τ : ℝ) : ℂ) *
            (α / ((Real.pi : ℂ) * ((ε : ℂ) + (τ : ℂ) * I)) +
             α / ((Real.pi : ℂ) * ((ε : ℂ) - (τ : ℂ) * I))) =
          (α / (Real.pi : ℂ)) * ((1 - τ : ℝ) : ℂ) *
            (1 / ((ε : ℂ) + (τ : ℂ) * I) + 1 / ((ε : ℂ) - (τ : ℂ) * I)) := by
        simp only [div_mul_eq_div_div]
        ring
      have hgrp :
          ((1 - τ : ℝ) : ℂ) *
            ((measureDual ν ((ε : ℂ) + (τ : ℂ) * I) +
                α / ((Real.pi : ℂ) * ((ε : ℂ) + (τ : ℂ) * I)) + β) +
             (measureDual ν ((ε : ℂ) - (τ : ℂ) * I) +
                α / ((Real.pi : ℂ) * ((ε : ℂ) - (τ : ℂ) * I)) + β)) =
          ((1 - τ : ℝ) : ℂ) *
            (measureDual ν ((ε : ℂ) + (τ : ℂ) * I) +
             measureDual ν ((ε : ℂ) - (τ : ℂ) * I)) +
          ((1 - τ : ℝ) : ℂ) *
            (α / ((Real.pi : ℂ) * ((ε : ℂ) + (τ : ℂ) * I)) +
             α / ((Real.pi : ℂ) * ((ε : ℂ) - (τ : ℂ) * I))) +
          ((2 * (1 - τ) : ℝ) : ℂ) * β := by
        push_cast
        ring
      rw [hgrp, hcauchy, inv_add_mul_I_add_inv_sub_mul_I hε0 τ]
      unfold tentPoleKernel
      push_cast
      field_simp [hπ]
    have hcD := (differentiableOn_measureDual ν hint).continuousOn
    have hintD_tau : IntervalIntegrable
        (fun τ : ℝ => ((1 - τ : ℝ) : ℂ) *
          (measureDual ν ((ε : ℂ) + (τ : ℂ) * I) +
           measureDual ν ((ε : ℂ) - (τ : ℂ) * I))) volume 0 1 := by
      refine Continuous.intervalIntegrable ?_ 0 1
      have hc1 : Continuous fun τ : ℝ => measureDual ν ((ε : ℂ) + (τ : ℂ) * I) :=
        hcD.comp_continuous (by fun_prop) fun τ => by simp [hε0]
      have hc2 : Continuous fun τ : ℝ => measureDual ν ((ε : ℂ) - (τ : ℂ) * I) :=
        hcD.comp_continuous (by fun_prop) fun τ => by simp [hε0]
      exact (by fun_prop : Continuous fun τ : ℝ => ((1 - τ : ℝ) : ℂ)).mul (hc1.add hc2)
    have hintP_tau : IntervalIntegrable
        (fun τ : ℝ => α * ((tentPoleKernel ε τ : ℝ) : ℂ)) volume 0 1 := by
      refine Continuous.intervalIntegrable ?_ 0 1
      unfold tentPoleKernel
      refine continuous_const.mul (Complex.continuous_ofReal.comp ?_)
      exact ((continuous_const.sub continuous_id).mul continuous_const).mul
        (continuous_const.div (by fun_prop) fun τ => by nlinarith [sq_nonneg τ])
    have hintB_tau : IntervalIntegrable
        (fun τ : ℝ => ((2 * (1 - τ) : ℝ) : ℂ) * β) volume 0 1 :=
      Continuous.intervalIntegrable (by fun_prop) 0 1
    have hβ_int : (∫ τ in (0 : ℝ)..1, ((2 * (1 - τ) : ℝ) : ℂ) * β) = β := by
      have hd : ∀ τ : ℝ, HasDerivAt (fun x : ℝ => 2 * x - x ^ 2) (2 * (1 - τ)) τ := by
        intro τ
        have h1 : HasDerivAt (fun x : ℝ => 2 * x) (2 * 1) τ := (hasDerivAt_id τ).const_mul 2
        have h2 : HasDerivAt (fun x : ℝ => x ^ 2) ((2 : ℕ) * τ ^ (2 - 1)) τ := hasDerivAt_pow 2 τ
        exact (h1.sub h2).congr_deriv (by norm_num; ring)
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun τ _ => hd τ)
        (Continuous.intervalIntegrable (by fun_prop) 0 1)
      rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal, hftc]
      norm_num
    rw [hswapL, intervalIntegral.integral_congr fun τ _ => hpt τ,
      intervalIntegral.integral_add (hintD_tau.add hintP_tau) hintB_tau,
      intervalIntegral.integral_add hintD_tau hintP_tau, ← hswapD,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal, hβ_int]
    simp only [IP]
    ring
  have heq_lim := tendsto_nhds_unique (hIL_lim.congr' hILIReq) (hID_lim.add hIP_lim)
  rw [hαβ, add_zero] at heq_lim
  have hcast : (((∫ u in Ici (1 : ℝ),
      (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 ∂ν) : ℝ) : ℂ) = 0 := by
    rw [integral_complex_ofReal] at heq_lim
    exact heq_lim.symm
  exact_mod_cast hcast

/-- **Borel measure rigidity of Riemann's functional equation on `[1, ∞)`.**
Let `ν` be an s-finite nonnegative Borel measure on `ℝ` supported on `[1, ∞)` (`ν (Iio 1) = 0`)
with `∫_{u ≥ 1} (1 / u²) dν(u) < ∞` whose theta integral satisfies
`θ_ν(x) = x^{-1/2} θ_ν(1/x) + α + β x^{-1/2}` for all `x > 0`. Then:
1. `α + β = 0`;
2. `ν` vanishes outside `ℕ₊ = {1, 2, 3, ...}` (`ν ((range (m ↦ m + 1))ᶜ) = 0`);
3. `ν = Σ_{m ≥ 0} ν {m + 1} • δ_{m + 1}` with uniform finite atom mass `ν.real {m + 1} = -2 Re α`
   (`((ν.real {m + 1} : ℝ) : ℂ) = -(2 * α)`) for every `m : ℕ`;
4. if `ν.real {1} = 1`, then `α = -1/2`, `β = 1/2`, and `ν = Σ_{m ≥ 0} δ_{m + 1}` is the exact
   counting measure on the positive integers. -/
theorem measure_eq_sum_nat_pos_dirac_of_measureTheta_relation (ν : Measure ℝ) [SFinite ν]
    (hsupp : ν (Iio 1) = 0)
    (hint : IntegrableOn (fun u : ℝ => 1 / u ^ 2) (Ici 1) ν) {α β : ℂ}
    (htheta : ∀ x : ℝ, 0 < x →
      measureTheta ν x =
        (x : ℂ) ^ (-(1 / 2 : ℂ)) * measureTheta ν x⁻¹ + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ))) :
    α + β = 0 ∧
      ν ((Set.range (fun m : ℕ => ((m + 1 : ℕ) : ℝ)))ᶜ) = 0 ∧
      ν = Measure.sum (fun m : ℕ => ν {((m + 1 : ℕ) : ℝ)} • Measure.dirac ((m + 1 : ℕ) : ℝ)) ∧
      (∀ m : ℕ, ((ν.real {((m + 1 : ℕ) : ℝ)} : ℝ) : ℂ) = -(2 * α)) ∧
      (ν.real {(1 : ℝ)} = 1 →
        α = -(1 / 2 : ℂ) ∧ β = (1 / 2 : ℂ) ∧
          ν = Measure.sum (fun m : ℕ => Measure.dirac ((m + 1 : ℕ) : ℝ))) := by
  obtain ⟨hαβ, hgap⟩ := integral_sin_sq_div_sq_eq_zero_of_measureTheta_relation ν hint htheta
  -- Integrability of `(sin(π u)/(π u))²` on `Ici 1`
  have hint_sin : IntegrableOn (fun u : ℝ => (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2)
      (Ici 1) ν := by
    refine (hint.const_mul (1 / Real.pi ^ 2)).mono' ?_
      ((ae_restrict_iff' measurableSet_Ici).mpr (Eventually.of_forall fun u hu => ?_))
    · refine ContinuousOn.aestronglyMeasurable (fun u hu => ?_) measurableSet_Ici
      have hu0 : (Real.pi * u) ≠ 0 := (mul_pos Real.pi_pos (lt_of_lt_of_le one_pos hu)).ne'
      exact (((by fun_prop : Continuous fun v : ℝ => Real.sin (Real.pi * v)).continuousAt.div
        (by fun_prop : Continuous fun v : ℝ => Real.pi * v).continuousAt hu0).pow 2
        ).continuousWithinAt
    · have hsin : Real.sin (Real.pi * u) ^ 2 ≤ 1 := by
        have hb := abs_le.mp (Real.abs_sin_le_one (Real.pi * u))
        nlinarith
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      calc (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2
          = Real.sin (Real.pi * u) ^ 2 / (Real.pi ^ 2 * u ^ 2) := by ring
        _ ≤ 1 / (Real.pi ^ 2 * u ^ 2) := by gcongr
        _ = (1 / Real.pi ^ 2) * (1 / u ^ 2) := by ring
  -- Vanishing of the nonnegative integral forces `u ∈ ℕ₊` `ν`-a.e.
  have hae_sin : ∀ᵐ u ∂(ν.restrict (Ici 1)),
      (Real.sin (Real.pi * u) / (Real.pi * u)) ^ 2 = 0 :=
    (MeasureTheory.integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hint_sin).mp hgap
  rw [ae_restrict_iff' measurableSet_Ici] at hae_sin
  have hae_ge1 : ∀ᵐ u ∂ν, 1 ≤ u := by
    rw [ae_iff]
    have hset_eq : {u : ℝ | ¬ 1 ≤ u} = Iio 1 := by ext u; simp
    rwa [hset_eq]
  have hae_nat : ∀ᵐ u ∂ν, u ∈ Set.range (fun m : ℕ => ((m + 1 : ℕ) : ℝ)) := by
    filter_upwards [hae_ge1, hae_sin] with u hu1 hsin0
    have h0 := hsin0 hu1
    have hdiv0 : Real.sin (Real.pi * u) / (Real.pi * u) = 0 := sq_eq_zero_iff.mp h0
    have hu_pos : 0 < u := lt_of_lt_of_le one_pos hu1
    have hπu : Real.pi * u ≠ 0 := (mul_pos Real.pi_pos hu_pos).ne'
    have hs : Real.sin (Real.pi * u) = 0 := (div_eq_zero_iff.mp hdiv0).resolve_right hπu
    obtain ⟨z, hz⟩ := Real.sin_eq_zero_iff.mp hs
    have huz : u = (z : ℝ) := mul_left_cancel₀ Real.pi_ne_zero (by linarith)
    have hz1 : (1 : ℤ) ≤ z := by
      have : (1 : ℝ) ≤ (z : ℝ) := huz ▸ hu1
      exact_mod_cast this
    refine ⟨z.toNat - 1, ?_⟩
    have hzn : ((z.toNat : ℕ) : ℤ) = z := Int.toNat_of_nonneg (by omega)
    have h1n : 1 ≤ z.toNat := by omega
    have hsub : z.toNat - 1 + 1 = z.toNat := Nat.sub_add_cancel h1n
    dsimp only
    rw [hsub, huz, ← hzn]
    norm_cast
  have hnull_compl : ν ((Set.range (fun m : ℕ => ((m + 1 : ℕ) : ℝ)))ᶜ) = 0 := by
    rwa [ae_iff] at hae_nat
  -- Atomic decomposition `ν = Σ_{m ≥ 0} ν {m + 1} • δ_{m + 1}`
  have hν_sum :
      ν = Measure.sum (fun m : ℕ => ν {((m + 1 : ℕ) : ℝ)} • Measure.dirac ((m + 1 : ℕ) : ℝ)) := by
    have hset : Set.range (fun m : ℕ => ((m + 1 : ℕ) : ℝ)) =
        ⋃ m : ℕ, {(((m + 1 : ℕ) : ℝ))} := by
      ext x; simp
    have hdisj : Pairwise
        (Function.onFun Disjoint (fun m : ℕ => ({((m + 1 : ℕ) : ℝ)} : Set ℝ))) := by
      intro i j hij
      rw [Function.onFun, Set.disjoint_singleton]
      intro heq
      have hnat : i + 1 = j + 1 := by exact_mod_cast heq
      omega
    calc ν = ν.restrict (Set.range (fun m : ℕ => ((m + 1 : ℕ) : ℝ))) :=
          (Measure.restrict_eq_self_of_ae_mem hae_nat).symm
      _ = Measure.sum (fun m : ℕ => ν.restrict {((m + 1 : ℕ) : ℝ)}) := by
          rw [hset, Measure.restrict_iUnion hdisj (fun m => measurableSet_singleton _)]
      _ = Measure.sum (fun m : ℕ => ν {((m + 1 : ℕ) : ℝ)} • Measure.dirac ((m + 1 : ℕ) : ℝ)) := by
          simp_rw [Measure.restrict_singleton]
  -- Finiteness of every singleton mass `ν {m + 1} < ⊤` from `hint`
  have hfin_atom : ∀ m : ℕ, ν {((m + 1 : ℕ) : ℝ)} ≠ ⊤ := by
    intro m
    have hsub : ({((m + 1 : ℕ) : ℝ)} : Set ℝ) ⊆ Ici 1 := by
      rw [Set.singleton_subset_iff, mem_Ici]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
    have hsing := hint.mono_set hsub
    rw [integrableOn_singleton_iff] at hsing
    rcases hsing with h0 | hlt
    · exfalso
      have hpos : (0 : ℝ) < 1 / ((m + 1 : ℕ) : ℝ) ^ 2 := by positivity
      rw [enorm_eq_zero] at h0
      exact hpos.ne' h0
    · exact hlt.ne
  -- Reduce `measureTheta ν` to `coeffTheta`
  have hrest_eq : ν.restrict (Ici 1) = ν :=
    Measure.restrict_eq_self_of_ae_mem hae_ge1
  set c : ℕ → ℂ := fun k => if k = 0 then 0 else ((ν.real {(k : ℝ)} : ℝ) : ℂ) with hc_def
  have hsum_c : Summable fun m : ℕ => ‖c (m + 1)‖ / ((m : ℝ) + 1) ^ (2 : ℝ) := by
    have hint_full : Integrable (fun u : ℝ => 1 / u ^ 2)
        (Measure.sum (fun m : ℕ => ν {((m + 1 : ℕ) : ℝ)} • Measure.dirac ((m + 1 : ℕ) : ℝ))) := by
      rw [← hν_sum, ← hrest_eq]
      exact hint
    have hdirac := hint_full.summable_of_dirac
    refine hdirac.congr fun m => ?_
    have hnn : 0 ≤ (ν {((m + 1 : ℕ) : ℝ)}).toReal := ENNReal.toReal_nonneg
    have hpos : 0 < 1 / ((m + 1 : ℕ) : ℝ) ^ 2 := by positivity
    have hrpow2 : ((m : ℝ) + 1) ^ (2 : ℝ) = ((m + 1 : ℕ) : ℝ) ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      push_cast; ring
    rw [hrpow2]
    simp only [hc_def, Nat.succ_ne_zero, ↓reduceIte, Complex.norm_real, Real.norm_eq_abs,
      measureReal_def]
    rw [abs_of_nonneg hnn, abs_of_pos hpos]
    ring
  have hθ_eq : ∀ x : ℝ, measureTheta ν x = coeffTheta c x := by
    intro x
    unfold measureTheta coeffTheta
    rw [hrest_eq]
    conv_lhs => rw [hν_sum]
    rw [MeasureTheory.integral_sum_dirac hfin_atom]
    refine tsum_congr fun m => ?_
    simp only [hc_def, Nat.succ_ne_zero, ↓reduceIte, measureReal_def, Complex.real_smul]
    push_cast
    rfl
  have hc_rel : ∀ x : ℝ, 0 < x →
      coeffTheta c x =
        (1 : ℂ) * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta c x⁻¹) + α +
          β * (x : ℂ) ^ (-(1 / 2 : ℂ)) := by
    intro x hx
    rw [one_mul, ← hθ_eq x, ← hθ_eq x⁻¹]
    exact htheta x hx
  have hconst := coeff_eq_of_coeffTheta_relation_of_sq hsum_c hsum_c hc_rel
  have hatom_eq : ∀ m : ℕ, ((ν.real {((m + 1 : ℕ) : ℝ)} : ℝ) : ℂ) = -(2 * α) := by
    intro m
    have hm := hconst m
    simp only [hc_def, Nat.succ_ne_zero, ↓reduceIte] at hm
    exact hm
  refine ⟨hαβ, hnull_compl, hν_sum, hatom_eq, fun h1 => ?_⟩
  have hα_eq : -(2 * α) = 1 := by
    have h0 := hatom_eq 0
    simp only [Nat.zero_add, Nat.cast_one, h1, Complex.ofReal_one] at h0
    exact h0.symm
  have hα : α = -(1 / 2 : ℂ) := by linear_combination -hα_eq / 2
  have hβ : β = (1 / 2 : ℂ) := by linear_combination hαβ + hα_eq / 2
  refine ⟨hα, hβ, ?_⟩
  conv_lhs => rw [hν_sum]
  congr 1 with m
  have hm_real : ν.real {((m + 1 : ℕ) : ℝ)} = 1 := by
    have hmC := hatom_eq m
    rw [hα_eq] at hmC
    exact_mod_cast hmC
  have hm_enn : ν {((m + 1 : ℕ) : ℝ)} = 1 := by
    have hof := ENNReal.ofReal_toReal (hfin_atom m)
    rw [← measureReal_def, hm_real, ENNReal.ofReal_one] at hof
    exact hof.symm
  rw [hm_enn, one_smul]

end GaloisForLFunctions.HTGeometry

#print axioms GaloisForLFunctions.HTGeometry.tsum_sin_sq_div_sq_eq_zero_of_freqTheta_relation
#print axioms GaloisForLFunctions.HTGeometry.beurlingSystem_rigidity_of_completed_functional_equation
#print axioms GaloisForLFunctions.HTGeometry.measure_eq_sum_nat_pos_dirac_of_measureTheta_relation
