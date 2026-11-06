import GaloisForLFunctions.ArithmeticPositiveDuality.PositiveMeasureHamburgerRigidity
import GaloisForLFunctions.HTGeometry.ClockSeriesIntegral
import GaloisForLFunctions.RHTower.BeurlingSystemGibbsGauge

/-!
# Complex Fejér–Tent Spectral Gap Law and Categorical Rigidity of Discrete Beurling Systems

`PositiveMeasureHamburgerRigidity` establishes Borel-measure Hamburger rigidity (`measure_eq_of_measureTheta_relation`,
`measure_eq_of_completed_functional_equation`) and Beurling prime-measure selectivity
(`eq_riemannPrimeMeasure_of_beurling_functional_equation`) via real Fejér pairing on nonnegative
measures. This companion module supplies the two complementary layers:

1. **Complex-coefficient Fejér–tent spectral gap identity (§1)**
   (`tsum_sin_sq_div_sq_eq_neg_add_of_freqSeries_eq`, `tsum_sin_sq_div_sq_eq_zero_of_freqTheta_relation`):
   Without any sign or reality restriction on the coefficients `a_n, b_n ∈ ℂ`, pairing the
   generalized Laplace identity `freqSeries a lam t = η * freqDual b mu t + α / (π t) + β` across
   conjugate vertical points `t = ε + iτ` and `t̄ = ε - iτ` against `1 - τ` on `[0, 1]` and sending
   `ε → 0⁺` yields the exact complex linear constraint
   `η * Σ b_n (sin(π μ_n) / (π μ_n))² + α + β = 0`
   for arbitrary frequencies `λ_n, μ_n ≥ 1` with `Σ ‖a_n‖ / λ_n² < ∞`, `Σ ‖b_n‖ / μ_n² < ∞` and
   zero separation hypothesis. In particular, under any self-dual theta relation on `[1, ∞)`,
   `α + β = 0` and `Σ a_n (sin(π λ_n) / (π λ_n))² = 0` identically, even when `a_n` changes sign
   (as in self-dual character combinations).

2. **Generalized Dirichlet series uniqueness and categorical rigidity of discrete Beurling prime systems (§2–§3)**
   (`freqDirichlet_eq_riemannZeta_of_theta_relation`,
   `freqDirichlet_eq_riemannZeta_of_completed_functional_equation`,
   `beurlingSystem_rigidity_of_theta_relation`,
   `beurlingSystem_rigidity_of_completed_functional_equation_rpow`,
   `beurlingSystem_rigidity_of_completed_functional_equation`):
   Building directly on `PositiveMeasureHamburgerRigidity` without duplicating Borel-measure
   theta-law proofs:
   * Any nonnegative generalized Dirichlet series `Σ w_n λ_n^{-s}` on `[1, ∞)` normalized by unit
     total weight at `λ = 1` whose theta series (`Σ w_n / λ_n² < ∞`) or completed `Γ_ℝ(s)` series
     (`Σ w_n / λ_n^{3/2} < ∞`) satisfies Riemann's degree-one reflection law automatically converges
     on all of `Re s > 1` and equals `riemannZeta s`, with `α = -1/2`, `β = 1/2`, and unit
     aggregated weight on every positive integer.
   * For any countable discrete Beurling generalized prime system `B : RHTower.BeurlingSystem`,
     the empty multiset `0 : B.Integer` is the unique generalized integer of norm `1`, forcing
     `α = -1/2` and `β = 1/2` (excluding any entire degree-one Beurling Euler product), identifying
     `beurlingSystemIntegerMeasure B` with `beurlingIntegerMeasure riemannPrimeMeasure`, forcing
     unique generalized-integer representation of every positive integer `m ≥ 1`, identifying
     `beurlingZeta B s = riemannZeta s` on `Re s > 1`, and producing an explicit norm-preserving
     bijection `B.Label ≃ {p : ℕ // Nat.Prime p}` onto the rational primes.
-/

open Complex MeasureTheory Filter Topology Set
open scoped BigOperators Interval ENNReal MeasureTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality

open GaloisForLFunctions.HTGeometry

/-! ## §1. The Complex-Coefficient Fejér–Tent Spectral Gap Law -/

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
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have h2 : (ε : ℂ) - (u : ℂ) * I ≠ 0 := by
    intro h; have := congrArg Complex.re h; simp at this; linarith
  have hdC : ((ε ^ 2 + u ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (ε ^ 2 + u ^ 2 : ℝ) ≠ 0)
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
    simp only [t]; push_cast; ring_nf; rw [Complex.I_sq]; ring
  have hfac2 : (l : ℂ) ^ 2 + t' ^ 2 =
      ((ε : ℂ) - ((τ - l : ℝ) : ℂ) * I) * ((ε : ℂ) - ((τ + l : ℝ) : ℂ) * I) := by
    simp only [t']; push_cast; ring_nf; rw [Complex.I_sq]; ring
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsplit1 : t / ((l : ℂ) ^ 2 + t ^ 2) =
      (1 / ((ε : ℂ) + ((τ - l : ℝ) : ℂ) * I) + 1 / ((ε : ℂ) + ((τ + l : ℝ) : ℂ) * I)) / 2 := by
    rw [hfac1, one_div_add_one_div hp1 hp2, div_div, div_eq_div_iff (mul_ne_zero hp1 hp2)
      (mul_ne_zero (mul_ne_zero hp1 hp2) two_ne_zero)]
    simp only [t]; push_cast; ring
  have hsplit2 : t' / ((l : ℂ) ^ 2 + t' ^ 2) =
      (1 / ((ε : ℂ) - ((τ - l : ℝ) : ℂ) * I) + 1 / ((ε : ℂ) - ((τ + l : ℝ) : ℂ) * I)) / 2 := by
    rw [hfac2, one_div_add_one_div hm1 hm2, div_div, div_eq_div_iff (mul_ne_zero hm1 hm2)
      (mul_ne_zero (mul_ne_zero hm1 hm2) two_ne_zero)]
    simp only [t']; push_cast; ring
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

/-- Half-line `[0, 1]` Fejér-tent partial-fraction kernel arising from conjugate vertical pairing. -/
def tentSeriesKernel (l ε τ : ℝ) : ℝ :=
  (1 - τ) * (1 / Real.pi) * (ε / (ε ^ 2 + (l - τ) ^ 2) + ε / (ε ^ 2 + (l + τ) ^ 2))

/-- Half-line `[0, 1]` Fejér-tent dual cosine kernel arising from conjugate vertical pairing. -/
def tentDualKernel (l ε τ : ℝ) : ℝ :=
  (1 - τ) * (2 * Real.exp (-(2 * Real.pi * l * ε)) * Real.cos (2 * Real.pi * l * τ))

/-- Half-line `[0, 1]` Fejér-tent origin-pole kernel arising from conjugate vertical pairing. -/
def tentPoleKernel (ε τ : ℝ) : ℝ :=
  (1 - τ) * (2 / Real.pi) * (ε / (ε ^ 2 + τ ^ 2))

/-- Uniform `O(1/l²)` bound on `tentSeriesKernel` for `l ≥ 1`, `0 < ε ≤ 1`, `τ ∈ [0, 1]`. -/
theorem tentSeriesKernel_nonneg_and_le {l ε τ : ℝ} (hl : 1 ≤ l) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) :
    0 ≤ tentSeriesKernel l ε τ ∧ tentSeriesKernel l ε τ ≤ (5 / Real.pi) / l ^ 2 := by
  have h1τ : 0 ≤ 1 - τ := by linarith
  have hnn : 0 ≤ tentSeriesKernel l ε τ := by unfold tentSeriesKernel; positivity
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
        rw [← mul_div_assoc, div_le_div_iff₀ hdpos two_pos]; linarith
      have hhalf4 : (1 / 2 : ℝ) ≤ 4 / l ^ 2 := by
        rw [div_le_div_iff₀ two_pos (by positivity)]; nlinarith
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

/-- As `ε → 0⁺`, `∫₀¹ tentSeriesKernel l ε τ dτ → 0` for every `l ≥ 1`, deduced directly from the
`O(√ε / l²)` collar bound `intervalIntegral_fejerSeriesKernel_le` in `PositiveMeasureHamburgerRigidity`. -/
theorem tendsto_integral_tentSeriesKernel {l : ℝ} (hl : 1 ≤ l) :
    Tendsto (fun ε : ℝ => ∫ τ in (0 : ℝ)..1, tentSeriesKernel l ε τ) (𝓝[>] 0) (𝓝 0) := by
  have hmaj : Tendsto (fun ε : ℝ => (24 * Real.sqrt ε / Real.pi) * (1 / l ^ 2)) (𝓝[>] 0) (𝓝 0) := by
    have hsq : Tendsto Real.sqrt (𝓝[>] 0) (𝓝 0) := by
      simpa using (Real.continuous_sqrt.tendsto 0).mono_left nhdsWithin_le_nhds
    have h0 : 24 * (0 : ℝ) / Real.pi * (1 / l ^ 2) = 0 := by ring
    have ht := (((hsq.const_mul 24).div_const Real.pi).mul_const (1 / l ^ 2))
    rwa [h0] at ht
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
    exact intervalIntegral.integral_nonneg zero_le_one fun τ hτ =>
      (tentSeriesKernel_nonneg_and_le hl hε.1 hε.2.le hτ.1 hτ.2).1
  · filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
    have hε0 : 0 < ε := hε.1
    have hε1 : ε ≤ 1 := hε.2.le
    have hc_fej : Continuous (fun τ : ℝ => fejerSeriesKernel ε τ l) := by
      have heq : (fun τ : ℝ => fejerSeriesKernel ε τ l) = fun τ : ℝ =>
          (1 - |τ|) * ((1 / Real.pi) * (ε / (ε ^ 2 + (τ - l) ^ 2) + ε / (ε ^ 2 + (τ + l) ^ 2))) :=
        funext fun τ => fejerSeriesKernel_eq hε0 τ l
      rw [heq]
      exact (continuous_const.sub continuous_abs).mul (continuous_const.mul
        ((continuous_const.div (by fun_prop) fun _ => by positivity).add
          (continuous_const.div (by fun_prop) fun _ => by positivity)))
    have hcongr : (∫ τ in (0 : ℝ)..1, tentSeriesKernel l ε τ) =
        ∫ τ in (0 : ℝ)..1, fejerSeriesKernel ε τ l := by
      refine intervalIntegral.integral_congr fun τ hτ => ?_
      rw [uIcc_of_le zero_le_one] at hτ
      rw [tentSeriesKernel, fejerSeriesKernel_eq hε0 τ l, abs_of_nonneg hτ.1,
        show (τ - l) ^ 2 = (l - τ) ^ 2 by ring, show (τ + l) ^ 2 = (l + τ) ^ 2 by ring]
      ring
    have hL_nn : 0 ≤ ∫ τ in (-1 : ℝ)..0, fejerSeriesKernel ε τ l :=
      intervalIntegral.integral_nonneg (by norm_num) fun τ hτ =>
        fejerSeriesKernel_nonneg hε0 (abs_le.mpr ⟨hτ.1, by linarith [hτ.2]⟩) l
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hc_fej.intervalIntegrable (μ := volume) (-1) 0)
      (hc_fej.intervalIntegrable (μ := volume) 0 1)
    have hfej := intervalIntegral_fejerSeriesKernel_le hl hε0 hε1
    linarith

/-- Exact evaluation `∫₀¹ tentDualKernel l ε τ dτ = e^{-2π l ε} (sin(π l) / (π l))²` via evenness and
`intervalIntegral_fejerDualKernel` from `PositiveMeasureHamburgerRigidity`. -/
theorem integral_tentDualKernel {l : ℝ} (hl : 1 ≤ l) (ε : ℝ) :
    (∫ τ in (0 : ℝ)..1, tentDualKernel l ε τ) =
      Real.exp (-(2 * Real.pi * l * ε)) * (Real.sin (Real.pi * l) / (Real.pi * l)) ^ 2 := by
  have hl0 : l ≠ 0 := (lt_of_lt_of_le one_pos hl).ne'
  have hc : Continuous (fun τ : ℝ => fejerDualKernel ε τ l) :=
    (continuous_uncurry_fejerDualKernel ε).comp (continuous_id.prodMk continuous_const)
  have hsplit := (intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (-1) 0) (hc.intervalIntegrable (μ := volume) 0 1)).symm
  have hL : (∫ τ in (-1 : ℝ)..0, fejerDualKernel ε τ l) =
      ∫ τ in (0 : ℝ)..1, tentDualKernel l ε τ := by
    have hneg := intervalIntegral.integral_comp_neg (fun τ : ℝ => fejerDualKernel ε τ l) (a := 0) (b := 1)
    simp only [neg_zero] at hneg
    rw [← hneg]
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [uIcc_of_le zero_le_one] at hτ
    rw [fejerDualKernel_eq, tentDualKernel, abs_neg, abs_of_nonneg hτ.1, mul_neg, Real.cos_neg,
      show -2 * Real.pi * l * ε = -(2 * Real.pi * l * ε) by ring]
    ring
  have hR : (∫ τ in (0 : ℝ)..1, fejerDualKernel ε τ l) =
      ∫ τ in (0 : ℝ)..1, tentDualKernel l ε τ := by
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [uIcc_of_le zero_le_one] at hτ
    rw [fejerDualKernel_eq, tentDualKernel, abs_of_nonneg hτ.1,
      show -2 * Real.pi * l * ε = -(2 * Real.pi * l * ε) by ring]
    ring
  have hfull := intervalIntegral_fejerDualKernel ε hl0
  rw [show -2 * Real.pi * l * ε = -(2 * Real.pi * l * ε) by ring] at hfull
  linarith

theorem abs_integral_tentDualKernel_le {l ε : ℝ} (hl : 1 ≤ l) (hε : 0 < ε) :
    |∫ τ in (0 : ℝ)..1, tentDualKernel l ε τ| ≤ 1 / (Real.pi ^ 2 * l ^ 2) := by
  rw [integral_tentDualKernel hl ε, abs_of_nonneg (by positivity)]
  have hexp : Real.exp (-(2 * Real.pi * l * ε)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have hl0 : 0 < l := lt_of_lt_of_le one_pos hl
    have hp : 0 < 2 * Real.pi * l * ε := by positivity
    linarith
  have hsin : Real.sin (Real.pi * l) ^ 2 ≤ 1 := Real.sin_sq_le_one _
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

/-- As `ε → 0⁺`, `∫₀¹ tentPoleKernel ε τ dτ → 1`, deduced directly from `tendsto_fejer_polar` in
`PositiveMeasureHamburgerRigidity`. -/
theorem tendsto_integral_tentPoleKernel :
    Tendsto (fun ε : ℝ => ∫ τ in (0 : ℝ)..1, tentPoleKernel ε τ) (𝓝[>] 0) (𝓝 1) := by
  have hp := tendsto_fejer_polar.const_mul (1 / Real.pi)
  rw [one_div_mul_cancel Real.pi_ne_zero] at hp
  refine hp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : 0 < ε := hε
  let g : ℝ → ℝ := fun τ => (1 - |τ|) * (ε / (ε ^ 2 + τ ^ 2))
  have hc : Continuous g :=
    (continuous_const.sub continuous_abs).mul (continuous_const.div (by fun_prop) fun _ => by positivity)
  have hsplit := (intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (μ := volume) (-1) 0) (hc.intervalIntegrable (μ := volume) 0 1)).symm
  have hL : (∫ τ in (-1 : ℝ)..0, g τ) = ∫ τ in (0 : ℝ)..1, g τ := by
    have hneg := intervalIntegral.integral_comp_neg g (a := 0) (b := 1)
    simp only [neg_zero] at hneg
    rw [← hneg]
    exact intervalIntegral.integral_congr fun τ _ => by simp only [g, abs_neg, neg_sq]
  have hR : (∫ τ in (0 : ℝ)..1, tentPoleKernel ε τ) = (2 / Real.pi) * ∫ τ in (0 : ℝ)..1, g τ := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [uIcc_of_le zero_le_one] at hτ
    simp only [tentPoleKernel, g, abs_of_nonneg hτ.1]
    ring
  change (1 / Real.pi) * (∫ τ in (-1 : ℝ)..1, g τ) = ∫ τ in (0 : ℝ)..1, tentPoleKernel ε τ
  rw [hsplit, hL, hR]
  ring

/-- Lower bound on `‖l² + (ε + iσ)²‖` for `l ≥ 1`, `0 < ε ≤ 1`, `|σ| ≤ 1`. -/
theorem norm_sq_add_vertical_sq_ge {l ε σ : ℝ} (hl : 1 ≤ l) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hσ : |σ| ≤ 1) :
    min (1 / 2) (ε ^ 2 / 4) * l ^ 2 ≤ ‖(l : ℂ) ^ 2 + ((ε : ℂ) + (σ : ℂ) * I) ^ 2‖ := by
  rcases le_or_gt l 2 with hl2 | hl2
  · have hfac : (l : ℂ) ^ 2 + ((ε : ℂ) + (σ : ℂ) * I) ^ 2 =
        ((ε : ℂ) + ((σ - l : ℝ) : ℂ) * I) * ((ε : ℂ) + ((σ + l : ℝ) : ℂ) * I) := by
      push_cast; ring_nf; rw [Complex.I_sq]; ring
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
        rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
      rw [hreim]
      have hσb := abs_le.mp hσ
      nlinarith
    have htri := norm_sub_le ((l : ℂ) ^ 2 + ((ε : ℂ) + (σ : ℂ) * I) ^ 2)
      (((ε : ℂ) + (σ : ℂ) * I) ^ 2)
    rw [add_sub_cancel_right, h1] at htri
    calc min (1 / 2) (ε ^ 2 / 4) * l ^ 2 ≤ (1 / 2) * l ^ 2 :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg l)
      _ ≤ l ^ 2 - 2 := by nlinarith
      _ ≤ ‖(l : ℂ) ^ 2 + ((ε : ℂ) + (σ : ℂ) * I) ^ 2‖ := by linarith

/-- **Complex Fejér–tent spectral gap identity (Laplace form).**
If `freqSeries a lam t = η * freqDual b mu t + α / (π t) + β` on `Re t > 0` for arbitrary complex
weights `a, b : ℕ → ℂ` and frequencies `lam n ≥ 1`, `mu n ≥ 1`, then
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
      intro τ _ _
      have hre1 : 0 < ((ε : ℂ) + (τ : ℂ) * I).re := by simp [hε0]
      have hre2 : 0 < ((ε : ℂ) - (τ : ℂ) * I).re := by simp [hε0]
      rw [heq hre1, heq hre2]
      have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      have hcauchy : α / ((Real.pi : ℂ) * ((ε : ℂ) + (τ : ℂ) * I)) +
          α / ((Real.pi : ℂ) * ((ε : ℂ) - (τ : ℂ) * I)) =
          (α / (Real.pi : ℂ)) *
            (1 / ((ε : ℂ) + (τ : ℂ) * I) + 1 / ((ε : ℂ) - (τ : ℂ) * I)) := by
        simp only [div_mul_eq_div_div]; ring
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
        hcD.comp_continuous (by fun_prop) fun _ => by simp [hε0]
      have hc2 : Continuous fun τ : ℝ => FreqHamburger.freqDual b mu ((ε : ℂ) - (τ : ℂ) * I) :=
        hcD.comp_continuous (by fun_prop) fun _ => by simp [hε0]
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

/-- **Complex Fejér–tent spectral gap identity for `freqTheta`.**
For arbitrary complex coefficients `a_n : ℂ` and frequencies `lam n ≥ 1` with `Σ ‖a_n‖ / λ_n² < ∞`,
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

/-! ## §2. Nonnegative Generalized Dirichlet Series Uniqueness -/

/-- Aggregated real weight carried by the integer frequency `m`. -/
def aggRealCoeff (w : ℕ → ℝ) (lam : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑' n : ℕ, if lam n = (m : ℝ) then w n else 0

/-- Generalized Dirichlet series `Σ a_n λ_n^{-s}`. -/
def freqDirichlet (a : ℕ → ℂ) (lam : ℕ → ℝ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, a n / (lam n : ℂ) ^ s

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

private theorem measureDirichlet_nat_succ_eq_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    measureDirichlet (Measure.sum fun k : ℕ => Measure.dirac ((k : ℝ) + 1)) s = riemannZeta s := by
  have hsmul : (Measure.sum fun k : ℕ => Measure.dirac ((k : ℝ) + 1)) =
      Measure.sum (fun k : ℕ => (1 : ℝ≥0∞) • Measure.dirac ((k : ℝ) + 1)) := by
    congr 1; ext k : 1; simp
  unfold measureDirichlet
  rw [hsmul, integral_sum_dirac (fun _ => ENNReal.one_ne_top),
    zeta_eq_tsum_one_div_nat_add_one_cpow hs]
  refine tsum_congr fun k => ?_
  rw [ENNReal.toReal_one, one_smul, Complex.cpow_neg, one_div,
    show (((k : ℝ) + 1 : ℝ) : ℂ) = (k : ℂ) + 1 by push_cast; ring]

private theorem freqDirichlet_eq_riemannZeta_of_measure_eq
    {w : ℕ → ℝ} {lam : ℕ → ℝ} {α β : ℂ}
    (hw : ∀ n, 0 ≤ w n)
    (hsum2 : Summable fun n : ℕ => w n / lam n ^ 2)
    (hone : aggRealCoeff w lam 1 = 1)
    (hβα : β = -α) (hαim : α.im = 0) (hρ_nn : 0 ≤ -2 * α.re)
    (hν_eq : Measure.sum (fun n : ℕ => ENNReal.ofReal (w n) • Measure.dirac (lam n)) =
      ENNReal.ofReal (-2 * α.re) • Measure.sum (fun k : ℕ => Measure.dirac ((k : ℝ) + 1))) :
    α = -1 / 2 ∧ β = 1 / 2 ∧
      (∀ n, w n ≠ 0 → ∃ m : ℕ, 1 ≤ m ∧ lam n = (m : ℝ)) ∧
      (∀ m : ℕ, aggRealCoeff w lam (m + 1) = 1) ∧
      (∀ s : ℂ, 1 < s.re → freqDirichlet (fun n => (w n : ℂ)) lam s = riemannZeta s) := by
  let ν : Measure ℝ := Measure.sum (fun n : ℕ => ENNReal.ofReal (w n) • Measure.dirac (lam n))
  have hc_fin : ∀ n : ℕ, ENNReal.ofReal (w n) ≠ ⊤ := fun _ => ENNReal.ofReal_ne_top
  have hν_eq' : ν =
      ENNReal.ofReal (-2 * α.re) • Measure.sum (fun k : ℕ => Measure.dirac ((k : ℝ) + 1)) := hν_eq
  have hint : ∀ n, w n ≠ 0 → ∃ m : ℕ, 1 ≤ m ∧ lam n = (m : ℝ) := by
    intro n hwn
    by_contra hnot
    have hpos : 0 < w n := lt_of_le_of_ne (hw n) (Ne.symm hwn)
    have hle1 : ENNReal.ofReal (w n) ≤ ν {lam n} := by
      have h := Measure.le_sum (fun m : ℕ => ENNReal.ofReal (w m) • Measure.dirac (lam m)) n {lam n}
      rwa [Measure.smul_apply, Measure.dirac_apply_of_mem (mem_singleton _), smul_eq_mul, mul_one] at h
    have hzero : ν {lam n} = 0 := by
      rw [hν_eq', Measure.smul_apply, Measure.sum_apply _ (measurableSet_singleton _)]
      have hsum0 : (∑' k : ℕ, Measure.dirac ((k : ℝ) + 1) {lam n}) = 0 := by
        refine (tsum_congr fun k => ?_).trans tsum_zero
        rw [Measure.dirac_apply, Set.indicator_of_notMem]
        simp only [mem_singleton_iff]
        intro heq
        exact hnot ⟨k + 1, by omega, by push_cast; exact heq.symm⟩
      rw [hsum0, smul_zero]
    rw [hzero, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hle1
    linarith
  have hagg_rho : ∀ m : ℕ, aggRealCoeff w lam (m + 1) = -2 * α.re := by
    intro m
    have hnn_m : 0 ≤ aggRealCoeff w lam (m + 1) :=
      tsum_nonneg fun n => by split_ifs <;> linarith [hw n]
    have heval := congrArg (fun μ : Measure ℝ => μ {((m + 1 : ℕ) : ℝ)}) hν_eq'
    have hlhs : ν {((m + 1 : ℕ) : ℝ)} = ENNReal.ofReal (aggRealCoeff w lam (m + 1)) := by
      dsimp only [ν]
      rw [Measure.sum_apply _ (measurableSet_singleton _), aggRealCoeff,
        ENNReal.ofReal_tsum_of_nonneg (fun n => by split_ifs <;> linarith [hw n])
          (summable_ite_of_sq hw hsum2 m)]
      refine tsum_congr fun n => ?_
      rw [Measure.smul_apply, smul_eq_mul]
      by_cases h : lam n = ((m + 1 : ℕ) : ℝ)
      · rw [if_pos h, h, Measure.dirac_apply_of_mem (mem_singleton _), mul_one]
      · rw [if_neg h, Measure.dirac_apply' _ (measurableSet_singleton _),
          Set.indicator_of_notMem (by simpa [mem_singleton_iff] using h), mul_zero,
          ENNReal.ofReal_zero]
    have hrhs : (ENNReal.ofReal (-2 * α.re) •
        Measure.sum (fun k : ℕ => Measure.dirac ((k : ℝ) + 1))) {((m + 1 : ℕ) : ℝ)} =
        ENNReal.ofReal (-2 * α.re) := by
      rw [Measure.smul_apply, smul_eq_mul, Measure.sum_apply _ (measurableSet_singleton _),
        tsum_eq_single m]
      · have hm_cast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
        rw [hm_cast]; simp
      · intro k hk
        rw [Measure.dirac_apply, Set.indicator_of_notMem]
        simp only [mem_singleton_iff]
        intro heq
        exact hk (by exact_mod_cast (by push_cast at heq; linarith : (k : ℝ) = (m : ℝ)))
    have hof : ENNReal.ofReal (aggRealCoeff w lam (m + 1)) = ENNReal.ofReal (-2 * α.re) := by
      rw [← hlhs, heval, hrhs]
    have htr := congrArg ENNReal.toReal hof
    rwa [ENNReal.toReal_ofReal hnn_m, ENNReal.toReal_ofReal hρ_nn] at htr
  have hρ1 : -2 * α.re = 1 := by
    have h0 := hagg_rho 0
    rw [zero_add, hone] at h0
    exact h0.symm
  have hα : α = -1 / 2 := by
    apply Complex.ext
    · simp; linarith
    · simp [hαim]
  have hβ : β = 1 / 2 := by rw [hβα, hα]; ring
  have hagg1 : ∀ m : ℕ, aggRealCoeff w lam (m + 1) = 1 := fun m => (hagg_rho m).trans hρ1
  have hν_nat : ν = Measure.sum (fun k : ℕ => Measure.dirac ((k : ℝ) + 1)) := by
    rw [hν_eq', hρ1, ENNReal.ofReal_one, one_smul]
  refine ⟨hα, hβ, hint, hagg1, fun s hs => ?_⟩
  have hdir_ν : freqDirichlet (fun n => (w n : ℂ)) lam s = measureDirichlet ν s := by
    unfold freqDirichlet measureDirichlet
    dsimp only [ν]
    rw [integral_sum_dirac hc_fin]
    refine tsum_congr fun n => ?_
    rw [ENNReal.toReal_ofReal (hw n), Complex.real_smul, Complex.cpow_neg, div_eq_mul_inv]
  rw [hdir_ν, hν_nat, measureDirichlet_nat_succ_eq_riemannZeta hs]

/-- **Uniqueness of `ζ` among nonnegative generalized theta series (`Σ w_n / λ_n² < ∞`).**
If `w : ℕ → ℝ` is nonnegative, `lam n ≥ 1`, `Σ w_n / λ_n² < ∞`, `aggRealCoeff w lam 1 = 1`, and
`freqTheta (w ·) lam` satisfies Riemann's degree-one theta relation, then `α = -1/2`, `β = 1/2`,
every active frequency is a positive integer, every positive integer has aggregated weight `1`,
and `freqDirichlet (w ·) lam s = riemannZeta s` on all of `Re s > 1`. -/
theorem freqDirichlet_eq_riemannZeta_of_theta_relation
    {w : ℕ → ℝ} {lam : ℕ → ℝ} {α β : ℂ}
    (hw : ∀ n, 0 ≤ w n) (hlam : ∀ n, 1 ≤ lam n)
    (hsum : Summable fun n : ℕ => w n / lam n ^ 2)
    (hone : aggRealCoeff w lam 1 = 1)
    (htheta : ∀ x : ℝ, 0 < x →
      FreqHamburger.freqTheta (fun n => (w n : ℂ)) lam x =
        (x : ℂ) ^ (-(1 / 2 : ℂ)) * FreqHamburger.freqTheta (fun n => (w n : ℂ)) lam x⁻¹ + α +
          β * (x : ℂ) ^ (-(1 / 2 : ℂ))) :
    α = -1 / 2 ∧ β = 1 / 2 ∧
      (∀ n, w n ≠ 0 → ∃ m : ℕ, 1 ≤ m ∧ lam n = (m : ℝ)) ∧
      (∀ m : ℕ, aggRealCoeff w lam (m + 1) = 1) ∧
      (∀ s : ℂ, 1 < s.re → freqDirichlet (fun n => (w n : ℂ)) lam s = riemannZeta s) := by
  let ν : Measure ℝ := Measure.sum (fun n : ℕ => ENNReal.ofReal (w n) • Measure.dirac (lam n))
  have hc_fin : ∀ n : ℕ, ENNReal.ofReal (w n) ≠ ⊤ := fun _ => ENNReal.ofReal_ne_top
  have hsupp : ν (Iio 1) = 0 := by
    dsimp only [ν]
    rw [Measure.sum_apply _ measurableSet_Iio]
    refine (tsum_congr fun n => ?_).trans tsum_zero
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ measurableSet_Iio,
      Set.indicator_of_notMem (by simp [hlam n]), mul_zero]
  have hmom : Integrable (fun u : ℝ => 1 / u ^ 2) ν := by
    refine integrable_sum_dirac hc_fin (hsum.congr fun n => ?_)
    have hl0 : 0 < lam n := lt_of_lt_of_le zero_lt_one (hlam n)
    rw [ENNReal.toReal_ofReal (hw n), Real.norm_eq_abs, abs_of_nonneg (by positivity), mul_one_div]
  have hθ_eq : ∀ x : ℝ, measureTheta ν x = FreqHamburger.freqTheta (fun n => (w n : ℂ)) lam x := by
    intro x
    unfold measureTheta FreqHamburger.freqTheta
    dsimp only [ν]
    rw [integral_sum_dirac hc_fin]
    exact tsum_congr fun n => by rw [ENNReal.toReal_ofReal (hw n), Complex.real_smul]
  obtain ⟨hβα, hαim, hρ_nn, hν_eq⟩ := measure_eq_of_measureTheta_relation hsupp hmom
    (fun x hx => by rw [hθ_eq x, hθ_eq x⁻¹]; exact htheta x hx)
  exact freqDirichlet_eq_riemannZeta_of_measure_eq hw hsum hone hβα hαim hρ_nn hν_eq

/-- **Uniqueness of `ζ` among nonnegative generalized Dirichlet series (`Σ w_n / λ_n^{3/2} < ∞`).**
If `w : ℕ → ℝ` is nonnegative, `lam n ≥ 1`, `Σ w_n / λ_n^{3/2} < ∞`, `aggRealCoeff w lam 1 = 1`,
and `Γ_ℝ(s) freqDirichlet (w ·) lam s` satisfies Riemann's degree-one reflection law on
`-1/2 ≤ Re s ≤ 3/2`, then `α = -1/2`, `β = 1/2`, every active frequency is a positive integer,
every positive integer carries aggregated weight `1`, and `freqDirichlet (w ·) lam s = riemannZeta s`
for all `Re s > 1`. -/
theorem freqDirichlet_eq_riemannZeta_of_completed_functional_equation_rpow
    {w : ℕ → ℝ} {lam : ℕ → ℝ} {E : ℂ → ℂ} {α β : ℂ} {C : ℝ}
    (hw : ∀ n, 0 ≤ w n) (hlam : ∀ n, 1 ≤ lam n)
    (hwsum : Summable fun n : ℕ => w n / lam n ^ (3 / 2 : ℝ))
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
  let ν : Measure ℝ := Measure.sum (fun n : ℕ => ENNReal.ofReal (w n) • Measure.dirac (lam n))
  have hc_fin : ∀ n : ℕ, ENNReal.ofReal (w n) ≠ ⊤ := fun _ => ENNReal.ofReal_ne_top
  have hsupp : ν (Iio 1) = 0 := by
    dsimp only [ν]
    rw [Measure.sum_apply _ measurableSet_Iio]
    refine (tsum_congr fun n => ?_).trans tsum_zero
    rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ measurableSet_Iio,
      Set.indicator_of_notMem (by simp [hlam n]), mul_zero]
  have hmom : Integrable (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) ν := by
    refine integrable_sum_dirac hc_fin (hwsum.congr fun n => ?_)
    have hl0 : 0 < lam n := lt_of_lt_of_le zero_lt_one (hlam n)
    rw [ENNReal.toReal_ofReal (hw n), Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hl0.le _), Real.rpow_neg hl0.le, div_eq_mul_inv]
  have hdir_ν : ∀ s : ℂ, measureDirichlet ν s = freqDirichlet (fun n => (w n : ℂ)) lam s := by
    intro s
    unfold measureDirichlet freqDirichlet
    dsimp only [ν]
    rw [integral_sum_dirac hc_fin]
    refine tsum_congr fun n => ?_
    rw [ENNReal.toReal_ofReal (hw n), Complex.real_smul, Complex.cpow_neg, div_eq_mul_inv]
  obtain ⟨hβα, hαim, hρ_nn, hν_eq⟩ := measure_eq_of_completed_functional_equation hsupp hmom hE hdecay
    (fun s hs => by rw [hdir_ν s]; exact hR s hs)
    (fun s hs => by rw [hdir_ν (1 - s)]; exact hL s hs)
  have hsum2 : Summable fun n : ℕ => w n / lam n ^ 2 := by
    refine hwsum.of_nonneg_of_le (fun n => div_nonneg (hw n) (sq_nonneg _)) fun n => ?_
    have hl0 : 0 < lam n := lt_of_lt_of_le zero_lt_one (hlam n)
    refine div_le_div_of_nonneg_left (hw n) (Real.rpow_pos_of_pos hl0 _) ?_
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (hlam n) (by norm_num)
  exact freqDirichlet_eq_riemannZeta_of_measure_eq hw hsum2 hone hβα hαim hρ_nn hν_eq

/-- Wrapper of `freqDirichlet_eq_riemannZeta_of_completed_functional_equation_rpow` under half-plane
convergence `∀ σ > 1, Summable (w n / lam n ^ σ)`. -/
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
      (∀ s : ℂ, 1 < s.re → freqDirichlet (fun n => (w n : ℂ)) lam s = riemannZeta s) :=
  freqDirichlet_eq_riemannZeta_of_completed_functional_equation_rpow
    hw hlam (hwsum (3 / 2) (by norm_num)) hone hE hdecay hR hL

/-! ## §3. Categorical Rigidity of Countable Discrete Beurling Prime Systems -/

/-- Theta series `Σ_{g : B.Integer} e^{-π |g|² x}` of a discrete Beurling prime system. -/
def beurlingTheta (B : RHTower.BeurlingSystem) (x : ℝ) : ℂ :=
  ∑' g : B.Integer, ((Real.exp (-Real.pi * B.intNorm g ^ 2 * x) : ℝ) : ℂ)

/-- Zeta series `Σ_{g : B.Integer} |g|^{-s}` of a discrete Beurling prime system. -/
def beurlingZeta (B : RHTower.BeurlingSystem) (s : ℂ) : ℂ :=
  ∑' g : B.Integer, (1 : ℂ) / (B.intNorm g : ℂ) ^ s

/-- Generalized-integer norm counting measure `Σ_{g : B.Integer} δ_{|g|}` on `ℝ`. -/
def beurlingSystemIntegerMeasure (B : RHTower.BeurlingSystem) : Measure ℝ :=
  Measure.sum fun g : B.Integer => Measure.dirac (B.intNorm g)

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

theorem beurlingSystemIntegerMeasure_Iio_one_eq_zero (B : RHTower.BeurlingSystem)
    [Countable B.Label] :
    beurlingSystemIntegerMeasure B (Iio 1) = 0 := by
  unfold beurlingSystemIntegerMeasure
  rw [Measure.sum_apply _ measurableSet_Iio]
  refine (tsum_congr fun g => ?_).trans tsum_zero
  rw [Measure.dirac_apply' _ measurableSet_Iio,
    Set.indicator_of_notMem (by simp [B.one_le_intNorm g])]

theorem beurlingSystemIntegerMeasure_singleton_one (B : RHTower.BeurlingSystem)
    [Countable B.Label] :
    beurlingSystemIntegerMeasure B {1} = 1 := by
  unfold beurlingSystemIntegerMeasure
  rw [Measure.sum_apply _ (measurableSet_singleton 1), tsum_eq_single (0 : B.Integer)]
  · simp [B.intNorm_zero]
  · intro g hg0
    rw [Measure.dirac_apply, Set.indicator_of_notMem]
    simp only [mem_singleton_iff]
    exact fun h1 => hg0 ((intNorm_eq_one_iff B g).mp h1)

theorem measureTheta_beurlingSystemIntegerMeasure (B : RHTower.BeurlingSystem)
    [Countable B.Label] (x : ℝ) :
    measureTheta (beurlingSystemIntegerMeasure B) x = beurlingTheta B x := by
  have hsmul : beurlingSystemIntegerMeasure B =
      Measure.sum (fun g : B.Integer => (1 : ℝ≥0∞) • Measure.dirac (B.intNorm g)) := by
    unfold beurlingSystemIntegerMeasure; congr 1; ext g : 1; simp
  unfold measureTheta beurlingTheta
  rw [hsmul, integral_sum_dirac (fun _ => ENNReal.one_ne_top)]
  exact tsum_congr fun _ => by rw [ENNReal.toReal_one, one_smul]

theorem measureDirichlet_beurlingSystemIntegerMeasure (B : RHTower.BeurlingSystem)
    [Countable B.Label] (s : ℂ) :
    measureDirichlet (beurlingSystemIntegerMeasure B) s = beurlingZeta B s := by
  have hsmul : beurlingSystemIntegerMeasure B =
      Measure.sum (fun g : B.Integer => (1 : ℝ≥0∞) • Measure.dirac (B.intNorm g)) := by
    unfold beurlingSystemIntegerMeasure; congr 1; ext g : 1; simp
  unfold measureDirichlet beurlingZeta
  rw [hsmul, integral_sum_dirac (fun _ => ENNReal.one_ne_top)]
  exact tsum_congr fun _ => by rw [ENNReal.toReal_one, one_smul, Complex.cpow_neg, one_div]

private theorem beurlingSystem_rigidity_of_measure_eq
    (B : RHTower.BeurlingSystem) [Countable B.Label]
    {α β : ℂ}
    (hβα : β = -α) (hαim : α.im = 0) (hρ_nn : 0 ≤ -2 * α.re)
    (hν_eq : beurlingSystemIntegerMeasure B =
      ENNReal.ofReal (-2 * α.re) • Measure.sum (fun k : ℕ => Measure.dirac ((k : ℝ) + 1))) :
    α = -1 / 2 ∧ β = 1 / 2 ∧
      beurlingSystemIntegerMeasure B = beurlingIntegerMeasure riemannPrimeMeasure ∧
      (∀ g : B.Integer, ∃ m : ℕ, 1 ≤ m ∧ B.intNorm g = (m : ℝ)) ∧
      (∀ m : ℕ, 1 ≤ m → ∃! g : B.Integer, B.intNorm g = (m : ℝ)) ∧
      (∀ s : ℂ, 1 < s.re → beurlingZeta B s = riemannZeta s) ∧
      Nonempty {e : B.Label ≃ {p : ℕ // Nat.Prime p} //
        ∀ l : B.Label, B.labelNorm l = ((e l : ℕ) : ℝ)} := by
  classical
  set ν : Measure ℝ := beurlingSystemIntegerMeasure B
  have hν_eq' : ν =
      ENNReal.ofReal (-2 * α.re) • Measure.sum (fun k : ℕ => Measure.dirac ((k : ℝ) + 1)) := hν_eq
  -- Evaluate at `{1}` to fix `α = -1/2`, `β = 1/2`
  have h1_lhs : ν {1} = 1 := beurlingSystemIntegerMeasure_singleton_one B
  have h1_rhs : (ENNReal.ofReal (-2 * α.re) •
      Measure.sum (fun k : ℕ => Measure.dirac ((k : ℝ) + 1))) {1} =
      ENNReal.ofReal (-2 * α.re) := by
    rw [Measure.smul_apply, smul_eq_mul, Measure.sum_apply _ (measurableSet_singleton 1),
      tsum_eq_single 0]
    · simp
    · intro k hk
      rw [Measure.dirac_apply, Set.indicator_of_notMem]
      simp only [mem_singleton_iff]
      intro heq
      exact hk (by exact_mod_cast (by linarith : (k : ℝ) = 0))
  have hof1 : ENNReal.ofReal (-2 * α.re) = 1 := by rw [← h1_rhs, ← hν_eq', h1_lhs]
  have hρ1 : -2 * α.re = 1 := by
    have := congrArg ENNReal.toReal hof1
    rwa [ENNReal.toReal_ofReal hρ_nn, ENNReal.toReal_one] at this
  have hα : α = -1 / 2 := by
    apply Complex.ext
    · simp; linarith
    · simp [hαim]
  have hβ : β = 1 / 2 := by rw [hβα, hα]; ring
  have hν_nat : ν = Measure.sum (fun k : ℕ => Measure.dirac ((k : ℝ) + 1)) := by
    rw [hν_eq', hof1, one_smul]
  have hν_beurling : ν = beurlingIntegerMeasure riemannPrimeMeasure :=
    hν_nat.trans beurlingIntegerMeasure_riemannPrimeMeasure.symm
  -- Every `g : B.Integer` has positive integer norm
  have hg_int : ∀ g : B.Integer, ∃ m : ℕ, 1 ≤ m ∧ B.intNorm g = (m : ℝ) := by
    intro g
    by_contra hnot
    have hle1 : (1 : ℝ≥0∞) ≤ ν {B.intNorm g} := by
      have h := Measure.le_sum (fun h : B.Integer => Measure.dirac (B.intNorm h)) g {B.intNorm g}
      rwa [Measure.dirac_apply_of_mem (mem_singleton _)] at h
    have hzero : ν {B.intNorm g} = 0 := by
      rw [hν_nat, Measure.sum_apply _ (measurableSet_singleton _)]
      refine (tsum_congr fun k => ?_).trans tsum_zero
      rw [Measure.dirac_apply, Set.indicator_of_notMem]
      simp only [mem_singleton_iff]
      intro heq
      exact hnot ⟨k + 1, by omega, by push_cast; exact heq.symm⟩
    rw [hzero] at hle1
    exact absurd hle1 (by norm_num)
  -- Every `m ≥ 1` occurs for a unique `g : B.Integer`
  have hm_uniq : ∀ m : ℕ, 1 ≤ m → ∃! g : B.Integer, B.intNorm g = (m : ℝ) := by
    intro m hm1
    have hν_m : ν {(m : ℝ)} = 1 := by
      rw [hν_nat, Measure.sum_apply _ (measurableSet_singleton _), tsum_eq_single (m - 1)]
      · have hm_sub : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by exact_mod_cast (by omega : m - 1 + 1 = m)
        rw [hm_sub]; simp
      · intro k hk
        rw [Measure.dirac_apply, Set.indicator_of_notMem]
        simp only [mem_singleton_iff]
        intro heq
        have hkm : k + 1 = m := by exact_mod_cast heq
        exact hk (by omega)
    have htsum_m : (∑' g : B.Integer, if B.intNorm g = (m : ℝ) then (1 : ℝ≥0∞) else 0) = 1 := by
      have h := hν_m
      dsimp only [ν, beurlingSystemIntegerMeasure] at h
      rw [Measure.sum_apply _ (measurableSet_singleton _)] at h
      refine (tsum_congr fun g => ?_).trans h
      rw [Measure.dirac_apply]
      by_cases hg : B.intNorm g = (m : ℝ) <;> simp [hg]
    have hex : ∃ g : B.Integer, B.intNorm g = (m : ℝ) := by
      by_contra hnone
      push Not at hnone
      simp [hnone] at htsum_m
    obtain ⟨g₀, hg₀⟩ := hex
    refine ⟨g₀, hg₀, fun g₁ hg₁ => ?_⟩
    by_contra hne
    have hle := ENNReal.sum_le_tsum (f := fun g : B.Integer =>
      if B.intNorm g = (m : ℝ) then (1 : ℝ≥0∞) else 0) ({g₀, g₁} : Finset B.Integer)
    rw [Finset.sum_pair (Ne.symm hne), if_pos hg₀, if_pos hg₁, htsum_m] at hle
    norm_num at hle
  -- `beurlingZeta B s = riemannZeta s` on `Re s > 1`
  have hzeta : ∀ s : ℂ, 1 < s.re → beurlingZeta B s = riemannZeta s := fun s hs => by
    rw [← measureDirichlet_beurlingSystemIntegerMeasure]
    change measureDirichlet ν s = riemannZeta s
    rw [hν_nat, measureDirichlet_nat_succ_eq_riemannZeta hs]
  -- Norm-preserving bijection `B.Label ≃ {p : ℕ // Nat.Prime p}`
  have hp_prime : ∀ l : B.Label, ∃ p : ℕ, Nat.Prime p ∧ B.labelNorm l = (p : ℝ) := by
    intro l
    obtain ⟨q, _, hq⟩ := hg_int {l}
    rw [B.intNorm_singleton] at hq
    have hq2 : 2 ≤ q := by
      have hl1 : (1 : ℝ) < (q : ℝ) := hq ▸ B.one_lt_labelNorm l
      have hqgt : 1 < q := by exact_mod_cast hl1
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
    obtain ⟨ga, hga, -⟩ := hm_uniq a (by omega)
    obtain ⟨gb, hgb, -⟩ := hm_uniq b (by omega)
    have hga0 : ga ≠ 0 := by
      intro h0; rw [h0, B.intNorm_zero] at hga
      have : 1 = a := by exact_mod_cast hga
      omega
    have hgb0 : gb ≠ 0 := by
      intro h0; rw [h0, B.intNorm_zero] at hgb
      have : 1 = b := by exact_mod_cast hgb
      omega
    have hprod : B.intNorm (ga + gb) = ((a * b : ℕ) : ℝ) := by
      rw [B.intNorm_add, hga, hgb]; push_cast; rfl
    have hsing : B.intNorm ({l} : B.Integer) = ((a * b : ℕ) : ℝ) := by rwa [B.intNorm_singleton]
    have heq_ms : ga + gb = {l} := (hm_uniq (a * b) (by omega)).unique hprod hsing
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
      exact Multiset.mem_singleton.mp (hms ▸ Multiset.mem_singleton_self l₁)
    · obtain ⟨g, hg, -⟩ := hm_uniq p hp.one_lt.le
      have hg0 : g ≠ 0 := by
        intro h0; rw [h0, B.intNorm_zero] at hg
        exact hp.ne_one (by exact_mod_cast hg.symm)
      obtain ⟨l, hl⟩ := Multiset.exists_mem_of_ne_zero hg0
      have hcons : g = l ::ₘ g.erase l := (Multiset.cons_erase hl).symm
      have hfac : (p : ℝ) = ((toP l : ℕ) : ℝ) * B.intNorm (g.erase l) := by
        rw [← hg]; conv_lhs => rw [hcons]
        rw [← Multiset.singleton_add, B.intNorm_add, B.intNorm_singleton, htoP_norm l]
      obtain ⟨b, _, hb⟩ := hg_int (g.erase l)
      rw [hb] at hfac
      have hdvd : (toP l : ℕ) ∣ p := ⟨b, by exact_mod_cast hfac⟩
      have heqp : (toP l : ℕ) = p :=
        (hp.eq_one_or_self_of_dvd _ hdvd).resolve_left (toP l).2.ne_one
      exact ⟨l, Subtype.ext heqp⟩
  exact ⟨hα, hβ, hν_beurling, hg_int, hm_uniq, hzeta,
    ⟨⟨Equiv.ofBijective toP hbij, fun l => htoP_norm l⟩⟩⟩

/-- The positive-integer counting measure determines a Beurling system and its prime labels. -/
theorem beurlingSystem_rigidity_of_integer_measure_eq
    (B : RHTower.BeurlingSystem) [Countable B.Label]
    (hν : beurlingSystemIntegerMeasure B =
      Measure.sum (fun k : ℕ => Measure.dirac ((k : ℝ) + 1))) :
    beurlingSystemIntegerMeasure B = beurlingIntegerMeasure riemannPrimeMeasure ∧
      (∀ g : B.Integer, ∃ m : ℕ, 1 ≤ m ∧ B.intNorm g = (m : ℝ)) ∧
      (∀ m : ℕ, 1 ≤ m → ∃! g : B.Integer, B.intNorm g = (m : ℝ)) ∧
      (∀ s : ℂ, 1 < s.re → beurlingZeta B s = riemannZeta s) ∧
      Nonempty {e : B.Label ≃ {p : ℕ // Nat.Prime p} //
        ∀ l : B.Label, B.labelNorm l = ((e l : ℕ) : ℝ)} := by
  have h := beurlingSystem_rigidity_of_measure_eq B (α := -1 / 2) (β := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by simpa using hν)
  exact h.2.2

/-- **Complete categorical rigidity of countable Beurling systems (theta-relation form).**
Let `B : RHTower.BeurlingSystem` have countable label type with `Σ_g |g|^{-2} < ∞`, and suppose
`beurlingTheta B` satisfies Riemann's degree-one theta relation. Then `α = -1/2`, `β = 1/2`,
`beurlingSystemIntegerMeasure B = beurlingIntegerMeasure riemannPrimeMeasure`, every positive
integer `m ≥ 1` occurs as `B.intNorm g` for a unique `g : B.Integer`, `beurlingZeta B s = riemannZeta s`
on `Re s > 1`, and `B.Label` admits a norm-preserving bijection onto the rational primes. -/
theorem beurlingSystem_rigidity_of_theta_relation
    (B : RHTower.BeurlingSystem) [Countable B.Label]
    {α β : ℂ}
    (hBsum2 : Summable fun g : B.Integer => 1 / B.intNorm g ^ 2)
    (htheta : ∀ x : ℝ, 0 < x →
      beurlingTheta B x =
        (x : ℂ) ^ (-(1 / 2 : ℂ)) * beurlingTheta B x⁻¹ + α + β * (x : ℂ) ^ (-(1 / 2 : ℂ))) :
    α = -1 / 2 ∧ β = 1 / 2 ∧
      beurlingSystemIntegerMeasure B = beurlingIntegerMeasure riemannPrimeMeasure ∧
      (∀ g : B.Integer, ∃ m : ℕ, 1 ≤ m ∧ B.intNorm g = (m : ℝ)) ∧
      (∀ m : ℕ, 1 ≤ m → ∃! g : B.Integer, B.intNorm g = (m : ℝ)) ∧
      (∀ s : ℂ, 1 < s.re → beurlingZeta B s = riemannZeta s) ∧
      Nonempty {e : B.Label ≃ {p : ℕ // Nat.Prime p} //
        ∀ l : B.Label, B.labelNorm l = ((e l : ℕ) : ℝ)} := by
  have hsupp : beurlingSystemIntegerMeasure B (Iio 1) = 0 :=
    beurlingSystemIntegerMeasure_Iio_one_eq_zero B
  have hmom : Integrable (fun u : ℝ => 1 / u ^ 2) (beurlingSystemIntegerMeasure B) := by
    have hsmul : beurlingSystemIntegerMeasure B =
        Measure.sum (fun g : B.Integer => (1 : ℝ≥0∞) • Measure.dirac (B.intNorm g)) := by
      unfold beurlingSystemIntegerMeasure; congr 1; ext g : 1; simp
    rw [hsmul]
    refine integrable_sum_dirac (fun _ => ENNReal.one_ne_top) (hBsum2.congr fun g => ?_)
    have hg0 : 0 < B.intNorm g := lt_of_lt_of_le zero_lt_one (B.one_le_intNorm g)
    rw [ENNReal.toReal_one, one_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  obtain ⟨hβα, hαim, hρ_nn, hν_eq⟩ := measure_eq_of_measureTheta_relation hsupp hmom
    (fun x hx => by
      rw [measureTheta_beurlingSystemIntegerMeasure, measureTheta_beurlingSystemIntegerMeasure]
      exact htheta x hx)
  exact beurlingSystem_rigidity_of_measure_eq B hβα hαim hρ_nn hν_eq

/-- **Complete categorical rigidity of countable Beurling systems (`|g|^{-3/2}` functional-equation form).**
Let `B : RHTower.BeurlingSystem` have countable label type with `Σ_g |g|^{-3/2} < ∞`, and suppose
`Γ_ℝ(s) beurlingZeta B s` satisfies Riemann's degree-one reflection law on `-1/2 ≤ Re s ≤ 3/2`.
Then `α = -1/2`, `β = 1/2`, `beurlingSystemIntegerMeasure B = beurlingIntegerMeasure riemannPrimeMeasure`,
every positive integer occurs as `B.intNorm g` for a unique `g : B.Integer`, `beurlingZeta B s = riemannZeta s`
on `Re s > 1`, and `B.Label` admits a norm-preserving bijection onto the rational primes. -/
theorem beurlingSystem_rigidity_of_completed_functional_equation_rpow
    (B : RHTower.BeurlingSystem) [Countable B.Label]
    {E : ℂ → ℂ} {α β : ℂ} {C : ℝ}
    (hBsum : Summable fun g : B.Integer => 1 / B.intNorm g ^ (3 / 2 : ℝ))
    (hE : DifferentiableOn ℂ E (verticalStrip (-1 / 2) (3 / 2)))
    (hdecay : ∀ s ∈ verticalStrip (-1 / 2) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2))
    (hR : ∀ s : ℂ, s.re = 3 / 2 →
      Complex.Gammaℝ s * beurlingZeta B s =
        E s + (α * Complex.Gammaℝ s + β * Complex.Gammaℝ (s - 1)))
    (hL : ∀ s : ℂ, s.re = -1 / 2 →
      Complex.Gammaℝ (1 - s) * beurlingZeta B (1 - s) =
        E s + (α * Complex.Gammaℝ s + β * Complex.Gammaℝ (s - 1))) :
    α = -1 / 2 ∧ β = 1 / 2 ∧
      beurlingSystemIntegerMeasure B = beurlingIntegerMeasure riemannPrimeMeasure ∧
      (∀ g : B.Integer, ∃ m : ℕ, 1 ≤ m ∧ B.intNorm g = (m : ℝ)) ∧
      (∀ m : ℕ, 1 ≤ m → ∃! g : B.Integer, B.intNorm g = (m : ℝ)) ∧
      (∀ s : ℂ, 1 < s.re → beurlingZeta B s = riemannZeta s) ∧
      Nonempty {e : B.Label ≃ {p : ℕ // Nat.Prime p} //
        ∀ l : B.Label, B.labelNorm l = ((e l : ℕ) : ℝ)} := by
  have hsupp : beurlingSystemIntegerMeasure B (Iio 1) = 0 :=
    beurlingSystemIntegerMeasure_Iio_one_eq_zero B
  have hmom : Integrable (fun u : ℝ => u ^ (-(3 / 2 : ℝ))) (beurlingSystemIntegerMeasure B) := by
    have hsmul : beurlingSystemIntegerMeasure B =
        Measure.sum (fun g : B.Integer => (1 : ℝ≥0∞) • Measure.dirac (B.intNorm g)) := by
      unfold beurlingSystemIntegerMeasure; congr 1; ext g : 1; simp
    rw [hsmul]
    refine integrable_sum_dirac (fun _ => ENNReal.one_ne_top) (hBsum.congr fun g => ?_)
    have hg0 : 0 < B.intNorm g := lt_of_lt_of_le zero_lt_one (B.one_le_intNorm g)
    rw [ENNReal.toReal_one, one_mul, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hg0.le _), Real.rpow_neg hg0.le, one_div]
  obtain ⟨hβα, hαim, hρ_nn, hν_eq⟩ := measure_eq_of_completed_functional_equation hsupp hmom hE hdecay
    (fun s hs => by rw [measureDirichlet_beurlingSystemIntegerMeasure]; exact hR s hs)
    (fun s hs => by rw [measureDirichlet_beurlingSystemIntegerMeasure]; exact hL s hs)
  exact beurlingSystem_rigidity_of_measure_eq B hβα hαim hρ_nn hν_eq

/-- **Complete categorical rigidity of countable Beurling systems (`∀ σ > 1` wrapper).** -/
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
      beurlingSystemIntegerMeasure B = beurlingIntegerMeasure riemannPrimeMeasure ∧
      (∀ g : B.Integer, ∃ m : ℕ, 1 ≤ m ∧ B.intNorm g = (m : ℝ)) ∧
      (∀ m : ℕ, 1 ≤ m → ∃! g : B.Integer, B.intNorm g = (m : ℝ)) ∧
      (∀ s : ℂ, 1 < s.re → beurlingZeta B s = riemannZeta s) ∧
      Nonempty {e : B.Label ≃ {p : ℕ // Nat.Prime p} //
        ∀ l : B.Label, B.labelNorm l = ((e l : ℕ) : ℝ)} :=
  beurlingSystem_rigidity_of_completed_functional_equation_rpow
    B (hBsum (3 / 2) (by norm_num)) hE hdecay hR hL

end GaloisForLFunctions.ArithmeticPositiveDuality
