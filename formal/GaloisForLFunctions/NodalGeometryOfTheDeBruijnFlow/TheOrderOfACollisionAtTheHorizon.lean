import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.TheHalfGaussAboveTheHorizon
import GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow.TheFrequencyIsAChaosLevel

/-!
# The order of a collision at the horizon

The frequency, read at the collision-free horizon, bounds the order of every zero below it.

Fix a height `X`, `α = ½ log(X/2π)`, and a time `t = t₀ + σ` above the horizon `2tα ≥ 6600/9991 + ε`. On the Gaussian window of the energy `F(σ)` at `(X, t₀)` the flow at time `t`
is a wave of frequency `α` and of amplitude comparable to `P = horizonAmp t X`, so

`F(σ) ≤ C P²`,  `F(σ) + D(σ)/α² ≥ c P²`    (`exists_energy_bounds`).

The wave might still spend all of its energy in the derivative. That is excluded by convexity: `2N(σ)` is the mean Taylor degree, so `F(rσ) ≥ r^{2N(σ)} F(σ)` for `r ≥ 1`
(`exp_frequency_mul_lineEnergy_le`), and `P` grows exactly like `e^{(r−1)σα²}`. Were `F(σ)` much smaller than `P²` the frequency would be too large for this growth. So `F(σ) ≥ c' P²` for
`Z = 2σα² ≥ Z₀` (`exists_lineEnergy_lower`).

The doubling inequality `F(rσ) ≥ r^k F(σ)` at a zero of order `k` then gives the **order bound** (`exists_order_le_at_horizon`)

`k ≤ (1 + δ) σ log²(X/2π)/2 + K`.

Taking `t₀ = 0` and the time `σ` of the horizon, a real zero of order `k` of `H₀` at height `X`, that is a zero of `ζ` on the line, has
`k ≤ (3300/9991 + ε) log X`, about `0.33 log X` (`exists_mult_le_log`). At positive time the same argument gives a bound that decreases linearly to the horizon: with `τ = t₀ log(X/2π)`,
the order is at most `(1 + δ)(6600/9991 + ε − τ) log(X/2π)/2 + K` (`exists_order_le_of_time`).
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn GaloisForLFunctions.ZeroConfigurationGeometry

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

noncomputable section

/-! ## Integrability of the energies -/

theorem norm_caloric_ofReal_le (g : ℝ → ℝ) (t x : ℝ) :
    ‖caloric g t (x : ℂ)‖ ≤ ∫ y : ℝ, |g y * Real.exp (t * y ^ 2)| := by
  unfold caloric
  refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae (Eventually.of_forall fun y => ?_)))
  have hre : (I * (x : ℂ) * (y : ℂ)).re = 0 := by simp
  simp only
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, hre, Real.exp_zero, mul_one]

/-- The energy density on the real line is integrable. -/
theorem integrable_energy {g : ℝ → ℝ} (hg : SuperGaussian g) (t : ℝ) {σ : ℝ} (hσ : 0 < σ) (x₀ : ℝ) :
    Integrable (fun x : ℝ => ‖caloric g t (x : ℂ)‖ ^ 2 * gaussDensity σ (x - x₀)) := by
  set B := ∫ y : ℝ, |g y * Real.exp (t * y ^ 2)| with hB
  have hcont : Continuous fun x : ℝ => caloric g t (x : ℂ) :=
    (differentiable_caloric hg t).continuous.comp Complex.continuous_ofReal
  have hG : Continuous fun x : ℝ => gaussDensity σ (x - x₀) := by
    unfold gaussDensity
    fun_prop
  refine ((integrable_gaussDensity_sub hσ x₀).const_mul (B ^ 2)).mono'
    ((hcont.norm.pow 2).mul hG).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  have hGpos := (gaussDensity_pos hσ (x - x₀)).le
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (norm_caloric_ofReal_le g t x) 2) hGpos

/-- The line energy at a real base point. -/
theorem lineEnergy_ofReal (g : ℝ → ℝ) (t₀ σ X : ℝ) :
    lineEnergy g t₀ (X : ℂ) σ = ∫ x : ℝ, ‖caloric g (t₀ + σ) (x : ℂ)‖ ^ 2 * gaussDensity σ (x - X) := by
  unfold lineEnergy
  simp

theorem gradEnergy_ofReal (g : ℝ → ℝ) (t₀ σ X : ℝ) :
    gradEnergy g t₀ (X : ℂ) σ =
      ∫ x : ℝ, ‖deriv (caloric g (t₀ + σ)) (x : ℂ)‖ ^ 2 * gaussDensity σ (x - X) := by
  unfold gradEnergy
  simp

/-- The derivative energy density on the real line is integrable. -/
theorem integrable_grad_energy {g : ℝ → ℝ} (hg : SuperGaussian g) (t : ℝ) {σ : ℝ} (hσ : 0 < σ) (x₀ : ℝ) :
    Integrable (fun x : ℝ => ‖deriv (caloric g t) (x : ℂ)‖ ^ 2 * gaussDensity σ (x - x₀)) := by
  refine (integrable_energy hg.mul_id t hσ x₀).congr (Eventually.of_forall fun x => ?_)
  simp only
  rw [deriv_caloric hg, norm_mul, Complex.norm_I, one_mul]

/-- Total mass and second moment of the Gaussian density. -/
theorem integral_gaussDensity_sub {σ : ℝ} (hσ : 0 < σ) (x₀ : ℝ) :
    ∫ x : ℝ, gaussDensity σ (x - x₀) = 1 := by
  rw [integral_sub_right_eq_self (μ := (volume : Measure ℝ)) (gaussDensity σ) x₀]
  have h := integral_gaussDensity_mul_pow_even hσ 0
  simpa using h

theorem integral_gaussDensity_sub_mul_sq {σ : ℝ} (hσ : 0 < σ) (x₀ : ℝ) :
    ∫ x : ℝ, gaussDensity σ (x - x₀) * (x - x₀) ^ 2 = 2 * σ := by
  rw [integral_sub_right_eq_self (μ := (volume : Measure ℝ)) (fun u => gaussDensity σ u * u ^ 2) x₀]
  have h := integral_gaussDensity_mul_pow_even hσ 1
  simpa using h

/-! ## Convexity of the energy -/

/-- **Convexity.** `F(rσ) ≥ r^{2N(σ)} F(σ)` for `r ≥ 1`: the mean Taylor degree controls the growth of the energy. -/
theorem exp_frequency_mul_lineEnergy_le {g : ℝ → ℝ} (hg : SuperGaussian g) (t₀ : ℝ) {σ r : ℝ} (hσ : 0 < σ) (hr : 1 ≤ r)
    (z₀ : ℂ) (hF : 0 < lineEnergy g t₀ z₀ σ) :
    Real.exp (2 * frequency g t₀ z₀ σ * Real.log r) * lineEnergy g t₀ z₀ σ ≤ lineEnergy g t₀ z₀ (r * σ) := by
  have hrpos : 0 < r := by linarith only [hr]
  have hrσ : 0 < r * σ := by positivity
  set F := lineEnergy g t₀ z₀ σ with hFdef
  set D := gradEnergy g t₀ z₀ σ with hDdef
  set nbar := 2 * frequency g t₀ z₀ σ with hnbar
  have hmean : nbar * F = 2 * σ * D := by
    rw [hnbar, frequency, ← hFdef, ← hDdef]
    field_simp
  have h1 := hasSum_lineEnergy hg t₀ hσ z₀
  have h2 := hasSum_two_mul_gradEnergy hg t₀ hσ z₀
  rw [← hFdef] at h1
  rw [← hDdef] at h2
  have hsum := (((h1.mul_left (1 - nbar * Real.log r)).add (h2.mul_left (Real.log r))).mul_left
    (Real.exp (nbar * Real.log r)))
  have hval : Real.exp (nbar * Real.log r) * ((1 - nbar * Real.log r) * F + Real.log r * (2 * σ * D)) =
      Real.exp (nbar * Real.log r) * F := by
    rw [← hmean]
    ring
  rw [hval] at hsum
  refine hasSum_le (fun n => ?_) hsum (hasSum_lineEnergy hg t₀ hrσ z₀)
  have hcoef : 0 ≤ fockCoeff (caloric g t₀) z₀ n * σ ^ n :=
    mul_nonneg (fockCoeff_nonneg _ _ _) (pow_pos hσ n).le
  have hpow : (r * σ) ^ n = r ^ n * σ ^ n := mul_pow _ _ _
  have hrn : r ^ n = Real.exp ((n : ℝ) * Real.log r) := by
    rw [mul_comm, Real.exp_mul, Real.exp_log hrpos, Real.rpow_natCast]
  have htang : Real.exp (nbar * Real.log r) * (1 + ((n : ℝ) - nbar) * Real.log r) ≤ r ^ n := by
    rw [hrn]
    have h3 := Real.add_one_le_exp (((n : ℝ) - nbar) * Real.log r)
    have h4 : Real.exp ((n : ℝ) * Real.log r) =
        Real.exp (nbar * Real.log r) * Real.exp (((n : ℝ) - nbar) * Real.log r) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [h4]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    linarith only [h3]
  rw [hpow]
  calc Real.exp (nbar * Real.log r) * ((1 - nbar * Real.log r) * (fockCoeff (caloric g t₀) z₀ n * σ ^ n) +
        Real.log r * ((n : ℝ) * (fockCoeff (caloric g t₀) z₀ n * σ ^ n)))
      = (Real.exp (nbar * Real.log r) * (1 + ((n : ℝ) - nbar) * Real.log r)) *
          (fockCoeff (caloric g t₀) z₀ n * σ ^ n) := by ring
    _ ≤ r ^ n * (fockCoeff (caloric g t₀) z₀ n * σ ^ n) := mul_le_mul_of_nonneg_right htang hcoef
    _ = fockCoeff (caloric g t₀) z₀ n * (r ^ n * σ ^ n) := by ring

/-! ## The energies at the horizon -/

/-- **The energies of the wave above the horizon.** With `P = horizonAmp (t₀ + σ) X`, one has `F(σ) ≤ C P²` and `c P² ≤ F(σ) + D(σ)/α²`. -/
theorem exists_energy_bounds {ε : ℝ} (hε : 0 < ε) :
    ∃ C c X₁ : ℝ, 0 < C ∧ 0 < c ∧ Real.exp 420 ≤ X₁ ∧ ∀ X : ℝ, X₁ ≤ X → ∀ t₀ σ : ℝ, 0 ≤ t₀ → 0 < σ →
      (t₀ + σ) * Real.log X ≤ 1 → 6600 / 9991 + ε ≤ 2 * (t₀ + σ) * (horizontalSlope X).re →
      lineEnergy riemannKernelReal t₀ (X : ℂ) σ ≤ C * horizonAmp (t₀ + σ) X ^ 2 ∧
      c * horizonAmp (t₀ + σ) X ^ 2 ≤ lineEnergy riemannKernelReal t₀ (X : ℂ) σ +
        gradEnergy riemannKernelReal t₀ (X : ℂ) σ / (horizontalSlope X).re ^ 2 := by
  obtain ⟨X₂, hX₂, hquad⟩ := exists_quadrature_bounds (half_pos hε)
  obtain ⟨G, hG, X₃, hX₃, hglobal⟩ := exists_riemannHeat_global_relative_bound
  obtain ⟨Δ₀, hΔ₀⟩ : ∃ Δ₀ : ℝ, Δ₀ = 16 * G + 13 := ⟨_, rfl⟩
  have hΔ₀13 : 13 ≤ Δ₀ := by rw [hΔ₀]; linarith only [hG]
  obtain ⟨X₁, hX₁def⟩ : ∃ X₁ : ℝ, X₁ = X₂ + X₃ + Real.exp 420 + 8 * (Δ₀ + 1) * (1 + 1 / ε) := ⟨_, rfl⟩
  have h1ε : 0 < 1 / ε := by positivity
  have hprod : 0 ≤ 8 * (Δ₀ + 1) * (1 + 1 / ε) := by positivity
  have he420 := Real.exp_pos 420
  refine ⟨12 * Real.exp (44 * Δ₀), 1 / (32 * Real.exp 44), X₁, by positivity, by positivity,
    by rw [hX₁def]; linarith only [hX₂, hX₃, hprod], ?_⟩
  intro X hX t₀ σ ht₀ hσ htL hc
  obtain ⟨t, htdef⟩ : ∃ t, t = t₀ + σ := ⟨_, rfl⟩
  rw [← htdef] at htL hc ⊢
  have hXX₂ : X₂ + X₃ + Real.exp 420 + 8 * (Δ₀ + 1) * (1 + 1 / ε) ≤ X := by rw [← hX₁def]; exact hX
  have hXe : Real.exp 420 ≤ X := by linarith only [hXX₂, hX₂, hX₃, hprod]
  have hX3 : X₃ ≤ X := by linarith only [hXX₂, hX₂, he420, hprod]
  have h420 : 420 ≤ Real.log X := by
    have h := Real.log_le_log he420 hXe
    rwa [Real.log_exp] at h
  have hXbig : 8 * (Δ₀ + 1) * (1 + 1 / ε) + 4000 ≤ X := by
    linarith only [hXX₂, hX₂, hX₃, he420]
  have hX₂big : X₂ + 8 * (Δ₀ + 1) * (1 + 1 / ε) ≤ X := by linarith only [hXX₂, hX₃, hX₂, he420]
  have hXpos : 0 < X := by linarith only [hXe, he420]
  set L := Real.log X with hL
  have hL0 : 0 < L := by linarith only [h420]
  have ht : 0 < t := by rw [htdef]; linarith only [ht₀, hσ]
  have ht8 : t ≤ 1 / 8 := by nlinarith only [h420, htL, ht]
  have hσt : σ ≤ t := by rw [htdef]; linarith only [ht₀]
  have hσL : σ * L ≤ 1 := (mul_le_mul_of_nonneg_right hσt hL0.le).trans htL
  have hσ4 : σ ≤ 1 / 4 := by nlinarith only [h420, hσL, hσ]
  set α := (horizontalSlope X).re with hα
  have hαL : 2 * α ≤ L := by
    rw [hα, horizontalSlope_re, hL]
    have h1 : X / (2 * Real.pi) ≤ X := div_le_self hXpos.le (by nlinarith only [Real.pi_gt_three])
    have h2 := Real.log_le_log (by positivity) h1
    linarith only [h2]
  have hα207 : 207 ≤ α := by
    rw [hα, horizontalSlope_re, Real.log_div hXpos.ne' (by positivity)]
    have h1 := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 * Real.pi)
    have h2 := Real.pi_lt_d2
    linarith only [h1, h2, h420]
  have hα0 : 0 < α := by linarith only [hα207]
  have hc0 : (6600 : ℝ) / 9991 ≥ 3 / 5 := by norm_num
  have hXc2 : 2 * t * α ≤ 1 := by nlinarith only [hαL, htL, ht]
  -- the facts at nearby heights
  have hnear (x : ℝ) (hx : |x - X| ≤ Δ₀ + 1) :
      X₂ ≤ x ∧ 400 ≤ x ∧ |x - X| ≤ X / 2 ∧ |X - x| ≤ x / 2 ∧
        6600 / 9991 + ε / 2 ≤ 2 * t * (horizontalSlope x).re ∧ 2 * t * (horizontalSlope x).re ≤ 1 ∧
        |(horizontalSlope x).re - α| ≤ 1 := by
    obtain ⟨hx1, hx2⟩ := abs_le.mp hx
    have hb1 : 8 * (Δ₀ + 1) ≤ 8 * (Δ₀ + 1) * (1 + 1 / ε) := by
      have : 0 ≤ 8 * (Δ₀ + 1) * (1 / ε) := by positivity
      linarith only [this]
    have hb2 : 8 * (Δ₀ + 1) * (1 / ε) ≤ 8 * (Δ₀ + 1) * (1 + 1 / ε) := by
      have : 0 ≤ 8 * (Δ₀ + 1) := by positivity
      nlinarith only [this]
    have hxge : X₂ ≤ x := by linarith only [hx1, hX₂big, hb1, hΔ₀13]
    have h1 : X / 2 ≤ x := by linarith only [hx1, hXbig, hb1, hΔ₀13]
    have hxpos : 0 < x := by linarith only [hXbig, hx1, hb1, hΔ₀13]
    have hmin : X / 2 ≤ min x X := le_min h1 (by linarith only [hXpos])
    have hminpos : 0 < min x X := lt_of_lt_of_le (by positivity) hmin
    have hslope : |(horizontalSlope x).re - α| ≤ 2 * (Δ₀ + 1) / X := by
      have h2 := abs_horizontalSlope_re_sub_le hXpos hxpos
      rw [min_comm] at h2
      refine h2.trans ?_
      rw [div_le_div_iff₀ hminpos hXpos]
      have h3 := mul_le_mul_of_nonneg_left hmin (by positivity : 0 ≤ 2 * (Δ₀ + 1))
      have h4 : |x - X| * X ≤ (Δ₀ + 1) * X := mul_le_mul_of_nonneg_right hx hXpos.le
      linarith only [h3, h4]
    have hsmall : 2 * (Δ₀ + 1) / X ≤ 1 := by
      rw [div_le_one hXpos]
      linarith only [hXbig, hb1, hΔ₀13]
    have hsmallε : 2 * (Δ₀ + 1) / X ≤ 2 * ε := by
      rw [div_le_iff₀ hXpos]
      have h5 : 8 * (Δ₀ + 1) * (1 / ε) ≤ X := by linarith only [hXbig, hb2]
      have h6 : ε * (8 * (Δ₀ + 1) * (1 / ε)) = 8 * (Δ₀ + 1) := by field_simp
      have h7 := mul_le_mul_of_nonneg_left h5 hε.le
      have : (0 : ℝ) ≤ Δ₀ + 1 := by linarith only [hΔ₀13]
      nlinarith only [h6, h7, this]
    refine ⟨hxge, ?_, ?_, ?_, ?_, ?_, hslope.trans hsmall⟩
    · linarith only [hx1, hXbig, hb1, hΔ₀13]
    · have : Δ₀ + 1 ≤ X / 2 := by linarith only [hXbig, hb1, hΔ₀13]
      exact hx.trans this
    · rw [abs_sub_comm]
      have : Δ₀ + 1 ≤ x / 2 := by linarith only [hXbig, hb1, hΔ₀13, hx1]
      exact hx.trans this
    · have h8 := (abs_le.mp (hslope.trans hsmallε)).1
      have h9 : 2 * t * (-(2 * ε)) ≤ 2 * t * ((horizontalSlope x).re - α) :=
        mul_le_mul_of_nonneg_left h8 (by positivity)
      have h10 : 2 * t * (2 * ε) ≤ ε / 2 := by nlinarith only [ht8, hε, ht]
      nlinarith only [h9, h10, hc]
    · rw [horizontalSlope_re]
      have h11 : x / (2 * Real.pi) ≤ X := by
        rw [div_le_iff₀ (by positivity)]
        have : x ≤ 2 * X := by linarith only [hx2, hXbig, hb1, hΔ₀13]
        nlinarith only [this, Real.pi_gt_three, hXpos]
      have h12 := Real.log_le_log (by positivity) h11
      have h13 : t * Real.log (x / (2 * Real.pi)) ≤ t * L := mul_le_mul_of_nonneg_left h12 ht.le
      linarith only [h13, htL]
  set P := horizonAmp t X with hP
  have hP0 : 0 ≤ P := horizonAmp_nonneg t X
  have hXdist : (400 : ℝ) ≤ X := by linarith only [hXbig, hprod]
  -- the upper bound
  have hpoint (x : ℝ) : ‖riemannHeat t (x : ℂ)‖ ^ 2 * gaussDensity σ (x - X) ≤
      12 * Real.exp (44 * Δ₀) * P ^ 2 * gaussDensity (2 * σ) (x - X) := by
    have hG2 := (gaussDensity_pos (by positivity : 0 < 2 * σ) (x - X)).le
    have hGσ := (gaussDensity_pos hσ (x - X)).le
    have hexpG := gaussDensity_mul_exp_le hσ (x - X)
    by_cases hx : |x - X| ≤ Δ₀
    · obtain ⟨h1, h2, h3, -, h5, h6, -⟩ := hnear x (by linarith only [hx])
      have hb := (hquad t x ht ht8 h1 h5 h6).1
      have hA := horizonAmp_height_le (x := X) (y := x) ht ht8 hXdist h3 (by linarith only [hc, hc0, hε])
        hXc2 (by linarith only [h5, hc0, hε]) h6
      have hexp : Real.exp (22 * |x - X|) ≤ Real.exp (22 * Δ₀) :=
        Real.exp_le_exp.mpr (by linarith only [hx])
      have hnorm : ‖riemannHeat t (x : ℂ)‖ ≤ 12 / 5 * (P * Real.exp (22 * Δ₀)) :=
        hb.trans (mul_le_mul_of_nonneg_left (hA.trans (mul_le_mul_of_nonneg_left hexp hP0)) (by norm_num))
      have hsq : ‖riemannHeat t (x : ℂ)‖ ^ 2 ≤ (12 / 5 * (P * Real.exp (22 * Δ₀))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      have hexp2 : Real.exp (22 * Δ₀) ^ 2 = Real.exp (44 * Δ₀) := by
        rw [← Real.exp_nat_mul]
        congr 1
        push_cast
        ring
      have hGle : gaussDensity σ (x - X) ≤ 2 * gaussDensity (2 * σ) (x - X) := by
        refine le_trans ?_ hexpG
        have : 1 ≤ Real.exp ((x - X) ^ 2 / (8 * σ)) := Real.one_le_exp (by positivity)
        nlinarith only [this, hGσ]
      have hEP : 0 ≤ P ^ 2 * Real.exp (44 * Δ₀) := by positivity
      calc ‖riemannHeat t (x : ℂ)‖ ^ 2 * gaussDensity σ (x - X)
          ≤ (12 / 5 * (P * Real.exp (22 * Δ₀))) ^ 2 * (2 * gaussDensity (2 * σ) (x - X)) :=
            mul_le_mul hsq hGle hGσ (by positivity)
        _ = 288 / 25 * (P ^ 2 * Real.exp (44 * Δ₀)) * gaussDensity (2 * σ) (x - X) := by
            rw [← hexp2]
            ring
        _ ≤ 12 * (P ^ 2 * Real.exp (44 * Δ₀)) * gaussDensity (2 * σ) (x - X) := by
            refine mul_le_mul_of_nonneg_right ?_ hG2
            linarith only [hEP]
        _ = _ := by ring
    · have hx' := not_le.mp hx
      set a := |x - X| with ha
      have ha0 : 0 ≤ a := abs_nonneg _
      have hgl := hglobal X hX3 t ht.le ht8 htL x 0 (by simp)
      have hpt : (x : ℂ) + I * ((0 : ℝ) : ℂ) = (x : ℂ) := by simp
      rw [hpt] at hgl
      have hanchor := norm_xiLine_sixteen_le_horizonAmp ht (by linarith only [hXbig, hprod])
        (by linarith only [hc, hc0, hε]) hXc2
      rw [← hα, ← hP] at hanchor
      have hnorm : ‖riemannHeat t (x : ℂ)‖ ≤ P * Real.exp (17 * α + 208 + G * L * (1 + a)) := by
        refine hgl.trans ?_
        rw [Real.exp_add]
        calc ‖xiLine X 16‖ * Real.exp (G * L * (1 + a))
            ≤ (P * Real.exp (17 * α + 208)) * Real.exp (G * L * (1 + a)) :=
              mul_le_mul_of_nonneg_right hanchor (Real.exp_pos _).le
          _ = _ := by ring
      have hsq : ‖riemannHeat t (x : ℂ)‖ ^ 2 ≤ P ^ 2 * Real.exp (2 * (17 * α + 208 + G * L * (1 + a))) := by
        have := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
        refine this.trans (le_of_eq ?_)
        rw [mul_pow, ← Real.exp_nat_mul]
        push_cast
        rfl
      -- the Gaussian beats the global growth
      have hsqa : (x - X) ^ 2 = a ^ 2 := by rw [ha, sq_abs]
      have hsplit : gaussDensity σ (x - X) =
          gaussDensity σ (x - X) * Real.exp (a ^ 2 / (8 * σ)) * Real.exp (-(a ^ 2 / (8 * σ))) := by
        rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
      have hGle : gaussDensity σ (x - X) ≤ 2 * gaussDensity (2 * σ) (x - X) * Real.exp (-(a ^ 2 / (8 * σ))) := by
        rw [hsqa] at hexpG
        rw [hsplit]
        exact mul_le_mul_of_nonneg_right hexpG (Real.exp_pos _).le
      have hexpo : 2 * (17 * α + 208 + G * L * (1 + a)) - a ^ 2 / (8 * σ) ≤ 0 := by
        have h1 : a ^ 2 * L / 8 ≤ a ^ 2 / (8 * σ) := by
          rw [le_div_iff₀ (by positivity)]
          have h2 : a ^ 2 * (σ * L) ≤ a ^ 2 * 1 := mul_le_mul_of_nonneg_left hσL (by positivity)
          nlinarith only [h2]
        have h3 : 144 + 16 * G * (1 + a) ≤ a ^ 2 := by
          have h4 : Δ₀ < a := hx'
          have h5 : 16 * G + 13 < a := by rw [← hΔ₀]; exact h4
          have h6 : 0 < a - 16 * G - 13 := by linarith only [h5]
          nlinarith only [h5, h6, hG, mul_pos h6 (by linarith only [h5, hG] : 0 < a)]
        have h7 := mul_le_mul_of_nonneg_right h3 hL0.le
        have h8 : 2 * (17 * α + 208 + G * L * (1 + a)) ≤ L * (18 + 2 * G * (1 + a)) := by
          nlinarith only [hαL, h420]
        nlinarith only [h1, h7, h8]
      have hexpo1 : Real.exp (2 * (17 * α + 208 + G * L * (1 + a))) * Real.exp (-(a ^ 2 / (8 * σ))) ≤ 1 := by
        rw [← Real.exp_add]
        apply Real.exp_le_one_iff.mpr
        linarith only [hexpo]
      have hE1 : 1 ≤ Real.exp (44 * Δ₀) := Real.one_le_exp (by linarith only [hΔ₀13])
      have hP2 : 0 ≤ P ^ 2 * gaussDensity (2 * σ) (x - X) := by positivity
      calc ‖riemannHeat t (x : ℂ)‖ ^ 2 * gaussDensity σ (x - X)
          ≤ (P ^ 2 * Real.exp (2 * (17 * α + 208 + G * L * (1 + a)))) *
              (2 * gaussDensity (2 * σ) (x - X) * Real.exp (-(a ^ 2 / (8 * σ)))) :=
            mul_le_mul hsq hGle hGσ (by positivity)
        _ = 2 * (P ^ 2 * gaussDensity (2 * σ) (x - X)) *
              (Real.exp (2 * (17 * α + 208 + G * L * (1 + a))) * Real.exp (-(a ^ 2 / (8 * σ)))) := by ring
        _ ≤ 2 * (P ^ 2 * gaussDensity (2 * σ) (x - X)) * 1 :=
            mul_le_mul_of_nonneg_left hexpo1 (by positivity)
        _ ≤ 12 * Real.exp (44 * Δ₀) * P ^ 2 * gaussDensity (2 * σ) (x - X) := by
            nlinarith only [mul_le_mul_of_nonneg_right hE1 hP2, hP2]
  have hcal : caloric riemannKernelReal t = riemannHeat t := caloric_riemannKernel t
  have hFeq : lineEnergy riemannKernelReal t₀ (X : ℂ) σ =
      ∫ x : ℝ, ‖riemannHeat t (x : ℂ)‖ ^ 2 * gaussDensity σ (x - X) := by
    rw [lineEnergy_ofReal, ← htdef, hcal]
  have hDeq : gradEnergy riemannKernelReal t₀ (X : ℂ) σ =
      ∫ x : ℝ, ‖deriv (riemannHeat t) (x : ℂ)‖ ^ 2 * gaussDensity σ (x - X) := by
    rw [gradEnergy_ofReal, ← htdef, hcal]
  have hIF : Integrable fun x : ℝ => ‖riemannHeat t (x : ℂ)‖ ^ 2 * gaussDensity σ (x - X) := by
    have := integrable_energy riemannKernel_superGaussian t hσ X
    rwa [hcal] at this
  have hID : Integrable fun x : ℝ => ‖deriv (riemannHeat t) (x : ℂ)‖ ^ 2 * gaussDensity σ (x - X) := by
    have := integrable_grad_energy riemannKernel_superGaussian t hσ X
    rwa [hcal] at this
  constructor
  · rw [hFeq]
    have hmaj : Integrable fun x : ℝ => 12 * Real.exp (44 * Δ₀) * P ^ 2 * gaussDensity (2 * σ) (x - X) :=
      (integrable_gaussDensity_sub (by positivity) X).const_mul _
    have h := integral_mono hIF hmaj hpoint
    rw [integral_const_mul, integral_gaussDensity_sub (by positivity), mul_one] at h
    exact h
  · -- the lower bound
    have hlower (x : ℝ) : 1 / (16 * Real.exp 44) * P ^ 2 * (gaussDensity σ (x - X) - gaussDensity σ (x - X) * (x - X) ^ 2) ≤
        ‖riemannHeat t (x : ℂ)‖ ^ 2 * gaussDensity σ (x - X) +
          ‖deriv (riemannHeat t) (x : ℂ)‖ ^ 2 * gaussDensity σ (x - X) / α ^ 2 := by
      have hGσ := (gaussDensity_pos hσ (x - X)).le
      have hW0 : 0 ≤ ‖riemannHeat t (x : ℂ)‖ ^ 2 + ‖deriv (riemannHeat t) (x : ℂ)‖ ^ 2 / α ^ 2 := by positivity
      have hrhs : ‖riemannHeat t (x : ℂ)‖ ^ 2 * gaussDensity σ (x - X) +
          ‖deriv (riemannHeat t) (x : ℂ)‖ ^ 2 * gaussDensity σ (x - X) / α ^ 2 =
          (‖riemannHeat t (x : ℂ)‖ ^ 2 + ‖deriv (riemannHeat t) (x : ℂ)‖ ^ 2 / α ^ 2) * gaussDensity σ (x - X) := by
        ring
      rw [hrhs, show gaussDensity σ (x - X) - gaussDensity σ (x - X) * (x - X) ^ 2 =
        (1 - (x - X) ^ 2) * gaussDensity σ (x - X) by ring, ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ hGσ
      by_cases hx : |x - X| ≤ 1
      · obtain ⟨h1, h2, -, h4, h5, h6, h7⟩ := hnear x (by linarith only [hx, hΔ₀13])
        have hb := (hquad t x ht ht8 h1 h5 h6).2
        have hA := horizonAmp_height_le (x := x) (y := X) ht ht8 h2 h4 (by linarith only [h5, hc0, hε]) h6
          (by linarith only [hc, hc0, hε]) hXc2
        have hA' : P ≤ horizonAmp t x * Real.exp 22 := by
          refine hA.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (horizonAmp_nonneg _ _))
          rw [abs_sub_comm]
          linarith only [hx]
        have hP2 : P ^ 2 ≤ horizonAmp t x ^ 2 * Real.exp 44 := by
          have := pow_le_pow_left₀ hP0 hA' 2
          refine this.trans (le_of_eq ?_)
          rw [mul_pow, ← Real.exp_nat_mul]
          norm_num
        have hαx : α / 2 ≤ (horizontalSlope x).re := by
          have := (abs_le.mp h7).1
          linarith only [this, hα207]
        have hαx0 : 0 < (horizontalSlope x).re := by linarith only [hαx, hα0]
        have hdiv : ‖deriv (riemannHeat t) (x : ℂ)‖ ^ 2 / (horizontalSlope x).re ^ 2 ≤
            4 * (‖deriv (riemannHeat t) (x : ℂ)‖ ^ 2 / α ^ 2) := by
          rw [show 4 * (‖deriv (riemannHeat t) (x : ℂ)‖ ^ 2 / α ^ 2) =
            ‖deriv (riemannHeat t) (x : ℂ)‖ ^ 2 / (α / 2) ^ 2 by field_simp; ring]
          exact div_le_div_of_nonneg_left (by positivity) (by positivity)
            (pow_le_pow_left₀ (by positivity) hαx 2)
        have hH0 : 0 ≤ ‖riemannHeat t (x : ℂ)‖ ^ 2 := by positivity
        have hamp : horizonAmp t x ^ 2 ≤
            16 * (‖riemannHeat t (x : ℂ)‖ ^ 2 + ‖deriv (riemannHeat t) (x : ℂ)‖ ^ 2 / α ^ 2) := by
          linarith only [hb, hdiv, hH0]
        have hE := Real.exp_pos 44
        have hfinal : P ^ 2 ≤ 16 * Real.exp 44 *
            (‖riemannHeat t (x : ℂ)‖ ^ 2 + ‖deriv (riemannHeat t) (x : ℂ)‖ ^ 2 / α ^ 2) := by
          refine hP2.trans ?_
          have := mul_le_mul_of_nonneg_right hamp hE.le
          linarith only [this]
        have hone : 1 - (x - X) ^ 2 ≤ 1 := by nlinarith only [sq_nonneg (x - X)]
        have hc' : 0 ≤ 1 / (16 * Real.exp 44) * P ^ 2 := by positivity
        calc 1 / (16 * Real.exp 44) * P ^ 2 * (1 - (x - X) ^ 2)
            ≤ 1 / (16 * Real.exp 44) * P ^ 2 * 1 := mul_le_mul_of_nonneg_left hone hc'
          _ = P ^ 2 / (16 * Real.exp 44) := by ring
          _ ≤ _ := by
              rw [div_le_iff₀ (by positivity)]
              linarith only [hfinal]
      · have hx' := not_le.mp hx
        have hneg : 1 - (x - X) ^ 2 ≤ 0 := by
          have : 1 ≤ (x - X) ^ 2 := by
            rw [← sq_abs]
            nlinarith only [hx']
          linarith only [this]
        have hc' : 0 ≤ 1 / (16 * Real.exp 44) * P ^ 2 := by positivity
        exact (mul_nonpos_of_nonneg_of_nonpos hc' hneg).trans hW0
    have hGi := integrable_gaussDensity_sub hσ X
    have hGi2 : Integrable fun x : ℝ => gaussDensity σ (x - X) * (x - X) ^ 2 :=
      (integrable_gaussDensity_mul_pow hσ 2).comp_sub_right X
    have hint := integral_mono ((hGi.sub hGi2).const_mul (1 / (16 * Real.exp 44) * P ^ 2))
      (hIF.add (hID.div_const (α ^ 2))) hlower
    simp only [Pi.sub_apply, Pi.add_apply] at hint
    rw [integral_const_mul, integral_sub hGi hGi2, integral_gaussDensity_sub hσ,
      integral_gaussDensity_sub_mul_sq hσ, integral_add hIF (hID.div_const _), integral_div,
      ← hFeq, ← hDeq] at hint
    have hhalf : 1 / 2 ≤ 1 - 2 * σ := by linarith only [hσ4]
    have hc' : 0 ≤ 1 / (16 * Real.exp 44) * P ^ 2 := by positivity
    refine le_trans (le_of_eq ?_) ((mul_le_mul_of_nonneg_left hhalf hc').trans hint)
    field_simp
    ring

/-- The package used below: the growth of the energy from scale `σ` to `rσ`, the lower bound for the sum of the energies, and the positivity of the amplitude. -/
theorem exists_energy_package {ε : ℝ} (hε : 0 < ε) :
    ∃ C c X₁ : ℝ, 0 < C ∧ 0 < c ∧ Real.exp 420 ≤ X₁ ∧ ∀ X : ℝ, X₁ ≤ X → ∀ t₀ σ : ℝ, 0 ≤ t₀ → 0 < σ →
      (t₀ + 4 / 3 * σ) * Real.log X ≤ 1 → 6600 / 9991 + ε ≤ 2 * (t₀ + σ) * (horizontalSlope X).re →
      0 < horizonAmp (t₀ + σ) X ∧ 207 ≤ (horizontalSlope X).re ∧
      (∀ r : ℝ, 1 ≤ r → r ≤ 4 / 3 → lineEnergy riemannKernelReal t₀ (X : ℂ) (r * σ) ≤
        C * Real.exp ((r - 1) * (2 * σ * (horizontalSlope X).re ^ 2)) * horizonAmp (t₀ + σ) X ^ 2) ∧
      c * horizonAmp (t₀ + σ) X ^ 2 ≤ lineEnergy riemannKernelReal t₀ (X : ℂ) σ +
        gradEnergy riemannKernelReal t₀ (X : ℂ) σ / (horizontalSlope X).re ^ 2 := by
  obtain ⟨C, c, X₁, hC, hc, hX₁, hen⟩ := exists_energy_bounds hε
  refine ⟨C * Real.exp 9, c, X₁, by positivity, hc, hX₁, ?_⟩
  intro X hX t₀ σ ht₀ hσ htL hcc
  have hXe : Real.exp 420 ≤ X := hX₁.trans hX
  have he420 := Real.exp_pos 420
  have hXpos : 0 < X := by linarith only [hXe, he420]
  have h420 : 420 ≤ Real.log X := by
    have h := Real.log_le_log he420 hXe
    rwa [Real.log_exp] at h
  have hL0 : 0 < Real.log X := by linarith only [h420]
  set α := (horizontalSlope X).re with hα
  have hαL : 2 * α ≤ Real.log X := by
    rw [hα, horizontalSlope_re]
    have h1 : X / (2 * Real.pi) ≤ X := div_le_self hXpos.le (by nlinarith only [Real.pi_gt_three])
    have h2 := Real.log_le_log (by positivity) h1
    linarith only [h2]
  have hα207 : 207 ≤ α := by
    rw [hα, horizontalSlope_re, Real.log_div hXpos.ne' (by positivity)]
    have h1 := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 * Real.pi)
    have h2 := Real.pi_lt_d2
    linarith only [h1, h2, h420]
  have hα0 : 0 < α := by linarith only [hα207]
  have hc0 : (6600 : ℝ) / 9991 ≥ 3 / 5 := by norm_num
  have ht1 : (t₀ + σ) * Real.log X ≤ 1 := by
    refine le_trans (mul_le_mul_of_nonneg_right ?_ hL0.le) htL
    linarith only [hσ]
  have hX200 : 200 ≤ X := by linarith only [hXe, Real.add_one_le_exp (420 : ℝ), hX₁]
  have hP : 0 < horizonAmp (t₀ + σ) X := by
    unfold horizonAmp
    refine mul_pos (norm_pos_iff.mpr ?_) (Real.exp_pos _)
    unfold xiLine
    rw [xiLine_point]
    refine xi_ne_zero_of_one_lt_re ?_
    simp only [add_re, ofReal_re, mul_re, I_re, I_im, ofReal_im, zero_mul, mul_zero, sub_zero]
    rw [← hα]
    linarith only [hcc, hc0, hε]
  refine ⟨hP, hα207, ?_, (hen X hX t₀ σ ht₀ hσ ht1 hcc).2⟩
  intro r hr1 hr2
  have hrσ : 0 < r * σ := by positivity
  have hle : t₀ + r * σ ≤ t₀ + 4 / 3 * σ := by
    have := mul_le_mul_of_nonneg_right hr2 hσ.le
    linarith only [this]
  have hge : t₀ + σ ≤ t₀ + r * σ := by
    have := mul_le_mul_of_nonneg_right hr1 hσ.le
    linarith only [this]
  have htL2 : (t₀ + r * σ) * Real.log X ≤ 1 := (mul_le_mul_of_nonneg_right hle hL0.le).trans htL
  have hcc2 : 6600 / 9991 + ε ≤ 2 * (t₀ + r * σ) * α := by
    have := mul_le_mul_of_nonneg_right hge hα0.le
    linarith only [this, hcc]
  have h1 := (hen X hX t₀ (r * σ) ht₀ hrσ htL2 hcc2).1
  have hhi : 2 * (t₀ + r * σ) * α ≤ 1 := by
    have hpos : 0 ≤ t₀ + r * σ := by linarith only [ht₀, hrσ]
    have := mul_le_mul_of_nonneg_left hαL hpos
    linarith only [this, htL2]
  have h2 := horizonAmp_time_le (t₁ := t₀ + σ) (t₂ := t₀ + r * σ) (X := X) hge hX200
    (by rw [← hα]; linarith only [hcc, hc0, hε]) (by rw [← hα]; exact hhi)
  rw [← hα] at h2
  have hdiff : t₀ + r * σ - (t₀ + σ) = (r - 1) * σ := by ring
  rw [hdiff] at h2
  have hσα : σ * α ≤ 1 / 2 := by
    have h3 : σ ≤ t₀ + r * σ := by
      have := mul_le_mul_of_nonneg_right hr1 hσ.le
      linarith only [this, ht₀]
    have := mul_le_mul_of_nonneg_right h3 hα0.le
    linarith only [this, hhi]
  have hsmall : 2 * (26 * ((r - 1) * σ * α)) ≤ 9 := by
    have h4 : (r - 1) * (σ * α) ≤ 1 / 3 * (1 / 2) :=
      mul_le_mul (by linarith only [hr2]) hσα (by positivity) (by norm_num)
    nlinarith only [h4]
  have hsq := pow_le_pow_left₀ (horizonAmp_nonneg _ _) h2 2
  have hexp2 : (horizonAmp (t₀ + σ) X * Real.exp ((r - 1) * σ * α ^ 2 + 26 * ((r - 1) * σ * α))) ^ 2 ≤
      horizonAmp (t₀ + σ) X ^ 2 * (Real.exp ((r - 1) * (2 * σ * α ^ 2)) * Real.exp 9) := by
    rw [mul_pow, ← Real.exp_nat_mul, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    push_cast
    nlinarith only [hsmall]
  calc lineEnergy riemannKernelReal t₀ (X : ℂ) (r * σ)
      ≤ C * horizonAmp (t₀ + r * σ) X ^ 2 := h1
    _ ≤ C * (horizonAmp (t₀ + σ) X ^ 2 * (Real.exp ((r - 1) * (2 * σ * α ^ 2)) * Real.exp 9)) :=
        mul_le_mul_of_nonneg_left (hsq.trans hexp2) hC.le
    _ = _ := by ring

/-- `F(σ) > 0` as soon as `F(σ)` and `D(σ)` do not both vanish. -/
theorem lineEnergy_pos_of_sum_pos {g : ℝ → ℝ} (hg : SuperGaussian g) (t₀ : ℝ) {σ : ℝ} (hσ : 0 < σ) (z₀ : ℂ)
    (h : lineEnergy g t₀ z₀ σ ≠ 0 ∨ gradEnergy g t₀ z₀ σ ≠ 0) : 0 < lineEnergy g t₀ z₀ σ := by
  have h1 := hasSum_lineEnergy hg t₀ hσ z₀
  have h2 := hasSum_two_mul_gradEnergy hg t₀ hσ z₀
  have hnn (n : ℕ) : 0 ≤ fockCoeff (caloric g t₀) z₀ n * σ ^ n :=
    mul_nonneg (fockCoeff_nonneg _ _ _) (pow_pos hσ n).le
  have hF0 : 0 ≤ lineEnergy g t₀ z₀ σ := h1.nonneg hnn
  refine lt_of_le_of_ne hF0 fun heq => ?_
  have hall : ∀ n, fockCoeff (caloric g t₀) z₀ n * σ ^ n = 0 := by
    rw [← heq] at h1
    have := (hasSum_zero_iff_of_nonneg hnn).mp h1
    exact fun n => congrFun this n
  have hD : 2 * σ * gradEnergy g t₀ z₀ σ = 0 := by
    refine h2.unique ?_
    have : (fun n : ℕ => (n : ℝ) * (fockCoeff (caloric g t₀) z₀ n * σ ^ n)) = fun _ => 0 := by
      funext n
      rw [hall n, mul_zero]
    rw [this]
    exact hasSum_zero
  have hD0 : gradEnergy g t₀ z₀ σ = 0 := by
    rcases mul_eq_zero.mp hD with h3 | h3
    · exact absurd h3 (by positivity)
    · exact h3
  rcases h with h3 | h3
  · exact h3 heq.symm
  · exact h3 hD0

/-! ## The energy of the wave is not all in the derivative -/

/-- **The self-improving lower bound.** A wave with too little energy in `F(σ)` would have too large a frequency to be compatible with the exact growth `e^{(r−1)Z}` of the amplitude. So `F(σ) ≥ y₀ P²`, for `Z = 2σα² ≥ Z₀`. -/
theorem exists_lineEnergy_lower {ε : ℝ} (hε : 0 < ε) :
    ∃ C y₀ Z₀ X₁ : ℝ, 0 < C ∧ 0 < y₀ ∧ 0 < Z₀ ∧ Real.exp 420 ≤ X₁ ∧ ∀ X : ℝ, X₁ ≤ X → ∀ t₀ σ : ℝ, 0 ≤ t₀ → 0 < σ →
      (t₀ + 4 / 3 * σ) * Real.log X ≤ 1 → 6600 / 9991 + ε ≤ 2 * (t₀ + σ) * (horizontalSlope X).re →
      Z₀ ≤ 2 * σ * (horizontalSlope X).re ^ 2 →
      0 < horizonAmp (t₀ + σ) X ∧ 207 ≤ (horizontalSlope X).re ∧
      (∀ r : ℝ, 1 ≤ r → r ≤ 4 / 3 → lineEnergy riemannKernelReal t₀ (X : ℂ) (r * σ) ≤
        C * Real.exp ((r - 1) * (2 * σ * (horizontalSlope X).re ^ 2)) * horizonAmp (t₀ + σ) X ^ 2) ∧
      y₀ * horizonAmp (t₀ + σ) X ^ 2 ≤ lineEnergy riemannKernelReal t₀ (X : ℂ) σ := by
  obtain ⟨C, c, X₁, hC, hc, hX₁, hpack⟩ := exists_energy_package hε
  obtain ⟨K, hKdef⟩ : ∃ K, K = Real.log C := ⟨_, rfl⟩
  refine ⟨C, 3 * c / 32, max (16 / c) (3 * |K| + 1), X₁, hC, by positivity,
    lt_max_of_lt_left (by positivity), hX₁, ?_⟩
  intro X hX t₀ σ ht₀ hσ htL hcc hZ
  obtain ⟨hP, hα207, hup, hlow⟩ := hpack X hX t₀ σ ht₀ hσ htL hcc
  refine ⟨hP, hα207, hup, ?_⟩
  set α := (horizontalSlope X).re with hα
  have hα0 : 0 < α := by linarith only [hα207]
  set P := horizonAmp (t₀ + σ) X with hPdef
  set F := lineEnergy riemannKernelReal t₀ (X : ℂ) σ with hFdef
  set D := gradEnergy riemannKernelReal t₀ (X : ℂ) σ with hDdef
  set Z := 2 * σ * α ^ 2 with hZdef
  have hZ1 : 16 / c ≤ Z := (le_max_left _ _).trans hZ
  have hZ2 : 3 * |K| + 1 ≤ Z := (le_max_right _ _).trans hZ
  have hZpos : 0 < Z := by positivity
  have hP2 : 0 < P ^ 2 := by positivity
  by_contra hcon
  have hF_lt : F < 3 * c / 32 * P ^ 2 := not_le.mp hcon
  -- the derivative carries the energy
  have hDbig : c / 2 * P ^ 2 ≤ D / α ^ 2 := by
    have h1 : 3 * c / 32 * P ^ 2 ≤ c / 2 * P ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith only [hc]) hP2.le
    have h2 : c * P ^ 2 = c / 2 * P ^ 2 + c / 2 * P ^ 2 := by ring
    linarith only [hlow, hF_lt, h1, h2]
  have hDpos : 0 < D := by
    have h1 : 0 < c / 2 * P ^ 2 := by positivity
    have h2 := h1.trans_le hDbig
    have h3 : 0 < α ^ 2 := by positivity
    by_contra hn
    have h4 : D ≤ 0 := not_lt.mp hn
    have h5 : D / α ^ 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg h4 h3.le
    linarith only [h2, h5]
  have hFpos : 0 < F := lineEnergy_pos_of_sum_pos riemannKernel_superGaussian t₀ hσ (X : ℂ) (Or.inr hDpos.ne')
  -- the convexity at the scale `(4/3) σ`
  have hconv := exp_frequency_mul_lineEnergy_le riemannKernel_superGaussian t₀ hσ
    (by norm_num : (1 : ℝ) ≤ 4 / 3) (X : ℂ) hFpos
  have hup43 := hup (4 / 3) (by norm_num) le_rfl
  rw [← hFdef] at hconv
  have hℓ : 1 / 4 ≤ Real.log (4 / 3) := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 4 / 3)
    norm_num at this ⊢
    linarith only [this]
  set y := F / P ^ 2 with hy
  have hypos : 0 < y := by positivity
  have hylt : y < 3 * c / 32 := by
    rw [hy, div_lt_iff₀ hP2]
    exact hF_lt
  have hFy : F = y * P ^ 2 := by
    rw [hy]
    field_simp
  -- the mean degree is large
  have hmean : Z * (c / 2) / y ≤ 2 * frequency riemannKernelReal t₀ (X : ℂ) σ := by
    have h1 : 2 * frequency riemannKernelReal t₀ (X : ℂ) σ = Z * (D / α ^ 2 / P ^ 2) / y := by
      unfold frequency
      rw [← hFdef, ← hDdef, hFy, hZdef]
      field_simp
    rw [h1]
    refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hZpos.le) hypos.le
    rw [le_div_iff₀ hP2]
    exact hDbig
  -- taking logarithms
  have hchain : Real.exp (2 * frequency riemannKernelReal t₀ (X : ℂ) σ * Real.log (4 / 3)) * y ≤
      C * Real.exp ((4 / 3 - 1) * Z) := by
    have h1 := hconv.trans hup43
    rw [hFy] at h1
    have h2 := (mul_le_mul_iff_left₀ hP2).mp (by
      calc Real.exp (2 * frequency riemannKernelReal t₀ (X : ℂ) σ * Real.log (4 / 3)) * y * P ^ 2
          = Real.exp (2 * frequency riemannKernelReal t₀ (X : ℂ) σ * Real.log (4 / 3)) * (y * P ^ 2) := by ring
        _ ≤ _ := h1)
    exact h2
  have hlog := Real.log_le_log (by positivity) hchain
  rw [Real.log_mul (Real.exp_pos _).ne' hypos.ne', Real.log_exp, Real.log_mul hC.ne' (Real.exp_pos _).ne',
    Real.log_exp, ← hKdef] at hlog
  have hlogy := Real.one_sub_inv_le_log_of_pos hypos
  set w := y⁻¹ with hw
  have hwpos : 0 < w := by positivity
  have hmean' : Z * (c / 2) * w ≤ 2 * frequency riemannKernelReal t₀ (X : ℂ) σ := by
    rw [hw, ← div_eq_mul_inv]
    exact hmean
  have hmul : Z * (c / 2) * w * (1 / 4) ≤
      2 * frequency riemannKernelReal t₀ (X : ℂ) σ * Real.log (4 / 3) :=
    mul_le_mul hmean' hℓ (by norm_num) ((by positivity : 0 ≤ Z * (c / 2) * w).trans hmean')
  -- the contradiction
  have hKabs : K ≤ |K| := le_abs_self K
  have hkey : (Z * c / 8 - 1) * w ≤ K + Z / 3 := by
    have h1 : (4 / 3 - 1 : ℝ) * Z = Z / 3 := by ring
    rw [h1] at hlog
    nlinarith only [hmul, hlog, hlogy]
  have hZc : 16 ≤ Z * c := by
    have := (div_le_iff₀ hc).mp hZ1
    linarith only [this]
  have hlower : Z * c / 16 ≤ Z * c / 8 - 1 := by linarith only [hZc]
  have hmid : Z * c / 16 * w ≤ 2 * Z / 3 := by
    have h1 := mul_le_mul_of_nonneg_right hlower hwpos.le
    have h2 : K + Z / 3 ≤ 2 * Z / 3 := by linarith only [hKabs, hZ2, abs_nonneg K]
    linarith only [h1, hkey, h2]
  have hw32 : c * w ≤ 32 / 3 := by
    have h1 : Z * (c * w / 16) ≤ Z * (2 / 3) := by
      calc Z * (c * w / 16) = Z * c / 16 * w := by ring
        _ ≤ 2 * Z / 3 := hmid
        _ = Z * (2 / 3) := by ring
    have h2 := le_of_mul_le_mul_left h1 hZpos
    linarith only [h2]
  have hwy : w * y = 1 := by
    rw [hw]
    exact inv_mul_cancel₀ hypos.ne'
  have hfinal : c * w * y < 32 / 3 * (3 * c / 32) := by
    calc c * w * y ≤ 32 / 3 * y := mul_le_mul_of_nonneg_right hw32 hypos.le
      _ < 32 / 3 * (3 * c / 32) := by
        apply mul_lt_mul_of_pos_left hylt
        norm_num
  have hval : c * w * y = c := by
    rw [mul_assoc, hwy, mul_one]
  rw [hval] at hfinal
  have hend : 32 / 3 * (3 * c / 32) = c := by ring
  rw [hend] at hfinal
  exact lt_irrefl _ hfinal

/-! ## The order bound -/

/-- **The order of a zero against the heat time to the horizon.** If `t₀ + σ` lies above the horizon, a real zero of order at least `k` of `H_{t₀}` at height `X` has
`k ≤ (1 + δ) 2σα² + K`, `2σα² = σ log²(X/2π)/2`. -/
theorem exists_order_le_at_horizon {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδ3 : δ ≤ 1 / 3) :
    ∃ K Z₀ X₁ : ℝ, 0 ≤ K ∧ 0 < Z₀ ∧ Real.exp 420 ≤ X₁ ∧ ∀ X : ℝ, X₁ ≤ X → ∀ t₀ σ : ℝ, 0 ≤ t₀ → 0 < σ →
      (t₀ + 4 / 3 * σ) * Real.log X ≤ 1 → 6600 / 9991 + ε ≤ 2 * (t₀ + σ) * (horizontalSlope X).re →
      Z₀ ≤ 2 * σ * (horizontalSlope X).re ^ 2 → ∀ k : ℕ,
      (∀ n < k, iteratedDeriv n (riemannHeat t₀) (X : ℂ) = 0) →
      (k : ℝ) ≤ (1 + δ) * (2 * σ * (horizontalSlope X).re ^ 2) + K := by
  obtain ⟨C, y₀, Z₀, X₁, hC, hy₀, hZ₀, hX₁, hpack⟩ := exists_lineEnergy_lower hε
  obtain ⟨K₁, hK₁⟩ : ∃ K₁, K₁ = Real.log C - Real.log y₀ := ⟨_, rfl⟩
  refine ⟨(1 + δ) * |K₁| / δ, Z₀, X₁, by positivity, hZ₀, hX₁, ?_⟩
  intro X hX t₀ σ ht₀ hσ htL hcc hZ k hvan
  obtain ⟨hP, -, hup, hlow⟩ := hpack X hX t₀ σ ht₀ hσ htL hcc hZ
  set α := (horizontalSlope X).re with hα
  set P := horizonAmp (t₀ + σ) X with hPdef
  set F := lineEnergy riemannKernelReal t₀ (X : ℂ) σ with hFdef
  set Z := 2 * σ * α ^ 2 with hZdef
  have hP2 : 0 < P ^ 2 := by positivity
  have hFpos : 0 < F := lt_of_lt_of_le (by positivity) hlow
  set r := 1 + δ with hr
  have hr1 : 1 ≤ r := by linarith only [hδ]
  have hrpos : 0 < r := by linarith only [hδ]
  have hr43 : r ≤ 4 / 3 := by linarith only [hδ3]
  have hvan' : ∀ n < k, iteratedDeriv n (caloric riemannKernelReal t₀) (X : ℂ) = 0 := by
    rw [caloric_riemannKernel]
    exact hvan
  have hdouble := pow_mul_lineEnergy_le riemannKernel_superGaussian t₀ hσ hr1 hvan'
  rw [← hFdef] at hdouble
  have hup' := hup r hr1 hr43
  have hchain : r ^ k * y₀ ≤ C * Real.exp ((r - 1) * Z) := by
    have h1 : r ^ k * (y₀ * P ^ 2) ≤ C * Real.exp ((r - 1) * Z) * P ^ 2 :=
      (mul_le_mul_of_nonneg_left hlow (by positivity)).trans (hdouble.trans hup')
    have h2 : r ^ k * y₀ * P ^ 2 ≤ C * Real.exp ((r - 1) * Z) * P ^ 2 := by
      calc r ^ k * y₀ * P ^ 2 = r ^ k * (y₀ * P ^ 2) := by ring
        _ ≤ _ := h1
    exact (mul_le_mul_iff_left₀ hP2).mp h2
  have hlog := Real.log_le_log (by positivity) hchain
  rw [Real.log_mul (pow_ne_zero _ hrpos.ne') hy₀.ne', Real.log_pow, Real.log_mul hC.ne' (Real.exp_pos _).ne',
    Real.log_exp] at hlog
  have hrm : r - 1 = δ := by rw [hr]; ring
  rw [hrm] at hlog
  have hkδ : (k : ℝ) * Real.log r ≤ K₁ + δ * Z := by
    rw [hK₁]
    linarith only [hlog]
  have hlogr : δ / r ≤ Real.log r := by
    have := Real.one_sub_inv_le_log_of_pos hrpos
    refine le_trans (le_of_eq ?_) this
    rw [hr]
    field_simp
    ring
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h1 : (k : ℝ) * (δ / r) ≤ |K₁| + δ * Z := by
    have h2 := mul_le_mul_of_nonneg_left hlogr hk0
    linarith only [h2, hkδ, le_abs_self K₁]
  have h3 : (k : ℝ) = (k : ℝ) * (δ / r) * (r / δ) := by
    field_simp
  have h4 : (k : ℝ) * (δ / r) * (r / δ) ≤ (|K₁| + δ * Z) * (r / δ) :=
    mul_le_mul_of_nonneg_right h1 (by positivity)
  have h5 : (|K₁| + δ * Z) * (r / δ) = r * Z + r * |K₁| / δ := by
    field_simp
    ring
  rw [h3]
  linarith only [h4, h5]

/-- A time at the scale `0.9/log(X/2π)` is admissible for the order bound, at large height. -/
theorem mul_log_le_one_of_le {s X : ℝ} (hX : 0 < X) (hα100 : 100 ≤ (horizontalSlope X).re)
    (hs0 : 0 ≤ s) (hs : s * (2 * (horizontalSlope X).re) ≤ 9 / 10) : s * Real.log X ≤ 1 := by
  have h1 : Real.log X ≤ 2 * (horizontalSlope X).re + 6 := by
    rw [horizontalSlope_re, Real.log_div hX.ne' (by positivity)]
    have h2 := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 * Real.pi)
    have h3 := Real.pi_lt_d2
    linarith only [h2, h3]
  have h2 : s * Real.log X ≤ s * (2 * (horizontalSlope X).re + 6) := mul_le_mul_of_nonneg_left h1 hs0
  have h3 : s * 200 ≤ s * (2 * (horizontalSlope X).re) :=
    mul_le_mul_of_nonneg_left (by linarith only [hα100]) hs0
  nlinarith only [h2, h3, hs]

/-- **The order bound decreases linearly to the horizon.** With `τ = t₀ · 2α = t₀ log(X/2π)` at most `6600/9991 + ε`, a real zero of `H_{t₀}` of order at least `k` at height `X` has
`k ≤ (1 + δ)(6600/9991 + ε − τ) α + K`, `α = ½ log(X/2π)`. -/
theorem exists_order_le_of_time {ε δ : ℝ} (hε : 0 < ε) (hε100 : ε ≤ 1 / 100) (hδ : 0 < δ) (hδ3 : δ ≤ 1 / 3) :
    ∃ K X₁ : ℝ, 0 ≤ K ∧ 0 < X₁ ∧ ∀ X : ℝ, X₁ ≤ X → ∀ t₀ : ℝ, 0 ≤ t₀ →
      t₀ * (2 * (horizontalSlope X).re) ≤ 6600 / 9991 + ε → ∀ k : ℕ,
      (∀ n < k, iteratedDeriv n (riemannHeat t₀) (X : ℂ) = 0) →
      (k : ℝ) ≤ (1 + δ) * ((6600 / 9991 + ε - t₀ * (2 * (horizontalSlope X).re)) * (horizontalSlope X).re) + K := by
  obtain ⟨K₀, Z₀, X₁, hK₀, hZ₀, hX₁, horder⟩ := exists_order_le_at_horizon hε hδ hδ3
  have h2π : 0 < 2 * Real.pi := by positivity
  have he420 := Real.exp_pos 420
  refine ⟨K₀ + 2 * Z₀, max X₁ (2 * Real.pi * Real.exp (2 * max 100 (300 * Z₀))), by positivity,
    lt_max_of_lt_left (he420.trans_le hX₁), ?_⟩
  intro X hX t₀ ht₀ hτ k hvan
  have hXX₁ : X₁ ≤ X := (le_max_left _ _).trans hX
  have hXe : 2 * Real.pi * Real.exp (2 * max 100 (300 * Z₀)) ≤ X := (le_max_right _ _).trans hX
  have hXpos : 0 < X := he420.trans_le (hX₁.trans hXX₁)
  set α := (horizontalSlope X).re with hα
  have hαbig : max 100 (300 * Z₀) ≤ α := by
    have h1 : Real.exp (2 * max 100 (300 * Z₀)) ≤ X / (2 * Real.pi) := by
      rw [le_div_iff₀ h2π]
      linarith only [hXe]
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at h2
    rw [hα, horizontalSlope_re]
    linarith only [h2]
  have hα100 : 100 ≤ α := (le_max_left _ _).trans hαbig
  have hαZ : 300 * Z₀ ≤ α := (le_max_right _ _).trans hαbig
  have hα0 : 0 < α := by linarith only [hα100]
  set τ := t₀ * (2 * α) with hτdef
  have hτ0 : 0 ≤ τ := by positivity
  set s := (6600 / 9991 + ε - τ) / (2 * α) with hs
  have hs0 : 0 ≤ s := div_nonneg (by linarith only [hτ]) (by positivity)
  have hs2 : s * (2 * α) = 6600 / 9991 + ε - τ := by
    rw [hs]
    field_simp
  set u := Z₀ / (2 * α ^ 2) with hu
  have hu0 : 0 < u := by positivity
  have hu2 : u * (2 * α ^ 2) = Z₀ := by
    rw [hu]
    field_simp
  set σ := s + u with hσ
  have hσ0 : 0 < σ := by positivity
  have hσα : 2 * (t₀ + σ) * α = τ + s * (2 * α) + u * (2 * α) := by
    rw [hσ, hτdef]
    ring
  have hu1 : u * (2 * α) * α = Z₀ := by
    rw [← hu2]
    ring
  have hu3 : u * (2 * α) ≤ 1 / 300 := by
    have h1 : u * (2 * α) * α ≤ 1 / 300 * α := by
      rw [hu1]
      linarith only [hαZ]
    have h2 : α * (u * (2 * α)) ≤ α * (1 / 300) := by linarith only [h1]
    exact le_of_mul_le_mul_left h2 hα0
  have hup0 : 0 ≤ u * (2 * α) := by positivity
  have hhor : 6600 / 9991 + ε ≤ 2 * (t₀ + σ) * α := by
    rw [hσα, hs2]
    linarith only [hup0]
  have hZ : Z₀ ≤ 2 * σ * α ^ 2 := by
    have h1 : 2 * σ * α ^ 2 = s * (2 * α ^ 2) + u * (2 * α ^ 2) := by
      rw [hσ]
      ring
    rw [h1, hu2]
    have : 0 ≤ s * (2 * α ^ 2) := by positivity
    linarith only [this]
  have hL : (t₀ + 4 / 3 * σ) * Real.log X ≤ 1 := by
    refine mul_log_le_one_of_le hXpos (by rwa [← hα]) (by positivity) ?_
    rw [← hα]
    have h1 : (t₀ + 4 / 3 * σ) * (2 * α) = τ + 4 / 3 * (s * (2 * α)) + 4 / 3 * (u * (2 * α)) := by
      rw [hσ, hτdef]
      ring
    rw [h1, hs2]
    have hc : (6600 : ℝ) / 9991 ≤ 661 / 1000 := by norm_num
    linarith only [hc, hε100, hτ0, hu3]
  have hk := horder X hXX₁ t₀ σ ht₀ hσ0 hL hhor hZ k hvan
  rw [← hα] at hk
  have hval : 2 * σ * α ^ 2 = (6600 / 9991 + ε - τ) * α + Z₀ := by
    have h1 : 2 * σ * α ^ 2 = (s * (2 * α)) * α + u * (2 * α ^ 2) := by
      rw [hσ]
      ring
    rw [h1, hs2, hu2]
  rw [hval] at hk
  have hδ2 : (1 + δ) * Z₀ ≤ 2 * Z₀ := by nlinarith only [hδ3, hZ₀]
  nlinarith only [hk, hδ2]

/-- **The multiplicity bound from the horizon.** A real zero of `H₀` of order at least `k` at height `X`, that is a zero of `ξ` on the critical line, has
`k ≤ (3300/9991 + ε) log X`; here `3300/9991 ≈ 0.3303`. -/
theorem exists_mult_le_log {ε : ℝ} (hε : 0 < ε) :
    ∃ X₁ : ℝ, 0 < X₁ ∧ ∀ X : ℝ, X₁ ≤ X → ∀ k : ℕ,
      (∀ n < k, iteratedDeriv n (riemannHeat 0) (X : ℂ) = 0) → (k : ℝ) ≤ (3300 / 9991 + ε) * Real.log X := by
  set ε₁ := min (ε / 2) (1 / 100) with hε₁
  set δ := min (ε / 2) (1 / 3) with hδ
  have hε₁0 : 0 < ε₁ := by positivity
  have hδ0 : 0 < δ := by positivity
  have hε₁1 : ε₁ ≤ ε / 2 := min_le_left _ _
  have hε₁2 : ε₁ ≤ 1 / 100 := min_le_right _ _
  have hδ1 : δ ≤ ε / 2 := min_le_left _ _
  have hδ2 : δ ≤ 1 / 3 := min_le_right _ _
  obtain ⟨K, X₁, hK, hX₁, hlaw⟩ := exists_order_le_of_time hε₁0 hε₁2 hδ0 hδ2
  refine ⟨max X₁ (max (Real.exp (2 * K / ε)) (2 * Real.pi)), lt_max_of_lt_left hX₁, ?_⟩
  intro X hX k hvan
  have hXX₁ : X₁ ≤ X := (le_max_left _ _).trans hX
  have hXe : Real.exp (2 * K / ε) ≤ X := ((le_max_left _ _).trans (le_max_right _ _)).trans hX
  have hX2π : 2 * Real.pi ≤ X := ((le_max_right _ _).trans (le_max_right _ _)).trans hX
  have hXpos : 0 < X := by linarith only [hX2π, Real.pi_pos]
  have hlog : 2 * K / ε ≤ Real.log X := by
    have := Real.log_le_log (Real.exp_pos _) hXe
    rwa [Real.log_exp] at this
  have hk := hlaw X hXX₁ 0 le_rfl (by
    rw [zero_mul]
    positivity) k hvan
  rw [zero_mul, sub_zero] at hk
  set α := (horizontalSlope X).re with hα
  have hαL : 2 * α ≤ Real.log X := by
    rw [hα, horizontalSlope_re]
    have h1 : X / (2 * Real.pi) ≤ X := div_le_self hXpos.le (by nlinarith only [Real.pi_gt_three])
    have h2 := Real.log_le_log (by positivity) h1
    linarith only [h2]
  have hα0 : 0 ≤ α := by
    rw [hα, horizontalSlope_re]
    have h1 : 1 ≤ X / (2 * Real.pi) := by
      rw [le_div_iff₀ (by positivity)]
      linarith only [hX2π]
    have := Real.log_nonneg h1
    linarith only [this]
  have hLpos : 0 ≤ Real.log X := by linarith only [hαL, hα0]
  have hKε : K ≤ ε / 2 * Real.log X := by
    have h1 := (div_le_iff₀ hε).mp hlog
    linarith only [h1]
  have hcoef : (1 + δ) * (6600 / 9991 + ε₁) ≤ 2 * (3300 / 9991) + 9 / 10 * ε := by
    have hc : (6600 : ℝ) / 9991 ≤ 661 / 1000 := by norm_num
    have h1 : δ * (6600 / 9991 + ε₁) ≤ ε / 2 * (7 / 10) :=
      mul_le_mul hδ1 (by linarith only [hc, hε₁2]) (by positivity) (by positivity)
    have h2 : (2 : ℝ) * (3300 / 9991) = 6600 / 9991 := by norm_num
    rw [h2]
    nlinarith only [h1, hε₁1, hε]
  have hmain : (1 + δ) * ((6600 / 9991 + ε₁) * α) ≤ (3300 / 9991 + 9 / 20 * ε) * Real.log X := by
    have h1 : (1 + δ) * ((6600 / 9991 + ε₁) * α) = ((1 + δ) * (6600 / 9991 + ε₁)) * α := by ring
    rw [h1]
    have h2 := mul_le_mul_of_nonneg_right hcoef hα0
    have h3 : (2 * (3300 / 9991) + 9 / 10 * ε) * α = (3300 / 9991 + 9 / 20 * ε) * (2 * α) := by ring
    have h4 : (3300 / 9991 + 9 / 20 * ε) * (2 * α) ≤ (3300 / 9991 + 9 / 20 * ε) * Real.log X :=
      mul_le_mul_of_nonneg_left hαL (by positivity)
    linarith only [h2, h3, h4]
  have hlast : (3300 / 9991 + 9 / 20 * ε) * Real.log X + ε / 2 * Real.log X ≤ (3300 / 9991 + ε) * Real.log X := by
    have : 0 ≤ ε * Real.log X := by positivity
    nlinarith only [this]
  linarith only [hk, hmain, hKε, hlast]

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
