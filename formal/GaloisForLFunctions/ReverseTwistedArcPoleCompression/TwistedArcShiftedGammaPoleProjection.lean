import GaloisForLFunctions.RHTower.PrimeBlindPoleCuspIdentity
import GaloisForLFunctions.RHTower.TruncatedRiemannKernelWeilEnergy
import GaloisForLFunctions.RHTower.ShiftedGammaNumericalRange

/-!
# Twisted-Arc Shifted-Gamma Pole Projection and Truncated Riemann-Kernel Parity Split

This module establishes the first leg of the **Reverse Twisted-Arc Duality on the $2\times 2$
Pole-Compression Matrix** (Mechanism 4):

1. **Shifted-Gamma Numerical Range Lower Bound**:
   For every shift $\sigma \in (0, 1)$ and frequency $x \in \mathbb{R}$, the real part of the
   shifted Gamma jump symbol $r(x + i\sigma)$ (`wallSymbol σ x`) is bounded below uniformly in
   frequency by $-\kappa_\sigma$ (`neg_gammaShiftKappa_le_re_wallSymbol`), where
   $\kappa_\sigma = \sum_{n\ge 0} \frac{2\sigma^2}{(n+1)((n+1)^2 - \sigma^2)} \ge 0$.

2. **Logarithmic-to-Multiplicative Pole Projection and Prime-Blind Cusp Identity**:
   Under the isometric half-line substitution $y = e^u$ mapping $F : \mathbb{R} \to \mathbb{R}$ to
   $f(y) = F(\log y) y^{-1/2}$ on $(0, \infty)$, the two pole functionals $\int_0^\infty f(y)\,dy$
   and $\int_0^\infty \frac{f(y)}{y}\,dy$ coincide unconditionally with the two exponential
   projections $\int_{\mathbb{R}} F(u) e^{u/2}\,du$ and $\int_{\mathbb{R}} F(u) e^{-u/2}\,du$.
   Consequently, the prime-blind cusp functional $C A_f(0) = \Psi_f(0)$ equals the bilinear
   pole product $2(\int_{\mathbb{R}} F(u) e^{u/2}\,du)(\int_{\mathbb{R}} F(u) e^{-u/2}\,du)$, and
   its twisted-arc defect $(1 - e^{-\epsilon})\Psi_f(0)$ vanishes linearly as $\epsilon \to 0^+$.

3. **Truncated $\Xi$-Divisible Riemann-Kernel Zero Annihilation and Parity Involution**:
   Every finite derivative combination $F_a = \sum_{i \le K} a_i \Phi^{(i)}$ (`kernelComb a`)
   vanishes at $\gamma_\rho$ and $\overline{\gamma_\rho}$ for every nontrivial zero
   $\rho \in \text{zetaZeroConfig.carrier}$ (`paperFT_kernelComb_at_zero`), its smooth cutoff
   truncation `nearRadicalTest L a` obeys the explicit tail-leakage bound
   `norm_W_nearRadicalTest_le`, and the reflection $u \mapsto -u$ acts on its cusp series by the
   exact parity involution `parityCoeff x` (`cuspSeries_kernelPoly_neg`).
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.ReverseTwistedArcPoleCompression

open GaloisForLFunctions.RHTower
open _root_.RHTower
open Zeta23

/-! ### 1. Shifted-Gamma Numerical Range Lower Bound -/

/-- For every shift `σ ∈ (0, 1)` and frequency `x : ℝ`, the shifted Gamma numerical-range constant
`gammaShiftKappa σ` is nonnegative, the real part of `wallSymbol σ x` is bounded below uniformly by
`-gammaShiftKappa σ`, and `(wallSymbol σ x).re` expands into the two-sided real Gauss series. -/
theorem shifted_gamma_numerical_range_and_gauss_series
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (x : ℝ) :
    0 ≤ gammaShiftKappa σ ∧
    -gammaShiftKappa σ ≤ (wallSymbol σ x).re ∧
    (wallSymbol σ x).re =
      (∑' n : ℕ, (1 / ((n : ℝ) + 1) -
        ((1 - σ) + n) / (((1 - σ) + n) ^ (2 : ℕ) + x ^ (2 : ℕ)))) +
      (∑' n : ℕ, (1 / ((n : ℝ) + 1) -
        ((1 + σ) + n) / (((1 + σ) + n) ^ (2 : ℕ) + x ^ (2 : ℕ)))) :=
  ⟨gammaShiftKappa_nonneg hσ0 hσ1,
   neg_gammaShiftKappa_le_re_wallSymbol hσ0 hσ1 x,
   re_wallSymbol_eq_tsum hσ0 hσ1 x⟩

/-! ### 2. Logarithmic-to-Multiplicative Pole Projection and Cusp Identity -/

/-- The logarithmic-to-multiplicative transform mapping a profile `F : ℝ → ℝ` on the logarithmic
line to `f(y) = F(log y) y^{-1/2}` on `(0, ∞)`. -/
def logToMultProfile (F : ℝ → ℝ) (y : ℝ) : ℝ :=
  F (Real.log y) * y ^ (-(1 / 2 : ℝ))

/-- Change of variables `y = exp u` for real integrals on the positive half-line
(one-dimensional Jacobian formula for the injective map `exp : ℝ → (0, ∞)`). -/
private theorem integral_Ioi_eq_integral_exp_mul (g : ℝ → ℝ) :
    ∫ y in Ioi (0 : ℝ), g y = ∫ u : ℝ, Real.exp u * g (Real.exp u) := by
  rw [← Real.range_exp, ← Set.image_univ]
  simpa only [Measure.restrict_univ, abs_of_pos (Real.exp_pos _), smul_eq_mul] using
    (MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      (s := Set.univ) MeasurableSet.univ
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
      Real.exp_injective.injOn g)

/-- **Mass of the dilation autocorrelation, integrable form**: for measurable `f` integrable on
`(0, ∞)` against `dy` and `dy/y`, `∫_0^∞ A_f = (∫_0^∞ f)(∫_0^∞ f(y)/y dy)`.  Tonelli bounds the
double integral of `|f(y) f(ry)|` by `‖f‖₁ ‖f/y‖₁`, which licenses the Fubini swap. -/
theorem integral_Ioi_dilationAutocorr_of_integrable {f : ℝ → ℝ} (hfm : Measurable f)
    (hf1 : IntegrableOn f (Ioi 0)) (hf2 : IntegrableOn (fun y => f y / y) (Ioi 0)) :
    ∫ r in Ioi (0 : ℝ), dilationAutocorr f r =
      (∫ y in Ioi (0 : ℝ), f y) * ∫ y in Ioi (0 : ℝ), f y / y := by
  unfold dilationAutocorr
  have hmeas : AEStronglyMeasurable (Function.uncurry fun r y => f y * f (r * y))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    Measurable.aestronglyMeasurable (by
      exact (hfm.comp measurable_snd).mul (hfm.comp (measurable_fst.mul measurable_snd)))
  have hint : Integrable (Function.uncurry fun r y => f y * f (r * y))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    refine (integrable_prod_iff' hmeas).2 ⟨?_, ?_⟩
    · -- each `r`-section is a rescaled copy of `f`
      refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun y hy => ?_)
      have hsec : IntegrableOn (fun r => f (r * y)) (Ioi 0) :=
        (integrableOn_Ioi_comp_mul_right_iff f 0 hy).2 (by simpa using hf1)
      exact Integrable.const_mul hsec (f y)
    · -- the section norms are `‖f y / y‖ ‖f‖₁`, integrable in `y`
      have hnorm : ∀ y ∈ Ioi (0 : ℝ), ∫ r in Ioi (0 : ℝ), ‖f y * f (r * y)‖ =
          ‖f y / y‖ * ∫ w in Ioi (0 : ℝ), ‖f w‖ := by
        intro y hy
        have hy0 : (0 : ℝ) < y := hy
        simp only [norm_mul]
        rw [integral_const_mul, integral_comp_mul_right_Ioi (fun w => ‖f w‖) 0 hy0, zero_mul,
          smul_eq_mul, norm_div, Real.norm_of_nonneg hy0.le]
        ring
      refine Integrable.congr
        (Integrable.mul_const (Integrable.norm hf2) (∫ w in Ioi (0 : ℝ), ‖f w‖)) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      exact (hnorm y hy).symm
  rw [integral_integral_swap hint]
  have hin : ∀ y ∈ Ioi (0 : ℝ), ∫ r in Ioi (0 : ℝ), f y * f (r * y) =
      f y / y * ∫ w in Ioi (0 : ℝ), f w := by
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    rw [integral_const_mul, integral_comp_mul_right_Ioi (fun w => f w) 0 hy0, zero_mul,
      smul_eq_mul]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hin, integral_mul_const]
  ring

/-- **Cusp value of the twisted kernel, integrable form**: `C A_f(0) = 2 (∫ f)(∫ f(y)/y dy)` for
measurable `f` integrable on `(0, ∞)` against `dy` and `dy/y`. -/
theorem halfLineCosTransform_dilationAutocorr_zero_of_integrable {f : ℝ → ℝ}
    (hfm : Measurable f) (hf1 : IntegrableOn f (Ioi 0))
    (hf2 : IntegrableOn (fun y => f y / y) (Ioi 0)) :
    halfLineCosTransform (dilationAutocorr f) 0 =
      2 * (∫ y in Ioi (0 : ℝ), f y) * ∫ y in Ioi (0 : ℝ), f y / y := by
  unfold halfLineCosTransform
  simp only [mul_zero, Real.cos_zero, mul_one]
  rw [integral_Ioi_dilationAutocorr_of_integrable hfm hf1 hf2]
  ring

/-- Under `y = exp u`, the pole functional `∫_{y > 0} f(y) / y dy` for
`f(y) = F(log y) y^{-1/2}` equals the lower-pole projection `∫_ℝ F(u) exp(-u/2) du`. -/
theorem integral_Ioi_logToMultProfile_div_self (F : ℝ → ℝ) :
    ∫ y in Ioi (0 : ℝ), logToMultProfile F y / y =
      ∫ u : ℝ, F u * Real.exp (-(u / 2)) := by
  rw [integral_Ioi_eq_integral_exp_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  dsimp only [logToMultProfile]
  rw [Real.log_exp, ← Real.exp_mul, mul_div_assoc', mul_div_cancel_left₀ _ (Real.exp_pos u).ne',
    show u * -(1 / 2 : ℝ) = -(u / 2) by ring]

/-- Under `y = exp u`, the pole functional `∫_{y > 0} f(y) dy` for
`f(y) = F(log y) y^{-1/2}` equals the upper-pole projection `∫_ℝ F(u) exp(u/2) du`. -/
theorem integral_Ioi_logToMultProfile (F : ℝ → ℝ) :
    ∫ y in Ioi (0 : ℝ), logToMultProfile F y =
      ∫ u : ℝ, F u * Real.exp (u / 2) := by
  rw [integral_Ioi_eq_integral_exp_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  dsimp only [logToMultProfile]
  rw [Real.log_exp, ← Real.exp_mul, mul_left_comm, ← Real.exp_add,
    show u + u * -(1 / 2 : ℝ) = u / 2 by ring]

/-- **Prime-Blind Cusp-to-Pole Identity in Logarithmic Coordinates**:
For any measurable profile `F : ℝ → ℝ` whose multiplicative avatar `f = logToMultProfile F`
is integrable with respect to `dy` and `dy/y` on `(0, ∞)`, both the half-line cosine transform at
the cusp `halfLineCosTransform (dilationAutocorr f) 0` and the cosine dilation kernel at zero
`cosDilationKernel f 0` equal `2 * (∫ F(u) e^{u/2} du) * (∫ F(u) e^{-u/2} du)`. -/
theorem prime_blind_cusp_pole_identity_log_profile {F : ℝ → ℝ} (hF : Measurable F)
    (hf1 : IntegrableOn (logToMultProfile F) (Ioi 0))
    (hf2 : IntegrableOn (fun y => logToMultProfile F y / y) (Ioi 0)) :
    halfLineCosTransform (dilationAutocorr (logToMultProfile F)) 0 =
      2 * (∫ u : ℝ, F u * Real.exp (u / 2)) * (∫ u : ℝ, F u * Real.exp (-(u / 2))) ∧
    cosDilationKernel (logToMultProfile F) 0 =
      2 * (∫ u : ℝ, F u * Real.exp (u / 2)) * (∫ u : ℝ, F u * Real.exp (-(u / 2))) := by
  rw [← integral_Ioi_logToMultProfile F, ← integral_Ioi_logToMultProfile_div_self F]
  exact ⟨halfLineCosTransform_dilationAutocorr_zero_of_integrable
           ((hF.comp Real.measurable_log).mul (measurable_id.pow_const _)) hf1 hf2,
         cosDilationKernel_zero_eq _⟩

/-- The twisted-arc cusp defect `(1 - exp(-ε)) * P` is bounded in absolute value by `ε * |P|` for
every `ε ≥ 0` and tends to `0` as `ε → 0`. -/
theorem twisted_arc_cusp_defect_bound_and_tendsto (P : ℝ) :
    (∀ ε : ℝ, 0 ≤ ε → |(1 - Real.exp (-ε)) * P| ≤ ε * |P|) ∧
    Tendsto (fun ε : ℝ => (1 - Real.exp (-ε)) * P) (𝓝 0) (𝓝 0) := by
  refine ⟨fun ε hε => ?_, ?_⟩
  · rw [abs_mul]
    have h1 : Real.exp (-ε) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h2 : 1 - ε ≤ Real.exp (-ε) := by
      have := Real.add_one_le_exp (-ε)
      linarith
    have habs : |1 - Real.exp (-ε)| ≤ ε := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    exact mul_le_mul_of_nonneg_right habs (abs_nonneg P)
  · have hcont : Continuous (fun ε : ℝ => (1 - Real.exp (-ε)) * P) := by fun_prop
    simpa using hcont.tendsto 0

/-! ### 3. Truncated $\Xi$-Divisible Riemann-Kernel Family & Parity Involution -/

/-- **Truncated $\Xi$-Divisible Riemann-Kernel Zero Annihilation and Tail-Leakage Bound**:
For every degree `K : ℕ`, complex coefficient vector `a : Fin (K + 1) → ℂ`, and real coefficient
vector `x : Fin (K + 1) → ℝ`:
1. The exact Riemann-kernel combination `kernelComb a` vanishes under `paperFT` at `gammaOf ρ`
   and `conj (gammaOf ρ)` for every nontrivial zero `ρ ∈ zetaZeroConfig.carrier`.
2. For every cutoff scale `L : ℝ` and transition-derivative bound `Λ : ℝ`, the Weil zero energy
   of `nearRadicalTest L a` is bounded explicitly by `(5/4) * S_Z` times the square of the sum of
   the `exp(|u|/2)`-weighted `L¹` norms of `nearRadicalTail L a` and `nearRadicalTailDeriv L a`.
3. Under reflection `u ↦ -u`, the cusp series of `kernelPoly x` and `cuspDeriv (kernelPoly x)`
   transform via the exact parity involution `parityCoeff x`. -/
theorem truncated_riemann_kernel_zero_annihilation_and_parity
    {K : ℕ} (a : Fin (K + 1) → ℂ) (x : Fin (K + 1) → ℝ) :
    (∀ ρ ∈ zetaZeroConfig.carrier,
      paperFT (kernelComb a) (gammaOf ρ) = 0 ∧
      paperFT (kernelComb a) ((starRingEnd ℂ) (gammaOf ρ)) = 0) ∧
    (∀ (L Λ : ℝ), (∀ t : ℝ, |deriv Real.smoothTransition t| ≤ Λ) →
      ‖zetaZeroConfig.W (nearRadicalTest L a) (nearRadicalTest L a)‖ ≤
        (5 / 4) * (∑' ρ : zetaZeroConfig.carrier,
          (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) *
        ((∫ u : ℝ, ‖nearRadicalTail L a u‖ * Real.exp (1 / 2 * |u|)) +
          ∫ u : ℝ, ‖nearRadicalTailDeriv L a u‖ * Real.exp (1 / 2 * |u|)) ^ 2) ∧
    (∀ u : ℝ,
      cuspSeries (kernelPoly x) (-u) = cuspSeries (kernelPoly (parityCoeff x)) u ∧
      cuspSeries (cuspDeriv (kernelPoly x)) (-u) =
        -cuspSeries (cuspDeriv (kernelPoly (parityCoeff x))) u) :=
  ⟨fun _ hρ => paperFT_kernelComb_at_zero a hρ,
   fun L _ hΛ => norm_W_nearRadicalTest_le L a hΛ,
   fun u => ⟨cuspSeries_kernelPoly_neg x u, cuspSeries_cuspDeriv_kernelPoly_neg x u⟩⟩

/-- The parity involution `parityCoeff` on `Fin (K + 1) → ℝ` is involutive
(`parityCoeff (parityCoeff x) = x`), acts as the identity on purely even derivative combinations
(`x i = 0` for odd `i`), and acts as negation on purely odd derivative combinations
(`x i = 0` for even `i`). -/
theorem parityCoeff_involutive_and_eigenchannels {K : ℕ} (x : Fin (K + 1) → ℝ) :
    parityCoeff (parityCoeff x) = x ∧
    ((∀ i : Fin (K + 1), Odd (i : ℕ) → x i = 0) → parityCoeff x = x) ∧
    ((∀ i : Fin (K + 1), Even (i : ℕ) → x i = 0) → parityCoeff x = -x) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i
    simp only [parityCoeff]
    rw [← mul_assoc, ← pow_add, ← two_mul]
    simp [pow_mul]
  · intro heven
    ext i
    simp only [parityCoeff]
    rcases Nat.even_or_odd (i : ℕ) with hi | hi
    · rw [hi.neg_one_pow, one_mul]
    · rw [heven i hi, mul_zero]
  · intro hodd
    ext i
    simp only [parityCoeff, Pi.neg_apply]
    rcases Nat.even_or_odd (i : ℕ) with hi | hi
    · rw [hodd i hi, mul_zero, neg_zero]
    · rw [hi.neg_one_pow, neg_one_mul]

end GaloisForLFunctions.ReverseTwistedArcPoleCompression
