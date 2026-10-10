import GaloisForLFunctions.RHTower.GaussianPrimeSumCeilingReceiver

/-!
# The Gaussian prime sum detects the zero at `1/2 + it`

For a width `ε > 0` and a frequency `t`, the Gaussian prime sum is

`P(ε, t) = (2/√(πε)) Σ_n Λ(n) n^{-1/2} exp(-(log n)²/(4ε)) cos(t log n)`

(`gaussianPrimeContribution`).

**Theorem** (`tendsto_gaussianPrimeContribution_of_outside_cones`).  Let `|t| > 1/2`, and suppose
every zero is either exactly `1/2 + it` or strictly outside the closed light cone over `t`.  Then
`P(ε, t) → -2 m(t)` as `ε → ∞`, where `m(t) = Σ_{o : z_o = t} 1` counts the zero `1/2 + it` with
multiplicity.

**Theorem** (`riemannHypothesis_iff_forall_rat_tendsto_gaussianPrimeContribution`).  RH holds iff
for every rational `r > 1/2` the Gaussian prime sum `P(ε, r)` converges as `ε → ∞`.  Under RH the
limit is `-2 m(r)`: the primes alone detect every critical zero and its multiplicity.

Mechanism.  `P = A - G`, with `G` the zero sum and `A` the archimedean part.  For `|t| > 1/2`, `A → 0`:
the pole term is `≤ 4 e^{ε(1/4 - t²)}`, the logarithmic term decays like `ε^{-1/2}`, and the digamma
integral goes to `0` by dominated convergence against the width-one majorant.  The zero sum
`G = 2 Re Σ_o e^{-ε(z_o - t)²}` tends to `2 m(t)` by dominated convergence.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

open RiemannGaussian GaloisForLFunctions.HTGeometry

noncomputable section

/-- The multiplicity count `m(t) = #{occurrences with spectral coordinate t}`. -/
def gaussianCriticalMultiplicity (t : ℝ) : ℝ :=
  ∑' o : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
    if zetaSpectralCoordinate o.1.1 = (t : ℂ) then (1 : ℝ) else 0

/-- **Zero-side limit.** -/
theorem tendsto_zero_sum_of_outside_cones {t : ℝ}
    (hout : ∀ o : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
      zetaSpectralCoordinate o.1.1 = (t : ℂ) ∨ 0 < ((zetaSpectralCoordinate o.1.1 - t) ^ 2).re) :
    Tendsto (fun ε : ℝ => ∑' o : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
        Complex.exp (-(ε : ℂ) * (zetaSpectralCoordinate o.1.1 - t) ^ 2)) atTop
      (𝓝 (∑' o : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
        if zetaSpectralCoordinate o.1.1 = (t : ℂ) then (1 : ℂ) else 0)) := by
  classical
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun o => Real.exp (1 / 4 + t ^ 2) *
      Real.exp (-(1 / 2) * (zetaSpectralCoordinate o.1.1).re ^ 2))
    ((zetaZeroGaussianOrdinateSummable (1 / 2) (by norm_num)).mul_left _) (fun o => ?_) ?_
  · rcases hout o with h | h
    · rw [if_pos h]
      refine tendsto_const_nhds.congr fun ε => ?_
      rw [h, sub_self]; simp
    · rw [if_neg (fun h' => by rw [h', sub_self] at h; simp at h)]
      apply squeeze_zero_norm (a := fun ε : ℝ =>
        Real.exp (-(ε * ((zetaSpectralCoordinate o.1.1 - t) ^ 2).re)))
      · intro ε
        rw [Complex.norm_exp]
        apply le_of_eq; congr 1
        rw [neg_mul, neg_re, re_ofReal_mul]
      · have : Tendsto (fun ε : ℝ => -(ε * ((zetaSpectralCoordinate o.1.1 - t) ^ 2).re)) atTop
            atBot := tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const h)
        exact Real.tendsto_exp_atBot.comp this
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with ε hε o
    exact norm_exp_neg_mul_spectral_sub_sq_le_of_re_nonneg hε t o (by
      rcases hout o with h | h
      · rw [h, sub_self]; simp
      · exact h.le)

/-- The digamma integral vanishes as the width grows. -/
theorem tendsto_gaussianDigammaIntegral_zero (t : ℝ) :
    Tendsto (fun ε : ℝ => gaussianDigammaIntegral ε t) atTop (𝓝 0) := by
  set g : ℝ → ℝ := fun r => (Real.exp (-1 * (r - t) ^ 2) + Real.exp (-1 * (r - -t) ^ 2)) *
    (quarterDigammaExponentialConstant * Real.exp (Real.pi * (|r| + 1)))
  have hgint : Integrable g := by
    have h1 := (integrable_translatedGaussian_mul_exp_pi_abs one_pos t).const_mul
      quarterDigammaExponentialConstant
    have h2 := (integrable_translatedGaussian_mul_exp_pi_abs one_pos (-t)).const_mul
      quarterDigammaExponentialConstant
    refine (h1.add h2).congr (Eventually.of_forall fun r => ?_)
    simp only [g, Pi.add_apply]
    ring
  have hlim : Tendsto (fun ε : ℝ => ∫ r : ℝ in Ioi 0,
      symmetricGaussian ε t r * riemannArchimedeanDensity r) atTop (𝓝 (∫ r : ℝ in Ioi 0, (0 : ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence g ?_ ?_ hgint.integrableOn ?_
    · have hcG : ∀ ε : ℝ, Continuous (fun r : ℝ => symmetricGaussian ε t r) := fun ε => by
        unfold symmetricGaussian translatedGaussian; fun_prop
      exact Eventually.of_forall fun ε =>
        ((hcG ε).mul continuous_riemannArchimedeanDensity).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with ε hε
      refine Eventually.of_forall fun r => ?_
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (symmetricGaussian_pos ε t r)]
      have hdens : |riemannArchimedeanDensity r| ≤
          quarterDigammaExponentialConstant * Real.exp (Real.pi * (|r| + 1)) :=
        (Complex.abs_re_le_norm _).trans (norm_digamma_quarter_line_le r)
      have hsym : symmetricGaussian ε t r ≤
          Real.exp (-1 * (r - t) ^ 2) + Real.exp (-1 * (r - -t) ^ 2) := by
        simp only [symmetricGaussian, translatedGaussian]
        have e1 : Real.exp (-ε * (r - t) ^ 2) ≤ Real.exp (-1 * (r - t) ^ 2) :=
          Real.exp_le_exp.2 (by nlinarith [sq_nonneg (r - t)])
        have e2 : Real.exp (-ε * (-r - t) ^ 2) ≤ Real.exp (-1 * (r - -t) ^ 2) := by
          rw [show (-r - t) ^ 2 = (r - -t) ^ 2 by ring]
          exact Real.exp_le_exp.2 (by nlinarith [sq_nonneg (r - -t)])
        linarith
      exact mul_le_mul hsym hdens (abs_nonneg _) (by positivity)
    · -- pointwise limit away from `r = ±t`
      have hfin : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), r ≠ t ∧ r ≠ -t := by
        refine ae_restrict_of_ae ?_
        have h1 : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ t := by
          rw [ae_iff]; simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton, measure_singleton]
        have h2 : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ -t := by
          rw [ae_iff]; simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton, measure_singleton]
        filter_upwards [h1, h2] with r h1 h2 using ⟨h1, h2⟩
      filter_upwards [hfin] with r ⟨h1, h2⟩
      have hp1 : 0 < (r - t) ^ 2 := by have : r - t ≠ 0 := sub_ne_zero.2 h1; positivity
      have hp2 : 0 < (-r - t) ^ 2 := by
        have : -r - t ≠ 0 := by intro h; apply h2; linarith
        positivity
      have hlim1 : Tendsto (fun ε : ℝ => Real.exp (-ε * (r - t) ^ (2 : ℕ))) atTop (𝓝 0) := by
        have : Tendsto (fun ε : ℝ => -ε * (r - t) ^ (2 : ℕ)) atTop atBot :=
          (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const hp1)).congr fun ε => by
            simp only [Function.comp, id]; ring
        exact Real.tendsto_exp_atBot.comp this
      have hlim2 : Tendsto (fun ε : ℝ => Real.exp (-ε * (-r - t) ^ (2 : ℕ))) atTop (𝓝 0) := by
        have : Tendsto (fun ε : ℝ => -ε * (-r - t) ^ (2 : ℕ)) atTop atBot :=
          (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const hp2)).congr fun ε => by
            simp only [Function.comp, id]; ring
        exact Real.tendsto_exp_atBot.comp this
      have := (hlim1.add hlim2).mul_const (riemannArchimedeanDensity r)
      simpa [symmetricGaussian, translatedGaussian] using this
  rw [integral_zero] at hlim
  have h := hlim.const_mul (1 / Real.pi)
  rw [mul_zero] at h
  exact h.congr fun ε => rfl

/-- For `|t| > 1/2` the archimedean part of the Gaussian formula vanishes as the width grows. -/
theorem tendsto_gaussianArchimedeanContribution_zero {t : ℝ} (ht : 1 / 2 < |t|) :
    Tendsto (fun ε : ℝ => gaussianArchimedeanContribution ε t) atTop (𝓝 0) := by
  have ht2 : 1 / 4 < t ^ 2 := by
    have := sq_lt_sq' (by linarith [abs_nonneg t]) ht
    rw [sq_abs] at this; linarith
  have hpole : Tendsto (fun ε : ℝ => 4 * Real.exp (ε / 4 - ε * t ^ 2) * Real.cos (ε * t)) atTop
      (𝓝 0) := by
    have hexp : Tendsto (fun ε : ℝ => Real.exp (ε / 4 - ε * t ^ 2)) atTop (𝓝 0) := by
      have : Tendsto (fun ε : ℝ => ε / 4 - ε * t ^ 2) atTop atBot := by
        have h := tendsto_id.atTop_mul_const (show 0 < t ^ 2 - 1 / 4 by linarith)
        refine (tendsto_neg_atTop_atBot.comp h).congr fun ε => ?_
        simp; ring
      exact Real.tendsto_exp_atBot.comp this
    apply squeeze_zero_norm (a := fun ε => 4 * Real.exp (ε / 4 - ε * t ^ 2))
    · intro ε
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4),
        abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)
    · simpa using hexp.const_mul 4
  have hlog : Tendsto (fun ε : ℝ => Real.log Real.pi / Real.sqrt (Real.pi * ε)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun ε : ℝ => Real.sqrt (Real.pi * ε)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp (tendsto_id.const_mul_atTop Real.pi_pos)
    exact tendsto_const_nhds.div_atTop h1
  have h := (hpole.sub hlog).add (tendsto_gaussianDigammaIntegral_zero t)
  simp only [sub_zero, add_zero] at h
  exact h.congr fun ε => by rw [gaussianArchimedeanContribution]

/-- **Arithmetic zero detector.** -/
theorem tendsto_gaussianPrimeContribution_of_outside_cones {t : ℝ} (ht : 1 / 2 < |t|)
    (hout : ∀ o : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
      zetaSpectralCoordinate o.1.1 = (t : ℂ) ∨ 0 < ((zetaSpectralCoordinate o.1.1 - t) ^ 2).re) :
    Tendsto (fun ε : ℝ => gaussianPrimeContribution ε t) atTop
      (𝓝 (-(2 * gaussianCriticalMultiplicity t))) := by
  classical
  have hz := tendsto_zero_sum_of_outside_cones hout
  have hG : Tendsto (fun ε : ℝ => gaussianArithmeticExplicitFormula ε t) atTop
      (𝓝 (2 * gaussianCriticalMultiplicity t)) := by
    have hre := (Complex.continuous_re.tendsto _).comp hz
    have h2 := hre.const_mul 2
    have hval : (2 : ℝ) * (∑' o : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
        if zetaSpectralCoordinate o.1.1 = (t : ℂ) then (1 : ℂ) else 0).re =
          2 * gaussianCriticalMultiplicity t := by
      congr 1
      rw [gaussianCriticalMultiplicity]
      have hcast : (∑' o : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
          if zetaSpectralCoordinate o.1.1 = (t : ℂ) then (1 : ℂ) else 0) =
            ((∑' o : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
              if zetaSpectralCoordinate o.1.1 = (t : ℂ) then (1 : ℝ) else 0 : ℝ) : ℂ) := by
        rw [Complex.ofReal_tsum]
        exact tsum_congr fun o => by split_ifs <;> simp
      rw [hcast, Complex.ofReal_re]
    rw [hval] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with ε hε
    simp only [Function.comp]
    rw [gaussianArithmeticExplicitFormula_eq_two_re_tsum hε]
  have hA := tendsto_gaussianArchimedeanContribution_zero ht
  have h := hA.sub hG
  rw [zero_sub] at h
  refine h.congr fun ε => ?_
  rw [gaussianArithmeticExplicitFormula]
  ring

/-- **RH as convergence of the Gaussian prime sums.**  RH holds iff for every rational `r > 1/2` the
Gaussian prime sum `P(ε, r)` converges as `ε → ∞`; under RH its limit is `-2 m(r)`. -/
theorem riemannHypothesis_iff_forall_rat_tendsto_gaussianPrimeContribution :
    RiemannHypothesis ↔
      ∀ r : ℚ, (1 / 2 : ℝ) < r → ∃ L : ℝ,
        Tendsto (fun ε : ℝ => gaussianPrimeContribution ε r) atTop (𝓝 L) := by
  constructor
  · intro hRH r hr
    refine ⟨_, tendsto_gaussianPrimeContribution_of_outside_cones
      (hr.trans_le (le_abs_self _)) fun o => ?_⟩
    have him : (zetaSpectralCoordinate o.1.1).im = 0 :=
      (riemannHypothesis_iff_spectralCoordinate_real.1 hRH) o.1.1 o.1.2.1 o.1.2.2.1 o.1.2.2.2
    by_cases hx : (zetaSpectralCoordinate o.1.1).re = r
    · left
      exact Complex.ext (by rw [hx]; simp) (by rw [him]; simp)
    · right
      rw [re_sub_ofReal_sq, him]
      have : (zetaSpectralCoordinate o.1.1).re - r ≠ 0 := sub_ne_zero.2 hx
      have := sq_pos_of_ne_zero this
      linarith [sq_nonneg (0 : ℝ)]
  · intro hconv
    rw [riemannHypothesis_iff_spectralCoordinate_real]
    intro s hs hnt hne1
    by_contra hy
    obtain ⟨r, hrcone, hnot⟩ :=
      exists_height_not_bddBelow_gaussianArithmeticExplicitFormula hs hnt hne1 hy
    apply hnot
    have h0s : 0 < s.re := by
      by_contra h
      push Not at h
      obtain ⟨n, hn⟩ := (riemannZeta_eq_zero_iff_of_re_le_zero h).1 hs
      exact hnt ⟨n, by rw [hn]; ring⟩
    have hs1 : s.re < 1 := by
      by_contra h
      push Not at h
      exact riemannZeta_ne_zero_of_one_le_re h hs
    have h4 := four_le_abs_im_of_zeta_zero h0s hs1 hs
    have hy2 : |(zetaSpectralCoordinate s).im| < 1 / 2 := by
      rw [zetaSpectralCoordinate_im, abs_lt]; constructor <;> linarith
    have hx : (zetaSpectralCoordinate s).re = s.im := zetaSpectralCoordinate_re s
    have hrabs : (1 / 2 : ℝ) < |(r : ℝ)| := by
      have := abs_sub_abs_le_abs_sub (zetaSpectralCoordinate s).re (r : ℝ)
      rw [abs_sub_comm] at hrcone
      rw [hx] at this hrcone
      linarith
    -- convergence of the prime sum at height `r`
    obtain ⟨L, hL⟩ : ∃ L : ℝ, Tendsto (fun ε : ℝ => gaussianPrimeContribution ε r) atTop (𝓝 L) := by
      rcases le_or_gt 0 (r : ℝ) with hpos | hneg
      · exact hconv r (by rw [abs_of_nonneg hpos] at hrabs; exact hrabs)
      · obtain ⟨L, hL⟩ := hconv (-r) (by push_cast; rw [abs_of_neg hneg] at hrabs; exact hrabs)
        refine ⟨L, hL.congr fun ε => ?_⟩
        push_cast
        rw [gaussianPrimeContribution_neg_center]
    obtain ⟨E₀, hE₀⟩ := Filter.eventually_atTop.1 (hL.eventually (gt_mem_nhds (lt_add_one L)))
    set E : ℝ := max E₀ 1
    -- the trivial bound for the zero sum on `[1, E]`
    set Btriv : ℝ := 2 * (Real.exp (E / 4 + E * (r : ℝ) ^ 2) *
      ∑' o : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
        Real.exp (-(1 / 2) * (zetaSpectralCoordinate o.1.1).re ^ 2))
    have hsumh := zetaZeroGaussianOrdinateSummable (1 / 2) (by norm_num)
    have hGtriv : ∀ ε : ℝ, 1 ≤ ε → ε ≤ E → |gaussianArithmeticExplicitFormula ε r| ≤ Btriv := by
      intro ε hε hεE
      rw [gaussianArithmeticExplicitFormula_eq_two_re_tsum (by linarith), abs_mul,
        abs_of_pos two_pos]
      refine mul_le_mul_of_nonneg_left ?_ zero_le_two
      refine (Complex.abs_re_le_norm _).trans ((norm_tsum_le_tsum_norm
        (summable_norm_exp_neg_mul_spectral_sub_sq (by linarith) r)).trans ?_)
      rw [← tsum_mul_left]
      refine Summable.tsum_le_tsum (fun o => ?_)
        (summable_norm_exp_neg_mul_spectral_sub_sq (by linarith) r) (hsumh.mul_left _)
      refine (norm_exp_neg_mul_spectral_sub_sq_le (by linarith) r o).trans ?_
      gcongr
    refine ⟨max Btriv (L + 1 + (4 + Real.log Real.pi / Real.sqrt Real.pi +
      gaussianDigammaMajorant r)), fun ε hε => ?_⟩
    rcases le_or_gt ε E with hεE | hεE
    · have := hGtriv ε hε hεE
      have := neg_abs_le (gaussianArithmeticExplicitFormula ε r)
      have := le_max_left Btriv (L + 1 + (4 + Real.log Real.pi / Real.sqrt Real.pi +
        gaussianDigammaMajorant r))
      linarith
    · have hP := hE₀ ε ((le_max_left _ _).trans hεE.le)
      have hA := abs_gaussianArchimedeanContribution_le hε hrabs.le
      rw [gaussianArithmeticExplicitFormula]
      have := neg_abs_le (gaussianArchimedeanContribution ε r)
      have := le_max_right Btriv (L + 1 + (4 + Real.log Real.pi / Real.sqrt Real.pi +
        gaussianDigammaMajorant r))
      linarith

end

end RHTower
