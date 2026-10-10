import GaloisForLFunctions.RHTower.GaussianArithmeticBoundedCeilingReceiver
import GaloisForLFunctions.RHTower.ZetaZeroFreeRegionAllZeros
import GaloisForLFunctions.RHTower.XiStripEdgeHeightFloorRatioGate

/-!
# A one-sided ceiling for Gaussian-smoothed prime sums is equivalent to RH

For a width `ε > 0` and a centre `t`, the Gaussian prime contribution is

`P(ε, t) = (2/√(π ε)) Σ_n Λ(n) n^{-1/2} exp(-(log n)²/(4ε)) cos(t log n)`

(`RiemannGaussian.gaussianPrimeContribution`).

**Theorem** (`riemannHypothesis_iff_forall_rat_gaussianPrimeContribution_bddAbove`).  RH holds iff
for every rational `r ≥ 1/2` the prime sum `P(ε, r)` is bounded above on `ε ≥ 1`.

This is the final arithmetic form of the amplified HCF route: one upper bound, depending on the
height, for one explicit absolutely convergent prime sum at each rational height.  It involves no
zeros, no Gamma factor and no sign condition.

Mechanism.
* The arithmetic Gaussian formula is `G = A - P`.  For `|t| ≥ 1/2` and `ε ≥ 1` the archimedean
  part `A` is bounded: the pole term `4 e^{ε(1/4 - t²)} cos(εt)` is at most `4`, and the digamma
  integral is dominated by the width-one Gaussian against the exponential digamma majorant
  (`abs_gaussianArchimedeanContribution_le`).
* Under RH, `G` is bounded, hence so is `P`.
* Conversely, an off-line zero lies in the light cone of a rational height `r`, and
  `|r| > 4 - 1/2` because every zero has ordinate at least `4`.  At that height `G` is unbounded
  below (`exists_height_not_bddBelow_gaussianArithmeticExplicitFormula`), so `P` is unbounded above.
  The prime sum is even in `t`, so positive rational heights suffice.
-/

open Complex Filter Topology Set MeasureTheory

namespace RHTower

open RiemannGaussian GaloisForLFunctions.HTGeometry

noncomputable section

/-- The width-one Gaussian majorant of the digamma integral. -/
def gaussianDigammaMajorant (t : ℝ) : ℝ :=
  (1 / Real.pi) * ∫ r : ℝ, (Real.exp (-1 * (r - t) ^ 2) + Real.exp (-1 * (r - -t) ^ 2)) *
    (quarterDigammaExponentialConstant * Real.exp (Real.pi * (|r| + 1)))

/-- For widths `ε ≥ 1` the digamma integral is bounded by the width-one majorant. -/
theorem abs_gaussianDigammaIntegral_le {ε : ℝ} (hε : 1 ≤ ε) (t : ℝ) :
    |gaussianDigammaIntegral ε t| ≤ gaussianDigammaMajorant t := by
  set g : ℝ → ℝ := fun r => (Real.exp (-1 * (r - t) ^ 2) + Real.exp (-1 * (r - -t) ^ 2)) *
    (quarterDigammaExponentialConstant * Real.exp (Real.pi * (|r| + 1))) with hgdef
  have hgint : Integrable g := by
    have h1 := (integrable_translatedGaussian_mul_exp_pi_abs one_pos t).const_mul
      quarterDigammaExponentialConstant
    have h2 := (integrable_translatedGaussian_mul_exp_pi_abs one_pos (-t)).const_mul
      quarterDigammaExponentialConstant
    refine (h1.add h2).congr (Eventually.of_forall fun r => ?_)
    simp only [hgdef, Pi.add_apply]
    ring
  have hg0 : ∀ r, 0 ≤ g r := fun r => by
    have := quarterDigammaExponentialConstant_nonneg
    simp only [hgdef]
    positivity
  have hpoint : ∀ r : ℝ, ‖symmetricGaussian ε t r * riemannArchimedeanDensity r‖ ≤ g r := by
    intro r
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
    simp only [hgdef]
    exact mul_le_mul hsym hdens (abs_nonneg _) (by positivity)
  rw [gaussianDigammaIntegral, gaussianDigammaMajorant, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.pi)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc |∫ r : ℝ in Ioi 0, symmetricGaussian ε t r * riemannArchimedeanDensity r|
      ≤ ∫ r : ℝ in Ioi 0, g r :=
        norm_integral_le_of_norm_le hgint.integrableOn (Eventually.of_forall hpoint)
    _ ≤ ∫ r : ℝ, g r := setIntegral_le_integral hgint (Eventually.of_forall hg0)

/-- For `|t| ≥ 1/2` and `ε ≥ 1` the archimedean part of the Gaussian formula is bounded. -/
theorem abs_gaussianArchimedeanContribution_le {ε t : ℝ} (hε : 1 ≤ ε) (ht : 1 / 2 ≤ |t|) :
    |gaussianArchimedeanContribution ε t| ≤
      4 + Real.log Real.pi / Real.sqrt Real.pi + gaussianDigammaMajorant t := by
  have hpole : |4 * Real.exp (ε / 4 - ε * t ^ 2) * Real.cos (ε * t)| ≤ 4 := by
    have ht2 : 1 / 4 ≤ t ^ 2 := by
      have := sq_le_sq' (by linarith [abs_nonneg t]) ht
      rw [sq_abs] at this
      linarith
    have hexp : Real.exp (ε / 4 - ε * t ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4),
      abs_of_pos (Real.exp_pos _)]
    have hcos := Real.abs_cos_le_one (ε * t)
    nlinarith [Real.exp_pos (ε / 4 - ε * t ^ 2)]
  have hlog : |Real.log Real.pi / Real.sqrt (Real.pi * ε)| ≤
      Real.log Real.pi / Real.sqrt Real.pi := by
    have hlogpos : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
    rw [abs_of_pos (div_pos hlogpos (Real.sqrt_pos.2 (by positivity)))]
    exact div_le_div_of_nonneg_left hlogpos.le (Real.sqrt_pos.2 Real.pi_pos)
      (Real.sqrt_le_sqrt (by nlinarith [Real.pi_pos]))
  have hD := abs_gaussianDigammaIntegral_le hε t
  rw [gaussianArchimedeanContribution]
  calc |4 * Real.exp (ε / 4 - ε * t ^ 2) * Real.cos (ε * t) -
          Real.log Real.pi / Real.sqrt (Real.pi * ε) + gaussianDigammaIntegral ε t|
      ≤ |4 * Real.exp (ε / 4 - ε * t ^ 2) * Real.cos (ε * t)| +
          |Real.log Real.pi / Real.sqrt (Real.pi * ε)| + |gaussianDigammaIntegral ε t| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_sub _ _
    _ ≤ 4 + Real.log Real.pi / Real.sqrt Real.pi + gaussianDigammaMajorant t := by
        linarith

/-- **Pure-prime receiver.**  RH holds iff for every rational `r ≥ 1/2` the Gaussian-smoothed prime
sum `(2/√(πε)) Σ Λ(n) n^{-1/2} e^{-(log n)²/(4ε)} cos(r log n)` is bounded above on `ε ≥ 1`. -/
theorem riemannHypothesis_iff_forall_rat_gaussianPrimeContribution_bddAbove :
    RiemannHypothesis ↔
      ∀ r : ℚ, (1 / 2 : ℝ) ≤ r → ∃ C : ℝ, ∀ ε : ℝ, 1 ≤ ε →
        gaussianPrimeContribution ε r ≤ C := by
  constructor
  · intro hRH r hr
    obtain ⟨C, hC⟩ :=
      riemannHypothesis_iff_forall_gaussianArithmeticExplicitFormula_bounded.1 hRH (r : ℝ)
    have hr' : (1 / 2 : ℝ) ≤ |(r : ℝ)| := hr.trans (le_abs_self _)
    refine ⟨4 + Real.log Real.pi / Real.sqrt Real.pi + gaussianDigammaMajorant r + C,
      fun ε hε => ?_⟩
    have hA := abs_gaussianArchimedeanContribution_le hε hr'
    have hG := hC ε hε
    rw [gaussianArithmeticExplicitFormula] at hG
    have h1 := le_abs_self (gaussianArchimedeanContribution ε r)
    have h2 := neg_abs_le (gaussianArchimedeanContribution ε r - gaussianPrimeContribution ε r)
    linarith
  · intro hbdd
    rw [riemannHypothesis_iff_spectralCoordinate_real]
    intro s hs hnt hne1
    by_contra hy
    obtain ⟨r, hrcone, hnot⟩ :=
      exists_height_not_bddBelow_gaussianArithmeticExplicitFormula hs hnt hne1 hy
    apply hnot
    -- the cone height is far from the origin
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
    have hrabs : (1 / 2 : ℝ) ≤ |(r : ℝ)| := by
      have := abs_sub_abs_le_abs_sub (zetaSpectralCoordinate s).re (r : ℝ)
      rw [abs_sub_comm] at hrcone
      rw [hx] at this hrcone
      linarith
    -- the height or its negative is a rational `≥ 1/2`
    obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ ε : ℝ, 1 ≤ ε → gaussianPrimeContribution ε r ≤ C := by
      rcases le_or_gt 0 (r : ℝ) with hpos | hneg
      · exact hbdd r (by rw [abs_of_nonneg hpos] at hrabs; exact hrabs)
      · obtain ⟨C, hC⟩ := hbdd (-r) (by push_cast; rw [abs_of_neg hneg] at hrabs; exact hrabs)
        refine ⟨C, fun ε hε => ?_⟩
        have := hC ε hε
        push_cast at this
        rwa [gaussianPrimeContribution_neg_center] at this
    refine ⟨4 + Real.log Real.pi / Real.sqrt Real.pi + gaussianDigammaMajorant r + C,
      fun ε hε => ?_⟩
    have hA := abs_gaussianArchimedeanContribution_le hε hrabs
    rw [gaussianArithmeticExplicitFormula]
    have := neg_abs_le (gaussianArchimedeanContribution ε r)
    have := hC ε hε
    linarith

/-- **Unconditional low-height producer.**  For `1/2 ≤ |t| ≤ 17/2` no light cone over `t` meets
the zeros, because every zero has `(Im ρ)² > 331/4` (computer-free zero-free band).  So the
Gaussian-smoothed prime sum at frequency `t` is bounded for all widths `ε ≥ 1`: square-root
cancellation for `Σ Λ(n) n^{-1/2} e^{-(log n)²/(4ε)} cos(t log n)` at low frequencies. -/
theorem exists_abs_gaussianPrimeContribution_le_of_low_height {t : ℝ} (h1 : 1 / 2 ≤ |t|)
    (h2 : |t| ≤ 17 / 2) :
    ∃ C : ℝ, ∀ ε : ℝ, 1 ≤ ε → |gaussianPrimeContribution ε t| ≤ C := by
  have hcone : ∀ o : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
      0 ≤ ((zetaSpectralCoordinate o.1.1 - t) ^ 2).re := fun o => by
    rw [re_sub_ofReal_sq, zetaSpectralCoordinate_re]
    have hre0 := NontrivialZetaZero.zero_lt_re o.1
    have hre1 := NontrivialZetaZero.re_lt_one o.1
    have hxi : xi o.1.1 = 0 := (xi_zero_iff_zeta_zero_of_mem_strip hre0 hre1).2 o.1.2.1
    have hfloor := xi_zero_im_sq_gt_floor hxi
    have him9 : 9 < |(o.1.1).im| := by
      by_contra h
      push Not at h
      have := sq_le_sq' (abs_le.1 h).1 (abs_le.1 h).2
      nlinarith
    have hdist : 1 / 2 < |(o.1.1).im - t| := by
      have := abs_sub_abs_le_abs_sub (o.1.1).im t
      linarith
    have hy := NontrivialZetaZero.abs_spectralCoordinate_im_lt_half o.1
    have hsq1 := sq_lt_sq' (abs_lt.1 hy).1 (abs_lt.1 hy).2
    have hsq2 : (1 / 2 : ℝ) ^ 2 < ((o.1.1).im - t) ^ 2 := by
      have := sq_lt_sq.2 (show |(1 / 2 : ℝ)| < |(o.1.1).im - t| by
        rwa [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)])
      exact this
    nlinarith
  refine ⟨4 + Real.log Real.pi / Real.sqrt Real.pi + gaussianDigammaMajorant t +
    2 * ∑' o : NontrivialZetaZeroOccurrence analyticZetaZeroMultiplicity,
      Real.exp (1 / 4 + t ^ 2) * Real.exp (-(1 / 2) * (zetaSpectralCoordinate o.1.1).re ^ 2),
    fun ε hε => ?_⟩
  have hA := abs_gaussianArchimedeanContribution_le hε h1
  have hG := abs_gaussianArithmeticExplicitFormula_le_of_cone hcone hε
  rw [gaussianArithmeticExplicitFormula] at hG
  have := abs_sub (gaussianArchimedeanContribution ε t)
    (gaussianArchimedeanContribution ε t - gaussianPrimeContribution ε t)
  rw [sub_sub_cancel] at this
  linarith

end

end RHTower
