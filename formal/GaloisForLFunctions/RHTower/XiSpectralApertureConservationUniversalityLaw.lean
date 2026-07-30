import GaloisForLFunctions.RHTower.XiAbstractInstance
import GaloisForLFunctions.RHTower.XiHurwitzFullTransverseApertureSpectrumUniversalityLaw

/-!
# Xi spectral-aperture conservation

The horizontal width of the Xi divisor is one invariant seen in several apparently unrelated
charts.  This module adds the missing Poisson-trace chart to the existing Hurwitz-monodromy,
Hedenmalm, prime-source, negative-energy, and projective charts and identifies their complete
nonnegative parameter spectrum.

The underlying theorem is not specific to Xi: for every admissible conjugation-stable discrete
spectral family, the least exponential type of its Poisson trace on a strict-right vertical line
is exactly the supremal transverse displacement.  The Xi instance transports that abstract
support--indicator duality to arithmetic source coordinates.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- The canonical Xi Poisson trace has vertical exponential type at most `alpha` on one
strict-right vertical line. -/
def XiPoissonTraceVerticalTypeAtMost (alpha : ℝ) : Prop :=
  ∃ σ C : ℝ, 0 < σ ∧
    ∀ x : ℝ,
      ‖xiPoissonTraceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤
        C * Real.exp (alpha * |x|)

/-- A horizontal Xi half-plane bound is the same pointwise bound in the centered spectral
coordinate. -/
theorem abs_im_xiSpectralPoint_le_of_xiZeroHalfPlaneBound
    {alpha : ℝ} (hzeros : XiZeroHalfPlaneBound alpha) :
    ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ alpha := by
  intro q
  rw [xiSpectralPoint_im_eq]
  simpa only [abs_sub_comm] using
    abs_xiZero_re_sub_half_le_of_halfPlaneBound hzeros q

/-- The same transverse bound holds in the canonical Poisson orientation coordinate. -/
theorem abs_im_xiPoissonPoint_le_of_xiZeroHalfPlaneBound
    {alpha : ℝ} (hzeros : XiZeroHalfPlaneBound alpha) :
    ∀ q : XiZeroCopy, |(xiPoissonPoint q).im| ≤ alpha := by
  intro q
  have hq := abs_im_xiSpectralPoint_le_of_xiZeroHalfPlaneBound hzeros q
  rw [xiPoissonPoint]
  split_ifs
  · exact hq
  · simpa only [Complex.neg_im, abs_neg] using hq

/-- **Poisson support--indicator law for Xi.**  At every nonnegative aperture, the canonical
Poisson trace has that vertical exponential type on one line exactly when every Xi zero lies in
the corresponding horizontal half-plane. -/
theorem xiPoissonTraceVerticalTypeAtMost_iff_xiZeroHalfPlaneBound
    {alpha : ℝ} (halpha : 0 ≤ alpha) :
    XiPoissonTraceVerticalTypeAtMost alpha ↔ XiZeroHalfPlaneBound alpha := by
  constructor
  · rintro ⟨σ, C, hσ, hline⟩
    have hlineAbstract :
        ∀ x : ℝ,
          ‖xiPoissonAbstract.traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤
            C * Real.exp (alpha * |x|) := by
      simpa only [xiPoissonAbstract_traceC] using hline
    have hpoint :=
      (xiPoissonAbstract.abs_im_le_iff_exists_line_growth halpha).2
        ⟨σ, C, hσ, hlineAbstract⟩
    have hspectral : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ alpha := by
      intro q
      have hq := hpoint q
      rw [xiPoissonAbstract_pt, xiPoissonPoint] at hq
      split_ifs at hq
      · exact hq
      · simpa only [Complex.neg_im, abs_neg] using hq
    intro rho hzero
    let support : XiDivisorSupport :=
      ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
    let q : XiZeroCopy :=
      ⟨support, ⟨0, xiSupportMultiplicity_pos support⟩⟩
    have hq := hspectral q
    rw [xiSpectralPoint_im_eq] at hq
    have hcenter : |rho.re - 1 / 2| ≤ alpha := by
      simpa only [q, support, abs_sub_comm] using hq
    linarith [le_abs_self (rho.re - 1 / 2)]
  · intro hzeros
    have hpoint : ∀ q : XiZeroCopy, |(xiPoissonAbstract.pt q).im| ≤ alpha := by
      intro q
      rw [xiPoissonAbstract_pt]
      exact abs_im_xiPoissonPoint_le_of_xiZeroHalfPlaneBound hzeros q
    obtain ⟨σ, C, hσ, hline⟩ :=
      (xiPoissonAbstract.abs_im_le_iff_exists_line_growth halpha).1 hpoint
    exact ⟨σ, C, hσ, by
      simpa only [xiPoissonAbstract_traceC] using hline⟩

/-- Under a width bound, every strict-right vertical line has the sharp termwise exponential
envelope with the real trace as its constant. -/
theorem norm_xiPoissonTraceC_le_of_xiZeroHalfPlaneBound
    {alpha : ℝ} (hzeros : XiZeroHalfPlaneBound alpha)
    {τ : ℂ} (hτ : 0 < τ.re) :
    ‖xiPoissonTraceC τ‖ ≤
      Real.exp (alpha * |τ.im|) * xiPoissonTraceReal τ.re := by
  have hpoint : ∀ q : XiZeroCopy, |(xiPoissonAbstract.pt q).im| ≤ alpha := by
    intro q
    rw [xiPoissonAbstract_pt]
    exact abs_im_xiPoissonPoint_le_of_xiZeroHalfPlaneBound hzeros q
  have h := xiPoissonAbstract.norm_traceC_le_of_abs_im_le hpoint hτ
  change ‖xiPoissonTraceC τ‖ ≤
    xiPoissonTraceReal τ.re * Real.exp (alpha * |τ.im|) at h
  simpa only [mul_comm] using h

/-- Simultaneous realization of one Xi aperture in seven exact charts:

* vertical exponential type of the canonical Poisson trace;
* complete Hedenmalm Gaussian Hankel positivity;
* inverse-tilted prime-source holomorphy;
* critical-Mellin holomorphy;
* explicit prime--Gamma negative energy;
* projective reflection radius;
* principal Hurwitz monodromy phase.
-/
def XiSpectralApertureCertificate
    (tau L alpha : ℝ) (N : ℕ) : Prop :=
  XiPoissonTraceVerticalTypeAtMost alpha ∧
  HedenmalmGaussianHankelTailCone tau alpha ∧
  InverseTiltedDyadicSourceAnalyticAbove alpha ∧
  CriticalMellinDefectAnalyticAbove alpha ∧
  XiRectangularNegativeChannelEnergyAbove alpha
    (xiRectangularPrimeGammaTailNegativePart L N) ∧
  xiProjectiveReflectionRadius ≤ alpha ∧
  xiHurwitzRightPrincipalPhaseSup ≤ alpha

/-- **Seven-chart aperture conservation law.**  Every nonnegative aperture is realized
simultaneously in all seven charts exactly when it contains the horizontal Xi divisor. -/
theorem xiSpectralApertureCertificate_iff_xiZeroHalfPlaneBound
    {tau L alpha : ℝ} (htau : 0 < tau) (hL : 0 < L) (halpha : 0 ≤ alpha)
    {N : ℕ} (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    XiSpectralApertureCertificate tau L alpha N ↔ XiZeroHalfPlaneBound alpha := by
  constructor
  · intro h
    exact
      (xiPoissonTraceVerticalTypeAtMost_iff_xiZeroHalfPlaneBound halpha).1 h.1
  · intro hzeros
    have hradius :
        xiProjectiveReflectionRadius ≤ alpha :=
      (xiZeroHalfPlaneBound_iff_projectiveReflectionRadius_le halpha).1 hzeros
    have hphase :
        xiHurwitzRightPrincipalPhaseSup ≤ alpha := by
      calc
        xiHurwitzRightPrincipalPhaseSup = xiRightTransverseSup :=
          xiHurwitzRightPrincipalPhaseSup_eq_transverseSup
        _ = xiProjectiveReflectionRadius :=
          xiProjectiveReflectionRadius_eq_transverseSup.symm
        _ ≤ alpha := hradius
    exact ⟨
      (xiPoissonTraceVerticalTypeAtMost_iff_xiZeroHalfPlaneBound halpha).2 hzeros,
      (hedenmalmGaussianHankelTailCone_iff_xiZeroHalfPlaneBound
        htau halpha).2 hzeros,
      (xiZeroHalfPlaneBound_iff_inverseTiltedDyadicSourceAnalyticAbove
        halpha).1 hzeros,
      (xiZeroHalfPlaneBound_iff_criticalMellinDefectAnalyticAbove
        halpha).1 hzeros,
      (xiZeroHalfPlaneBound_iff_primeGammaTailNegativeEnergyAbove
        hL halpha hN).1 hzeros,
      hradius,
      hphase⟩

/-- Nonnegative apertures at which all seven exact charts are simultaneously valid. -/
def XiSpectralApertureSpectrum
    (tau L : ℝ) (N : ℕ) : Set ℝ :=
  {alpha : ℝ | 0 ≤ alpha ∧ XiSpectralApertureCertificate tau L alpha N}

/-- **Complete aperture-spectrum law.**  Without a nonemptiness assumption and including the RH
endpoint, the common seven-chart aperture spectrum is the closed upper ray beginning at the
intrinsic projective/Hurwitz/Poisson support radius. -/
theorem xiSpectralApertureSpectrum_eq_Ici_projectiveReflectionRadius
    {tau L : ℝ} (htau : 0 < tau) (hL : 0 < L)
    {N : ℕ} (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    XiSpectralApertureSpectrum tau L N =
      Set.Ici xiProjectiveReflectionRadius := by
  ext alpha
  simp only [XiSpectralApertureSpectrum, Set.mem_setOf_eq, Set.mem_Ici]
  constructor
  · rintro ⟨halpha, hcertificate⟩
    have hzeros :=
      (xiSpectralApertureCertificate_iff_xiZeroHalfPlaneBound
        htau hL halpha hN).1 hcertificate
    exact
      (xiZeroHalfPlaneBound_iff_projectiveReflectionRadius_le halpha).1 hzeros
  · intro hradius
    have halpha : 0 ≤ alpha :=
      xiProjectiveReflectionRadius_nonneg.trans hradius
    have hzeros : XiZeroHalfPlaneBound alpha :=
      (xiZeroHalfPlaneBound_iff_projectiveReflectionRadius_le halpha).2 hradius
    exact ⟨halpha,
      (xiSpectralApertureCertificate_iff_xiZeroHalfPlaneBound
        htau hL halpha hN).2 hzeros⟩

/-- The zero-aperture endpoint of the conservation law is exactly RH. -/
theorem xiSpectralApertureCertificate_zero_iff_riemannHypothesis
    {tau L : ℝ} (htau : 0 < tau) (hL : 0 < L)
    {N : ℕ} (hN : ∀ n : ℕ, N ≤ n → 1 ≤ n ∧ L ≤ Real.log n / 2) :
    XiSpectralApertureCertificate tau L 0 N ↔ RiemannHypothesis := by
  rw [xiSpectralApertureCertificate_iff_xiZeroHalfPlaneBound
    htau hL (le_refl 0) hN]
  exact
    (hedenmalmGaussianHankelTailCone_iff_xiZeroHalfPlaneBound
      htau (le_refl 0)).symm.trans
      (hedenmalmGaussianHankelTailCone_zero_iff_riemannHypothesis htau)

end

end RHTower
