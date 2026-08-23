import GaloisForLFunctions.RHTower.CCMCompletedPrimeGammaAccretivityCriterion
import GaloisForLFunctions.RHTower.XiHedenmalmKummerRootRH
import GaloisForLFunctions.RHTower.XiSchurDiscGerm
import GaloisForLFunctions.RHTower.XiWeilHardyFiberDeflatedTrace

/-!
# Fixed-fiber Poisson margin for the continued prime--Gamma trace

Deflating a complete critical Xi fiber raises the imaginary part of the continued source trace by
the fiber's exact upper-half-plane Poisson kernel.  Under RH the remaining Xi divisor terms are
still anti-Herglotz term by term.  Conversely, passivity after this positive rational correction
forces passivity before correction and hence RH.

Thus, for every fixed critical fiber `ρ`, RH is equivalent to the quantitative source inequality

`multiplicity(ρ) * Im z / ‖xiSpectralPointSupport ρ - z‖²
  ≤ -Im (continuedPrimeArchSourceRelativeTrace z)`.

The forward proof below deletes the finite fiber inside the absolutely summable Xi resolvent trace;
it does not reuse packet positivity or the previously proved sampling-floor equivalence.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Upper-strip anti-Herglotz passivity after deleting one complete Xi fiber. -/
def FixedFiberDeflatedUpperAntiHerglotz (ρ : XiDivisorSupport) : Prop :=
  ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
    riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
      (ccmFixedFiberDeflatedRelativeTrace ρ z).im ≤ 0

/-- Quantitative prime--Gamma margin needed to pay for one complete critical Xi fiber. -/
def FixedFiberPrimeGammaPoissonMargin (ρ : XiDivisorSupport) : Prop :=
  ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
    riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
      ((xiZeroCopyFiber ρ).card : ℝ) * z.im /
          Complex.normSq (xiSpectralPointSupport ρ - z) ≤
        -(continuedPrimeArchSourceRelativeTrace z).im

/-- On a real centered fiber, zero deflation adds exactly its multiplicity-weighted Poisson
kernel to the source imaginary part. -/
theorem ccmFixedFiberDeflatedRelativeTrace_im_eq_add_poisson
    (ρ : XiDivisorSupport) (z : ℂ)
    (hαim : (xiSpectralPointSupport ρ).im = 0) :
    (ccmFixedFiberDeflatedRelativeTrace ρ z).im =
      (continuedPrimeArchSourceRelativeTrace z).im +
        ((xiZeroCopyFiber ρ).card : ℝ) * z.im /
          Complex.normSq (xiSpectralPointSupport ρ - z) := by
  rw [ccmFixedFiberDeflatedRelativeTrace, Complex.add_im, Complex.mul_im,
    Complex.sub_im, Complex.inv_im, Complex.inv_im]
  simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero,
    hαim, neg_zero, zero_div, sub_zero, Complex.sub_im]
  ring

/-- Under RH, deleting any finite multiplicity fiber from the Xi relative-resolvent trace leaves
an anti-Herglotz trace.  This is a genuine deleted-`tsum` argument. -/
theorem xiRelativeResolventTrace_sub_fiber_im_nonpos_of_rh
    (hRH : RiemannHypothesis) (ρ : XiDivisorSupport) {z : ℂ}
    (hz : z ∈ xiCenteredUpperHalfPlane) :
    (xiRelativeResolventTrace z -
      ∑ q ∈ xiZeroCopyFiber ρ, xiRelativeResolventTerm z q).im ≤ 0 := by
  have hXi : XiC z ≠ 0 := XiC_ne_zero_upperHalf_of_rh hRH hz
  have hsum : Summable (xiRelativeResolventTerm z) :=
    summable_xiRelativeResolventTerm hXi
  have hsplit := hsum.sum_add_tsum_subtype_compl (xiZeroCopyFiber ρ)
  have hres :
      xiRelativeResolventTrace z -
          ∑ q ∈ xiZeroCopyFiber ρ, xiRelativeResolventTerm z q =
        ∑' q : {q : XiZeroCopy // q ∉ xiZeroCopyFiber ρ},
          xiRelativeResolventTerm z q := by
    rw [xiRelativeResolventTrace, ← hsplit]
    ring
  rw [hres]
  have hcomp : Summable
      (fun q : {q : XiZeroCopy // q ∉ xiZeroCopyFiber ρ} =>
        xiRelativeResolventTerm z q) := hsum.subtype _
  have himsum :
      (∑' q : {q : XiZeroCopy // q ∉ xiZeroCopyFiber ρ},
          xiRelativeResolventTerm z q).im =
        ∑' q : {q : XiZeroCopy // q ∉ xiZeroCopyFiber ρ},
          (xiRelativeResolventTerm z q).im := by
    exact Complex.imCLM.map_tsum hcomp
  rw [himsum]
  refine tsum_nonpos fun q => ?_
  obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
  exact xiRelativeResolventTerm_im_nonpos
    (by
      rw [xiCenteredUpperHalfPlane, Set.mem_setOf_eq] at hz
      exact hz) ht

/-- RH makes every fixed-fiber-deflated source trace passive on the centered upper strip. -/
theorem fixedFiberDeflatedUpperAntiHerglotz_of_riemannHypothesis
    (hRH : RiemannHypothesis) (ρ : XiDivisorSupport) :
    FixedFiberDeflatedUpperAntiHerglotz ρ := by
  intro z hzpos hzhalf hzeta
  rw [ccmFixedFiberDeflatedRelativeTrace_eq_xiTrace_sub_fiber ρ
    (centeredAbscissa_re_pos hzhalf) (centeredAbscissa_ne_one hzpos) hzeta]
  exact xiRelativeResolventTrace_sub_fiber_im_nonpos_of_rh hRH ρ (by
    rw [xiCenteredUpperHalfPlane, Set.mem_setOf_eq]
    exact hzpos)

/-- At a critical fiber, residual passivity and the explicit Poisson-kernel source margin are the
same pointwise inequality. -/
theorem fixedFiberDeflatedUpperAntiHerglotz_iff_primeGammaPoissonMargin
    (ρ : XiDivisorSupport) (hρ : (ρ : ℂ).re = 1 / 2) :
    FixedFiberDeflatedUpperAntiHerglotz ρ ↔
      FixedFiberPrimeGammaPoissonMargin ρ := by
  have hαim : (xiSpectralPointSupport ρ).im = 0 :=
    (xiSpectralPointSupport_im_eq_zero_iff ρ).2 hρ
  constructor
  · intro h z hzpos hzhalf hzeta
    have hz := h z hzpos hzhalf hzeta
    rw [ccmFixedFiberDeflatedRelativeTrace_im_eq_add_poisson ρ z hαim] at hz
    linarith
  · intro h z hzpos hzhalf hzeta
    have hz := h z hzpos hzhalf hzeta
    rw [ccmFixedFiberDeflatedRelativeTrace_im_eq_add_poisson ρ z hαim]
    linarith

/-- Paying the positive Poisson floor at one critical fiber implies ordinary source passivity. -/
theorem continuedPrimeArchUpperAntiHerglotz_of_fixedFiberPrimeGammaPoissonMargin
    (ρ : XiDivisorSupport) (hmargin : FixedFiberPrimeGammaPoissonMargin ρ) :
    ContinuedPrimeArchUpperAntiHerglotz := by
  intro z hzpos hzhalf hzeta
  have hz := hmargin z hzpos hzhalf hzeta
  have hfloor : 0 ≤ ((xiZeroCopyFiber ρ).card : ℝ) * z.im /
      Complex.normSq (xiSpectralPointSupport ρ - z) :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) hzpos.le)
      (Complex.normSq_nonneg _)
  linarith

/-- For any fixed critical Xi fiber, passivity after deleting that fiber is exactly RH. -/
theorem riemannHypothesis_iff_fixedCriticalFiberDeflatedUpperAntiHerglotz
    (ρ : XiDivisorSupport) (hρ : (ρ : ℂ).re = 1 / 2) :
    RiemannHypothesis ↔ FixedFiberDeflatedUpperAntiHerglotz ρ := by
  constructor
  · intro hRH
    exact fixedFiberDeflatedUpperAntiHerglotz_of_riemannHypothesis hRH ρ
  · intro hdeflated
    apply continuedPrimeArchUpperAntiHerglotz_iff_riemannHypothesis.mp
    apply continuedPrimeArchUpperAntiHerglotz_of_fixedFiberPrimeGammaPoissonMargin ρ
    exact (fixedFiberDeflatedUpperAntiHerglotz_iff_primeGammaPoissonMargin ρ hρ).mp
      hdeflated

/-- The exact fixed-critical-fiber Poisson margin is itself an RH criterion. -/
theorem riemannHypothesis_iff_fixedCriticalFiberPrimeGammaPoissonMargin
    (ρ : XiDivisorSupport) (hρ : (ρ : ℂ).re = 1 / 2) :
    RiemannHypothesis ↔ FixedFiberPrimeGammaPoissonMargin ρ := by
  rw [riemannHypothesis_iff_fixedCriticalFiberDeflatedUpperAntiHerglotz ρ hρ,
    fixedFiberDeflatedUpperAntiHerglotz_iff_primeGammaPoissonMargin ρ hρ]

/-- Hardy supplies an unconditional critical fiber carrying the quantitative Poisson-margin RH
criterion. -/
theorem exists_hardyCriticalFiber_primeGammaPoissonMargin_criterion :
    ∃ ρ : XiDivisorSupport,
      (ρ : ℂ).re = 1 / 2 ∧
        (RiemannHypothesis ↔ FixedFiberPrimeGammaPoissonMargin ρ) := by
  obtain ⟨ρ, hρ⟩ := exists_criticalLine_xiDivisorSupport_of_hardy
  exact ⟨ρ, hρ,
    riemannHypothesis_iff_fixedCriticalFiberPrimeGammaPoissonMargin ρ hρ⟩

end

end RHTower
