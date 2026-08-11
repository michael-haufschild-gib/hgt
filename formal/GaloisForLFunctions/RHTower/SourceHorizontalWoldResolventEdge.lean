import GaloisForLFunctions.RHTower.SourceHorizontalWoldEulerGreenAnomaly
import GaloisForLFunctions.RHTower.XiResolventDiagonalEdgeDetection
import GaloisForLFunctions.HTGeometry.DiagonalMomentEdgeDetection

/-!
# Source-horizontal Wold carrier meets the Xi resolvent edge

This module constructs a literal Frankenstein seam.  The nonlinear Wold polar work selects every
off-critical Xi divisor copy, preserving its multiplicity label and both reflection orientations.
On that source-selected carrier, diagonal resolvent moment positivity alone is impossible unless
the carrier is empty: abstract edge detection would produce a positive-real maximal resolvent
atom, while positive Wold work says that same copy is off the critical line.

Hence RH is equivalent to nonnegativity of all diagonal moments on the positive-polar-work
carrier.  This is thinner than the full resolvent Hankel cone.  It remains a receiver until a
pre-zero source trace identifies and orients these selected moments.
-/

open Complex

namespace RHTower

noncomputable section

/-- Multiplicity-labelled Xi copies on which the source-horizontal nonlinear polar work is
strictly positive.  By the Wold profile law, these are exactly the off-critical copies. -/
abbrev SourceHorizontalWoldPositivePolarCopy :=
  {q : XiZeroCopy // 0 < sourceZeroHorizontalWoldPrimeClockPolarWork q}

/-- Diagonal resolvent moments restricted by the source-horizontal positive polar carrier. -/
def sourceHorizontalWoldPositivePolarResolventMoment (n : ℕ) (X : ℝ) : ℂ :=
  ∑' q : SourceHorizontalWoldPositivePolarCopy,
    xiResolventPoint X q.1 ^ (n + 1)

theorem summable_norm_sourceHorizontalWoldPositivePolarResolventPoint
    {X : ℝ} (hX : 0 ≤ X) :
    Summable (fun q : SourceHorizontalWoldPositivePolarCopy =>
      ‖xiResolventPoint X q.1‖) :=
  (summable_norm_xiResolventPoint hX).subtype _

theorem summable_norm_sourceHorizontalWoldPositivePolarResolventPoint_pow
    {X : ℝ} (hX : 0 ≤ X) (n : ℕ) :
    Summable (fun q : SourceHorizontalWoldPositivePolarCopy =>
      ‖xiResolventPoint X q.1 ^ (n + 1)‖) :=
  (summable_norm_xiResolventPoint_pow hX n).subtype _

/-- A positive-real Xi resolvent atom has critical horizontal coordinate. -/
theorem xiZeroCopy_re_eq_half_of_xiResolventPoint_eq_norm
    {X : ℝ} (q : XiZeroCopy)
    (hreal : xiResolventPoint X q = (‖xiResolventPoint X q‖ : ℂ)) :
    (q.1 : ℂ).re = 1 / 2 := by
  have hwreal : xiSpectralPoint q ^ 2 + (X : ℂ) =
      ((‖xiResolventPoint X q‖ : ℝ) : ℂ)⁻¹ := by
    have h2 : ((xiSpectralPoint q ^ 2 + (X : ℂ))⁻¹) =
        ((‖xiResolventPoint X q‖ : ℝ) : ℂ) := hreal
    calc
      xiSpectralPoint q ^ 2 + (X : ℂ)
          = ((xiSpectralPoint q ^ 2 + (X : ℂ))⁻¹)⁻¹ := (inv_inv _).symm
      _ = ((‖xiResolventPoint X q‖ : ℝ) : ℂ)⁻¹ := by rw [h2]
  have himsq : (xiSpectralPoint q ^ 2).im = 0 := by
    have h3 : (xiSpectralPoint q ^ 2 + (X : ℂ)).im = 0 := by
      rw [hwreal, ← Complex.ofReal_inv]
      exact Complex.ofReal_im _
    rw [Complex.add_im, Complex.ofReal_im, add_zero] at h3
    exact h3
  have hprod : 2 * (xiSpectralPoint q).re * (xiSpectralPoint q).im = 0 := by
    have h4 : (xiSpectralPoint q ^ 2).im =
        2 * (xiSpectralPoint q).re * (xiSpectralPoint q).im := by
      rw [sq, Complex.mul_im]
      ring
    rw [h4] at himsq
    exact himsq
  have hrene : (xiSpectralPoint q).re ≠ 0 := by
    have h := xiZeroCopy_two_lt_im_sq q
    rw [← xiSpectralPoint_re_eq] at h
    intro h0
    rw [h0] at h
    norm_num at h
  have him0 : (xiSpectralPoint q).im = 0 := by
    rcases mul_eq_zero.mp hprod with h2 | h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · norm_num at h3
      · exact absurd h3 hrene
    · exact h2
  rw [xiSpectralPoint] at him0
  norm_num [mul_im] at him0
  linarith

/-- **Frankenstein edge collapse.**  If every diagonal resolvent moment on the exact
positive-polar-work carrier is nonnegative at one nonnegative shift, then that carrier is empty. -/
theorem isEmpty_sourceHorizontalWoldPositivePolarCopy_of_forall_moment_re_nonneg
    {X : ℝ} (hX : 0 ≤ X)
    (hmom : ∀ n : ℕ,
      0 ≤ (sourceHorizontalWoldPositivePolarResolventMoment n X).re) :
    IsEmpty SourceHorizontalWoldPositivePolarCopy := by
  constructor
  intro qa
  letI : Nonempty SourceHorizontalWoldPositivePolarCopy := ⟨qa⟩
  obtain ⟨q, hqreal, _hqmax⟩ :=
    GaloisForLFunctions.HTGeometry.exists_positiveReal_maximal_of_forall_powerMoment_re_nonneg
      (fun q : SourceHorizontalWoldPositivePolarCopy => xiResolventPoint X q.1)
      (fun q => xiResolventPoint_ne_zero hX q.1)
      (fun {r} hr => by
        have hpre := Set.Finite.preimage
          (f := fun q : SourceHorizontalWoldPositivePolarCopy => q.1)
          Subtype.val_injective.injOn
          (finite_setOf_le_norm_xiResolventPoint hX hr)
        simpa only [Set.preimage_setOf_eq] using hpre)
      (summable_norm_sourceHorizontalWoldPositivePolarResolventPoint hX)
      (summable_norm_sourceHorizontalWoldPositivePolarResolventPoint_pow hX)
      (fun n => by
        simpa only [sourceHorizontalWoldPositivePolarResolventMoment] using hmom n)
  have hline : (q.1.1 : ℂ).re = 1 / 2 :=
    xiZeroCopy_re_eq_half_of_xiResolventPoint_eq_norm q.1 hqreal
  exact ((sourceZeroHorizontalWoldPrimeClockPolarWork_pos_iff 0 q.1).1 q.2) hline

/-- Diagonal positivity on the source-horizontal positive-work carrier forces RH. -/
theorem riemannHypothesis_of_forall_sourceHorizontalWoldPositivePolarResolventMoment_re_nonneg
    {X : ℝ} (hX : 0 ≤ X)
    (hmom : ∀ n : ℕ,
      0 ≤ (sourceHorizontalWoldPositivePolarResolventMoment n X).re) :
    RiemannHypothesis := by
  have hempty :=
    isEmpty_sourceHorizontalWoldPositivePolarCopy_of_forall_moment_re_nonneg hX hmom
  have hline : ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2 := by
    intro q
    by_contra hq
    have hpos : 0 < sourceZeroHorizontalWoldPrimeClockPolarWork q :=
      (sourceZeroHorizontalWoldPrimeClockPolarWork_pos_iff 0 q).2 hq
    exact hempty.false ⟨q, hpos⟩
  apply riemannHypothesis_of_xiSpectralPoint_real
  intro q
  refine ⟨(q.1 : ℂ).im, ?_⟩
  apply Complex.ext
  · simp [xiSpectralPoint]
  · simp [xiSpectralPoint, hline q]

/-- **Exact source-horizontal/resolvent endpoint.**  At every nonnegative shift, RH is equivalent
to nonnegativity of the diagonal moments carried only by positive nonlinear Wold work. -/
theorem forall_sourceHorizontalWoldPositivePolarResolventMoment_re_nonneg_iff_riemannHypothesis
    {X : ℝ} (hX : 0 ≤ X) :
    (∀ n : ℕ, 0 ≤ (sourceHorizontalWoldPositivePolarResolventMoment n X).re) ↔
      RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_forall_sourceHorizontalWoldPositivePolarResolventMoment_re_nonneg
      hX
  · intro hRH n
    letI : IsEmpty SourceHorizontalWoldPositivePolarCopy := by
      constructor
      intro q
      have hline := xi_divisor_support_re_eq_half_of_rh hRH q.1.1
      exact ((sourceZeroHorizontalWoldPrimeClockPolarWork_pos_iff 0 q.1).1 q.2) hline
    simp [sourceHorizontalWoldPositivePolarResolventMoment]

end

end RHTower
