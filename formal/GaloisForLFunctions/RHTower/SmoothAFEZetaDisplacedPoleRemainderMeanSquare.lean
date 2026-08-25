import GaloisForLFunctions.RHTower.SmoothAFEZetaDisplacedPoleDecay

/-!
# Mean square for displaced mollified pole remainders

The pointwise Gaussian envelope is integrated on every positive subwindow.  This closes the two
literal pole terms without mixing them into direct/reflected polynomial main terms.
-/

noncomputable section

namespace RHTower

open Complex MeasureTheory Set

theorem continuous_smoothAFEZetaShiftedPoleResidue_displaced
    {d x : ℝ} (hd : 0 < d) (hx : 0 < x) :
    Continuous (fun t : ℝ =>
      smoothAFEZetaShiftedPoleResidue (displacedLinePt d t) x) := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (hasDerivAt_smoothAFEZetaShiftedPoleResidue_displaced hd hx t).continuousAt

theorem continuous_smoothAFEZetaDisplacedPoleResidueHeightDerivative
    {d x : ℝ} (hd : 0 < d) (hx : 0 < x) :
    Continuous (smoothAFEZetaDisplacedPoleResidueHeightDerivative d x) := by
  rw [continuous_iff_continuousAt]
  intro t
  let z : ℝ → ℂ := fun u => smoothAFEZetaDisplacedPoleCoordinate d u
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hz0 : z t ≠ 0 :=
    smoothAFEZetaDisplacedPoleCoordinate_ne_zero hd t
  have hz : ContinuousAt z t := by
    dsimp only [z, smoothAFEZetaDisplacedPoleCoordinate, displacedLinePt]
    fun_prop
  have hA : ContinuousAt (fun u : ℝ => (x : ℂ) ^ z u) t :=
    (Complex.hasStrictDerivAt_const_cpow
      (x := (x : ℂ)) (y := z t) (Or.inl hxC)).hasDerivAt.continuousAt.comp hz
  have hE : ContinuousAt (fun u : ℝ => Complex.exp ((z u) ^ 2)) t :=
    (hz.pow 2).cexp
  have hAz : ContinuousAt
      (fun u : ℝ => ((x : ℂ) ^ z u * Complex.log (x : ℂ)) * (-I)) t :=
    (hA.mul continuousAt_const).mul continuousAt_const
  have hEz : ContinuousAt
      (fun u : ℝ => Complex.exp ((z u) ^ 2) * (2 * z u * (-I))) t :=
    hE.mul ((continuousAt_const.mul hz).mul continuousAt_const)
  have hnum : ContinuousAt
      (fun u : ℝ =>
        ((((x : ℂ) ^ z u * Complex.log (x : ℂ)) * (-I) *
              Complex.exp ((z u) ^ 2) +
            (x : ℂ) ^ z u *
              (Complex.exp ((z u) ^ 2) * (2 * z u * (-I)))) * z u -
          ((x : ℂ) ^ z u * Complex.exp ((z u) ^ 2)) * (-I))) t :=
    (((hAz.mul hE).add (hA.mul hEz)).mul hz).sub
      ((hA.mul hE).mul continuousAt_const)
  have hden : ContinuousAt (fun u : ℝ => (z u) ^ 2) t := hz.pow 2
  have hquot := hnum.div hden (pow_ne_zero 2 hz0)
  unfold smoothAFEZetaDisplacedPoleResidueHeightDerivative
  dsimp only
  convert hquot using 1
  funext u
  rfl

theorem continuous_smoothAFEZetaDisplacedMollifiedPoleRemainder
    {d x : ℝ} (hd : 0 < d) (hx : 0 < x) (lam : ℝ) (M : ℕ) :
    Continuous (smoothAFEZetaDisplacedMollifiedPoleRemainder lam d x M) := by
  have hres := continuous_smoothAFEZetaShiftedPoleResidue_displaced hd hx
  have hder := continuous_smoothAFEZetaDisplacedPoleResidueHeightDerivative hd hx
  rw [show smoothAFEZetaDisplacedMollifiedPoleRemainder lam d x M =
      fun t : ℝ =>
        -smoothAFEZetaShiftedPoleResidue (displacedLinePt d t) x *
            Sieve.levinsonLinearMollifier M t +
          (lam : ℂ) * I *
            smoothAFEZetaDisplacedPoleResidueHeightDerivative d x t *
              Sieve.levinsonLinearMollifier M t by rfl]
  exact (hres.neg.mul (continuous_levinsonLinearMollifier M)).add
    (((continuous_const.mul continuous_const).mul hder).mul
      (continuous_levinsonLinearMollifier M))

/-- Gaussian mean-square bound for both pole remainders on any positive interval above `T`. -/
theorem integral_smoothAFEZetaDisplacedMollifiedPoleRemainder_normSq_le
    {lam d x T a b : ℝ} (hd : 0 < d) (hx : 0 < x)
    (hT : 1 ≤ T) (haT : T ≤ a) (hab : a ≤ b)
    {M : ℕ} (hM : 1 < M) :
    (∫ t in a..b,
      ‖smoothAFEZetaDisplacedMollifiedPoleRemainder lam d x M t‖ ^ 2) ≤
      (b - a) *
        ((2 * Real.sqrt M) *
          (x ^ (1 / 2 + d) * Real.exp ((1 / 2 + d) ^ 2)) *
          (1 + |lam| * (|Real.log x| + 3)) *
          Real.exp (-(T ^ 2))) ^ 2 := by
  let C : ℝ := (2 * Real.sqrt M) *
    (x ^ (1 / 2 + d) * Real.exp ((1 / 2 + d) ^ 2)) *
    (1 + |lam| * (|Real.log x| + 3))
  have hC0 : 0 ≤ C := by dsimp only [C]; positivity
  have hpoint : ∀ t ∈ Set.Icc a b,
      ‖smoothAFEZetaDisplacedMollifiedPoleRemainder lam d x M t‖ ^ 2 ≤
        (C * Real.exp (-(T ^ 2))) ^ 2 := by
    intro t ht
    have ht1 : 1 ≤ |t| := by
      have htpos : 0 ≤ t := by linarith [hT, haT, ht.1]
      rw [abs_of_nonneg htpos]
      linarith [hT, haT, ht.1]
    have hrem := norm_smoothAFEZetaDisplacedMollifiedPoleRemainder_le
      (lam := lam) hd hx ht1 hM
    change ‖smoothAFEZetaDisplacedMollifiedPoleRemainder lam d x M t‖ ≤
      C * Real.exp (-(t ^ 2)) at hrem
    have hsquare : T ^ 2 ≤ t ^ 2 := by
      have hT0 : 0 ≤ T := by linarith
      have htt : T ≤ t := haT.trans ht.1
      nlinarith
    have hexp : Real.exp (-(t ^ 2)) ≤ Real.exp (-(T ^ 2)) :=
      Real.exp_le_exp.mpr (by linarith)
    have hnorm := hrem.trans (mul_le_mul_of_nonneg_left hexp hC0)
    have hright0 : 0 ≤ C * Real.exp (-(T ^ 2)) := by positivity
    nlinarith [norm_nonneg
      (smoothAFEZetaDisplacedMollifiedPoleRemainder lam d x M t)]
  have hcont :=
    (continuous_smoothAFEZetaDisplacedMollifiedPoleRemainder hd hx lam M).norm.pow 2
  have hmono := intervalIntegral.integral_mono_on hab
    (hcont.intervalIntegrable (μ := MeasureTheory.volume) a b)
    (continuous_const.intervalIntegrable (μ := MeasureTheory.volume) a b) hpoint
  change (∫ t in a..b,
    ‖smoothAFEZetaDisplacedMollifiedPoleRemainder lam d x M t‖ ^ 2) ≤ _
  refine hmono.trans_eq ?_
  simp only [intervalIntegral.integral_const]
  dsimp only [C]
  ring

end RHTower
