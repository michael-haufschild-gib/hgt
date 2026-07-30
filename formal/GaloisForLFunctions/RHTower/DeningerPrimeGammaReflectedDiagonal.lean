import GaloisForLFunctions.RHTower.DeningerPrimeGammaPacketCohomology
import GaloisForLFunctions.RHTower.XiWeilHilbertCore
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangleExhaustion
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Reflected-diagonal comparison for prime--Gamma packet cohomology

The off-diagonal source kernel is already the divisor Cauchy polarization.  This file proves the
missing diagonal value.  Around every lower Euler parameter, the centered Xi divisor remains a
uniform positive distance away because all divisor points lie in `|Im z| < 1/2`.  The derivative
series is therefore locally dominated by four times the square-summable Cauchy evaluation.

Termwise differentiation gives

`R'(z) = -∑_q (xiSpectralPoint q - z)⁻²`.

Consequently the removable source value `-R'(z)` is exactly the squared-Cauchy divisor
polarization.  No positivity or RH is used.
-/

open Complex Metric

namespace RHTower

noncomputable section

private def deningerPrimeGammaDifferentiationRadius
    (z : DeningerPrimeGammaLowerPoint) : ℝ :=
  (-(1 / 2 : ℝ) - (z : ℂ).im) / 2

private theorem deningerPrimeGammaDifferentiationRadius_pos
    (z : DeningerPrimeGammaLowerPoint) :
    0 < deningerPrimeGammaDifferentiationRadius z := by
  have hz := z.property
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.div_re, Complex.one_re, Complex.one_im, Complex.re_ofNat,
    Complex.im_ofNat, Complex.normSq_apply] at hz
  norm_num at hz
  unfold deningerPrimeGammaDifferentiationRadius
  linarith

private theorem two_mul_deningerPrimeGammaDifferentiationRadius
    (z : DeningerPrimeGammaLowerPoint) :
    2 * deningerPrimeGammaDifferentiationRadius z =
      -(1 / 2 : ℝ) - (z : ℂ).im := by
  unfold deningerPrimeGammaDifferentiationRadius
  ring

private theorem two_mul_deningerPrimeGammaDifferentiationRadius_lt_norm_sub
    (z : DeningerPrimeGammaLowerPoint) (q : XiZeroCopy) :
    2 * deningerPrimeGammaDifferentiationRadius z <
      ‖xiSpectralPoint q - (z : ℂ)‖ := by
  have hq := (xiSpectralPoint_im_mem_openHalf q).1
  have him :
      (xiSpectralPoint q).im - (z : ℂ).im ≤
        |(xiSpectralPoint q - (z : ℂ)).im| := by
    rw [Complex.sub_im]
    exact le_abs_self _
  have hnorm := Complex.abs_im_le_norm (xiSpectralPoint q - (z : ℂ))
  rw [two_mul_deningerPrimeGammaDifferentiationRadius]
  calc
    -(1 / 2 : ℝ) - (z : ℂ).im <
        (xiSpectralPoint q).im - (z : ℂ).im := by linarith
    _ ≤ |(xiSpectralPoint q - (z : ℂ)).im| := him
    _ ≤ ‖xiSpectralPoint q - (z : ℂ)‖ := hnorm

private theorem half_norm_sub_lt_norm_sub_of_mem_differentiationBall
    (z : DeningerPrimeGammaLowerPoint) (q : XiZeroCopy) {u : ℂ}
    (hu : u ∈ Metric.ball (z : ℂ)
      (deningerPrimeGammaDifferentiationRadius z)) :
    ‖xiSpectralPoint q - (z : ℂ)‖ / 2 <
      ‖xiSpectralPoint q - u‖ := by
  have hur :
      ‖u - (z : ℂ)‖ < deningerPrimeGammaDifferentiationRadius z := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hu
  have htri :
      ‖xiSpectralPoint q - (z : ℂ)‖ ≤
        ‖xiSpectralPoint q - u‖ + ‖u - (z : ℂ)‖ := by
    calc
      ‖xiSpectralPoint q - (z : ℂ)‖ =
          ‖(xiSpectralPoint q - u) + (u - (z : ℂ))‖ := by ring_nf
      _ ≤ ‖xiSpectralPoint q - u‖ + ‖u - (z : ℂ)‖ := norm_add_le _ _
  have hsep :=
    two_mul_deningerPrimeGammaDifferentiationRadius_lt_norm_sub z q
  linarith

private theorem hasDerivAt_xiRelativeResolventTerm
    (q : XiZeroCopy) {u : ℂ} (hqu : xiSpectralPoint q ≠ u) :
    HasDerivAt (fun v => xiRelativeResolventTerm v q)
      (-((xiSpectralPoint q - u)⁻¹ ^ 2)) u := by
  change HasDerivAt
    (fun v => (xiSpectralPoint q)⁻¹ - (xiSpectralPoint q - v)⁻¹)
    (-((xiSpectralPoint q - u)⁻¹ ^ 2)) u
  have hsub : xiSpectralPoint q - u ≠ 0 := sub_ne_zero.mpr hqu
  convert! (hasDerivAt_const (x := u) (c := (xiSpectralPoint q)⁻¹)).sub
    (((hasDerivAt_const (x := u) (c := xiSpectralPoint q)).sub
      (hasDerivAt_id (𝕜 := ℂ) (x := u))).inv hsub) using 1
  simp

private theorem norm_xiRelativeResolventTerm_deriv_le
    (z : DeningerPrimeGammaLowerPoint) (q : XiZeroCopy) {u : ℂ}
    (hu : u ∈ Metric.ball (z : ℂ)
      (deningerPrimeGammaDifferentiationRadius z)) :
    ‖-((xiSpectralPoint q - u)⁻¹ ^ 2)‖ ≤
      4 * ‖xiWeilCauchyTest (z : ℂ) (xiSpectralPoint q)‖ ^ 2 := by
  have hhalf :=
    (half_norm_sub_lt_norm_sub_of_mem_differentiationBall z q hu).le
  have haz : 0 < ‖xiSpectralPoint q - (z : ℂ)‖ := by
    exact norm_pos_iff.mpr (sub_ne_zero.mpr fun h =>
      (XiC_ne_zero_of_one_lt_centered_re z.property)
        ((XiC_eq_zero_iff_exists_xiZeroCopy (z : ℂ)).mpr ⟨q, h⟩))
  have hau : 0 < ‖xiSpectralPoint q - u‖ :=
    lt_of_lt_of_le (half_pos haz) hhalf
  have hinv :
      ‖xiSpectralPoint q - u‖⁻¹ ≤
        2 * ‖xiSpectralPoint q - (z : ℂ)‖⁻¹ := by
    have h := one_div_le_one_div_of_le (half_pos haz) hhalf
    rw [one_div, one_div, inv_div] at h
    simpa [mul_comm] using! h
  rw [norm_neg, norm_pow, norm_inv, xiWeilCauchyTest, norm_inv]
  calc
    ‖xiSpectralPoint q - u‖⁻¹ ^ 2 ≤
        (2 * ‖xiSpectralPoint q - (z : ℂ)‖⁻¹) ^ 2 := by
      gcongr
    _ = 4 * ‖xiSpectralPoint q - (z : ℂ)‖⁻¹ ^ 2 := by ring

/-- The relative-resolvent trace is locally termwise differentiable below the Xi strip. -/
theorem hasDerivAt_xiRelativeResolventTrace_of_eulerPoint
    (z : DeningerPrimeGammaLowerPoint) :
    HasDerivAt xiRelativeResolventTrace
      (∑' q : XiZeroCopy, -((xiSpectralPoint q - (z : ℂ))⁻¹ ^ 2))
      (z : ℂ) := by
  let r := deningerPrimeGammaDifferentiationRadius z
  let majorant : XiZeroCopy → ℝ := fun q =>
    4 * ‖xiWeilCauchyTest (z : ℂ) (xiSpectralPoint q)‖ ^ 2
  have hr : 0 < r := deningerPrimeGammaDifferentiationRadius_pos z
  have hmajorant : Summable majorant :=
    (XiWeilSquareSummable_cauchy (z : ℂ)).mul_left 4
  have hbase :
      Summable (fun q : XiZeroCopy => xiRelativeResolventTerm (z : ℂ) q) :=
    summable_xiRelativeResolventTerm
      (XiC_ne_zero_of_one_lt_centered_re z.property)
  have hderiv :
      ∀ q : XiZeroCopy, ∀ u ∈ Metric.ball (z : ℂ) r,
        HasDerivAt (fun v => xiRelativeResolventTerm v q)
          (-((xiSpectralPoint q - u)⁻¹ ^ 2)) u := by
    intro q u hu
    apply hasDerivAt_xiRelativeResolventTerm
    exact sub_ne_zero.mp (norm_ne_zero_iff.mp
      (ne_of_gt (lt_of_lt_of_le
        (half_pos (norm_pos_iff.mpr (sub_ne_zero.mpr fun h =>
          (XiC_ne_zero_of_one_lt_centered_re z.property)
            ((XiC_eq_zero_iff_exists_xiZeroCopy (z : ℂ)).mpr ⟨q, h⟩))))
        (half_norm_sub_lt_norm_sub_of_mem_differentiationBall z q hu).le)))
  have hbound :
      ∀ q : XiZeroCopy, ∀ u ∈ Metric.ball (z : ℂ) r,
        ‖-((xiSpectralPoint q - u)⁻¹ ^ 2)‖ ≤ majorant q := by
    intro q u hu
    exact norm_xiRelativeResolventTerm_deriv_le z q hu
  change HasDerivAt
    (fun u => ∑' q : XiZeroCopy, xiRelativeResolventTerm u q)
    (∑' q : XiZeroCopy, -((xiSpectralPoint q - (z : ℂ))⁻¹ ^ 2))
    (z : ℂ)
  exact hasDerivAt_tsum_of_isPreconnected hmajorant Metric.isOpen_ball
    (convex_ball (z : ℂ) r).isPreconnected hderiv hbound
    (Metric.mem_ball_self hr) hbase (Metric.mem_ball_self hr)

/--
The removable reflected-diagonal prime--Gamma kernel equals the divisor-side squared-Cauchy Weil
polarization.  This closes the atomic source/target comparison at every pair of Euler points.
-/
theorem deningerPrimeGammaSourceKernel_eq_xiWeilPolarization_reflectedDiagonal
    (z : DeningerPrimeGammaLowerPoint) :
    deningerPrimeGammaSourceKernel z (deningerPrimeGammaPointConjEquiv z) =
      xiWeilPolarization
        (xiWeilCauchyTest (z : ℂ))
        (xiWeilCauchyTest
          (deningerPrimeGammaPointConjEquiv z : ℂ)) := by
  rw [deningerPrimeGammaSourceKernel_reflectedDiagonal,
    deriv_primeArchSourceRelativeTrace_eq_deriv_xiRelativeResolventTrace,
    (hasDerivAt_xiRelativeResolventTrace_of_eulerPoint z).deriv]
  rw [xiWeilPolarization]
  calc
    -(∑' q : XiZeroCopy, -((xiSpectralPoint q - (z : ℂ))⁻¹ ^ 2)) =
        ∑' q : XiZeroCopy, (xiSpectralPoint q - (z : ℂ))⁻¹ ^ 2 := by
      rw [← tsum_neg]
      simp
    _ = ∑' q : XiZeroCopy,
        xiWeilCauchyTest (z : ℂ) (xiSpectralPoint q) *
          xiWeilSharp
            (xiWeilCauchyTest
              (deningerPrimeGammaPointConjEquiv z : ℂ))
            (xiSpectralPoint q) := by
      apply tsum_congr
      intro q
      rw [xiWeilSharp_cauchy]
      simp only [deningerPrimeGammaPointConjEquiv, Equiv.coe_fn_mk,
        starRingEnd_self_apply, xiWeilCauchyTest]
      ring

/-- Every lower/upper source atom has an absolutely summable divisor-side Weil pair. -/
theorem xiWeilPairSummable_deningerPrimeGammaAtoms
    (z : DeningerPrimeGammaLowerPoint)
    (w : DeningerPrimeGammaUpperPoint) :
    XiWeilPairSummable
      (xiWeilCauchyTest (z : ℂ))
      (xiWeilCauchyTest (w : ℂ)) := by
  by_cases hzw : (z : ℂ) = (starRingEnd ℂ) (w : ℂ)
  · unfold XiWeilPairSummable
    apply Summable.of_norm
    apply (XiWeilSquareSummable_cauchy (z : ℂ)).congr
    intro q
    rw [xiWeilSharp_cauchy]
    simp only [hzw, norm_mul, pow_two]
  · exact xiWeilPairSummable_cauchy
      (XiC_ne_zero_of_one_lt_centered_re z.property)
      (XiC_ne_zero_of_one_lt_centered_re w.property) hzw

/-- Complete atomic source/target comparison, including the reflected diagonal. -/
theorem deningerPrimeGammaSourceKernel_eq_xiWeilPolarization
    (z : DeningerPrimeGammaLowerPoint)
    (w : DeningerPrimeGammaUpperPoint) :
    deningerPrimeGammaSourceKernel z w =
      xiWeilPolarization
        (xiWeilCauchyTest (z : ℂ))
        (xiWeilCauchyTest (w : ℂ)) := by
  by_cases hzw : (z : ℂ) = (starRingEnd ℂ) (w : ℂ)
  · have hw : w = deningerPrimeGammaPointConjEquiv z := by
      apply Subtype.ext
      have h := congrArg (starRingEnd ℂ) hzw
      simpa [deningerPrimeGammaPointConjEquiv] using h.symm
    subst w
    exact
      deningerPrimeGammaSourceKernel_eq_xiWeilPolarization_reflectedDiagonal z
  · exact deningerPrimeGammaSourceKernel_eq_xiWeilPolarization_of_ne z w hzw

/-- Divisor test represented by a finite lower source packet. -/
def deningerPrimeGammaLowerCauchyTest
    (x : DeningerPrimeGammaLowerPacket) (a : ℂ) : ℂ :=
  x.sum fun z c => c * xiWeilCauchyTest (z : ℂ) a

/--
The sharp transform of the divisor test represented by an upper source packet.
Using this as the second Weil argument makes its source coefficients linear.
-/
def deningerPrimeGammaUpperSharpCauchyTest
    (y : DeningerPrimeGammaUpperPacket) (a : ℂ) : ℂ :=
  y.sum fun w d =>
    d * xiWeilCauchyTest ((starRingEnd ℂ) (w : ℂ)) a

/-- Anti-linear upper packet realization whose Weil sharp is the linear sharp test above. -/
def deningerPrimeGammaUpperCauchyTest
    (y : DeningerPrimeGammaUpperPacket) : ℂ → ℂ :=
  xiWeilSharp (deningerPrimeGammaUpperSharpCauchyTest y)

@[simp]
theorem xiWeilSharp_deningerPrimeGammaUpperCauchyTest
    (y : DeningerPrimeGammaUpperPacket) (a : ℂ) :
    xiWeilSharp (deningerPrimeGammaUpperCauchyTest y) a =
      deningerPrimeGammaUpperSharpCauchyTest y a := by
  simp [deningerPrimeGammaUpperCauchyTest, xiWeilSharp]

/-- The bundled source cup map is exactly the finite double kernel sum. -/
theorem deningerPrimeGammaSourceCup_eq_sum
    (x : DeningerPrimeGammaLowerPacket)
    (y : DeningerPrimeGammaUpperPacket) :
    deningerPrimeGammaSourceCup x y =
      x.sum fun z c =>
        y.sum fun w d => c * d * deningerPrimeGammaSourceKernel z w := by
  classical
  simp [deningerPrimeGammaSourceCup, deningerPrimeGammaSourceKernelLinear,
    Finsupp.lsum, LinearMap.toSpanSingleton, smul_eq_mul]
  apply Finsupp.sum_congr
  intro z hz
  rw [Finsupp.mul_sum]
  apply Finsupp.sum_congr
  intro w hw
  ring

/--
Every finite source packet pairing equals the multiplicity-exact divisor Weil polarization.
The source side remains the definition; divisor data enter only in this comparison theorem.
-/
theorem deningerPrimeGammaSourceCup_eq_xiWeilPolarization
    (x : DeningerPrimeGammaLowerPacket)
    (y : DeningerPrimeGammaUpperPacket) :
    deningerPrimeGammaSourceCup x y =
      xiWeilPolarization
        (deningerPrimeGammaLowerCauchyTest x)
        (deningerPrimeGammaUpperCauchyTest y) := by
  classical
  let term :
      DeningerPrimeGammaLowerPoint →
        DeningerPrimeGammaUpperPoint → XiZeroCopy → ℂ :=
    fun z w q =>
      x z * y w *
        (xiWeilCauchyTest (z : ℂ) (xiSpectralPoint q) *
          xiWeilSharp (xiWeilCauchyTest (w : ℂ)) (xiSpectralPoint q))
  have hterm (z : DeningerPrimeGammaLowerPoint)
      (w : DeningerPrimeGammaUpperPoint) :
      Summable (term z w) := by
    exact (xiWeilPairSummable_deningerPrimeGammaAtoms z w).mul_left
      (x z * y w)
  rw [deningerPrimeGammaSourceCup_eq_sum, xiWeilPolarization]
  calc
    x.sum (fun z c =>
        y.sum fun w d => c * d * deningerPrimeGammaSourceKernel z w) =
        x.sum (fun z c =>
          y.sum fun w d =>
            c * d *
              xiWeilPolarization
                (xiWeilCauchyTest (z : ℂ))
                (xiWeilCauchyTest (w : ℂ))) := by
      apply Finsupp.sum_congr
      intro z hz
      apply Finsupp.sum_congr
      intro w hw
      rw [deningerPrimeGammaSourceKernel_eq_xiWeilPolarization]
    _ = ∑' q : XiZeroCopy,
        deningerPrimeGammaLowerCauchyTest x (xiSpectralPoint q) *
          xiWeilSharp (deningerPrimeGammaUpperCauchyTest y)
            (xiSpectralPoint q) := by
      simp only [deningerPrimeGammaLowerCauchyTest,
        xiWeilSharp_deningerPrimeGammaUpperCauchyTest,
        deningerPrimeGammaUpperSharpCauchyTest]
      simp only [xiWeilPolarization]
      calc
        x.sum (fun z c =>
            y.sum fun w d =>
              c * d *
                ∑' q : XiZeroCopy,
                  xiWeilCauchyTest (z : ℂ) (xiSpectralPoint q) *
                    xiWeilSharp (xiWeilCauchyTest (w : ℂ))
                      (xiSpectralPoint q)) =
            x.sum (fun z c =>
              y.sum fun w d => ∑' q : XiZeroCopy, term z w q) := by
          apply Finsupp.sum_congr
          intro z hz
          apply Finsupp.sum_congr
          intro w hw
          rw [tsum_mul_left]
        _ = ∑' q : XiZeroCopy,
            x.sum (fun z c =>
              y.sum fun w d => term z w q) := by
          change
            (∑ z ∈ x.support, ∑ w ∈ y.support,
              ∑' q : XiZeroCopy, term z w q) =
              ∑' q : XiZeroCopy, ∑ z ∈ x.support, ∑ w ∈ y.support, term z w q
          rw [Summable.tsum_finsetSum
            (fun z hz => summable_sum fun w hw => hterm z w)]
          apply Finset.sum_congr rfl
          intro z hz
          rw [Summable.tsum_finsetSum (fun w hw => hterm z w)]
        _ = ∑' q : XiZeroCopy,
            (x.sum fun z c =>
              c * xiWeilCauchyTest (z : ℂ) (xiSpectralPoint q)) *
              (y.sum fun w d =>
                d * xiWeilCauchyTest ((starRingEnd ℂ) (w : ℂ))
                  (xiSpectralPoint q)) := by
          apply tsum_congr
          intro q
          rw [Finsupp.sum_mul]
          apply Finsupp.sum_congr
          intro z hz
          rw [Finsupp.mul_sum]
          apply Finsupp.sum_congr
          intro w hw
          simp only [term]
          rw [xiWeilSharp_cauchy]
          ring

end

end RHTower
