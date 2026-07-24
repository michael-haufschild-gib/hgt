import GaloisForLFunctions.RHTower.XiWeilPolarization
import GaloisForLFunctions.RHTower.XiGuinandWeilExplicitFormula

/-!
# The Weil Gram matrix on the resolvent test algebra

The Weil polarization pairs a test function with the sharp-reflected one, so on a
finite superposition `F = ∑ c i · K (z i)` of regularized Cauchy kernels it is the
Hermitian form of the Gram matrix

`M i j = ∑' q, K (z i) (pt q) · K (conj (z j)) (pt q)`.

The algebra of regularized Cauchy kernels closes under multiplication modulo a
single new generator: for distinct nonzero base points

`K z · K z' = (·)⁻² − (z'/(z(z−z')))·K z + (z/(z'(z−z')))·K z'`.

Consequently every Gram entry is an explicit combination of the second inverse
moment of the divisor and two values of the relative resolvent trace — that is,
of the logarithmic derivative of the completed zeta, whose prime–archimedean
evaluation is the Guinand–Weil explicit formula.  The Weil form on this algebra
is therefore evaluable from arithmetic data alone, with no reference to the
location of the zeros.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## §1 The product closure of the kernel algebra -/

/-- **Closure identity.**  The pointwise product of two regularized Cauchy
kernels is the inverse square plus an explicit linear combination of the two
kernels: the test algebra closes under multiplication modulo the single
generator `w ↦ w⁻²`. -/
theorem xiCauchyRegularizedKernel_mul {z z' w : ℂ} (hz : z ≠ 0) (hz' : z' ≠ 0)
    (hzz' : z ≠ z') (hw : w ≠ 0) (hwz : w ≠ z) (hwz' : w ≠ z') :
    xiCauchyRegularizedKernel z w * xiCauchyRegularizedKernel z' w =
      w⁻¹ * w⁻¹ - (z' / (z * (z - z'))) * xiCauchyRegularizedKernel z w +
        (z / (z' * (z - z'))) * xiCauchyRegularizedKernel z' w := by
  have hwz0 : w - z ≠ 0 := sub_ne_zero.mpr hwz
  have hwz'0 : w - z' ≠ 0 := sub_ne_zero.mpr hwz'
  have hd : z - z' ≠ 0 := sub_ne_zero.mpr hzz'
  unfold xiCauchyRegularizedKernel
  field_simp
  ring

/-- The second inverse moment of the centered divisor. -/
def xiSecondInverseMoment : ℂ := ∑' q : XiZeroCopy, (xiSpectralPoint q)⁻¹ ^ 2

theorem summable_xiSpectralPoint_inv_sq :
    Summable (fun q : XiZeroCopy => (xiSpectralPoint q)⁻¹ ^ 2) := by
  refine Summable.of_norm_bounded xiSpectralPoint_inv_sq_summable (fun q => ?_)
  have hne : xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero q
  rw [norm_pow, norm_inv, one_div, ← inv_pow]

/-! ## §2 The Gram entries -/

/-- The Weil Gram entry of two base points, as a spectral sum. -/
def xiWeilGramEntry (z z' : ℂ) : ℂ :=
  ∑' q : XiZeroCopy,
    xiCauchyRegularizedKernel z (xiSpectralPoint q) *
      xiCauchyRegularizedKernel z' (xiSpectralPoint q)

/-- **Arithmetic evaluation of a Gram entry.**  For distinct admissible base
points the Gram entry is the second inverse moment corrected by two relative
resolvent traces — each of which the explicit formula evaluates by primes and
the archimedean factor. -/
theorem xiWeilGramEntry_eq {z z' : ℂ} (hz : XiC z ≠ 0) (hz' : XiC z' ≠ 0)
    (hz0 : z ≠ 0) (hz'0 : z' ≠ 0) (hzz' : z ≠ z') :
    xiWeilGramEntry z z' =
      xiSecondInverseMoment -
        (z' / (z * (z - z'))) * xiRelativeResolventTrace z +
        (z / (z' * (z - z'))) * xiRelativeResolventTrace z' := by
  have hsq := summable_xiSpectralPoint_inv_sq
  have hK := summable_xiRelativeResolventTerm hz
  have hK' := summable_xiRelativeResolventTerm hz'
  have hne : ∀ q : XiZeroCopy, xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero
  have hnez : ∀ q : XiZeroCopy, xiSpectralPoint q ≠ z := by
    intro q h
    exact hz ((XiC_eq_zero_iff_exists_xiZeroCopy z).mpr ⟨q, h⟩)
  have hnez' : ∀ q : XiZeroCopy, xiSpectralPoint q ≠ z' := by
    intro q h
    exact hz' ((XiC_eq_zero_iff_exists_xiZeroCopy z').mpr ⟨q, h⟩)
  have hpoint : ∀ q : XiZeroCopy,
      xiCauchyRegularizedKernel z (xiSpectralPoint q) *
        xiCauchyRegularizedKernel z' (xiSpectralPoint q) =
      (xiSpectralPoint q)⁻¹ ^ 2 -
        (z' / (z * (z - z'))) * xiRelativeResolventTerm z q +
        (z / (z' * (z - z'))) * xiRelativeResolventTerm z' q := by
    intro q
    have h := xiCauchyRegularizedKernel_mul (z := z) (z' := z')
      (w := xiSpectralPoint q) hz0 hz'0 hzz' (hne q) (hnez q) (hnez' q)
    rw [h, ← sq, xiCauchyRegularizedKernel_apply_spectralPoint,
      xiCauchyRegularizedKernel_apply_spectralPoint]
  rw [xiWeilGramEntry, tsum_congr hpoint,
    Summable.tsum_add (hsq.sub (hK.mul_left _)) (hK'.mul_left _),
    Summable.tsum_sub hsq (hK.mul_left _), tsum_mul_left, tsum_mul_left]
  rfl

/-- The Gram entry evaluated through the logarithmic derivative of the centered
completed zeta: the form is a functional of `logDeriv XiC` alone. -/
theorem xiWeilGramEntry_eq_logDeriv {z z' : ℂ} (hz : XiC z ≠ 0)
    (hz' : XiC z' ≠ 0) (hz0 : z ≠ 0) (hz'0 : z' ≠ 0) (hzz' : z ≠ z') :
    xiWeilGramEntry z z' =
      xiSecondInverseMoment -
        (z' / (z * (z - z'))) * logDeriv XiC z +
        (z / (z' * (z - z'))) * logDeriv XiC z' := by
  rw [xiWeilGramEntry_eq hz hz' hz0 hz'0 hzz',
    logDeriv_XiC_eq_relativeResolventTrace hz,
    logDeriv_XiC_eq_relativeResolventTrace hz']

/-! ## §3 The Weil form of a superposition -/

/-- Sharp reflection sends a regularized Cauchy kernel to the kernel at the
conjugate base point. -/
theorem xiWeilSharp_cauchyKernel (z w : ℂ) :
    xiWeilSharp (xiCauchyRegularizedKernel z) w =
      xiCauchyRegularizedKernel ((starRingEnd ℂ) z) w := by
  unfold xiWeilSharp xiCauchyRegularizedKernel
  rw [map_sub, map_inv₀, map_inv₀, map_sub]
  simp

/-- **The Weil polarization of two kernels is the Gram entry at the conjugated
second base point.** -/
theorem xiWeilPolarization_cauchyKernel (z z' : ℂ) :
    xiWeilPolarization (xiCauchyRegularizedKernel z)
        (xiCauchyRegularizedKernel z') =
      xiWeilGramEntry z ((starRingEnd ℂ) z') := by
  unfold xiWeilPolarization xiWeilGramEntry
  exact tsum_congr fun q => by
    rw [xiWeilSharp_cauchyKernel]

/-- **Arithmetic evaluation of the Weil polarization on the resolvent algebra.**
The Weil pairing of two Cauchy kernels is an explicit combination of the second
inverse moment and two values of `logDeriv XiC`; no zero location enters. -/
theorem xiWeilPolarization_cauchyKernel_eq {z z' : ℂ} (hz : XiC z ≠ 0)
    (hz' : XiC ((starRingEnd ℂ) z') ≠ 0) (hz0 : z ≠ 0)
    (hz'0 : (starRingEnd ℂ) z' ≠ 0) (hzz' : z ≠ (starRingEnd ℂ) z') :
    xiWeilPolarization (xiCauchyRegularizedKernel z)
        (xiCauchyRegularizedKernel z') =
      xiSecondInverseMoment -
        ((starRingEnd ℂ) z' / (z * (z - (starRingEnd ℂ) z'))) * logDeriv XiC z +
        (z / ((starRingEnd ℂ) z' * (z - (starRingEnd ℂ) z'))) *
          logDeriv XiC ((starRingEnd ℂ) z') := by
  rw [xiWeilPolarization_cauchyKernel,
    xiWeilGramEntry_eq_logDeriv hz hz' hz0 hz'0 hzz']

/-- **The diagonal Weil value at a single base point.**  With `z` off the real
axis the diagonal entry is governed by the two resolvent traces at `z` and its
conjugate: as `z` approaches an off-critical zero these develop opposite poles,
which is the mechanism by which a displaced zero makes the form indefinite. -/
theorem xiWeilPolarization_cauchyKernel_diagonal {z : ℂ} (hz : XiC z ≠ 0)
    (hzc : XiC ((starRingEnd ℂ) z) ≠ 0) (hz0 : z ≠ 0)
    (hzim : z.im ≠ 0) :
    xiWeilPolarization (xiCauchyRegularizedKernel z)
        (xiCauchyRegularizedKernel z) =
      xiSecondInverseMoment -
        ((starRingEnd ℂ) z / (z * (z - (starRingEnd ℂ) z))) * logDeriv XiC z +
        (z / ((starRingEnd ℂ) z * (z - (starRingEnd ℂ) z))) *
          logDeriv XiC ((starRingEnd ℂ) z) := by
  have hz0' : (starRingEnd ℂ) z ≠ 0 := by
    simpa using hz0
  have hne : z ≠ (starRingEnd ℂ) z := by
    intro h
    have := congrArg Complex.im h
    rw [Complex.conj_im] at this
    exact hzim (by linarith)
  exact xiWeilPolarization_cauchyKernel_eq hz hzc hz0 hz0' hne

end

end RHTower
