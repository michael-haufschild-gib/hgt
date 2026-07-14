import GaloisForLFunctions.RHTower.XiHurwitzOrientationExteriorCauchyClosure

/-!
# Positive-frequency Schwarz-paired source closure

Ordinary Schwarz conjugation sends a centered Xi spectral point `a` to `-conj a` and sends the
Cauchy vector at `z` to minus the conjugate-reflected Cauchy vector at `-conj z`.  Since the
Hurwitz orientation coordinate is invariant under ordinary conjugation, its complete exterior
source approximation can be regrouped into positive-frequency pairs

`C_z - C_{-conj z}`,  with `R < re z`.

The same reflection is exact on the analytically continued prime--Gamma source, not merely on its
imaginary part.  Consequently the four-block kernel of a paired packet is a real kernel involving
only positive-frequency source values.  This module isolates that one-sided source surface and
wires its finite matrix passivity to RH.
-/

open Complex Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## Exact Schwarz reflection on the continued source domain -/

/-- The frequency-reflecting involution on centered source points. -/
def xiCenteredNegConj (z : ℂ) : ℂ :=
  -(starRingEnd ℂ) z

@[simp] theorem xiCenteredNegConj_re (z : ℂ) :
    (xiCenteredNegConj z).re = -z.re := by
  simp [xiCenteredNegConj]

@[simp] theorem xiCenteredNegConj_im (z : ℂ) :
    (xiCenteredNegConj z).im = z.im := by
  simp [xiCenteredNegConj]

@[simp] theorem xiCenteredNegConj_involutive (z : ℂ) :
    xiCenteredNegConj (xiCenteredNegConj z) = z := by
  simp [xiCenteredNegConj]

/-- The full continued Cauchy source domain is invariant under `z ↦ -conj z`. -/
theorem ccmContinuedCauchyDomain_negConj {z : ℂ}
    (hz : CCMContinuedCauchyDomain z) :
    CCMContinuedCauchyDomain (xiCenteredNegConj z) := by
  have hzlo : -(1 / 2 : ℝ) < z.im := by
    have h := hz.2.2.2.1
    simp [mul_re] at h
    linarith
  have hzhi : z.im < 1 / 2 := by
    have h := hz.1
    simp [mul_re] at h
    linarith
  have hzXi : XiC z ≠ 0 :=
    XiC_ne_zero_of_continuedPrimeArch_domain hz.1 hz.2.1 hz.2.2.1
  have hwXi : XiC (xiCenteredNegConj z) ≠ 0 := by
    rw [xiCenteredNegConj, XiC_even, XiC_conj]
    exact (map_ne_zero (starRingEnd ℂ)).2 hzXi
  apply ccmContinuedCauchyDomain_of_regular_mem_centeredStrip
  · simpa using hzlo
  · simpa using hzhi
  · exact hwXi

/-- The full source domain is invariant under ordinary conjugation. -/
theorem ccmContinuedCauchyDomain_conj {z : ℂ}
    (hz : CCMContinuedCauchyDomain z) :
    CCMContinuedCauchyDomain ((starRingEnd ℂ) z) := by
  refine ⟨hz.2.2.2.1, hz.2.2.2.2.1, hz.2.2.2.2.2, ?_, ?_, ?_⟩
  · simpa using hz.1
  · simpa using hz.2.1
  · simpa using hz.2.2.1

/-- The full source domain is invariant under the even reflection. -/
theorem ccmContinuedCauchyDomain_neg {z : ℂ}
    (hz : CCMContinuedCauchyDomain z) :
    CCMContinuedCauchyDomain (-z) := by
  have h := ccmContinuedCauchyDomain_negConj
    (ccmContinuedCauchyDomain_conj hz)
  simpa [xiCenteredNegConj] using h

/-- Exact complex source reflection.  The earlier high-frequency theorem used only its imaginary
part; the full identity is what makes the paired matrix one-sided. -/
theorem continuedPrimeArchSourceRelativeTrace_negConj
    {z : ℂ} (hz : CCMContinuedCauchyDomain z) :
    continuedPrimeArchSourceRelativeTrace (xiCenteredNegConj z) =
      -(starRingEnd ℂ) (continuedPrimeArchSourceRelativeTrace z) := by
  let w : ℂ := xiCenteredNegConj z
  have hw : CCMContinuedCauchyDomain w :=
    ccmContinuedCauchyDomain_negConj hz
  have hzXi : XiC z ≠ 0 :=
    XiC_ne_zero_of_continuedPrimeArch_domain hz.1 hz.2.1 hz.2.2.1
  have hwXi : XiC w ≠ 0 :=
    XiC_ne_zero_of_continuedPrimeArch_domain hw.1 hw.2.1 hw.2.2.1
  have hsourceZ :
      continuedPrimeArchSourceRelativeTrace z = logDeriv XiC z := by
    rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      hz.1 hz.2.1 hz.2.2.1,
      ← logDeriv_XiC_eq_relativeResolventTrace hzXi]
  have hsourceW :
      continuedPrimeArchSourceRelativeTrace w = logDeriv XiC w := by
    rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      hw.1 hw.2.1 hw.2.2.1,
      ← logDeriv_XiC_eq_relativeResolventTrace hwXi]
  have hcXi : XiC ((starRingEnd ℂ) z) ≠ 0 := by
    rw [XiC_conj]
    exact (map_ne_zero (starRingEnd ℂ)).2 hzXi
  have hlogConj :
      logDeriv XiC ((starRingEnd ℂ) z) =
        (starRingEnd ℂ) (logDeriv XiC z) := by
    rw [logDeriv_XiC_eq_relativeResolventTrace hcXi,
      logDeriv_XiC_eq_relativeResolventTrace hzXi,
      xiRelativeResolventTrace_conj]
  rw [show xiCenteredNegConj z = w by rfl, hsourceW, hsourceZ]
  rw [show w = -((starRingEnd ℂ) z) by rfl,
    logDeriv_XiC_neg, hlogConj]

/-- Schwarz reflection of the continued source itself. -/
theorem continuedPrimeArchSourceRelativeTrace_conj
    {z : ℂ} (hz : CCMContinuedCauchyDomain z) :
    continuedPrimeArchSourceRelativeTrace ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (continuedPrimeArchSourceRelativeTrace z) := by
  have hcdom := ccmContinuedCauchyDomain_conj hz
  have hzXi : XiC z ≠ 0 :=
    XiC_ne_zero_of_continuedPrimeArch_domain hz.1 hz.2.1 hz.2.2.1
  have hcXi : XiC ((starRingEnd ℂ) z) ≠ 0 :=
    XiC_ne_zero_of_continuedPrimeArch_domain
      hcdom.1 hcdom.2.1 hcdom.2.2.1
  have hsourceZ :
      continuedPrimeArchSourceRelativeTrace z = logDeriv XiC z := by
    rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      hz.1 hz.2.1 hz.2.2.1,
      ← logDeriv_XiC_eq_relativeResolventTrace hzXi]
  have hsourceC :
      continuedPrimeArchSourceRelativeTrace ((starRingEnd ℂ) z) =
        logDeriv XiC ((starRingEnd ℂ) z) := by
    rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      hcdom.1 hcdom.2.1 hcdom.2.2.1,
      ← logDeriv_XiC_eq_relativeResolventTrace hcXi]
  rw [hsourceC, hsourceZ,
    logDeriv_XiC_eq_relativeResolventTrace hcXi,
    logDeriv_XiC_eq_relativeResolventTrace hzXi,
    xiRelativeResolventTrace_conj]

/-- Oddness of the continued source on its two-sided domain. -/
theorem continuedPrimeArchSourceRelativeTrace_neg
    {z : ℂ} (hz : CCMContinuedCauchyDomain z) :
    continuedPrimeArchSourceRelativeTrace (-z) =
      -continuedPrimeArchSourceRelativeTrace z := by
  have hn := ccmContinuedCauchyDomain_neg hz
  have hzXi : XiC z ≠ 0 :=
    XiC_ne_zero_of_continuedPrimeArch_domain hz.1 hz.2.1 hz.2.2.1
  have hnXi : XiC (-z) ≠ 0 :=
    XiC_ne_zero_of_continuedPrimeArch_domain hn.1 hn.2.1 hn.2.2.1
  rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      hn.1 hn.2.1 hn.2.2.1,
    ← logDeriv_XiC_eq_relativeResolventTrace hnXi,
    logDeriv_XiC_neg,
    continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      hz.1 hz.2.1 hz.2.2.1,
    ← logDeriv_XiC_eq_relativeResolventTrace hzXi]

/-! ## Schwarz anti-isometry on the Xi divisor carrier -/

/-- Ordinary Schwarz conjugation on the multiplicity-exact Xi `ell²` carrier. -/
def xiWeilSchwarzLp (v : lp (fun _ : XiZeroCopy => ℂ) 2) :
    lp (fun _ : XiZeroCopy => ℂ) 2 := by
  refine ⟨fun q ↦ (starRingEnd ℂ) (v (xiZeroCopyConjEquiv q)), ?_⟩
  apply HilbertSchmidt.memℓp_of_sq
  have hbase : Summable (fun q : XiZeroCopy ↦
      ‖(starRingEnd ℂ) (v q)‖ ^ 2) :=
    (HilbertSchmidt.summable_coe_sq v).congr fun q ↦ by
      rw [Complex.norm_conj]
  simpa only [Function.comp_apply] using
    (xiZeroCopyConjEquiv.summable_iff.mpr hbase)

@[simp] theorem xiWeilSchwarzLp_apply
    (v : lp (fun _ : XiZeroCopy => ℂ) 2) (q : XiZeroCopy) :
    xiWeilSchwarzLp v q =
      (starRingEnd ℂ) (v (xiZeroCopyConjEquiv q)) := rfl

/-- Schwarz conjugation preserves the `ell²` norm. -/
theorem norm_xiWeilSchwarzLp (v : lp (fun _ : XiZeroCopy => ℂ) 2) :
    ‖xiWeilSchwarzLp v‖ = ‖v‖ := by
  have hsq : ‖xiWeilSchwarzLp v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [HilbertSchmidt.lp_norm_sq_eq, HilbertSchmidt.lp_norm_sq_eq]
    simpa only [xiWeilSchwarzLp_apply, Complex.norm_conj] using
      xiZeroCopyConjEquiv.tsum_eq (fun q ↦ ‖v q‖ ^ 2)
  nlinarith [norm_nonneg (xiWeilSchwarzLp v), norm_nonneg v]

theorem xiWeilSchwarzLp_add
    (v w : lp (fun _ : XiZeroCopy => ℂ) 2) :
    xiWeilSchwarzLp (v + w) = xiWeilSchwarzLp v + xiWeilSchwarzLp w := by
  apply Subtype.ext
  funext q
  change (starRingEnd ℂ) (v (xiZeroCopyConjEquiv q) +
      w (xiZeroCopyConjEquiv q)) =
    (starRingEnd ℂ) (v (xiZeroCopyConjEquiv q)) +
      (starRingEnd ℂ) (w (xiZeroCopyConjEquiv q))
  exact map_add (starRingEnd ℂ) _ _

theorem xiWeilSchwarzLp_smul
    (c : ℂ) (v : lp (fun _ : XiZeroCopy => ℂ) 2) :
    xiWeilSchwarzLp (c • v) =
      (starRingEnd ℂ) c • xiWeilSchwarzLp v := by
  apply Subtype.ext
  funext q
  change (starRingEnd ℂ) (c * v (xiZeroCopyConjEquiv q)) =
    (starRingEnd ℂ) c *
      (starRingEnd ℂ) (v (xiZeroCopyConjEquiv q))
  exact map_mul (starRingEnd ℂ) _ _

theorem xiWeilSchwarzLp_sub
    (v w : lp (fun _ : XiZeroCopy => ℂ) 2) :
    xiWeilSchwarzLp (v - w) = xiWeilSchwarzLp v - xiWeilSchwarzLp w := by
  apply Subtype.ext
  funext q
  change (starRingEnd ℂ) (v (xiZeroCopyConjEquiv q) -
      w (xiZeroCopyConjEquiv q)) =
    (starRingEnd ℂ) (v (xiZeroCopyConjEquiv q)) -
      (starRingEnd ℂ) (w (xiZeroCopyConjEquiv q))
  exact map_sub (starRingEnd ℂ) _ _

/-- Norm convergence is preserved by Schwarz conjugation. -/
theorem tendsto_xiWeilSchwarzLp
    {v : ℕ → lp (fun _ : XiZeroCopy => ℂ) 2}
    {x : lp (fun _ : XiZeroCopy => ℂ) 2}
    (h : Tendsto v atTop (nhds x)) :
    Tendsto (fun n ↦ xiWeilSchwarzLp (v n)) atTop
      (nhds (xiWeilSchwarzLp x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  rw [tendsto_iff_norm_sub_tendsto_zero] at h
  convert h using 1
  funext n
  rw [← xiWeilSchwarzLp_sub, norm_xiWeilSchwarzLp]

end

end RHTower

namespace RHTower

noncomputable section

/-! ## Positive-frequency paired Cauchy generators -/

/-- Reflection of a genuine continued-source Cauchy point. -/
def xiContinuedCauchyNegConj (z : XiContinuedCauchyPoint) :
    XiContinuedCauchyPoint := by
  let w : ℂ := xiCenteredNegConj (z : ℂ)
  have hwdom : CCMContinuedCauchyDomain w :=
    ccmContinuedCauchyDomain_negConj z.property
  exact ⟨⟨w, XiC_ne_zero_of_continuedPrimeArch_domain
    hwdom.1 hwdom.2.1 hwdom.2.2.1⟩, hwdom⟩

@[simp] theorem xiContinuedCauchyNegConj_coe
    (z : XiContinuedCauchyPoint) :
    (xiContinuedCauchyNegConj z : ℂ) = xiCenteredNegConj (z : ℂ) := rfl

/-- A continued-source pole in the positive exterior half-line. -/
abbrev XiPositiveExteriorContinuedCauchyPoint (R : ℝ) :=
  {z : XiContinuedCauchyPoint // R < (z : ℂ).re}

/-- The Schwarz partner of a positive exterior pole lies in the negative exterior half-line. -/
theorem xiContinuedCauchyNegConj_re_lt_neg
    (R : ℝ) (z : XiPositiveExteriorContinuedCauchyPoint R) :
    (xiContinuedCauchyNegConj z.1 : ℂ).re < -R := by
  simpa using (neg_lt_neg z.property)

/-- A positive pole and its negative-frequency Schwarz partner. -/
def xiWeilPositivePairedContinuedCauchyLp (R : ℝ)
    (z : XiPositiveExteriorContinuedCauchyPoint R) :
    lp (fun _ : XiZeroCopy => ℂ) 2 :=
  xiWeilContinuedCauchyLp z.1 -
    xiWeilContinuedCauchyLp (xiContinuedCauchyNegConj z.1)

/-- Complex algebraic span of positive-frequency Schwarz-paired generators. -/
def xiWeilPositivePairedContinuedCauchyAlgebraicSubspace (R : ℝ) :
    Submodule ℂ (lp (fun _ : XiZeroCopy => ℂ) 2) :=
  Submodule.span ℂ (Set.range (xiWeilPositivePairedContinuedCauchyLp R))

/-- Hilbert closure of the positive-frequency Schwarz-paired source core. -/
def xiWeilPositivePairedContinuedCauchyHilbertSubspace (R : ℝ) :
    Submodule ℂ (lp (fun _ : XiZeroCopy => ℂ) 2) :=
  (xiWeilPositivePairedContinuedCauchyAlgebraicSubspace R).topologicalClosure

/-- Schwarz conjugation sends a Cauchy vector to minus the vector at the reflected pole. -/
theorem xiWeilSchwarzLp_continuedCauchy
    (z : XiContinuedCauchyPoint) :
    xiWeilSchwarzLp (xiWeilContinuedCauchyLp z) =
      -xiWeilContinuedCauchyLp (xiContinuedCauchyNegConj z) := by
  apply Subtype.ext
  funext q
  rw [xiWeilSchwarzLp_apply]
  change (starRingEnd ℂ)
      ((xiSpectralPoint (xiZeroCopyConjEquiv q) - (z : ℂ))⁻¹) =
    -((xiSpectralPoint q - xiCenteredNegConj (z : ℂ))⁻¹)
  rw [xiSpectralPoint_copyConj]
  simp only [map_inv₀, map_sub, map_neg, xiCenteredNegConj]
  rw [show -(starRingEnd ℂ) ((starRingEnd ℂ) (xiSpectralPoint q)) -
      (starRingEnd ℂ) (z : ℂ) =
      -((starRingEnd ℂ) (z : ℂ) + xiSpectralPoint q) by simp; ring]
  rw [inv_neg]
  simp only [sub_neg_eq_add, add_comm]

/-- Schwarz conjugation sends a spectral-fiber indicator to the indicator of the reflected
spectral fiber. -/
theorem xiWeilSchwarzLp_fiberIndicator (alpha : ℂ) :
    xiWeilSchwarzLp (xiWeilFiberIndicatorLp alpha) =
      xiWeilFiberIndicatorLp (xiCenteredNegConj alpha) := by
  apply Subtype.ext
  funext q
  rw [xiWeilSchwarzLp_apply, xiWeilFiberIndicatorLp_apply,
    xiWeilFiberIndicatorLp_apply, xiSpectralPoint_copyConj]
  unfold xiCenteredNegConj
  by_cases h : -(starRingEnd ℂ) (xiSpectralPoint q) = alpha
  · have h' : xiSpectralPoint q = -(starRingEnd ℂ) alpha := by
      have := congrArg (starRingEnd ℂ) h
      simpa using congrArg Neg.neg this
    simp [h']
  · have h' : xiSpectralPoint q ≠ -(starRingEnd ℂ) alpha := by
      intro heq
      apply h
      rw [heq]
      simp
    simp [h, h']

/-- The centered spectral support coordinate transforms by the same reflection. -/
@[simp] theorem xiSpectralPointSupport_zeroConj (rho : XiDivisorSupport) :
    xiSpectralPointSupport (xiZeroConjEquiv rho) =
      xiCenteredNegConj (xiSpectralPointSupport rho) := by
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
      Complex.conj_ofReal]
  change (((starRingEnd ℂ) (rho : ℂ)) - 1 / 2) * (-I) =
    -((starRingEnd ℂ) (((rho : ℂ) - 1 / 2) * (-I)))
  simp only [map_mul, map_sub, map_neg, conj_I, hhalf]
  ring

end

end RHTower

namespace RHTower

noncomputable section

open HurwitzOrbit

/-- Exact signed trigonometric formula for one orientation fiber coefficient. -/
theorem xiHurwitzOrientationFiberCoefficient_eq_neg_sin_div
    (rho : XiDivisorSupport) :
    xiHurwitzOrientationFiberCoefficient rho =
      (((-Real.sin (2 * Real.pi * (rho : ℂ).re)) /
        ‖(rho : ℂ) - 1 / 2‖ : ℝ) : ℂ) := by
  have hre : (-(2 * (Real.pi : ℂ) * I * (rho : ℂ))).re =
      2 * Real.pi * (rho : ℂ).im := by simp
  have him : (-(2 * (Real.pi : ℂ) * I * (rho : ℂ))).im =
      -(2 * Real.pi * (rho : ℂ).re) := by simp
  rw [xiHurwitzOrientationFiberCoefficient,
    xiHurwitzOrientationCoordinate]
  simp only [xiFirstZeroCopy_fst, xiHurwitzMonodromyCharacter,
    monoScalar, Complex.exp_im, Complex.norm_exp, hre, him, Real.sin_neg]
  have hexp : Real.exp (2 * Real.pi * (rho : ℂ).im) ≠ 0 :=
    ne_of_gt (Real.exp_pos _)
  push_cast
  field_simp [hexp]

/-- Ordinary Schwarz conjugation preserves the signed orientation fiber coefficient. -/
theorem xiHurwitzOrientationFiberCoefficient_zeroConj
    (rho : XiDivisorSupport) :
    xiHurwitzOrientationFiberCoefficient (xiZeroConjEquiv rho) =
      xiHurwitzOrientationFiberCoefficient rho := by
  rw [xiHurwitzOrientationFiberCoefficient_eq_neg_sin_div,
    xiHurwitzOrientationFiberCoefficient_eq_neg_sin_div]
  change (((-Real.sin
      (2 * Real.pi * ((starRingEnd ℂ) (rho : ℂ)).re)) /
      ‖((starRingEnd ℂ) (rho : ℂ)) - 1 / 2‖ : ℝ) : ℂ) = _
  have hnorm :
      ‖((starRingEnd ℂ) (rho : ℂ)) - 1 / 2‖ =
        ‖(rho : ℂ) - 1 / 2‖ := by
    have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
        Complex.conj_ofReal]
    calc
      ‖((starRingEnd ℂ) (rho : ℂ)) - 1 / 2‖ =
          ‖(starRingEnd ℂ) ((rho : ℂ) - 1 / 2)‖ := by
            congr 1
            rw [map_sub, hhalf]
      _ = ‖(rho : ℂ) - 1 / 2‖ := Complex.norm_conj _
  simp only [Complex.conj_re, hnorm]

/-- One positive-frequency Schwarz pair of complete multiplicity fibers. -/
def xiHurwitzOrientationPositivePairedFiberVector
    (rho : XiDivisorSupport) : lp (fun _ : XiZeroCopy => ℂ) 2 :=
  if 0 < (xiSpectralPointSupport rho).re then
    xiHurwitzOrientationFiberVector rho +
      xiHurwitzOrientationFiberVector (xiZeroConjEquiv rho)
  else 0

end

end RHTower

namespace RHTower

noncomputable section

/-- A positive-frequency orientation fiber together with its Schwarz partner belongs to the
positive paired exterior source closure. -/
theorem xiHurwitzOrientationFiberPair_mem_positivePairedHilbertSubspace
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R)
    (rho : XiDivisorSupport)
    (hpos : 0 < (xiSpectralPointSupport rho).re) :
    xiHurwitzOrientationFiberVector rho +
        xiHurwitzOrientationFiberVector (xiZeroConjEquiv rho) ∈
      xiWeilPositivePairedContinuedCauchyHilbertSubspace R := by
  by_cases hoff : (rho : ℂ).re ≠ 1 / 2
  · let q : XiZeroCopy := xiFirstZeroCopy rho
    let alpha : ℂ := xiSpectralPointSupport rho
    obtain ⟨c, hc, _hcap, z, hzform, hzlim⟩ :=
      exists_normalizedCauchyLp_tendsto_fiberIndicator_with_cap
        alpha zero_lt_one
    have halphaRe : alpha.re = (rho : ℂ).im := by
      simp [alpha, xiSpectralPointSupport, mul_re]
    have hheightAbs : R + 1 / 2 < |alpha.re| := by
      rw [halphaRe]
      exact xiOffLineQuartetAccretiveBand_add_half_lt_abs_im_of_offLine
        R hband q (by simpa [q] using hoff)
    have hheight : R + 1 / 2 < alpha.re := by
      rw [abs_of_pos hpos] at hheightAbs
      exact hheightAbs
    have hzPositive : ∀ n, R < (z n : ℂ).re := by
      intro n
      have hrpos : 0 < c / (n + 1 : ℕ) := div_pos hc (by positivity)
      have hzre : (z n : ℂ).re = alpha.re + c / (n + 1 : ℕ) := by
        rw [hzform n]
        simp only [add_re, ofReal_re]
      rw [hzre]
      linarith
    let zc : ℕ → XiContinuedCauchyPoint := fun n ↦
      ⟨z n, ccmContinuedCauchyDomain_of_regular_same_spectral_im q
        (z n).property (by
          rw [hzform n]
          simp [q, alpha, xiSpectralPointSupport, xiSpectralPoint,
            Complex.div_im])⟩
    let zp : ℕ → XiPositiveExteriorContinuedCauchyPoint R := fun n ↦
      ⟨zc n, hzPositive n⟩
    let V : ℕ → lp (fun _ : XiZeroCopy => ℂ) 2 := fun n ↦
      (alpha - (z n : ℂ)) • xiWeilContinuedCauchyLp (zc n)
    have hV : Tendsto V atTop
        (nhds (xiWeilFiberIndicatorLp alpha)) := by
      simpa only [V, xiWeilContinuedCauchyLp, zc] using hzlim
    have hSV : Tendsto (fun n ↦ xiWeilSchwarzLp (V n)) atTop
        (nhds (xiWeilFiberIndicatorLp (xiCenteredNegConj alpha))) := by
      simpa only [xiWeilSchwarzLp_fiberIndicator] using
        tendsto_xiWeilSchwarzLp hV
    have hpairPoint : ∀ n,
        V n + xiWeilSchwarzLp (V n) =
          (alpha - (z n : ℂ)) •
            xiWeilPositivePairedContinuedCauchyLp R (zp n) := by
      intro n
      have hreal :
          (starRingEnd ℂ) (alpha - (z n : ℂ)) = alpha - (z n : ℂ) := by
        rw [hzform n]
        simp
      rw [xiWeilSchwarzLp_smul, hreal,
        xiWeilSchwarzLp_continuedCauchy]
      simp only [V, xiWeilPositivePairedContinuedCauchyLp, zp, zc]
      module
    have hpair : Tendsto
        (fun n ↦ (alpha - (z n : ℂ)) •
          xiWeilPositivePairedContinuedCauchyLp R (zp n))
        atTop
        (nhds (xiWeilFiberIndicatorLp alpha +
          xiWeilFiberIndicatorLp (xiCenteredNegConj alpha))) := by
      apply (hV.add hSV).congr'
      exact Eventually.of_forall hpairPoint
    have hscaled := hpair.const_smul (xiHurwitzOrientationFiberCoefficient rho)
    have htarget :
        xiHurwitzOrientationFiberCoefficient rho •
            (xiWeilFiberIndicatorLp alpha +
              xiWeilFiberIndicatorLp (xiCenteredNegConj alpha)) =
          xiHurwitzOrientationFiberVector rho +
            xiHurwitzOrientationFiberVector (xiZeroConjEquiv rho) := by
      rw [xiHurwitzOrientationFiberVector,
        xiHurwitzOrientationFiberVector,
        xiHurwitzOrientationFiberCoefficient_zeroConj,
        xiSpectralPointSupport_zeroConj]
      simp only [alpha]
      exact smul_add _ _ _
    rw [htarget] at hscaled
    apply (Submodule.isClosed_topologicalClosure
      (xiWeilPositivePairedContinuedCauchyAlgebraicSubspace R)).mem_of_tendsto
        hscaled
    exact Eventually.of_forall fun n ↦ by
      have hgen : xiWeilPositivePairedContinuedCauchyLp R (zp n) ∈
          xiWeilPositivePairedContinuedCauchyAlgebraicSubspace R :=
        Submodule.subset_span ⟨zp n, rfl⟩
      have hgenClosure : xiWeilPositivePairedContinuedCauchyLp R (zp n) ∈
          xiWeilPositivePairedContinuedCauchyHilbertSubspace R :=
        Submodule.le_topologicalClosure _ hgen
      exact (xiWeilPositivePairedContinuedCauchyHilbertSubspace R).smul_mem _
        ((xiWeilPositivePairedContinuedCauchyHilbertSubspace R).smul_mem _
          hgenClosure)
  · have hrho : (rho : ℂ).re = 1 / 2 := not_ne_iff.mp hoff
    have hconj : ((xiZeroConjEquiv rho : XiDivisorSupport) : ℂ).re = 1 / 2 := by
      simpa using hrho
    rw [xiHurwitzOrientationFiberVector,
      xiHurwitzOrientationFiberVector,
      xiHurwitzOrientationFiberCoefficient_eq_zero_of_re_eq_half rho hrho,
      xiHurwitzOrientationFiberCoefficient_eq_zero_of_re_eq_half
        (xiZeroConjEquiv rho) hconj,
      zero_smul, zero_add]
    simpa only [zero_smul] using
      (xiWeilPositivePairedContinuedCauchyHilbertSubspace R).zero_mem

end

end RHTower

namespace RHTower

noncomputable section

/-- Positive and negative frequency exhaust the Xi divisor support: no Xi zero is real. -/
theorem xiSpectralPointSupport_re_ne_zero (rho : XiDivisorSupport) :
    (xiSpectralPointSupport rho).re ≠ 0 := by
  have him := xi_divisor_support_im_ne_zero rho
  simpa [xiSpectralPointSupport, mul_re] using him

/-- Regrouping the absolutely summable orientation expansion over positive-frequency Schwarz
pairs leaves the complete orientation vector unchanged. -/
theorem hasSum_xiHurwitzOrientationPositivePairedFiberVector :
    HasSum xiHurwitzOrientationPositivePairedFiberVector
      xiHurwitzOrientationVector := by
  let f : XiDivisorSupport → lp (fun _ : XiZeroCopy => ℂ) 2 :=
    xiHurwitzOrientationFiberVector
  let fp : XiDivisorSupport → lp (fun _ : XiZeroCopy => ℂ) 2 := fun rho ↦
    if 0 < (xiSpectralPointSupport rho).re then f rho else 0
  let fn : XiDivisorSupport → lp (fun _ : XiZeroCopy => ℂ) 2 := fun rho ↦
    if (xiSpectralPointSupport rho).re < 0 then f rho else 0
  let fcp : XiDivisorSupport → lp (fun _ : XiZeroCopy => ℂ) 2 := fun rho ↦
    if 0 < (xiSpectralPointSupport rho).re then
      f (xiZeroConjEquiv rho) else 0
  have hf : Summable f := hasSum_xiHurwitzOrientationFiberVector.summable
  have hfp : Summable fp := by
    simpa [fp, Set.indicator] using
      hf.indicator {rho | 0 < (xiSpectralPointSupport rho).re}
  have hfn : Summable fn := by
    simpa [fn, Set.indicator] using
      hf.indicator {rho | (xiSpectralPointSupport rho).re < 0}
  have hfc : Summable (fun rho ↦ f (xiZeroConjEquiv rho)) := by
    simpa only [Function.comp_apply] using
      (xiZeroConjEquiv.summable_iff.mpr hf)
  have hfcp : Summable fcp := by
    simpa [fcp, Set.indicator] using
      hfc.indicator {rho | 0 < (xiSpectralPointSupport rho).re}
  have hsplitPoint : ∀ rho, fp rho + fn rho = f rho := by
    intro rho
    have hne := xiSpectralPointSupport_re_ne_zero rho
    by_cases hp : 0 < (xiSpectralPointSupport rho).re
    · simp [fp, fn, hp, not_lt.mpr hp.le]
    · have hn : (xiSpectralPointSupport rho).re < 0 :=
        lt_of_le_of_ne (le_of_not_gt hp) hne
      simp [fp, fn, hp, hn]
  have hsplit : (∑' rho, fp rho) + (∑' rho, fn rho) = ∑' rho, f rho := by
    rw [← hfp.tsum_add hfn]
    exact tsum_congr hsplitPoint
  have hconjPoint : ∀ rho,
      fn (xiZeroConjEquiv rho) = fcp rho := by
    intro rho
    have hre :
        (xiSpectralPointSupport (xiZeroConjEquiv rho)).re =
          -(xiSpectralPointSupport rho).re := by
      rw [xiSpectralPointSupport_zeroConj]
      simp
    by_cases hp : 0 < (xiSpectralPointSupport rho).re
    · have hn :
          (xiSpectralPointSupport (xiZeroConjEquiv rho)).re < 0 := by
        rw [hre]
        linarith
      simp [fn, fcp, hp]
    · have hnn : ¬(xiSpectralPointSupport
          (xiZeroConjEquiv rho)).re < 0 := by
        rw [hre]
        linarith
      simp [fn, fcp, hp]
  have hconj : (∑' rho, fcp rho) = ∑' rho, fn rho := by
    calc
      (∑' rho, fcp rho) =
          ∑' rho, fn (xiZeroConjEquiv rho) :=
        tsum_congr fun rho ↦ (hconjPoint rho).symm
      _ = ∑' rho, fn rho := xiZeroConjEquiv.tsum_eq fn
  have hpairedPoint : ∀ rho,
      xiHurwitzOrientationPositivePairedFiberVector rho =
        fp rho + fcp rho := by
    intro rho
    by_cases hp : 0 < (xiSpectralPointSupport rho).re <;>
      simp [xiHurwitzOrientationPositivePairedFiberVector, fp, fcp, f, hp]
  have hpairedSummable :
      Summable xiHurwitzOrientationPositivePairedFiberVector :=
    (hfp.add hfcp).congr fun rho ↦ (hpairedPoint rho).symm
  have htsum :
      (∑' rho, xiHurwitzOrientationPositivePairedFiberVector rho) =
        xiHurwitzOrientationVector := by
    calc
    (∑' rho, xiHurwitzOrientationPositivePairedFiberVector rho) =
        (∑' rho, fp rho) + ∑' rho, fcp rho := by
      rw [← hfp.tsum_add hfcp]
      exact tsum_congr hpairedPoint
    _ = (∑' rho, fp rho) + ∑' rho, fn rho := by rw [hconj]
    _ = ∑' rho, f rho := hsplit
    _ = xiHurwitzOrientationVector :=
      hasSum_xiHurwitzOrientationFiberVector.tsum_eq
  rw [← htsum]
  exact hpairedSummable.hasSum

/-- Every positive-paired orientation summand belongs to the one-sided paired source closure. -/
theorem xiHurwitzOrientationPositivePairedFiberVector_mem
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R)
    (rho : XiDivisorSupport) :
    xiHurwitzOrientationPositivePairedFiberVector rho ∈
      xiWeilPositivePairedContinuedCauchyHilbertSubspace R := by
  by_cases hp : 0 < (xiSpectralPointSupport rho).re
  · rw [xiHurwitzOrientationPositivePairedFiberVector, if_pos hp]
    exact xiHurwitzOrientationFiberPair_mem_positivePairedHilbertSubspace
      R hband rho hp
  · rw [xiHurwitzOrientationPositivePairedFiberVector, if_neg hp]
    exact (xiWeilPositivePairedContinuedCauchyHilbertSubspace R).zero_mem

/-- **One-sided paired closure law.**  The full Hurwitz orientation vector belongs to the Hilbert
closure generated only by positive-frequency exterior pairs `C_z - C_{-conj z}`. -/
theorem xiHurwitzOrientationVector_mem_positivePairedContinuedCauchyHilbertSubspace
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R) :
    xiHurwitzOrientationVector ∈
      xiWeilPositivePairedContinuedCauchyHilbertSubspace R := by
  have hmem :
      (∑' rho : XiDivisorSupport,
        xiHurwitzOrientationPositivePairedFiberVector rho) ∈
          xiWeilPositivePairedContinuedCauchyHilbertSubspace R :=
    tsum_mem
      (Submodule.isClosed_topologicalClosure
        (xiWeilPositivePairedContinuedCauchyAlgebraicSubspace R))
      (xiHurwitzOrientationPositivePairedFiberVector_mem R hband)
  rw [hasSum_xiHurwitzOrientationPositivePairedFiberVector.tsum_eq] at hmem
  exact hmem

/-- Positivity on the one-sided paired algebraic core extends to its Hilbert closure. -/
theorem xiWeilHilbertQuadratic_nonneg_on_positivePairedHilbertSubspace
    (R : ℝ)
    (hpos : ∀ v ∈ xiWeilPositivePairedContinuedCauchyAlgebraicSubspace R,
      0 ≤ xiWeilHilbertQuadratic v) :
    ∀ v ∈ xiWeilPositivePairedContinuedCauchyHilbertSubspace R,
      0 ≤ xiWeilHilbertQuadratic v := by
  intro v hv
  have hclosed : IsClosed {w | 0 ≤ xiWeilHilbertQuadratic w} :=
    isClosed_Ici.preimage continuous_xiWeilHilbertQuadratic
  exact (closure_minimal hpos hclosed) hv

/-- Positivity on only the positive-frequency paired exterior core implies RH. -/
theorem riemannHypothesis_of_positivePairedContinuedCauchyCore_nonnegative
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R)
    (hpos : ∀ v ∈ xiWeilPositivePairedContinuedCauchyAlgebraicSubspace R,
      0 ≤ xiWeilHilbertQuadratic v) :
    RiemannHypothesis := by
  apply riemannHypothesis_iff_xiHurwitzOrientationVector_weil_nonneg.mpr
  exact xiWeilHilbertQuadratic_nonneg_on_positivePairedHilbertSubspace R hpos
    xiHurwitzOrientationVector
      (xiHurwitzOrientationVector_mem_positivePairedContinuedCauchyHilbertSubspace
        R hband)

end

end RHTower

namespace RHTower

noncomputable section

/-! ## One-sided value kernel -/

/-- Four-block source kernel of two Schwarz-paired positive-frequency generators. -/
def ccmPositivePairedCauchyKernel (z w : ℂ) : ℂ :=
  ccmContinuedCauchyKernel z w -
    ccmContinuedCauchyKernel z (xiCenteredNegConj w) -
    ccmContinuedCauchyKernel (xiCenteredNegConj z) w +
    ccmContinuedCauchyKernel (xiCenteredNegConj z) (xiCenteredNegConj w)

/-- The reduced real kernel, written only in terms of positive-frequency source values. -/
def ccmPositivePairedReducedKernel (z w : ℂ) : ℝ :=
  2 * (((
      ((starRingEnd ℂ) (continuedPrimeArchSourceRelativeTrace w) -
        continuedPrimeArchSourceRelativeTrace z) /
          (z - (starRingEnd ℂ) w)) +
      ((continuedPrimeArchSourceRelativeTrace w +
        continuedPrimeArchSourceRelativeTrace z) / (z + w))).re)

/-- A mixed positive/negative block has a positive-frequency value formula. -/
theorem ccmContinuedCauchyKernel_right_negConj
    {z w : ℂ} (hw : CCMContinuedCauchyDomain w) :
    ccmContinuedCauchyKernel z (xiCenteredNegConj w) =
      -(continuedPrimeArchSourceRelativeTrace w +
          continuedPrimeArchSourceRelativeTrace z) / (z + w) := by
  rw [ccmContinuedCauchyKernel]
  have harg : (starRingEnd ℂ) (xiCenteredNegConj w) = -w := by
    simp [xiCenteredNegConj]
  rw [harg, continuedPrimeArchSourceRelativeTrace_neg hw]
  ring

/-- The opposite mixed block is the conjugate of the first. -/
theorem ccmContinuedCauchyKernel_left_negConj
    {z w : ℂ} (hz : CCMContinuedCauchyDomain z)
    (hw : CCMContinuedCauchyDomain w) :
    ccmContinuedCauchyKernel (xiCenteredNegConj z) w =
      (starRingEnd ℂ)
        (ccmContinuedCauchyKernel z (xiCenteredNegConj w)) := by
  rw [ccmContinuedCauchyKernel,
    continuedPrimeArchSourceRelativeTrace_conj hw,
    continuedPrimeArchSourceRelativeTrace_negConj hz,
    ccmContinuedCauchyKernel_right_negConj hw]
  simp only [map_div₀, map_neg, map_add]
  simp [xiCenteredNegConj]
  rw [show -(starRingEnd ℂ) z - (starRingEnd ℂ) w =
      -((starRingEnd ℂ) z + (starRingEnd ℂ) w) by ring, div_neg]
  ring

/-- The negative-negative block is the conjugate of the positive-positive block. -/
theorem ccmContinuedCauchyKernel_negConj_negConj
    {z w : ℂ} (hz : CCMContinuedCauchyDomain z)
    (hw : CCMContinuedCauchyDomain w) :
    ccmContinuedCauchyKernel (xiCenteredNegConj z)
        (xiCenteredNegConj w) =
      (starRingEnd ℂ) (ccmContinuedCauchyKernel z w) := by
  have h := ccmContinuedCauchyKernel_left_negConj hz
    (ccmContinuedCauchyDomain_negConj hw)
      (z := z) (w := xiCenteredNegConj w)
  simpa only [xiCenteredNegConj_involutive] using h

/-- The ordinary positive-positive block also uses only positive-frequency source values. -/
theorem ccmContinuedCauchyKernel_eq_positiveValues
    {z w : ℂ} (hw : CCMContinuedCauchyDomain w) :
    ccmContinuedCauchyKernel z w =
      ((starRingEnd ℂ) (continuedPrimeArchSourceRelativeTrace w) -
        continuedPrimeArchSourceRelativeTrace z) /
          (z - (starRingEnd ℂ) w) := by
  rw [ccmContinuedCauchyKernel,
    continuedPrimeArchSourceRelativeTrace_conj hw]

/-- **One-sided reflection reduction.**  The entire four-block paired kernel is the real lift of
one explicit kernel involving only the two positive-frequency source values. -/
theorem ccmPositivePairedCauchyKernel_eq_reduced
    {z w : ℂ} (hz : CCMContinuedCauchyDomain z)
    (hw : CCMContinuedCauchyDomain w) :
    ccmPositivePairedCauchyKernel z w =
      ((ccmPositivePairedReducedKernel z w : ℝ) : ℂ) := by
  rw [ccmPositivePairedCauchyKernel,
    ccmContinuedCauchyKernel_left_negConj hz hw,
    ccmContinuedCauchyKernel_negConj_negConj hz hw,
    ccmContinuedCauchyKernel_right_negConj hw,
    ccmContinuedCauchyKernel_eq_positiveValues hw]
  have hpair (A H : ℂ) :
      A - (-H) - (starRingEnd ℂ) (-H) + (starRingEnd ℂ) A =
        (((2 * (A + H).re : ℝ)) : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  simpa only [ccmPositivePairedReducedKernel, neg_div] using
    hpair
      (((starRingEnd ℂ) (continuedPrimeArchSourceRelativeTrace w) -
          continuedPrimeArchSourceRelativeTrace z) /
        (z - (starRingEnd ℂ) w))
      ((continuedPrimeArchSourceRelativeTrace w +
          continuedPrimeArchSourceRelativeTrace z) / (z + w))

end

end RHTower

namespace RHTower

noncomputable section

/-- Positivity on the algebraic span of positive-frequency Schwarz-paired exterior source
vectors. -/
def XiPositivePairedContinuedCauchyCorePassivity (R : ℝ) : Prop :=
  ∀ v ∈ xiWeilPositivePairedContinuedCauchyAlgebraicSubspace R,
    0 ≤ xiWeilHilbertQuadratic v

/-- The one-sided paired core criterion is exact at every quartet-admissible radius. -/
theorem positivePairedContinuedCauchyCorePassivity_iff_riemannHypothesis
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R) :
    XiPositivePairedContinuedCauchyCorePassivity R ↔ RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_positivePairedContinuedCauchyCore_nonnegative
      R hband
  · intro hRH v _hv
    exact xiWeilHilbertQuadratic_nonneg_of_riemannHypothesis hRH v

/-- Clean rational one-sided paired criterion beyond the discharged central band. -/
theorem positivePairedContinuedCauchyCorePassivity_twoHundredEighteen_twentyFifths_iff_rh :
    XiPositivePairedContinuedCauchyCorePassivity (218 / 25) ↔
      RiemannHypothesis :=
  positivePairedContinuedCauchyCorePassivity_iff_riemannHypothesis
    (218 / 25) xiOffLineQuartetAccretiveBand_twoHundredEighteen_twentyFifths

/-- The reduced paired kernel is real-valued when lifted to `ℂ`. -/
theorem ccmPositivePairedCauchyKernel_im_eq_zero
    {z w : ℂ} (hz : CCMContinuedCauchyDomain z)
    (hw : CCMContinuedCauchyDomain w) :
    (ccmPositivePairedCauchyKernel z w).im = 0 := by
  rw [ccmPositivePairedCauchyKernel_eq_reduced hz hw]
  simp

/-- For one genuinely separated positive pole, the Hilbert quadratic value of its paired Cauchy
vector is exactly the one-sided reduced prime--Gamma kernel on the diagonal. -/
theorem xiWeilHilbertQuadratic_positivePairedCauchy_eq_reducedKernel
    (R : ℝ) (hR : 0 ≤ R)
    (z : XiPositiveExteriorContinuedCauchyPoint R)
    (hzIm : (z : ℂ).im ≠ 0) :
    xiWeilHilbertQuadratic
        (xiWeilPositivePairedContinuedCauchyLp R z) =
      ccmPositivePairedReducedKernel (z : ℂ) (z : ℂ) := by
  let w : XiContinuedCauchyPoint := xiContinuedCauchyNegConj z.1
  have hzdom : CCMContinuedCauchyDomain (z : ℂ) := z.1.property
  have hwdom : CCMContinuedCauchyDomain (w : ℂ) := w.property
  have hzRe : 0 < (z : ℂ).re := lt_of_le_of_lt hR z.property
  have hwRe : (w : ℂ).re < 0 := by
    simp [w, xiCenteredNegConj]
    linarith
  have hzw : (z : ℂ) ≠ (w : ℂ) := by
    intro h
    have := congrArg Complex.re h
    linarith
  have hzz : (z : ℂ) ≠ (starRingEnd ℂ) (z : ℂ) := by
    intro h
    exact hzIm (Complex.conj_eq_iff_im.mp h.symm)
  have hww : (w : ℂ) ≠ (starRingEnd ℂ) (w : ℂ) := by
    intro h
    have hwIm : (w : ℂ).im = (z : ℂ).im := by
      simp [w, xiCenteredNegConj]
    apply hzIm
    rw [← hwIm]
    exact Complex.conj_eq_iff_im.mp h.symm
  have hzwc : (z : ℂ) ≠ (starRingEnd ℂ) (w : ℂ) := by
    intro h
    have hre := congrArg Complex.re h
    simp [w, xiCenteredNegConj] at hre
    linarith
  have hwzc : (w : ℂ) ≠ (starRingEnd ℂ) (z : ℂ) := by
    intro h
    have hre := congrArg Complex.re h
    simp [w, xiCenteredNegConj] at hre
    linarith
  have hpol := xiWeilPolarization_twoCauchy_eq_continuedSourceEnergy
    hzdom hwdom hzw hzz hzwc hwzc hww
    (a := (1 : ℂ)) (b := (-1 : ℂ))
  have heval := xiWeilEvaluationLp_twoCauchyPacket
    z.1 w (1 : ℂ) (-1 : ℂ)
  have hvec :
      xiWeilEvaluationLp
          (xiWeilTwoCauchyPacket z.1 w (1 : ℂ) (-1 : ℂ))
          (xiWeilTwoCauchyPacket_squareSummable z.1 w (1 : ℂ) (-1 : ℂ)) =
        xiWeilPositivePairedContinuedCauchyLp R z := by
    rw [heval]
    simp [xiWeilPositivePairedContinuedCauchyLp,
      xiWeilContinuedCauchyLp, w]
    exact (sub_eq_add_neg _ _).symm
  rw [← hvec, xiWeilHilbertQuadratic_evaluation_eq_polarization_re,
    hpol]
  have henergy :
      ccmTwoPoleSourceEnergy (z : ℂ) (w : ℂ) (1 : ℂ) (-1 : ℂ) =
        ccmPositivePairedCauchyKernel (z : ℂ) (z : ℂ) := by
    simp [ccmTwoPoleSourceEnergy, ccmPositivePairedCauchyKernel, w]
    ring
  rw [henergy, ccmPositivePairedCauchyKernel_eq_reduced hzdom hzdom]
  simp

end

end RHTower

namespace RHTower

noncomputable section

/-! ## Exact finite positive-paired source matrices -/

/-- Coefficients of the doubled packet underlying a positive paired packet. -/
def xiPositivePairedDoubledCoeff
    {ι : Type*} (c : ι → ℂ) : ι ⊕ ι → ℂ
  | Sum.inl i => c i
  | Sum.inr i => -c i

/-- Poles of the doubled packet underlying a positive paired packet. -/
def xiPositivePairedDoubledPole
    {ι : Type*} {R : ℝ}
    (z : ι → XiPositiveExteriorContinuedCauchyPoint R) :
    ι ⊕ ι → XiContinuedCauchyPoint
  | Sum.inl i => (z i).1
  | Sum.inr i => xiContinuedCauchyNegConj (z i).1

/-- A finite positive-frequency paired Cauchy packet. -/
def xiWeilPositivePairedContinuedCauchyPacketLp
    {ι : Type*} [Fintype ι] (R : ℝ) (c : ι → ℂ)
    (z : ι → XiPositiveExteriorContinuedCauchyPoint R) :
    lp (fun _ : XiZeroCopy => ℂ) 2 :=
  ∑ i, c i • xiWeilPositivePairedContinuedCauchyLp R (z i)

/-- The explicit four-block source energy of a positive paired packet. -/
def ccmPositivePairedPacketSourceEnergy
    {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (z : ι → ℂ) : ℝ :=
  (∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) *
    ccmPositivePairedCauchyKernel (z i) (z j)).re

/-- The same packet energy after the exact one-sided reflection reduction. -/
def ccmPositivePairedPacketReducedEnergy
    {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (z : ι → ℂ) : ℝ :=
  (∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) *
    ((ccmPositivePairedReducedKernel (z i) (z j) : ℝ) : ℂ)).re

/-- The doubled standard Cauchy packet is exactly the paired packet. -/
theorem xiWeilContinuedCauchyPacketLp_doubled_eq_positivePaired
    {ι : Type*} [Fintype ι] (R : ℝ) (c : ι → ℂ)
    (z : ι → XiPositiveExteriorContinuedCauchyPoint R) :
    xiWeilContinuedCauchyPacketLp
        (xiPositivePairedDoubledCoeff c)
        (xiPositivePairedDoubledPole z) =
      xiWeilPositivePairedContinuedCauchyPacketLp R c z := by
  unfold xiWeilContinuedCauchyPacketLp
  rw [Fintype.sum_sum_type]
  unfold xiPositivePairedDoubledCoeff xiPositivePairedDoubledPole
  unfold xiWeilPositivePairedContinuedCauchyPacketLp
  simp only [xiWeilPositivePairedContinuedCauchyLp]
  simp_rw [neg_smul, smul_sub]
  rw [Finset.sum_neg_distrib, Finset.sum_sub_distrib]
  exact (sub_eq_add_neg _ _).symm

/-- Positive-pole conjugate separation is exactly what is needed to separate the whole doubled
packet. -/
theorem xiPositivePairedDoubledPole_conjSeparated
    {ι : Type*} [Fintype ι] {R : ℝ} (hR : 0 ≤ R)
    (z : ι → XiPositiveExteriorContinuedCauchyPoint R)
    (hsep : ∀ i j, (z i : ℂ) ≠ (starRingEnd ℂ) (z j : ℂ)) :
    ∀ u v : ι ⊕ ι,
      (xiPositivePairedDoubledPole z u : ℂ) ≠
        (starRingEnd ℂ) (xiPositivePairedDoubledPole z v : ℂ) := by
  intro u v
  rcases u with i | i <;> rcases v with j | j
  · exact hsep i j
  · intro h
    have hre := congrArg Complex.re h
    have hzi : 0 < (z i : ℂ).re := lt_of_le_of_lt hR (z i).property
    have hzj : 0 < (z j : ℂ).re := lt_of_le_of_lt hR (z j).property
    simp [xiPositivePairedDoubledPole, xiContinuedCauchyNegConj,
      xiCenteredNegConj] at hre
    linarith
  · intro h
    have hre := congrArg Complex.re h
    have hzi : 0 < (z i : ℂ).re := lt_of_le_of_lt hR (z i).property
    have hzj : 0 < (z j : ℂ).re := lt_of_le_of_lt hR (z j).property
    simp [xiPositivePairedDoubledPole, xiContinuedCauchyNegConj,
      xiCenteredNegConj] at hre
    linarith
  · intro h
    apply hsep i j
    have hc := congrArg (starRingEnd ℂ) h
    simpa [xiPositivePairedDoubledPole, xiContinuedCauchyNegConj,
      xiCenteredNegConj] using congrArg Neg.neg hc

/-- Expanding the doubled source energy produces exactly the four-block paired kernel. -/
theorem continuedCauchyPacketSourceEnergy_doubled_eq_positivePaired
    {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (z : ι → ℂ) (zd : ι ⊕ ι → XiContinuedCauchyPoint)
    (hzd : ∀ i, (zd (Sum.inl i) : ℂ) = z i)
    (hzdr : ∀ i, (zd (Sum.inr i) : ℂ) = xiCenteredNegConj (z i)) :
    continuedCauchyPacketSourceEnergy
        (xiPositivePairedDoubledCoeff c) zd =
      ccmPositivePairedPacketSourceEnergy c z := by
  unfold continuedCauchyPacketSourceEnergy
  unfold ccmPositivePairedPacketSourceEnergy
  simp only [Fintype.sum_sum_type]
  simp only [xiPositivePairedDoubledCoeff, hzd, hzdr, map_neg]
  unfold ccmPositivePairedCauchyKernel
  simp_rw [← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  ring

/-- Exact reduced positive-frequency source matrix for every separated positive paired packet. -/
theorem xiWeilHilbertQuadratic_positivePairedPacket_eq_reducedEnergy
    {ι : Type*} [Fintype ι] (R : ℝ) (hR : 0 ≤ R)
    (c : ι → ℂ) (z : ι → XiPositiveExteriorContinuedCauchyPoint R)
    (hsep : ∀ i j, (z i : ℂ) ≠ (starRingEnd ℂ) (z j : ℂ)) :
    xiWeilHilbertQuadratic
        (xiWeilPositivePairedContinuedCauchyPacketLp R c z) =
      ccmPositivePairedPacketReducedEnergy c (fun i ↦ (z i : ℂ)) := by
  let cd : ι ⊕ ι → ℂ := xiPositivePairedDoubledCoeff c
  let zd : ι ⊕ ι → XiContinuedCauchyPoint :=
    xiPositivePairedDoubledPole z
  have hdsep : ∀ u v, (zd u : ℂ) ≠ (starRingEnd ℂ) (zd v : ℂ) :=
    xiPositivePairedDoubledPole_conjSeparated hR z hsep
  have hsource :=
    xiWeilHilbertQuadratic_indexedCauchyPacket_eq_continuedSource_re
      cd zd hdsep
  rw [xiWeilContinuedCauchyPacketLp_doubled_eq_positivePaired R c z]
    at hsource
  rw [hsource]
  have hexpand := continuedCauchyPacketSourceEnergy_doubled_eq_positivePaired
    c (fun i ↦ (z i : ℂ)) zd (fun _ ↦ rfl) (fun _ ↦ rfl)
  change continuedCauchyPacketSourceEnergy cd zd = _
  change continuedCauchyPacketSourceEnergy
    (xiPositivePairedDoubledCoeff c) zd = _
  rw [hexpand]
  unfold ccmPositivePairedPacketSourceEnergy
  unfold ccmPositivePairedPacketReducedEnergy
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro i _hi
  apply Finset.sum_congr rfl
  intro j _hj
  rw [ccmPositivePairedCauchyKernel_eq_reduced
    (z i).1.property (z j).1.property]

end

end RHTower

namespace RHTower

noncomputable section

/-- Every algebraic positive-paired source vector has a finite indexed packet representation. -/
theorem exists_finsupp_positivePairedPacket_eq_of_mem
    (R : ℝ) (v : lp (fun _ : XiZeroCopy => ℂ) 2)
    (hv : v ∈ xiWeilPositivePairedContinuedCauchyAlgebraicSubspace R) :
    ∃ c : XiPositiveExteriorContinuedCauchyPoint R →₀ ℂ,
      xiWeilPositivePairedContinuedCauchyPacketLp R
        (fun i : {x // x ∈ c.support} ↦ c i.1)
        (fun i : {x // x ∈ c.support} ↦ i.1) = v := by
  rw [xiWeilPositivePairedContinuedCauchyAlgebraicSubspace] at hv
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hv
  refine ⟨c, ?_⟩
  rw [← hc]
  unfold xiWeilPositivePairedContinuedCauchyPacketLp
  rw [Finsupp.sum]
  exact (Finset.sum_subtype c.support (fun _ => Iff.rfl)
    (fun i => c i • xiWeilPositivePairedContinuedCauchyLp R i)).symm

/-- The centered negative-conjugation map is continuous. -/
theorem continuous_xiCenteredNegConj : Continuous xiCenteredNegConj := by
  unfold xiCenteredNegConj
  fun_prop

/-- Positive pairwise conjugate-separated packets are dense in every finite positive paired
packet, and their reduced source energies converge to the Hilbert quadratic value. -/
theorem exists_pairwiseConjSeparatedPositivePairedSourceEnergy_tendsto
    {ι : Type*} [Fintype ι] (R : ℝ) (hR : 0 ≤ R)
    (c : ι → ℂ) (z : ι → XiPositiveExteriorContinuedCauchyPoint R) :
    ∃ w : ℕ → ι → XiPositiveExteriorContinuedCauchyPoint R,
      (∀ n i j, (w n i : ℂ) ≠ (starRingEnd ℂ) (w n j : ℂ)) ∧
      Tendsto
        (fun n ↦ xiWeilPositivePairedContinuedCauchyPacketLp R c (w n))
        atTop
        (nhds (xiWeilPositivePairedContinuedCauchyPacketLp R c z)) ∧
      Tendsto
        (fun n ↦ ccmPositivePairedPacketReducedEnergy c
          (fun i ↦ (w n i : ℂ)))
        atTop
        (nhds (xiWeilHilbertQuadratic
          (xiWeilPositivePairedContinuedCauchyPacketLp R c z))) := by
  obtain ⟨w0, hw0sep, hw0⟩ :=
    exists_pairwiseConjSeparatedContinuedCauchyPacket_tendsto
      (fun i ↦ (z i).1)
  have hopen : IsOpen {u : ℂ | R < u.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hw0Positive : ∀ᶠ n in atTop, ∀ i, R < (w0 n i : ℂ).re := by
    rw [Filter.eventually_all]
    intro i
    exact (hw0 i).eventually (hopen.mem_nhds (z i).property)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hw0Positive
  let w : ℕ → ι → XiPositiveExteriorContinuedCauchyPoint R := fun n i ↦
    ⟨w0 (n + N) i, hN (n + N) (Nat.le_add_left N n) i⟩
  have hwpoint : ∀ i,
      Tendsto (fun n ↦ (w n i : ℂ)) atTop (nhds (z i : ℂ)) := by
    intro i
    exact (hw0 i).comp (tendsto_add_atTop_nat N)
  have hwmirror : ∀ i,
      Tendsto
        (fun n ↦ (xiContinuedCauchyNegConj (w n i).1 : ℂ))
        atTop
        (nhds (xiContinuedCauchyNegConj (z i).1 : ℂ)) := by
    intro i
    exact continuous_xiCenteredNegConj.continuousAt.tendsto.comp (hwpoint i)
  have hwvec : Tendsto
      (fun n ↦ xiWeilPositivePairedContinuedCauchyPacketLp R c (w n))
      atTop
      (nhds (xiWeilPositivePairedContinuedCauchyPacketLp R c z)) := by
    unfold xiWeilPositivePairedContinuedCauchyPacketLp
    apply tendsto_finsetSum
    intro i _hi
    apply Filter.Tendsto.const_smul
    exact (tendsto_xiWeilCauchyLp (hwpoint i)).sub
      (tendsto_xiWeilCauchyLp (hwmirror i))
  have hwsep : ∀ n i j,
      (w n i : ℂ) ≠ (starRingEnd ℂ) (w n j : ℂ) := by
    intro n i j
    exact hw0sep (n + N) i j
  refine ⟨w, hwsep, hwvec, ?_⟩
  have hQ := continuous_xiWeilHilbertQuadratic.continuousAt.tendsto.comp hwvec
  apply hQ.congr'
  exact Eventually.of_forall fun n ↦ by
    simpa only [Function.comp_apply] using
      xiWeilHilbertQuadratic_positivePairedPacket_eq_reducedEnergy
        R hR c (w n) (hwsep n)

/-- Positivity of every exact finite reduced matrix on separated positive exterior poles. -/
def XiPositivePairedReducedSourcePassivity (R : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] (c : ι → ℂ)
    (z : ι → XiPositiveExteriorContinuedCauchyPoint R),
    (∀ i j, (z i : ℂ) ≠ (starRingEnd ℂ) (z j : ℂ)) →
      0 ≤ ccmPositivePairedPacketReducedEnergy c (fun i ↦ (z i : ℂ))

/-- Reduced positive-frequency source passivity gives positivity on the paired algebraic core,
including collision limits. -/
theorem positivePairedCore_nonnegative_of_reducedSourcePassivity
    (R : ℝ) (hR : 0 ≤ R)
    (hsource : XiPositivePairedReducedSourcePassivity R) :
    ∀ v ∈ xiWeilPositivePairedContinuedCauchyAlgebraicSubspace R,
      0 ≤ xiWeilHilbertQuadratic v := by
  intro v hv
  obtain ⟨c, hc⟩ := exists_finsupp_positivePairedPacket_eq_of_mem R v hv
  let ι := {x // x ∈ c.support}
  let coeff : ι → ℂ := fun i ↦ c i.1
  let pole : ι → XiPositiveExteriorContinuedCauchyPoint R := fun i ↦ i.1
  obtain ⟨w, hwsep, _hwvec, hwenergy⟩ :=
    exists_pairwiseConjSeparatedPositivePairedSourceEnergy_tendsto
      R hR coeff pole
  have hnonneg : ∀ n,
      0 ≤ ccmPositivePairedPacketReducedEnergy coeff
        (fun i ↦ (w n i : ℂ)) := by
    intro n
    exact hsource ι coeff (w n) (hwsep n)
  have hlimit :
      0 ≤ xiWeilHilbertQuadratic
        (xiWeilPositivePairedContinuedCauchyPacketLp R coeff pole) :=
    ge_of_tendsto hwenergy (Eventually.of_forall hnonneg)
  rw [show xiWeilPositivePairedContinuedCauchyPacketLp R coeff pole = v by
    exact hc] at hlimit
  exact hlimit

/-- The exact one-sided reduced prime--Gamma matrix criterion implies RH. -/
theorem riemannHypothesis_of_positivePairedReducedSourcePassivity
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R)
    (hsource : XiPositivePairedReducedSourcePassivity R) :
    RiemannHypothesis :=
  riemannHypothesis_of_positivePairedContinuedCauchyCore_nonnegative R hband
    (positivePairedCore_nonnegative_of_reducedSourcePassivity
      R hband.1 hsource)

/-- RH supplies every reduced positive-frequency paired source matrix inequality. -/
theorem positivePairedReducedSourcePassivity_of_riemannHypothesis
    (R : ℝ) (hR : 0 ≤ R) (hRH : RiemannHypothesis) :
    XiPositivePairedReducedSourcePassivity R := by
  intro ι _inst c z hsep
  rw [← xiWeilHilbertQuadratic_positivePairedPacket_eq_reducedEnergy
    R hR c z hsep]
  exact xiWeilHilbertQuadratic_nonneg_of_riemannHypothesis hRH _

/-- **Exact positive-frequency value criterion.**  At every quartet-admissible radius, RH is
 equivalent to positive semidefiniteness of all finite real reduced prime--Gamma kernel matrices
 on separated positive exterior poles. -/
theorem positivePairedReducedSourcePassivity_iff_riemannHypothesis
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R) :
    XiPositivePairedReducedSourcePassivity R ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_positivePairedReducedSourcePassivity R hband,
    positivePairedReducedSourcePassivity_of_riemannHypothesis R hband.1⟩

/-- Clean rational positive-frequency reduced source criterion. -/
theorem positivePairedReducedSourcePassivity_twoHundredEighteen_twentyFifths_iff_rh :
    XiPositivePairedReducedSourcePassivity (218 / 25) ↔ RiemannHypothesis :=
  positivePairedReducedSourcePassivity_iff_riemannHypothesis
    (218 / 25) xiOffLineQuartetAccretiveBand_twoHundredEighteen_twentyFifths

end

end RHTower
