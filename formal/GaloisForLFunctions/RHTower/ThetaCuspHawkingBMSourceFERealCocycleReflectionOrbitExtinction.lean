import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSourceFEKernelPeierlsClassification

/-!
# Real source-FE cocycle and complete reflected-orbit Peierls extinction

The literal BM unit-source functional-equation cocycle is real exactly on the critical line.  The
proof is source-native: a real cocycle makes the reflected/unreflected source product real; after
cancelling the nonzero helicity factor, the carrier product becomes `t^2 * (t+6)` for
`t=s*(1-s)`.  Its imaginary part is the centered displacement times a strictly positive open-strip
cofactor.

Combining this rigidity with the arbitrary-kernel classification proves that every
reflection-real Ward kernel vanishes on the complete two-copy reflection block of a tilted Xi
fibre.  In particular, nondegeneracy only on reflection-pair entries—not on the diagonal—is enough
to make full packet covariance equivalent to RH.

`[NEW] [SOURCE COCYCLE REALITY] [MIXED-COPY EXTINCTION] [ARBITRARY KERNEL] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Unit-amplitude polynomial factor of the literal BM quadratic Einstein source. -/
def hbXiPeierlsUnitSourceCarrierPolynomial (s : ℂ) : ℂ :=
  (1 + s / 2) * (s / 2) ^ 2

/-- Reflection-paired carrier product collapses to one cubic in `s(1-s)`. -/
theorem hbXiPeierlsUnitSourceCarrierPolynomial_reflectionProduct
    (s : ℂ) :
    hbXiPeierlsUnitSourceCarrierPolynomial (1 - s) *
        hbXiPeierlsUnitSourceCarrierPolynomial s =
      (s * (1 - s)) ^ 2 * (s * (1 - s) + 6) / 64 := by
  unfold hbXiPeierlsUnitSourceCarrierPolynomial
  ring

/-- In the open critical strip at nonzero height, reality of the reflection-paired literal
carrier product forces the critical line. -/
theorem hbXiPeierlsUnitSourceCarrierPolynomial_reflectionProduct_im_eq_zero_implies
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) (him : s.im ≠ 0)
    (hreal :
      (hbXiPeierlsUnitSourceCarrierPolynomial (1 - s) *
        hbXiPeierlsUnitSourceCarrierPolynomial s).im = 0) :
    s.re = 1 / 2 := by
  let t : ℂ := s * (1 - s)
  let u : ℝ := s.re * (1 - s.re) + s.im ^ 2
  let v : ℝ := s.im * (1 - 2 * s.re)
  have htRe : t.re = u := by
    simp [t, u, Complex.mul_re]
    ring
  have htIm : t.im = v := by
    simp [t, v, Complex.mul_im]
    ring
  have hfactor := hbXiPeierlsUnitSourceCarrierPolynomial_reflectionProduct s
  have hpoly : (t ^ 2 * (t + 6)).im = 0 := by
    have hfactorIm := congrArg Complex.im hfactor
    rw [hreal] at hfactorIm
    change 0 = ((t ^ 2 * (t + 6)) / 64).im at hfactorIm
    norm_num [Complex.div_im] at hfactorIm
    norm_num [Complex.mul_im] at hfactorIm ⊢
    linarith
  have hpolyIm :
      (t ^ 2 * (t + 6)).im =
        t.im * (3 * t.re ^ 2 - t.im ^ 2 + 12 * t.re) := by
    simp [pow_two, Complex.mul_re, Complex.mul_im]
    ring
  rw [hpolyIm, htRe, htIm] at hpoly
  have hstrip : 0 < s.re * (1 - s.re) :=
    mul_pos h0 (sub_pos.mpr h1)
  have hbSq : 0 < s.im ^ 2 := sq_pos_of_ne_zero him
  have hu : 0 < u := by
    dsimp [u]
    positivity
  have hcenterSq : (1 - 2 * s.re) ^ 2 < 1 := by
    nlinarith
  have hvSq_lt_bSq : v ^ 2 < s.im ^ 2 := by
    dsimp [v]
    nlinarith [mul_pos hbSq (sub_pos.mpr hcenterSq)]
  have hvSq_lt_u : v ^ 2 < u := by
    dsimp [u]
    nlinarith
  have hcofactor : 0 < 3 * u ^ 2 - v ^ 2 + 12 * u := by
    nlinarith [sq_nonneg u]
  have hv : v = 0 :=
    (mul_eq_zero.mp hpoly).resolve_right (ne_of_gt hcofactor)
  dsimp [v] at hv
  have hcenter : 1 - 2 * s.re = 0 :=
    (mul_eq_zero.mp hv).resolve_left him
  linarith

/-- Literal BM source FE cocycle is real exactly on the critical line. -/
theorem hbXiPeierlsUnitSourceFECocycle_im_eq_zero_iff (q : XiZeroCopy) :
    (hbXiPeierlsUnitSourceFECocycle q).im = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hkappaIm
    by_contra hline
    let source : XiZeroCopy → ℂ :=
      fun r => d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 r
    let mixing : ℂ := d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q
    let carrier : XiZeroCopy → ℂ := fun r =>
      d4ThetaHawkingSelfDualQuadraticCarrierCoefficient 1 (xiSpectralPoint r)
    have hsource : source q ≠ 0 := by
      dsimp [source]
      exact (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero q).not.mpr
        hline
    have hmixing : mixing ≠ 0 := by
      dsimp [mixing]
      exact (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq_zero_iff q).not.mpr
        hline
    have hkappaOfReal :
        hbXiPeierlsUnitSourceFECocycle q =
          ((hbXiPeierlsUnitSourceFECocycle q).re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using hkappaIm
    have htransport := hbXiPeierlsUnitSourceFECocycle_sourceTransport q
    have hsourceProduct :
        source (xiZeroCopyReflectEquiv q) * source q =
          hbXiPeierlsUnitSourceFECocycle q * (Complex.normSq (source q) : ℂ) := by
      calc
        source (xiZeroCopyReflectEquiv q) * source q =
            (hbXiPeierlsUnitSourceFECocycle q *
              (starRingEnd ℂ) (source q)) * source q := by
                rw [htransport]
        _ = hbXiPeierlsUnitSourceFECocycle q *
            (source q * (starRingEnd ℂ) (source q)) := by ring
        _ = _ := by rw [Complex.mul_conj]
    have hsourceProductIm :
        (source (xiZeroCopyReflectEquiv q) * source q).im = 0 := by
      rw [hsourceProduct, hkappaOfReal]
      simp
    have hsourceFactor :
        source (xiZeroCopyReflectEquiv q) * source q =
          mixing ^ 2 *
            (carrier (xiZeroCopyReflectEquiv q) * carrier q) := by
      dsimp [source, mixing, carrier]
      rw [d4BMXiSecondHarmonicPolarizedSourceAmplitude,
        d4BMXiSecondHarmonicPolarizedSourceAmplitude,
        d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_reflect]
      ring
    rw [hsourceFactor] at hsourceProductIm
    have hmixingRe : mixing.re = 0 := by
      dsimp [mixing]
      rw [d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq]
      simp
    have hmixingIm : mixing.im ≠ 0 := by
      intro hzero
      apply hmixing
      apply Complex.ext
      · simpa using hmixingRe
      · simpa using hzero
    have hcarrierProductIm :
        (carrier (xiZeroCopyReflectEquiv q) * carrier q).im = 0 := by
      norm_num [pow_two, Complex.mul_re, Complex.mul_im, hmixingRe] at hsourceProductIm
      exact hsourceProductIm.resolve_left hmixingIm
    have href : ((xiZeroCopyReflectEquiv q).1 : ℂ) = 1 - (q.1 : ℂ) :=
      xiZeroReflectEquiv_apply q.1
    have hcarrierPolynomial :
        (hbXiPeierlsUnitSourceCarrierPolynomial (1 - (q.1 : ℂ)) *
          hbXiPeierlsUnitSourceCarrierPolynomial (q.1 : ℂ)).im = 0 := by
      dsimp [carrier] at hcarrierProductIm
      rw [d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_eq,
        d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_eq, href]
        at hcarrierProductIm
      simpa [hbXiPeierlsUnitSourceCarrierPolynomial] using hcarrierProductIm
    obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit q.1
    exact hline
      (hbXiPeierlsUnitSourceCarrierPolynomial_reflectionProduct_im_eq_zero_implies
        h0 h1 (xi_divisor_support_im_ne_zero q.1) hcarrierPolynomial)
  · intro hline
    have hsource :=
      (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero q).mpr hline
    simp [hbXiPeierlsUnitSourceFECocycle, hsource]

/-- A nonzero fixed Ward coefficient coupling a copy to its own FE reflection forces the wall. -/
theorem criticalLine_of_kernelWard_of_reflectionReal_of_reflectionPair_ne_zero
    (K : XiZeroCopy → XiZeroCopy → ℂ)
    (hward : HBXiPeierlsUnitSourceFEKernelWard K)
    (hreflect : HBXiPeierlsReflectionRealKernel K)
    (q : XiZeroCopy) (hpair : K q (xiZeroCopyReflectEquiv q) ≠ 0) :
    (q.1 : ℂ).re = 1 / 2 := by
  have hW := hward q (xiZeroCopyReflectEquiv q)
  rw [hreflect q (xiZeroCopyReflectEquiv q)] at hW
  have hK : (starRingEnd ℂ) (K q (xiZeroCopyReflectEquiv q)) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).mpr hpair
  have hproduct :
      hbXiPeierlsUnitSourceFECocycle q *
          hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv q) = 1 := by
    apply mul_left_cancel₀ hK
    simpa only [mul_one, mul_assoc] using hW
  have hcocycle := hbXiPeierlsUnitSourceFECocycle_involutive q
  have hkappaConj :
      hbXiPeierlsUnitSourceFECocycle q =
        (starRingEnd ℂ) (hbXiPeierlsUnitSourceFECocycle q) := by
    have hR : hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv q) ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at hcocycle
      norm_num at hcocycle
    apply mul_left_cancel₀ hR
    calc
      hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv q) *
          hbXiPeierlsUnitSourceFECocycle q = 1 := by simpa [mul_comm] using hproduct
      _ = hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv q) *
          (starRingEnd ℂ) (hbXiPeierlsUnitSourceFECocycle q) := hcocycle.symm
  have him : (hbXiPeierlsUnitSourceFECocycle q).im = 0 := by
    have h := congrArg Complex.im hkappaConj
    simp at h
    linarith
  exact (hbXiPeierlsUnitSourceFECocycle_im_eq_zero_iff q).mp him

/-- Every tilted functional-equation orbit block of a reflection-real Ward kernel is zero. -/
theorem kernel_reflectionOrbitBlock_eq_zero_of_kernelWard_of_reflectionReal_of_tilt
    (K : XiZeroCopy → XiZeroCopy → ℂ)
    (hward : HBXiPeierlsUnitSourceFEKernelWard K)
    (hreflect : HBXiPeierlsReflectionRealKernel K)
    (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    K q q = 0 ∧
      K q (xiZeroCopyReflectEquiv q) = 0 ∧
      K (xiZeroCopyReflectEquiv q) q = 0 ∧
      K (xiZeroCopyReflectEquiv q) (xiZeroCopyReflectEquiv q) = 0 := by
  have hdiag := kernel_diagonal_eq_zero_of_kernelWard_of_reflectionReal_of_tilt
    K hward hreflect q htilt
  have hpair : K q (xiZeroCopyReflectEquiv q) = 0 := by
    by_contra hne
    exact htilt (criticalLine_of_kernelWard_of_reflectionReal_of_reflectionPair_ne_zero
      K hward hreflect q hne)
  have hcross : K (xiZeroCopyReflectEquiv q) q = 0 := by
    have href := hreflect q (xiZeroCopyReflectEquiv q)
    rw [xiZeroCopyReflectEquiv_apply_apply, hpair, map_zero] at href
    exact href
  have hRdiag :
      K (xiZeroCopyReflectEquiv q) (xiZeroCopyReflectEquiv q) = 0 := by
    rw [hreflect q q, hdiag, map_zero]
  exact ⟨hdiag, hpair, hcross, hRdiag⟩

/-- Pure reflection-pair nondegeneracy is already enough: arbitrary other cross-orbit couplings do
not weaken the fixed-form RH obstruction. -/
theorem forall_hbXiPeierlsKernelForm_packetTransport_iff_rh_of_reflectionReal_of_reflectionPair
    (K : XiZeroCopy → XiZeroCopy → ℂ)
    (hreflect : HBXiPeierlsReflectionRealKernel K)
    (hpair : ∀ q : XiZeroCopy, K q (xiZeroCopyReflectEquiv q) ≠ 0) :
    (∀ x y : HBXiPeierlsPacket,
      hbXiPeierlsKernelForm K (hbXiPeierlsUnitSourceFEPacketTransport x)
          (hbXiPeierlsUnitSourceFEPacketTransport y) =
        (starRingEnd ℂ) (hbXiPeierlsKernelForm K x y)) ↔
      RiemannHypothesis := by
  rw [forall_hbXiPeierlsKernelForm_packetTransport_iff_kernelWard]
  constructor
  · intro hward
    apply (forall_hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff_rh).mp
    intro q
    apply (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff q).mpr
    exact criticalLine_of_kernelWard_of_reflectionReal_of_reflectionPair_ne_zero
      K hward hreflect q (hpair q)
  · intro hRH q r
    have hfixed :=
      (forall_hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff_rh).mpr hRH
    have hq : (q.1 : ℂ).re = 1 / 2 :=
      (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff q).mp (hfixed q)
    have hr : (r.1 : ℂ).re = 1 / 2 :=
      (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff r).mp (hfixed r)
    have hkq : hbXiPeierlsUnitSourceFECocycle q = 1 := by
      have hsource :=
        (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero q).mpr hq
      simp [hbXiPeierlsUnitSourceFECocycle, hsource]
    have hkr : hbXiPeierlsUnitSourceFECocycle r = 1 := by
      have hsource :=
        (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero r).mpr hr
      simp [hbXiPeierlsUnitSourceFECocycle, hsource]
    rw [hreflect q r, hkq, hkr, mul_one, mul_one]

end

end RHTower
