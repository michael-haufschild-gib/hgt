import GaloisForLFunctions.RHTower.XiHedenmalmKummerCollision
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmGaussianHankelApertureWidthSpectrum
import GaloisForLFunctions.RHTower.XiWeilOneCauchyGate
import GaloisForLFunctions.RHTower.CentralReciprocalMoments
import GaloisForLFunctions.RHTower.XiHurwitzHardyAnchor
import GaloisForLFunctions.RHTower.XiZerosInfinite
import GaloisForLFunctions.RHTower.XiDerivativeKummerCollision
import GaloisForLFunctions.RHTower.ThetaFourierLaplaceLocalKummerCollision

/-!
# RH supplies Hedenmalm Kummer roots

The endpoint Xi half-plane bound and the relative-resolvent orientation law imply that the
Hedenmalm source

`E_Xi(z) = XiC(z) + I * XiC'(z)`

is zero-free in the centered upper half-plane under RH.  Indeed, an `E_Xi` zero would force the
Xi logarithmic derivative to equal `I`, while reflection of the lower-half-plane resolvent sign
forces its imaginary part to be nonpositive.

The centered upper half-plane is simply connected, so both `XiC` and `E_Xi` have analytic roots
of every positive degree there.  Thus every nontrivial common Hedenmalm Kummer-root interface is
equivalent to RH, and the degree-two source premise is discharged under RH.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- RH supplies the endpoint transverse half-plane bound. -/
theorem xiZeroHalfPlaneBound_zero_of_rh
    (hRH : RiemannHypothesis) :
    XiZeroHalfPlaneBound 0 := by
  intro rho hzero
  let support : XiDivisorSupport :=
    ⟨rho, mem_xi_divisor_support_of_eq_zero hzero⟩
  have hre := xi_divisor_support_re_eq_half_of_rh hRH support
  simpa only [add_zero] using hre.le

/-- The zero-width Xi half-plane bound is exactly RH. -/
theorem xiZeroHalfPlaneBound_zero_iff_rh :
    XiZeroHalfPlaneBound 0 ↔ RiemannHypothesis := by
  constructor
  · intro hbound
    rw [rh_iff_xi_ne_zero_right]
    intro rho hrho hzero
    have hle := hbound rho hzero
    rw [mem_rightHalf] at hrho
    norm_num at hle
    linarith
  · exact xiZeroHalfPlaneBound_zero_of_rh

/-- Under RH, `XiC` is zero-free in the centered upper half-plane. -/
theorem XiC_ne_zero_upperHalf_of_rh
    (hRH : RiemannHypothesis) {z : ℂ}
    (hz : z ∈ xiCenteredUpperHalfPlane) :
    XiC z ≠ 0 := by
  intro hzero
  have hxi : xi (1 / 2 + z * I) = 0 := by
    simpa only [XiC] using hzero
  let support : XiDivisorSupport :=
    ⟨1 / 2 + z * I, mem_xi_divisor_support_of_eq_zero hxi⟩
  have hre := xi_divisor_support_re_eq_half_of_rh hRH support
  rw [xiCenteredUpperHalfPlane, Set.mem_setOf_eq] at hz
  dsimp only [support] at hre
  have hcoord : (1 / 2 + z * I).re = 1 / 2 - z.im := by
    simp
    ring
  rw [hcoord] at hre
  linarith

/-- Under RH, the relative-resolvent trace has the upper-half-plane anti-Herglotz sign. -/
theorem xiRelativeResolventTrace_im_nonpos_upperHalf_of_rh
    (hRH : RiemannHypothesis) {z : ℂ}
    (hz : z ∈ xiCenteredUpperHalfPlane) :
    (xiRelativeResolventTrace z).im ≤ 0 := by
  have hzConj : ((starRingEnd ℂ) z).im < -(0 : ℝ) := by
    rw [xiCenteredUpperHalfPlane, Set.mem_setOf_eq] at hz
    simp
    linarith
  have hlower :=
    xiRelativeResolventTrace_im_nonneg_of_halfPlaneBound
      (alpha := 0) (by rfl)
      (xiZeroHalfPlaneBound_zero_of_rh hRH)
      ((starRingEnd ℂ) z) hzConj
  have hreflect := congrArg Complex.im
    (xiRelativeResolventTrace_conj z)
  simp only [Complex.conj_im] at hreflect
  linarith

/-- Under RH, the Hedenmalm source `XiC + I * XiC'` has no upper-half-plane zero. -/
theorem xiHedenmalmDeBrangesE_ne_zero_upperHalf_of_rh
    (hRH : RiemannHypothesis) {z : ℂ}
    (hz : z ∈ xiCenteredUpperHalfPlane) :
    xiHedenmalmDeBrangesE z ≠ 0 := by
  intro hEzero
  have hXi := XiC_ne_zero_upperHalf_of_rh hRH hz
  have hderiv : deriv XiC z = I * XiC z := by
    rw [xiHedenmalmDeBrangesE] at hEzero
    have hmul := congrArg (fun w : ℂ => I * w) hEzero
    change I * (XiC z + I * deriv XiC z) = I * 0 at hmul
    rw [mul_add, mul_zero, ← mul_assoc, I_mul_I, neg_one_mul] at hmul
    linear_combination -hmul
  have hlog : logDeriv XiC z = I := by
    rw [logDeriv_apply, hderiv]
    field_simp [hXi]
  have htrace : xiRelativeResolventTrace z = I := by
    rw [← logDeriv_XiC_eq_relativeResolventTrace hXi]
    exact hlog
  have himNonpos :=
    xiRelativeResolventTrace_im_nonpos_upperHalf_of_rh hRH hz
  rw [htrace] at himNonpos
  norm_num at himNonpos

/-- The Hedenmalm source is entire. -/
theorem xiHedenmalmDeBrangesE_analytic :
    AnalyticOnNhd ℂ xiHedenmalmDeBrangesE Set.univ := by
  intro z _
  change AnalyticAt ℂ (fun w => XiC w + I * deriv XiC w) z
  exact (XiC_analytic z (Set.mem_univ z)).add
    (analyticAt_const.mul (XiC_analytic z (Set.mem_univ z)).deriv)

/-- The centered upper half-plane is convex. -/
theorem convex_xiCenteredUpperHalfPlane :
    Convex ℝ xiCenteredUpperHalfPlane := by
  rw [xiCenteredUpperHalfPlane]
  exact convex_halfSpace_im_gt 0

/-- RH supplies common analytic Kummer roots of `XiC` and the Hedenmalm source in every positive
degree. -/
theorem xiHedenmalmCommonKummerRootUpperHalf_of_rh
    {d : ℕ} (hd : d ≠ 0) (hRH : RiemannHypothesis) :
    XiHedenmalmCommonKummerRootUpperHalf d := by
  have hsc : IsSimplyConnected xiCenteredUpperHalfPlane :=
    isSimplyConnected_of_convex convex_xiCenteredUpperHalfPlane
      ⟨I, by simp [xiCenteredUpperHalfPlane]⟩
  obtain ⟨g, hg, _hgne, hgpow⟩ :=
    U0KummerBranch.exists_analyticOnNhd_pow_eq
      isOpen_xiCenteredUpperHalfPlane hsc
      (XiC_analytic.mono (Set.subset_univ _))
      (fun z hz => XiC_ne_zero_upperHalf_of_rh hRH hz)
      hd
  obtain ⟨h, hh, _hhne, hhpow⟩ :=
    U0KummerBranch.exists_analyticOnNhd_pow_eq
      isOpen_xiCenteredUpperHalfPlane hsc
      (xiHedenmalmDeBrangesE_analytic.mono (Set.subset_univ _))
      (fun z hz => xiHedenmalmDeBrangesE_ne_zero_upperHalf_of_rh
        hRH hz)
      hd
  exact ⟨g, h, hg, hh, hgpow, hhpow⟩

/-- For every nontrivial degree, the common Xi/Hedenmalm Kummer-root interface is exactly RH. -/
theorem xiHedenmalmCommonKummerRootUpperHalf_iff_rh
    {d : ℕ} (hd : 1 < d) :
    XiHedenmalmCommonKummerRootUpperHalf d ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_xiHedenmalmCommonKummerRootUpperHalf hd,
    xiHedenmalmCommonKummerRootUpperHalf_of_rh
      (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hd))⟩

/-- RH discharges the upper-half-plane Hedenmalm square-root interface. -/
theorem xiHedenmalmESquareRootUpperHalf_of_rh
    (hRH : RiemannHypothesis) :
    XiHedenmalmESquareRootUpperHalf := by
  obtain ⟨_g, h, _hg, hh, _hgpow, hhpow⟩ :=
    xiHedenmalmCommonKummerRootUpperHalf_of_rh
      (d := 2) (by norm_num) hRH
  exact ⟨h, hh, hhpow⟩

/-- The first multiplicity rung together with the formerly conditional Hedenmalm square root is
an exact RH characterization. -/
theorem rhLadder_one_and_xiHedenmalmESquareRootUpperHalf_iff_rh :
    RHLadder 1 ∧ XiHedenmalmESquareRootUpperHalf ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨hladder, hroot⟩
    exact riemannHypothesis_of_rhLadder_one_of_xiHedenmalmESquareRootUpperHalf
      hladder hroot
  · intro hRH
    exact ⟨(rh_iff_forall_ladder.mp hRH) 1,
      xiHedenmalmESquareRootUpperHalf_of_rh hRH⟩

/-- **Xi Hedenmalm-Kummer/Hurwitz-anchor reality universality law.** For every nontrivial
Kummer degree, common analytic roots of `XiC` and its Hedenmalm source on the centered upper
half-plane are equivalent to existence of one critical-line Xi-divisor anchor together with
reality of every two-node Hurwitz separator at every critical anchor. -/
theorem xiHedenmalmKummerRoot_iff_hurwitzCriticalAnchorRealityUniversality
    {d : ℕ} (hd : 1 < d) :
    XiHedenmalmCommonKummerRootUpperHalf d ↔
      (∃ τ : XiDivisorSupport, (τ : ℂ).re = 1 / 2) ∧
        XiHurwitzEveryCriticalAnchorPairVandermondeReal := by
  constructor
  · intro hroot
    have hRH :=
      riemannHypothesis_of_xiHedenmalmCommonKummerRootUpperHalf hd hroot
    letI : Infinite XiDivisorSupport :=
      Set.infinite_coe_iff.mpr xiDivisorSupport_infinite
    let τ : XiDivisorSupport :=
      Classical.choice (inferInstance : Nonempty XiDivisorSupport)
    refine ⟨⟨τ, xi_divisor_support_re_eq_half_of_rh hRH τ⟩, ?_⟩
    intro anchor _hanchor
    exact xiHurwitzAnchoredPairVandermondeReal_of_rh hRH anchor
  · rintro ⟨⟨τ, hτ⟩, hreal⟩
    have hRH : RiemannHypothesis :=
      (riemannHypothesis_iff_xiHurwitzAnchoredPairVandermondeReal
        τ hτ).mpr (hreal τ hτ)
    exact xiHedenmalmCommonKummerRootUpperHalf_of_rh
      (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hd)) hRH

/-- Any nontrivial Kummer collision among the differentiated Xi, Hedenmalm, or differentiated
theta source pairs forces common Hedenmalm covers of every nontrivial degree. This is the
Hedenmalm-source half of the three-source all-degree closure law. -/
theorem anyKummerCollision_allHedenmalmSourceCoversUniversality
    {dXi dH dTheta : ℕ}
    (hdXi : 1 < dXi) (hdH : 1 < dH) (hdTheta : 1 < dTheta)
    (hsource :
      XiDerivativeCommonKummerRootRightHalf dXi ∨
        XiHedenmalmCommonKummerRootUpperHalf dH ∨
          ThetaCuspDerivativeCommonKummerRootRightZeroBand dTheta) :
    ∀ e : ℕ, 1 < e →
      XiHedenmalmCommonKummerRootUpperHalf e := by
  have hRH : RiemannHypothesis := by
    rcases hsource with hXi | hH | hTheta
    · exact riemannHypothesis_of_xiDerivativeCommonKummerRootRightHalf
        hdXi hXi
    · exact riemannHypothesis_of_xiHedenmalmCommonKummerRootUpperHalf
        hdH hH
    · exact
        riemannHypothesis_of_thetaCuspDerivativeCommonKummerRootRightZeroBand
          hdTheta hTheta
  intro e he
  exact xiHedenmalmCommonKummerRootUpperHalf_of_rh
    (Nat.ne_of_gt (lt_trans Nat.zero_lt_one he)) hRH

end

end RHTower
