import GaloisForLFunctions.RHTower.XiWardInteriorTraceSplit
import GaloisForLFunctions.RHTower.CCM.CCMRectangularDominantFold

/-!
# Functional-equation absorption of the Ward boundary symbol

Functional-equation reflection sends every strict-right Xi divisor copy to
the strict-left complementary divisor.  At an interior probe, one reflected
mode is exactly its genus-one boundary contact plus a positive Poisson term.
Schwarz pairing before summation makes the contact series absolutely
summable.  Consequently the complementary logarithmic derivative absorbs
the complete strict-right boundary self-symbol.

This removes the last target-fed term from the interior Ward bound: the
resulting majorant contains only pole, Gamma, and von Mangoldt source data.
-/

open Complex

namespace RHTower

noncomputable section

/-- A reflected strict-left mode is its right boundary contact plus its
interior Poisson resolvent. -/
theorem xiWard_reflectedRelativeResolventTerm_eq
    (q : XiRightZeroCopy) (w : ℂ)
    (hw : 1 / 2 < w.re) :
    2 * I * xiRelativeResolventTerm (I * w)
        (xiRightLeftReflectEquiv q).1 =
      2 * ((xiRightCenteredZero q)⁻¹ +
        (w - xiRightCenteredZero q)⁻¹) := by
  rw [xiRelativeResolventTerm]
  change
    2 * I *
        ((xiSpectralPoint (xiZeroCopyReflectEquiv q.1))⁻¹ -
          (xiSpectralPoint (xiZeroCopyReflectEquiv q.1) - I * w)⁻¹) =
      2 * ((I * xiSpectralPoint q.1)⁻¹ +
        (w - I * xiSpectralPoint q.1)⁻¹)
  rw [xiSpectralPoint_reflect]
  have hI : I ≠ (0 : ℂ) := I_ne_zero
  have hI2 : I ^ (2 : ℕ) = -(1 : ℂ) := by norm_num
  have hq : xiSpectralPoint q.1 ≠ 0 := xiSpectralPoint_ne_zero q.1
  have hIq : I * xiSpectralPoint q.1 ≠ 0 := mul_ne_zero hI hq
  have hlam_re :
      (I * xiSpectralPoint q.1).re < 1 / 2 :=
    (abs_lt.mp (abs_re_I_mul_xiSpectralPoint_le_half q.1)).2
  have hwq : w - I * xiSpectralPoint q.1 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.zero_re] at hre
    linarith
  have hsub : -xiSpectralPoint q.1 - I * w ≠ 0 := by
    intro h
    apply hwq
    have hmul : -I * (w - I * xiSpectralPoint q.1) = 0 := by
      calc
        -I * (w - I * xiSpectralPoint q.1)
            = -xiSpectralPoint q.1 - I * w := by
                calc
                  _ = -I * w + I ^ (2 : ℕ) * xiSpectralPoint q.1 := by ring
                  _ = -xiSpectralPoint q.1 - I * w := by rw [hI2]; ring
        _ = 0 := h
    exact (mul_eq_zero.mp hmul).resolve_left (neg_ne_zero.mpr hI)
  field_simp [hI, hq, hIq, hwq, hsub]
  simp only [hI2]
  ring_nf
  simp only [hI2]
  ring

/-- The reflected strict-left mode dominates its boundary contact in real
part throughout the source half-plane. -/
theorem re_xiWard_reflectedRelativeResolventTerm_ge_contact
    (q : XiRightZeroCopy) (w : ℂ) (hw : 1 / 2 < w.re) :
    (2 * (xiRightCenteredZero q)⁻¹).re ≤
      (2 * I * xiRelativeResolventTerm (I * w)
        (xiRightLeftReflectEquiv q).1).re := by
  rw [xiWard_reflectedRelativeResolventTerm_eq q w hw]
  simp only [Complex.mul_re, Complex.add_re, Complex.inv_re,
    Complex.sub_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul,
    sub_zero]
  have hlam_re :
      (xiRightCenteredZero q).re < 1 / 2 :=
    (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q)).2
  have hnum : 0 < (w - xiRightCenteredZero q).re := by
    simp only [Complex.sub_re]
    linarith
  have hne : w - xiRightCenteredZero q ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [Complex.zero_re] at hre
    linarith
  have hden : 0 < Complex.normSq (w - xiRightCenteredZero q) :=
    Complex.normSq_pos.mpr hne
  have hfrac : 0 ≤
      (w - xiRightCenteredZero q).re /
        Complex.normSq (w - xiRightCenteredZero q) :=
    div_nonneg hnum.le hden.le
  rw [Complex.sub_re] at hfrac
  linarith

def xiWardLeftReflectedPairResponse
    (q : XiRightUpperZeroCopy) (w : ℂ) : ℂ :=
  2 * I * xiRelativeResolventTerm (I * w)
      (xiRightLeftReflectEquiv q.1).1 +
    2 * I * xiRelativeResolventTerm (I * w)
      (xiRightLeftReflectEquiv
        (xiRightZeroCopyConjEquiv q.1)).1

theorem re_xiWardLeftReflectedPairResponse_ge_boundary
    (q : XiRightUpperZeroCopy) (w : ℂ) (hw : 1 / 2 < w.re) :
    (xiAntiCausalWardBoundaryPairTerm q).re ≤
      (xiWardLeftReflectedPairResponse q w).re := by
  have hq :=
    re_xiWard_reflectedRelativeResolventTerm_ge_contact q.1 w hw
  have hqc :=
    re_xiWard_reflectedRelativeResolventTerm_ge_contact
      (xiRightZeroCopyConjEquiv q.1) w hw
  rw [xiAntiCausalWardBoundaryPairTerm_eq_pair,
    xiWardLeftReflectedPairResponse]
  simp only [Complex.mul_re, Complex.add_re, Complex.re_ofNat,
    Complex.im_ofNat, zero_mul, sub_zero] at hq hqc ⊢
  linarith

private theorem re_boundary_le_left_tsum
    {w : ℂ} (hw : 1 / 2 < w.re) (hz : XiC (I * w) ≠ 0) :
    (xiAntiCausalWardBoundarySelfSymbol).re ≤
      ∑' q : XiLeftZeroCopy,
        (2 * I * xiRelativeResolventTerm (I * w) q.1).re := by
  let F : XiZeroCopy → ℝ := fun q =>
    (2 * I * xiRelativeResolventTerm (I * w) q).re
  let G : XiRightZeroCopy → ℝ := fun q =>
    F (xiRightLeftReflectEquiv q).1
  have hsumFComplex := summable_xiRelativeResolventTerm hz
  have hsumF : Summable F :=
    (Complex.hasSum_re
      (hsumFComplex.mul_left (2 * I)).hasSum).summable
  have hsumLeft : Summable (fun q : XiLeftZeroCopy => F q.1) :=
    hsumF.subtype _
  have hsumG : Summable G := by
    exact (xiRightLeftReflectEquiv.summable_iff (f := fun q : XiLeftZeroCopy => F q.1)).mpr hsumLeft
  have hinl : Summable (fun q : XiRightUpperZeroCopy =>
      G (xiRightSchwarzPairEquiv (Sum.inl q))) := by
    simp only [xiRightSchwarzPairEquiv_inl]
    exact hsumG.comp_injective Subtype.val_injective
  have hinr : Summable (fun q : XiRightUpperZeroCopy =>
      G (xiRightSchwarzPairEquiv (Sum.inr q))) := by
    simp only [xiRightSchwarzPairEquiv_inr]
    exact hsumG.comp_injective (xiRightZeroCopyConjEquiv.injective.comp Subtype.val_injective)
  have hsumPair : Summable (fun q : XiRightUpperZeroCopy =>
      (xiWardLeftReflectedPairResponse q w).re) := by
    exact (hinl.add hinr).congr (fun q => by
      simp only [G, F, xiRightSchwarzPairEquiv_inl,
        xiRightSchwarzPairEquiv_inr,
        xiWardLeftReflectedPairResponse, Complex.add_re])
  have hleft_eq :
      (∑' q : XiLeftZeroCopy, F q.1) =
        ∑' q : XiRightUpperZeroCopy,
          (xiWardLeftReflectedPairResponse q w).re := by
    calc
      (∑' q : XiLeftZeroCopy, F q.1) =
          ∑' q : XiRightZeroCopy, G q := by
        exact (xiRightLeftReflectEquiv.tsum_eq
          (fun q : XiLeftZeroCopy => F q.1)).symm
      _ = ∑' x : XiRightUpperZeroCopy ⊕ XiRightUpperZeroCopy,
          G (xiRightSchwarzPairEquiv x) :=
        (xiRightSchwarzPairEquiv.tsum_eq G).symm
      _ = (∑' q : XiRightUpperZeroCopy,
            G (xiRightSchwarzPairEquiv (Sum.inl q))) +
          ∑' q : XiRightUpperZeroCopy,
            G (xiRightSchwarzPairEquiv (Sum.inr q)) :=
        (HasSum.sum (f := fun x => G (xiRightSchwarzPairEquiv x)) hinl.hasSum hinr.hasSum).tsum_eq
      _ = ∑' q : XiRightUpperZeroCopy,
          (G (xiRightSchwarzPairEquiv (Sum.inl q)) +
            G (xiRightSchwarzPairEquiv (Sum.inr q))) :=
        (hinl.tsum_add hinr).symm
      _ = ∑' q : XiRightUpperZeroCopy,
          (xiWardLeftReflectedPairResponse q w).re := by
        apply tsum_congr
        intro q
        simp only [G, F, xiRightSchwarzPairEquiv_inl,
          xiRightSchwarzPairEquiv_inr,
          xiWardLeftReflectedPairResponse, Complex.add_re]
  have hsumBoundaryRe : Summable (fun q : XiRightUpperZeroCopy =>
      (xiAntiCausalWardBoundaryPairTerm q).re) :=
    (Complex.hasSum_re
      summable_xiAntiCausalWardBoundaryPairTerm.hasSum).summable
  have hpair_le :
      (∑' q : XiRightUpperZeroCopy,
          (xiAntiCausalWardBoundaryPairTerm q).re) ≤
        ∑' q : XiRightUpperZeroCopy,
          (xiWardLeftReflectedPairResponse q w).re :=
    Summable.tsum_le_tsum
      (fun q => re_xiWardLeftReflectedPairResponse_ge_boundary q w hw)
      hsumBoundaryRe hsumPair
  rw [xiAntiCausalWardBoundarySelfSymbol,
    Complex.re_tsum summable_xiAntiCausalWardBoundaryPairTerm,
    hleft_eq]
  exact hpair_le

private theorem left_tsum_le_nonright_complement
    {w : ℂ} (hw : 1 / 2 < w.re) (hz : XiC (I * w) ≠ 0) :
    (∑' q : XiLeftZeroCopy,
        (2 * I * xiRelativeResolventTerm (I * w) q.1).re) ≤
      ∑' q : ↑{q : XiZeroCopy |
          0 < (I * xiSpectralPoint q).re}ᶜ,
        (2 * I * xiRelativeResolventTerm (I * w) q.1).re := by
  let F : XiZeroCopy → ℝ := fun q =>
    (2 * I * xiRelativeResolventTerm (I * w) q).re
  let L : Set XiZeroCopy := {q | (I * xiSpectralPoint q).re < 0}
  let R : Set XiZeroCopy := {q | 0 < (I * xiSpectralPoint q).re}
  have hsumFComplex := summable_xiRelativeResolventTerm hz
  have hsumF : Summable F :=
    (Complex.hasSum_re
      (hsumFComplex.mul_left (2 * I)).hasSum).summable
  have hz₀ : 1 / 2 < (I * w).im := by
    simpa only [Complex.mul_im, Complex.I_re, zero_mul,
      Complex.I_im, one_mul, zero_add] using hw
  change (∑' q : ↑L, F q.1) ≤ ∑' q : ↑Rᶜ, F q.1
  rw [tsum_subtype, tsum_subtype]
  exact Summable.tsum_le_tsum (fun q => by
    by_cases hl : q ∈ L
    · have hc : q ∈ Rᶜ := by
        change ¬0 < (I * xiSpectralPoint q).re
        change (I * xiSpectralPoint q).re < 0 at hl
        linarith
      simp only [Set.indicator_of_mem hl, Set.indicator_of_mem hc]
      exact le_rfl
    · rw [Set.indicator_of_notMem hl]
      by_cases hc : q ∈ Rᶜ
      · rw [Set.indicator_of_mem hc]
        have hq : (I * xiSpectralPoint q).re ≤ 0 := by
          change ¬0 < (I * xiSpectralPoint q).re at hc
          exact not_lt.mp hc
        exact re_two_I_mul_relativeResolventTerm_nonneg hq hz₀
      · rw [Set.indicator_of_notMem hc])
    (hsumF.indicator L) (hsumF.indicator Rᶜ)

/-- The nonright complement contains the reflected strict-left divisor and any disjoint selected
critical-line stratum.  Keeping the latter instead of discarding it is the source-side form of
separating positive real shifts from diagonal critical multiplicity. -/
private theorem left_tsum_add_critical_tsum_le_nonright_complement
    {w : ℂ} (hw : 1 / 2 < w.re) (hz : XiC (I * w) ≠ 0)
    (C : Set XiZeroCopy)
    (hcritical : ∀ q, q ∈ C → (I * xiSpectralPoint q).re = 0) :
    (∑' q : XiLeftZeroCopy,
        (2 * I * xiRelativeResolventTerm (I * w) q.1).re) +
      ∑' q : C,
        (2 * I * xiRelativeResolventTerm (I * w) q.1).re ≤
      ∑' q : ↑{q : XiZeroCopy |
          0 < (I * xiSpectralPoint q).re}ᶜ,
        (2 * I * xiRelativeResolventTerm (I * w) q.1).re := by
  let F : XiZeroCopy → ℝ := fun q =>
    (2 * I * xiRelativeResolventTerm (I * w) q).re
  let L : Set XiZeroCopy := {q | (I * xiSpectralPoint q).re < 0}
  let R : Set XiZeroCopy := {q | 0 < (I * xiSpectralPoint q).re}
  have hsumFComplex := summable_xiRelativeResolventTerm hz
  have hsumF : Summable F :=
    (Complex.hasSum_re
      (hsumFComplex.mul_left (2 * I)).hasSum).summable
  have hsumL : Summable (L.indicator F) := hsumF.indicator L
  have hsumC : Summable (C.indicator F) := hsumF.indicator C
  have hsumR : Summable (Rᶜ.indicator F) := hsumF.indicator Rᶜ
  have hz₀ : 1 / 2 < (I * w).im := by
    simpa only [Complex.mul_im, Complex.I_re, zero_mul,
      Complex.I_im, one_mul, zero_add] using hw
  have hpoint : ∀ q : XiZeroCopy,
      L.indicator F q + C.indicator F q ≤ Rᶜ.indicator F q := by
    intro q
    by_cases hl : q ∈ L
    · have hnc : q ∉ C := by
        intro hc
        have hzero := hcritical q hc
        change (I * xiSpectralPoint q).re < 0 at hl
        linarith
      have hrc : q ∈ Rᶜ := by
        change ¬ 0 < (I * xiSpectralPoint q).re
        change (I * xiSpectralPoint q).re < 0 at hl
        linarith
      simp only [Set.indicator_of_mem hl, Set.indicator_of_notMem hnc,
        Set.indicator_of_mem hrc, add_zero]
      exact le_rfl
    · by_cases hc : q ∈ C
      · have hrc : q ∈ Rᶜ := by
          change ¬ 0 < (I * xiSpectralPoint q).re
          rw [hcritical q hc]
          norm_num
        simp only [Set.indicator_of_notMem hl, Set.indicator_of_mem hc,
          Set.indicator_of_mem hrc, zero_add]
        exact le_rfl
      · simp only [Set.indicator_of_notMem hl, Set.indicator_of_notMem hc,
          zero_add]
        by_cases hrc : q ∈ Rᶜ
        · rw [Set.indicator_of_mem hrc]
          have hq : (I * xiSpectralPoint q).re ≤ 0 := by
            change ¬ 0 < (I * xiSpectralPoint q).re at hrc
            exact not_lt.mp hrc
          exact re_two_I_mul_relativeResolventTerm_nonneg hq hz₀
        · rw [Set.indicator_of_notMem hrc]
  change (∑' q : ↑L, F q.1) + (∑' q : C, F q.1) ≤
    ∑' q : ↑Rᶜ, F q.1
  rw [tsum_subtype, tsum_subtype, tsum_subtype]
  calc
    (∑' q : XiZeroCopy, L.indicator F q) +
        ∑' q : XiZeroCopy, C.indicator F q =
        ∑' q : XiZeroCopy, (L.indicator F q + C.indicator F q) :=
      (hsumL.tsum_add hsumC).symm
    _ ≤ ∑' q : XiZeroCopy, Rᶜ.indicator F q :=
      Summable.tsum_le_tsum hpoint (hsumL.add hsumC) hsumR

theorem re_two_I_logDeriv_nonright_eq_complement_tsum
    {w : ℂ} (hz : XiC (I * w) ≠ 0) :
    (2 * I * logDeriv xiNonrightCanonicalProduct (I * w)).re =
      ∑' q : ↑{q : XiZeroCopy |
          0 < (I * xiSpectralPoint q).re}ᶜ,
        (2 * I * xiRelativeResolventTerm (I * w) q.1).re := by
  have hcan_ne : xiCanonicalProduct (I * w) ≠ 0 := by
    intro h
    apply hz
    have hsource :=
      congrFun xiHadamardQuotient_mul_canonicalProduct (I * w)
    rw [Pi.mul_apply] at hsource
    rw [← hsource, h, mul_zero]
  have hright_ne : xiRightCanonicalProduct (I * w) ≠ 0 := by
    intro h
    apply hcan_ne
    rw [xiCanonicalProduct_eq_right_mul_nonright (I * w), h, zero_mul]
  have hsumF := summable_xiRelativeResolventTerm hz
  have hsumR := summable_xiRightRelativeResolventTerm hright_ne
  have hreF : (2 * I * xiRelativeResolventTrace (I * w)).re =
      ∑' q : XiZeroCopy,
        (2 * I * xiRelativeResolventTerm (I * w) q).re := by
    rw [xiRelativeResolventTrace, ← tsum_mul_left,
      Complex.re_tsum (hsumF.mul_left (2 * I))]
  have hreR : (2 * I * xiRightRelativeResolventTrace (I * w)).re =
      ∑' q : XiRightZeroCopy,
        (2 * I * xiRelativeResolventTerm (I * w) q.1).re := by
    rw [xiRightRelativeResolventTrace, ← tsum_mul_left,
      Complex.re_tsum (hsumR.mul_left (2 * I))]
    exact tsum_congr fun q => rfl
  have hsumreF : Summable (fun q : XiZeroCopy =>
      (2 * I * xiRelativeResolventTerm (I * w) q).re) :=
    (Complex.hasSum_re (hsumF.mul_left (2 * I)).hasSum).summable
  have hsplit := hsumreF.tsum_subtype_add_tsum_subtype_compl
    {q : XiZeroCopy | 0 < (I * xiSpectralPoint q).re}
  have hld : logDeriv xiNonrightCanonicalProduct (I * w) =
      xiRelativeResolventTrace (I * w) -
        xiRightRelativeResolventTrace (I * w) :=
    logDeriv_nonright_eq_full_sub_right hz
  have hexpand : (2 * I *
      logDeriv xiNonrightCanonicalProduct (I * w)).re =
      (2 * I * xiRelativeResolventTrace (I * w)).re -
        (2 * I * xiRightRelativeResolventTrace (I * w)).re := by
    rw [hld]
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im]
    ring
  rw [hexpand, hreF, hreR]
  have hright_eq :
      (∑' q : XiRightZeroCopy,
          (2 * I * xiRelativeResolventTerm (I * w) q.1).re) =
        ∑' q : ↑{q : XiZeroCopy |
            0 < (I * xiSpectralPoint q).re},
          (2 * I * xiRelativeResolventTerm (I * w) q.1).re := rfl
  rw [hright_eq]
  linarith [hsplit]

/-- **Functional-equation boundary absorption law.**  At every interior
probe, the FE-reflected left divisor contained in the complementary
factor contributes the complete strict-right genus-one boundary symbol,
plus nonnegative Poisson mass. -/
theorem re_xiAntiCausalWardBoundarySelfSymbol_le_two_I_logDeriv_nonright
    {w : ℂ} (hw : 1 / 2 < w.re) (hz : XiC (I * w) ≠ 0) :
    (xiAntiCausalWardBoundarySelfSymbol).re ≤
      (2 * I * logDeriv xiNonrightCanonicalProduct (I * w)).re := by
  calc
    (xiAntiCausalWardBoundarySelfSymbol).re ≤
        ∑' q : XiLeftZeroCopy,
          (2 * I * xiRelativeResolventTerm (I * w) q.1).re :=
      re_boundary_le_left_tsum hw hz
    _ ≤ ∑' q : ↑{q : XiZeroCopy |
          0 < (I * xiSpectralPoint q).re}ᶜ,
        (2 * I * xiRelativeResolventTerm (I * w) q.1).re :=
      left_tsum_le_nonright_complement hw hz
    _ = (2 * I * logDeriv
          xiNonrightCanonicalProduct (I * w)).re :=
      (re_two_I_logDeriv_nonright_eq_complement_tsum hz).symm

/-- **Critical-line-retaining reflection absorption.**  The complementary factor pays both the
strict-right boundary self-symbol and every selected critical-line divisor contribution.  The
usual source majorant is the special case where the critical set is empty. -/
theorem re_boundary_add_critical_tsum_le_two_I_logDeriv_nonright
    {w : ℂ} (hw : 1 / 2 < w.re) (hz : XiC (I * w) ≠ 0)
    (C : Set XiZeroCopy)
    (hcritical : ∀ q, q ∈ C → (I * xiSpectralPoint q).re = 0) :
    (xiAntiCausalWardBoundarySelfSymbol).re +
        ∑' q : C,
          (2 * I * xiRelativeResolventTerm (I * w) q.1).re ≤
      (2 * I * logDeriv xiNonrightCanonicalProduct (I * w)).re := by
  have hboundary := re_boundary_le_left_tsum hw hz
  have hcriticalAbsorb :=
    left_tsum_add_critical_tsum_le_nonright_complement hw hz C hcritical
  have htrace := re_two_I_logDeriv_nonright_eq_complement_tsum
    (w := w) hz
  rw [htrace]
  linarith

theorem xiWard_interior_XiC_ne_zero
    {w : ℂ} (hw : 1 / 2 < w.re) :
    XiC (I * w) ≠ 0 := by
  have hright :
      1 < (1 / 2 + (-I * w) * I).re := by
    have hcoord :
        (1 / 2 + (-I * w) * I).re = 1 / 2 + w.re := by
      norm_num [Complex.add_re, Complex.mul_re, Complex.div_re,
        Complex.normSq_apply]
    rw [hcoord]
    linarith
  have hneg : XiC (-I * w) ≠ 0 :=
    XiC_ne_zero_of_one_lt_centered_re hright
  have harg : -I * w = -(I * w) := by ring
  rw [harg, XiC_even] at hneg
  exact hneg

/-- Arithmetic Ward head with no strict-right boundary symbol. -/
noncomputable def xiWardInteriorSourceArithmeticBound (w : ℂ) : ℝ :=
  (2 * (((1 / 2 : ℂ) + w)⁻¹ + ((1 / 2 : ℂ) + w - 1)⁻¹ +
    logDeriv Complex.Gammaℝ ((1 / 2 : ℂ) + w) -
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      ((1 / 2 : ℂ) + w))).re

/-- **Source-only interior Ward bound.**  FE-reflected complementary
mass absorbs the complete strict-right boundary symbol, leaving a bound
containing only pole, Gamma, and von Mangoldt source terms. -/
theorem re_continuedXiAntiCausalWardResponse_le_sourceArithmetic
    {w : ℂ} (hw : 1 / 2 < w.re) :
    (continuedXiAntiCausalWardResponse w).re ≤
      xiWardInteriorSourceArithmeticBound w := by
  have hz := xiWard_interior_XiC_ne_zero hw
  have hid := continuedXiAntiCausalWardResponse_eq_arithmetic hw hz
  have hquot := logDeriv_xiHadamardQuotient_eq_zero (I * w)
  rw [hquot, mul_zero, sub_zero] at hid
  have habsorb :=
    re_xiAntiCausalWardBoundarySelfSymbol_le_two_I_logDeriv_nonright
      hw hz
  have hre := congrArg Complex.re hid
  rw [Complex.add_re, Complex.sub_re] at hre
  unfold xiWardInteriorSourceArithmeticBound
  linarith [hre, habsorb]

/-- **Euler--Gamma source estimate with critical diagonal retained.**  Any selected critical-line
stratum can be moved to the left side of the source inequality.  Hence strict positive real
shifts and diagonal critical multiplicity are separated before the arithmetic majorant is read;
no RH, simplicity, or zero-selection hypothesis is used. -/
theorem re_continued_add_critical_tsum_le_sourceArithmetic
    {w : ℂ} (hw : 1 / 2 < w.re)
    (C : Set XiZeroCopy)
    (hcritical : ∀ q, q ∈ C → (I * xiSpectralPoint q).re = 0) :
    (continuedXiAntiCausalWardResponse w).re +
        ∑' q : C,
          (2 * I * xiRelativeResolventTerm (I * w) q.1).re ≤
      xiWardInteriorSourceArithmeticBound w := by
  have hz := xiWard_interior_XiC_ne_zero hw
  have hid := continuedXiAntiCausalWardResponse_eq_arithmetic hw hz
  have hquot := logDeriv_xiHadamardQuotient_eq_zero (I * w)
  rw [hquot, mul_zero, sub_zero] at hid
  have habsorb :=
    re_boundary_add_critical_tsum_le_two_I_logDeriv_nonright
      hw hz C hcritical
  have hre := congrArg Complex.re hid
  rw [Complex.add_re, Complex.sub_re] at hre
  unfold xiWardInteriorSourceArithmeticBound
  linarith [hre, habsorb]

/-- Source-only window clearing: one strict arithmetic inequality at an
interior probe excludes every strict-right Xi pair in the window. -/
theorem xiWard_source_window_clearing {h c δ : ℝ} (hh : 1 / 2 < h)
    (hA : xiWardInteriorSourceArithmeticBound
        (((h : ℝ) : ℂ) + I * ((c : ℝ) : ℂ)) <
      2 * h / ((h + 1 / 2) ^ (2 : ℕ) + δ ^ (2 : ℕ)))
    (q : XiRightUpperZeroCopy) :
    δ ^ (2 : ℕ) < ((xiRightCenteredZero q.1).im - c) ^ (2 : ℕ) := by
  by_contra hcon
  push Not at hcon
  have hq := interior_pair_quantum (by linarith : (0 : ℝ) < h) q hcon
  have hwre : (0 : ℝ) <
      ((((h : ℝ) : ℂ) + I * ((c : ℝ) : ℂ))).re := by
    norm_num [Complex.add_re, Complex.mul_re]
    linarith
  have hdom :=
    re_xiAntiCausalWardSchwarzPairResponse_le_continued q hwre
  have hwre2 : (1 / 2 : ℝ) <
      ((((h : ℝ) : ℂ) + I * ((c : ℝ) : ℂ))).re := by
    norm_num [Complex.add_re, Complex.mul_re]
    linarith
  have hup :=
    re_continuedXiAntiCausalWardResponse_le_sourceArithmetic hwre2
  linarith

end

end RHTower
