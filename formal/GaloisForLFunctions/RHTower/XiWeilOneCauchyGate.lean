import GaloisForLFunctions.RHTower.PrimeArchAntiHerglotzGate
import GaloisForLFunctions.RHTower.XiWeilCauchyPoleExhaustion
import GaloisForLFunctions.RHTower.XiWeilResolventGram

/-!
# One-Cauchy source gate to RH

The regular two-pole Cauchy criterion can be reduced further.  On the centered upper half-strip,
the diagonal Weil value of one regular Cauchy kernel is the continued prime--archimedean divided
difference

`(T(conj z) - T(z)) / (z - conj z) = -Im(T(z)) / Im(z)`.

Thus nonnegativity of single-kernel diagonals is exactly the source anti-Herglotz sign already known
to exclude every off-line Xi zero.  This module proves the conjugation law for the relative trace,
identifies the source divided-difference condition with anti-Herglotzness, and gives an exact
one-Cauchy positivity criterion for RH.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The Xi relative resolvent trace respects centered critical-line conjugation. -/
theorem xiRelativeResolventTrace_conj (z : ℂ) :
    xiRelativeResolventTrace ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (xiRelativeResolventTrace z) := by
  unfold xiRelativeResolventTrace
  calc
    (∑' q : XiZeroCopy,
        xiRelativeResolventTerm ((starRingEnd ℂ) z) q) =
        ∑' q : XiZeroCopy,
          xiRelativeResolventTerm ((starRingEnd ℂ) z)
            (xiZeroCopyLineConjEquiv q) := by
      symm
      exact xiZeroCopyLineConjEquiv.tsum_eq _
    _ = ∑' q : XiZeroCopy,
        (starRingEnd ℂ) (xiRelativeResolventTerm z q) := by
      apply tsum_congr
      intro q
      simp [xiRelativeResolventTerm, xiSpectralPoint_lineConj]
    _ = (starRingEnd ℂ)
        (∑' q : XiZeroCopy, xiRelativeResolventTerm z q) := by
      exact (Complex.conj_tsum _).symm

/-- Conjugation law for the continued source whenever both centered points lie in its natural
pole-free domain. -/
theorem continuedPrimeArchSourceRelativeTrace_conj_of_domain
    {z : ℂ}
    (hzpos : 0 < (1 / 2 + z * I).re)
    (hz1 : 1 / 2 + z * I ≠ 1)
    (hzzeta : riemannZeta (1 / 2 + z * I) ≠ 0)
    (hcpos : 0 < (1 / 2 + (starRingEnd ℂ) z * I).re)
    (hc1 : 1 / 2 + (starRingEnd ℂ) z * I ≠ 1)
    (hczeta : riemannZeta (1 / 2 + (starRingEnd ℂ) z * I) ≠ 0) :
    continuedPrimeArchSourceRelativeTrace ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (continuedPrimeArchSourceRelativeTrace z) := by
  rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      hcpos hc1 hczeta,
    continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      hzpos hz1 hzzeta,
    xiRelativeResolventTrace_conj]

/-- The conjugate centered point of an upper-half-strip source point remains in the continued
prime--archimedean pole-free domain. -/
theorem continuedPrimeArch_conj_domain_of_upperHalfStrip
    {z : ℂ} (hzpos : 0 < z.im) (hzhalf : z.im < 1 / 2)
    (hzeta : riemannZeta (1 / 2 + z * I) ≠ 0) :
    0 < (1 / 2 + (starRingEnd ℂ) z * I).re ∧
      1 / 2 + (starRingEnd ℂ) z * I ≠ 1 ∧
      riemannZeta (1 / 2 + (starRingEnd ℂ) z * I) ≠ 0 := by
  have hspos : 0 < (1 / 2 + z * I).re :=
    centeredAbscissa_re_pos (by linarith)
  have hs1 : 1 / 2 + z * I ≠ 1 :=
    centeredAbscissa_ne_one (by linarith)
  have hXi : XiC z ≠ 0 :=
    XiC_ne_zero_of_continuedPrimeArch_domain hspos hs1 hzeta
  have hcXi : XiC ((starRingEnd ℂ) z) ≠ 0 := XiC_ne_zero_conj hXi
  have hcpos : 0 < (1 / 2 + (starRingEnd ℂ) z * I).re := by
    simp [mul_re]
    linarith
  have hc1 : 1 / 2 + (starRingEnd ℂ) z * I ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [mul_re] at hre
    linarith
  have hczeta : riemannZeta (1 / 2 + (starRingEnd ℂ) z * I) ≠ 0 := by
    have hxi : xi (1 / 2 + (starRingEnd ℂ) z * I) ≠ 0 := by
      simpa only [XiC] using hcXi
    exact (xi_eq_zero_iff hcpos hc1).not.mp hxi
  exact ⟨hcpos, hc1, hczeta⟩

/-- Upper-half-strip conjugation law for the continued source. -/
theorem continuedPrimeArchSourceRelativeTrace_conj_of_upperHalfStrip
    {z : ℂ} (hzpos : 0 < z.im) (hzhalf : z.im < 1 / 2)
    (hzeta : riemannZeta (1 / 2 + z * I) ≠ 0) :
    continuedPrimeArchSourceRelativeTrace ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (continuedPrimeArchSourceRelativeTrace z) := by
  have hspos : 0 < (1 / 2 + z * I).re := centeredAbscissa_re_pos (by linarith)
  have hs1 : 1 / 2 + z * I ≠ 1 :=
    centeredAbscissa_ne_one (by linarith)
  obtain ⟨hcpos, hc1, hczeta⟩ :=
    continuedPrimeArch_conj_domain_of_upperHalfStrip hzpos hzhalf hzeta
  exact continuedPrimeArchSourceRelativeTrace_conj_of_domain
    hspos hs1 hzeta hcpos hc1 hczeta

/-- Source-only positivity of the one-Cauchy divided-difference diagonal on the centered upper
half-strip. -/
def ContinuedPrimeArchUpperCauchyDiagonalNonnegative : Prop :=
  ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
    riemannZeta (1 / 2 + z * I) ≠ 0 →
      0 ≤ (((continuedPrimeArchSourceRelativeTrace ((starRingEnd ℂ) z) -
        continuedPrimeArchSourceRelativeTrace z) /
          (z - (starRingEnd ℂ) z)).re)

/-- The one-Cauchy source diagonal is exactly the anti-Herglotz sign. -/
theorem continuedPrimeArchUpperCauchyDiagonalNonnegative_iff_antiHerglotz :
    ContinuedPrimeArchUpperCauchyDiagonalNonnegative ↔
      ContinuedPrimeArchUpperAntiHerglotz := by
  constructor
  · intro hdiag z hzpos hzhalf hzeta
    have hconj := continuedPrimeArchSourceRelativeTrace_conj_of_upperHalfStrip
      hzpos hzhalf hzeta
    have hd := hdiag z hzpos hzhalf hzeta
    rw [hconj] at hd
    have hzine : z.im ≠ 0 := ne_of_gt hzpos
    have hcalc :
        ((((starRingEnd ℂ) (continuedPrimeArchSourceRelativeTrace z) -
          continuedPrimeArchSourceRelativeTrace z) /
            (z - (starRingEnd ℂ) z)).re) =
          -(continuedPrimeArchSourceRelativeTrace z).im / z.im := by
      rw [Complex.div_re]
      simp [Complex.normSq_apply]
      field_simp
      ring
    rw [hcalc] at hd
    have hm := mul_nonneg hd hzpos.le
    rw [div_mul_cancel₀ _ hzine] at hm
    linarith
  · intro hanti z hzpos hzhalf hzeta
    have hconj := continuedPrimeArchSourceRelativeTrace_conj_of_upperHalfStrip
      hzpos hzhalf hzeta
    rw [hconj]
    have hzine : z.im ≠ 0 := ne_of_gt hzpos
    have hcalc :
        ((((starRingEnd ℂ) (continuedPrimeArchSourceRelativeTrace z) -
          continuedPrimeArchSourceRelativeTrace z) /
            (z - (starRingEnd ℂ) z)).re) =
          -(continuedPrimeArchSourceRelativeTrace z).im / z.im := by
      rw [Complex.div_re]
      simp [Complex.normSq_apply]
      field_simp
      ring
    rw [hcalc]
    exact div_nonneg (neg_nonneg.mpr (hanti z hzpos hzhalf hzeta)) hzpos.le

/-- Positivity of every single regular Cauchy diagonal in the centered upper half-strip. -/
def XiWeilUpperOneCauchyNonnegative : Prop :=
  ∀ z : XiCRegularPoint, 0 < (z : ℂ).im → (z : ℂ).im < 1 / 2 →
    0 ≤ (xiWeilPolarization (xiWeilCauchyTest z) (xiWeilCauchyTest z)).re

/-- One-Cauchy Weil positivity supplies the source divided-difference sign. -/
theorem continuedPrimeArchUpperCauchyDiagonalNonnegative_of_xiWeilOneCauchy
    (hone : XiWeilUpperOneCauchyNonnegative) :
    ContinuedPrimeArchUpperCauchyDiagonalNonnegative := by
  intro z hzpos hzhalf hzeta
  have hspos : 0 < (1 / 2 + z * I).re := centeredAbscissa_re_pos (by linarith)
  have hs1 : 1 / 2 + z * I ≠ 1 :=
    centeredAbscissa_ne_one (by linarith)
  have hXi : XiC z ≠ 0 :=
    XiC_ne_zero_of_continuedPrimeArch_domain hspos hs1 hzeta
  obtain ⟨hcpos, hc1, hczeta⟩ :=
    continuedPrimeArch_conj_domain_of_upperHalfStrip hzpos hzhalf hzeta
  let zr : XiCRegularPoint := ⟨z, hXi⟩
  have hpos := hone zr hzpos hzhalf
  have hne : z ≠ (starRingEnd ℂ) z := by
    intro h
    have him := congrArg Complex.im h
    simp at him
    linarith
  rw [xiWeilPolarization_cauchy_eq_continuedPrimeArchSource_dividedDifference
    hspos hs1 hzeta hcpos hc1 hczeta hne] at hpos
  exact hpos

/-- One regular Cauchy diagonal at a time already suffices to prove RH. -/
theorem riemannHypothesis_of_xiWeilUpperOneCauchyNonnegative
    (hone : XiWeilUpperOneCauchyNonnegative) : RiemannHypothesis :=
  riemannHypothesis_of_continuedPrimeArchUpperAntiHerglotz
    (continuedPrimeArchUpperCauchyDiagonalNonnegative_iff_antiHerglotz.mp
      (continuedPrimeArchUpperCauchyDiagonalNonnegative_of_xiWeilOneCauchy hone))

/-- RH makes every regular one-Cauchy diagonal nonnegative. -/
theorem xiWeilUpperOneCauchyNonnegative_of_riemannHypothesis
    (hRH : RiemannHypothesis) : XiWeilUpperOneCauchyNonnegative := by
  intro z _hzpos _hzhalf
  exact xiWeilPolarization_diagonal_nonneg_of_riemannHypothesis hRH _
    (XiWeilSquareSummable_cauchy z)

/-- Exact rank-one Cauchy criterion for RH. -/
theorem xiWeilUpperOneCauchyNonnegative_iff_riemannHypothesis :
    XiWeilUpperOneCauchyNonnegative ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_xiWeilUpperOneCauchyNonnegative,
    xiWeilUpperOneCauchyNonnegative_of_riemannHypothesis⟩

/-- The source-only one-Cauchy divided-difference sign proves RH. -/
theorem riemannHypothesis_of_continuedPrimeArchUpperCauchyDiagonalNonnegative
    (hsource : ContinuedPrimeArchUpperCauchyDiagonalNonnegative) :
    RiemannHypothesis :=
  riemannHypothesis_of_continuedPrimeArchUpperAntiHerglotz
    (continuedPrimeArchUpperCauchyDiagonalNonnegative_iff_antiHerglotz.mp hsource)

/-- RH supplies the source-only one-Cauchy divided-difference sign. -/
theorem continuedPrimeArchUpperCauchyDiagonalNonnegative_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ContinuedPrimeArchUpperCauchyDiagonalNonnegative :=
  continuedPrimeArchUpperCauchyDiagonalNonnegative_of_xiWeilOneCauchy
    (xiWeilUpperOneCauchyNonnegative_of_riemannHypothesis hRH)

/-- Exact source-only rank-one divided-difference criterion for RH. -/
theorem continuedPrimeArchUpperCauchyDiagonalNonnegative_iff_riemannHypothesis :
    ContinuedPrimeArchUpperCauchyDiagonalNonnegative ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_continuedPrimeArchUpperCauchyDiagonalNonnegative,
    continuedPrimeArchUpperCauchyDiagonalNonnegative_of_riemannHypothesis⟩

end

end RHTower
