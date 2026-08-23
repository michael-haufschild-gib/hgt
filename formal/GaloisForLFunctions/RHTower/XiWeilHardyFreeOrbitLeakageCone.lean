import GaloisForLFunctions.RHTower.XiWeilHardyCriticalLocusVerifiedHeightBand

/-!
# Lorentzian localization of the free-orbit RH obstruction

For an off-critical Xi copy with centered spectral point `a`, the line-conjugate resolvent pair
has anti-Herglotz sign whenever

`a.im ^ 2 < (z.re - a.re) ^ 2 + z.im ^ 2`.

This is the spacelike side of a literal Lorentzian cone.  The complement is the closed timelike
cone emitted by that free reflection orbit.  After deleting the complete critical fixed locus,
all possible positive imaginary response is confined to the union of these cones.

Combining this geometric localization with the source-certified verified-height band shows that
RH is equivalent to free-sector passivity only above frequency `233 / 20` and only at observation
points lying in at least one off-critical leakage cone.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- An observation point is strictly outside every Lorentzian leakage cone emitted by an
off-critical Xi copy. -/
def XiOffCriticalLeakageConeAvoidance (z : ℂ) : Prop :=
  ∀ q : XiZeroCopy, q ∉ xiCriticalLineZeroCopySet →
    (xiSpectralPoint q).im ^ 2 <
      (z.re - (xiSpectralPoint q).re) ^ 2 + z.im ^ 2

/-- An observation point lies in the closed Lorentzian leakage cone of at least one off-critical
Xi copy. -/
def XiOffCriticalLeakageConeHit (z : ℂ) : Prop :=
  ∃ q : XiZeroCopy, q ∉ xiCriticalLineZeroCopySet ∧
    (z.re - (xiSpectralPoint q).re) ^ 2 + z.im ^ 2 ≤
      (xiSpectralPoint q).im ^ 2

/-- Leakage-cone hit is exactly failure of strict avoidance. -/
theorem not_xiOffCriticalLeakageConeAvoidance_iff_hit (z : ℂ) :
    ¬ XiOffCriticalLeakageConeAvoidance z ↔
      XiOffCriticalLeakageConeHit z := by
  classical
  constructor
  · intro h
    rw [XiOffCriticalLeakageConeAvoidance] at h
    push Not at h
    rcases h with ⟨q, hq, hcone⟩
    exact ⟨q, hq, hcone⟩
  · rintro ⟨q, hq, hcone⟩ hAvoid
    exact (not_lt_of_ge hcone) (hAvoid q hq)

/-- Outside all off-critical leakage cones, every free reflection orbit and hence their complete
relative-resolvent trace has the anti-Herglotz sign. -/
theorem xiOffCriticalRelativeResolventTrace_im_nonpos_of_leakageConeAvoidance
    (z : ℂ) (hzIm : 0 < z.im) (hXi : XiC z ≠ 0)
    (havoid : XiOffCriticalLeakageConeAvoidance z) :
    (xiOffCriticalRelativeResolventTrace z).im ≤ 0 := by
  apply xiOffCriticalRelativeResolventTrace_im_nonpos_of_lineConj_pairs z hXi
  intro q
  apply xiRelativeResolventTerm_lineConj_pair_im_nonpos_of_core z hzIm q
  by_cases hq : q ∈ xiCriticalLineZeroCopySet
  · have hqIm : (xiSpectralPoint q).im = 0 :=
      xiSpectralPoint_im_eq_zero_of_mem_criticalLine
        (⟨q, hq⟩ : XiCriticalLineResolventCopy)
    rw [hqIm]
    nlinarith [sq_pos_of_pos hzIm]
  · have hsep := havoid q hq
    linarith

/-- Positive free-sector imaginary response can occur only inside an off-critical leakage cone. -/
theorem xiOffCriticalLeakageConeHit_of_freeTrace_im_pos
    (z : ℂ) (hzIm : 0 < z.im) (hXi : XiC z ≠ 0)
    (hpos : 0 < (xiOffCriticalRelativeResolventTrace z).im) :
    XiOffCriticalLeakageConeHit z := by
  rw [← not_xiOffCriticalLeakageConeAvoidance_iff_hit]
  intro hAvoid
  have hsign :=
    xiOffCriticalRelativeResolventTrace_im_nonpos_of_leakageConeAvoidance
      z hzIm hXi hAvoid
  linarith

/-- Remaining positive-frequency passivity obligation, restricted to observation points inside
at least one off-critical leakage cone. -/
def OffCriticalRelativeResolventPositiveFrequencyLeakageConeAbove (R : ℝ) : Prop :=
  ∀ z : ℂ, R < z.re → 0 < z.im → z.im < 1 / 2 →
    riemannZeta (1 / 2 + z * I) ≠ 0 →
    XiOffCriticalLeakageConeHit z →
      (xiOffCriticalRelativeResolventTrace z).im ≤ 0

/-- Cone-exterior passivity is automatic, so the unrestricted free-sector tail condition is
equivalent to testing only points in the union of off-critical leakage cones. -/
theorem offCriticalRelativeResolventPositiveFrequencyAbove_iff_leakageConeAbove
    (R : ℝ) :
    OffCriticalRelativeResolventPositiveFrequencyAbove R ↔
      OffCriticalRelativeResolventPositiveFrequencyLeakageConeAbove R := by
  constructor
  · intro hfree z hzRe hzIm hzHalf hzeta _hHit
    exact hfree z hzRe hzIm hzHalf hzeta
  · intro hcone z hzRe hzIm hzHalf hzeta
    by_cases hAvoid : XiOffCriticalLeakageConeAvoidance z
    · have hspos : 0 < (1 / 2 + z * I).re := centeredAbscissa_re_pos hzHalf
      have hs1 : 1 / 2 + z * I ≠ 1 := centeredAbscissa_ne_one hzIm
      have hXi : XiC z ≠ 0 :=
        XiC_ne_zero_of_continuedPrimeArch_domain hspos hs1 hzeta
      exact
        xiOffCriticalRelativeResolventTrace_im_nonpos_of_leakageConeAvoidance
          z hzIm hXi hAvoid
    · exact hcone z hzRe hzIm hzHalf hzeta
        ((not_xiOffCriticalLeakageConeAvoidance_iff_hit z).mp hAvoid)

/-- Source-certified Lorentzian endpoint: RH is equivalent to passivity of the free reflection
sector only above frequency `233 / 20` and only inside the union of off-critical leakage cones. -/
theorem riemannHypothesis_iff_offCriticalRelativeResolventPositiveFrequencyLeakageConeAbove_twoHundredThirtyThree_twentieths :
    RiemannHypothesis ↔
      OffCriticalRelativeResolventPositiveFrequencyLeakageConeAbove
        (233 / 20) :=
  riemannHypothesis_iff_offCriticalRelativeResolventPositiveFrequencyAbove_twoHundredThirtyThree_twentieths.trans
    (offCriticalRelativeResolventPositiveFrequencyAbove_iff_leakageConeAbove
      (233 / 20))

end

end RHTower
