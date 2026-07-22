import GaloisForLFunctions.RHTower.XiSquaredEulerAllDegreeChargeCriterion
import GaloisForLFunctions.RHTower.XiSquaredEulerApertureDiagonalControlObstruction

/-!
# Xi squared-Euler diagonal-correlation universality

The atomic transverse-charge radical, finite-packet boundary charge, finite central minors,
orbitwise diagonal control, all-degree global domination, prime--Gamma source cone, and complete
Weil cone carry exactly one orientation datum.  The complementary theorem packages explicit
atomic, packet, polynomial, source, and Weil witnesses in the failure chamber.
-/

open Complex Polynomial
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

/-- Every multiplicity-exact squared-Euler atom has zero transverse charge. -/
def XiSquaredEulerAllOrbitChargeDensitiesVanish : Prop :=
  ∀ q : XiZeroCopy, xiSquaredEulerApertureOrbitChargeDensity q = 0

/-- Atomic transverse-charge vanishing is exactly RH. -/
theorem xiSquaredEulerAllOrbitChargeDensitiesVanish_iff_riemannHypothesis :
    XiSquaredEulerAllOrbitChargeDensitiesVanish ↔ RiemannHypothesis := by
  constructor
  · intro hcharge
    apply riemannHypothesis_iff_forall_xiZeroCopyReciprocalSquare_nonnegative.2
    intro q
    have hline : (q.1 : ℂ).re = 1 / 2 :=
      (xiSquaredEulerApertureOrbitChargeDensity_eq_zero_iff q).1 (hcharge q)
    have him : (xiZeroCopyReciprocalSquare q).im = 0 := by
      rw [xiZeroCopyReciprocalSquare_eq]
      exact (xiCentralReciprocalSquare_im_eq_zero_iff q.1).2 hline
    exact Complex.nonneg_iff.2
      ⟨(xiZeroCopyReciprocalSquare_re_pos q).le, him.symm⟩
  · intro hRH q
    have hpositive : (0 : ℂ) ≤ xiZeroCopyReciprocalSquare q :=
      riemannHypothesis_iff_forall_xiZeroCopyReciprocalSquare_nonnegative.1 hRH q
    have him : (xiZeroCopyReciprocalSquare q).im = 0 :=
      (Complex.nonneg_iff.1 hpositive).2.symm
    apply (xiSquaredEulerApertureOrbitChargeDensity_eq_zero_iff q).2
    apply (xiCentralReciprocalSquare_im_eq_zero_iff q.1).1
    simpa only [xiZeroCopyReciprocalSquare_eq] using him

/-- Every nonempty finite packet has zero total transverse boundary charge. -/
def XiSquaredEulerAllFinitePacketBoundaryChargesVanish : Prop :=
  ∀ S : Finset XiZeroCopy, S.Nonempty →
    xiSquaredEulerFiniteApertureBoundaryCharge S = 0

/-- Finite-packet boundary-charge vanishing is exactly RH. -/
theorem xiSquaredEulerAllFinitePacketBoundaryChargesVanish_iff_riemannHypothesis :
    XiSquaredEulerAllFinitePacketBoundaryChargesVanish ↔ RiemannHypothesis := by
  constructor
  · intro hpacket
    apply xiSquaredEulerAllOrbitChargeDensitiesVanish_iff_riemannHypothesis.1
    intro q
    have hzero := hpacket {q} (by simp)
    have hline : (q.1 : ℂ).re = 1 / 2 :=
      (xiSquaredEulerFiniteApertureBoundaryCharge_eq_zero_iff (by simp)).1
        hzero q (by simp)
    exact (xiSquaredEulerApertureOrbitChargeDensity_eq_zero_iff q).2 hline
  · intro hRH S hS
    apply (xiSquaredEulerFiniteApertureBoundaryCharge_eq_zero_iff hS).2
    intro q _hq
    exact (xiSquaredEulerApertureOrbitChargeDensity_eq_zero_iff q).1
      (xiSquaredEulerAllOrbitChargeDensitiesVanish_iff_riemannHypothesis.2 hRH q)

/-- Every finite multiplicity-exact packet has nonnegative first central squared-Euler minor. -/
def XiSquaredEulerAllFiniteCentralMinorsNonnegative : Prop :=
  ∀ S : Finset XiZeroCopy, 0 ≤ xiSquaredEulerFiniteApertureCentralMinor S

/-- Finite central-minor nonnegativity is exactly RH; singleton packets detect every failure. -/
theorem xiSquaredEulerAllFiniteCentralMinorsNonnegative_iff_riemannHypothesis :
    XiSquaredEulerAllFiniteCentralMinorsNonnegative ↔ RiemannHypothesis := by
  constructor
  · intro hminor
    apply xiSquaredEulerAllOrbitChargeDensitiesVanish_iff_riemannHypothesis.1
    intro q
    by_contra hcharge
    have hoff : (q.1 : ℂ).re ≠ 1 / 2 :=
      (xiSquaredEulerApertureOrbitChargeDensity_eq_zero_iff q).not.1 hcharge
    exact (not_lt_of_ge (hminor {q}))
      (xiSquaredEulerAperture_singleOrbitCentralMinor_neg_of_ne_half q hoff)
  · intro hRH S
    have hcharge : xiSquaredEulerFiniteApertureBoundaryCharge S = 0 := by
      unfold xiSquaredEulerFiniteApertureBoundaryCharge
      have hsum :
          (∑ q ∈ S, xiSquaredEulerApertureOrbitChargeDensity q) = 0 := by
        apply Finset.sum_eq_zero
        intro q _hq
        exact xiSquaredEulerAllOrbitChargeDensitiesVanish_iff_riemannHypothesis.2 hRH q
      rw [hsum, mul_zero]
    rw [xiSquaredEulerFiniteApertureCentralMinor_eq_hilbertGram_sub_boundaryCharge,
      hcharge, sub_zero]
    exact xiSquaredEulerFiniteApertureHilbertGram_nonneg S

/-- Simultaneous atomic, finite-packet, diagonal, global, source, and Weil realization of the
squared-Euler transverse orientation datum. -/
def XiSquaredEulerDiagonalCorrelationUniversalCertificate : Prop :=
  XiSquaredEulerAllOrbitChargeDensitiesVanish ∧
  XiSquaredEulerAllFinitePacketBoundaryChargesVanish ∧
  XiSquaredEulerAllFiniteCentralMinorsNonnegative ∧
  XiSquaredEulerApertureOrbitwiseBoundedCharge ∧
  XiSquaredEulerApertureChargeDominated ∧
  XiSquaredEulerApertureIntChargeDominated ∧
  PrimeArchSourceTraceHankelIntNonnegative ∧
  (∀ F : ℂ → ℂ, XiWeilSquareSummable F →
    0 ≤ (xiWeilPolarization F F).re)

/-- **Xi squared-Euler diagonal-correlation universality law.** Atomic transverse-charge
vanishing is equivalent to simultaneous realization in eight atom, packet, diagonal, all-degree,
source, and Weil charts. -/
theorem xiSquaredEulerAllOrbitChargeDensitiesVanish_iff_universalCertificate :
    XiSquaredEulerAllOrbitChargeDensitiesVanish ↔
      XiSquaredEulerDiagonalCorrelationUniversalCertificate := by
  constructor
  · intro hcharge
    have hRH : RiemannHypothesis :=
      xiSquaredEulerAllOrbitChargeDensitiesVanish_iff_riemannHypothesis.1 hcharge
    have hint : XiSquaredEulerApertureIntChargeDominated :=
      xiSquaredEulerApertureIntChargeDominated_iff_riemannHypothesis.2 hRH
    exact ⟨
      hcharge,
      xiSquaredEulerAllFinitePacketBoundaryChargesVanish_iff_riemannHypothesis.2 hRH,
      xiSquaredEulerAllFiniteCentralMinorsNonnegative_iff_riemannHypothesis.2 hRH,
      xiSquaredEulerApertureOrbitwiseBoundedCharge_iff_riemannHypothesis.2 hRH,
      xiSquaredEulerApertureChargeDominated_iff_riemannHypothesis.2 hRH,
      hint,
      xiSquaredEulerApertureIntChargeDominated_iff_primeArchSourceTraceHankelIntNonnegative.1
        hint,
      riemannHypothesis_iff_xiWeilPolarization_nonneg.1 hRH⟩
  · intro hcertificate
    exact hcertificate.1

/-- Simultaneous explicit failure witnesses for atomic charge, finite packets, diagonal control,
all-degree domination, the prime--Gamma source cone, and the complete Weil cone. -/
def XiSquaredEulerDiagonalCorrelationFailureUniversalCertificate : Prop :=
  (∃ q : XiZeroCopy,
    0 < xiSquaredEulerApertureOrbitChargeDensity q ∧
    0 < xiSquaredEulerFiniteApertureBoundaryCharge {q} ∧
    xiSquaredEulerFiniteApertureCentralMinor {q} < 0 ∧
    ¬ ∃ K : ℝ, ∀ p : Polynomial ℝ,
      xiSquaredEulerApertureTransverseTerm p q ≤
        K * xiSquaredEulerApertureHilbertTerm p q) ∧
  (∃ p : Polynomial ℝ,
    xiSquaredEulerApertureHilbertEnergy p <
      xiSquaredEulerApertureTransverseEnergy p) ∧
  (∃ p : Polynomial ℤ,
    xiSquaredEulerApertureHilbertEnergy (p.map (Int.castRingHom ℝ)) <
      xiSquaredEulerApertureTransverseEnergy (p.map (Int.castRingHom ℝ))) ∧
  (∃ p : Polynomial ℤ,
    (primeArchSourceTraceHankel (p.map (Int.castRingHom ℝ))).re < 0) ∧
  (∃ F : ℂ → ℂ, XiWeilSquareSummable F ∧
    (xiWeilPolarization F F).re < 0)

/-- **Complementary squared-Euler diagonal-correlation failure law.** Failure of RH is
equivalent to simultaneous atomic, packet, minor, diagonal, all-degree, source, and Weil
witnesses. -/
theorem not_riemannHypothesis_iff_squaredEulerDiagonalCorrelationFailureUniversalCertificate :
    ¬RiemannHypothesis ↔
      XiSquaredEulerDiagonalCorrelationFailureUniversalCertificate := by
  classical
  constructor
  · intro hnotRH
    have hnotPositive :
        ¬ ∀ q : XiZeroCopy, (0 : ℂ) ≤ xiZeroCopyReciprocalSquare q := by
      intro hpositive
      exact hnotRH
        (riemannHypothesis_iff_forall_xiZeroCopyReciprocalSquare_nonnegative.2 hpositive)
    push Not at hnotPositive
    obtain ⟨q, hq⟩ := hnotPositive
    have hoff : (q.1 : ℂ).re ≠ 1 / 2 := by
      intro hline
      apply hq
      have him : (xiZeroCopyReciprocalSquare q).im = 0 := by
        rw [xiZeroCopyReciprocalSquare_eq]
        exact (xiCentralReciprocalSquare_im_eq_zero_iff q.1).2 hline
      exact Complex.nonneg_iff.2
        ⟨(xiZeroCopyReciprocalSquare_re_pos q).le, him.symm⟩
    have hatom : 0 < xiSquaredEulerApertureOrbitChargeDensity q :=
      xiSquaredEulerApertureOrbitChargeDensity_pos_of_ne_half q hoff
    have hpacket : 0 < xiSquaredEulerFiniteApertureBoundaryCharge {q} := by
      simpa [xiSquaredEulerFiniteApertureBoundaryCharge,
        xiSquaredEulerFiniteApertureCentralA,
        xiSquaredEulerApertureOrbitMass] using
        mul_pos (xiZeroCopyReciprocalSquare_re_pos q) hatom
    have hminor : xiSquaredEulerFiniteApertureCentralMinor {q} < 0 :=
      xiSquaredEulerAperture_singleOrbitCentralMinor_neg_of_ne_half q hoff
    have hdiagonal :=
      not_exists_xiSquaredEulerAperture_termwise_bound_of_ne_half q hoff
    have hnotReal : ¬XiSquaredEulerApertureChargeDominated := by
      intro hdom
      exact hnotRH
        (xiSquaredEulerApertureChargeDominated_iff_riemannHypothesis.1 hdom)
    rw [XiSquaredEulerApertureChargeDominated] at hnotReal
    push Not at hnotReal
    have hnotInt : ¬XiSquaredEulerApertureIntChargeDominated := by
      intro hdom
      exact hnotRH
        (xiSquaredEulerApertureIntChargeDominated_iff_riemannHypothesis.1 hdom)
    rw [XiSquaredEulerApertureIntChargeDominated] at hnotInt
    push Not at hnotInt
    have hnotSource : ¬PrimeArchSourceTraceHankelIntNonnegative := by
      intro hsource
      exact hnotRH (riemannHypothesis_of_primeArchSourceTraceHankelIntNonnegative hsource)
    rw [PrimeArchSourceTraceHankelIntNonnegative] at hnotSource
    push Not at hnotSource
    have hnotWeil : ¬(∀ F : ℂ → ℂ, XiWeilSquareSummable F →
        0 ≤ (xiWeilPolarization F F).re) := by
      intro hweil
      exact hnotRH (riemannHypothesis_iff_xiWeilPolarization_nonneg.2 hweil)
    push Not at hnotWeil
    exact ⟨⟨q, hatom, hpacket, hminor, hdiagonal⟩,
      hnotReal, hnotInt, hnotSource, hnotWeil⟩
  · rintro ⟨⟨q, hatom, _hpacket, _hminor, _hdiagonal⟩, _hreal, _hint,
      _hsource, _hweil⟩ hRH
    have hzero :=
      xiSquaredEulerAllOrbitChargeDensitiesVanish_iff_riemannHypothesis.2 hRH q
    exact (ne_of_gt hatom) hzero

end

end RHTower
