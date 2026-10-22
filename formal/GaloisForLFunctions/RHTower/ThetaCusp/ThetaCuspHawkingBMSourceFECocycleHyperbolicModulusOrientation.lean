import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSourceFERealCocycleReflectionOrbitExtinction
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingSharedWardEnergySquare

/-!
# Hyperbolic modulus orientation of the literal BM source-FE cocycle

The literal nonlinear Birmingham--Mokhtari source determines an anti-linear functional-equation
cocycle.  Existing results classified its phase: it is real exactly on the critical wall.  This
module proves the missing positive orientation.  Its squared modulus is greater than, equal to, or
less than one exactly on the left half-strip, critical wall, or right half-strip.

The mechanism is coefficient-faithful.  For the exact quadratic Einstein carrier
`P(s) = (1+s/2)(s/2)^(2 : ℕ)`, reflection changes both positive norm factors in the same direction:

`|1-s|^(2 : ℕ) - |s|^(2 : ℕ) = 1-2 Re(s)` and
`|3-s|^(2 : ℕ) - |s+2|^(2 : ℕ) = 5(1-2 Re(s))`.

There is therefore no cross-factor cancellation.  Off the wall, the reflection-invariant helicity
coefficient cancels from the exact source-cocycle norm ratio.  On the wall the source vanishes and
the canonical cocycle value is one.  Functional-equation reflection makes the two gains reciprocal.

The unit-gain locus is pointwise identical to HB optical darkness, Deninger Ward cancellation,
FZZ-P information equilibrium, every PW-B partner balance, and RBH multiplicity-leading balance.
Universal unit gain is exactly RH.  This is an exact source-native receiver and orientation law; it
does not assert the still-missing physical Ward mechanism forcing unit gain.

`[NEW] [PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Exact squared modulus of the unit-source quadratic Einstein carrier polynomial. -/
theorem normSq_hbXiPeierlsUnitSourceCarrierPolynomial (s : ℂ) :
    Complex.normSq (hbXiPeierlsUnitSourceCarrierPolynomial s) =
      (((s.re + 2) ^ (2 : ℕ) + s.im ^ (2 : ℕ)) *
        (s.re ^ (2 : ℕ) + s.im ^ (2 : ℕ)) ^ (2 : ℕ)) / 64 := by
  simp [hbXiPeierlsUnitSourceCarrierPolynomial, Complex.normSq_apply,
    pow_two, Complex.mul_re, Complex.mul_im]
  ring

/-- In the open strip, the reflected carrier has larger squared modulus exactly on the left of
the critical wall. -/
theorem normSq_hbXiPeierlsUnitSourceCarrierPolynomial_lt_reflect_iff
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    Complex.normSq (hbXiPeierlsUnitSourceCarrierPolynomial s) <
        Complex.normSq (hbXiPeierlsUnitSourceCarrierPolynomial (1 - s)) ↔
      s.re < 1 / 2 := by
  rw [normSq_hbXiPeierlsUnitSourceCarrierPolynomial,
    normSq_hbXiPeierlsUnitSourceCarrierPolynomial]
  simp only [sub_re, one_re, sub_im, one_im, zero_sub]
  constructor
  · intro h
    by_contra hn
    have hx : 1 / 2 ≤ s.re := le_of_not_gt hn
    have ha :
        (1 - s.re) ^ (2 : ℕ) + (-s.im) ^ (2 : ℕ) ≤ s.re ^ (2 : ℕ) + s.im ^ (2 : ℕ) := by
      nlinarith
    have hb :
        (3 - s.re) ^ (2 : ℕ) + (-s.im) ^ (2 : ℕ) ≤ (s.re + 2) ^ (2 : ℕ) + s.im ^ (2 : ℕ) := by
      nlinarith
    have ha0 : 0 ≤ (1 - s.re) ^ (2 : ℕ) + (-s.im) ^ (2 : ℕ) := by positivity
    have ha20 : 0 ≤ ((1 - s.re) ^ (2 : ℕ) + (-s.im) ^ (2 : ℕ)) ^ (2 : ℕ) := sq_nonneg _
    have hb0 : 0 ≤ (s.re + 2) ^ (2 : ℕ) + s.im ^ (2 : ℕ) := by positivity
    have ha2 :
        ((1 - s.re) ^ (2 : ℕ) + (-s.im) ^ (2 : ℕ)) ^ (2 : ℕ) ≤
          (s.re ^ (2 : ℕ) + s.im ^ (2 : ℕ)) ^ (2 : ℕ) := by
      nlinarith [sq_nonneg ((s.re ^ (2 : ℕ) + s.im ^ (2 : ℕ)) -
        ((1 - s.re) ^ (2 : ℕ) + (-s.im) ^ (2 : ℕ)))]
    have hprod :
        ((3 - s.re) ^ (2 : ℕ) + (-s.im) ^ (2 : ℕ)) *
            ((1 - s.re) ^ (2 : ℕ) + (-s.im) ^ (2 : ℕ)) ^ (2 : ℕ) ≤
          ((s.re + 2) ^ (2 : ℕ) + s.im ^ (2 : ℕ)) *
            (s.re ^ (2 : ℕ) + s.im ^ (2 : ℕ)) ^ (2 : ℕ) := by
      exact mul_le_mul hb ha2 ha20 hb0
    nlinarith
  · intro hx
    let a : ℝ := s.re ^ (2 : ℕ) + s.im ^ (2 : ℕ)
    let ar : ℝ := (1 - s.re) ^ (2 : ℕ) + (-s.im) ^ (2 : ℕ)
    let b : ℝ := (s.re + 2) ^ (2 : ℕ) + s.im ^ (2 : ℕ)
    let br : ℝ := (3 - s.re) ^ (2 : ℕ) + (-s.im) ^ (2 : ℕ)
    have ha0 : 0 < a := by
      dsimp [a]
      nlinarith [sq_nonneg s.im]
    have hb0 : 0 < b := by
      dsimp [b]
      nlinarith [sq_nonneg s.im]
    have har : a < ar := by
      dsimp [a, ar]
      nlinarith
    have hbr : b < br := by
      dsimp [b, br]
      nlinarith
    have har0 : 0 < ar := lt_trans ha0 har
    have ha2 : a ^ (2 : ℕ) < ar ^ (2 : ℕ) := by
      nlinarith [mul_pos (sub_pos.mpr har) (add_pos_of_pos_of_nonneg ha0 (le_of_lt har0))]
    have hprod : b * a ^ (2 : ℕ) < br * ar ^ (2 : ℕ) := by
      have h1p : 0 < (br - b) * ar ^ (2 : ℕ) :=
        mul_pos (sub_pos.mpr hbr) (sq_pos_of_pos har0)
      have h2p : 0 < b * (ar ^ (2 : ℕ) - a ^ (2 : ℕ)) :=
        mul_pos hb0 (sub_pos.mpr ha2)
      nlinarith
    dsimp [a, ar, b, br] at hprod
    nlinarith

/-- In the open strip, the reflected carrier has smaller squared modulus exactly on the right of
the critical wall. -/
theorem normSq_hbXiPeierlsUnitSourceCarrierPolynomial_reflect_lt_iff
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    Complex.normSq (hbXiPeierlsUnitSourceCarrierPolynomial (1 - s)) <
        Complex.normSq (hbXiPeierlsUnitSourceCarrierPolynomial s) ↔
      1 / 2 < s.re := by
  have h0' : 0 < (1 - s).re := by simp; linarith
  have h1' : (1 - s).re < 1 := by simp; linarith
  have h := normSq_hbXiPeierlsUnitSourceCarrierPolynomial_lt_reflect_iff
    (s := 1 - s) h0' h1'
  rw [show 1 - (1 - s) = s by ring] at h
  simp only [sub_re, one_re] at h
  constructor
  · intro hlt
    have := h.mp hlt
    linarith
  · intro hx
    apply h.mpr
    linarith

/-- Equality of reflected and unreflected carrier norms has no accidental open-strip solutions:
it is exactly the critical wall. -/
theorem normSq_hbXiPeierlsUnitSourceCarrierPolynomial_reflect_eq_iff
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    Complex.normSq (hbXiPeierlsUnitSourceCarrierPolynomial (1 - s)) =
        Complex.normSq (hbXiPeierlsUnitSourceCarrierPolynomial s) ↔
      s.re = 1 / 2 := by
  constructor
  · intro heq
    rcases lt_trichotomy s.re (1 / 2) with hlt | heqre | hgt
    · have hstrict :=
        (normSq_hbXiPeierlsUnitSourceCarrierPolynomial_lt_reflect_iff h0 h1).mpr hlt
      exact False.elim (ne_of_lt hstrict heq.symm)
    · exact heqre
    · have hstrict :=
        (normSq_hbXiPeierlsUnitSourceCarrierPolynomial_reflect_lt_iff h0 h1).mpr hgt
      exact False.elim (ne_of_lt hstrict heq)
  · intro hre
    rw [normSq_hbXiPeierlsUnitSourceCarrierPolynomial,
      normSq_hbXiPeierlsUnitSourceCarrierPolynomial]
    simp only [sub_re, one_re, sub_im, one_im, zero_sub]
    rw [hre]
    ring

/-- The literal unit source norm factors into helicity mixing and the exact Einstein carrier. -/
theorem normSq_d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_carrier
    (q : XiZeroCopy) :
    Complex.normSq
        (d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q) =
      Complex.normSq
          (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q) *
        Complex.normSq
          (hbXiPeierlsUnitSourceCarrierPolynomial (q.1 : ℂ)) := by
  rw [d4BMXiSecondHarmonicPolarizedSourceAmplitude,
    Complex.normSq_mul,
    d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_eq]
  simp only [one_pow, one_mul]
  rfl

/-- The reflected literal unit source has the same helicity norm and the reflected exact Einstein
carrier norm. -/
theorem normSq_d4BMXiSecondHarmonicPolarizedSourceAmplitude_reflect_eq_carrier
    (q : XiZeroCopy) :
    Complex.normSq
        (d4BMXiSecondHarmonicPolarizedSourceAmplitude 1
          (xiZeroCopyReflectEquiv q)) =
      Complex.normSq
          (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q) *
        Complex.normSq
          (hbXiPeierlsUnitSourceCarrierPolynomial (1 - (q.1 : ℂ))) := by
  have href : ((xiZeroCopyReflectEquiv q).1 : ℂ) = 1 - (q.1 : ℂ) :=
    xiZeroReflectEquiv_apply q.1
  rw [d4BMXiSecondHarmonicPolarizedSourceAmplitude,
    Complex.normSq_mul,
    d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_reflect,
    d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_eq,
    href]
  simp only [one_pow, one_mul]
  rfl

/-- Off the wall, exact source transport makes the cocycle gain the reflected/unreflected
Einstein-carrier norm ratio. -/
theorem normSq_hbXiPeierlsUnitSourceFECocycle_eq_carrier_ratio_of_tilt
    (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    Complex.normSq (hbXiPeierlsUnitSourceFECocycle q) =
      Complex.normSq
          (hbXiPeierlsUnitSourceCarrierPolynomial (1 - (q.1 : ℂ))) /
        Complex.normSq
          (hbXiPeierlsUnitSourceCarrierPolynomial (q.1 : ℂ)) := by
  have hsource :
      d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q ≠ 0 :=
    (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero q).not.mpr
      htilt
  have hstar :
      Complex.normSq ((starRingEnd ℂ)
          (d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q)) =
        Complex.normSq (d4BMXiSecondHarmonicPolarizedSourceAmplitude 1 q) := by
    simp [Complex.normSq_apply]
  rw [hbXiPeierlsUnitSourceFECocycle, if_neg hsource,
    Complex.normSq_div,
    normSq_d4BMXiSecondHarmonicPolarizedSourceAmplitude_reflect_eq_carrier,
    hstar, normSq_d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_carrier]
  have hmix :
      Complex.normSq (d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient q) ≠ 0 :=
    mt Complex.normSq_eq_zero.mp
      ((d4ThetaTeukolskyOrthogonalHelicityMixingCoefficient_eq_zero_iff q).not.mpr
        htilt)
  field_simp

/-- The exact unit-source Einstein carrier never vanishes at an actual Xi divisor copy. -/
theorem hbXiPeierlsUnitSourceCarrierPolynomial_xi_ne_zero (q : XiZeroCopy) :
    hbXiPeierlsUnitSourceCarrierPolynomial (q.1 : ℂ) ≠ 0 := by
  have hcarrier :=
    d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_ne_zero one_ne_zero q
  rw [d4ThetaHawkingSelfDualQuadraticCarrierCoefficient_xi_eq] at hcarrier
  simpa only [one_pow, one_mul, hbXiPeierlsUnitSourceCarrierPolynomial] using hcarrier

/-- The literal nonlinear source-FE cocycle expands exactly on the left half-strip. -/
theorem one_lt_normSq_hbXiPeierlsUnitSourceFECocycle_iff (q : XiZeroCopy) :
    1 < Complex.normSq (hbXiPeierlsUnitSourceFECocycle q) ↔
      (q.1 : ℂ).re < 1 / 2 := by
  by_cases hline : (q.1 : ℂ).re = 1 / 2
  · have hsource :=
      (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero q).mpr hline
    simp [hbXiPeierlsUnitSourceFECocycle, hsource, hline]
  · rw [normSq_hbXiPeierlsUnitSourceFECocycle_eq_carrier_ratio_of_tilt q hline,
      one_lt_div
        (Complex.normSq_pos.mpr (hbXiPeierlsUnitSourceCarrierPolynomial_xi_ne_zero q))]
    exact normSq_hbXiPeierlsUnitSourceCarrierPolynomial_lt_reflect_iff
      (xi_divisor_support_re_mem_open_unit q.1).1
      (xi_divisor_support_re_mem_open_unit q.1).2

/-- The literal nonlinear source-FE cocycle contracts exactly on the right half-strip. -/
theorem normSq_hbXiPeierlsUnitSourceFECocycle_lt_one_iff (q : XiZeroCopy) :
    Complex.normSq (hbXiPeierlsUnitSourceFECocycle q) < 1 ↔
      1 / 2 < (q.1 : ℂ).re := by
  by_cases hline : (q.1 : ℂ).re = 1 / 2
  · have hsource :=
      (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero q).mpr hline
    simp [hbXiPeierlsUnitSourceFECocycle, hsource, hline]
  · rw [normSq_hbXiPeierlsUnitSourceFECocycle_eq_carrier_ratio_of_tilt q hline,
      div_lt_one
        (Complex.normSq_pos.mpr (hbXiPeierlsUnitSourceCarrierPolynomial_xi_ne_zero q))]
    exact normSq_hbXiPeierlsUnitSourceCarrierPolynomial_reflect_lt_iff
      (xi_divisor_support_re_mem_open_unit q.1).1
      (xi_divisor_support_re_mem_open_unit q.1).2

/-- Unit cocycle gain is exactly critical-line placement. -/
theorem normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff (q : XiZeroCopy) :
    Complex.normSq (hbXiPeierlsUnitSourceFECocycle q) = 1 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  by_cases hline : (q.1 : ℂ).re = 1 / 2
  · have hsource :=
      (d4BMXiSecondHarmonicPolarizedSourceAmplitude_eq_zero_iff one_ne_zero q).mpr hline
    simp [hbXiPeierlsUnitSourceFECocycle, hsource, hline]
  · rw [normSq_hbXiPeierlsUnitSourceFECocycle_eq_carrier_ratio_of_tilt q hline,
      div_eq_one_iff_eq
        (ne_of_gt
          (Complex.normSq_pos.mpr (hbXiPeierlsUnitSourceCarrierPolynomial_xi_ne_zero q))),
      normSq_hbXiPeierlsUnitSourceCarrierPolynomial_reflect_eq_iff
        (xi_divisor_support_re_mem_open_unit q.1).1
        (xi_divisor_support_re_mem_open_unit q.1).2]

/-- Universal unit gain of the literal source-FE cocycle is exactly RH. -/
theorem forall_normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff_rh :
    (∀ q : XiZeroCopy,
      Complex.normSq (hbXiPeierlsUnitSourceFECocycle q) = 1) ↔
      RiemannHypothesis := by
  constructor
  · intro h
    apply forall_hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff_rh.mp
    intro q
    apply (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff q).mpr
    exact (normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff q).mp (h q)
  · intro hRH q
    apply (normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff q).mpr
    have hfixed :=
      forall_hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff_rh.mpr hRH q
    exact (hbXiPeierlsUnitSourceFEBasisTransport_fixedPairing_iff q).mp hfixed

/-- Functional-equation reflection gives reciprocal source gains without division. -/
theorem normSq_hbXiPeierlsUnitSourceFECocycle_reflect_mul (q : XiZeroCopy) :
    Complex.normSq
          (hbXiPeierlsUnitSourceFECocycle (xiZeroCopyReflectEquiv q)) *
        Complex.normSq (hbXiPeierlsUnitSourceFECocycle q) = 1 := by
  have h := congrArg Complex.normSq
    (hbXiPeierlsUnitSourceFECocycle_involutive q)
  rw [Complex.normSq_mul] at h
  simpa [Complex.normSq_apply] using h

/-- Unit source gain and HB canonical orbit optical darkness are the same pointwise law. -/
theorem normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff_opticalPower_zero
    (n : ℕ) (q : XiZeroCopy) :
    Complex.normSq (hbXiPeierlsUnitSourceFECocycle q) = 1 ↔
      hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower n q = 0 := by
  rw [normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff,
    hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower_eq_zero_iff_line]

/-- Unit source gain and the common Deninger Ward cancellation are pointwise identical. -/
theorem normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff_sharedWardCharge_zero
    (n : ℕ) (q : XiZeroCopy) :
    Complex.normSq (hbXiPeierlsUnitSourceFECocycle q) = 1 ↔
      fzzCigarParityDeningerReflectGaugeWardCharge q = 0 := by
  rw [normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff_opticalPower_zero n q,
    hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower_eq_zero_iff_sharedWardCharge]

/-- Unit source gain and FZZ-P information equilibrium are pointwise identical. -/
theorem normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff_informationForce_zero
    (n : ℕ) (q : XiZeroCopy) :
    Complex.normSq (hbXiPeierlsUnitSourceFECocycle q) = 1 ↔
      fzzCigarParityReflectedFermiInformationForce
          (deningerDivisorThetaEigen q).re = 0 := by
  rw [normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff_opticalPower_zero n q,
    hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower_eq_zero_iff_informationForce]

/-- Unit source gain and PW-B partner balance are pointwise identical at every grade. -/
theorem normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff_pwBalance_zero
    (n : ℕ) (q : XiZeroCopy) (k : ℕ) :
    Complex.normSq (hbXiPeierlsUnitSourceFECocycle q) = 1 ↔
      schwarzschildParikhWilczekBorelPartnerRealImbalance
          (deningerDivisorThetaEigen q) k = 0 := by
  rw [normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff_opticalPower_zero n q,
    hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower_eq_zero_iff_pwBorelPartnerBalance]

/-- On the canonical divisor copy, unit source gain and RBH multiplicity-leading balance are
identical. -/
theorem normSq_hbXiPeierlsUnitSourceFECocycle_firstCopy_eq_one_iff_rbhBalance_zero
    (n : ℕ) (rho : XiDivisorSupport) :
    Complex.normSq
        (hbXiPeierlsUnitSourceFECocycle
          (reflectedBiHeatFirstDivisorCopy rho)) = 1 ↔
      reflectedBiHeatMultiplicityLeadingJetNormImbalance rho = 0 := by
  rw [normSq_hbXiPeierlsUnitSourceFECocycle_eq_one_iff_opticalPower_zero n,
    hbXiPeierlsFESchwarzCanonicalOrbitOpticalPower_eq_zero_iff_rbhBalance]

end

end RHTower
