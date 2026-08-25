import GaloisForLFunctions.RHTower.ThetaCuspHawkingTeukolskyThermalDealiasingEndpoint

/-!
# Single-sector Teukolsky frequency-support obstruction

Finite stationary nonlinearities cannot convert one Birmingham--Mokhtari QNM and its real-field
partner into the opposite QNM branch in the same Xi sector.
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Normal form of the positive Birmingham--Mokhtari QNM frequency. -/
def d4QNMPlusFrequencyNormalForm (x y decay : ℝ) : ℂ :=
  (x : ℂ) + Complex.I * ((y - decay : ℝ) : ℂ)

/-- Normal form of the negative Birmingham--Mokhtari QNM frequency. -/
def d4QNMMinusFrequencyNormalForm (x y decay : ℝ) : ℂ :=
  (-x : ℂ) + Complex.I * ((-y - decay : ℝ) : ℂ)

/-- Frequency carried by the conjugate term required for a real perturbation. -/
def d4QNMRealFieldPartnerFrequency (omega : ℂ) : ℂ := -star omega

/-- Fourier frequency of a monomial with positive-mode and real-partner multiplicities. -/
def d4SingleSectorMonomialFrequency (r s : ℕ) (omega : ℂ) : ℂ :=
  (r : ℂ) * omega + (s : ℂ) * d4QNMRealFieldPartnerFrequency omega

lemma d4QNMPlusFrequencyNormalForm_re (x y decay : ℝ) :
    (d4QNMPlusFrequencyNormalForm x y decay).re = x := by
  simp [d4QNMPlusFrequencyNormalForm]

lemma d4QNMPlusFrequencyNormalForm_im (x y decay : ℝ) :
    (d4QNMPlusFrequencyNormalForm x y decay).im = y - decay := by
  simp [d4QNMPlusFrequencyNormalForm]

lemma d4QNMRealFieldPartnerFrequency_re (x y decay : ℝ) :
    (d4QNMRealFieldPartnerFrequency
      (d4QNMPlusFrequencyNormalForm x y decay)).re = -x := by
  simp [d4QNMRealFieldPartnerFrequency, d4QNMPlusFrequencyNormalForm]

lemma d4QNMRealFieldPartnerFrequency_im (x y decay : ℝ) :
    (d4QNMRealFieldPartnerFrequency
      (d4QNMPlusFrequencyNormalForm x y decay)).im = y - decay := by
  simp [d4QNMRealFieldPartnerFrequency, d4QNMPlusFrequencyNormalForm]

/-- Exact frequency-matching classification for same-sector branch conversion. -/
theorem d4SingleSectorMonomialFrequency_eq_minus_iff
    (x y decay : ℝ) (hx : x ≠ 0) (r s : ℕ) :
    d4SingleSectorMonomialFrequency r s (d4QNMPlusFrequencyNormalForm x y decay) =
        d4QNMMinusFrequencyNormalForm x y decay ↔
      s = r + 1 ∧ ((r : ℝ) + 1) * y = (r : ℝ) * decay := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp [d4SingleSectorMonomialFrequency, d4QNMPlusFrequencyNormalForm,
      d4QNMMinusFrequencyNormalForm, d4QNMRealFieldPartnerFrequency,
      Complex.mul_re, Complex.mul_im] at hre him
    have hrsR : (s : ℝ) = (r : ℝ) + 1 := by
      apply (mul_left_cancel₀ hx)
      nlinarith [hre]
    have hrs : s = r + 1 := by
      exact_mod_cast hrsR
    subst s
    constructor
    · rfl
    · norm_num at him ⊢
      nlinarith [him]
  · rintro ⟨rfl, hy⟩
    apply Complex.ext
    · simp [d4SingleSectorMonomialFrequency, d4QNMPlusFrequencyNormalForm,
        d4QNMMinusFrequencyNormalForm, d4QNMRealFieldPartnerFrequency,
        Complex.mul_re]
      ring
    · simp [d4SingleSectorMonomialFrequency, d4QNMPlusFrequencyNormalForm,
        d4QNMMinusFrequencyNormalForm, d4QNMRealFieldPartnerFrequency,
        Complex.mul_im] at hy ⊢
      nlinarith [hy]

/-- Critical-strip damping excludes every finite same-sector branch-converting monomial. -/
theorem d4SingleSectorMonomialFrequency_ne_minus_of_strip
    (x y decay : ℝ) (hx : x ≠ 0) (hy0 : 0 < y) (hyHalf : y < 1 / 2)
    (hDecay : 3 / 2 ≤ decay) (r s : ℕ) :
    d4SingleSectorMonomialFrequency r s (d4QNMPlusFrequencyNormalForm x y decay) ≠
      d4QNMMinusFrequencyNormalForm x y decay := by
  intro h
  obtain ⟨_, hy⟩ :=
    (d4SingleSectorMonomialFrequency_eq_minus_iff x y decay hx r s).mp h
  by_cases hr : r = 0
  · subst r
    norm_num at hy
    linarith
  · have hrOne : (1 : ℝ) ≤ r := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hr)
    have hrNonneg : (0 : ℝ) ≤ r := by positivity
    have hleft : (3 / 2 : ℝ) * r ≤ decay * r :=
      mul_le_mul_of_nonneg_right hDecay hrNonneg
    have hright : ((r : ℝ) + 1) * y < ((r : ℝ) + 1) * (1 / 2) :=
      mul_lt_mul_of_pos_left hyHalf (by linarith)
    nlinarith [hy, hleft, hright]

lemma thetaCuspHawkingTopologicalBlackHoleQNMPlus_eq_normalForm
    (n : ℕ) (z : ℂ) :
    thetaCuspHawkingTopologicalBlackHoleQNMPlus n z =
      d4QNMPlusFrequencyNormalForm
        (thetaCuspHawkingTopologicalBlackHoleAngularMomentum z).re
        (thetaCuspHawkingTopologicalBlackHoleAngularMomentum z).im
        (thetaCuspHawkingTopologicalBlackHoleConformalDecay n) := by
  apply Complex.ext <;>
    simp [thetaCuspHawkingTopologicalBlackHoleQNMPlus,
      d4QNMPlusFrequencyNormalForm]

lemma thetaCuspHawkingTopologicalBlackHoleQNMMinus_eq_normalForm
    (n : ℕ) (z : ℂ) :
    thetaCuspHawkingTopologicalBlackHoleQNMMinus n z =
      d4QNMMinusFrequencyNormalForm
        (thetaCuspHawkingTopologicalBlackHoleAngularMomentum z).re
        (thetaCuspHawkingTopologicalBlackHoleAngularMomentum z).im
        (thetaCuspHawkingTopologicalBlackHoleConformalDecay n) := by
  apply Complex.ext <;>
    simp [thetaCuspHawkingTopologicalBlackHoleQNMMinus,
      d4QNMMinusFrequencyNormalForm]

/-- Same-sector Fourier support generated by one positive QNM and its real-field partner. -/
def d4BMSingleSectorMonomialOutputFrequency (n r s : ℕ) (z : ℂ) : ℂ :=
  d4SingleSectorMonomialFrequency r s
    (thetaCuspHawkingTopologicalBlackHoleQNMPlus n z)

/-- No finite stationary single-sector vertex reaches the opposite branch at an Xi divisor. -/
theorem d4BMSingleSectorMonomialOutputFrequency_ne_qnmMinus_xi
    (n r s : ℕ) (q : XiZeroCopy) :
    d4BMSingleSectorMonomialOutputFrequency n r s (xiSpectralPoint q) ≠
      thetaCuspHawkingTopologicalBlackHoleQNMMinus n (xiSpectralPoint q) := by
  let xi := thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q)
  let decay := thetaCuspHawkingTopologicalBlackHoleConformalDecay n
  have hx : xi.re ≠ 0 := by
    dsimp [xi]
    simpa [thetaCuspHawkingTopologicalBlackHoleAngularMomentum] using
      thetaCuspHawkingHypergeometricXiSpectralPoint_re_ne_zero q
  have hy0 : 0 < xi.im := by
    exact thetaCuspHawkingBMContinuedAngularMomentum_xi_im_pos q
  have hyHalf : xi.im < 1 / 2 := by
    rw [show xi.im = (1 - (q.1 : ℂ).re) / 2 by
      exact thetaCuspHawkingBMContinuedAngularMomentum_xi_im q]
    linarith [(xi_divisor_support_re_mem_open_unit q.1).1]
  have hDecay : (3 / 2 : ℝ) ≤ decay := by
    dsimp [decay, thetaCuspHawkingTopologicalBlackHoleConformalDecay]
    have hn : (0 : ℝ) ≤ n := by positivity
    linarith
  rw [d4BMSingleSectorMonomialOutputFrequency,
    thetaCuspHawkingTopologicalBlackHoleQNMPlus_eq_normalForm,
    thetaCuspHawkingTopologicalBlackHoleQNMMinus_eq_normalForm]
  exact d4SingleSectorMonomialFrequency_ne_minus_of_strip
    xi.re xi.im decay hx hy0 hyHalf hDecay r s

/-- Two positive-branch decay frequencies cannot sum to a negative-branch decay frequency. -/
theorem d4QuadraticDecayMatch_impossible
    (y0 y1 y2 : ℝ)
    (hy00 : 0 < y0) (hy01 : y0 < 1 / 2)
    (hy10 : 0 < y1) (hy11 : y1 < 1 / 2)
    (hy20 : 0 < y2) (hy21 : y2 < 1 / 2)
    (n0 n1 n2 : ℕ) :
    (y1 - thetaCuspHawkingTopologicalBlackHoleConformalDecay n1) +
        (y2 - thetaCuspHawkingTopologicalBlackHoleConformalDecay n2) ≠
      -y0 - thetaCuspHawkingTopologicalBlackHoleConformalDecay n0 := by
  intro h
  have hY0 : 0 < y0 + y1 + y2 := by linarith
  have hYlt : y0 + y1 + y2 < 3 / 2 := by linarith
  simp only [thetaCuspHawkingTopologicalBlackHoleConformalDecay] at h
  by_cases hn : n0 ≤ n1 + n2
  · have hnR : (n0 : ℝ) ≤ n1 + n2 := by exact_mod_cast hn
    nlinarith
  · have hnNat : n1 + n2 + 1 ≤ n0 := by omega
    have hnR : (n1 : ℝ) + n2 + 1 ≤ n0 := by exact_mod_cast hnNat
    nlinarith

/-- Two positive-branch decay frequencies cannot sum to another positive-branch decay frequency. -/
theorem d4QuadraticDecayMatchPlus_impossible
    (y0 y1 y2 : ℝ)
    (hy00 : 0 < y0) (hy01 : y0 < 1 / 2)
    (hy10 : 0 < y1) (hy11 : y1 < 1 / 2)
    (hy20 : 0 < y2) (hy21 : y2 < 1 / 2)
    (n0 n1 n2 : ℕ) :
    (y1 - thetaCuspHawkingTopologicalBlackHoleConformalDecay n1) +
        (y2 - thetaCuspHawkingTopologicalBlackHoleConformalDecay n2) ≠
      y0 - thetaCuspHawkingTopologicalBlackHoleConformalDecay n0 := by
  intro h
  have hYlow : -1 / 2 < y1 + y2 - y0 := by linarith
  have hYhigh : y1 + y2 - y0 < 1 := by linarith
  simp only [thetaCuspHawkingTopologicalBlackHoleConformalDecay] at h
  by_cases hn : n0 ≤ n1 + n2
  · have hnR : (n0 : ℝ) ≤ n1 + n2 := by exact_mod_cast hn
    nlinarith
  · have hnNat : n1 + n2 + 1 ≤ n0 := by omega
    have hnR : (n1 : ℝ) + n2 + 1 ≤ n0 := by exact_mod_cast hnNat
    nlinarith

/-- Cubic decay matching forces one overtone step and four-sector critical barycenter. -/
theorem d4CubicDecayMatch_classification
    (y0 y1 y2 y3 : ℝ)
    (hy00 : 0 < y0) (hy01 : y0 < 1 / 2)
    (hy10 : 0 < y1) (hy11 : y1 < 1 / 2)
    (hy20 : 0 < y2) (hy21 : y2 < 1 / 2)
    (hy30 : 0 < y3) (hy31 : y3 < 1 / 2)
    (n0 n1 n2 n3 : ℕ)
    (hmatch :
      (y1 - thetaCuspHawkingTopologicalBlackHoleConformalDecay n1) +
          (y2 - thetaCuspHawkingTopologicalBlackHoleConformalDecay n2) +
          (y3 - thetaCuspHawkingTopologicalBlackHoleConformalDecay n3) =
        -y0 - thetaCuspHawkingTopologicalBlackHoleConformalDecay n0) :
    n0 = n1 + n2 + n3 + 1 ∧ y0 + y1 + y2 + y3 = 1 := by
  have hY0 : 0 < y0 + y1 + y2 + y3 := by linarith
  have hYlt : y0 + y1 + y2 + y3 < 2 := by linarith
  simp only [thetaCuspHawkingTopologicalBlackHoleConformalDecay] at hmatch
  have hnLow : ¬ n0 ≤ n1 + n2 + n3 := by
    intro hn
    have hnR : (n0 : ℝ) ≤ n1 + n2 + n3 := by exact_mod_cast hn
    nlinarith
  have hnHigh : ¬ n1 + n2 + n3 + 2 ≤ n0 := by
    intro hn
    have hnR : (n1 : ℝ) + n2 + n3 + 2 ≤ n0 := by exact_mod_cast hn
    nlinarith
  have hnEq : n0 = n1 + n2 + n3 + 1 := by omega
  constructor
  · exact hnEq
  · have hnEqR : (n0 : ℝ) = n1 + n2 + n3 + 1 := by exact_mod_cast hnEq
    nlinarith

/-- Either Fourier sign of a real positive-branch QNM perturbation. -/
def d4BMRealFieldChoiceFrequency (partner : Bool) (n : ℕ) (z : ℂ) : ℂ :=
  if partner then
    d4QNMRealFieldPartnerFrequency
      (thetaCuspHawkingTopologicalBlackHoleQNMPlus n z)
  else thetaCuspHawkingTopologicalBlackHoleQNMPlus n z

lemma d4BMRealFieldChoiceFrequency_im (partner : Bool) (n : ℕ) (z : ℂ) :
    (d4BMRealFieldChoiceFrequency partner n z).im =
      (thetaCuspHawkingTopologicalBlackHoleAngularMomentum z).im -
        thetaCuspHawkingTopologicalBlackHoleConformalDecay n := by
  cases partner
  · simp [d4BMRealFieldChoiceFrequency,
      thetaCuspHawkingTopologicalBlackHoleQNMPlus]
  · simp [d4BMRealFieldChoiceFrequency, d4QNMRealFieldPartnerFrequency,
      thetaCuspHawkingTopologicalBlackHoleQNMPlus]
    ring

lemma thetaCuspHawkingTopologicalBlackHoleQNMMinus_im_eq_decay
    (n : ℕ) (z : ℂ) :
    (thetaCuspHawkingTopologicalBlackHoleQNMMinus n z).im =
      -(thetaCuspHawkingTopologicalBlackHoleAngularMomentum z).im -
        thetaCuspHawkingTopologicalBlackHoleConformalDecay n := by
  simp [thetaCuspHawkingTopologicalBlackHoleQNMMinus]

private lemma d4BMXiAngularMomentum_im_lt_half (q : XiZeroCopy) :
    (thetaCuspHawkingTopologicalBlackHoleAngularMomentum
      (xiSpectralPoint q)).im < 1 / 2 := by
  rw [thetaCuspHawkingBMContinuedAngularMomentum_xi_im]
  linarith [(xi_divisor_support_re_mem_open_unit q.1).1]

/-- Quadratic Fourier support of two positive-branch real perturbations. -/
def d4BMQuadraticOutputFrequency (p1 p2 : Bool) (n1 n2 : ℕ)
    (z1 z2 : ℂ) : ℂ :=
  d4BMRealFieldChoiceFrequency p1 n1 z1 +
    d4BMRealFieldChoiceFrequency p2 n2 z2

/-- No quadratic Xi-sector input pair reaches any negative-branch Xi QNM. -/
theorem d4BMQuadraticOutputFrequency_ne_qnmMinus_xi
    (p1 p2 : Bool) (n0 n1 n2 : ℕ) (q0 q1 q2 : XiZeroCopy) :
    d4BMQuadraticOutputFrequency p1 p2 n1 n2
        (xiSpectralPoint q1) (xiSpectralPoint q2) ≠
      thetaCuspHawkingTopologicalBlackHoleQNMMinus n0 (xiSpectralPoint q0) := by
  intro h
  have him := congrArg Complex.im h
  rw [thetaCuspHawkingTopologicalBlackHoleQNMMinus_im_eq_decay] at him
  simp [d4BMQuadraticOutputFrequency, d4BMRealFieldChoiceFrequency_im] at him
  apply d4QuadraticDecayMatch_impossible
    (thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q0)).im
    (thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q1)).im
    (thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q2)).im
    (thetaCuspHawkingBMContinuedAngularMomentum_xi_im_pos q0)
    (d4BMXiAngularMomentum_im_lt_half q0)
    (thetaCuspHawkingBMContinuedAngularMomentum_xi_im_pos q1)
    (d4BMXiAngularMomentum_im_lt_half q1)
    (thetaCuspHawkingBMContinuedAngularMomentum_xi_im_pos q2)
    (d4BMXiAngularMomentum_im_lt_half q2)
    n0 n1 n2
  exact him

/-- No quadratic Xi-sector input pair reaches any positive-branch Xi QNM. -/
theorem d4BMQuadraticOutputFrequency_ne_qnmPlus_xi
    (p1 p2 : Bool) (n0 n1 n2 : ℕ) (q0 q1 q2 : XiZeroCopy) :
    d4BMQuadraticOutputFrequency p1 p2 n1 n2
        (xiSpectralPoint q1) (xiSpectralPoint q2) ≠
      thetaCuspHawkingTopologicalBlackHoleQNMPlus n0 (xiSpectralPoint q0) := by
  intro h
  have him := congrArg Complex.im h
  simp [d4BMQuadraticOutputFrequency, d4BMRealFieldChoiceFrequency_im,
    thetaCuspHawkingTopologicalBlackHoleQNMPlus] at him
  apply d4QuadraticDecayMatchPlus_impossible
    (thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q0)).im
    (thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q1)).im
    (thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q2)).im
    (thetaCuspHawkingBMContinuedAngularMomentum_xi_im_pos q0)
    (d4BMXiAngularMomentum_im_lt_half q0)
    (thetaCuspHawkingBMContinuedAngularMomentum_xi_im_pos q1)
    (d4BMXiAngularMomentum_im_lt_half q1)
    (thetaCuspHawkingBMContinuedAngularMomentum_xi_im_pos q2)
    (d4BMXiAngularMomentum_im_lt_half q2)
    n0 n1 n2
  exact him

/-- Cubic Fourier support of three positive-branch real perturbations. -/
def d4BMCubicOutputFrequency (p1 p2 p3 : Bool) (n1 n2 n3 : ℕ)
    (z1 z2 z3 : ℂ) : ℂ :=
  d4BMRealFieldChoiceFrequency p1 n1 z1 +
    d4BMRealFieldChoiceFrequency p2 n2 z2 +
    d4BMRealFieldChoiceFrequency p3 n3 z3

/-- A cubic negative-branch return requires overtone conservation and critical barycenter. -/
theorem d4BMCubicOutputFrequency_eq_qnmMinus_xi_forces_criticalBarycenter
    (p1 p2 p3 : Bool) (n0 n1 n2 n3 : ℕ) (q0 q1 q2 q3 : XiZeroCopy)
    (h : d4BMCubicOutputFrequency p1 p2 p3 n1 n2 n3
      (xiSpectralPoint q1) (xiSpectralPoint q2) (xiSpectralPoint q3) =
      thetaCuspHawkingTopologicalBlackHoleQNMMinus n0 (xiSpectralPoint q0)) :
    n0 = n1 + n2 + n3 + 1 ∧
      (q0.1 : ℂ).re + (q1.1 : ℂ).re + (q2.1 : ℂ).re + (q3.1 : ℂ).re = 2 := by
  have him := congrArg Complex.im h
  rw [thetaCuspHawkingTopologicalBlackHoleQNMMinus_im_eq_decay] at him
  simp [d4BMCubicOutputFrequency, d4BMRealFieldChoiceFrequency_im] at him
  have hc := d4CubicDecayMatch_classification
    (thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q0)).im
    (thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q1)).im
    (thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q2)).im
    (thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q3)).im
    (thetaCuspHawkingBMContinuedAngularMomentum_xi_im_pos q0)
    (d4BMXiAngularMomentum_im_lt_half q0)
    (thetaCuspHawkingBMContinuedAngularMomentum_xi_im_pos q1)
    (d4BMXiAngularMomentum_im_lt_half q1)
    (thetaCuspHawkingBMContinuedAngularMomentum_xi_im_pos q2)
    (d4BMXiAngularMomentum_im_lt_half q2)
    (thetaCuspHawkingBMContinuedAngularMomentum_xi_im_pos q3)
    (d4BMXiAngularMomentum_im_lt_half q3)
    n0 n1 n2 n3 him
  refine ⟨hc.1, ?_⟩
  rw [thetaCuspHawkingBMContinuedAngularMomentum_xi_im,
    thetaCuspHawkingBMContinuedAngularMomentum_xi_im,
    thetaCuspHawkingBMContinuedAngularMomentum_xi_im,
    thetaCuspHawkingBMContinuedAngularMomentum_xi_im] at hc
  nlinarith [hc.2]

/-- Schwarz-conjugated Xi mode is the real-field frequency partner. -/
lemma d4BMXiConjugateQNMPlus_eq_realFieldPartner
    (n : ℕ) (q : XiZeroCopy) :
    thetaCuspHawkingTopologicalBlackHoleQNMPlus n
        (xiSpectralPoint (xiZeroCopyConjEquiv q)) =
      d4QNMRealFieldPartnerFrequency
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)) := by
  rw [xiSpectralPoint_copyConj]
  simp only [thetaCuspHawkingTopologicalBlackHoleQNMPlus,
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum,
    thetaCuspHawkingTopologicalBlackHoleConformalDecay,
    d4QNMRealFieldPartnerFrequency]
  push_cast
  apply Complex.ext <;> simp <;> ring

/-- Reflected Xi pair supplies the second real-field frequency pair. -/
lemma d4BMXiReflectQNMPlus_eq_realFieldPartner
    (n : ℕ) (q : XiZeroCopy) :
    thetaCuspHawkingTopologicalBlackHoleQNMPlus n
        (xiSpectralPoint (xiZeroCopyReflectEquiv q)) =
      d4QNMRealFieldPartnerFrequency
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus n
          (xiSpectralPoint
            (xiZeroCopyReflectEquiv (xiZeroCopyConjEquiv q)))) := by
  rw [xiSpectralPoint_reflect, xiSpectralPoint_reflect,
    xiSpectralPoint_copyConj]
  simp only [thetaCuspHawkingTopologicalBlackHoleQNMPlus,
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum,
    thetaCuspHawkingTopologicalBlackHoleConformalDecay,
    d4QNMRealFieldPartnerFrequency]
  push_cast
  apply Complex.ext <;> simp <;> ring

/-- Universal frequency carried by one functional-reflection QNM pair. -/
def d4BMFunctionalReflectionMediatorFrequency (n2 n3 : ℕ) : ℂ :=
  -Complex.I * ((2 * ((n2 : ℝ) + (n3 : ℝ)) + 5 / 2 : ℝ) : ℂ)

/-- Fixed BM spectral point underlying the reflection-pair mediator tower. -/
def d4BMFunctionalReflectionMediatorSpectralPoint : ℂ :=
  -(5 / 2) * Complex.I

lemma d4BMFunctionalReflectionMediatorSpectralPoint_angularMomentum :
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum
        d4BMFunctionalReflectionMediatorSpectralPoint = -Complex.I := by
  simp [d4BMFunctionalReflectionMediatorSpectralPoint,
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum]
  ring

lemma d4BMFunctionalReflectionMediatorSpectralPoint_angularEigenvalue :
    thetaCuspHawkingTopologicalBlackHoleAngularEigenvalue
        d4BMFunctionalReflectionMediatorSpectralPoint = -(3 / 4 : ℂ) := by
  rw [thetaCuspHawkingTopologicalBlackHoleAngularEigenvalue]
  rw [d4BMFunctionalReflectionMediatorSpectralPoint_angularMomentum]
  rw [sq, neg_mul_neg, Complex.I_mul_I]
  ring

lemma d4BMFunctionalReflectionMediatorSpectralPoint_rho :
    d4ThetaTeukolskyRho d4BMFunctionalReflectionMediatorSpectralPoint = 3 := by
  unfold d4ThetaTeukolskyRho d4BMFunctionalReflectionMediatorSpectralPoint
  ring_nf
  rw [Complex.I_sq]
  norm_num

/-- Reflection-pair mediator is one fixed non-Xi BM QNM tower. -/
theorem d4BMFunctionalReflectionMediatorFrequency_eq_qnmPlus
    (n2 n3 : ℕ) :
    d4BMFunctionalReflectionMediatorFrequency n2 n3 =
      thetaCuspHawkingTopologicalBlackHoleQNMPlus (n2 + n3)
        d4BMFunctionalReflectionMediatorSpectralPoint := by
  rw [thetaCuspHawkingTopologicalBlackHoleQNMPlus,
    d4BMFunctionalReflectionMediatorSpectralPoint_angularMomentum]
  simp only [thetaCuspHawkingTopologicalBlackHoleConformalDecay,
    d4BMFunctionalReflectionMediatorFrequency]
  push_cast
  ring

/-- Mediator angular eigenvalue is outside every nonnegative horizon shell. -/
theorem d4BMFunctionalReflectionMediatorSpectralPoint_ne_nonnegAngularEigenvalue
    (Q : ℝ) (hQ : 0 ≤ Q) :
    thetaCuspHawkingTopologicalBlackHoleAngularEigenvalue
        d4BMFunctionalReflectionMediatorSpectralPoint ≠ (Q : ℂ) := by
  rw [d4BMFunctionalReflectionMediatorSpectralPoint_angularEigenvalue]
  intro h
  have hre := congrArg Complex.re h
  simp at hre
  linarith

/-- Functional-reflection pair loses all dependence on the Xi spectral point. -/
theorem d4BMXiFunctionalReflectionPair_frequency_eq_mediator
    (n2 n3 : ℕ) (q : XiZeroCopy) :
    thetaCuspHawkingTopologicalBlackHoleQNMPlus n2
          (xiSpectralPoint (xiZeroCopyConjEquiv q)) +
        thetaCuspHawkingTopologicalBlackHoleQNMPlus n3
          (xiSpectralPoint
            (xiZeroCopyReflectEquiv (xiZeroCopyConjEquiv q))) =
      d4BMFunctionalReflectionMediatorFrequency n2 n3 := by
  rw [xiSpectralPoint_copyConj, xiSpectralPoint_reflect,
    xiSpectralPoint_copyConj]
  simp only [thetaCuspHawkingTopologicalBlackHoleQNMPlus,
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum,
    thetaCuspHawkingTopologicalBlackHoleConformalDecay,
    d4BMFunctionalReflectionMediatorFrequency]
  push_cast
  ring_nf

/-- Universal mediator plus reflected QNM is the opposite-branch quartet output. -/
theorem d4BMXiFunctionalReflectionMediator_cascade
    (n1 n2 n3 : ℕ) (q : XiZeroCopy) :
    d4BMFunctionalReflectionMediatorFrequency n2 n3 +
        thetaCuspHawkingTopologicalBlackHoleQNMPlus n1
          (xiSpectralPoint (xiZeroCopyReflectEquiv q)) =
      thetaCuspHawkingTopologicalBlackHoleQNMMinus (n1 + n2 + n3 + 1)
        (xiSpectralPoint q) := by
  rw [xiSpectralPoint_reflect]
  simp only [thetaCuspHawkingTopologicalBlackHoleQNMPlus,
    thetaCuspHawkingTopologicalBlackHoleQNMMinus,
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum,
    thetaCuspHawkingTopologicalBlackHoleConformalDecay,
    d4BMFunctionalReflectionMediatorFrequency]
  push_cast
  ring_nf

/-- Reflection-pair mediator is purely damped. -/
theorem d4BMFunctionalReflectionMediatorFrequency_purelyDamped
    (n2 n3 : ℕ) :
    (d4BMFunctionalReflectionMediatorFrequency n2 n3).re = 0 ∧
      (d4BMFunctionalReflectionMediatorFrequency n2 n3).im < 0 := by
  have hn2 : (0 : ℝ) ≤ n2 := by positivity
  have hn3 : (0 : ℝ) ≤ n3 := by positivity
  constructor
  · simp [d4BMFunctionalReflectionMediatorFrequency]
  · simp [d4BMFunctionalReflectionMediatorFrequency]
    linarith

/-- Reflection-pair mediator is off every Xi-labelled BM QNM shell. -/
theorem d4BMFunctionalReflectionMediatorFrequency_ne_xiQNM
    (n0 n2 n3 : ℕ) (q q0 : XiZeroCopy) :
    d4BMFunctionalReflectionMediatorFrequency n2 n3 ≠
        thetaCuspHawkingTopologicalBlackHoleQNMPlus n0 (xiSpectralPoint q0) ∧
      d4BMFunctionalReflectionMediatorFrequency n2 n3 ≠
        thetaCuspHawkingTopologicalBlackHoleQNMMinus n0 (xiSpectralPoint q0) := by
  constructor
  · rw [← d4BMXiFunctionalReflectionPair_frequency_eq_mediator n2 n3 q]
    simpa [d4BMQuadraticOutputFrequency, d4BMRealFieldChoiceFrequency] using
      (d4BMQuadraticOutputFrequency_ne_qnmPlus_xi false false n0 n2 n3 q0
        (xiZeroCopyConjEquiv q)
        (xiZeroCopyReflectEquiv (xiZeroCopyConjEquiv q)))
  · rw [← d4BMXiFunctionalReflectionPair_frequency_eq_mediator n2 n3 q]
    simpa [d4BMQuadraticOutputFrequency, d4BMRealFieldChoiceFrequency] using
      (d4BMQuadraticOutputFrequency_ne_qnmMinus_xi false false n0 n2 n3 q0
        (xiZeroCopyConjEquiv q)
        (xiZeroCopyReflectEquiv (xiZeroCopyConjEquiv q)))

/-- Frequency carried by the reflected real-field QNM pair. -/
def d4BMXiReflectedRealPairFrequency (n : ℕ) (q : XiZeroCopy) : ℂ :=
  thetaCuspHawkingTopologicalBlackHoleQNMPlus n
      (xiSpectralPoint (xiZeroCopyReflectEquiv q)) +
    thetaCuspHawkingTopologicalBlackHoleQNMPlus n
      (xiSpectralPoint
        (xiZeroCopyReflectEquiv (xiZeroCopyConjEquiv q)))

lemma d4BMXiReflectedRealPairFrequency_eq
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiReflectedRealPairFrequency n q =
      -Complex.I * (((4 : ℝ) * n + 3 - (q.1 : ℂ).re : ℝ) : ℂ) := by
  rw [d4BMXiReflectedRealPairFrequency, xiSpectralPoint_reflect,
    xiSpectralPoint_reflect, xiSpectralPoint_copyConj]
  simp only [thetaCuspHawkingTopologicalBlackHoleQNMPlus,
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum,
    thetaCuspHawkingTopologicalBlackHoleConformalDecay, xiSpectralPoint]
  push_cast
  apply Complex.ext <;> simp <;> ring

/-- Real-pair and functional-reflection clocks differ by the Xi tilt. -/
theorem d4BMXiReflectedRealPairFrequency_sub_functionalMediator
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiReflectedRealPairFrequency n q -
        d4BMFunctionalReflectionMediatorFrequency n n =
      Complex.I * ((((q.1 : ℂ).re - 1 / 2 : ℝ) : ℂ)) := by
  rw [d4BMXiReflectedRealPairFrequency_eq]
  simp only [d4BMFunctionalReflectionMediatorFrequency]
  push_cast
  ring

/-- Two-channel clock defect is transported by reflected-versus-conjugated sector exchange. -/
theorem d4BMXiTwoChannelThermalAssociator_eq_sectorFrequencyDefect
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiReflectedRealPairFrequency n q -
        d4BMFunctionalReflectionMediatorFrequency n n =
      thetaCuspHawkingTopologicalBlackHoleQNMPlus n
          (xiSpectralPoint (xiZeroCopyReflectEquiv q)) -
        thetaCuspHawkingTopologicalBlackHoleQNMPlus n
          (xiSpectralPoint (xiZeroCopyConjEquiv q)) := by
  rw [← d4BMXiFunctionalReflectionPair_frequency_eq_mediator n n q]
  unfold d4BMXiReflectedRealPairFrequency
  ring

/-- Reflected-versus-conjugated QNM frequency defect is exactly the Xi tilt. -/
theorem d4BMXiReflected_sub_conjugateQNMPlus_eq_tilt
    (n : ℕ) (q : XiZeroCopy) :
    thetaCuspHawkingTopologicalBlackHoleQNMPlus n
          (xiSpectralPoint (xiZeroCopyReflectEquiv q)) -
        thetaCuspHawkingTopologicalBlackHoleQNMPlus n
          (xiSpectralPoint (xiZeroCopyConjEquiv q)) =
      Complex.I * ((((q.1 : ℂ).re - 1 / 2 : ℝ) : ℂ)) := by
  rw [← d4BMXiTwoChannelThermalAssociator_eq_sectorFrequencyDefect]
  exact d4BMXiReflectedRealPairFrequency_sub_functionalMediator n q

/-- Real-pair and functional-reflection clocks coincide exactly on the critical line. -/
theorem d4BMXiReflectedRealPairFrequency_eq_functionalMediator_iff
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiReflectedRealPairFrequency n q =
        d4BMFunctionalReflectionMediatorFrequency n n ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro h
    have hs : d4BMXiReflectedRealPairFrequency n q -
        d4BMFunctionalReflectionMediatorFrequency n n = 0 := sub_eq_zero.mpr h
    rw [d4BMXiReflectedRealPairFrequency_sub_functionalMediator] at hs
    have him := congrArg Complex.im hs
    simp at him
    linarith
  · intro h
    apply sub_eq_zero.mp
    rw [d4BMXiReflectedRealPairFrequency_sub_functionalMediator, h]
    norm_num

/-- Every reflected real-pair clock is purely damped. -/
theorem d4BMXiReflectedRealPairFrequency_purelyDamped
    (n : ℕ) (q : XiZeroCopy) :
    (d4BMXiReflectedRealPairFrequency n q).re = 0 ∧
      (d4BMXiReflectedRealPairFrequency n q).im < 0 := by
  rw [d4BMXiReflectedRealPairFrequency_eq]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  constructor
  · simp
  · simp
    have hn : (0 : ℝ) ≤ n := by positivity
    linarith

/-- Real-pair backreaction channel gives the equal-overtone quartet return. -/
theorem d4BMXiReflectedRealPairFrequency_cascade
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiReflectedRealPairFrequency n q +
        thetaCuspHawkingTopologicalBlackHoleQNMPlus n
          (xiSpectralPoint (xiZeroCopyConjEquiv q)) =
      thetaCuspHawkingTopologicalBlackHoleQNMMinus (3 * n + 1)
        (xiSpectralPoint q) := by
  rw [d4BMXiReflectedRealPairFrequency, xiSpectralPoint_reflect,
    xiSpectralPoint_reflect, xiSpectralPoint_copyConj]
  simp only [thetaCuspHawkingTopologicalBlackHoleQNMPlus,
    thetaCuspHawkingTopologicalBlackHoleQNMMinus,
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum,
    thetaCuspHawkingTopologicalBlackHoleConformalDecay]
  push_cast
  ring_nf

/-- FE--Schwarz orbit contributes one affine thermal unit. -/
lemma d4BMXiFunctionalQuartet_angularMomentumThermalCocycle
    (q : XiZeroCopy) :
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum
          (xiSpectralPoint (xiZeroCopyConjEquiv q)) +
        thetaCuspHawkingTopologicalBlackHoleAngularMomentum
          (xiSpectralPoint (xiZeroCopyReflectEquiv q)) +
        thetaCuspHawkingTopologicalBlackHoleAngularMomentum
          (xiSpectralPoint (xiZeroCopyReflectEquiv (xiZeroCopyConjEquiv q))) =
      -thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q) +
        Complex.I := by
  rw [xiSpectralPoint_copyConj, xiSpectralPoint_reflect,
    xiSpectralPoint_reflect, xiSpectralPoint_copyConj]
  simp only [thetaCuspHawkingTopologicalBlackHoleAngularMomentum]
  ring_nf

/-- Four FE--Schwarz angular momenta sum to one affine thermal unit. -/
theorem d4BMXiFunctionalQuartet_angularMomentum_sum
    (q : XiZeroCopy) :
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q) +
        thetaCuspHawkingTopologicalBlackHoleAngularMomentum
          (xiSpectralPoint (xiZeroCopyConjEquiv q)) +
        thetaCuspHawkingTopologicalBlackHoleAngularMomentum
          (xiSpectralPoint (xiZeroCopyReflectEquiv q)) +
        thetaCuspHawkingTopologicalBlackHoleAngularMomentum
          (xiSpectralPoint (xiZeroCopyReflectEquiv (xiZeroCopyConjEquiv q))) =
      Complex.I := by
  have h := d4BMXiFunctionalQuartet_angularMomentumThermalCocycle q
  calc
    _ = thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q) +
        (thetaCuspHawkingTopologicalBlackHoleAngularMomentum
            (xiSpectralPoint (xiZeroCopyConjEquiv q)) +
          thetaCuspHawkingTopologicalBlackHoleAngularMomentum
            (xiSpectralPoint (xiZeroCopyReflectEquiv q)) +
          thetaCuspHawkingTopologicalBlackHoleAngularMomentum
            (xiSpectralPoint
              (xiZeroCopyReflectEquiv (xiZeroCopyConjEquiv q)))) := by ring
    _ = Complex.I := by rw [h]; ring

/-- Reflected and conjugated source sectors collide exactly on the critical line. -/
theorem d4BMXiFunctionalQuartet_reflect_conj_spectralCollision_iff
    (q : XiZeroCopy) :
    xiSpectralPoint (xiZeroCopyReflectEquiv q) =
        xiSpectralPoint (xiZeroCopyConjEquiv q) ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [xiSpectralPoint_reflect, xiSpectralPoint_copyConj]
  constructor
  · intro h
    have him := congrArg Complex.im h
    simp [xiSpectralPoint] at him
    linarith
  · intro h
    apply Complex.ext <;> simp [xiSpectralPoint, h]

/-- Three BM decay offsets reindex by one overtone after removing one thermal unit. -/
lemma d4BMConformalDecay_three_sub_one
    (n1 n2 n3 : ℕ) :
    thetaCuspHawkingTopologicalBlackHoleConformalDecay n1 +
        thetaCuspHawkingTopologicalBlackHoleConformalDecay n2 +
        thetaCuspHawkingTopologicalBlackHoleConformalDecay n3 - 1 =
      thetaCuspHawkingTopologicalBlackHoleConformalDecay
        (n1 + n2 + n3 + 1) := by
  simp only [thetaCuspHawkingTopologicalBlackHoleConformalDecay]
  push_cast
  ring

/-- FE--Schwarz quartet is an exact cubic BM branch resonance. -/
theorem d4BMXiFunctionalQuartet_cubicFrequencyResonance
    (n1 n2 n3 : ℕ) (q : XiZeroCopy) :
    thetaCuspHawkingTopologicalBlackHoleQNMPlus n1
          (xiSpectralPoint (xiZeroCopyConjEquiv q)) +
        thetaCuspHawkingTopologicalBlackHoleQNMPlus n2
          (xiSpectralPoint (xiZeroCopyReflectEquiv q)) +
        thetaCuspHawkingTopologicalBlackHoleQNMPlus n3
          (xiSpectralPoint (xiZeroCopyReflectEquiv (xiZeroCopyConjEquiv q))) =
      thetaCuspHawkingTopologicalBlackHoleQNMMinus (n1 + n2 + n3 + 1)
        (xiSpectralPoint q) := by
  rw [xiSpectralPoint_copyConj, xiSpectralPoint_reflect,
    xiSpectralPoint_reflect, xiSpectralPoint_copyConj]
  simp only [thetaCuspHawkingTopologicalBlackHoleQNMPlus,
    thetaCuspHawkingTopologicalBlackHoleQNMMinus,
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum,
    thetaCuspHawkingTopologicalBlackHoleConformalDecay]
  push_cast
  ring_nf

/-- BM spectral point whose overtone `2n` realizes the reflected real-pair clock. -/
def d4BMXiReflectedRealPairMediatorSpectralPoint (q : XiZeroCopy) : ℂ :=
  Complex.I * ((((2 : ℝ) * (q.1 : ℂ).re - 7 / 2 : ℝ) : ℂ))

lemma d4BMXiReflectedRealPairMediatorSpectralPoint_angularMomentum
    (q : XiZeroCopy) :
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum
        (d4BMXiReflectedRealPairMediatorSpectralPoint q) =
      Complex.I * ((((q.1 : ℂ).re - 3 / 2 : ℝ) : ℂ)) := by
  simp [d4BMXiReflectedRealPairMediatorSpectralPoint,
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum]
  ring

lemma d4BMXiReflectedRealPairMediatorSpectralPoint_rho
    (q : XiZeroCopy) :
    d4ThetaTeukolskyRho (d4BMXiReflectedRealPairMediatorSpectralPoint q) =
      (((4 - 2 * (q.1 : ℂ).re : ℝ) : ℂ)) := by
  unfold d4ThetaTeukolskyRho d4BMXiReflectedRealPairMediatorSpectralPoint
  rw [← mul_assoc, Complex.I_mul_I]
  push_cast
  ring

/-- Real angular eigenvalue of the reflected real-pair virtual channel. -/
def d4BMXiReflectedRealPairMediatorAngularQ (q : XiZeroCopy) : ℝ :=
  (2 - (q.1 : ℂ).re) * ((q.1 : ℂ).re - 1)

lemma d4BMXiReflectedRealPairMediatorSpectralPoint_angularEigenvalue
    (q : XiZeroCopy) :
    thetaCuspHawkingTopologicalBlackHoleAngularEigenvalue
        (d4BMXiReflectedRealPairMediatorSpectralPoint q) =
      (d4BMXiReflectedRealPairMediatorAngularQ q : ℂ) := by
  rw [thetaCuspHawkingTopologicalBlackHoleAngularEigenvalue,
    d4BMXiReflectedRealPairMediatorSpectralPoint_angularMomentum]
  unfold d4BMXiReflectedRealPairMediatorAngularQ
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Reflected real-pair clock is a BM virtual QNM at overtone `2n`. -/
theorem d4BMXiReflectedRealPairFrequency_eq_mediatorQNM
    (n : ℕ) (q : XiZeroCopy) :
    d4BMXiReflectedRealPairFrequency n q =
      thetaCuspHawkingTopologicalBlackHoleQNMPlus (2 * n)
        (d4BMXiReflectedRealPairMediatorSpectralPoint q) := by
  rw [d4BMXiReflectedRealPairFrequency_eq,
    thetaCuspHawkingTopologicalBlackHoleQNMPlus,
    d4BMXiReflectedRealPairMediatorSpectralPoint_angularMomentum]
  simp only [thetaCuspHawkingTopologicalBlackHoleConformalDecay]
  push_cast
  ring

lemma d4BMXiReflectedRealPairMediatorAngularQ_add_two
    (q : XiZeroCopy) :
    d4BMXiReflectedRealPairMediatorAngularQ q + 2 =
      (q.1 : ℂ).re * (3 - (q.1 : ℂ).re) := by
  unfold d4BMXiReflectedRealPairMediatorAngularQ
  ring

/-- Every real-pair mediator lies in the virtual angular chamber `-2 < Q < 0`. -/
theorem d4BMXiReflectedRealPairMediatorAngularQ_mem_Ioo
    (q : XiZeroCopy) :
    d4BMXiReflectedRealPairMediatorAngularQ q ∈ Set.Ioo (-2) 0 := by
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  constructor
  · rw [← sub_pos]
    rw [sub_eq_add_neg]
    have hprod : 0 < (q.1 : ℂ).re * (3 - (q.1 : ℂ).re) :=
      mul_pos hstrip.1 (by linarith)
    rw [← d4BMXiReflectedRealPairMediatorAngularQ_add_two] at hprod
    linarith
  · unfold d4BMXiReflectedRealPairMediatorAngularQ
    exact mul_neg_of_pos_of_neg (by linarith) (by linarith)

/-- First-mass parity split in the universal functional-reflection channel. -/
def d4BMFunctionalReflectionMediatorBackreactionSplit : ℝ :=
  d4BackreactionSplit (-3 / 4)

lemma d4BMFunctionalReflectionMediatorBackreactionSplit_eq :
    d4BMFunctionalReflectionMediatorBackreactionSplit = 48 / 5 := by
  norm_num [d4BMFunctionalReflectionMediatorBackreactionSplit, d4BackreactionSplit]

/-- First-mass parity split in the reflected real-pair channel. -/
def d4BMXiReflectedRealPairMediatorBackreactionSplit (q : XiZeroCopy) : ℝ :=
  d4BackreactionSplit (d4BMXiReflectedRealPairMediatorAngularQ q)

lemma d4BMXiReflectedRealPairMediatorBackreactionSplit_eq
    (q : XiZeroCopy) :
    d4BMXiReflectedRealPairMediatorBackreactionSplit q =
      12 / ((q.1 : ℂ).re * (3 - (q.1 : ℂ).re)) := by
  rw [d4BMXiReflectedRealPairMediatorBackreactionSplit, d4BackreactionSplit,
    d4BMXiReflectedRealPairMediatorAngularQ_add_two]

/-- Real-pair channel retains positive chiral backreaction throughout the critical strip. -/
theorem d4BMXiReflectedRealPairMediatorBackreactionSplit_pos
    (q : XiZeroCopy) :
    0 < d4BMXiReflectedRealPairMediatorBackreactionSplit q := by
  rw [d4BMXiReflectedRealPairMediatorBackreactionSplit_eq]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  exact div_pos (by norm_num) (mul_pos hstrip.1 (by linarith))

/-- Difference of the two BM virtual-channel parity responses. -/
def d4BMXiTwoChannelBackreactionDefect (q : XiZeroCopy) : ℝ :=
  d4BMXiReflectedRealPairMediatorBackreactionSplit q -
    d4BMFunctionalReflectionMediatorBackreactionSplit

lemma d4BMXiTwoChannelBackreactionDefect_eq (q : XiZeroCopy) :
    d4BMXiTwoChannelBackreactionDefect q =
      12 * (2 * (q.1 : ℂ).re - 1) * (2 * (q.1 : ℂ).re - 5) /
        (5 * (q.1 : ℂ).re * (3 - (q.1 : ℂ).re)) := by
  rw [d4BMXiTwoChannelBackreactionDefect,
    d4BMXiReflectedRealPairMediatorBackreactionSplit_eq,
    d4BMFunctionalReflectionMediatorBackreactionSplit_eq]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have ha : (q.1 : ℂ).re ≠ 0 := ne_of_gt hstrip.1
  have h3a : 3 - (q.1 : ℂ).re ≠ 0 := ne_of_gt (by linarith)
  field_simp [ha, h3a]
  ring

/-- Two virtual-channel parity responses agree exactly on the critical line. -/
theorem d4BMXiTwoChannelBackreactionDefect_eq_zero_iff
    (q : XiZeroCopy) :
    d4BMXiTwoChannelBackreactionDefect q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMXiTwoChannelBackreactionDefect, sub_eq_zero,
    d4BMXiReflectedRealPairMediatorBackreactionSplit_eq,
    d4BMFunctionalReflectionMediatorBackreactionSplit_eq]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have ha : (q.1 : ℂ).re ≠ 0 := ne_of_gt hstrip.1
  have h3a : 3 - (q.1 : ℂ).re ≠ 0 := ne_of_gt (by linarith)
  constructor
  · intro h
    field_simp [ha, h3a] at h
    nlinarith
  · intro h
    rw [h]
    norm_num

/-- Helicity-basis coefficient induced by the two-channel parity-response defect. -/
def d4BMXiTwoChannelHelicityTransfer (q : XiZeroCopy) : ℝ :=
  d4BMXiTwoChannelBackreactionDefect q / 2

/-- Two-channel helicity transfer vanishes exactly on the critical line. -/
theorem d4BMXiTwoChannelHelicityTransfer_eq_zero_iff
    (q : XiZeroCopy) :
    d4BMXiTwoChannelHelicityTransfer q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMXiTwoChannelHelicityTransfer, div_eq_zero_iff]
  norm_num
  exact d4BMXiTwoChannelBackreactionDefect_eq_zero_iff q

theorem d4BMXiTwoChannelHelicityTransfer_ne_zero_iff
    (q : XiZeroCopy) :
    d4BMXiTwoChannelHelicityTransfer q ≠ 0 ↔
      (q.1 : ℂ).re ≠ 1 / 2 := by
  exact not_congr (d4BMXiTwoChannelHelicityTransfer_eq_zero_iff q)

/-- Every tilted divisor has nonzero two-channel helicity transfer. -/
theorem d4BMXiTwoChannelHelicityTransfer_ne_zero_of_tilt
    (q : XiZeroCopy) (hq : (q.1 : ℂ).re ≠ 1 / 2) :
    d4BMXiTwoChannelHelicityTransfer q ≠ 0 :=
  (d4BMXiTwoChannelHelicityTransfer_ne_zero_iff q).2 hq

/-- Vanishing transfer in every Xi channel. -/
def D4BMXiTwoChannelBackreactionIsConfluent : Prop :=
  ∀ q : XiZeroCopy, d4BMXiTwoChannelHelicityTransfer q = 0

/-- Global two-channel confluence is equivalent to critical-line placement. -/
theorem riemannHypothesis_iff_d4BMXiTwoChannelBackreactionIsConfluent :
    RiemannHypothesis ↔ D4BMXiTwoChannelBackreactionIsConfluent := by
  constructor
  · intro hRH q
    exact (d4BMXiTwoChannelHelicityTransfer_eq_zero_iff q).2
      (xi_divisor_support_re_eq_half_of_rh hRH q.1)
  · intro hconfluent
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have hline :=
      (d4BMXiTwoChannelHelicityTransfer_eq_zero_iff q).1 (hconfluent q)
    refine ⟨(xiSpectralPoint q).re, ?_⟩
    apply Complex.ext
    · simp
    · simp [xiSpectralPoint, hline]

lemma d4BMXiReflect_re (q : XiZeroCopy) :
    ((xiZeroCopyReflectEquiv q).1 : ℂ).re = 1 - (q.1 : ℂ).re := by
  change (1 - (q.1 : ℂ)).re = 1 - (q.1 : ℂ).re
  simp

/-- Difference of real-pair parity responses in reflected Xi sectors. -/
def d4BMXiReflectionOddBackreactionDefect (q : XiZeroCopy) : ℝ :=
  d4BMXiReflectedRealPairMediatorBackreactionSplit q -
    d4BMXiReflectedRealPairMediatorBackreactionSplit
      (xiZeroCopyReflectEquiv q)

lemma d4BMXiReflectionOddBackreactionDefect_eq (q : XiZeroCopy) :
    d4BMXiReflectionOddBackreactionDefect q =
      24 * (1 - 2 * (q.1 : ℂ).re) /
        ((q.1 : ℂ).re * (1 - (q.1 : ℂ).re) *
          (3 - (q.1 : ℂ).re) * (2 + (q.1 : ℂ).re)) := by
  rw [d4BMXiReflectionOddBackreactionDefect,
    d4BMXiReflectedRealPairMediatorBackreactionSplit_eq,
    d4BMXiReflectedRealPairMediatorBackreactionSplit_eq,
    d4BMXiReflect_re]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have ha : (q.1 : ℂ).re ≠ 0 := ne_of_gt hstrip.1
  have h1a : 1 - (q.1 : ℂ).re ≠ 0 := ne_of_gt (by linarith)
  have h3a : 3 - (q.1 : ℂ).re ≠ 0 := ne_of_gt (by linarith)
  have h2a : 2 + (q.1 : ℂ).re ≠ 0 := ne_of_gt (by linarith)
  have hd1 : (q.1 : ℂ).re * (3 - (q.1 : ℂ).re) ≠ 0 :=
    mul_ne_zero ha h3a
  have hd2 : (1 - (q.1 : ℂ).re) * (3 - (1 - (q.1 : ℂ).re)) ≠ 0 :=
    mul_ne_zero h1a (by linarith)
  have hdR : (q.1 : ℂ).re * (1 - (q.1 : ℂ).re) *
      (3 - (q.1 : ℂ).re) * (2 + (q.1 : ℂ).re) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero ha h1a) h3a) h2a
  rw [show 3 - (1 - (q.1 : ℂ).re) = 2 + (q.1 : ℂ).re by ring]
  field_simp [hd1, hd2, hdR]
  ring

/-- Reflected-sector response defect has one zero in the critical strip. -/
theorem d4BMXiReflectionOddBackreactionDefect_eq_zero_iff
    (q : XiZeroCopy) :
    d4BMXiReflectionOddBackreactionDefect q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMXiReflectionOddBackreactionDefect_eq]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have ha : (q.1 : ℂ).re ≠ 0 := ne_of_gt hstrip.1
  have h1a : 1 - (q.1 : ℂ).re ≠ 0 := ne_of_gt (by linarith)
  have h3a : 3 - (q.1 : ℂ).re ≠ 0 := ne_of_gt (by linarith)
  have h2a : 2 + (q.1 : ℂ).re ≠ 0 := ne_of_gt (by linarith)
  constructor
  · intro h
    field_simp [ha, h1a, h3a, h2a] at h
    linarith
  · intro h
    rw [h]
    norm_num

lemma d4BMXiReflectionOddBackreactionDefect_reflect (q : XiZeroCopy) :
    d4BMXiReflectionOddBackreactionDefect (xiZeroCopyReflectEquiv q) =
      -d4BMXiReflectionOddBackreactionDefect q := by
  unfold d4BMXiReflectionOddBackreactionDefect
  rw [xiZeroCopyReflectEquiv_apply_apply]
  ring

theorem d4BMXiReflectionOddBackreactionDefect_pos_of_left
    (q : XiZeroCopy) (hq : (q.1 : ℂ).re < 1 / 2) :
    0 < d4BMXiReflectionOddBackreactionDefect q := by
  rw [d4BMXiReflectionOddBackreactionDefect_eq]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hden : 0 < (q.1 : ℂ).re * (1 - (q.1 : ℂ).re) *
      (3 - (q.1 : ℂ).re) * (2 + (q.1 : ℂ).re) :=
    mul_pos (mul_pos (mul_pos hstrip.1 (by linarith)) (by linarith)) (by linarith)
  exact div_pos (by linarith) hden

theorem d4BMXiReflectionOddBackreactionDefect_neg_of_right
    (q : XiZeroCopy) (hq : 1 / 2 < (q.1 : ℂ).re) :
    d4BMXiReflectionOddBackreactionDefect q < 0 := by
  rw [d4BMXiReflectionOddBackreactionDefect_eq]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have hden : 0 < (q.1 : ℂ).re * (1 - (q.1 : ℂ).re) *
      (3 - (q.1 : ℂ).re) * (2 + (q.1 : ℂ).re) :=
    mul_pos (mul_pos (mul_pos hstrip.1 (by linarith)) (by linarith)) (by linarith)
  exact div_neg_of_neg_of_pos (by linarith) hden

end

end RHTower
