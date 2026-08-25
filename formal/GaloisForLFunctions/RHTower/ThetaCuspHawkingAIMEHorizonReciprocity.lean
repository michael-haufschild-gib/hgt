import GaloisForLFunctions.RHTower.ThetaCuspHawkingTeukolskyThermalDealiasingEndpoint

/-!
# Horizon-flux AIME reciprocity

For the exact `d = 4` topological-black-hole branches, opposite imaginary co-dilations preserve
the common QNM decay. Requiring the two branches to be physical mirrors at real centered momentum
uniquely selects the shifts `∓I/4`; their corrected gap is then `z`.

A unit-absorbed-mass QNM history decays at twice the seed-amplitude rate. Duhamel projection of
that exponential horizon history across the corrected branch gap gives reduced denominators

`2d - 2 Im z + I Re z` and `2d + 2 Im z - I Re z`.

The difference of their reciprocal squared norms is exactly

`16 d Im z / (D₊ D₋)`.

Thus a closed reciprocal two-branch return is possible exactly on the critical line. At any tilted
Xi sector, a reciprocal full Einstein--Teukolsky return requires a nonzero unresolved-channel
correction. This does not prove that full dynamics obeys the reduced reciprocity law.
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Opposite branch-graded horizon co-dilation of the positive QNM branch. -/
def d4HawkingCodilatedQNMPlus (c : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  thetaCuspHawkingTopologicalBlackHoleQNMPlus n z - Complex.I * c

/-- Opposite branch-graded horizon co-dilation of the negative QNM branch. -/
def d4HawkingCodilatedQNMMinus (c : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  thetaCuspHawkingTopologicalBlackHoleQNMMinus n z + Complex.I * c

/-- The co-dilation leaves the common branch trace unchanged. -/
theorem d4HawkingCodilatedQNM_sum (c : ℝ) (n : ℕ) (z : ℂ) :
    d4HawkingCodilatedQNMPlus c n z + d4HawkingCodilatedQNMMinus c n z =
      -2 * Complex.I * thetaCuspHawkingTopologicalBlackHoleConformalDecay n := by
  unfold d4HawkingCodilatedQNMPlus d4HawkingCodilatedQNMMinus
    thetaCuspHawkingTopologicalBlackHoleQNMPlus
    thetaCuspHawkingTopologicalBlackHoleQNMMinus
  ring

/-- Physical mirror covariance on a real channel forces the quarter-surface-gravity co-dilation. -/
theorem d4HawkingCodilation_eq_quarter_of_real_mirror
    (c x : ℝ) (n : ℕ)
    (hmirror : d4HawkingCodilatedQNMMinus c n x =
      -starRingEnd ℂ (d4HawkingCodilatedQNMPlus c n x)) :
    c = 1 / 4 := by
  have him := congrArg Complex.im hmirror
  simp [d4HawkingCodilatedQNMPlus, d4HawkingCodilatedQNMMinus,
    thetaCuspHawkingTopologicalBlackHoleQNMPlus,
    thetaCuspHawkingTopologicalBlackHoleQNMMinus,
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum,
    Complex.div_im] at him
  linarith

/-- Quarter co-dilation gives physical mirror covariance on every real channel. -/
theorem d4HawkingCodilation_quarter_real_mirror (x : ℝ) (n : ℕ) :
    d4HawkingCodilatedQNMMinus (1 / 4) n x =
      -starRingEnd ℂ (d4HawkingCodilatedQNMPlus (1 / 4) n x) := by
  apply Complex.ext
  · simp [d4HawkingCodilatedQNMPlus, d4HawkingCodilatedQNMMinus,
      thetaCuspHawkingTopologicalBlackHoleQNMPlus,
      thetaCuspHawkingTopologicalBlackHoleQNMMinus,
      thetaCuspHawkingTopologicalBlackHoleAngularMomentum,
      Complex.div_re]
    ring
  · simp [d4HawkingCodilatedQNMPlus, d4HawkingCodilatedQNMMinus,
      thetaCuspHawkingTopologicalBlackHoleQNMPlus,
      thetaCuspHawkingTopologicalBlackHoleQNMMinus,
      thetaCuspHawkingTopologicalBlackHoleAngularMomentum,
      Complex.div_im]
    norm_num
    ring

/-- Real-channel mirror covariance uniquely characterizes the quarter co-dilation. -/
theorem d4HawkingCodilation_real_mirror_iff (c x : ℝ) (n : ℕ) :
    d4HawkingCodilatedQNMMinus c n x =
        -starRingEnd ℂ (d4HawkingCodilatedQNMPlus c n x) ↔
      c = 1 / 4 := by
  constructor
  · exact d4HawkingCodilation_eq_quarter_of_real_mirror c x n
  · rintro rfl
    exact d4HawkingCodilation_quarter_real_mirror x n

/-- Canonical quarter-co-dilated positive branch. -/
def d4HawkingMirrorQNMPlus (n : ℕ) (z : ℂ) : ℂ :=
  d4HawkingCodilatedQNMPlus (1 / 4) n z

/-- Canonical quarter-co-dilated negative branch. -/
def d4HawkingMirrorQNMMinus (n : ℕ) (z : ℂ) : ℂ :=
  d4HawkingCodilatedQNMMinus (1 / 4) n z

theorem d4HawkingMirrorQNMPlus_eq (n : ℕ) (z : ℂ) :
    d4HawkingMirrorQNMPlus n z =
      z / 2 - Complex.I * thetaCuspHawkingTopologicalBlackHoleConformalDecay n := by
  unfold d4HawkingMirrorQNMPlus d4HawkingCodilatedQNMPlus
    thetaCuspHawkingTopologicalBlackHoleQNMPlus
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum
  norm_num
  ring

theorem d4HawkingMirrorQNMMinus_eq (n : ℕ) (z : ℂ) :
    d4HawkingMirrorQNMMinus n z =
      -z / 2 - Complex.I * thetaCuspHawkingTopologicalBlackHoleConformalDecay n := by
  unfold d4HawkingMirrorQNMMinus d4HawkingCodilatedQNMMinus
    thetaCuspHawkingTopologicalBlackHoleQNMMinus
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum
  norm_num
  ring

/-- Canonical co-dilation removes the full thermal half-shift from the branch gap. -/
theorem d4HawkingMirrorQNM_gap (n : ℕ) (z : ℂ) :
    d4HawkingMirrorQNMPlus n z - d4HawkingMirrorQNMMinus n z = z := by
  rw [d4HawkingMirrorQNMPlus_eq, d4HawkingMirrorQNMMinus_eq]
  ring

/-- Canonical branches are physical mirrors exactly for a real centered momentum. -/
theorem d4HawkingMirrorQNM_mirror_iff (n : ℕ) (z : ℂ) :
    d4HawkingMirrorQNMMinus n z =
        -starRingEnd ℂ (d4HawkingMirrorQNMPlus n z) ↔
      z.im = 0 := by
  rw [d4HawkingMirrorQNMPlus_eq, d4HawkingMirrorQNMMinus_eq]
  constructor
  · intro h
    have him := congrArg Complex.im h
    simp [map_sub, map_div₀, Complex.div_im] at him
    linarith
  · intro him
    apply Complex.ext
    · simp [him, Complex.div_re]
      ring
    · simp [him, Complex.div_im]

/-- Twice the decay rate of the positive seed amplitude, as seen by horizon energy flux. -/
def d4AIMEHorizonFluxDecayPlus (n : ℕ) (z : ℂ) : ℝ :=
  -2 * (d4HawkingMirrorQNMPlus n z).im

/-- Twice the decay rate of the negative seed amplitude, as seen by horizon energy flux. -/
def d4AIMEHorizonFluxDecayMinus (n : ℕ) (z : ℂ) : ℝ :=
  -2 * (d4HawkingMirrorQNMMinus n z).im

theorem d4AIMEHorizonFluxDecayPlus_eq (n : ℕ) (z : ℂ) :
    d4AIMEHorizonFluxDecayPlus n z =
      2 * thetaCuspHawkingTopologicalBlackHoleConformalDecay n - z.im := by
  rw [d4AIMEHorizonFluxDecayPlus, d4HawkingMirrorQNMPlus_eq]
  simp
  ring

theorem d4AIMEHorizonFluxDecayMinus_eq (n : ℕ) (z : ℂ) :
    d4AIMEHorizonFluxDecayMinus n z =
      2 * thetaCuspHawkingTopologicalBlackHoleConformalDecay n + z.im := by
  rw [d4AIMEHorizonFluxDecayMinus, d4HawkingMirrorQNMMinus_eq]
  simp
  ring

/-- Duhamel denominator for positive-to-negative AIME conversion. -/
def d4AIMEHorizonDenominatorPlus (n : ℕ) (z : ℂ) : ℂ :=
  (d4AIMEHorizonFluxDecayPlus n z : ℂ) +
    Complex.I * (d4HawkingMirrorQNMPlus n z - d4HawkingMirrorQNMMinus n z)

/-- Duhamel denominator for negative-to-positive AIME conversion. -/
def d4AIMEHorizonDenominatorMinus (n : ℕ) (z : ℂ) : ℂ :=
  (d4AIMEHorizonFluxDecayMinus n z : ℂ) +
    Complex.I * (d4HawkingMirrorQNMMinus n z - d4HawkingMirrorQNMPlus n z)

/-- Flux-normalized temporal AIME susceptibility in the positive-to-negative direction. -/
def d4AIMEHorizonSusceptibilityPlus (n : ℕ) (z : ℂ) : ℂ :=
  (d4AIMEHorizonDenominatorPlus n z)⁻¹

/-- Flux-normalized temporal AIME susceptibility in the negative-to-positive direction. -/
def d4AIMEHorizonSusceptibilityMinus (n : ℕ) (z : ℂ) : ℂ :=
  (d4AIMEHorizonDenominatorMinus n z)⁻¹

/-- Squared gain of the reduced positive-to-negative temporal susceptibility. -/
def d4AIMEHorizonGainPlus (n : ℕ) (z : ℂ) : ℝ :=
  1 / Complex.normSq (d4AIMEHorizonDenominatorPlus n z)

/-- Squared gain of the reduced negative-to-positive temporal susceptibility. -/
def d4AIMEHorizonGainMinus (n : ℕ) (z : ℂ) : ℝ :=
  1 / Complex.normSq (d4AIMEHorizonDenominatorMinus n z)

theorem normSq_d4AIMEHorizonDenominatorPlus (n : ℕ) (z : ℂ) :
    Complex.normSq (d4AIMEHorizonDenominatorPlus n z) =
      (2 * thetaCuspHawkingTopologicalBlackHoleConformalDecay n - 2 * z.im) ^ 2 +
        z.re ^ 2 := by
  rw [d4AIMEHorizonDenominatorPlus, d4HawkingMirrorQNM_gap,
    d4AIMEHorizonFluxDecayPlus_eq, Complex.normSq_apply]
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem normSq_d4AIMEHorizonDenominatorMinus (n : ℕ) (z : ℂ) :
    Complex.normSq (d4AIMEHorizonDenominatorMinus n z) =
      (2 * thetaCuspHawkingTopologicalBlackHoleConformalDecay n + 2 * z.im) ^ 2 +
        z.re ^ 2 := by
  rw [d4AIMEHorizonDenominatorMinus, d4AIMEHorizonFluxDecayMinus_eq]
  have hgap : d4HawkingMirrorQNMMinus n z - d4HawkingMirrorQNMPlus n z = -z := by
    rw [d4HawkingMirrorQNMPlus_eq, d4HawkingMirrorQNMMinus_eq]
    ring
  rw [hgap, Complex.normSq_apply]
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- Exact mirror-gain defect of the flux-normalized AIME horizon history. -/
theorem d4AIMEHorizonGain_sub_mirror
    (n : ℕ) (z : ℂ) (hz : z.re ≠ 0) :
    d4AIMEHorizonGainPlus n z - d4AIMEHorizonGainMinus n z =
      16 * thetaCuspHawkingTopologicalBlackHoleConformalDecay n * z.im /
        (Complex.normSq (d4AIMEHorizonDenominatorPlus n z) *
          Complex.normSq (d4AIMEHorizonDenominatorMinus n z)) := by
  have hplusPos : 0 < Complex.normSq (d4AIMEHorizonDenominatorPlus n z) := by
    rw [normSq_d4AIMEHorizonDenominatorPlus]
    nlinarith [sq_pos_of_ne_zero hz]
  have hminusPos : 0 < Complex.normSq (d4AIMEHorizonDenominatorMinus n z) := by
    rw [normSq_d4AIMEHorizonDenominatorMinus]
    nlinarith [sq_pos_of_ne_zero hz]
  unfold d4AIMEHorizonGainPlus d4AIMEHorizonGainMinus
  field_simp [ne_of_gt hplusPos, ne_of_gt hminusPos]
  rw [normSq_d4AIMEHorizonDenominatorPlus, normSq_d4AIMEHorizonDenominatorMinus]
  ring

/-- Reduced horizon-history reciprocity is equivalent to zero tilt. -/
theorem d4AIMEHorizonGain_eq_mirror_iff
    (n : ℕ) (z : ℂ) (hz : z.re ≠ 0) :
    d4AIMEHorizonGainPlus n z = d4AIMEHorizonGainMinus n z ↔ z.im = 0 := by
  have hplusPos : 0 < Complex.normSq (d4AIMEHorizonDenominatorPlus n z) := by
    rw [normSq_d4AIMEHorizonDenominatorPlus]
    nlinarith [sq_pos_of_ne_zero hz]
  have hminusPos : 0 < Complex.normSq (d4AIMEHorizonDenominatorMinus n z) := by
    rw [normSq_d4AIMEHorizonDenominatorMinus]
    nlinarith [sq_pos_of_ne_zero hz]
  constructor
  · intro hgain
    have hdiff : d4AIMEHorizonGainPlus n z - d4AIMEHorizonGainMinus n z = 0 :=
      sub_eq_zero.mpr hgain
    rw [d4AIMEHorizonGain_sub_mirror n z hz] at hdiff
    have hnum :
        16 * thetaCuspHawkingTopologicalBlackHoleConformalDecay n * z.im = 0 :=
      (div_eq_zero_iff.mp hdiff).resolve_right
        (mul_ne_zero (ne_of_gt hplusPos) (ne_of_gt hminusPos))
    have hdecay : thetaCuspHawkingTopologicalBlackHoleConformalDecay n ≠ 0 := by
      unfold thetaCuspHawkingTopologicalBlackHoleConformalDecay
      positivity
    exact (mul_eq_zero.mp hnum).resolve_left (mul_ne_zero (by norm_num) hdecay)
  · intro him
    unfold d4AIMEHorizonGainPlus d4AIMEHorizonGainMinus
    rw [normSq_d4AIMEHorizonDenominatorPlus, normSq_d4AIMEHorizonDenominatorMinus]
    simp [him]

/-- At a Xi divisor, reciprocal reduced AIME gain is exactly critical-line incidence. -/
theorem xi_d4AIMEHorizonGain_eq_mirror_iff (n : ℕ) (q : XiZeroCopy) :
    d4AIMEHorizonGainPlus n (xiSpectralPoint q) =
        d4AIMEHorizonGainMinus n (xiSpectralPoint q) ↔
      (xiSpectralPoint q).im = 0 := by
  exact d4AIMEHorizonGain_eq_mirror_iff n _
    (thetaCuspHawkingHypergeometricXiSpectralPoint_re_ne_zero q)

/-- Every divisor-indexed reduced horizon-history block is reciprocal. -/
def D4ThetaTeukolskyAIMEHorizonReciprocal : Prop :=
  ∀ (n : ℕ) (q : XiZeroCopy),
    d4AIMEHorizonGainPlus n (xiSpectralPoint q) =
      d4AIMEHorizonGainMinus n (xiSpectralPoint q)

/-- RH is equivalent to reciprocity of every flux-normalized AIME horizon-history block. -/
theorem riemannHypothesis_iff_d4ThetaTeukolskyAIMEHorizonReciprocal :
    RiemannHypothesis ↔ D4ThetaTeukolskyAIMEHorizonReciprocal := by
  constructor
  · intro hRH n q
    exact (xi_d4AIMEHorizonGain_eq_mirror_iff n q).mpr
      (xiSpectralPoint_im_eq_zero_of_riemannHypothesis hRH q)
  · intro h
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have him := (xi_d4AIMEHorizonGain_eq_mirror_iff 0 q).mp (h 0 q)
    exact ⟨(xiSpectralPoint q).re, by
      apply Complex.ext
      · simp
      · simpa using him⟩

/-- Full reciprocity fixes the exact imbalance required from unresolved return channels. -/
theorem d4AIMEHorizonExternalCorrection_difference
    (n : ℕ) (z : ℂ) (hz : z.re ≠ 0)
    (externalPlus externalMinus : ℝ)
    (hbalance : d4AIMEHorizonGainPlus n z + externalPlus =
      d4AIMEHorizonGainMinus n z + externalMinus) :
    externalPlus - externalMinus =
      -(16 * thetaCuspHawkingTopologicalBlackHoleConformalDecay n * z.im /
        (Complex.normSq (d4AIMEHorizonDenominatorPlus n z) *
          Complex.normSq (d4AIMEHorizonDenominatorMinus n z))) := by
  linarith [d4AIMEHorizonGain_sub_mirror n z hz]

/-- A tilted sector cannot be both reciprocal and closed under the reduced two-branch return. -/
theorem d4AIMEHorizon_tilt_forces_externalCorrection
    (n : ℕ) (z : ℂ) (hz : z.re ≠ 0) (htilt : z.im ≠ 0)
    (externalPlus externalMinus : ℝ)
    (hbalance : d4AIMEHorizonGainPlus n z + externalPlus =
      d4AIMEHorizonGainMinus n z + externalMinus) :
    externalPlus ≠ 0 ∨ externalMinus ≠ 0 := by
  by_contra hnonzero
  have hzero : externalPlus = 0 ∧ externalMinus = 0 := by
    simpa only [not_or, not_ne_iff] using hnonzero
  have hgain : d4AIMEHorizonGainPlus n z = d4AIMEHorizonGainMinus n z := by
    rw [hzero.1, hzero.2, add_zero, add_zero] at hbalance
    exact hbalance
  exact htilt ((d4AIMEHorizonGain_eq_mirror_iff n z hz).mp hgain)

/-- Every tilted Xi sector needs a nonzero unresolved correction in any reciprocal completion. -/
theorem xi_d4AIMEHorizon_tilt_forces_externalCorrection
    (n : ℕ) (q : XiZeroCopy) (htilt : (xiSpectralPoint q).im ≠ 0)
    (externalPlus externalMinus : ℝ)
    (hbalance : d4AIMEHorizonGainPlus n (xiSpectralPoint q) + externalPlus =
      d4AIMEHorizonGainMinus n (xiSpectralPoint q) + externalMinus) :
    externalPlus ≠ 0 ∨ externalMinus ≠ 0 := by
  exact d4AIMEHorizon_tilt_forces_externalCorrection n _
    (thetaCuspHawkingHypergeometricXiSpectralPoint_re_ne_zero q) htilt
    externalPlus externalMinus hbalance

end


end RHTower
