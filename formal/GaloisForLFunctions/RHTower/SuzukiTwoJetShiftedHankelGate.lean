import GaloisForLFunctions.RHTower.SuzukiSecondDefectCompactParitySource
import GaloisForLFunctions.RHTower.SuzukiFiniteApertureHermiteBiehler
import GaloisForLFunctions.HTGeometry.ReflectedDividedDifference
import Mathlib.Analysis.Complex.Schwarz

/-!
# Suzuki's two-jet shifted-Hankel gate

An anchored holomorphic self-map of the disk has a nonlinear second-jet constraint

`‖f''(0)‖ ≤ 2 * (1 - ‖f'(0)‖²)`.

For Suzuki's parity coordinates this is exactly

`0 ≤ O * (E + alpha) - E * beta`.

For the normalized Xi target the same slack is exactly sixteen times the first `2 × 2`
Hankel determinant of the safe-shift reciprocal moments, divided by the square of the zeroth
moment.  Thus the finite-aperture Schur problem and the shifted Hankel problem are the same
two-jet gate, not merely analogous positivity questions.

The final decomposition records a sharp limitation of the position-torque invariant:
`alpha - beta` controls only one summand of the Schur slack.  The local tilt-asymmetry term
`alpha * (O - E)` remains independent.

No RH assumption or numerical computation occurs.
-/

open Complex Metric Set

namespace RHTower

noncomputable section

private theorem diskMobius_normSq_sub
    (a w : ℂ) :
    Complex.normSq (1 - (starRingEnd ℂ) a * w) -
        Complex.normSq (w - a) =
      (1 - Complex.normSq a) * (1 - Complex.normSq w) := by
  rw [Complex.normSq_sub, Complex.normSq_sub, Complex.normSq_mul,
    Complex.normSq_conj]
  simp only [one_mul, Complex.normSq_eq_norm_sq]
  have hre : (((starRingEnd ℂ) ((starRingEnd ℂ) a * w)).re) =
      (((starRingEnd ℂ) a * w).re) := by
    simpa only [map_mul, star_star] using
      Complex.conj_re ((starRingEnd ℂ) a * w)
  rw [hre, norm_one]
  ring

private theorem diskMobius_norm_le_one
    {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ ≤ 1) :
    ‖(w - a) / (1 - (starRingEnd ℂ) a * w)‖ ≤ 1 := by
  have hprod : ‖(starRingEnd ℂ) a * w‖ < 1 := by
    rw [norm_mul, Complex.norm_conj]
    calc
      ‖a‖ * ‖w‖ ≤ ‖a‖ * 1 :=
        mul_le_mul_of_nonneg_left hw (norm_nonneg a)
      _ < 1 * 1 := by simpa using ha
      _ = 1 := one_mul 1
  have hden : 1 - (starRingEnd ℂ) a * w ≠ 0 := by
    rw [sub_ne_zero]
    intro heq
    have : ‖(starRingEnd ℂ) a * w‖ = 1 := by
      rw [← heq, norm_one]
    linarith
  have haSq : Complex.normSq a < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg a]
  have hwSq : Complex.normSq w ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg w]
  have hSq : Complex.normSq (w - a) ≤
      Complex.normSq (1 - (starRingEnd ℂ) a * w) := by
    have hid := diskMobius_normSq_sub a w
    have hnonneg : 0 ≤
        (1 - Complex.normSq a) * (1 - Complex.normSq w) :=
      mul_nonneg (le_of_lt (sub_pos.mpr haSq)) (sub_nonneg.mpr hwSq)
    linarith
  rw [norm_div, div_le_one (norm_pos_iff.mpr hden)]
  rw [← (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _))]
  simpa only [← Complex.normSq_eq_norm_sq] using hSq

/-- **Anchored Schur second-jet bound.**  This is the order-two Schwarz--Pick constraint at the
origin, proved here in the exact normalization used by Suzuki's disk carrier. -/
theorem norm_iteratedDeriv_two_le_schurSlack
    {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hf0 : f 0 = 0)
    (hmap : MapsTo f (Metric.ball 0 1) (Metric.closedBall 0 1))
    (ha : ‖deriv f 0‖ < 1) :
    ‖iteratedDeriv 2 f 0‖ ≤ 2 * (1 - ‖deriv f 0‖ ^ 2) := by
  let g : ℂ → ℂ := dslope f 0
  let a : ℂ := deriv f 0
  let h : ℂ → ℂ :=
    fun z => (g z - a) / (1 - (starRingEnd ℂ) a * g z)
  have hball : Metric.ball (0 : ℂ) (1 : ℝ) ∈ nhds 0 :=
    Metric.ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1)
  have hg : DifferentiableOn ℂ g (Metric.ball 0 1) := by
    exact (differentiableOn_dslope hball).mpr hf
  have hgw : ∀ z ∈ Metric.ball (0 : ℂ) 1, ‖g z‖ ≤ 1 := by
    intro z hz
    have hm : MapsTo f (Metric.ball (0 : ℂ) 1)
        (Metric.closedBall (f 0) 1) := by
      simpa only [hf0] using hmap
    have hs := Complex.norm_dslope_le_div_of_mapsTo_ball hf hm hz
    norm_num [g] at hs ⊢
    exact hs
  have hden : ∀ z ∈ Metric.ball (0 : ℂ) 1,
      1 - (starRingEnd ℂ) a * g z ≠ 0 := by
    intro z hz
    rw [sub_ne_zero]
    intro heq
    have hprod : ‖(starRingEnd ℂ) a * g z‖ < 1 := by
      rw [norm_mul, Complex.norm_conj]
      calc
        ‖a‖ * ‖g z‖ ≤ ‖a‖ * 1 :=
          mul_le_mul_of_nonneg_left (hgw z hz) (norm_nonneg a)
        _ < 1 * 1 := by simpa only [a, mul_one, one_mul] using ha
        _ = 1 := one_mul 1
    have : ‖(starRingEnd ℂ) a * g z‖ = 1 := by
      rw [← heq, norm_one]
    linarith
  have hh : DifferentiableOn ℂ h (Metric.ball 0 1) := by
    intro z hz
    exact ((hg z hz).sub_const a).div
      ((differentiableWithinAt_const (c := (1 : ℂ))).sub
        ((hg z hz).const_mul ((starRingEnd ℂ) a)))
      (hden z hz)
  have hmaph : MapsTo h (Metric.ball (0 : ℂ) 1)
      (Metric.closedBall (h 0) 1) := by
    intro z hz
    have hg0 : g 0 = a := by
      simp only [g, a, dslope_same]
    have hh0 : h 0 = 0 := by
      simp only [h, hg0, sub_self, zero_div]
    rw [hh0, mem_closedBall_zero_iff]
    exact diskMobius_norm_le_one ha (hgw z hz)
  have hdh :=
    Complex.norm_deriv_le_one_of_mapsTo_ball hh hmaph (by norm_num)
  have hg0 : g 0 = a := by
    simp only [g, a, dslope_same]
  have haSq : 1 - Complex.normSq a ≠ 0 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg a]
  have hgd : HasDerivAt g (iteratedDeriv 2 f 0 / 2) 0 := by
    have hfa : AnalyticAt ℂ f 0 := hf.analyticAt hball
    have hs :=
      HTGeometry.iteratedDeriv_dslope_self_eq_iteratedDeriv_succ_div hfa 1
    have hderiv : deriv g 0 = iteratedDeriv 2 f 0 / 2 := by
      simpa only [one_add_one_eq_two, Nat.cast_one, iteratedDeriv_one, g] using hs
    rw [← hderiv]
    exact (hg.differentiableAt hball).hasDerivAt
  have hhd : HasDerivAt h
      ((iteratedDeriv 2 f 0 / 2) / (1 - Complex.normSq a)) 0 := by
    have hnum := hgd.sub_const a
    have hden' := (hasDerivAt_const (x := (0 : ℂ)) (1 : ℂ)).sub
      (hgd.const_mul ((starRingEnd ℂ) a))
    have hq := hnum.div hden' (by
      change 1 - (starRingEnd ℂ) a * g 0 ≠ 0
      rw [hg0, ← Complex.normSq_eq_conj_mul_self]
      exact_mod_cast haSq)
    simp only [Pi.sub_apply, hg0, sub_self, zero_mul, sub_zero,
      ← Complex.normSq_eq_conj_mul_self] at hq
    change HasDerivAt h
      (iteratedDeriv 2 f 0 / 2 * (1 - (Complex.normSq a : ℂ)) /
        (1 - (Complex.normSq a : ℂ)) ^ 2) 0 at hq
    have hcoeff :
        iteratedDeriv 2 f 0 / 2 * (1 - (Complex.normSq a : ℂ)) /
            (1 - (Complex.normSq a : ℂ)) ^ 2 =
          (iteratedDeriv 2 f 0 / 2) / (1 - Complex.normSq a) := by
      have hcast : (1 - (Complex.normSq a : ℂ)) ≠ 0 := by
        exact_mod_cast haSq
      field_simp [hcast]
    rw [hcoeff] at hq
    exact hq
  have hnorm :
      ‖(iteratedDeriv 2 f 0 / 2) / (1 - Complex.normSq a)‖ ≤ 1 := by
    simpa only [hhd.deriv] using hdh
  rw [norm_div, norm_div] at hnorm
  have hpos : 0 < 1 - Complex.normSq a := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg a]
  have hdennorm :
      ‖(1 - (Complex.normSq a : ℂ))‖ = 1 - Complex.normSq a := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hpos]
  rw [hdennorm] at hnorm
  rw [Complex.normSq_eq_norm_sq] at hnorm hpos
  simp only [a] at hnorm hpos
  norm_num at hnorm
  have hhalf :
      ‖iteratedDeriv 2 f 0‖ / 2 ≤ 1 - ‖deriv f 0‖ ^ 2 :=
    (div_le_one hpos).mp hnorm
  nlinarith

/-- Real form of the anchored Schur lower-curvature boundary. -/
theorem real_secondJet_add_schurBoundary_nonneg
    {f : ℂ → ℂ} {firstJet secondJet : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hf0 : f 0 = 0)
    (hmap : MapsTo f (Metric.ball 0 1) (Metric.closedBall 0 1))
    (hfirst : deriv f 0 = (firstJet : ℂ))
    (hsecond : iteratedDeriv 2 f 0 = (secondJet : ℂ))
    (hfirstStrict : |firstJet| < 1) :
    0 ≤ secondJet + 2 * (1 - firstJet ^ 2) := by
  have hbound := norm_iteratedDeriv_two_le_schurSlack hf hf0 hmap (by
    rw [hfirst, Complex.norm_real, Real.norm_eq_abs]
    exact hfirstStrict)
  rw [hfirst, hsecond] at hbound
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hbound
  have hlower := neg_le_of_abs_le hbound
  linarith

/-- The abstract disk hypotheses above are automatic for Suzuki's actual all-angle
Hermite--Biehler carrier after disk conjugation. -/
theorem suzukiAllAngleCarrier_forces_real_twoJetSlack
    {A E : ℂ → ℂ} {firstJet secondJet : ℝ}
    (hA : Differentiable ℂ A) (hE : Differentiable ℂ E)
    (hAi : A I = 0)
    (hreal : GaloisForLFunctions.RHTower.SuzukiAllAngleRealZeros A E)
    (hfirst : deriv (fun w =>
      GaloisForLFunctions.RHTower.suzukiLivsicQuotient A E
        (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w)) 0 =
      (firstJet : ℂ))
    (hsecond : iteratedDeriv 2 (fun w =>
      GaloisForLFunctions.RHTower.suzukiLivsicQuotient A E
        (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w)) 0 =
      (secondJet : ℂ))
    (hfirstStrict : |firstJet| < 1) :
    0 ≤ secondJet + 2 * (1 - firstJet ^ 2) := by
  let f : ℂ → ℂ := fun w =>
    GaloisForLFunctions.RHTower.suzukiLivsicQuotient A E
      (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w)
  have hopen : IsOpen {z : ℂ | 0 < z.im} :=
    isOpen_lt continuous_const Complex.continuous_im
  have hquot :=
    GaloisForLFunctions.RHTower.differentiableOn_suzukiLivsicQuotient_upperHalfPlane
      hA hE hAi hreal
  have hf : DifferentiableOn ℂ f (Metric.ball 0 1) := by
    intro w hw
    have hwlt : ‖w‖ < 1 := by
      simpa [mem_ball_zero_iff] using hw
    have hw1 : w ≠ 1 := by
      intro heq
      rw [heq, norm_one] at hwlt
      exact (lt_irrefl 1) hwlt
    have hinv :
        DifferentiableAt ℂ
          GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w := by
      change DifferentiableAt ℂ
        (fun v : ℂ => I * ((1 + v) / (1 - v))) w
      fun_prop (disch := exact sub_ne_zero.mpr (Ne.symm hw1))
    have him :=
      GaloisForLFunctions.RHTower.suzukiUpperCayleyInv_im_pos_of_norm_lt_one hwlt
    have hout :
        DifferentiableAt ℂ
          (GaloisForLFunctions.RHTower.suzukiLivsicQuotient A E)
          (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w) :=
      hquot.differentiableAt (hopen.mem_nhds him)
    exact (hout.comp w hinv).differentiableWithinAt
  have hf0 : f 0 = 0 := by
    change GaloisForLFunctions.RHTower.suzukiLivsicQuotient A E
      (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv 0) = 0
    rw [show GaloisForLFunctions.RHTower.suzukiUpperCayleyInv 0 = I by
      norm_num [GaloisForLFunctions.RHTower.suzukiUpperCayleyInv]]
    exact GaloisForLFunctions.RHTower.suzukiLivsicQuotient_I_eq_zero hAi
  have hmap :
      MapsTo f (Metric.ball (0 : ℂ) 1) (Metric.closedBall 0 1) := by
    intro w hw
    rw [mem_closedBall_zero_iff]
    have hwlt : ‖w‖ < 1 := by
      simpa [mem_ball_zero_iff] using hw
    exact (GaloisForLFunctions.RHTower.norm_suzukiLivsicQuotient_lt_one
      hA.continuous hE.continuous hAi hreal
      (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv_im_pos_of_norm_lt_one
        hwlt)).le
  exact real_secondJet_add_schurBoundary_nonneg
    hf hf0 hmap hfirst hsecond hfirstStrict

/-- Exact parity-coordinate form of the Schur two-jet slack. -/
theorem suzukiParity_twoJetSlack_eq
    {evenEnergy oddEnergy evenTilt oddTilt : ℝ}
    (hsum : evenEnergy + oddEnergy ≠ 0) :
    suzukiSecondDefectParityCurvature
          evenEnergy oddEnergy evenTilt oddTilt +
        2 * (1 - GaloisForLFunctions.RHTower.suzukiDefectAngle
          evenEnergy oddEnergy ^ 2) =
      8 * (oddEnergy * (evenEnergy + evenTilt) -
          evenEnergy * oddTilt) /
        (evenEnergy + oddEnergy) ^ 2 := by
  rw [suzukiSecondDefectParityCurvature,
    GaloisForLFunctions.RHTower.suzukiDefectAngle]
  field_simp [hsum]
  ring

/-- **Suzuki source Schur law.**  Any finite-aperture carrier satisfying the anchored disk
self-map property forces this nonlinear inequality between parity energies and their exponential
tilts.  It is a source law, not a target-selected calibration. -/
theorem suzukiSchurCarrier_forces_parity_twoJetSlack
    {f : ℂ → ℂ} {evenEnergy oddEnergy evenTilt oddTilt : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    (hf0 : f 0 = 0)
    (hmap : MapsTo f (Metric.ball 0 1) (Metric.closedBall 0 1))
    (heven : 0 < evenEnergy) (hodd : 0 < oddEnergy)
    (hfirst : deriv f 0 =
      (GaloisForLFunctions.RHTower.suzukiDefectAngle
        evenEnergy oddEnergy : ℂ))
    (hsecond : iteratedDeriv 2 f 0 =
      (suzukiSecondDefectParityCurvature
        evenEnergy oddEnergy evenTilt oddTilt : ℂ)) :
    0 ≤ oddEnergy * (evenEnergy + evenTilt) -
      evenEnergy * oddTilt := by
  have hsum : 0 < evenEnergy + oddEnergy := add_pos heven hodd
  have hangle :
      |GaloisForLFunctions.RHTower.suzukiDefectAngle
        evenEnergy oddEnergy| < 1 := by
    rw [GaloisForLFunctions.RHTower.suzukiDefectAngle, abs_lt]
    constructor
    · rw [lt_div_iff₀ hsum]
      linarith
    · rw [div_lt_iff₀ hsum]
      linarith
  have hslack := real_secondJet_add_schurBoundary_nonneg
    hf hf0 hmap hfirst hsecond hangle
  rw [suzukiParity_twoJetSlack_eq hsum.ne'] at hslack
  have hden : 0 < (evenEnergy + oddEnergy) ^ 2 :=
    sq_pos_of_pos hsum
  have hnum := (le_div_iff₀ hden).mp hslack
  nlinarith

/-- **Literal all-angle Suzuki source law.**  The abstract disk-map hypothesis has been eliminated:
Suzuki's all-angle real-zero theorem supplies it through finite-aperture Hermite--Biehler
separation. -/
theorem suzukiAllAngleCarrier_forces_parity_twoJetSlack
    {A E : ℂ → ℂ} {evenEnergy oddEnergy evenTilt oddTilt : ℝ}
    (hA : Differentiable ℂ A) (hE : Differentiable ℂ E)
    (hAi : A I = 0)
    (hreal : GaloisForLFunctions.RHTower.SuzukiAllAngleRealZeros A E)
    (heven : 0 < evenEnergy) (hodd : 0 < oddEnergy)
    (hfirst : deriv (fun w =>
      GaloisForLFunctions.RHTower.suzukiLivsicQuotient A E
        (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w)) 0 =
      (GaloisForLFunctions.RHTower.suzukiDefectAngle
        evenEnergy oddEnergy : ℂ))
    (hsecond : iteratedDeriv 2 (fun w =>
      GaloisForLFunctions.RHTower.suzukiLivsicQuotient A E
        (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w)) 0 =
      (suzukiSecondDefectParityCurvature
        evenEnergy oddEnergy evenTilt oddTilt : ℂ)) :
    0 ≤ oddEnergy * (evenEnergy + evenTilt) -
      evenEnergy * oddTilt := by
  have hsum : 0 < evenEnergy + oddEnergy := add_pos heven hodd
  have hangle :
      |GaloisForLFunctions.RHTower.suzukiDefectAngle
        evenEnergy oddEnergy| < 1 := by
    rw [GaloisForLFunctions.RHTower.suzukiDefectAngle, abs_lt]
    constructor
    · rw [lt_div_iff₀ hsum]
      linarith
    · rw [div_lt_iff₀ hsum]
      linarith
  have hslack := suzukiAllAngleCarrier_forces_real_twoJetSlack
    hA hE hAi hreal hfirst hsecond hangle
  rw [suzukiParity_twoJetSlack_eq hsum.ne'] at hslack
  have hden : 0 < (evenEnergy + oddEnergy) ^ 2 :=
    sq_pos_of_pos hsum
  have hnum := (le_div_iff₀ hden).mp hslack
  nlinarith

/-- The source Schur numerator decomposes into energy, position torque, and a residual local
tilt-asymmetry term.  Therefore the commutator torque alone cannot determine its sign. -/
theorem suzukiParity_twoJetSlack_torque_decomposition
    (evenEnergy oddEnergy evenTilt oddTilt : ℝ) :
    oddEnergy * (evenEnergy + evenTilt) - evenEnergy * oddTilt =
      evenEnergy * oddEnergy +
        evenEnergy * (evenTilt - oddTilt) +
        evenTilt * (oddEnergy - evenEnergy) := by
  ring

/-- **Torque-only fiber classification.**  Away from exact parity-energy balance, fixing the
commutator torque `evenTilt - oddTilt` leaves the Schur numerator completely unconstrained: every
real value occurs.  This is a class-complete obstruction to closing Suzuki's two-jet gate from
position torque alone. -/
theorem suzukiParity_twoJetSlack_surjective_at_fixed_torque
    {evenEnergy oddEnergy torque target : ℝ}
    (hbalance : oddEnergy ≠ evenEnergy) :
    ∃ evenTilt oddTilt : ℝ,
      evenTilt - oddTilt = torque ∧
      oddEnergy * (evenEnergy + evenTilt) -
          evenEnergy * oddTilt = target := by
  let evenTilt :=
    (target - evenEnergy * oddEnergy - evenEnergy * torque) /
      (oddEnergy - evenEnergy)
  let oddTilt := evenTilt - torque
  refine ⟨evenTilt, oddTilt, by simp only [oddTilt]; ring, ?_⟩
  dsimp only [evenTilt, oddTilt]
  field_simp [sub_ne_zero.mpr hbalance]
  ring

/-- At exact parity-energy balance the missing local tilt term vanishes, so torque becomes a
complete sign coordinate for the two-jet Schur numerator. -/
theorem suzukiParity_twoJetSlack_of_balanced_energy
    (energy evenTilt oddTilt : ℝ) :
    energy * (energy + evenTilt) - energy * oddTilt =
      energy * (energy + (evenTilt - oddTilt)) := by
  ring

/-- Sharp balanced-energy torque threshold. -/
theorem suzukiParity_twoJetSlack_balanced_nonneg_iff
    {energy torque : ℝ} (henergy : 0 < energy) :
    0 ≤ energy * (energy + torque) ↔ -energy ≤ torque := by
  constructor
  · intro h
    nlinarith
  · intro h
    exact mul_nonneg henergy.le (by linarith)

/-- Generic moment algebra behind the shifted-Hankel identification. -/
theorem moment_twoJetSlack_eq_hankelMinor
    {A B C : ℝ} (hA : A ≠ 0) :
    8 * (2 * C / A - B / A - (B / A) ^ 2) +
        2 * (1 - ((A - 2 * B) / A) ^ 2) =
      16 * (A * C - B ^ 2) / A ^ 2 := by
  field_simp [hA]
  ring

/-- **Exact safe-shift Hankel gate.**  Xi's first and second Suzuki calibrations have Schur slack
equal to the normalized first `2 × 2` Hankel minor of the safe-shift reciprocal moments. -/
theorem primeArchSuzuki_twoJetSlack_eq_shiftedHankelMinor :
    primeArchSuzukiSecondDefectCalibration +
        2 * (1 - primeArchSuzukiFirstDefectCalibration ^ 2) =
      16 *
          ((primeArchShiftedReciprocalMoment 1 0).re *
              (primeArchShiftedReciprocalMoment 1 2).re -
            (primeArchShiftedReciprocalMoment 1 1).re ^ 2) /
        (primeArchShiftedReciprocalMoment 1 0).re ^ 2 := by
  have hA : (primeArchShiftedReciprocalMoment 1 0).re ≠ 0 :=
    ne_of_gt re_primeArchShiftedReciprocalMoment_one_zero_pos
  rw [primeArchSuzukiFirstDefectCalibration,
    primeArchSuzukiSecondDefectCalibration]
  exact moment_twoJetSlack_eq_hankelMinor hA

/-- Nonnegativity of Xi's Suzuki two-jet Schur slack is equivalent, with no loss, to
nonnegativity of the safe-shift first Hankel minor. -/
theorem primeArchSuzuki_twoJetSlack_nonneg_iff_shiftedHankelMinor_nonneg :
    0 ≤ primeArchSuzukiSecondDefectCalibration +
          2 * (1 - primeArchSuzukiFirstDefectCalibration ^ 2) ↔
      0 ≤
        (primeArchShiftedReciprocalMoment 1 0).re *
            (primeArchShiftedReciprocalMoment 1 2).re -
          (primeArchShiftedReciprocalMoment 1 1).re ^ 2 := by
  rw [primeArchSuzuki_twoJetSlack_eq_shiftedHankelMinor]
  have hA : 0 < (primeArchShiftedReciprocalMoment 1 0).re :=
    re_primeArchShiftedReciprocalMoment_one_zero_pos
  have hden :
      0 < (primeArchShiftedReciprocalMoment 1 0).re ^ 2 :=
    sq_pos_of_pos hA
  constructor
  · intro h
    have hnum := (le_div_iff₀ hden).mp h
    nlinarith
  · intro h
    apply (le_div_iff₀ hden).2
    nlinarith

end

end RHTower
