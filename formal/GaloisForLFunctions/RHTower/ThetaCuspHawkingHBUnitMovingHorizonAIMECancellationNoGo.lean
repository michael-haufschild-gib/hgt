import GaloisForLFunctions.RHTower.ThetaCuspHawkingEventHorizonThirdMassAIMEAntialignment

/-!
# HB unit moving-horizon/AIME cancellation no-go

The exact moving-event-horizon third mass defect and theta-mirror AIME chiral defect have opposite
orientation, but their physical unit-normalized magnitudes do not match.  Write

`A = a(3-a)`, `B = (1-a)(2+a)`, `a = Re rho`,

and let `N = A²(2-B) + B²(2-A) + 2AB` be the exact third-mass cross numerator.  The corpus
susceptibility has the closed form

`S = 54 N (2-a)(a+1)/(A²B²)`.

Every Xi copy has `0<a<1` and `0<A,B<2`.  Therefore `N>2AB`,
`(2-a)(a+1)>2`, and `AB<4`, which force `S>54`.  In particular, the unit AIME coefficient cannot
equal the unique coefficient required to cancel the moving-horizon defect on any tilted fibre.

Consequently the literal unit sum vanishes exactly on the critical line, and its universal
extinction is equivalent to RH.  This kills the concrete HB escape in which the moving-horizon
third mass channel alone supplies the unit-normalized radiative `++` counterterm.  A survivor must
derive a genuinely amplified, fibre-adaptive coefficient or use another non-AIME third-order
cokernel channel.

`[NEW] [HB] [THIRD ORDER] [AIME] [UNIT NORMALIZATION] [ROUTE KILL] [LEAN-PROVED]`
-/

open Complex

namespace RHTower

noncomputable section

/-- Structural magnitude gap: the exact coefficient required for third-mass/AIME cancellation is
larger than `54` on every Xi copy. -/
theorem d4BMXiEventHorizonThirdMassToAIMEChiralSusceptibility_gt_fiftyFour
    (q : XiZeroCopy) :
    54 < d4BMXiEventHorizonThirdMassToAIMEChiralSusceptibility q := by
  let a : ℝ := (q.1 : ℂ).re
  let A : ℝ := d4BMXiHorizonAngularShift q
  let B : ℝ := d4BMXiHorizonAngularShift (xiZeroCopyReflectEquiv q)
  let N : ℝ := d4EventHorizonThirdMassParityCrossNumerator A B
  let C : ℝ := (2 - a) * (a + 1)
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  have ha0 : 0 < a := by simpa [a] using hstrip.1
  have ha1 : a < 1 := by simpa [a] using hstrip.2
  have hA0 : 0 < A := by
    simpa [A] using d4BMXiHorizonAngularShift_pos q
  have hA2 : A < 2 := by
    simpa [A] using d4BMXiHorizonAngularShift_lt_two q
  have hB0 : 0 < B := by
    simpa [B] using d4BMXiHorizonAngularShift_pos (xiZeroCopyReflectEquiv q)
  have hB2 : B < 2 := by
    simpa [B] using
      d4BMXiHorizonAngularShift_lt_two (xiZeroCopyReflectEquiv q)
  have hAeq : A = a * (3 - a) := by
    simpa [A, a] using d4BMXiHorizonAngularShift_eq q
  have hBeq : B = (1 - a) * (2 + a) := by
    simpa [B, a] using d4BMXiHorizonAngularShift_reflect_eq q
  have hNgt : 2 * A * B < N := by
    have hleft : 0 < A ^ 2 * (2 - B) :=
      mul_pos (sq_pos_of_pos hA0) (sub_pos.mpr hB2)
    have hright : 0 < B ^ 2 * (2 - A) :=
      mul_pos (sq_pos_of_pos hB0) (sub_pos.mpr hA2)
    unfold N d4EventHorizonThirdMassParityCrossNumerator
    linarith
  have hCgt : 2 < C := by
    have hpositive : 0 < a * (1 - a) :=
      mul_pos ha0 (sub_pos.mpr ha1)
    dsimp [C]
    nlinarith
  have hAB0 : 0 < A * B := mul_pos hA0 hB0
  have hABlt : A * B < 4 := by
    have h := mul_lt_mul hA2 (le_of_lt hB2) hB0 (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at h ⊢
    exact h
  have hden : 0 < A ^ 2 * B ^ 2 :=
    mul_pos (sq_pos_of_pos hA0) (sq_pos_of_pos hB0)
  have hden_lt_fourAB : A ^ 2 * B ^ 2 < 4 * (A * B) := by
    nlinarith [mul_pos hAB0 (sub_pos.mpr hABlt)]
  have hfourAB_lt_NC : 4 * (A * B) < N * C := by
    have hNdiff : 0 < N - 2 * A * B := sub_pos.mpr hNgt
    have hCdiff : 0 < C - 2 := sub_pos.mpr hCgt
    have hC0 : 0 < C := by linarith
    nlinarith [mul_pos hNdiff hC0,
      mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) hAB0) hCdiff]
  have hcore : A ^ 2 * B ^ 2 < N * C :=
    lt_trans hden_lt_fourAB hfourAB_lt_NC
  have hformula :
      d4BMXiEventHorizonThirdMassToAIMEChiralSusceptibility q =
        54 * N * C / (A ^ 2 * B ^ 2) := by
    have hAne : A ≠ 0 := ne_of_gt hA0
    have hBne : B ≠ 0 := ne_of_gt hB0
    unfold d4BMXiEventHorizonThirdMassToAIMEChiralSusceptibility
      d4BMXiEventHorizonThirdMassReflectionSusceptibility
      d4BMXiThetaMirrorAIMEDenominator
    change
      (648 * N / (A ^ 3 * B ^ 3)) *
          (a * (1 - a) * (2 - a) * (3 - a) * (a + 1) * (a + 2)) / 12 =
        54 * N * C / (A ^ 2 * B ^ 2)
    rw [hAeq, hBeq]
    dsimp [C]
    field_simp [hAne, hBne]
    ring
  rw [hformula, lt_div_iff₀ hden]
  nlinarith

/-- Literal unit-normalized sum of moving-horizon third-mass and AIME reflection defects. -/
def d4BMXiUnitMovingHorizonThirdMassAIMEChiralDefect (q : XiZeroCopy) : ℝ :=
  d4BMXiEventHorizonThirdMassParityJetDefect q +
    d4BMXiThetaMirrorAIMEChiralKernelDefect q

/-- Unit normalization cannot realize the unique amplified counterterm off line: the literal sum
vanishes exactly at critical-line incidence. -/
theorem d4BMXiUnitMovingHorizonThirdMassAIMEChiralDefect_eq_zero_iff
    (q : XiZeroCopy) :
    d4BMXiUnitMovingHorizonThirdMassAIMEChiralDefect q = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  constructor
  · intro hzero
    by_contra htilt
    have hcoefficient :=
      (d4BMXiEventHorizonThirdMass_add_coefficient_mul_AIME_eq_zero_iff
        q htilt 1).mp
        (by simpa [d4BMXiUnitMovingHorizonThirdMassAIMEChiralDefect] using hzero)
    have hgap :=
      d4BMXiEventHorizonThirdMassToAIMEChiralSusceptibility_gt_fiftyFour q
    linarith
  · intro hline
    have hmass : d4BMXiEventHorizonThirdMassParityJetDefect q = 0 :=
      (d4BMXiEventHorizonThirdMassParityJetDefect_eq_zero_iff q).2 hline
    have haime : d4BMXiThetaMirrorAIMEChiralKernelDefect q = 0 := by
      by_contra hne
      exact ((d4BMXiThetaMirrorAIMEChiralKernelDefect_ne_zero_iff q).1 hne) hline
    simp [d4BMXiUnitMovingHorizonThirdMassAIMEChiralDefect, hmass, haime]

/-- Every tilted Xi fibre retains a nonzero unit-normalized third-mass/AIME defect. -/
theorem d4BMXiUnitMovingHorizonThirdMassAIMEChiralDefect_ne_zero_of_tilt
    (q : XiZeroCopy) (htilt : (q.1 : ℂ).re ≠ 1 / 2) :
    d4BMXiUnitMovingHorizonThirdMassAIMEChiralDefect q ≠ 0 :=
  (not_congr
    (d4BMXiUnitMovingHorizonThirdMassAIMEChiralDefect_eq_zero_iff q)).2 htilt

/-- Universal extinction of the literal unit sum is exactly RH, so this counterterm is a receiver,
not an unconditional source producer. -/
theorem forall_d4BMXiUnitMovingHorizonThirdMassAIMEChiralDefect_eq_zero_iff_rh :
    (∀ q : XiZeroCopy,
      d4BMXiUnitMovingHorizonThirdMassAIMEChiralDefect q = 0) ↔
      RiemannHypothesis := by
  constructor
  · intro hall
    apply (forall_d4BMXiEventHorizonThirdMassParityJetDefect_eq_zero_iff_rh).1
    intro q
    apply (d4BMXiEventHorizonThirdMassParityJetDefect_eq_zero_iff q).2
    exact (d4BMXiUnitMovingHorizonThirdMassAIMEChiralDefect_eq_zero_iff q).1 (hall q)
  · intro hRH q
    apply (d4BMXiUnitMovingHorizonThirdMassAIMEChiralDefect_eq_zero_iff q).2
    have hmass :=
      (forall_d4BMXiEventHorizonThirdMassParityJetDefect_eq_zero_iff_rh).2 hRH q
    exact (d4BMXiEventHorizonThirdMassParityJetDefect_eq_zero_iff q).1 hmass

/-- Closed route class: unit-normalized moving-horizon third mass response cannot be the missing
HB AIME/radiative `++` counterterm. -/
def D4HBUnitMovingHorizonAIMECancellationRouteKilled : Prop :=
  (∀ q : XiZeroCopy,
    54 < d4BMXiEventHorizonThirdMassToAIMEChiralSusceptibility q) ∧
  (∀ q : XiZeroCopy,
    d4BMXiUnitMovingHorizonThirdMassAIMEChiralDefect q = 0 ↔
      (q.1 : ℂ).re = 1 / 2) ∧
  ((∀ q : XiZeroCopy,
      d4BMXiUnitMovingHorizonThirdMassAIMEChiralDefect q = 0) ↔
    RiemannHypothesis)

/-- Premise-free certificate killing unit moving-horizon/AIME cancellation as an HB producer. -/
theorem d4HBUnitMovingHorizonAIMECancellationRouteKilled :
    D4HBUnitMovingHorizonAIMECancellationRouteKilled := by
  exact ⟨d4BMXiEventHorizonThirdMassToAIMEChiralSusceptibility_gt_fiftyFour,
    d4BMXiUnitMovingHorizonThirdMassAIMEChiralDefect_eq_zero_iff,
    forall_d4BMXiUnitMovingHorizonThirdMassAIMEChiralDefect_eq_zero_iff_rh⟩

end

end RHTower
