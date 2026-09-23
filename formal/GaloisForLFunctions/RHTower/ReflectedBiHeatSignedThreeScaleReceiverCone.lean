import GaloisForLFunctions.RHTower.ReflectedBiHeatSignedTwoScaleReceiverCone
import GaloisForLFunctions.RHTower.ThetaCuspHawkingParikhWilczekQuadraticHalfLineReceiverCone

/-!
# Reflected bi-heat signed three-scale receiver cone

For three commensurate RBH aperture rates, triple-angle factorization turns the signed reporter
into `sinh(t)` times a quadratic in `cosh(t)`.  This file transfers the complete PW-B quadratic
half-line cone to RBH, including the missing converse that a continuous quadratic nonvanishing on
`(1,∞)` must have one strict sign there.

The resulting semialgebraic cone is exact.  It contains the genuinely signed boundary receiver
`sinh(3t) - 3 sinh(t) = 4 sinh(t)^(3 : ℕ)`, and every cone point gives an RH-equivalent physical
three-aperture leading-jet balance.

`[NEW] [CROSS-ROUTE TRANSFER] [SIGNED RECEIVER CONE] [EXACT CLASSIFICATION] [LEAN-PROVED]`
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- A real quadratic is nonzero on `(1,∞)` exactly when it has one strict sign there. -/
theorem quadratic_ne_zero_on_one_iff (a b c : ℝ) :
    (∀ x : ℝ, 1 < x → a * x ^ 2 + b * x + c ≠ 0) ↔
      quadraticPositiveOnOneCondition a b c ∨
        quadraticPositiveOnOneCondition (-a) (-b) (-c) := by
  let q : ℝ → ℝ := fun x => a * x ^ 2 + b * x + c
  have hcont : Continuous q := by
    dsimp [q]
    fun_prop
  constructor
  · intro hne
    have hq2ne : q 2 ≠ 0 := by
      exact hne 2 (by norm_num)
    rcases lt_or_gt_of_ne hq2ne with hq2neg | hq2pos
    · right
      apply (quadratic_pos_on_one_iff (-a) (-b) (-c)).mp
      intro x hx
      have hqxne : q x ≠ 0 := hne x hx
      have hqxneg : q x < 0 := by
        rcases lt_or_gt_of_ne hqxne with hneg | hpos
        · exact hneg
        · exfalso
          rcases lt_trichotomy x 2 with hx2 | hx2 | hx2
          · have hzeroMem : (0 : ℝ) ∈ Set.Ioo (q 2) (q x) := ⟨hq2neg, hpos⟩
            obtain ⟨z, hz, hz0⟩ := intermediate_value_Ioo' hx2.le
              hcont.continuousOn hzeroMem
            exact (hne z (lt_trans hx hz.1)) hz0
          · subst x
            exact (lt_asymm hpos hq2neg).elim
          · have hzeroMem : (0 : ℝ) ∈ Set.Ioo (q 2) (q x) := ⟨hq2neg, hpos⟩
            obtain ⟨z, hz, hz0⟩ := intermediate_value_Ioo hx2.le
              hcont.continuousOn hzeroMem
            exact (hne z (lt_trans (by norm_num) hz.1)) hz0
      dsimp [q] at hqxneg
      linarith
    · left
      apply (quadratic_pos_on_one_iff a b c).mp
      intro x hx
      have hqxne : q x ≠ 0 := hne x hx
      have hqxpos : 0 < q x := by
        rcases lt_or_gt_of_ne hqxne with hneg | hpos
        · exfalso
          rcases lt_trichotomy x 2 with hx2 | hx2 | hx2
          · have hzeroMem : (0 : ℝ) ∈ Set.Ioo (q x) (q 2) := ⟨hneg, hq2pos⟩
            obtain ⟨z, hz, hz0⟩ := intermediate_value_Ioo hx2.le
              hcont.continuousOn hzeroMem
            exact (hne z (lt_trans hx hz.1)) hz0
          · subst x
            exact (lt_asymm hneg hq2pos).elim
          · have hzeroMem : (0 : ℝ) ∈ Set.Ioo (q x) (q 2) := ⟨hneg, hq2pos⟩
            obtain ⟨z, hz, hz0⟩ := intermediate_value_Ioo' hx2.le
              hcont.continuousOn hzeroMem
            exact (hne z (lt_trans (by norm_num) hz.1)) hz0
        · exact hpos
      exact hqxpos
  · rintro (hpos | hneg) x hx
    · exact ne_of_gt ((quadratic_pos_on_one_iff a b c).mpr hpos x hx)
    · have h := (quadratic_pos_on_one_iff (-a) (-b) (-c)).mpr hneg x hx
      nlinarith

/-- Signed three-scale RBH reporter at normalized wall displacement. -/
def reflectedBiHeatSignedThreeScaleReporter (a b c t : ℝ) : ℝ :=
  a * Real.sinh t + b * Real.sinh (2 * t) + c * Real.sinh (3 * t)

/-- Triple-angle factorization into the forced wall zero and a quadratic in `cosh(t)`. -/
theorem reflectedBiHeatSignedThreeScaleReporter_factor (a b c t : ℝ) :
    reflectedBiHeatSignedThreeScaleReporter a b c t =
      Real.sinh t *
        (4 * c * Real.cosh t ^ 2 + 2 * b * Real.cosh t + (a - c)) := by
  rw [reflectedBiHeatSignedThreeScaleReporter, Real.sinh_two_mul,
    Real.sinh_three_mul, Real.cosh_sq]
  ring

/-- Exact semialgebraic cone for wall-selective signed three-scale reporters. -/
def ReflectedBiHeatSignedThreeScaleWallSelective (a b c : ℝ) : Prop :=
  quadraticPositiveOnOneCondition (4 * c) (2 * b) (a - c) ∨
    quadraticPositiveOnOneCondition (-(4 * c)) (-(2 * b)) (-(a - c))

/-- Exact transfer of quadratic half-line nonvanishing to three-scale RBH wall selectivity. -/
theorem reflectedBiHeatSignedThreeScaleWallSelective_iff
    (a b c : ℝ) :
    ReflectedBiHeatSignedThreeScaleWallSelective a b c ↔
      ∀ t : ℝ,
        reflectedBiHeatSignedThreeScaleReporter a b c t = 0 ↔ t = 0 := by
  rw [ReflectedBiHeatSignedThreeScaleWallSelective,
    ← quadratic_ne_zero_on_one_iff]
  constructor
  · intro hquad t
    rw [reflectedBiHeatSignedThreeScaleReporter_factor]
    constructor
    · intro hzero
      rcases mul_eq_zero.mp hzero with hsinh | hquadzero
      · exact Real.sinh_eq_zero.mp hsinh
      · by_contra ht
        exact hquad (Real.cosh t) (Real.one_lt_cosh.mpr ht) hquadzero
    · rintro rfl
      simp
  · intro hselect u hu hqu
    let t := Real.arcosh u
    have ht : 0 < t := Real.arcosh_pos hu
    have hcosh : Real.cosh t = u := Real.cosh_arcosh hu.le
    have hzero : reflectedBiHeatSignedThreeScaleReporter a b c t = 0 := by
      rw [reflectedBiHeatSignedThreeScaleReporter_factor, hcosh, hqu, mul_zero]
    exact ht.ne' ((hselect t).mp hzero)

/-- Every positive integer-power aperture has the same nonzero coefficient and one hyperbolic
frequency after the canonical `x^(n/2)` normalization. -/
theorem reflectedBiHeatWeightedPowerApertureGap_eq_sinh
    (n : ℕ) {x : ℝ} (hx : 0 < x) (rho : XiDivisorSupport) :
    x ^ ((n : ℝ) / 2) *
        (reflectedBiHeatLeftLeadingJetNorm rho (x ^ n) ^ 2 -
          reflectedBiHeatRightLeadingJetNorm rho (x ^ n) ^ 2) =
      2 * ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2 *
        Real.sinh ((n : ℝ) *
          (Real.log x * ((rho : ℂ).re - 1 / 2))) := by
  have hxn : 0 < x ^ n := pow_pos hx n
  rw [reflectedBiHeatLeftLeadingJetNorm_eq rho hxn,
    reflectedBiHeatRightLeadingJetNorm_eq rho hxn]
  simp only [reflectedBiHeatLeftScaleOrder, reflectedBiHeatRightScaleOrder]
  rw [Real.rpow_def_of_pos hx,
    Real.rpow_def_of_pos hxn, Real.rpow_def_of_pos hxn,
    Real.log_pow, Real.sinh_eq]
  let r : ℝ := (rho : ℂ).re
  let L : ℝ := Real.log x
  let m : ℝ := n
  have h1 : Real.exp (L * (m / 2)) *
      Real.exp ((m * L) * ((r - 1) / 2)) ^ 2 =
      Real.exp (m * (L * (r - 1 / 2))) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    norm_num
    ring
  have h2 : Real.exp (L * (m / 2)) *
      Real.exp ((m * L) * (-r / 2)) ^ 2 =
      Real.exp (-(m * (L * (r - 1 / 2)))) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    norm_num
    ring
  change
    Real.exp (L * (m / 2)) *
        ((‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ *
            Real.exp ((m * L) * ((r - 1) / 2))) ^ 2 -
          (‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ *
            Real.exp ((m * L) * (-r / 2))) ^ 2) =
      2 * ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2 *
        ((Real.exp (m * (L * (r - 1 / 2))) -
          Real.exp (-(m * (L * (r - 1 / 2))))) / 2)
  simp only [mul_pow]
  linear_combination
    ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2 * h1 -
    ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2 * h2

/-- Physical signed gap at the three commensurate apertures `x`, `x²`, and `x³`. -/
def reflectedBiHeatSignedThreeApertureGap
    (a b c x : ℝ) (rho : XiDivisorSupport) : ℝ :=
  a * (x ^ ((1 : ℝ) / 2) *
      (reflectedBiHeatLeftLeadingJetNorm rho (x ^ 1) ^ 2 -
        reflectedBiHeatRightLeadingJetNorm rho (x ^ 1) ^ 2)) +
    b * (x *
      (reflectedBiHeatLeftLeadingJetNorm rho (x ^ 2) ^ 2 -
        reflectedBiHeatRightLeadingJetNorm rho (x ^ 2) ^ 2)) +
    c * (x ^ ((3 : ℝ) / 2) *
      (reflectedBiHeatLeftLeadingJetNorm rho (x ^ 3) ^ 2 -
        reflectedBiHeatRightLeadingJetNorm rho (x ^ 3) ^ 2))

/-- Exact physical three-aperture factorization. -/
theorem reflectedBiHeatSignedThreeApertureGap_eq_reporter
    (a b c : ℝ) {x : ℝ} (hx : 0 < x) (rho : XiDivisorSupport) :
    reflectedBiHeatSignedThreeApertureGap a b c x rho =
      2 * ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2 *
        reflectedBiHeatSignedThreeScaleReporter a b c
          (Real.log x * ((rho : ℂ).re - 1 / 2)) := by
  have h1 := reflectedBiHeatWeightedPowerApertureGap_eq_sinh 1 hx rho
  have h2 := reflectedBiHeatWeightedPowerApertureGap_eq_sinh 2 hx rho
  have h3 := reflectedBiHeatWeightedPowerApertureGap_eq_sinh 3 hx rho
  norm_num at h1 h2 h3
  rw [reflectedBiHeatSignedThreeApertureGap,
    reflectedBiHeatSignedThreeScaleReporter]
  simp only [pow_one]
  linear_combination a * h1 + b * h2 + c * h3

/-- The complete three-scale cone gives physical balance exactly on the critical wall. -/
theorem reflectedBiHeatSignedThreeApertureGap_eq_zero_iff
    {a b c : ℝ} (hcone : ReflectedBiHeatSignedThreeScaleWallSelective a b c)
    {x : ℝ} (hx : 1 < x) (rho : XiDivisorSupport) :
    reflectedBiHeatSignedThreeApertureGap a b c x rho = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [reflectedBiHeatSignedThreeApertureGap_eq_reporter a b c
    (lt_trans zero_lt_one hx) rho]
  have hcoef :
      2 * ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2 ≠ 0 := by
    exact mul_ne_zero (by norm_num)
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr
        (reflectedBiHeatMultiplicityLeadingCoefficient_ne_zero rho)))
  constructor
  · intro hzero
    have hreport : reflectedBiHeatSignedThreeScaleReporter a b c
        (Real.log x * ((rho : ℂ).re - 1 / 2)) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hcoef
    have hu :=
      ((reflectedBiHeatSignedThreeScaleWallSelective_iff a b c).mp hcone
        (Real.log x * ((rho : ℂ).re - 1 / 2))).mp hreport
    have hlog : 0 < Real.log x := Real.log_pos hx
    have hsub : (rho : ℂ).re - 1 / 2 = 0 :=
      (mul_eq_zero.mp hu).resolve_left hlog.ne'
    exact sub_eq_zero.mp hsub
  · intro hre
    rw [hre, sub_self, mul_zero]
    simp [reflectedBiHeatSignedThreeScaleReporter]

/-- Every triple in the exact signed three-scale cone supplies an RH-equivalent receiver. -/
theorem riemannHypothesis_iff_reflectedBiHeatSignedThreeApertureGap_eq_zero
    {a b c : ℝ} (hcone : ReflectedBiHeatSignedThreeScaleWallSelective a b c)
    {x : ℝ} (hx : 1 < x) :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport,
        reflectedBiHeatSignedThreeApertureGap a b c x rho = 0 := by
  constructor
  · intro hRH rho
    exact (reflectedBiHeatSignedThreeApertureGap_eq_zero_iff hcone hx rho).mpr
      (xi_divisor_support_re_eq_half_of_rh hRH rho)
  · intro h
    exact riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho =>
      (reflectedBiHeatSignedThreeApertureGap_eq_zero_iff hcone hx rho).mp (h rho)

/-- Cubic boundary receiver `sinh(3t)-3sinh(t)=4sinh(t)^(3 : ℕ)`. -/
theorem reflectedBiHeatSignedThreeScaleWallSelective_neg_three_zero_one :
    ReflectedBiHeatSignedThreeScaleWallSelective (-3) 0 1 := by
  left
  norm_num [ReflectedBiHeatSignedThreeScaleWallSelective,
    quadraticPositiveOnOneCondition]

/-- The genuinely three-scale signed boundary ray `(-3,0,1)` is an exact RH receiver. -/
theorem riemannHypothesis_iff_reflectedBiHeatSignedNegThreeZeroOneApertureGap_eq_zero
    {x : ℝ} (hx : 1 < x) :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport,
        reflectedBiHeatSignedThreeApertureGap (-3) 0 1 x rho = 0 :=
  riemannHypothesis_iff_reflectedBiHeatSignedThreeApertureGap_eq_zero
    reflectedBiHeatSignedThreeScaleWallSelective_neg_three_zero_one hx

end

end RHTower
