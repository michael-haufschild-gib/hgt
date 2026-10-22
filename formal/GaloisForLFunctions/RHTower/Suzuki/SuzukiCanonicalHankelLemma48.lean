import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelLemma47

/-!
# Suzuki (2012), Lemma 4.8: meromorphic Fredholm functions and pole clearing

This module formalizes the continuation-theoretic content of Lemma 4.8.  A quotient of entire
functions is represented in Lean by total division, so its value at a pole is not the value of its
meromorphic germ.  Accordingly, the source's statement that multiplication by
`xi(1/2 + omega - i z)` is entire is expressed by an explicit entire cleared numerator together
with equality on the denominator's regular locus.  This is the literal meaning of pole clearing;
no value is silently assigned at a pole.
-/

open Complex Real MeasureTheory Set

noncomputable section

namespace RHTower


attribute [local instance] Measure.Subtype.measureSpace

/-- The coefficient `sqrt(a)/2` in Suzuki's equation (4.20). -/
def suzukiHankelTildeCoefficient (a : ℝ) : ℂ :=
  ((Real.sqrt a / 2 : ℝ) : ℂ)

/-- The elementary term `a^(i z)`, written with its entire exponential representative. -/
def suzukiHankelAiz (a : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (I * z * (Real.log a : ℂ))

/-- The original upper-half-plane definition of `tilde E_a` in equation (4.20). -/
def suzukiHankelTildeE
    (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) (z : ℂ) : ℂ :=
  suzukiHankelAiz a z +
    suzukiHankelTildeCoefficient a * suzukiHankelPsi omega a homega ha z

/-- Meromorphic continuation of `tilde E_a`, obtained from Lemma 4.7. -/
def suzukiHankelTildeEContinuation
    (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) (z : ℂ) : ℂ :=
  suzukiHankelAiz a z +
    suzukiHankelTildeCoefficient a *
      suzukiHankelPsiContinuation omega a homega ha z

/-- Entire compact-transform part of `tilde E_a`. -/
def suzukiHankelTildeERegularPart
    (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) (z : ℂ) : ℂ :=
  suzukiHankelAiz a z + suzukiHankelTildeCoefficient a *
    suzukiCompactL2Fourier (Real.log a)
      (suzukiHankelPhiSumHankelLog omega a homega ha) z

/-- Entire coefficient of `Theta_omega` in `tilde E_a`. -/
def suzukiHankelTildeEThetaPart
    (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) (z : ℂ) : ℂ :=
  -suzukiHankelTildeCoefficient a *
    suzukiCompactL2Fourier (Real.log a)
      (suzukiHankelPhiSumLog omega a homega ha) (-z)

theorem suzukiHankelTildeEContinuation_eq_regular_add_theta
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    suzukiHankelTildeEContinuation omega a homega ha z =
      suzukiHankelTildeERegularPart omega a homega ha z +
        suzukiCanonicalTheta omega z *
          suzukiHankelTildeEThetaPart omega a homega ha z := by
  rw [suzukiHankelTildeEContinuation, suzukiHankelPsiContinuation,
    suzukiHankelTildeERegularPart, suzukiHankelTildeEThetaPart]
  ring

/-- Explicit pole-aware continuation of `tilde E_a^*`.  This is the
`entire + Theta_omega * entire` form obtained in Suzuki's proof. -/
def suzukiHankelTildeEStarContinuation
    (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) (z : ℂ) : ℂ :=
  -suzukiHankelTildeCoefficient a *
      suzukiCompactL2Fourier (Real.log a)
        (suzukiHankelPhiSumLog omega a homega ha) z +
    suzukiCanonicalTheta omega z *
      (suzukiHankelAiz a (-z) + suzukiHankelTildeCoefficient a *
        suzukiCompactL2Fourier (Real.log a)
          (suzukiHankelPhiSumHankelLog omega a homega ha) (-z))

theorem differentiable_suzukiHankelAiz (a : ℝ) :
    Differentiable ℂ (suzukiHankelAiz a) := by
  unfold suzukiHankelAiz
  fun_prop

theorem differentiable_suzukiHankelTildeERegularPart
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    Differentiable ℂ (suzukiHankelTildeERegularPart omega a homega ha) := by
  have hA : 0 ≤ Real.log a := (Real.log_pos ha).le
  exact (differentiable_suzukiHankelAiz a).add
    ((differentiable_suzukiCompactL2Fourier hA _).const_mul
      (suzukiHankelTildeCoefficient a))

theorem differentiable_suzukiHankelTildeEThetaPart
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    Differentiable ℂ (suzukiHankelTildeEThetaPart omega a homega ha) := by
  have hA : 0 ≤ Real.log a := (Real.log_pos ha).le
  exact ((differentiable_suzukiCompactL2Fourier hA _).comp (by fun_prop)).const_mul
    (-suzukiHankelTildeCoefficient a)

/-- `tilde E_a` agrees with its continuation throughout the strict upper half-plane. -/
theorem suzukiHankelTildeE_eq_continuation
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a)
    {z : ℂ} (hz : 0 < z.im) :
    suzukiHankelTildeE omega a homega ha z =
      suzukiHankelTildeEContinuation omega a homega ha z := by
  rw [suzukiHankelTildeE, suzukiHankelTildeEContinuation,
    suzuki2012_equation_four_two_two_one homega ha hz]

/-- `tilde E_a` has a meromorphic continuation to the whole plane. -/
theorem meromorphicOn_suzukiHankelTildeEContinuation
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    MeromorphicOn (suzukiHankelTildeEContinuation omega a homega ha) Set.univ := by
  rw [show suzukiHankelTildeEContinuation omega a homega ha = fun z =>
      suzukiHankelTildeERegularPart omega a homega ha z +
        suzukiCanonicalTheta omega z *
          suzukiHankelTildeEThetaPart omega a homega ha z by
    funext z
    exact suzukiHankelTildeEContinuation_eq_regular_add_theta homega ha z]
  exact (differentiable_suzukiHankelTildeERegularPart homega ha).differentiableOn
      |>.analyticOnNhd isOpen_univ |>.meromorphicOn |>.add
    ((meromorphicOn_suzukiCanonicalTheta omega).mul
      ((differentiable_suzukiHankelTildeEThetaPart homega ha).differentiableOn
        |>.analyticOnNhd isOpen_univ |>.meromorphicOn))

/-- `tilde E_a` is analytic in the strict upper half-plane. -/
theorem analyticOnNhd_suzukiHankelTildeEContinuation
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    AnalyticOnNhd ℂ (suzukiHankelTildeEContinuation omega a homega ha)
      suzukiUpperHalfPlane := by
  rw [show suzukiHankelTildeEContinuation omega a homega ha = fun z =>
      suzukiHankelTildeERegularPart omega a homega ha z +
        suzukiCanonicalTheta omega z *
          suzukiHankelTildeEThetaPart omega a homega ha z by
    funext z
    exact suzukiHankelTildeEContinuation_eq_regular_add_theta homega ha z]
  exact ((differentiable_suzukiHankelTildeERegularPart homega ha).differentiableOn
      |>.analyticOnNhd isOpen_univ |>.mono (subset_univ _)).add
    (((suzukiCanonicalTheta_meromorphicInner_of_half_lt (by linarith)).2.1).mul
      ((differentiable_suzukiHankelTildeEThetaPart homega ha).differentiableOn
        |>.analyticOnNhd isOpen_univ |>.mono (subset_univ _)))

/-- The explicit continuation of `tilde E_a^*` is meromorphic on the whole plane. -/
theorem meromorphicOn_suzukiHankelTildeEStarContinuation
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    MeromorphicOn
      (suzukiHankelTildeEStarContinuation omega a homega ha) Set.univ := by
  have hA : 0 ≤ Real.log a := (Real.log_pos ha).le
  have hleft : Differentiable ℂ (fun z : ℂ =>
      -suzukiHankelTildeCoefficient a *
        suzukiCompactL2Fourier (Real.log a)
          (suzukiHankelPhiSumLog omega a homega ha) z) :=
    (differentiable_suzukiCompactL2Fourier hA _).const_mul
      (-suzukiHankelTildeCoefficient a)
  have hright : Differentiable ℂ (fun z : ℂ =>
      suzukiHankelAiz a (-z) + suzukiHankelTildeCoefficient a *
        suzukiCompactL2Fourier (Real.log a)
          (suzukiHankelPhiSumHankelLog omega a homega ha) (-z)) :=
    ((differentiable_suzukiHankelAiz a).comp (by fun_prop)).add
      (((differentiable_suzukiCompactL2Fourier hA _).comp (by fun_prop)).const_mul
        (suzukiHankelTildeCoefficient a))
  unfold suzukiHankelTildeEStarContinuation
  exact hleft.differentiableOn.analyticOnNhd isOpen_univ |>.meromorphicOn |>.add
    ((meromorphicOn_suzukiCanonicalTheta omega).mul
      (hright.differentiableOn.analyticOnNhd isOpen_univ).meromorphicOn)

/-- The explicit continuation of `tilde E_a^*` is analytic in the strict upper half-plane. -/
theorem analyticOnNhd_suzukiHankelTildeEStarContinuation
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    AnalyticOnNhd ℂ
      (suzukiHankelTildeEStarContinuation omega a homega ha)
      suzukiUpperHalfPlane := by
  have hA : 0 ≤ Real.log a := (Real.log_pos ha).le
  have hleft : Differentiable ℂ (fun z : ℂ =>
      -suzukiHankelTildeCoefficient a *
        suzukiCompactL2Fourier (Real.log a)
          (suzukiHankelPhiSumLog omega a homega ha) z) :=
    (differentiable_suzukiCompactL2Fourier hA _).const_mul
      (-suzukiHankelTildeCoefficient a)
  have hright : Differentiable ℂ (fun z : ℂ =>
      suzukiHankelAiz a (-z) + suzukiHankelTildeCoefficient a *
        suzukiCompactL2Fourier (Real.log a)
          (suzukiHankelPhiSumHankelLog omega a homega ha) (-z)) :=
    ((differentiable_suzukiHankelAiz a).comp (by fun_prop)).add
      (((differentiable_suzukiCompactL2Fourier hA _).comp (by fun_prop)).const_mul
        (suzukiHankelTildeCoefficient a))
  unfold suzukiHankelTildeEStarContinuation
  exact (hleft.differentiableOn.analyticOnNhd isOpen_univ |>.mono (subset_univ _)).add
    ((suzukiCanonicalTheta_meromorphicInner_of_half_lt (by linarith)).2.1.mul
      (hright.differentiableOn.analyticOnNhd isOpen_univ |>.mono (subset_univ _)))

/-- Suzuki's functional equation for the two continued Fredholm functions, on the regular locus
of both quotient factors.  This is pointwise content of the global meromorphic identity. -/
theorem suzukiHankelTildeEStarContinuation_eq_theta_mul_neg
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a)
    (z : ℂ) (hz : suzukiCanonicalE omega z ≠ 0)
    (hneg : suzukiCanonicalE omega (-z) ≠ 0) :
    suzukiHankelTildeEStarContinuation omega a homega ha z =
      suzukiCanonicalTheta omega z *
        suzukiHankelTildeEContinuation omega a homega ha (-z) := by
  rw [suzukiHankelTildeEStarContinuation,
    suzukiHankelTildeEContinuation_eq_regular_add_theta homega ha]
  rw [suzukiHankelTildeERegularPart, suzukiHankelTildeEThetaPart]
  have htheta := suzukiCanonicalTheta_mul_neg_eq_one omega z hz hneg
  simp only [neg_neg] at htheta ⊢
  calc
    _ = suzukiCanonicalTheta omega z *
          (suzukiHankelAiz a (-z) + suzukiHankelTildeCoefficient a *
            suzukiCompactL2Fourier (Real.log a)
              (suzukiHankelPhiSumHankelLog omega a homega ha) (-z)) +
        1 * (-suzukiHankelTildeCoefficient a *
          suzukiCompactL2Fourier (Real.log a)
            (suzukiHankelPhiSumLog omega a homega ha) z) := by ring
    _ = suzukiCanonicalTheta omega z *
          (suzukiHankelAiz a (-z) + suzukiHankelTildeCoefficient a *
            suzukiCompactL2Fourier (Real.log a)
              (suzukiHankelPhiSumHankelLog omega a homega ha) (-z)) +
        (suzukiCanonicalTheta omega z * suzukiCanonicalTheta omega (-z)) *
          (-suzukiHankelTildeCoefficient a *
            suzukiCompactL2Fourier (Real.log a)
              (suzukiHankelPhiSumLog omega a homega ha) z) := by rw [htheta]
    _ = _ := by ring

/-- **Suzuki (2012), equation (4.24), literal pointwise kernel form.**  The Hankel transform of
the compact Fredholm difference is `2 h_omega(a x)` minus the global Fredholm sum. -/
theorem suzuki2012_equation_four_two_four
    {omega a x : ℝ} (homega : 1 < omega) (ha : 1 < a) (hx : 0 < x) :
    (∫ y : ClosedInterval 0 a,
        suzukiSourceHFinite omega (x * (y : ℝ)) *
          (suzukiHankelPhi SuzukiHankelSign.positive omega a (by linarith) ha -
            suzukiHankelPhi SuzukiHankelSign.negative omega a (by linarith) ha) y ∂volume) =
      2 * suzukiSourceHFinite omega (a * x) -
        suzukiHankelPhiGlobal SuzukiHankelSign.positive omega a homega ha x -
        suzukiHankelPhiGlobal SuzukiHankelSign.negative omega a homega ha x := by
  let B : ℝ := max a x + 1
  have hB : 1 < B := by
    dsimp only [B]
    linarith [le_max_left a x]
  have haB : a ≤ B := by
    dsimp only [B]
    linarith [le_max_left a x]
  have hxB : x ≤ B := by
    dsimp only [B]
    linarith [le_max_right a x]
  let p : IntervalL2 0 a :=
    suzukiHankelPhi SuzukiHankelSign.positive omega a (by linarith) ha
  let m : IntervalL2 0 a :=
    suzukiHankelPhi SuzukiHankelSign.negative omega a (by linarith) ha
  let row : IntervalL2 0 a :=
    suzukiPhysicalIntervalRestrictionBetween a B
      (suzukiCompressedHankelRow omega B (by linarith) hB x)
  have hp := suzukiRestrictedLargeRow_pairing_eq_integral
    (show 1 / 2 < omega by linarith) (show 0 < a by linarith)
      hB haB hx hxB p
  have hm := suzukiRestrictedLargeRow_pairing_eq_integral
    (show 1 / 2 < omega by linarith) (show 0 < a by linarith)
      hB haB hx hxB m
  have hd := suzukiRestrictedLargeRow_pairing_eq_integral
    (show 1 / 2 < omega by linarith) (show 0 < a by linarith)
      hB haB hx hxB (p - m)
  change (∫ y : ClosedInterval 0 a,
      suzukiSourceHFinite omega (x * (y : ℝ)) * (p - m) y ∂volume) = _
  rw [suzukiHankelPhiGlobal, suzukiHankelPhiGlobal]
  rw [← hp, ← hm, ← hd]
  change (complexMulBilinear.lpPairing volume 2 2) row (p - m) = _
  rw [map_sub]
  dsimp only [row]
  simp only [SuzukiHankelSign.coeff_positive,
    SuzukiHankelSign.coeff_negative]
  ring

/-- Canonical entire numerator clearing the poles of `tilde E_a`. -/
def suzukiHankelTildeECleared
    (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) (z : ℂ) : ℂ :=
  suzukiCanonicalE omega z *
      suzukiHankelTildeERegularPart omega a homega ha z +
    suzukiCanonicalE omega (-z) *
      suzukiHankelTildeEThetaPart omega a homega ha z

/-- Canonical entire numerator clearing the poles of `tilde E_a^*`. -/
def suzukiHankelTildeEStarCleared
    (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) (z : ℂ) : ℂ :=
  suzukiCanonicalE omega z *
      (-suzukiHankelTildeCoefficient a *
        suzukiCompactL2Fourier (Real.log a)
          (suzukiHankelPhiSumLog omega a homega ha) z) +
    suzukiCanonicalE omega (-z) *
      (suzukiHankelAiz a (-z) + suzukiHankelTildeCoefficient a *
        suzukiCompactL2Fourier (Real.log a)
          (suzukiHankelPhiSumHankelLog omega a homega ha) (-z))

theorem differentiable_suzukiHankelTildeECleared
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    Differentiable ℂ (suzukiHankelTildeECleared omega a homega ha) := by
  unfold suzukiHankelTildeECleared
  exact (differentiable_suzukiCanonicalE omega).mul
      (differentiable_suzukiHankelTildeERegularPart homega ha) |>.add
    (((differentiable_suzukiCanonicalE omega).comp (by fun_prop)).mul
      (differentiable_suzukiHankelTildeEThetaPart homega ha))

theorem differentiable_suzukiHankelTildeEStarCleared
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    Differentiable ℂ (suzukiHankelTildeEStarCleared omega a homega ha) := by
  have hA : 0 ≤ Real.log a := (Real.log_pos ha).le
  unfold suzukiHankelTildeEStarCleared
  exact ((differentiable_suzukiCanonicalE omega).mul
      ((differentiable_suzukiCompactL2Fourier hA _).const_mul
        (-suzukiHankelTildeCoefficient a))).add
    (((differentiable_suzukiCanonicalE omega).comp (by fun_prop)).mul
      (((differentiable_suzukiHankelAiz a).comp (by fun_prop)).add
        (((differentiable_suzukiCompactL2Fourier hA _).comp (by fun_prop)).const_mul
          (suzukiHankelTildeCoefficient a))))

/-- On every regular point, the entire cleared numerator is exactly
`xi(1/2+omega-iz) * tilde E_a(z)`. -/
theorem suzukiHankelTildeECleared_eq_E_mul
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a)
    (z : ℂ) (hz : suzukiCanonicalE omega z ≠ 0) :
    suzukiHankelTildeECleared omega a homega ha z =
      suzukiCanonicalE omega z *
        suzukiHankelTildeEContinuation omega a homega ha z := by
  rw [suzukiHankelTildeECleared,
    suzukiHankelTildeEContinuation_eq_regular_add_theta homega ha,
    suzukiCanonicalTheta_eq_E_neg_div_E]
  field_simp

/-- On every regular point, the second entire cleared numerator is exactly
`xi(1/2+omega-iz) * tilde E_a^*(z)`. -/
theorem suzukiHankelTildeEStarCleared_eq_E_mul
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a)
    (z : ℂ) (hz : suzukiCanonicalE omega z ≠ 0) :
    suzukiHankelTildeEStarCleared omega a homega ha z =
      suzukiCanonicalE omega z *
        suzukiHankelTildeEStarContinuation omega a homega ha z := by
  rw [suzukiHankelTildeEStarCleared,
    suzukiHankelTildeEStarContinuation,
    suzukiCanonicalTheta_eq_E_neg_div_E]
  field_simp

/-- **Suzuki (2012), Lemma 4.8, closed continuation-and-clearing theorem.** -/
theorem suzuki2012_lemma_four_eight_continuation_and_clearing :
    ∀ (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a),
      MeromorphicOn (suzukiHankelTildeEContinuation omega a homega ha) Set.univ ∧
      MeromorphicOn (suzukiHankelTildeEStarContinuation omega a homega ha) Set.univ ∧
      AnalyticOnNhd ℂ (suzukiHankelTildeEContinuation omega a homega ha)
        suzukiUpperHalfPlane ∧
      AnalyticOnNhd ℂ (suzukiHankelTildeEStarContinuation omega a homega ha)
        suzukiUpperHalfPlane ∧
      (∀ z : ℂ, suzukiCanonicalE omega z ≠ 0 →
        suzukiCanonicalE omega (-z) ≠ 0 →
        suzukiHankelTildeEStarContinuation omega a homega ha z =
          suzukiCanonicalTheta omega z *
            suzukiHankelTildeEContinuation omega a homega ha (-z)) ∧
      Differentiable ℂ (suzukiHankelTildeECleared omega a homega ha) ∧
      Differentiable ℂ (suzukiHankelTildeEStarCleared omega a homega ha) ∧
      (∀ z : ℂ, suzukiCanonicalE omega z ≠ 0 →
        suzukiHankelTildeECleared omega a homega ha z =
          suzukiCanonicalE omega z *
            suzukiHankelTildeEContinuation omega a homega ha z) ∧
      (∀ z : ℂ, suzukiCanonicalE omega z ≠ 0 →
        suzukiHankelTildeEStarCleared omega a homega ha z =
          suzukiCanonicalE omega z *
            suzukiHankelTildeEStarContinuation omega a homega ha z) := by
  intro omega a homega ha
  exact ⟨meromorphicOn_suzukiHankelTildeEContinuation homega ha,
    meromorphicOn_suzukiHankelTildeEStarContinuation homega ha,
    analyticOnNhd_suzukiHankelTildeEContinuation homega ha,
    analyticOnNhd_suzukiHankelTildeEStarContinuation homega ha,
    fun z hz hneg =>
      suzukiHankelTildeEStarContinuation_eq_theta_mul_neg homega ha z hz hneg,
    differentiable_suzukiHankelTildeECleared homega ha,
    differentiable_suzukiHankelTildeEStarCleared homega ha,
    fun z hz => suzukiHankelTildeECleared_eq_E_mul homega ha z hz,
    fun z hz => suzukiHankelTildeEStarCleared_eq_E_mul homega ha z hz⟩

end RHTower
