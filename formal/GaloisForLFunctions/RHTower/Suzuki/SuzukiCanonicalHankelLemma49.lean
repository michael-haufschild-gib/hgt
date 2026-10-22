import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelLemma48Exterior
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCanonicalHankelMuRegularity

/-!
# Suzuki (2012), Lemma 4.9: completed Fredholm parity

This module formalizes equations (4.16), (4.17), (4.20), and Lemma 4.9.  The normalization
`m(a)` is the literal exponential of the real coupling integral, not an arbitrary nonzero scale.
The meromorphic functional equations are stated on the regular locus of Lean's total quotient;
their pole-cleared entire forms hold at every point and therefore retain the full meromorphic
content at poles.
-/

open Complex Real MeasureTheory Set intervalIntegral

noncomputable section

namespace RHTower


/-! ## The literal normalization `m(a)` from equation (4.17) -/

/-- Real scalar representative of Suzuki's coupling coefficient. -/
def suzukiHankelMuScalar (omega : ℝ) (homega : 1 < omega) (a : ℝ) : ℝ :=
  (suzukiHankelMuReal omega homega a).re

/-- The totalized complex coefficient is exactly the real embedding of its scalar
representative.  Above `a=1` this uses the pointwise reality of both Fredholm solutions; below
the endpoint all three functions are zero by definition. -/
theorem ofReal_suzukiHankelMuScalar_eq
    {omega : ℝ} (homega : 1 < omega) (a : ℝ) :
    (suzukiHankelMuScalar omega homega a : ℂ) =
      suzukiHankelMuReal omega homega a := by
  by_cases ha : 1 < a
  · unfold suzukiHankelMuScalar
    rw [suzukiHankelMuReal_of_one_lt homega ha]
    have hp := suzukiHankelPhiGlobal_real
      SuzukiHankelSign.positive homega ha (x := a)
    have hm := suzukiHankelPhiGlobal_real
      SuzukiHankelSign.negative homega ha (x := a)
    have him : (suzukiHankelMu omega a homega ha).im = 0 := by
      simp [suzukiHankelMu, hp, hm]
    apply Complex.ext
    · simp
    · simpa only [Complex.ofReal_im] using him.symm
  · have hle : a ≤ 1 := le_of_not_gt ha
    simp [suzukiHankelMuScalar, suzukiHankelMuReal,
      suzukiHankelBoundaryTraceReal, ha]

/-- The scalar coupling is continuous at every `a>1`. -/
theorem continuousAt_suzukiHankelMuScalar_of_one_lt
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    ContinuousAt (suzukiHankelMuScalar omega homega) a := by
  exact Complex.continuous_re.continuousAt.comp
    ((continuousAt_suzukiHankelBoundaryTraceReal_of_one_lt
        SuzukiHankelSign.positive homega ha).add
      (continuousAt_suzukiHankelBoundaryTraceReal_of_one_lt
        SuzukiHankelSign.negative homega ha))

/-- The scalar coupling is continuous at the left endpoint. -/
theorem continuousAt_suzukiHankelMuScalar_one
    {omega : ℝ} (homega : 1 < omega) :
    ContinuousAt (suzukiHankelMuScalar omega homega) 1 := by
  exact Complex.continuous_re.continuousAt.comp
    ((continuousAt_suzukiHankelBoundaryTraceReal_one
        SuzukiHankelSign.positive homega).add
      (continuousAt_suzukiHankelBoundaryTraceReal_one
        SuzukiHankelSign.negative homega))

/-- The logarithmic coupling density in equation (4.17) is interval-integrable on every printed
interval `[1,a]`, `a>1`. -/
theorem intervalIntegrable_suzukiHankelMuScalar_div
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    IntervalIntegrable (fun b => suzukiHankelMuScalar omega homega b / b)
      volume 1 a := by
  have hcont : ContinuousOn (suzukiHankelMuScalar omega homega) (Icc 1 a) := by
    intro b hb
    by_cases hb1 : b = 1
    · subst b
      exact (continuousAt_suzukiHankelMuScalar_one homega).continuousWithinAt
    · exact (continuousAt_suzukiHankelMuScalar_of_one_lt homega
        (lt_of_le_of_ne hb.1 (Ne.symm hb1))).continuousWithinAt
  exact (hcont.div continuousOn_id (fun b hb => by
      simpa only [id_eq] using
        (ne_of_gt (lt_of_lt_of_le zero_lt_one hb.1))))
    |>.intervalIntegrable_of_Icc ha.le

/-- Suzuki's literal normalization, equation (4.17).  Totalizing `μ` by zero below one also gives
the paper's convention `m(a)=1` on `0<a≤1`. -/
def suzukiHankelM (omega : ℝ) (homega : 1 < omega) (a : ℝ) : ℝ :=
  Real.exp (∫ b in (1 : ℝ)..a, suzukiHankelMuScalar omega homega b / b)

theorem suzuki_equation_417
    {omega : ℝ} (homega : 1 < omega) (a : ℝ) :
    suzukiHankelM omega homega a =
      Real.exp (∫ b in (1 : ℝ)..a, suzukiHankelMuScalar omega homega b / b) := by
  rfl

theorem suzukiHankelM_pos
    {omega : ℝ} (homega : 1 < omega) (a : ℝ) :
    0 < suzukiHankelM omega homega a := by
  exact Real.exp_pos _

theorem suzukiHankelM_ne_zero
    {omega : ℝ} (homega : 1 < omega) (a : ℝ) :
    suzukiHankelM omega homega a ≠ 0 :=
  ne_of_gt (suzukiHankelM_pos homega a)

/-! ## The `A/B` meromorphic pair and entire pole clearing -/

/-- `2 tilde A_a = tilde E_a + tilde E_a^*`, from equation (4.20). -/
def suzukiHankelTildeAContinuation
    (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) (z : ℂ) : ℂ :=
  (suzukiHankelTildeEContinuation omega a homega ha z +
    suzukiHankelTildeEStarContinuation omega a homega ha z) / 2

/-- `2i tilde B_a = tilde E_a^* - tilde E_a`, from equation (4.20). -/
def suzukiHankelTildeBContinuation
    (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) (z : ℂ) : ℂ :=
  (suzukiHankelTildeEStarContinuation omega a homega ha z -
    suzukiHankelTildeEContinuation omega a homega ha z) / (2 * I)

/-- Entire pole-cleared numerator `E^omega tilde A_a`. -/
def suzukiHankelTildeACleared
    (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) (z : ℂ) : ℂ :=
  (suzukiHankelTildeECleared omega a homega ha z +
    suzukiHankelTildeEStarCleared omega a homega ha z) / 2

/-- Entire pole-cleared numerator `E^omega tilde B_a`. -/
def suzukiHankelTildeBCleared
    (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) (z : ℂ) : ℂ :=
  (suzukiHankelTildeEStarCleared omega a homega ha z -
    suzukiHankelTildeECleared omega a homega ha z) / (2 * I)

theorem meromorphicOn_suzukiHankelTildeAContinuation
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    MeromorphicOn (suzukiHankelTildeAContinuation omega a homega ha) Set.univ := by
  exact (meromorphicOn_suzukiHankelTildeEContinuation homega ha).add
      (meromorphicOn_suzukiHankelTildeEStarContinuation homega ha) |>.div
    (analyticOnNhd_const.meromorphicOn)

theorem meromorphicOn_suzukiHankelTildeBContinuation
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    MeromorphicOn (suzukiHankelTildeBContinuation omega a homega ha) Set.univ := by
  exact (meromorphicOn_suzukiHankelTildeEStarContinuation homega ha).sub
      (meromorphicOn_suzukiHankelTildeEContinuation homega ha) |>.div
    (analyticOnNhd_const.meromorphicOn)

theorem analyticOnNhd_suzukiHankelTildeAContinuation
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    AnalyticOnNhd ℂ (suzukiHankelTildeAContinuation omega a homega ha)
      suzukiUpperHalfPlane := by
  exact (analyticOnNhd_suzukiHankelTildeEContinuation homega ha).add
      (analyticOnNhd_suzukiHankelTildeEStarContinuation homega ha) |>.div
    analyticOnNhd_const (by intro z hz; norm_num)

theorem analyticOnNhd_suzukiHankelTildeBContinuation
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    AnalyticOnNhd ℂ (suzukiHankelTildeBContinuation omega a homega ha)
      suzukiUpperHalfPlane := by
  exact (analyticOnNhd_suzukiHankelTildeEStarContinuation homega ha).sub
      (analyticOnNhd_suzukiHankelTildeEContinuation homega ha) |>.div
    analyticOnNhd_const (by intro z hz; norm_num [Complex.I_ne_zero])

theorem differentiable_suzukiHankelTildeACleared
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    Differentiable ℂ (suzukiHankelTildeACleared omega a homega ha) := by
  exact ((differentiable_suzukiHankelTildeECleared homega ha).add
    (differentiable_suzukiHankelTildeEStarCleared homega ha)).div_const 2

theorem differentiable_suzukiHankelTildeBCleared
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    Differentiable ℂ (suzukiHankelTildeBCleared omega a homega ha) := by
  exact ((differentiable_suzukiHankelTildeEStarCleared homega ha).sub
    (differentiable_suzukiHankelTildeECleared homega ha)).div_const (2 * I)

/-- Entire reflection identity underlying all parity statements. -/
theorem suzukiHankelTildeEStarCleared_eq_ECleared_neg
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    suzukiHankelTildeEStarCleared omega a homega ha z =
      suzukiHankelTildeECleared omega a homega ha (-z) := by
  rw [suzukiHankelTildeEStarCleared, suzukiHankelTildeECleared,
    suzukiHankelTildeERegularPart, suzukiHankelTildeEThetaPart]
  simp only [neg_neg]
  ring

/-- Global entire form of `A_a(-z)=A_a(z)` before the real normalization. -/
theorem suzukiHankelTildeACleared_neg
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    suzukiHankelTildeACleared omega a homega ha (-z) =
      suzukiHankelTildeACleared omega a homega ha z := by
  unfold suzukiHankelTildeACleared
  rw [
    ← suzukiHankelTildeEStarCleared_eq_ECleared_neg homega ha z,
    suzukiHankelTildeEStarCleared_eq_ECleared_neg homega ha (-z)]
  simp only [neg_neg]
  ring

/-- Global entire form of `B_a(-z)=-B_a(z)` before the real normalization. -/
theorem suzukiHankelTildeBCleared_neg
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    suzukiHankelTildeBCleared omega a homega ha (-z) =
      -suzukiHankelTildeBCleared omega a homega ha z := by
  unfold suzukiHankelTildeBCleared
  rw [
    ← suzukiHankelTildeEStarCleared_eq_ECleared_neg homega ha z,
    suzukiHankelTildeEStarCleared_eq_ECleared_neg homega ha (-z)]
  simp only [neg_neg]
  ring

theorem suzukiHankelTildeACleared_eq_E_mul
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a)
    (z : ℂ) (hz : suzukiCanonicalE omega z ≠ 0) :
    suzukiHankelTildeACleared omega a homega ha z =
      suzukiCanonicalE omega z *
        suzukiHankelTildeAContinuation omega a homega ha z := by
  rw [suzukiHankelTildeACleared, suzukiHankelTildeAContinuation,
    suzukiHankelTildeECleared_eq_E_mul homega ha z hz,
    suzukiHankelTildeEStarCleared_eq_E_mul homega ha z hz]
  ring

theorem suzukiHankelTildeBCleared_eq_E_mul
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a)
    (z : ℂ) (hz : suzukiCanonicalE omega z ≠ 0) :
    suzukiHankelTildeBCleared omega a homega ha z =
      suzukiCanonicalE omega z *
        suzukiHankelTildeBContinuation omega a homega ha z := by
  rw [suzukiHankelTildeBCleared, suzukiHankelTildeBContinuation,
    suzukiHankelTildeECleared_eq_E_mul homega ha z hz,
    suzukiHankelTildeEStarCleared_eq_E_mul homega ha z hz]
  ring

/-! ## Meromorphic functional equations -/

theorem suzukiHankelTildeA_functionalEquation
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a)
    (z : ℂ) (hz : suzukiCanonicalE omega z ≠ 0)
    (hneg : suzukiCanonicalE omega (-z) ≠ 0) :
    suzukiCanonicalTheta omega z *
        suzukiHankelTildeAContinuation omega a homega ha (-z) =
      suzukiHankelTildeAContinuation omega a homega ha z := by
  have hstar := suzukiHankelTildeEStarContinuation_eq_theta_mul_neg
    homega ha z hz hneg
  have hstarNeg := suzukiHankelTildeEStarContinuation_eq_theta_mul_neg
    homega ha (-z) hneg (by simpa only [neg_neg] using hz)
  have htheta := suzukiCanonicalTheta_mul_neg_eq_one omega z hz hneg
  rw [suzukiHankelTildeAContinuation, suzukiHankelTildeAContinuation,
    hstar]
  simp only [neg_neg] at hstarNeg
  rw [hstarNeg]
  ring_nf at htheta ⊢
  rw [htheta]
  ring

theorem suzukiHankelTildeB_functionalEquation
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a)
    (z : ℂ) (hz : suzukiCanonicalE omega z ≠ 0)
    (hneg : suzukiCanonicalE omega (-z) ≠ 0) :
    suzukiCanonicalTheta omega z *
        suzukiHankelTildeBContinuation omega a homega ha (-z) =
      -suzukiHankelTildeBContinuation omega a homega ha z := by
  have hstar := suzukiHankelTildeEStarContinuation_eq_theta_mul_neg
    homega ha z hz hneg
  have hstarNeg := suzukiHankelTildeEStarContinuation_eq_theta_mul_neg
    homega ha (-z) hneg (by simpa only [neg_neg] using hz)
  have htheta := suzukiCanonicalTheta_mul_neg_eq_one omega z hz hneg
  rw [suzukiHankelTildeBContinuation, suzukiHankelTildeBContinuation,
    hstar]
  simp only [neg_neg] at hstarNeg
  rw [hstarNeg]
  ring_nf at htheta ⊢
  rw [htheta]
  ring

/-! ## The completed entire pair from equation (4.16) -/

/-- Entire continuation of Suzuki's `A_a` with the exact normalization `m(a)`. -/
def suzukiHankelCompletedA
    (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) (z : ℂ) : ℂ :=
  (suzukiHankelM omega homega a : ℂ) *
    suzukiHankelTildeACleared omega a homega ha z

/-- Entire continuation of Suzuki's `B_a` with the exact normalization `1/m(a)`. -/
def suzukiHankelCompletedB
    (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a) (z : ℂ) : ℂ :=
  (suzukiHankelM omega homega a : ℂ)⁻¹ *
    suzukiHankelTildeBCleared omega a homega ha z

theorem differentiable_suzukiHankelCompletedA
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    Differentiable ℂ (suzukiHankelCompletedA omega a homega ha) := by
  exact (differentiable_suzukiHankelTildeACleared homega ha).const_mul _

theorem differentiable_suzukiHankelCompletedB
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) :
    Differentiable ℂ (suzukiHankelCompletedB omega a homega ha) := by
  exact (differentiable_suzukiHankelTildeBCleared homega ha).const_mul _

/-- Suzuki (2012), equation (4.16), first identity, on the quotient regular locus. -/
theorem suzuki_equation_416_A
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a)
    (z : ℂ) (hz : suzukiCanonicalE omega z ≠ 0) :
    suzukiHankelCompletedA omega a homega ha z =
      (suzukiHankelM omega homega a : ℂ) * suzukiCanonicalE omega z *
        suzukiHankelTildeAContinuation omega a homega ha z := by
  rw [suzukiHankelCompletedA,
    suzukiHankelTildeACleared_eq_E_mul homega ha z hz]
  ring

/-- Suzuki (2012), equation (4.16), second identity, on the quotient regular locus. -/
theorem suzuki_equation_416_B
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a)
    (z : ℂ) (hz : suzukiCanonicalE omega z ≠ 0) :
    suzukiHankelCompletedB omega a homega ha z =
      (suzukiHankelM omega homega a : ℂ)⁻¹ * suzukiCanonicalE omega z *
        suzukiHankelTildeBContinuation omega a homega ha z := by
  rw [suzukiHankelCompletedB,
    suzukiHankelTildeBCleared_eq_E_mul homega ha z hz]
  ring

theorem suzukiHankelCompletedA_neg
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    suzukiHankelCompletedA omega a homega ha (-z) =
      suzukiHankelCompletedA omega a homega ha z := by
  unfold suzukiHankelCompletedA
  rw [suzukiHankelTildeACleared_neg homega ha]

theorem suzukiHankelCompletedB_neg
    {omega a : ℝ} (homega : 1 < omega) (ha : 1 < a) (z : ℂ) :
    suzukiHankelCompletedB omega a homega ha (-z) =
      -suzukiHankelCompletedB omega a homega ha z := by
  unfold suzukiHankelCompletedB
  rw [suzukiHankelTildeBCleared_neg homega ha]
  ring

/-- **Suzuki (2012), Lemma 4.9, closed theorem.** -/
theorem suzuki2012_lemma_four_nine :
    ∀ (omega a : ℝ) (homega : 1 < omega) (ha : 1 < a),
      MeromorphicOn (suzukiHankelTildeAContinuation omega a homega ha) Set.univ ∧
      MeromorphicOn (suzukiHankelTildeBContinuation omega a homega ha) Set.univ ∧
      AnalyticOnNhd ℂ (suzukiHankelTildeAContinuation omega a homega ha)
        suzukiUpperHalfPlane ∧
      AnalyticOnNhd ℂ (suzukiHankelTildeBContinuation omega a homega ha)
        suzukiUpperHalfPlane ∧
      Differentiable ℂ (suzukiHankelCompletedA omega a homega ha) ∧
      Differentiable ℂ (suzukiHankelCompletedB omega a homega ha) ∧
      (∀ z : ℂ, suzukiCanonicalE omega z ≠ 0 →
        suzukiCanonicalE omega (-z) ≠ 0 →
        suzukiCanonicalTheta omega z *
            suzukiHankelTildeAContinuation omega a homega ha (-z) =
          suzukiHankelTildeAContinuation omega a homega ha z) ∧
      (∀ z : ℂ, suzukiCanonicalE omega z ≠ 0 →
        suzukiCanonicalE omega (-z) ≠ 0 →
        suzukiCanonicalTheta omega z *
            suzukiHankelTildeBContinuation omega a homega ha (-z) =
          -suzukiHankelTildeBContinuation omega a homega ha z) ∧
      (∀ z : ℂ, suzukiHankelCompletedA omega a homega ha (-z) =
        suzukiHankelCompletedA omega a homega ha z) ∧
      (∀ z : ℂ, suzukiHankelCompletedB omega a homega ha (-z) =
        -suzukiHankelCompletedB omega a homega ha z) := by
  intro omega a homega ha
  exact ⟨meromorphicOn_suzukiHankelTildeAContinuation homega ha,
    meromorphicOn_suzukiHankelTildeBContinuation homega ha,
    analyticOnNhd_suzukiHankelTildeAContinuation homega ha,
    analyticOnNhd_suzukiHankelTildeBContinuation homega ha,
    differentiable_suzukiHankelCompletedA homega ha,
    differentiable_suzukiHankelCompletedB homega ha,
    fun z hz hneg => suzukiHankelTildeA_functionalEquation homega ha z hz hneg,
    fun z hz hneg => suzukiHankelTildeB_functionalEquation homega ha z hz hneg,
    fun z => suzukiHankelCompletedA_neg homega ha z,
    fun z => suzukiHankelCompletedB_neg homega ha z⟩

end RHTower
