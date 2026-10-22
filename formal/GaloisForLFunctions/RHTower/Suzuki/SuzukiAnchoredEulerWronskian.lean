import GaloisForLFunctions.RHTower.Suzuki.SuzukiCompactifiedPhaseProfile
import GaloisForLFunctions.RHTower.Suzuki.SuzukiShiftedXiTargetFlatPencil
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic

/-!
# Anchored Euler--Wronskian elimination of Suzuki endpoint escape

Every finite-aperture Suzuki Donoghue function has zero linear Nevanlinna term, but a cofinal
compactified spectral limit may acquire `alpha * z` from probability escaping through either
projective endpoint.  This module changes the limiting observable to the degree-one Euler defect

`E[m](z) = z m'(z) - m(z)`.

The defect kills the complete linear escape mode.  For a common-gauge entire pair
`m = -i A / B`, it is the quotient of a homogeneous Euler--Wronskian covariant, so the varying
common gauge cancels exactly.  Its Donoghue kernel tends to zero at both projective ends.  Finally,
the canonical anchor `m(i)=i` makes the transform injective on the upper half-plane: the only
kernel before anchoring is `c z`.

Thus zero linear mass need not be passed as a separate cofinal premise if the source identifies
the Euler--Wronskian target.  Interior Clark-label overcrowding and the target identification
itself remain open.  No RH assumption and no numerical computation occur here.
-/

open Complex Filter Set Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Degree-one Euler defect.  Its kernel on a connected nonzero domain consists of linear modes. -/
def suzukiEulerDefect (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  z * deriv F z - F z

/-- Homogeneous pair representative of the Euler defect of `-i A/B`. -/
def suzukiEulerWronskian (A B : ℂ → ℂ) (z : ℂ) : ℂ :=
  z * (deriv A z * B z - A z * deriv B z) - A z * B z

/-- Euler defect of the Donoghue probability kernel, in its endpoint-regular rational form. -/
def suzukiDonoghueEulerKernel (t : ℝ) (z : ℂ) : ℂ :=
  ((t : ℂ) * (z ^ (2 : ℕ) - 1) + 2 * z) / ((t : ℂ) - z) ^ (2 : ℕ)

/-! ## Exact linear and common-gauge kernels -/

/-- Adding arbitrary linear Nevanlinna mass does not change the Euler defect. -/
theorem suzukiEulerDefect_add_linear
    (F : ℂ → ℂ) (c z : ℂ) (hF : AnalyticAt ℂ F z) :
    suzukiEulerDefect (fun w => F w + c * w) z = suzukiEulerDefect F z := by
  have hlinear : HasDerivAt (fun w : ℂ => c * w) c z := by
    simpa only [id_eq, mul_one] using (hasDerivAt_id z).const_mul c
  have hsum : deriv (fun w => F w + c * w) z = deriv F z + c :=
    ((hF.differentiableAt.hasDerivAt).add hlinear).deriv
  rw [suzukiEulerDefect, suzukiEulerDefect, hsum]
  ring

/-- The Euler--Wronskian is quadratic under a common holomorphic gauge. -/
theorem suzukiEulerWronskian_commonGauge
    (G A B : ℂ → ℂ) (z : ℂ)
    (hG : AnalyticAt ℂ G z) (hA : AnalyticAt ℂ A z) (hB : AnalyticAt ℂ B z) :
    suzukiEulerWronskian (fun w => G w * A w) (fun w => G w * B w) z =
      G z ^ (2 : ℕ) * suzukiEulerWronskian A B z := by
  have hGA : deriv (fun w => G w * A w) z =
      deriv G z * A z + G z * deriv A z :=
    ((hG.differentiableAt.hasDerivAt).mul
      hA.differentiableAt.hasDerivAt).deriv
  have hGB : deriv (fun w => G w * B w) z =
      deriv G z * B z + G z * deriv B z :=
    ((hG.differentiableAt.hasDerivAt).mul
      hB.differentiableAt.hasDerivAt).deriv
  rw [suzukiEulerWronskian, suzukiEulerWronskian, hGA, hGB]
  ring

/-- Quotient form of the Euler defect for an arbitrary analytic pair. -/
theorem suzukiEulerDefect_div
    (A B : ℂ → ℂ) (z : ℂ)
    (hA : AnalyticAt ℂ A z) (hB : AnalyticAt ℂ B z) (hBz : B z ≠ 0) :
    suzukiEulerDefect (fun w => A w / B w) z =
      suzukiEulerWronskian A B z / B z ^ (2 : ℕ) := by
  have hquot : HasDerivAt (fun w : ℂ => A w / B w)
      ((deriv A z * B z - A z * deriv B z) / B z ^ (2 : ℕ)) z :=
    hA.differentiableAt.hasDerivAt.div hB.differentiableAt.hasDerivAt hBz
  rw [suzukiEulerDefect, suzukiEulerWronskian, hquot.deriv]
  field_simp [hBz]

/-- Quotient form of the Euler defect of Suzuki's two-angle Donoghue carrier. -/
theorem suzukiEulerDefect_neg_I_mul_div
    (A B : ℂ → ℂ) (z : ℂ)
    (hA : AnalyticAt ℂ A z) (hB : AnalyticAt ℂ B z) (hBz : B z ≠ 0) :
    suzukiEulerDefect (fun w => -I * (A w / B w)) z =
      -I * suzukiEulerWronskian A B z / B z ^ (2 : ℕ) := by
  have hquot : HasDerivAt (fun w : ℂ => A w / B w)
      ((deriv A z * B z - A z * deriv B z) / B z ^ (2 : ℕ)) z :=
    hA.differentiableAt.hasDerivAt.div hB.differentiableAt.hasDerivAt hBz
  have hcarrier : deriv (fun w : ℂ => -I * (A w / B w)) z =
      -I * ((deriv A z * B z - A z * deriv B z) / B z ^ (2 : ℕ)) := by
    exact (hquot.const_mul (-I)).deriv
  rw [suzukiEulerDefect, suzukiEulerWronskian, hcarrier]
  field_simp [hBz]
  ring

/-- The normalized Euler--Wronskian quotient is exactly common-gauge invariant. -/
theorem suzukiEulerWronskianQuotient_commonGauge
    (G A B : ℂ → ℂ) (z : ℂ)
    (hG : AnalyticAt ℂ G z) (hA : AnalyticAt ℂ A z) (hB : AnalyticAt ℂ B z)
    (hGz : G z ≠ 0) (hBz : B z ≠ 0) :
    suzukiEulerWronskian (fun w => G w * A w) (fun w => G w * B w) z /
        (G z * B z) ^ (2 : ℕ) =
      suzukiEulerWronskian A B z / B z ^ (2 : ℕ) := by
  rw [suzukiEulerWronskian_commonGauge G A B z hG hA hB]
  field_simp [hGz, hBz]

/-! ## Exact shifted-Xi target connector -/

/-- Named homogeneous Euler--Wronskian of the boundary-free shifted Xi pair
`(z² XiC, XiC' - eta XiC)`. -/
def suzukiShiftedXiEulerWronskian (eta z : ℂ) : ℂ :=
  suzukiEulerWronskian (fun w => w ^ (2 : ℕ) * _root_.RHTower.XiC w)
    (_root_.RHTower.suzukiShiftedXiDenominator eta) z

/-- The one-phase shifted Xi target's Euler defect is exactly its named pair covariant divided by
the denominator square.  This is an algebraic connector, not an identification of that target
with Suzuki's separately anchored two-phase Donoghue ratio. -/
theorem suzukiEulerDefect_suzukiShiftedXiTarget
    (eta z : ℂ)
    (hden : _root_.RHTower.suzukiShiftedXiDenominator eta z ≠ 0) :
    suzukiEulerDefect (_root_.RHTower.suzukiShiftedXiTarget eta) z =
      suzukiShiftedXiEulerWronskian eta z /
        _root_.RHTower.suzukiShiftedXiDenominator eta z ^ (2 : ℕ) := by
  have hXi : AnalyticAt ℂ _root_.RHTower.XiC z :=
    _root_.RHTower.XiC_analytic z (Set.mem_univ z)
  have hnum : AnalyticAt ℂ (fun w : ℂ => w ^ (2 : ℕ) * _root_.RHTower.XiC w) z := by
    fun_prop
  have hdenAn : AnalyticAt ℂ (_root_.RHTower.suzukiShiftedXiDenominator eta) z := by
    exact hXi.deriv.sub (analyticAt_const.mul hXi)
  simpa only [_root_.RHTower.suzukiShiftedXiTarget,
    suzukiShiftedXiEulerWronskian] using!
    suzukiEulerDefect_div (fun w : ℂ => w ^ (2 : ℕ) * _root_.RHTower.XiC w)
      (_root_.RHTower.suzukiShiftedXiDenominator eta) z hnum hdenAn hden

/-! ## Donoghue kernel and its projective endpoint values -/

/-- Exact spectral derivative of Donoghue's probability kernel. -/
theorem hasDerivAt_suzukiDonoghueKernel
    (t : ℝ) (z : ℂ) (h : (t : ℂ) - z ≠ 0) :
    HasDerivAt (suzukiDonoghueKernel t)
      (((t : ℂ) ^ (2 : ℕ) + 1) / ((t : ℂ) - z) ^ (2 : ℕ)) z := by
  have hnum : HasDerivAt (fun w : ℂ => w ^ (2 : ℕ) + 1) (2 * z) z := by
    simpa [id_eq, mul_comm] using ((hasDerivAt_id z).pow 2).add_const 1
  have hden : HasDerivAt (fun w : ℂ => (t : ℂ) - w) (-1) z := by
    simpa using! (hasDerivAt_const z (t : ℂ)).sub (hasDerivAt_id z)
  have hkernel := (hasDerivAt_id z).add (hnum.div hden h)
  have hcoeff :
      1 + (2 * z * ((t : ℂ) - z) - (z ^ (2 : ℕ) + 1) * (-1)) / ((t : ℂ) - z) ^ (2 : ℕ) =
        ((t : ℂ) ^ (2 : ℕ) + 1) / ((t : ℂ) - z) ^ (2 : ℕ) := by
    field_simp [h]
    ring
  rw [← hcoeff]
  simpa only [suzukiDonoghueKernel, id_eq] using! hkernel

/-- The Euler defect of the Donoghue kernel is the endpoint-regular kernel above. -/
theorem suzukiEulerDefect_donoghueKernel
    (t : ℝ) (z : ℂ) (h : (t : ℂ) - z ≠ 0) :
    suzukiEulerDefect (suzukiDonoghueKernel t) z =
      suzukiDonoghueEulerKernel t z := by
  rw [suzukiEulerDefect, suzukiDonoghueEulerKernel,
    (hasDerivAt_suzukiDonoghueKernel t z h).deriv, suzukiDonoghueKernel]
  field_simp [h]
  ring

/-- Inverse-denominator decomposition exposing one and two powers of projective decay. -/
theorem suzukiDonoghueEulerKernel_eq_inverse_decomp
    (t : ℝ) (z : ℂ) (h : (t : ℂ) - z ≠ 0) :
    suzukiDonoghueEulerKernel t z =
      (z ^ (2 : ℕ) - 1) / ((t : ℂ) - z) +
        (z * (z ^ (2 : ℕ) + 1)) / ((t : ℂ) - z) ^ (2 : ℕ) := by
  rw [suzukiDonoghueEulerKernel]
  field_simp [h]
  ring

/-- The Euler-transformed Donoghue kernel vanishes at positive projective infinity. -/
theorem tendsto_suzukiDonoghueEulerKernel_atTop
    (z : ℂ) (hz : z.im ≠ 0) :
    Tendsto (fun t : ℝ => suzukiDonoghueEulerKernel t z) atTop (nhds 0) := by
  have htz : ∀ t : ℝ, (t : ℂ) - z ≠ 0 := by
    intro t h
    have him := congrArg Complex.im h
    simp only [sub_im, ofReal_im, zero_sub] at him
    exact hz (neg_eq_zero.mp him)
  have hden : Tendsto (fun t : ℝ => (t : ℂ) - z) atTop
      (Bornology.cobounded ℂ) :=
    (tendsto_sub_const_cobounded z).comp (RCLike.tendsto_ofReal_atTop_cobounded ℂ)
  have hinv : Tendsto (fun t : ℝ => ((t : ℂ) - z)⁻¹) atTop (nhds 0) :=
    tendsto_inv₀_cobounded.comp hden
  have hfirst : Tendsto
      (fun t : ℝ => (z ^ (2 : ℕ) - 1) * ((t : ℂ) - z)⁻¹) atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds (x := z ^ (2 : ℕ) - 1)).mul hinv
  have hsecond : Tendsto
      (fun t : ℝ => (z * (z ^ (2 : ℕ) + 1)) * (((t : ℂ) - z)⁻¹) ^ (2 : ℕ)) atTop (nhds 0) := by
    simpa only [zero_pow two_ne_zero, mul_zero] using
      (tendsto_const_nhds (x := z * (z ^ (2 : ℕ) + 1))).mul (hinv.pow 2)
  have hsum := hfirst.add hsecond
  simpa only [suzukiDonoghueEulerKernel_eq_inverse_decomp _ z (htz _),
    div_eq_mul_inv, inv_pow, mul_zero, add_zero, zero_pow two_ne_zero] using hsum

/-- The Euler-transformed Donoghue kernel also vanishes at negative projective infinity. -/
theorem tendsto_suzukiDonoghueEulerKernel_atBot
    (z : ℂ) (hz : z.im ≠ 0) :
    Tendsto (fun t : ℝ => suzukiDonoghueEulerKernel t z) atBot (nhds 0) := by
  have htz : ∀ t : ℝ, (t : ℂ) - z ≠ 0 := by
    intro t h
    have him := congrArg Complex.im h
    simp only [sub_im, ofReal_im, zero_sub] at him
    exact hz (neg_eq_zero.mp him)
  have hden : Tendsto (fun t : ℝ => (t : ℂ) - z) atBot
      (Bornology.cobounded ℂ) :=
    (tendsto_sub_const_cobounded z).comp (RCLike.tendsto_ofReal_atBot_cobounded ℂ)
  have hinv : Tendsto (fun t : ℝ => ((t : ℂ) - z)⁻¹) atBot (nhds 0) :=
    tendsto_inv₀_cobounded.comp hden
  have hfirst : Tendsto
      (fun t : ℝ => (z ^ (2 : ℕ) - 1) * ((t : ℂ) - z)⁻¹) atBot (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds (x := z ^ (2 : ℕ) - 1)).mul hinv
  have hsecond : Tendsto
      (fun t : ℝ => (z * (z ^ (2 : ℕ) + 1)) * (((t : ℂ) - z)⁻¹) ^ (2 : ℕ)) atBot (nhds 0) := by
    simpa only [zero_pow two_ne_zero, mul_zero] using
      (tendsto_const_nhds (x := z * (z ^ (2 : ℕ) + 1))).mul (hinv.pow 2)
  have hsum := hfirst.add hsecond
  simpa only [suzukiDonoghueEulerKernel_eq_inverse_decomp _ z (htz _),
    div_eq_mul_inv, inv_pow, mul_zero, add_zero, zero_pow two_ne_zero] using hsum

/-! ## Anchored injectivity on the upper half-plane -/

/-- **Anchored Euler injectivity.**  Two differentiable carriers on the upper half-plane with the
same Euler defect differ by `c*z`; equality at Suzuki's canonical anchor `i` forces `c=0`. -/
theorem eqOn_upperHalfPlane_of_suzukiEulerDefect_eq_of_eq_I
    (m n : ℂ → ℂ)
    (hm : DifferentiableOn ℂ m UpperHalfPlane.upperHalfPlaneSet)
    (hn : DifferentiableOn ℂ n UpperHalfPlane.upperHalfPlaneSet)
    (hdefect : Set.EqOn (suzukiEulerDefect m) (suzukiEulerDefect n)
      UpperHalfPlane.upperHalfPlaneSet)
    (hanchor : m I = n I) :
    Set.EqOn m n UpperHalfPlane.upperHalfPlaneSet := by
  let q : ℂ → ℂ := fun z => (m z - n z) / z
  have hz_ne (z : ℂ) (hz : z ∈ UpperHalfPlane.upperHalfPlaneSet) : z ≠ 0 := by
    intro hzero
    subst z
    have hnot : ¬(0 : ℂ) ∈ UpperHalfPlane.upperHalfPlaneSet := by
      simp [UpperHalfPlane.upperHalfPlaneSet]
    exact hnot hz
  have hq : DifferentiableOn ℂ q UpperHalfPlane.upperHalfPlaneSet := by
    intro z hz
    exact ((hm z hz).sub (hn z hz)).div
      differentiableAt_id.differentiableWithinAt (hz_ne z hz)
  have hqderiv : Set.EqOn (deriv q) 0 UpperHalfPlane.upperHalfPlaneSet := by
    intro z hz
    change deriv q z = (0 : ℂ)
    have hmz : DifferentiableAt ℂ m z :=
      hm.differentiableAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz)
    have hnz : DifferentiableAt ℂ n z :=
      hn.differentiableAt (UpperHalfPlane.isOpen_upperHalfPlaneSet.mem_nhds hz)
    have hformula : deriv q z =
        (((deriv m z - deriv n z) * z - (m z - n z)) / z ^ (2 : ℕ)) := by
      have hsub : HasDerivAt (fun w => m w - n w)
          (deriv m z - deriv n z) z := by
        simpa only [Pi.sub_apply] using! hmz.hasDerivAt.sub hnz.hasDerivAt
      have hid : HasDerivAt (fun w : ℂ => w) 1 z := by
        simpa only [id_eq] using! hasDerivAt_id z
      have hdiv := (hsub.div hid (hz_ne z hz)).deriv
      change deriv (fun w => (m w - n w) / w) z = _
      simpa only [mul_one] using! hdiv
    rw [hformula]
    have he := hdefect hz
    rw [suzukiEulerDefect, suzukiEulerDefect] at he
    have hnum : (deriv m z - deriv n z) * z - (m z - n z) = 0 := by
      linear_combination he
    rw [hnum, zero_div]
  have hpre : IsPreconnected UpperHalfPlane.upperHalfPlaneSet :=
    (convex_halfSpace_im_gt 0).isPreconnected
  have hI : I ∈ UpperHalfPlane.upperHalfPlaneSet := by
    simp [UpperHalfPlane.upperHalfPlaneSet]
  intro z hz
  have hconst : q I = q z :=
    UpperHalfPlane.isOpen_upperHalfPlaneSet.is_const_of_deriv_eq_zero
      hpre hq hqderiv hI hz
  have hqI : q I = 0 := by
    simp only [q, hanchor, sub_self, zero_div]
  have hqz : q z = 0 := hconst ▸ hqI
  simp only [q, div_eq_zero_iff] at hqz
  exact sub_eq_zero.mp (hqz.resolve_right (hz_ne z hz))

end GaloisForLFunctions.RHTower
