import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularCovector
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspIndicialSelection

/-!
# Cross-branch angular source for literal cyclic Peierls B2

The same-rate Peierls pair is identically zero, while a complementary-rate
pair has clock `-6`.  A literal B2 realization must consequently use the
product of the two distinct full angular branches.  This module gives its
exact angular equation.  Its cross-gradient term is retained as source data;
it cannot be replaced by the one-branch square contact.

Proof-chain role:
`complementary Peierls legs -> exact cross-branch angular source at clock -6
-> cross-rate completed contact/metric -> actual left-QNM current ->
coefficientwise residual-face transport -> HB B2 -> affine cusp receiver -> RH`.
-/

namespace RHTower.D4BMLiteralCyclicPeierlsCrossBranchSource

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open D4BMHorizon D4BMAngularSeries D4BMGlobalAngularResponse D4BMModularCore
open D4BMCuspProjection

noncomputable section
set_option autoImplicit false

/-- Hyperbolically weighted gradient pairing of two literal angular fields. -/
def crossGradient (F G : Field) (z : Point) : ℂ :=
  (z 1 : ℂ) ^ (2 : ℕ) *
    (coordDeriv 0 F z * coordDeriv 0 G z +
      coordDeriv 1 F z * coordDeriv 1 G z)

/-- Exact product law for the literal angular Laplacian. -/
theorem scalarLaplacian_mul (F G : Field) (z : Point) (hz : 0 < z 1)
    (hF : ContDiffAt ℝ 2 F z) (hG : ContDiffAt ℝ 2 G z) :
    scalarLaplacian (fun w => F w * G w) z =
      F z * scalarLaplacian G z + G z * scalarLaplacian F z +
        2 * crossGradient F G z := by
  have hmul := ofField_mul hF hG
  have h0 := congrArg (fun J => J.second 0 0) hmul
  have h1 := congrArg (fun J => J.second 1 1) hmul
  simp only [ofField, ScalarTwoJet.mul] at h0 h1
  rw [scalarLaplacian_eq _ z hz, scalarLaplacian_eq _ z hz,
    scalarLaplacian_eq _ z hz]
  unfold crossGradient
  rw [h0, h1]
  ring

/-- The cross-gradient which survives in the complementary-rate source. -/
def crossBranchGradient (q : XiZeroCopy) (z : Point) : ℂ :=
  crossGradient (fullAngularField q true) (fullAngularField q false) z

/-- Complete non-eigenfield forcing of the complementary-rate angular product. -/
def crossBranchAngularForcing (q : XiZeroCopy) (z : Point) : ℂ :=
  (parameter q true / 2) * scalar (center q) z ^ (2 : ℕ) * fullAngularField q false z +
    (parameter q false / 2) * scalar (center q) z ^ (2 : ℕ) * fullAngularField q true z +
      2 * crossBranchGradient q z

/-- Exact angular source equation for the complementary physical branches.
The final term is the forced cross-gradient datum required by any literal
cross-rate B2 contact. -/
theorem crossBranchAngular_product_equation (q : XiZeroCopy) (z : Point)
    (hz : 0 < z 1) :
    scalarLaplacian (fun w => fullAngularField q true w * fullAngularField q false w) z =
      (parameter q true + parameter q false) *
        (fullAngularField q true z * fullAngularField q false z) +
      crossBranchAngularForcing q z := by
  have htrue : ContDiffAt ℝ 2 (fullAngularField q true) z := by
    have h := (contDiffAt_infty.mp (fullAngularField_smooth q true z hz)) 2
    norm_num at h
    exact h
  have hfalse : ContDiffAt ℝ 2 (fullAngularField q false) z := by
    have h := (contDiffAt_infty.mp (fullAngularField_smooth q false z hz)) 2
    norm_num at h
    exact h
  rw [scalarLaplacian_mul _ _ z hz htrue hfalse,
    fullAngularField_equation q true z hz,
    fullAngularField_equation q false z hz]
  unfold crossBranchAngularForcing crossBranchGradient
  ring

/-- Clock carried by the two complementary physical Peierls legs. -/
def crossBranchClock (q : XiZeroCopy) : ℂ :=
  physicalRate q true + physicalRate q false

/-- Indicial parameter associated with the total cross-branch clock. -/
def crossBranchClockParameter (q : XiZeroCopy) : ℂ :=
  (crossBranchClock q + 1) * (crossBranchClock q + 2)

/-- Sum of the literal angular parameters carried by the two product factors. -/
def crossBranchAngularParameter (q : XiZeroCopy) : ℂ :=
  parameter q true + parameter q false

/-- Complementary physical legs carry the exact fixed clock required by the
cross-rate current. -/
theorem crossBranchClock_eq_neg_six (q : XiZeroCopy) :
    crossBranchClock q = (-6 : ℂ) := by
  simp only [crossBranchClock, physicalRate, if_true, Bool.false_eq_true, if_false]
  ring

/-- The cross-rate clock would have indicial parameter `20` if its angular
carrier were homogeneous at that clock. -/
theorem crossBranchClockParameter_eq_twenty (q : XiZeroCopy) :
    crossBranchClockParameter q = (20 : ℂ) := by
  rw [crossBranchClockParameter, crossBranchClock_eq_neg_six]
  norm_num

/-- Exact angular parameter of the literal product before its forced
cross-gradient term is accounted for. -/
theorem crossBranchAngularParameter_eq (q : XiZeroCopy) :
    crossBranchAngularParameter q =
      8 * (q.1 : ℂ) ^ (2 : ℕ) - 8 * (q.1 : ℂ) + 6 := by
  rw [crossBranchAngularParameter, physicalRate_parameter q true,
    physicalRate_parameter q false]
  simp only [physicalRate, if_true, Bool.false_eq_true, if_false]
  ring

/-- The literal product's displayed angular parameter differs from the
homogeneous parameter selected by its total clock.  Thus a direct
parameter-identification cannot remove the explicit cross forcing; whether
that forcing can compensate the mismatch is a separate question. -/
theorem crossBranchAngularParameter_ne_crossBranchClockParameter (q : XiZeroCopy) :
    crossBranchAngularParameter q ≠ crossBranchClockParameter q := by
  rw [crossBranchAngularParameter_eq, crossBranchClockParameter_eq_twenty]
  intro h
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  norm_num [Complex.add_im, Complex.sub_im, Complex.mul_im, pow_two] at him
  norm_num [Complex.add_re, Complex.sub_re, Complex.mul_re, pow_two] at hre
  have hfactor : (q.1 : ℂ).im * (2 * (q.1 : ℂ).re - 1) = 0 := by
    nlinarith [him]
  have hreal : (q.1 : ℂ).re = 1 / 2 := by
    rcases mul_eq_zero.mp hfactor with hzero | hzero
    · exact False.elim (xi_divisor_support_im_ne_zero q.1 hzero)
    · linarith
  have hsq := sq_nonneg ((q.1 : ℂ).im)
  nlinarith [hre]

end

end RHTower.D4BMLiteralCyclicPeierlsCrossBranchSource
