import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullAngularCovector

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

noncomputable section
set_option autoImplicit false

/-- Hyperbolically weighted gradient pairing of two literal angular fields. -/
def crossGradient (F G : Field) (z : Point) : ℂ :=
  (z 1 : ℂ) ^ 2 *
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
  (parameter q true / 2) * scalar (center q) z ^ 2 * fullAngularField q false z +
    (parameter q false / 2) * scalar (center q) z ^ 2 * fullAngularField q true z +
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

end

end RHTower.D4BMLiteralCyclicPeierlsCrossBranchSource
