import GaloisForLFunctions.RHTower.SuzukiVolterraCartesianPhaseDefect
import GaloisForLFunctions.RHTower.SuzukiJumpKernelLoewnerGap

/-!
# Suzuki global-local compound Bezoutian weld

The local marked Volterra response is a projective pair `(Q,P)`.  Suzuki's
centered global multiplier is the projective pair `(XiC', z^(2 : ℕ) XiC)`.  Their
affine difference has the division-free compound pair

`N = Q*T - S*P`, `D = P*T`.

This module proves that `N` is the unique bilinear weld invariant under a
common affine gauge and vanishing on coincident projective pairs.  It then
proves the exact Hermitian Bezoutian product rule

`[N,D] = T*T#*[Q,P] - P*P#*[S,T]`.

Thus the full Suzuki jump Pick kernel has one canonical, division-free
global-local carrier.  Remaining RH-bearing problem is a positive
prime--Gamma Gram factorization of this specific signed Bezoutian.  No
positivity, zero-free hypothesis, RH premise, estimate, or computation is
used below.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## Canonical compound weld -/

/-- Determinant coupling of a local projective pair `(Q,P)` and a global pair
`(S,T)`. -/
def suzukiGlobalLocalCompoundNumerator
    {F : Type*} [CommRing F] (Q P S T : F) : F :=
  Q * T - S * P

/-- Product denominator of the compound affine difference. -/
def suzukiGlobalLocalCompoundDenominator
    {F : Type*} [CommRing F] (P T : F) : F :=
  P * T

/-- General bidegree-`(1,1)` local-global weld used in the uniqueness
classification. -/
def suzukiBilinearGlobalLocalWeld
    {F : Type*} [CommRing F]
    (a b c d Q P S T : F) : F :=
  a * Q * S + b * Q * T + c * P * S + d * P * T

/-- Away from the two explicit denominator divisors, the compound quotient
is exactly the difference of the two affine responses. -/
theorem suzukiGlobalLocalCompound_quotient
    {F : Type*} [Field F] (Q P S T : F)
    (hP : P ≠ 0) (hT : T ≠ 0) :
    suzukiGlobalLocalCompoundNumerator Q P S T /
        suzukiGlobalLocalCompoundDenominator P T =
      Q / P - S / T := by
  simp only [suzukiGlobalLocalCompoundNumerator,
    suzukiGlobalLocalCompoundDenominator]
  field_simp [hP, hT]

/-- Every common pointwise affine gauge cancels before division. -/
theorem suzukiGlobalLocalCompound_commonGauge_invariant
    {F : Type*} [CommRing F] (Q P S T delta : F) :
    suzukiGlobalLocalCompoundNumerator
        (Q + delta * P) P (S + delta * T) T =
      suzukiGlobalLocalCompoundNumerator Q P S T := by
  simp only [suzukiGlobalLocalCompoundNumerator]
  ring

/-- Independent gauges leave exactly the relative gauge times the compound
denominator. -/
theorem suzukiGlobalLocalCompound_relativeGauge
    {F : Type*} [CommRing F] (Q P S T deltaLocal deltaGlobal : F) :
    suzukiGlobalLocalCompoundNumerator
        (Q + deltaLocal * P) P (S + deltaGlobal * T) T =
      suzukiGlobalLocalCompoundNumerator Q P S T +
        (deltaLocal - deltaGlobal) *
          suzukiGlobalLocalCompoundDenominator P T := by
  simp only [suzukiGlobalLocalCompoundNumerator,
    suzukiGlobalLocalCompoundDenominator]
  ring

/-- **Canonical-weld classification.**  Common affine-gauge invariance and
vanishing on coincident projective pairs characterize `Q*T-S*P` among all
bidegree-`(1,1)` welds, up to scalar. -/
theorem suzukiBilinearGlobalLocalWeld_classification
    {F : Type*} [CommRing F] (a b c d : F)
    (hinvariant : ∀ Q P S T delta : F,
      suzukiBilinearGlobalLocalWeld a b c d
          (Q + delta * P) P (S + delta * T) T =
        suzukiBilinearGlobalLocalWeld a b c d Q P S T)
    (hcoincident : ∀ Q P S T : F, Q * T = S * P →
      suzukiBilinearGlobalLocalWeld a b c d Q P S T = 0) :
    ∀ Q P S T : F,
      suzukiBilinearGlobalLocalWeld a b c d Q P S T =
        b * suzukiGlobalLocalCompoundNumerator Q P S T := by
  have ha : a = 0 := by
    have h := hinvariant 0 1 1 0 1
    simpa [suzukiBilinearGlobalLocalWeld] using h
  have hbc : b + c = 0 := by
    have h := hinvariant 0 1 0 1 1
    simp only [suzukiBilinearGlobalLocalWeld, ha, zero_mul, zero_add, mul_one] at h
    linear_combination h
  have hc : c = -b := by
    linear_combination hbc
  have hd : d = 0 := by
    have h := hcoincident 0 1 0 1 (by ring)
    simpa [suzukiBilinearGlobalLocalWeld] using h
  intro Q P S T
  simp only [suzukiBilinearGlobalLocalWeld,
    suzukiGlobalLocalCompoundNumerator, ha, hc, hd]
  ring

/-! ## Hermitian cross-Bezoutian -/

/-- Division-free numerator of the Hermitian Bezoutian of `(F,G)`. -/
def suzukiHermitianBezoutCross
    (F G : ℂ → ℂ) (z w : ℂ) : ℂ :=
  F z * (starRingEnd ℂ) (G w) -
    G z * (starRingEnd ℂ) (F w)

/-- Pointwise compound numerator for function pairs. -/
def suzukiGlobalLocalCompoundNumeratorFn
    (Q P S T : ℂ → ℂ) (z : ℂ) : ℂ :=
  suzukiGlobalLocalCompoundNumerator (Q z) (P z) (S z) (T z)

/-- Pointwise compound denominator for function pairs. -/
def suzukiGlobalLocalCompoundDenominatorFn
    (P T : ℂ → ℂ) (z : ℂ) : ℂ :=
  suzukiGlobalLocalCompoundDenominator (P z) (T z)

/-- **Compound Bezoutian product rule.**  This is the exact division-free
global-local signed kernel: local marked tensor minus global Xi deficit. -/
theorem suzukiGlobalLocalCompound_bezoutCross_productRule
    (Q P S T : ℂ → ℂ) (z w : ℂ) :
    suzukiHermitianBezoutCross
        (suzukiGlobalLocalCompoundNumeratorFn Q P S T)
        (suzukiGlobalLocalCompoundDenominatorFn P T) z w =
      T z * (starRingEnd ℂ) (T w) *
          suzukiHermitianBezoutCross Q P z w -
        P z * (starRingEnd ℂ) (P w) *
          suzukiHermitianBezoutCross S T z w := by
  simp only [suzukiHermitianBezoutCross,
    suzukiGlobalLocalCompoundNumeratorFn,
    suzukiGlobalLocalCompoundDenominatorFn,
    suzukiGlobalLocalCompoundNumerator,
    suzukiGlobalLocalCompoundDenominator, map_mul, map_sub]
  ring

/-- Exact curvature left by a relative, point-dependent affine gauge. -/
theorem suzukiHermitianBezoutCross_relativeGauge
    (N D r : ℂ → ℂ) (z w : ℂ) :
    suzukiHermitianBezoutCross (fun u => N u + r u * D u) D z w =
      suzukiHermitianBezoutCross N D z w +
        D z * (starRingEnd ℂ) (D w) *
          (r z - (starRingEnd ℂ) (r w)) := by
  simp only [suzukiHermitianBezoutCross, map_add, map_mul]
  ring

/-- Sharp algebraic correction to the affine-chart obstruction: a real
constant relative gauge changes the response but not its Hermitian Pick
cross-numerator. -/
theorem suzukiHermitianBezoutCross_realConstantGauge_invariant
    (N D : ℂ → ℂ) (delta : ℝ) (z w : ℂ) :
    suzukiHermitianBezoutCross
        (fun u => N u + (delta : ℂ) * D u) D z w =
      suzukiHermitianBezoutCross N D z w := by
  simp only [suzukiHermitianBezoutCross, map_add, map_mul, conj_ofReal]
  ring

/-- Standard connector from a homogeneous pair to the scalar Pick kernel of
its affine quotient.  Only this quotient-facing statement needs denominator
nonvanishing. -/
theorem suzukiScalarPickKernel_quotient_eq_bezoutCross
    (N D : ℂ → ℂ) {z w : ℂ}
    (hz : D z ≠ 0) (hw : D w ≠ 0) :
    suzukiScalarPickKernel (fun u => N u / D u) z w =
      suzukiHermitianBezoutCross N D z w /
        (D z * (starRingEnd ℂ) (D w) *
          (z - (starRingEnd ℂ) w)) := by
  simp only [suzukiScalarPickKernel, suzukiHermitianBezoutCross, map_div₀]
  field_simp [hz, hw]

/-! ## Exact Xi and marked-Volterra specialization -/

/-- Numerator member of the centered global Xi projective pair. -/
def suzukiXiDerivativePairNumerator (z : ℂ) : ℂ :=
  deriv XiC z

/-- Denominator member of the centered global Xi projective pair. -/
def suzukiXiDerivativePairDenominator (z : ℂ) : ℂ :=
  z ^ (2 : ℕ) * XiC z

/-- Compound numerator coupling any local pair to Suzuki's centered global
Xi multiplier pair. -/
def suzukiXiGlobalLocalCompoundNumerator
    (Q P : ℂ → ℂ) (z : ℂ) : ℂ :=
  suzukiGlobalLocalCompoundNumeratorFn Q P
    suzukiXiDerivativePairNumerator suzukiXiDerivativePairDenominator z

/-- Compound denominator coupling any local pair to Suzuki's centered global
Xi multiplier pair. -/
def suzukiXiGlobalLocalCompoundDenominator
    (P : ℂ → ℂ) (z : ℂ) : ℂ :=
  suzukiGlobalLocalCompoundDenominatorFn P
    suzukiXiDerivativePairDenominator z

/-- The Xi-specialized compound quotient is exactly local response minus
Suzuki's centered global multiplier. -/
theorem suzukiXiGlobalLocalCompound_quotient
    (Q P : ℂ → ℂ) {z : ℂ}
    (hP : P z ≠ 0)
    (hXiDenominator : suzukiXiDerivativePairDenominator z ≠ 0) :
    suzukiXiGlobalLocalCompoundNumerator Q P z /
        suzukiXiGlobalLocalCompoundDenominator P z =
      Q z / P z - suzukiShiftedXiMultiplier 0 z := by
  rw [suzukiShiftedXiMultiplier_eq]
  simp only [suzukiShiftedXiDenominator, zero_mul, sub_zero,
    suzukiXiGlobalLocalCompoundNumerator,
    suzukiXiGlobalLocalCompoundDenominator,
    suzukiGlobalLocalCompoundNumeratorFn,
    suzukiGlobalLocalCompoundDenominatorFn,
    suzukiXiDerivativePairNumerator,
    suzukiXiDerivativePairDenominator]
  exact suzukiGlobalLocalCompound_quotient
    (Q z) (P z) (deriv XiC z) (z ^ (2 : ℕ) * XiC z) hP hXiDenominator

/-- **Xi-deficit capstone.**  Exact division-free full-jump numerator for an
arbitrary local projective pair. -/
theorem suzukiXiGlobalLocalCompound_bezoutCross
    (Q P : ℂ → ℂ) (z w : ℂ) :
    suzukiHermitianBezoutCross
        (suzukiXiGlobalLocalCompoundNumerator Q P)
        (suzukiXiGlobalLocalCompoundDenominator P) z w =
      suzukiXiDerivativePairDenominator z *
          (starRingEnd ℂ) (suzukiXiDerivativePairDenominator w) *
          suzukiHermitianBezoutCross Q P z w -
        P z * (starRingEnd ℂ) (P w) *
          suzukiHermitianBezoutCross
            suzukiXiDerivativePairNumerator
            suzukiXiDerivativePairDenominator z w := by
  exact suzukiGlobalLocalCompound_bezoutCross_productRule Q P
    suzukiXiDerivativePairNumerator suzukiXiDerivativePairDenominator z w

/-- Existing marked Volterra affine-secant numerator, packaged as a spectral
function for the compound weld. -/
def suzukiMarkedAffineSecantNumeratorFn
    (alpha beta : ℂ) (x X y Y c : ℂ → ℂ) (z : ℂ) : ℂ :=
  suzukiComplexProjectiveAffineSecantTensor alpha beta
    (x z) (X z) (y z) (Y z) (c z)

/-- Existing marked Volterra affine-secant denominator, packaged as a
spectral function for the compound weld. -/
def suzukiMarkedAffineSecantDenominatorFn
    (alpha beta : ℂ) (y Y : ℂ → ℂ) (z : ℂ) : ℂ :=
  suzukiProjectiveAffineSecantDenominator alpha beta (y z) (Y z)

/-- Source-specific compound numerator joining the existing marked Volterra
secant to the centered global Xi pair. -/
def suzukiMarkedXiCompoundNumerator
    (alpha beta : ℂ) (x X y Y c : ℂ → ℂ) (z : ℂ) : ℂ :=
  suzukiXiGlobalLocalCompoundNumerator
    (suzukiMarkedAffineSecantNumeratorFn alpha beta x X y Y c)
    (suzukiMarkedAffineSecantDenominatorFn alpha beta y Y) z

/-- Source-specific compound denominator joining the existing marked
Volterra secant to the centered global Xi pair. -/
def suzukiMarkedXiCompoundDenominator
    (alpha beta : ℂ) (y Y : ℂ → ℂ) (z : ℂ) : ℂ :=
  suzukiXiGlobalLocalCompoundDenominator
    (suzukiMarkedAffineSecantDenominatorFn alpha beta y Y) z

/-- **Marked Volterra--Xi weld.**  The exact source specialization of the
compound Bezoutian product rule.  This is the canonical target whose positive
prime--Gamma Gram factorization remains the RH-bearing open core. -/
theorem suzukiMarkedXiCompound_bezoutCross
    (alpha beta : ℂ) (x X y Y c : ℂ → ℂ) (z w : ℂ) :
    suzukiHermitianBezoutCross
        (suzukiMarkedXiCompoundNumerator alpha beta x X y Y c)
        (suzukiMarkedXiCompoundDenominator alpha beta y Y) z w =
      suzukiXiDerivativePairDenominator z *
          (starRingEnd ℂ) (suzukiXiDerivativePairDenominator w) *
          suzukiHermitianBezoutCross
            (suzukiMarkedAffineSecantNumeratorFn alpha beta x X y Y c)
            (suzukiMarkedAffineSecantDenominatorFn alpha beta y Y) z w -
        suzukiMarkedAffineSecantDenominatorFn alpha beta y Y z *
          (starRingEnd ℂ)
            (suzukiMarkedAffineSecantDenominatorFn alpha beta y Y w) *
          suzukiHermitianBezoutCross
            suzukiXiDerivativePairNumerator
            suzukiXiDerivativePairDenominator z w := by
  exact suzukiXiGlobalLocalCompound_bezoutCross
    (suzukiMarkedAffineSecantNumeratorFn alpha beta x X y Y c)
    (suzukiMarkedAffineSecantDenominatorFn alpha beta y Y) z w

end

end RHTower
