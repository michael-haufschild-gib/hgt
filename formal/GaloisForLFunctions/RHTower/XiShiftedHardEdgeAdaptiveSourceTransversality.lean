import GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionHardEdgeSourceLaw
import GaloisForLFunctions.HTGeometry.FiniteGaussQuadrature
import GaloisForLFunctions.HTGeometry.PowerLinearizationBound

/-!
# Adaptive completed-source transversality at hard Gauss nodes

Reciprocal clearing sends every nonzero admitted root `x` to its actual hard coordinate
`u = x⁻¹ - y`.  The diagonal reverse-Euler landing of the adaptive mixed/completed arithmetic
source vanishes there, but its derivative is not an orientation chosen after aggregation:

`T'(u) = -2 * x⁻¹ * S'(u)^(2 : ℕ)`.

Thus the admission-dependent normalization `-(x / 2) * T'(u)` is exactly the square of the
cleared amplitude derivative.  It is a nonnegative source-transverse capacity, strictly positive
at every simple hard root.  This is the local quantity appearing in the denominator of the
hard-edge Padé-residue law; affine root spread is not.
-/

open Complex Matrix Polynomial Filter Topology

namespace RHTower

noncomputable section

/-- A nonzero admitted root becomes a root at the centered reciprocal hard coordinate after
reciprocal clearing. -/
theorem xiShiftedHardEdgeReciprocalClearing_eval_centeredReciprocal_eq_zero
    {P : Polynomial ℝ} {N : ℕ} (hP : P.natDegree ≤ N)
    (y : ℝ) {x : ℝ} (hx : x ≠ 0) (hroot : P.eval x = 0) :
    (xiShiftedHardEdgeReciprocalClearing y N P).eval (x⁻¹ - y) = 0 := by
  letI := invertibleOfNonzero hx
  have hreflect : (P.reflect N).eval x⁻¹ = 0 := by
    have hiff := Polynomial.eval₂_reflect_eq_zero_iff (RingHom.id ℝ) x N P hP
    simpa [Polynomial.eval₂_eq_eval_map, invOf_eq_inv] using hiff.mpr hroot
  simpa [xiShiftedHardEdgeReciprocalClearing] using hreflect

/-- At a root of `S`, the derivative of its squared reverse-Euler source is the negative
hard-coordinate factor times the square of `S'`.  The grade disappears completely. -/
theorem derivative_xiShiftedHardEdgeReverseEulerSource_sq_eval_root
    {S : Polynomial ℝ} {y u : ℝ} {d : ℕ}
    (hroot : S.eval u = 0) :
    (xiShiftedHardEdgeReverseEulerSource y d (S ^ (2 : ℕ))).derivative.eval u =
      -2 * (u + y) * (S.derivative.eval u) ^ (2 : ℕ) := by
  simp only [xiShiftedHardEdgeReverseEulerSource, Polynomial.derivative_sub,
    Polynomial.derivative_smul, Polynomial.derivative_mul, Polynomial.derivative_add,
    Polynomial.derivative_X, Polynomial.derivative_C, add_zero, Polynomial.derivative_pow,
    Nat.cast_ofNat, Nat.reduceSub, pow_one, Polynomial.eval_sub, Polynomial.eval_smul,
    Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_mul]
  rw [hroot]
  ring

/-- Every admitted hard root is a zero of the actual diagonal adaptive source landing. -/
theorem xiShiftedHardEdgeAdaptiveBilinearSource_eval_centeredReciprocal_eq_zero
    {A : Polynomial ℝ} {N : ℕ} (y : ℝ) {x : ℝ}
    (hA : A.natDegree ≤ N) (hx : x ≠ 0) (hroot : A.eval x = 0) :
    (xiShiftedHardEdgeAdaptiveBilinearSource y N N A A).eval (x⁻¹ - y) = 0 := by
  have hS := xiShiftedHardEdgeReciprocalClearing_eval_centeredReciprocal_eq_zero
    (P := A) (N := N) hA y hx hroot
  simp only [xiShiftedHardEdgeAdaptiveBilinearSource,
    xiShiftedHardEdgeReverseEulerSource, Polynomial.eval_sub, Polynomial.eval_smul,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.derivative_mul]
  rw [hS]
  ring

/-- **Source-first hard-node slope law.** The transverse derivative of the literal diagonal
adaptive source at a hard root is the negative square of the cleared amplitude derivative, with
the exact reciprocal-node factor. -/
theorem derivative_xiShiftedHardEdgeAdaptiveBilinearSource_eval_centeredReciprocal
    {A : Polynomial ℝ} {N : ℕ} (y : ℝ) {x : ℝ}
    (hA : A.natDegree ≤ N) (hx : x ≠ 0) (hroot : A.eval x = 0) :
    let S := xiShiftedHardEdgeReciprocalClearing y N A
    (xiShiftedHardEdgeAdaptiveBilinearSource y N N A A).derivative.eval (x⁻¹ - y) =
      -2 * x⁻¹ * (S.derivative.eval (x⁻¹ - y)) ^ (2 : ℕ) := by
  dsimp only
  have hS := xiShiftedHardEdgeReciprocalClearing_eval_centeredReciprocal_eq_zero
    (P := A) (N := N) hA y hx hroot
  rw [xiShiftedHardEdgeAdaptiveBilinearSource]
  rw [show N + N + 2 = 2 * N + 2 by omega]
  rw [show xiShiftedHardEdgeReciprocalClearing y N A *
      xiShiftedHardEdgeReciprocalClearing y N A =
      (xiShiftedHardEdgeReciprocalClearing y N A) ^ (2 : ℕ) by ring]
  rw [derivative_xiShiftedHardEdgeReverseEulerSource_sq_eval_root hS]
  congr 2
  field_simp
  ring

/-- Adaptive nonlinear capacity carried by the actual completed source at one admitted hard root.
The evaluation point and normalization are selected by that same admission. -/
def xiShiftedHardEdgeAdaptiveSourceTransverseCapacity
    (y : ℝ) (N : ℕ) (A : Polynomial ℝ) (x : ℝ) : ℝ :=
  -(x / 2) *
    (xiShiftedHardEdgeAdaptiveBilinearSource y N N A A).derivative.eval (x⁻¹ - y)

/-- **Exact capacity landing.** Adaptive source-transverse capacity is precisely the cleared
hard-amplitude derivative square. -/
theorem xiShiftedHardEdgeAdaptiveSourceTransverseCapacity_eq_sq
    {A : Polynomial ℝ} {N : ℕ} (y : ℝ) {x : ℝ}
    (hA : A.natDegree ≤ N) (hx : x ≠ 0) (hroot : A.eval x = 0) :
    xiShiftedHardEdgeAdaptiveSourceTransverseCapacity y N A x =
      ((xiShiftedHardEdgeReciprocalClearing y N A).derivative.eval (x⁻¹ - y)) ^ (2 : ℕ) := by
  rw [xiShiftedHardEdgeAdaptiveSourceTransverseCapacity,
    derivative_xiShiftedHardEdgeAdaptiveBilinearSource_eval_centeredReciprocal
      y hA hx hroot]
  field_simp

theorem xiShiftedHardEdgeAdaptiveSourceTransverseCapacity_nonneg
    {A : Polynomial ℝ} {N : ℕ} (y : ℝ) {x : ℝ}
    (hA : A.natDegree ≤ N) (hx : x ≠ 0) (hroot : A.eval x = 0) :
    0 ≤ xiShiftedHardEdgeAdaptiveSourceTransverseCapacity y N A x := by
  rw [xiShiftedHardEdgeAdaptiveSourceTransverseCapacity_eq_sq y hA hx hroot]
  positivity

/-- A simple hard root carries strictly positive adaptive source-transverse capacity. -/
theorem xiShiftedHardEdgeAdaptiveSourceTransverseCapacity_pos
    {A : Polynomial ℝ} {N : ℕ} (y : ℝ) {x : ℝ}
    (hA : A.natDegree ≤ N) (hx : x ≠ 0) (hroot : A.eval x = 0)
    (hsimple :
      (xiShiftedHardEdgeReciprocalClearing y N A).derivative.eval (x⁻¹ - y) ≠ 0) :
    0 < xiShiftedHardEdgeAdaptiveSourceTransverseCapacity y N A x := by
  rw [xiShiftedHardEdgeAdaptiveSourceTransverseCapacity_eq_sq y hA hx hroot]
  positivity

/-- At a positive simple Gauss node, the actual adaptive source crosses its hard zero with strict
negative slope.  This is a consequence of positive capacity, not an imposed orientation map. -/
theorem derivative_xiShiftedHardEdgeAdaptiveBilinearSource_neg_at_centeredReciprocal
    {A : Polynomial ℝ} {N : ℕ} (y : ℝ) {x : ℝ}
    (hA : A.natDegree ≤ N) (hx : 0 < x) (hroot : A.eval x = 0)
    (hsimple :
      (xiShiftedHardEdgeReciprocalClearing y N A).derivative.eval (x⁻¹ - y) ≠ 0) :
    (xiShiftedHardEdgeAdaptiveBilinearSource y N N A A).derivative.eval (x⁻¹ - y) < 0 := by
  rw [derivative_xiShiftedHardEdgeAdaptiveBilinearSource_eval_centeredReciprocal
    y hA hx.ne' hroot]
  have hinv : 0 < x⁻¹ := inv_pos.mpr hx
  have hsq : 0 <
      ((xiShiftedHardEdgeReciprocalClearing y N A).derivative.eval (x⁻¹ - y)) ^ (2 : ℕ) :=
    sq_pos_of_ne_zero hsimple
  nlinarith

/-- Clearing derivative at a hard root, in a denominator-free normalization.  This is the exact
bridge from ordinary Gauss derivative to reciprocal hard derivative. -/
theorem pow_mul_derivative_xiShiftedHardEdgeReciprocalClearing_eval_centeredReciprocal
    {P : Polynomial ℝ} {N : ℕ} (hP : P.natDegree ≤ N)
    (y : ℝ) {x : ℝ} (hx : x ≠ 0) (hroot : P.eval x = 0) :
    x ^ N * (xiShiftedHardEdgeReciprocalClearing y N P).derivative.eval (x⁻¹ - y) =
      -(x ^ (2 : ℕ) * P.derivative.eval x) := by
  letI := invertibleOfNonzero hx
  have hreflect : (P.reflect N).eval x⁻¹ = 0 := by
    have hiff := Polynomial.eval₂_reflect_eq_zero_iff (RingHom.id ℝ) x N P hP
    simpa [Polynomial.eval₂_eq_eval_map, invOf_eq_inv] using hiff.mpr hroot
  have hXP : (X * P.derivative).natDegree ≤ N := by
    by_cases hN : N = 0
    · subst N
      have hP0 : P.natDegree = 0 := Nat.le_zero.mp hP
      rw [Polynomial.derivative_of_natDegree_zero hP0, mul_zero]
      simp
    · calc
        (X * P.derivative).natDegree ≤ X.natDegree + P.derivative.natDegree :=
          Polynomial.natDegree_mul_le
        _ ≤ 1 + (P.natDegree - 1) := by
          simp
        _ ≤ N := by omega
  have hreflectDerivative :
      ((X * P.derivative).reflect N).eval x⁻¹ * x ^ N =
        x * P.derivative.eval x := by
    have h := Polynomial.eval₂_reflect_mul_pow (RingHom.id ℝ) x N
      (X * P.derivative) hXP
    simpa [Polynomial.eval₂_eq_eval_map, invOf_eq_inv] using h
  have hreverse := congrArg (Polynomial.eval x⁻¹)
    (reflect_X_mul_derivative_eq_reverseEuler (R := P) hP)
  simp only [Polynomial.eval_sub, Polynomial.eval_smul, Polynomial.eval_mul,
    Polynomial.eval_X] at hreverse
  rw [hreflect] at hreverse
  simp only [smul_eq_mul, mul_zero, zero_sub] at hreverse
  have hderivative :
      (xiShiftedHardEdgeReciprocalClearing y N P).derivative.eval (x⁻¹ - y) =
        (P.reflect N).derivative.eval x⁻¹ := by
    simp [xiShiftedHardEdgeReciprocalClearing, Polynomial.derivative_comp]
  rw [hderivative]
  rw [hreverse] at hreflectDerivative
  field_simp at hreflectDerivative ⊢
  nlinarith

/-- Source-transverse capacity has hard weight `2N`: after restoring that weight it is exactly the
ordinary derivative square with weight four. -/
theorem pow_mul_xiShiftedHardEdgeAdaptiveSourceTransverseCapacity_eq
    {P : Polynomial ℝ} {N : ℕ} (hP : P.natDegree ≤ N)
    (y : ℝ) {x : ℝ} (hx : x ≠ 0) (hroot : P.eval x = 0) :
    x ^ (2 * N) * xiShiftedHardEdgeAdaptiveSourceTransverseCapacity y N P x =
      x ^ (4 : ℕ) * (P.derivative.eval x) ^ (2 : ℕ) := by
  rw [xiShiftedHardEdgeAdaptiveSourceTransverseCapacity_eq_sq y hP hx hroot]
  have hderiv :=
    pow_mul_derivative_xiShiftedHardEdgeReciprocalClearing_eval_centeredReciprocal
      hP y hx hroot
  calc
    x ^ (2 * N) *
          ((xiShiftedHardEdgeReciprocalClearing y N P).derivative.eval (x⁻¹ - y)) ^ (2 : ℕ) =
        (x ^ N *
          (xiShiftedHardEdgeReciprocalClearing y N P).derivative.eval (x⁻¹ - y)) ^ (2 : ℕ) := by
            rw [show 2 * N = N + N by omega, pow_add]
            ring
    _ = (-(x ^ (2 : ℕ) * P.derivative.eval x)) ^ (2 : ℕ) := by rw [hderiv]
    _ = x ^ (4 : ℕ) * (P.derivative.eval x) ^ (2 : ℕ) := by ring

/-- Positive Gauss/Padé residue in absolute mass coordinates.  For an actual degree-`N` Gauss
polynomial, `christoffel s (N-1) x` is the quadrature weight at `x`. -/
def xiShiftedHardEdgeGaussPadeResidue
    (s : ℕ → ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  HTGeometry.christoffel s (N - 1) x / x

/-- Finite hard terminal mass attached to a Gauss root.  Existing hard-edge compactification
identifies its limit with divided-root completed-source mass. -/
def xiShiftedHardEdgeGaussTerminalMass
    (y : ℝ) (s : ℕ → ℝ) (N : ℕ) (P : Polynomial ℝ) (x : ℝ) : ℝ :=
  y * x ^ (4 : ℕ) * HTGeometry.christoffel s (N - 1) x * (P.derivative.eval x) ^ (2 : ℕ)

/-- Endogenous source capacity in the same normalization as the absolute Padé residue. -/
def xiShiftedHardEdgeAdaptiveEffectiveSourceCapacity
    (y : ℝ) (N : ℕ) (P : Polynomial ℝ) (x : ℝ) : ℝ :=
  y * x ^ (2 * N + 1) * xiShiftedHardEdgeAdaptiveSourceTransverseCapacity y N P x

/-- Hard-edge amplitude in the compactness normalization.  It is the reciprocal clearing divided
by its moving center to the admission depth, so its value is
`(1 + U / y)^N P((y + U)⁻¹)` whenever `y ≠ 0`. -/
def xiShiftedHardEdgeNormalizedReciprocalClearing
    (y : ℝ) (N : ℕ) (P : Polynomial ℝ) : Polynomial ℝ :=
  (y ^ N)⁻¹ • xiShiftedHardEdgeReciprocalClearing y N P

/-- Differentiation commutes with hard-edge normalization by the moving-center scalar. -/
theorem derivative_xiShiftedHardEdgeNormalizedReciprocalClearing_eval
    (y : ℝ) (N : ℕ) (P : Polynomial ℝ) (u : ℝ) :
    (xiShiftedHardEdgeNormalizedReciprocalClearing y N P).derivative.eval u =
      (y ^ N)⁻¹ *
        (xiShiftedHardEdgeReciprocalClearing y N P).derivative.eval u := by
  simp [xiShiftedHardEdgeNormalizedReciprocalClearing]

/-- If total first-order displacement `m*|b|` vanishes, a moving natural power of `1+b`
converges to one.  Unlike the fixed-exponent continuity lemma, this retains the cofinal degree
needed at the hard edge. -/
theorem tendsto_one_add_pow_of_nat_mul_abs_tendsto_zero
    {b : ℕ → ℝ} {m : ℕ → ℕ}
    (hsmall : Tendsto (fun k => (m k : ℝ) * |b k|) atTop (nhds 0)) :
    Tendsto (fun k => (1 + b k) ^ m k) atTop (nhds 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [Real.norm_eq_abs]
  apply squeeze_zero'
  · exact Eventually.of_forall fun k => abs_nonneg _
  · exact Eventually.of_forall fun k => by
      calc
        |(1 + b k) ^ m k - 1| =
            |((1 + b k) ^ m k - 1 - (m k : ℝ) * b k) +
              (m k : ℝ) * b k| := by ring_nf
        _ ≤ |(1 + b k) ^ m k - 1 - (m k : ℝ) * b k| +
              |(m k : ℝ) * b k| := abs_add_le _ _
        _ ≤ ((m k : ℝ) * |b k|) ^ (2 : ℕ) *
              Real.exp ((m k : ℝ) * |b k|) +
              (m k : ℝ) * |b k| := by
            gcongr
            · exact HTGeometry.abs_pow_sub_one_sub_le (b k) (m k)
            · rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg (m k))]
  · have hexp : Tendsto
        (fun k => Real.exp ((m k : ℝ) * |b k|)) atTop (nhds 1) := by
      have hcomp := Real.continuous_exp.continuousAt.tendsto.comp hsmall
      change Tendsto (fun k => Real.exp ((m k : ℝ) * |b k|))
        atTop (nhds (Real.exp 0)) at hcomp
      simpa only [Real.exp_zero] using hcomp
    simpa using (hsmall.pow 2).mul hexp |>.add hsmall

/-- The compact hard-node factor has no residual normalization whenever degree times reciprocal
hard displacement vanishes. -/
theorem tendsto_hardEdgeNodeFactor_one
    {y u : ℕ → ℝ} {N : ℕ → ℕ}
    (hdenom : ∀ k, y k + u k ≠ 0)
    (hsmall : Tendsto
      (fun k => ((2 * N k + 1 : ℕ) : ℝ) * |u k / (y k + u k)|)
      atTop (nhds 0)) :
    Tendsto
      (fun k => (y k * (y k + u k)⁻¹) ^ (2 * N k + 1))
      atTop (nhds 1) := by
  have hsmall' : Tendsto
      (fun k => ((2 * N k + 1 : ℕ) : ℝ) *
        |-u k / (y k + u k)|) atTop (nhds 0) := by
    simpa only [abs_div, abs_neg] using hsmall
  have hpow := tendsto_one_add_pow_of_nat_mul_abs_tendsto_zero hsmall'
  convert hpow using 1
  funext k
  congr 1
  field_simp [hdenom k]
  ring

/-- **Compact-normalized source-capacity law.** At an admitted hard root, effective adaptive
source capacity is exactly the squared derivative of the compact-normalized hard amplitude,
weighted only by the dimensionless node `y*x`.  Hence for a simple compact hard root the source
factor itself has no hidden growing or vanishing normalization; any Padé-residue extinction must
come through terminal mass. -/
theorem xiShiftedHardEdgeAdaptiveEffectiveSourceCapacity_eq_normalizedDerivative_sq
    {P : Polynomial ℝ} {N : ℕ} (hP : P.natDegree ≤ N)
    {y x : ℝ} (hy : y ≠ 0) (hx : x ≠ 0) (hroot : P.eval x = 0) :
    xiShiftedHardEdgeAdaptiveEffectiveSourceCapacity y N P x =
      (y * x) ^ (2 * N + 1) *
        ((xiShiftedHardEdgeNormalizedReciprocalClearing y N P).derivative.eval
          (x⁻¹ - y)) ^ (2 : ℕ) := by
  rw [xiShiftedHardEdgeAdaptiveEffectiveSourceCapacity,
    xiShiftedHardEdgeAdaptiveSourceTransverseCapacity_eq_sq y hP hx hroot,
    derivative_xiShiftedHardEdgeNormalizedReciprocalClearing_eval]
  field_simp [pow_ne_zero N hy]
  ring

/-- **Adaptive source-capacity/Padé-residue law.** At every nonzero admitted root, actual Gauss
residue times endogenous completed-source transverse capacity is exactly hard terminal mass, with
the forced reciprocal weight.  This is source-first and nonlinear in current admission. -/
theorem xiShiftedHardEdgeGaussPadeResidue_mul_sourceTransverseCapacity_eq_terminalMass
    {s : ℕ → ℝ} {P : Polynomial ℝ} {N : ℕ} (hP : P.natDegree ≤ N)
    (y : ℝ) {x : ℝ} (hx : x ≠ 0) (hroot : P.eval x = 0) :
    xiShiftedHardEdgeGaussPadeResidue s N x * y * x ^ (2 * N + 1) *
        xiShiftedHardEdgeAdaptiveSourceTransverseCapacity y N P x =
      xiShiftedHardEdgeGaussTerminalMass y s N P x := by
  rw [xiShiftedHardEdgeGaussPadeResidue, xiShiftedHardEdgeGaussTerminalMass]
  have hcapacity :=
    pow_mul_xiShiftedHardEdgeAdaptiveSourceTransverseCapacity_eq hP y hx hroot
  rw [pow_succ]
  field_simp
  calc
    HTGeometry.christoffel s (N - 1) x * y * x ^ (2 * N) *
          xiShiftedHardEdgeAdaptiveSourceTransverseCapacity y N P x =
        HTGeometry.christoffel s (N - 1) x * y *
          (x ^ (2 * N) *
            xiShiftedHardEdgeAdaptiveSourceTransverseCapacity y N P x) := by ring
    _ = HTGeometry.christoffel s (N - 1) x * y *
          (x ^ (4 : ℕ) * (P.derivative.eval x) ^ (2 : ℕ)) := by rw [hcapacity]
    _ = HTGeometry.christoffel s (N - 1) x * x ^ (4 : ℕ) * y *
          (P.derivative.eval x) ^ (2 : ℕ) := by ring

/-- Capacity-product form of the same law. -/
theorem xiShiftedHardEdgeGaussPadeResidue_mul_effectiveSourceCapacity_eq_terminalMass
    {s : ℕ → ℝ} {P : Polynomial ℝ} {N : ℕ} (hP : P.natDegree ≤ N)
    (y : ℝ) {x : ℝ} (hx : x ≠ 0) (hroot : P.eval x = 0) :
    xiShiftedHardEdgeGaussPadeResidue s N x *
        xiShiftedHardEdgeAdaptiveEffectiveSourceCapacity y N P x =
      xiShiftedHardEdgeGaussTerminalMass y s N P x := by
  rw [xiShiftedHardEdgeAdaptiveEffectiveSourceCapacity]
  simpa only [mul_assoc] using
    (xiShiftedHardEdgeGaussPadeResidue_mul_sourceTransverseCapacity_eq_terminalMass
      (s := s) hP y hx hroot)

/-- Where effective source capacity is nonzero, the Padé residue is exactly terminal mass divided
by that admission-sensitive capacity. -/
theorem xiShiftedHardEdgeGaussPadeResidue_eq_terminalMass_div_effectiveSourceCapacity
    {s : ℕ → ℝ} {P : Polynomial ℝ} {N : ℕ} (hP : P.natDegree ≤ N)
    (y : ℝ) {x : ℝ} (hx : x ≠ 0) (hroot : P.eval x = 0)
    (hcapacity : xiShiftedHardEdgeAdaptiveEffectiveSourceCapacity y N P x ≠ 0) :
    xiShiftedHardEdgeGaussPadeResidue s N x =
      xiShiftedHardEdgeGaussTerminalMass y s N P x /
        xiShiftedHardEdgeAdaptiveEffectiveSourceCapacity y N P x := by
  apply (eq_div_iff hcapacity).mpr
  exact xiShiftedHardEdgeGaussPadeResidue_mul_effectiveSourceCapacity_eq_terminalMass
    hP y hx hroot

/-- Equivalent derivative-only form of the source-capacity/Padé-residue law. -/
theorem neg_gaussPadeResidue_mul_sourceDerivative_div_two_eq_terminalMass
    {s : ℕ → ℝ} {P : Polynomial ℝ} {N : ℕ} (hP : P.natDegree ≤ N)
    (y : ℝ) {x : ℝ} (hx : x ≠ 0) (hroot : P.eval x = 0) :
    -(xiShiftedHardEdgeGaussPadeResidue s N x * y * x ^ (2 * N + 2) *
        (xiShiftedHardEdgeAdaptiveBilinearSource y N N P P).derivative.eval (x⁻¹ - y)) / 2 =
      xiShiftedHardEdgeGaussTerminalMass y s N P x := by
  rw [← xiShiftedHardEdgeGaussPadeResidue_mul_sourceTransverseCapacity_eq_terminalMass
    hP y hx hroot]
  rw [xiShiftedHardEdgeAdaptiveSourceTransverseCapacity]
  rw [show 2 * N + 2 = (2 * N + 1) + 1 by omega, pow_succ]
  ring

/-! ## Literal shifted-Xi canonical specialization -/

/-- Source-transverse capacity of the actual inverse-Hankel admission and its completed
`P^sharp` hard-edge producer. -/
def xiShiftedCanonicalAdmissionHardEdgeSourceTransverseCapacity
    (w : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  -(x / 2) *
    (xiShiftedCanonicalAdmissionHardEdgeSource w n).derivative.eval (x⁻¹ - w ^ (2 : ℕ))

/-- Actual canonical Padé residue selected by the shifted-Xi moment admission. -/
def xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue
    (w : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  xiShiftedHardEdgeGaussPadeResidue (xiShiftedRealMomentSequence w) n x

/-- Actual canonical finite hard terminal mass. -/
def xiShiftedCanonicalAdmissionHardEdgeGaussTerminalMass
    (w : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  xiShiftedHardEdgeGaussTerminalMass (w ^ (2 : ℕ)) (xiShiftedRealMomentSequence w) n
    (HTGeometry.monicMomentAdmissionPolynomial (xiShiftedRealMomentSequence w) n) x

/-- Actual canonical effective source capacity paired with the absolute Padé residue. -/
def xiShiftedCanonicalAdmissionHardEdgeEffectiveSourceCapacity
    (w : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (w ^ (2 : ℕ)) * x ^ (2 * n + 1) *
    xiShiftedCanonicalAdmissionHardEdgeSourceTransverseCapacity w n x

/-- Compact-normalized hard amplitude of the actual shifted-Xi inverse-Hankel admission. -/
def xiShiftedCanonicalAdmissionHardEdgeNormalizedClearing
    (w : ℝ) (n : ℕ) : Polynomial ℝ :=
  xiShiftedHardEdgeNormalizedReciprocalClearing (w ^ (2 : ℕ)) n
    (HTGeometry.monicMomentAdmissionPolynomial (xiShiftedRealMomentSequence w) n)

/-- Canonical source-transverse capacity is the square of the reciprocal-cleared admission
derivative at every nonzero root. -/
theorem xiShiftedCanonicalAdmissionHardEdgeSourceTransverseCapacity_eq_sq
    {w : ℝ} {n : ℕ} {x : ℝ} (hx : x ≠ 0)
    (hroot :
      (HTGeometry.monicMomentAdmissionPolynomial
        (xiShiftedRealMomentSequence w) n).eval x = 0) :
    xiShiftedCanonicalAdmissionHardEdgeSourceTransverseCapacity w n x =
      ((xiShiftedHardEdgeReciprocalClearing (w ^ (2 : ℕ)) n
        (HTGeometry.monicMomentAdmissionPolynomial
          (xiShiftedRealMomentSequence w) n)).derivative.eval (x⁻¹ - w ^ (2 : ℕ))) ^ (2 : ℕ) := by
  let P := HTGeometry.monicMomentAdmissionPolynomial (xiShiftedRealMomentSequence w) n
  have hP : P.natDegree ≤ n := by
    dsimp only [P]
    rw [HTGeometry.monicMomentAdmissionPolynomial_natDegree]
  simpa only [xiShiftedCanonicalAdmissionHardEdgeSourceTransverseCapacity,
    xiShiftedCanonicalAdmissionHardEdgeSource,
    xiShiftedHardEdgeAdaptiveSourceTransverseCapacity, P] using
    (xiShiftedHardEdgeAdaptiveSourceTransverseCapacity_eq_sq
      (y := w ^ (2 : ℕ)) hP hx hroot
      : xiShiftedHardEdgeAdaptiveSourceTransverseCapacity (w ^ (2 : ℕ)) n P x = _)

/-- **Literal shifted-Xi arithmetic source-capacity law.** The actual canonical Padé residue times
the actual adaptive mixed/completed `P^sharp` transverse source capacity equals finite hard
terminal mass.  Admission, degree, reciprocal chart, and arithmetic source all vary together. -/
theorem xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue_mul_sourceTransverseCapacity_eq_terminalMass
    {w : ℝ} {n : ℕ} {x : ℝ} (hx : x ≠ 0)
    (hroot :
      (HTGeometry.monicMomentAdmissionPolynomial
        (xiShiftedRealMomentSequence w) n).eval x = 0) :
    xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue w n x *
        (w ^ (2 : ℕ)) * x ^ (2 * n + 1) *
          xiShiftedCanonicalAdmissionHardEdgeSourceTransverseCapacity w n x =
      xiShiftedCanonicalAdmissionHardEdgeGaussTerminalMass w n x := by
  let P := HTGeometry.monicMomentAdmissionPolynomial (xiShiftedRealMomentSequence w) n
  have hP : P.natDegree ≤ n := by
    dsimp only [P]
    rw [HTGeometry.monicMomentAdmissionPolynomial_natDegree]
  simpa only [xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue,
    xiShiftedCanonicalAdmissionHardEdgeGaussTerminalMass,
    xiShiftedCanonicalAdmissionHardEdgeSourceTransverseCapacity,
    xiShiftedCanonicalAdmissionHardEdgeSource,
    xiShiftedHardEdgeAdaptiveSourceTransverseCapacity, P] using
    (xiShiftedHardEdgeGaussPadeResidue_mul_sourceTransverseCapacity_eq_terminalMass
      (s := xiShiftedRealMomentSequence w) hP (w ^ (2 : ℕ)) hx hroot :
      xiShiftedHardEdgeGaussPadeResidue (xiShiftedRealMomentSequence w) n x *
          (w ^ (2 : ℕ)) * x ^ (2 * n + 1) *
            xiShiftedHardEdgeAdaptiveSourceTransverseCapacity (w ^ (2 : ℕ)) n P x = _)

/-- Canonical capacity-product form of the literal arithmetic law. -/
theorem xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue_mul_effectiveSourceCapacity_eq_terminalMass
    {w : ℝ} {n : ℕ} {x : ℝ} (hx : x ≠ 0)
    (hroot :
      (HTGeometry.monicMomentAdmissionPolynomial
        (xiShiftedRealMomentSequence w) n).eval x = 0) :
    xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue w n x *
        xiShiftedCanonicalAdmissionHardEdgeEffectiveSourceCapacity w n x =
      xiShiftedCanonicalAdmissionHardEdgeGaussTerminalMass w n x := by
  rw [xiShiftedCanonicalAdmissionHardEdgeEffectiveSourceCapacity]
  simpa only [mul_assoc] using
    (xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue_mul_sourceTransverseCapacity_eq_terminalMass
      hx hroot)

/-- **Literal compact-normalized shifted-Xi capacity law.** The effective capacity of the actual
adaptive mixed/completed source has exactly the compact hard-amplitude normalization. -/
theorem xiShiftedCanonicalAdmissionHardEdgeEffectiveSourceCapacity_eq_normalizedDerivative_sq
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} {x : ℝ} (hx : x ≠ 0)
    (hroot :
      (HTGeometry.monicMomentAdmissionPolynomial
        (xiShiftedRealMomentSequence w) n).eval x = 0) :
    xiShiftedCanonicalAdmissionHardEdgeEffectiveSourceCapacity w n x =
      (w ^ (2 : ℕ) * x) ^ (2 * n + 1) *
        ((xiShiftedCanonicalAdmissionHardEdgeNormalizedClearing w n).derivative.eval
          (x⁻¹ - w ^ (2 : ℕ))) ^ (2 : ℕ) := by
  let P := HTGeometry.monicMomentAdmissionPolynomial (xiShiftedRealMomentSequence w) n
  have hP : P.natDegree ≤ n := by
    dsimp only [P]
    rw [HTGeometry.monicMomentAdmissionPolynomial_natDegree]
  have hw0 : w ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 (ne_of_gt (lt_trans (by norm_num) hw))
  simpa only [xiShiftedCanonicalAdmissionHardEdgeEffectiveSourceCapacity,
    xiShiftedCanonicalAdmissionHardEdgeSourceTransverseCapacity,
    xiShiftedCanonicalAdmissionHardEdgeSource,
    xiShiftedCanonicalAdmissionHardEdgeNormalizedClearing,
    xiShiftedHardEdgeAdaptiveEffectiveSourceCapacity,
    xiShiftedHardEdgeAdaptiveSourceTransverseCapacity, P] using
    (xiShiftedHardEdgeAdaptiveEffectiveSourceCapacity_eq_normalizedDerivative_sq
      hP hw0 hx hroot)

/-- **Compact-limit elimination of capacity escape.** Along actual canonical shifted-Xi
admissions, if the hard node has coordinate `u`, the cofinal degree resolves that coordinate with
vanishing total displacement, and normalized hard derivatives converge to `d`, then effective
adaptive source capacity converges to `d^(2 : ℕ)`.  Thus at a simple compact hard root (`d ≠ 0`) Padé
extinction cannot be caused by source-capacity blow-up or collapse. -/
theorem tendsto_xiShiftedCanonicalAdmissionHardEdgeEffectiveSourceCapacity
    {w : ℕ → ℝ} {n : ℕ → ℕ} {x u : ℕ → ℝ} {d : ℝ}
    (hw : ∀ k, 1 / 2 < w k)
    (hdenom : ∀ k, w k ^ (2 : ℕ) + u k ≠ 0)
    (hx : ∀ k, x k = (w k ^ (2 : ℕ) + u k)⁻¹)
    (hroot : ∀ k,
      (HTGeometry.monicMomentAdmissionPolynomial
        (xiShiftedRealMomentSequence (w k)) (n k)).eval (x k) = 0)
    (hsmall : Tendsto
      (fun k => ((2 * n k + 1 : ℕ) : ℝ) *
        |u k / (w k ^ (2 : ℕ) + u k)|) atTop (nhds 0))
    (hderiv : Tendsto
      (fun k =>
        (xiShiftedCanonicalAdmissionHardEdgeNormalizedClearing
          (w k) (n k)).derivative.eval ((x k)⁻¹ - w k ^ (2 : ℕ)))
      atTop (nhds d)) :
    Tendsto
      (fun k =>
        xiShiftedCanonicalAdmissionHardEdgeEffectiveSourceCapacity
          (w k) (n k) (x k))
      atTop (nhds (d ^ (2 : ℕ))) := by
  have hfactor : Tendsto
      (fun k => (w k ^ (2 : ℕ) * x k) ^ (2 * n k + 1)) atTop (nhds 1) := by
    have hfactor' := tendsto_hardEdgeNodeFactor_one
      (y := fun k => w k ^ (2 : ℕ)) (u := u) (N := n) hdenom hsmall
    simpa only [hx] using hfactor'
  have hproduct := hfactor.mul (hderiv.pow 2)
  have heq :
      (fun k => (w k ^ (2 : ℕ) * x k) ^ (2 * n k + 1) *
        ((xiShiftedCanonicalAdmissionHardEdgeNormalizedClearing
          (w k) (n k)).derivative.eval ((x k)⁻¹ - w k ^ (2 : ℕ))) ^ (2 : ℕ)) =ᶠ[atTop]
      (fun k => xiShiftedCanonicalAdmissionHardEdgeEffectiveSourceCapacity
        (w k) (n k) (x k)) := by
    filter_upwards with k
    symm
    exact xiShiftedCanonicalAdmissionHardEdgeEffectiveSourceCapacity_eq_normalizedDerivative_sq
      (hw k) (by rw [hx k]; exact inv_ne_zero (hdenom k)) (hroot k)
  simpa only [one_mul] using hproduct.congr' heq

/-- In a positive shifted-Xi chamber, every positive canonical Gauss node has positive absolute
Padé residue. -/
theorem xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue_pos
    {w : ℝ} {n : ℕ} {x : ℝ}
    (hH : (HTGeometry.momentHankelMatrix (xiShiftedRealMomentSequence w) (n + 2)).PosDef)
    (hx : 0 < x) :
    0 < xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue w n x := by
  let hbelow := HTGeometry.positiveMomentFormBelow_of_hankelPosDef hH
  rw [xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue,
    xiShiftedHardEdgeGaussPadeResidue]
  exact div_pos (HTGeometry.christoffel_pos_below hbelow (n - 1) (by omega) x) hx

/-- A positive simple canonical Gauss root has positive effective completed-source capacity. -/
theorem xiShiftedCanonicalAdmissionHardEdgeEffectiveSourceCapacity_pos
    {w : ℝ} (hw : 1 / 2 < w) {n : ℕ} {x : ℝ} (hx : 0 < x)
    (hroot :
      (HTGeometry.monicMomentAdmissionPolynomial
        (xiShiftedRealMomentSequence w) n).eval x = 0)
    (hsimple :
      (xiShiftedHardEdgeReciprocalClearing (w ^ (2 : ℕ)) n
        (HTGeometry.monicMomentAdmissionPolynomial
          (xiShiftedRealMomentSequence w) n)).derivative.eval (x⁻¹ - w ^ (2 : ℕ)) ≠ 0) :
    0 < xiShiftedCanonicalAdmissionHardEdgeEffectiveSourceCapacity w n x := by
  rw [xiShiftedCanonicalAdmissionHardEdgeEffectiveSourceCapacity]
  have hsource : 0 < xiShiftedCanonicalAdmissionHardEdgeSourceTransverseCapacity w n x := by
    rw [xiShiftedCanonicalAdmissionHardEdgeSourceTransverseCapacity_eq_sq hx.ne' hroot]
    exact sq_pos_of_ne_zero hsimple
  positivity

/-- Exact hostile-test identity for the old affine hard-edge observation.  Fixed hard levels `u,v`
are compressed by an additional factor of order `y⁻¹`; therefore affine root-spread collapse is
compatible with a nontrivial reciprocal hard limit. -/
theorem affineHardEdgeCoordinate_sub_affineHardEdgeCoordinate
    {y u v : ℝ} (hu : y + u ≠ 0) (hv : y + v ≠ 0) :
    (y - u) / (y + u) - (y - v) / (y + v) =
      2 * y * (v - u) / ((y + u) * (y + v)) := by
  field_simp
  ring

end

end RHTower
