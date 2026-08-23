import GaloisForLFunctions.HTGeometry.AntiLownerSignSwitch
import GaloisForLFunctions.RHTower.ThetaCuspTiltFluxWeilParityEulerRayWeld
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeMomentDerivatives
import GaloisForLFunctions.RHTower.XiResolventHankelMatrixLadder
import GaloisForLFunctions.RHTower.XiLogDerivSymmetry

/-!
# The squared-Euler anti-Lowner/Hankel endpoint

[LEAN-PROVED] [BRIDGE/REDUCTION] [NOVELTY UNVERIFIED]

The complete squared-Euler kernel is an anti-Lowner matrix for
`Q(x) = xiSquaredEulerFullQ x`.  Audenaert's anti-Lowner theorem associates to `Q` the two
functions

`X ↦ Q(√X) / √X` and `X ↦ √X * Q(√X)`.

This file identifies them with the Xi resolvent response `R(X)` and `X * R(X)`, respectively.
It also proves the exact off-diagonal splitting

`K_Q + L_Q = 2 L_(X R(X))`,

`K_Q - L_Q = 2 x y L_(-R)(x²,y²)`.

Most importantly, every normalized derivative of `R` is the corresponding Xi resolvent moment.
Consequently the derivative Hankel matrix of the decreasing Audenaert transform is literally the
existing resolvent Hankel matrix, whose all-degree positive-semidefinite hierarchy is equivalent to
RH at every one fixed positive shift.

This is not an RH proof.  It identifies the remaining producer precisely: derive positivity of
these collision/derivative Hankel matrices from universal finite anti-Lowner positivity.  The
imported sign-switch theorem formalizes one Schur-complement core of Audenaert's finite-order
bridge and its finite arbitrary-sign iteration; the divided-difference/collision passage remains
open here.
-/

open Complex

namespace RHTower

noncomputable section

/-! ## The full positive ray, not only the absolute Euler half-ray -/

/-- The centered Xi logarithmic derivative equals the complete squared-Euler response on every
positive real node.  The previous exterior weld required `1/2 < x`; global Schwarz symmetry of
`logDeriv xi` removes that artificial restriction. -/
theorem logDeriv_xiCent_ofReal_eq_fullQ_pos
    {x : ℝ} (hx : 0 < x) :
    logDeriv xiCent (x : ℂ) = (xiSquaredEulerFullQ x : ℂ) := by
  have hconj := logDeriv_xi_conj ((1 / 2 : ℂ) + (x : ℂ))
  have harg :
      (starRingEnd ℂ) ((1 / 2 : ℂ) + (x : ℂ)) =
        (1 / 2 : ℂ) + (x : ℂ) := by
    apply Complex.ext <;> norm_num
  have hreal :
      logDeriv xi ((1 / 2 : ℂ) + (x : ℂ)) =
        (starRingEnd ℂ) (logDeriv xi ((1 / 2 : ℂ) + (x : ℂ))) := by
    rw [harg] at hconj
    exact hconj
  have him : (logDeriv xi ((1 / 2 : ℂ) + (x : ℂ))).im = 0 := by
    have := congrArg Complex.im hreal
    simp only [Complex.conj_im] at this
    linarith
  apply Complex.ext
  · rw [logDeriv_xiCent_eq_shift]
    simpa only [Complex.ofReal_re] using
      (xiSquaredEulerFullQ_eq_logDeriv_re hx).symm
  · rw [logDeriv_xiCent_eq_shift]
    simpa only [Complex.ofReal_im] using him

/-- The RH-critical logarithmic-derivative kernel is the complete squared-Euler anti-Lowner
kernel on the entire positive real ray. -/
theorem criticalLogDerivKernel_ofReal_eq_fullKernel_pos
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    criticalLogDerivKernel (x : ℂ) (y : ℂ) =
      (xiSquaredEulerFullKernel x y : ℂ) := by
  rw [criticalLogDerivKernel, logDeriv_xiCent_ofReal_eq_fullQ_pos hx,
    logDeriv_xiCent_ofReal_eq_fullQ_pos hy]
  simp only [Complex.conj_ofReal]
  rw [xiSquaredEulerFullKernel, eulerRayResponseKernel]
  push_cast
  rfl

/-! ## Audenaert's two transforms -/

/-- Decreasing Audenaert transform of the squared-Euler response.  It is the real zeroth Xi
resolvent moment. -/
def xiEulerAudenaertDecreasing (X : ℝ) : ℝ :=
  2 * squaredXiRadialField X

/-- Increasing Audenaert transform of the squared-Euler response. -/
def xiEulerAudenaertIncreasing (X : ℝ) : ℝ :=
  X * xiEulerAudenaertDecreasing X

/-- Off-diagonal real Loewner divided difference. -/
def eulerOffDiagonalLoewnerKernel (f : ℝ → ℝ) (X Y : ℝ) : ℝ :=
  (f X - f Y) / (X - Y)

/-- The decreasing transform is exactly the real zeroth resolvent moment. -/
theorem xiEulerAudenaertDecreasing_eq_resolventMoment_re
    {X : ℝ} (hX : 0 ≤ X) :
    xiEulerAudenaertDecreasing X = (xiResolventMoment 0 X).re := by
  rw [xiEulerAudenaertDecreasing, squaredXiRadialField,
    xiShiftedReciprocalMoment_eq_xiResolventMoment hX]
  ring

/-- Audenaert's decreasing transform has its literal square-root form
`Q(√X) / √X = R(X)`. -/
theorem xiEulerAudenaertDecreasing_eq_fullQ_div_sqrt
    {X : ℝ} (hX : 0 < X) :
    xiEulerAudenaertDecreasing X =
      xiSquaredEulerFullQ (Real.sqrt X) / Real.sqrt X := by
  have hs : 0 < Real.sqrt X := Real.sqrt_pos.2 hX
  have hs2 : (Real.sqrt X) ^ 2 = X := Real.sq_sqrt hX.le
  have hF := squaredXiRadialField_sq_eq hs
  rw [hs2] at hF
  have hQ : xiSquaredEulerFullQ (Real.sqrt X) =
      xiRealLogDeriv (Real.sqrt X) := by
    simpa only [xiRealLogDeriv] using xiSquaredEulerFullQ_eq_logDeriv_re hs
  rw [xiEulerAudenaertDecreasing, hQ, hF]
  field_simp [hs.ne']

/-- Audenaert's increasing transform has its literal square-root form
`√X Q(√X) = X R(X)`. -/
theorem xiEulerAudenaertIncreasing_eq_sqrt_mul_fullQ
    {X : ℝ} (hX : 0 < X) :
    xiEulerAudenaertIncreasing X =
      Real.sqrt X * xiSquaredEulerFullQ (Real.sqrt X) := by
  have hs : 0 < Real.sqrt X := Real.sqrt_pos.2 hX
  have hs2 : (Real.sqrt X) ^ 2 = X := Real.sq_sqrt hX.le
  rw [xiEulerAudenaertIncreasing,
    xiEulerAudenaertDecreasing_eq_fullQ_div_sqrt hX]
  rw [← hs2, Real.sqrt_sq hs.le]
  field_simp [hs.ne']

/-- Positive-ray response factorization `Q(x) = x R(x²)`. -/
theorem xiSquaredEulerFullQ_eq_mul_audenaertDecreasing
    {x : ℝ} (hx : 0 < x) :
    xiSquaredEulerFullQ x = x * xiEulerAudenaertDecreasing (x ^ 2) := by
  have hX : 0 < x ^ 2 := sq_pos_of_pos hx
  have h := xiEulerAudenaertDecreasing_eq_fullQ_div_sqrt hX
  rw [Real.sqrt_sq hx.le] at h
  field_simp [hx.ne'] at h
  linarith

/-! ## Exact anti-Lowner/Loewner splitting -/

/-- The sum of the full anti-Lowner kernel and the ordinary Loewner kernel of `Q` is twice the
Loewner kernel of Audenaert's increasing transform after the square map. -/
theorem xiSquaredEulerFullKernel_add_fullQLoewner_eq_increasingLoewner
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    xiSquaredEulerFullKernel x y +
        eulerOffDiagonalLoewnerKernel xiSquaredEulerFullQ x y =
      2 * eulerOffDiagonalLoewnerKernel xiEulerAudenaertIncreasing (x ^ 2) (y ^ 2) := by
  have hsum : x + y ≠ 0 := by positivity
  have hsq : x ^ 2 - y ^ 2 ≠ 0 := by
    intro h
    have hfactor : (x - y) * (x + y) = 0 := by nlinarith
    have hsub : x - y = 0 := (mul_eq_zero.mp hfactor).resolve_right hsum
    exact hxy (sub_eq_zero.mp hsub)
  rw [xiSquaredEulerFullKernel, eulerRayResponseKernel,
    eulerOffDiagonalLoewnerKernel, eulerOffDiagonalLoewnerKernel,
    xiSquaredEulerFullQ_eq_mul_audenaertDecreasing hx,
    xiSquaredEulerFullQ_eq_mul_audenaertDecreasing hy]
  simp only [xiEulerAudenaertIncreasing]
  field_simp [hxy, hsum, hsq]
  ring

/-- The difference of the full anti-Lowner kernel and the ordinary Loewner kernel of `Q` is a
positive diagonal congruence of the Loewner kernel of Audenaert's decreasing transform with its
matrix-monotone orientation reversed. -/
theorem xiSquaredEulerFullKernel_sub_fullQLoewner_eq_decreasingLoewner
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    xiSquaredEulerFullKernel x y -
        eulerOffDiagonalLoewnerKernel xiSquaredEulerFullQ x y =
      2 * x * y * eulerOffDiagonalLoewnerKernel
        (fun X => -xiEulerAudenaertDecreasing X) (x ^ 2) (y ^ 2) := by
  have hsum : x + y ≠ 0 := by positivity
  have hsq : x ^ 2 - y ^ 2 ≠ 0 := by
    intro h
    have hfactor : (x - y) * (x + y) = 0 := by nlinarith
    have hsub : x - y = 0 := (mul_eq_zero.mp hfactor).resolve_right hsum
    exact hxy (sub_eq_zero.mp hsub)
  rw [xiSquaredEulerFullKernel, eulerRayResponseKernel,
    eulerOffDiagonalLoewnerKernel, eulerOffDiagonalLoewnerKernel,
    xiSquaredEulerFullQ_eq_mul_audenaertDecreasing hx,
    xiSquaredEulerFullQ_eq_mul_audenaertDecreasing hy]
  field_simp [hxy, hsum, hsq]
  ring

/-! ## Collision derivatives are the RH-deciding resolvent moments -/

/-- Every derivative of the decreasing Audenaert transform is the corresponding resolvent moment,
with the exact Stieltjes sign and factorial. -/
theorem iteratedDeriv_xiEulerAudenaertDecreasing
    (n : ℕ) {X : ℝ} (hX : 0 < X) :
    iteratedDeriv n xiEulerAudenaertDecreasing X =
      (-1 : ℝ) ^ n * (n.factorial : ℝ) * (xiResolventMoment n X).re := by
  change iteratedDeriv n (fun X => 2 * squaredXiRadialField X) X = _
  rw [iteratedDeriv_const_mul_field,
    iteratedDeriv_squaredXiRadialField n hX,
    xiShiftedReciprocalMoment_eq_xiResolventMoment hX.le]
  ring

/-- Factorial-normalized alternating derivative of the decreasing Audenaert transform. -/
def xiEulerAudenaertDerivativeMoment (n : ℕ) (X : ℝ) : ℝ :=
  (-1 : ℝ) ^ n / (n.factorial : ℝ) *
    iteratedDeriv n xiEulerAudenaertDecreasing X

/-- The normalized derivative coordinate is exactly the corresponding resolvent moment. -/
theorem xiEulerAudenaertDerivativeMoment_eq_resolventMoment_re
    (n : ℕ) {X : ℝ} (hX : 0 < X) :
    xiEulerAudenaertDerivativeMoment n X =
      (xiResolventMoment n X).re := by
  rw [xiEulerAudenaertDerivativeMoment,
    iteratedDeriv_xiEulerAudenaertDecreasing n hX]
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  have hsign : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  field_simp [hfac]
  rw [pow_two, hsign]
  ring

/-- Hankel matrix of normalized collision derivatives of the decreasing Audenaert transform. -/
def xiEulerAudenaertDerivativeHankelMatrix (N : ℕ) (X : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  fun i j => xiEulerAudenaertDerivativeMoment ((i : ℕ) + (j : ℕ)) X

/-- The Audenaert derivative Hankel matrix is literally the Xi resolvent Hankel matrix. -/
theorem xiEulerAudenaertDerivativeHankelMatrix_eq_xiResolventHankelMatrix
    (N : ℕ) {X : ℝ} (hX : 0 < X) :
    xiEulerAudenaertDerivativeHankelMatrix N X =
      xiResolventHankelMatrix N X := by
  ext i j
  exact xiEulerAudenaertDerivativeMoment_eq_resolventMoment_re
    ((i : ℕ) + (j : ℕ)) hX

/-- **Anti-Lowner derivative endpoint.**  At every fixed positive shift, RH is exactly
positive-semidefiniteness in every degree of the normalized derivative Hankel matrix of
Audenaert's decreasing transform. -/
theorem riemannHypothesis_iff_forall_xiEulerAudenaertDerivativeHankelMatrix_posSemidef
    {X : ℝ} (hX : 0 < X) :
    RiemannHypothesis ↔
      ∀ N : ℕ, (xiEulerAudenaertDerivativeHankelMatrix N X).PosSemidef := by
  rw [show (∀ N : ℕ, (xiEulerAudenaertDerivativeHankelMatrix N X).PosSemidef) ↔
      ∀ N : ℕ, (xiResolventHankelMatrix N X).PosSemidef by
        apply forall_congr'
        intro N
        rw [xiEulerAudenaertDerivativeHankelMatrix_eq_xiResolventHankelMatrix N hX]]
  exact riemannHypothesis_iff_forall_xiResolventHankelMatrix_posSemidef hX.le

end

end RHTower
