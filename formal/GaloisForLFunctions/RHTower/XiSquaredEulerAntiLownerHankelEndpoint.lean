import GaloisForLFunctions.HTGeometry.AntiLownerCollisionBridge
import GaloisForLFunctions.HTGeometry.HigherLoewnerCollisionConfluence
import GaloisForLFunctions.HTGeometry.ImaginaryPoleBezoutianGram
import GaloisForLFunctions.HTGeometry.SpectralActionPhaseAnalytic
import GaloisForLFunctions.RHTower.ThetaCuspTiltFluxWeilParityEulerRayWeld
import GaloisForLFunctions.RHTower.SuzukiTorqueContinuationAnalytic
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeMomentDerivatives
import GaloisForLFunctions.RHTower.XiResolventHankelMatrixLadder
import GaloisForLFunctions.RHTower.XiLogDerivSymmetry
import GaloisForLFunctions.RHTower.XiUnitEulerPoleBezoutianSufficiency
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

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

This is not an RH proof.  The imported bridges formalize Audenaert's Schur-complement sign switch,
its finite arbitrary-sign iteration, the doubled-node collision passage to the `K ± L` Loewner
matrices, and the all-order collision-confluence passage from separated matrices to derivative
jets.  Both actual Audenaert transforms are real analytic and their normalized diagonal Loewner
jets are exactly `H₁` and `H₀ - X H₁`.  Reflection-parity recombination
`H₀ = (H₀ - X H₁) + X H₁` turns positivity of both towers into RH.  Conversely, RH gives
the universal finite anti-Lowner producer through the critical-kernel Bezoutian Gram factorization.
Thus this file classifies that producer exactly: it is equivalent to RH, not an independent weaker
positivity target.
-/

open Complex Filter
open scoped ComplexOrder Matrix MatrixOrder Topology

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

theorem xiSquaredEulerFullQ_pos_of_pos {x : ℝ} (hx : 0 < x) :
    0 < xiSquaredEulerFullQ x := by
  unfold xiSquaredEulerFullQ
  exact mul_pos hx (xiSquaredEulerFullResponse_pos (sq_nonneg x))

/-! ## Audenaert's two transforms -/

/-- Decreasing Audenaert transform of the squared-Euler response.  It is the real zeroth Xi
resolvent moment. -/
def xiEulerAudenaertDecreasing (X : ℝ) : ℝ :=
  2 * squaredXiRadialField X

/-- Increasing Audenaert transform of the squared-Euler response. -/
def xiEulerAudenaertIncreasing (X : ℝ) : ℝ :=
  X * xiEulerAudenaertDecreasing X

theorem hasDerivAt_xiEulerAudenaertDecreasing
    {X : ℝ} (hX : 0 < X) :
    HasDerivAt xiEulerAudenaertDecreasing
      (-(xiShiftedReciprocalMoment X 1).re) X := by
  unfold xiEulerAudenaertDecreasing
  have h := (hasDerivAt_squaredXiRadialField hX).const_mul 2
  have hcoef : 2 * (-(xiShiftedReciprocalMoment X 1).re / 2) =
      -(xiShiftedReciprocalMoment X 1).re := by ring
  rw [hcoef] at h
  exact h

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

theorem hasDerivAt_xiSquaredEulerFullQ
    {x : ℝ} (hx : 0 < x) :
    HasDerivAt xiSquaredEulerFullQ
      (xiEulerAudenaertDecreasing (x ^ 2) -
        2 * x ^ 2 * (xiShiftedReciprocalMoment (x ^ 2) 1).re) x := by
  have hX : 0 < x ^ 2 := sq_pos_of_pos hx
  have hsq : HasDerivAt (fun v : ℝ => v ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hR := HasDerivAt.comp (h := fun v : ℝ => v ^ 2) x
    (hasDerivAt_xiEulerAudenaertDecreasing hX) hsq
  have hmul := (hasDerivAt_id x).mul hR
  have hmulCoeff : HasDerivAt
      (id * xiEulerAudenaertDecreasing ∘ fun v : ℝ => v ^ 2)
      (xiEulerAudenaertDecreasing (x ^ 2) +
        x * (-(xiShiftedReciprocalMoment (x ^ 2) 1).re * (2 * x))) x := by
    simpa only [Function.comp_apply, id_eq, one_mul] using hmul
  have hmulNorm : HasDerivAt (fun v : ℝ =>
      v * xiEulerAudenaertDecreasing (v ^ 2))
      (xiEulerAudenaertDecreasing (x ^ 2) +
        x * (-(xiShiftedReciprocalMoment (x ^ 2) 1).re * (2 * x))) x := by
    refine hmulCoeff.congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
    intro v
    rfl
  have hmul' : HasDerivAt (fun v : ℝ =>
      v * xiEulerAudenaertDecreasing (v ^ 2))
      (xiEulerAudenaertDecreasing (x ^ 2) -
        2 * x ^ 2 * (xiShiftedReciprocalMoment (x ^ 2) 1).re) x := by
    convert hmulNorm using 1
    ring
  refine hmul'.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hx] with v hv
  exact xiSquaredEulerFullQ_eq_mul_audenaertDecreasing hv

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

/-- On injective nodes, the derivative-filled Löwner matrix is the removable divided-slope
matrix. -/
theorem loewnerDerivativeMatrixAt_eq_dslope
    {ι : Type*} [DecidableEq ι]
    (f : ℝ → ℝ) (x : ι → ℝ)
    (hinj : Function.Injective x)
    (hderiv : ∀ i, HasDerivAt f (deriv f (x i)) (x i)) :
    loewnerDerivativeMatrixAt f (fun i => deriv f (x i)) x =
      fun i j => dslope f (x i) (x j) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [loewnerDerivativeMatrixAt, dslope_same, (hderiv i).deriv]
  · rw [loewnerDerivativeMatrixAt, if_neg hij]
    rw [dslope_of_ne _ (hinj.ne hij).symm, slope_def_field]
    rw [show x j - x i = -(x i - x j) by ring, div_neg]
    ring

/-- Derivative of the increasing Audenaert reflection-parity transform. -/
theorem hasDerivAt_xiEulerAudenaertIncreasing
    {X : ℝ} (hX : 0 < X) :
    HasDerivAt xiEulerAudenaertIncreasing
      (xiEulerAudenaertDecreasing X -
        X * (xiShiftedReciprocalMoment X 1).re) X := by
  have h := (hasDerivAt_id X).mul
    (hasDerivAt_xiEulerAudenaertDecreasing hX)
  have h' : HasDerivAt (fun Y : ℝ => Y * xiEulerAudenaertDecreasing Y)
      (xiEulerAudenaertDecreasing X +
        X * (-(xiShiftedReciprocalMoment X 1).re)) X := by
    have hs : HasDerivAt (id * xiEulerAudenaertDecreasing)
        (xiEulerAudenaertDecreasing X +
          X * (-(xiShiftedReciprocalMoment X 1).re)) X := by
      simpa only [one_mul, id_eq] using h
    have hfun : (id * xiEulerAudenaertDecreasing) =ᶠ[nhds X]
        (fun Y : ℝ => Y * xiEulerAudenaertDecreasing Y) :=
      Filter.Eventually.of_forall fun Y => by rfl
    exact hfun.hasDerivAt_iff.mp hs
  change HasDerivAt (fun Y : ℝ => Y * xiEulerAudenaertDecreasing Y) _ X
  convert h' using 1
  ring

/-- Derivative of the reversed decreasing Audenaert transform. -/
theorem hasDerivAt_neg_xiEulerAudenaertDecreasing
    {X : ℝ} (hX : 0 < X) :
    HasDerivAt (fun Y => -xiEulerAudenaertDecreasing Y)
      (xiShiftedReciprocalMoment X 1).re X := by
  have h := (hasDerivAt_xiEulerAudenaertDecreasing hX).neg
  have h' : HasDerivAt (fun Y : ℝ => -xiEulerAudenaertDecreasing Y)
      (-(-(xiShiftedReciprocalMoment X 1).re)) X := by
    apply (Filter.EventuallyEq.hasDerivAt_iff
      (Filter.Eventually.of_forall fun Y : ℝ => by rfl)).mp
    exact h
  simpa only [neg_neg] using h'

/-- Exact confluent version of the even reflection-parity splitting, including diagonal nodes. -/
theorem xiSquaredEuler_add_loewner_eq_increasing_dslope
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (hx : ∀ i, 0 < x i) (hinj : Function.Injective x) :
    antiLownerMatrixAt xiSquaredEulerFullQ x +
        loewnerDerivativeMatrixAt xiSquaredEulerFullQ
          (fun i => deriv xiSquaredEulerFullQ (x i)) x =
      (fun i j => 2 * dslope xiEulerAudenaertIncreasing
        ((x i) ^ 2) ((x j) ^ 2) : Matrix ι ι ℝ) := by
  ext i j
  simp only [Matrix.add_apply]
  by_cases hij : i = j
  · subst j
    have hX : 0 < (x i) ^ 2 := sq_pos_of_pos (hx i)
    rw [loewnerDerivativeMatrixAt, if_pos rfl, dslope_same,
      (hasDerivAt_xiSquaredEulerFullQ (hx i)).deriv,
      (hasDerivAt_xiEulerAudenaertIncreasing hX).deriv]
    rw [antiLownerMatrixAt, signedAntiLownerMatrix]
    simp only [Function.comp_apply, one_mul]
    rw [xiSquaredEulerFullQ_eq_mul_audenaertDecreasing (hx i)]
    field_simp [(hx i).ne']
    ring
  · rw [loewnerDerivativeMatrixAt, if_neg hij]
    rw [antiLownerMatrixAt, signedAntiLownerMatrix]
    simp only [Function.comp_apply, one_mul]
    have hxy : x i ≠ x j := hinj.ne hij
    have hsq : (x j) ^ 2 ≠ (x i) ^ 2 := by
      intro h
      have hsqrt := congrArg Real.sqrt h
      rw [Real.sqrt_sq (hx j).le, Real.sqrt_sq (hx i).le] at hsqrt
      exact hxy hsqrt.symm
    have hds : dslope xiEulerAudenaertIncreasing
        ((x i) ^ 2) ((x j) ^ 2) =
        eulerOffDiagonalLoewnerKernel xiEulerAudenaertIncreasing
          ((x i) ^ 2) ((x j) ^ 2) := by
      rw [dslope_of_ne _ hsq, slope_def_field,
        eulerOffDiagonalLoewnerKernel]
      have hne : (x i) ^ 2 - (x j) ^ 2 ≠ 0 := sub_ne_zero.mpr hsq.symm
      field_simp [hne]
      ring
    rw [hds]
    exact xiSquaredEulerFullKernel_add_fullQLoewner_eq_increasingLoewner
      (hx i) (hx j) hxy

/-- Exact confluent version of the odd reflection-parity splitting, including diagonal nodes. -/
theorem xiSquaredEuler_sub_loewner_eq_decreasing_dslope
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ) (hx : ∀ i, 0 < x i) (hinj : Function.Injective x) :
    antiLownerMatrixAt xiSquaredEulerFullQ x -
        loewnerDerivativeMatrixAt xiSquaredEulerFullQ
          (fun i => deriv xiSquaredEulerFullQ (x i)) x =
      (fun i j => 2 * x i * x j *
        dslope (fun X => -xiEulerAudenaertDecreasing X)
          ((x i) ^ 2) ((x j) ^ 2) : Matrix ι ι ℝ) := by
  ext i j
  simp only [Matrix.sub_apply]
  by_cases hij : i = j
  · subst j
    have hX : 0 < (x i) ^ 2 := sq_pos_of_pos (hx i)
    rw [loewnerDerivativeMatrixAt, if_pos rfl, dslope_same,
      (hasDerivAt_xiSquaredEulerFullQ (hx i)).deriv,
      (hasDerivAt_neg_xiEulerAudenaertDecreasing hX).deriv]
    rw [antiLownerMatrixAt, signedAntiLownerMatrix]
    simp only [Function.comp_apply, one_mul]
    rw [xiSquaredEulerFullQ_eq_mul_audenaertDecreasing (hx i)]
    field_simp [(hx i).ne']
    ring
  · rw [loewnerDerivativeMatrixAt, if_neg hij]
    rw [antiLownerMatrixAt, signedAntiLownerMatrix]
    simp only [Function.comp_apply, one_mul]
    have hxy : x i ≠ x j := hinj.ne hij
    have hsq : (x j) ^ 2 ≠ (x i) ^ 2 := by
      intro h
      have hsqrt := congrArg Real.sqrt h
      rw [Real.sqrt_sq (hx j).le, Real.sqrt_sq (hx i).le] at hsqrt
      exact hxy hsqrt.symm
    have hds : dslope (fun X => -xiEulerAudenaertDecreasing X)
        ((x i) ^ 2) ((x j) ^ 2) =
        eulerOffDiagonalLoewnerKernel
          (fun X => -xiEulerAudenaertDecreasing X)
          ((x i) ^ 2) ((x j) ^ 2) := by
      rw [dslope_of_ne _ hsq, slope_def_field,
        eulerOffDiagonalLoewnerKernel]
      have hne : (x i) ^ 2 - (x j) ^ 2 ≠ 0 := sub_ne_zero.mpr hsq.symm
      field_simp [hne]
      ring
    rw [hds]
    exact xiSquaredEulerFullKernel_sub_fullQLoewner_eq_decreasingLoewner
      (hx i) (hx j) hxy

/-- The squared-Euler anti-Löwner producer feeds the complete finite sign-switch/collision bridge.
Thus universal doubled-configuration positivity forces both confluent reflection-parity Löwner
matrices at every positive injective node family. -/
theorem xiSquaredEulerAntiLownerProducer_imp_add_sub_loewnerDerivative
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ)
    (hx : ∀ i, 0 < x i)
    (hinj : Function.Injective x)
    (hanti : ∀ z : ι ⊕ ι → ℝ, (∀ k, 0 < z k) → Function.Injective z →
      (antiLownerMatrixAt xiSquaredEulerFullQ z).PosSemidef) :
    ((antiLownerMatrixAt xiSquaredEulerFullQ x) +
        (loewnerDerivativeMatrixAt xiSquaredEulerFullQ
          (fun i => deriv xiSquaredEulerFullQ (x i)) x)).PosSemidef ∧
      ((antiLownerMatrixAt xiSquaredEulerFullQ x) -
        (loewnerDerivativeMatrixAt xiSquaredEulerFullQ
          (fun i => deriv xiSquaredEulerFullQ (x i)) x)).PosSemidef := by
  apply antiLownerMatrixAt_posSemidef_imp_add_sub_loewnerDerivative
    xiSquaredEulerFullQ (fun i => deriv xiSquaredEulerFullQ (x i)) x hx hinj
    (fun t ht => xiSquaredEulerFullQ_pos_of_pos ht)
  · intro i
    exact (hasDerivAt_xiSquaredEulerFullQ (hx i)).differentiableAt.hasDerivAt
  · exact hanti

/-- Universal doubled anti-Löwner positivity forces finite Löwner positivity for both actual
Audenaert reflection-parity transforms on every positive injective squared-node family. -/
theorem xiSquaredEulerAntiLownerProducer_imp_parityDslope_posSemidef
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℝ)
    (hx : ∀ i, 0 < x i)
    (hinj : Function.Injective x)
    (hanti : ∀ z : ι ⊕ ι → ℝ, (∀ k, 0 < z k) → Function.Injective z →
      (antiLownerMatrixAt xiSquaredEulerFullQ z).PosSemidef) :
    Matrix.PosSemidef (fun i j => dslope xiEulerAudenaertIncreasing
        ((x i) ^ 2) ((x j) ^ 2)) ∧
      Matrix.PosSemidef (fun i j => dslope (fun X => -xiEulerAudenaertDecreasing X)
        ((x i) ^ 2) ((x j) ^ 2)) := by
  obtain ⟨hadd, hsub⟩ :=
    xiSquaredEulerAntiLownerProducer_imp_add_sub_loewnerDerivative x hx hinj hanti
  constructor
  · rw [xiSquaredEuler_add_loewner_eq_increasing_dslope x hx hinj] at hadd
    have hscaled := hadd.smul (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    have heq : (1 / 2 : ℝ) •
        (fun i j => 2 * dslope xiEulerAudenaertIncreasing
          ((x i) ^ 2) ((x j) ^ 2) : Matrix ι ι ℝ) =
        (fun i j => dslope xiEulerAudenaertIncreasing
          ((x i) ^ 2) ((x j) ^ 2) : Matrix ι ι ℝ) := by
      ext i j
      simp
    exact Eq.mp (congrArg Matrix.PosSemidef heq) hscaled
  · let D : Matrix ι ι ℝ := Matrix.diagonal fun i => (x i)⁻¹
    have hcong := hsub.mul_mul_conjTranspose_same D
    have hD : Dᴴ = D := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [D, Matrix.conjTranspose_apply]
      · simp [D, Matrix.conjTranspose_apply, hij, Ne.symm hij]
    have hrecover :
        D * (antiLownerMatrixAt xiSquaredEulerFullQ x -
          loewnerDerivativeMatrixAt xiSquaredEulerFullQ
            (fun i => deriv xiSquaredEulerFullQ (x i)) x) * Dᴴ =
          (fun i j => 2 * dslope (fun X => -xiEulerAudenaertDecreasing X)
            ((x i) ^ 2) ((x j) ^ 2) : Matrix ι ι ℝ) := by
      rw [hD]
      rw [xiSquaredEuler_sub_loewner_eq_decreasing_dslope x hx hinj]
      ext i j
      simp only [D, Matrix.diagonal_mul, Matrix.mul_diagonal]
      field_simp [(hx i).ne', (hx j).ne']
    rw [hrecover] at hcong
    have hscaled := hcong.smul (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    have heq : (1 / 2 : ℝ) •
        (fun i j => 2 * dslope (fun X => -xiEulerAudenaertDecreasing X)
          ((x i) ^ 2) ((x j) ^ 2) : Matrix ι ι ℝ) =
        (fun i j => dslope (fun X => -xiEulerAudenaertDecreasing X)
          ((x i) ^ 2) ((x j) ^ 2) : Matrix ι ι ℝ) := by
      ext i j
      simp
    exact Eq.mp (congrArg Matrix.PosSemidef heq) hscaled

/-- Remaining squared-Euler producer: positive semidefiniteness of every finite anti-Löwner
matrix on positive injective configurations. -/
def XiSquaredEulerAntiLownerProducer : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (z : ι → ℝ),
    (∀ i, 0 < z i) → Function.Injective z →
      (antiLownerMatrixAt xiSquaredEulerFullQ z).PosSemidef

/-- A real matrix is positive semidefinite whenever its entrywise complexification is positive
semidefinite. -/
theorem realMatrix_posSemidef_of_complexification
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ}
    (hA : (A.map Complex.ofReal).PosSemidef) : A.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · rw [Matrix.IsHermitian]
    ext i j
    have hc := congrFun (congrFun hA.isHermitian.eq i) j
    have hre := congrArg Complex.re hc
    simpa [Matrix.conjTranspose_apply] using hre
  · intro v
    have hc := hA.dotProduct_mulVec_nonneg (fun i => (v i : ℂ))
    have hre := (RCLike.nonneg_iff.mp hc).1
    simpa [dotProduct, Matrix.mulVec] using hre

/-- Under RH, the imaginary-zero Bezoutian Gram factorization makes every finite real
squared-Euler anti-Löwner matrix positive semidefinite. -/
theorem xiSquaredEulerAntiLownerMatrix_posSemidef_of_riemannHypothesis
    (hRH : RiemannHypothesis) {N : ℕ}
    (z : Fin N → ℝ) (hz : ∀ i, 0 < z i) :
    (antiLownerMatrixAt xiSquaredEulerFullQ z).PosSemidef := by
  let W : Fin N → ℂ := fun i => (z i : ℂ)
  have hcrit : ∀ s : ℂ, xi s = 0 → s.re = 1 / 2 :=
    riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH
  have hWpos : ∀ i, 0 < (W i).re := by
    intro i
    simpa [W] using hz i
  have hne : ∀ i, xiCent (W i) ≠ 0 := by
    intro i hzero
    have hre := hcrit (1 / 2 + W i) hzero
    simp only [Complex.add_re, Complex.div_re, Complex.one_re, Complex.one_im,
      W, Complex.ofReal_re] at hre
    norm_num at hre
    linarith [hz i]
  have hbez := posSemidef_xiTranslatedBezoutian_of_critical hcrit W hWpos
  have hcongr := GaloisForLFunctions.HTGeometry.posSemidef_congr_diagonal
    hbez (fun i => (xiCent (W i))⁻¹)
  have hEq :
      (Matrix.of fun i j : Fin N => criticalLogDerivKernel (W i) (W j)) =
      Matrix.of fun i j : Fin N =>
        (xiCent (W i))⁻¹ * xiTranslatedBezoutian 0 (W i) (W j) *
          (starRingEnd ℂ) ((xiCent (W j))⁻¹) := by
    ext i j
    rw [Matrix.of_apply, Matrix.of_apply, criticalLogDerivKernel,
      xiTranslatedBezoutian]
    have h1 : xiTranslatedCentered 0 (W i) = xiCent (W i) := (xiCent_eq _).symm
    have h2 : xiTranslatedCentered 0 (W j) = xiCent (W j) := (xiCent_eq _).symm
    have h3 : deriv (xiTranslatedCentered 0) = deriv xiCent := by
      congr 1
      funext u
      exact (xiCent_eq u).symm
    rw [h1, h2, h3, logDeriv_apply, logDeriv_apply, map_div₀, map_inv₀]
    have hjc : (starRingEnd ℂ) (xiCent (W j)) ≠ 0 := by
      simpa using (map_ne_zero (starRingEnd ℂ)).mpr (hne j)
    field_simp [hne i, hne j, hjc]
  have hcritical :
      (Matrix.of fun i j : Fin N =>
        criticalLogDerivKernel (W i) (W j)).PosSemidef := by
    rw [hEq]
    exact hcongr
  apply realMatrix_posSemidef_of_complexification
  have hmap :
      (antiLownerMatrixAt xiSquaredEulerFullQ z).map Complex.ofReal =
        Matrix.of fun i j : Fin N => criticalLogDerivKernel (W i) (W j) := by
    ext i j
    rw [Matrix.map_apply, Matrix.of_apply]
    rw [criticalLogDerivKernel_ofReal_eq_fullKernel_pos (hz i) (hz j)]
    simp [antiLownerMatrixAt, signedAntiLownerMatrix,
      xiSquaredEulerFullKernel, eulerRayResponseKernel]
  rw [hmap]
  exact hcritical

/-- RH supplies the universal squared-Euler anti-Löwner producer.  Reindexing reduces an arbitrary
finite type to the canonical `Fin` Gram matrix. -/
theorem xiSquaredEulerAntiLownerProducer_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    XiSquaredEulerAntiLownerProducer := by
  intro ι _ _ z hz hinj
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hfin := xiSquaredEulerAntiLownerMatrix_posSemidef_of_riemannHypothesis
    hRH (fun j => z (e.symm j)) (fun j => hz (e.symm j))
  have hsub := hfin.submatrix e
  have heq :
      (antiLownerMatrixAt xiSquaredEulerFullQ
        (fun j => z (e.symm j))).submatrix e e =
          antiLownerMatrixAt xiSquaredEulerFullQ z := by
    ext i j
    simp [antiLownerMatrixAt, signedAntiLownerMatrix, e]
  rw [heq] at hsub
  exact hsub

/-- A universal squared-Euler producer supplies, near every positive collision center, both
punctured uniform Löwner PSD families required by higher confluence. -/
theorem xiSquaredEulerAntiLownerProducer_imp_eventually_uniform_parity
    (hproducer : XiSquaredEulerAntiLownerProducer)
    {X : ℝ} (hX : 0 < X) (N : ℕ) :
    (∀ᶠ h in 𝓝[≠] (0 : ℝ),
      (GaloisForLFunctions.HTGeometry.uniformMovingDslopeMatrix
        xiEulerAudenaertIncreasing X N h).PosSemidef) ∧
    (∀ᶠ h in 𝓝[≠] (0 : ℝ),
      (GaloisForLFunctions.HTGeometry.uniformMovingDslopeMatrix
        (fun Y => -xiEulerAudenaertDecreasing Y) X N h).PosSemidef) := by
  have hnodes : ∀ᶠ h in 𝓝[≠] (0 : ℝ),
      ∀ i : Fin N, 0 < X + (i : ℝ) * h := by
    rw [Filter.eventually_all]
    intro i
    have hid : Tendsto (fun h : ℝ => h) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
      (tendsto_id : Tendsto (fun h : ℝ => h) (𝓝 0) (𝓝 0)).mono_left
        nhdsWithin_le_nhds
    have ht : Tendsto (fun h : ℝ => X + (i : ℝ) * h)
        (𝓝[≠] (0 : ℝ)) (𝓝 X) := by
      simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hid)
    exact ht.eventually (Ioi_mem_nhds hX)
  have hpair : ∀ᶠ h in 𝓝[≠] (0 : ℝ),
      (GaloisForLFunctions.HTGeometry.uniformMovingDslopeMatrix
        xiEulerAudenaertIncreasing X N h).PosSemidef ∧
      (GaloisForLFunctions.HTGeometry.uniformMovingDslopeMatrix
        (fun Y => -xiEulerAudenaertDecreasing Y) X N h).PosSemidef := by
    filter_upwards [hnodes, self_mem_nhdsWithin] with h hY hhmem
    have hh : h ≠ 0 := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hhmem
    let Y : Fin N → ℝ := fun i => X + (i : ℝ) * h
    let x : Fin N → ℝ := fun i => Real.sqrt (Y i)
    have hYpos : ∀ i, 0 < Y i := by
      intro i
      exact hY i
    have hYinj : Function.Injective Y := by
      intro i j hij
      have hm : ((i : ℝ) - (j : ℝ)) * h = 0 := by
        dsimp only [Y] at hij
        linarith
      have hc : (i : ℝ) = (j : ℝ) :=
        sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hh)
      exact Fin.ext (by exact_mod_cast hc)
    have hxpos : ∀ i, 0 < x i := fun i => Real.sqrt_pos.mpr (hYpos i)
    have hxinj : Function.Injective x := by
      intro i j hij
      apply hYinj
      have hsquare := congrArg (fun t : ℝ => t ^ 2) hij
      simpa only [x, Real.sq_sqrt (hYpos i).le,
        Real.sq_sqrt (hYpos j).le] using hsquare
    have hp := xiSquaredEulerAntiLownerProducer_imp_parityDslope_posSemidef
      x hxpos hxinj
      (fun z hz hzinj => hproducer (Fin N ⊕ Fin N) z hz hzinj)
    have hsquare : ∀ i, (x i) ^ 2 = Y i :=
      fun i => Real.sq_sqrt (hYpos i).le
    constructor
    · have heq :
          (fun i j => dslope xiEulerAudenaertIncreasing
            ((x i) ^ 2) ((x j) ^ 2) : Matrix (Fin N) (Fin N) ℝ) =
          GaloisForLFunctions.HTGeometry.uniformMovingDslopeMatrix
            xiEulerAudenaertIncreasing X N h := by
          ext i j
          simp only [GaloisForLFunctions.HTGeometry.uniformMovingDslopeMatrix,
            GaloisForLFunctions.HTGeometry.movingDslope, hsquare, Y]
      rw [← heq]
      exact hp.1
    · have heq :
          (fun i j => dslope (fun T => -xiEulerAudenaertDecreasing T)
            ((x i) ^ 2) ((x j) ^ 2) : Matrix (Fin N) (Fin N) ℝ) =
          GaloisForLFunctions.HTGeometry.uniformMovingDslopeMatrix
            (fun T => -xiEulerAudenaertDecreasing T) X N h := by
          ext i j
          simp only [GaloisForLFunctions.HTGeometry.uniformMovingDslopeMatrix,
            GaloisForLFunctions.HTGeometry.movingDslope, hsquare, Y]
      rw [← heq]
      exact hp.2
  exact ⟨hpair.mono (fun _ hp => hp.1), hpair.mono (fun _ hp => hp.2)⟩

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

/-! ## All-order reflection-parity jet reconstruction -/

/-- The decreasing Audenaert transform is real analytic at every positive shift.  The proof
complexifies through the zero-free real Xi logarithmic derivative and composes with the
real-analytic positive square-root chart. -/
theorem analyticAt_xiEulerAudenaertDecreasing
    {X : ℝ} (hX : 0 < X) :
    AnalyticAt ℝ xiEulerAudenaertDecreasing X := by
  have hsqrt : AnalyticAt ℝ Real.sqrt X :=
    GaloisForLFunctions.HTGeometry.analyticAt_rsqrt hX
  let g : ℂ → ℂ := fun z => logDeriv xi (1 / 2 + z)
  have hg : AnalyticAt ℂ g (Real.sqrt X : ℂ) := by
    apply AnalyticAt.comp (x := (Real.sqrt X : ℂ))
      (g := logDeriv xi) (f := fun z : ℂ => 1 / 2 + z)
    · exact analyticAt_logDeriv_xi (xi_ofReal_shift_ne_zero (Real.sqrt X))
    · exact analyticAt_const.add analyticAt_id
  have hreal : AnalyticAt ℝ (fun w : ℝ => (g w).re) (Real.sqrt X) :=
    hg.re_ofReal
  have hquot : AnalyticAt ℝ
      (fun Y : ℝ => (g (Real.sqrt Y)).re / Real.sqrt Y) X :=
    (hreal.comp hsqrt).div hsqrt (Real.sqrt_pos.mpr hX).ne'
  apply hquot.congr
  filter_upwards [Ioi_mem_nhds hX] with Y hY
  rw [xiEulerAudenaertDecreasing_eq_fullQ_div_sqrt hY]
  have hQ := xiSquaredEulerFullQ_eq_logDeriv_re (Real.sqrt_pos.mpr hY)
  change xiSquaredEulerFullQ (Real.sqrt Y) = (g (Real.sqrt Y)).re at hQ
  rw [hQ]

/-- The increasing Audenaert transform is real analytic at every positive shift. -/
theorem analyticAt_xiEulerAudenaertIncreasing
    {X : ℝ} (hX : 0 < X) :
    AnalyticAt ℝ xiEulerAudenaertIncreasing X := by
  change AnalyticAt ℝ (fun Y => Y * xiEulerAudenaertDecreasing Y) X
  exact analyticAt_id.mul (analyticAt_xiEulerAudenaertDecreasing hX)

/-- Leibniz collapse for multiplication by the coordinate: only derivative orders zero and one
of the coordinate survive. -/
theorem iteratedDeriv_id_mul_succ (f : ℝ → ℝ) {X : ℝ} (n : ℕ)
    (hf : ContDiffAt ℝ (n + 1) f X) :
    iteratedDeriv (n + 1) (fun Y => Y * f Y) X =
      X * iteratedDeriv (n + 1) f X +
        (n + 1 : ℝ) * iteratedDeriv n f X := by
  change iteratedDeriv (n + 1) (id * f) X = _
  rw [iteratedDeriv_mul
    (contDiffAt_id : ContDiffAt ℝ (n + 1) (fun Y : ℝ => Y) X) hf]
  let term : ℕ → ℝ := fun i =>
    (n + 1).choose i * iteratedDeriv i id X * iteratedDeriv (n + 1 - i) f X
  have h0 : 0 ∈ Finset.range (n + 1 + 1) := by simp
  have h1 : 1 ∈ (Finset.range (n + 1 + 1)).erase 0 := by simp
  have hsum : (∑ i ∈ Finset.range (n + 1 + 1), term i) = term 0 + term 1 := by
    rw [← Finset.sum_erase_add _ _ h0, ← Finset.sum_erase_add _ _ h1]
    have hz : ∑ i ∈ ((Finset.range (n + 1 + 1)).erase 0).erase 1, term i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi1 : i ≠ 1 := (Finset.mem_erase.mp hi).1
      have hi0 : i ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
      simp [term, iteratedDeriv_id, hi0, hi1]
    rw [hz]
    ring
  change (∑ i ∈ Finset.range (n + 1 + 1), term i) = _
  rw [hsum]
  simp [term, iteratedDeriv_id]

/-- Alternating factorial normalization of the diagonal jets of a removable Loewner kernel. -/
def alternatingNormalizedLoewnerJet
    (f : ℝ → ℝ) (n : ℕ) (X : ℝ) : ℝ :=
  (-1 : ℝ) ^ n / (n.factorial : ℝ) *
    iteratedDeriv n (dslope f X) X

/-- Analytic divided-slope jets shift the source derivative order by one, with the exact
factorial normalization. -/
theorem alternatingNormalizedLoewnerJet_eq_succ
    {f : ℝ → ℝ} {X : ℝ} (hf : AnalyticAt ℝ f X) (n : ℕ) :
    alternatingNormalizedLoewnerJet f n X =
      (-1 : ℝ) ^ n / ((n + 1).factorial : ℝ) *
        iteratedDeriv (n + 1) f X := by
  rw [alternatingNormalizedLoewnerJet,
    HTGeometry.iteratedDeriv_dslope_self_eq_iteratedDeriv_succ_div hf]
  push_cast [Nat.factorial_succ]
  have hn : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp

/-- Normalized diagonal Loewner jet of the decreasing reflection-parity transform `-R`. -/
def xiEulerAudenaertDecreasingLoewnerJetMoment
    (n : ℕ) (X : ℝ) : ℝ :=
  alternatingNormalizedLoewnerJet
    (fun Y => -xiEulerAudenaertDecreasing Y) n X

/-- Normalized diagonal Loewner jet of the increasing reflection-parity transform `X R(X)`. -/
def xiEulerAudenaertIncreasingLoewnerJetMoment
    (n : ℕ) (X : ℝ) : ℝ :=
  alternatingNormalizedLoewnerJet xiEulerAudenaertIncreasing n X

/-- The decreasing parity jet is exactly the one-step shifted Xi resolvent moment. -/
theorem xiEulerAudenaertDecreasingLoewnerJetMoment_eq
    (n : ℕ) {X : ℝ} (hX : 0 < X) :
    xiEulerAudenaertDecreasingLoewnerJetMoment n X =
      (xiResolventMoment (n + 1) X).re := by
  rw [xiEulerAudenaertDecreasingLoewnerJetMoment]
  change alternatingNormalizedLoewnerJet (-xiEulerAudenaertDecreasing) n X = _
  rw [alternatingNormalizedLoewnerJet_eq_succ
      (analyticAt_xiEulerAudenaertDecreasing hX).neg,
    iteratedDeriv_neg,
    iteratedDeriv_xiEulerAudenaertDecreasing (n + 1) hX]
  rw [pow_succ]
  have hfac : ((n + 1).factorial : ℝ) ≠ 0 := by positivity
  have hsign : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  field_simp [hfac]
  rw [pow_two, hsign]
  ring

/-- The increasing parity jet is exactly `mₙ - X mₙ₊₁`. -/
theorem xiEulerAudenaertIncreasingLoewnerJetMoment_eq
    (n : ℕ) {X : ℝ} (hX : 0 < X) :
    xiEulerAudenaertIncreasingLoewnerJetMoment n X =
      (xiResolventMoment n X).re -
        X * (xiResolventMoment (n + 1) X).re := by
  rw [xiEulerAudenaertIncreasingLoewnerJetMoment,
    alternatingNormalizedLoewnerJet_eq_succ
      (analyticAt_xiEulerAudenaertIncreasing hX)]
  have hprod := iteratedDeriv_id_mul_succ xiEulerAudenaertDecreasing n
    (analyticAt_xiEulerAudenaertDecreasing hX).contDiffAt
  change iteratedDeriv (n + 1) xiEulerAudenaertIncreasing X = _ at hprod
  rw [hprod, iteratedDeriv_xiEulerAudenaertDecreasing (n + 1) hX,
    iteratedDeriv_xiEulerAudenaertDecreasing n hX]
  rw [pow_succ]
  push_cast [Nat.factorial_succ]
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
  have hsign : (-1 : ℝ) ^ n * (-1 : ℝ) ^ n = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  field_simp [hfac, hn1]
  rw [pow_two, hsign]
  ring

/-- Hankel matrix of normalized decreasing-parity Loewner jets. -/
def xiEulerAudenaertDecreasingLoewnerJetMatrix
    (N : ℕ) (X : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => xiEulerAudenaertDecreasingLoewnerJetMoment
    ((i : ℕ) + (j : ℕ)) X

/-- Hankel matrix of normalized increasing-parity Loewner jets. -/
def xiEulerAudenaertIncreasingLoewnerJetMatrix
    (N : ℕ) (X : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => xiEulerAudenaertIncreasingLoewnerJetMoment
    ((i : ℕ) + (j : ℕ)) X

/-- The Xi decreasing-parity jet matrix is the generic alternating higher-confluence limit. -/
theorem xiEulerAudenaertDecreasingLoewnerJetMatrix_eq_alternating
    (N : ℕ) {X : ℝ} (hX : 0 < X) :
    xiEulerAudenaertDecreasingLoewnerJetMatrix N X =
      GaloisForLFunctions.HTGeometry.alternatingNormalizedLoewnerJetMatrix
        (fun Y => -xiEulerAudenaertDecreasing Y) X N := by
  ext i j
  change alternatingNormalizedLoewnerJet
      (-xiEulerAudenaertDecreasing) ((i : ℕ) + (j : ℕ)) X =
    (-1 : ℝ) ^ ((i : ℕ) + (j : ℕ)) *
      (iteratedDeriv ((i : ℕ) + (j : ℕ) + 1)
        (-xiEulerAudenaertDecreasing) X /
          (((i : ℕ) + (j : ℕ) + 1).factorial : ℝ))
  rw [alternatingNormalizedLoewnerJet_eq_succ
    (analyticAt_xiEulerAudenaertDecreasing hX).neg]
  ring

/-- The Xi increasing-parity jet matrix is the generic alternating higher-confluence limit. -/
theorem xiEulerAudenaertIncreasingLoewnerJetMatrix_eq_alternating
    (N : ℕ) {X : ℝ} (hX : 0 < X) :
    xiEulerAudenaertIncreasingLoewnerJetMatrix N X =
      GaloisForLFunctions.HTGeometry.alternatingNormalizedLoewnerJetMatrix
        xiEulerAudenaertIncreasing X N := by
  ext i j
  change alternatingNormalizedLoewnerJet
      xiEulerAudenaertIncreasing ((i : ℕ) + (j : ℕ)) X =
    (-1 : ℝ) ^ ((i : ℕ) + (j : ℕ)) *
      (iteratedDeriv ((i : ℕ) + (j : ℕ) + 1)
        xiEulerAudenaertIncreasing X /
          (((i : ℕ) + (j : ℕ) + 1).factorial : ℝ))
  rw [alternatingNormalizedLoewnerJet_eq_succ
    (analyticAt_xiEulerAudenaertIncreasing hX)]
  ring

/-- The universal finite anti-Löwner producer supplies both all-order Xi reflection-parity jet
towers at every positive collision center. -/
theorem xiSquaredEulerAntiLownerProducer_imp_audenaertLoewnerJetMatrix_posSemidef
    (hproducer : XiSquaredEulerAntiLownerProducer)
    {X : ℝ} (hX : 0 < X) :
    (∀ N : ℕ,
      (xiEulerAudenaertDecreasingLoewnerJetMatrix N X).PosSemidef) ∧
    (∀ N : ℕ,
      (xiEulerAudenaertIncreasingLoewnerJetMatrix N X).PosSemidef) := by
  constructor
  · intro N
    obtain ⟨_, hdec⟩ :=
      xiSquaredEulerAntiLownerProducer_imp_eventually_uniform_parity
        hproducer hX N
    have hjet := GaloisForLFunctions.HTGeometry.normalizedLoewnerJetMatrix_posSemidef_of_eventually_uniform
      (analyticAt_xiEulerAudenaertDecreasing hX).neg N hdec
    have halt := GaloisForLFunctions.HTGeometry.alternatingNormalizedLoewnerJetMatrix_posSemidef
      (fun Y => -xiEulerAudenaertDecreasing Y) X N hjet
    rw [xiEulerAudenaertDecreasingLoewnerJetMatrix_eq_alternating N hX]
    exact halt
  · intro N
    obtain ⟨hinc, _⟩ :=
      xiSquaredEulerAntiLownerProducer_imp_eventually_uniform_parity
        hproducer hX N
    have hjet := GaloisForLFunctions.HTGeometry.normalizedLoewnerJetMatrix_posSemidef_of_eventually_uniform
      (analyticAt_xiEulerAudenaertIncreasing hX) N hinc
    have halt := GaloisForLFunctions.HTGeometry.alternatingNormalizedLoewnerJetMatrix_posSemidef
      xiEulerAudenaertIncreasing X N hjet
    rw [xiEulerAudenaertIncreasingLoewnerJetMatrix_eq_alternating N hX]
    exact halt

/-- **Reflection-parity jet conservation law.**  The increasing block `H₀ - X H₁` plus `X` times
the decreasing block `H₁` is exactly the full RH-deciding resolvent Hankel matrix `H₀`. -/
theorem xiEulerAudenaertLoewnerJetMatrix_reconstruction
    (N : ℕ) {X : ℝ} (hX : 0 < X) :
    xiEulerAudenaertIncreasingLoewnerJetMatrix N X +
        X • xiEulerAudenaertDecreasingLoewnerJetMatrix N X =
      xiResolventHankelMatrix N X := by
  ext i j
  rw [Matrix.add_apply, Matrix.smul_apply]
  simp only [smul_eq_mul, xiEulerAudenaertIncreasingLoewnerJetMatrix,
    xiEulerAudenaertDecreasingLoewnerJetMatrix,
    xiResolventHankelMatrix,
    xiEulerAudenaertIncreasingLoewnerJetMoment_eq
      ((i : ℕ) + (j : ℕ)) hX,
    xiEulerAudenaertDecreasingLoewnerJetMoment_eq
      ((i : ℕ) + (j : ℕ)) hX]
  ring

/-- **All-order Audenaert parity-jet RH bridge.**  Positive semidefiniteness of both normalized
Loewner jet towers at one positive shift reconstructs the entire Xi resolvent Hankel cone and
therefore forces RH. -/
theorem riemannHypothesis_of_audenaertLoewnerJetMatrix_posSemidef
    {X : ℝ} (hX : 0 < X)
    (hdec : ∀ N : ℕ,
      (xiEulerAudenaertDecreasingLoewnerJetMatrix N X).PosSemidef)
    (hinc : ∀ N : ℕ,
      (xiEulerAudenaertIncreasingLoewnerJetMatrix N X).PosSemidef) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_forall_xiResolventHankelMatrix_posSemidef hX.le]
  intro N
  rw [← xiEulerAudenaertLoewnerJetMatrix_reconstruction N hX]
  exact (hinc N).add ((hdec N).smul hX.le)

/-- **Closed squared-Euler anti-Löwner endpoint.**  Universal finite positive-ray anti-Löwner
positivity for the actual squared-Euler Xi response implies RH, with all collision, confluence,
normalization, and reflection-parity steps discharged in Lean. -/
theorem riemannHypothesis_of_xiSquaredEulerAntiLownerProducer
    (hproducer : XiSquaredEulerAntiLownerProducer) :
    RiemannHypothesis := by
  obtain ⟨hdec, hinc⟩ :=
    xiSquaredEulerAntiLownerProducer_imp_audenaertLoewnerJetMatrix_posSemidef
      hproducer (X := 1) zero_lt_one
  exact riemannHypothesis_of_audenaertLoewnerJetMatrix_posSemidef
    zero_lt_one hdec hinc

/-- **Exact classification.**  Universal positive-ray anti-Löwner positivity of the actual
squared-Euler Xi response is equivalent to RH. -/
theorem xiSquaredEulerAntiLownerProducer_iff_riemannHypothesis :
    XiSquaredEulerAntiLownerProducer ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_xiSquaredEulerAntiLownerProducer,
    xiSquaredEulerAntiLownerProducer_of_riemannHypothesis⟩

end

end RHTower
