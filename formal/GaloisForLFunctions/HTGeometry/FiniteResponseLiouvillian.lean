import GaloisForLFunctions.HTGeometry.ReflectionPositiveHankel
import GaloisForLFunctions.HTGeometry.ThermalKrylovDeterminant

/-!
# Finite response-theory Liouvillian sum rules

In an energy eigenbasis the commutator Liouvillian acts diagonally on transition entries by the
real energy gap `E_a - E_b`.  This file realizes that diagonal action as a bounded self-adjoint
operator on the finite transition Hilbert space and proves the exact response-moment identity

`inner omega (L^k omega) = sum_(a,b) intensity a b * (E_a-E_b)^k`.

The squared Liouvillian therefore has the even thermal moments as its ordinary vacuum moments.
This is the finite spectral algebra behind response-theory sum rules that identify spectral
frequency moments with equal-time nested commutator values.
-/

open scoped BigOperators InnerProductSpace

namespace HTGeometry

noncomputable section

/-- The finite spectral Liouvillian as a linear map on transition entries. -/
def transitionGapLiouvillianLinear {α : Type*} [Fintype α] (energy : α → ℝ) :
    EuclideanSpace ℂ (α × α) →ₗ[ℂ] EuclideanSpace ℂ (α × α) where
  toFun x := WithLp.toLp 2 fun ab =>
    ((energy ab.1 - energy ab.2 : ℝ) : ℂ) * x ab
  map_add' x y := by
    ext ab
    simp
    ring
  map_smul' c x := by
    ext ab
    simp
    ring

/-- The bounded finite spectral Liouvillian. -/
def transitionGapLiouvillian {α : Type*} [Fintype α] (energy : α → ℝ) :
    EuclideanSpace ℂ (α × α) →L[ℂ] EuclideanSpace ℂ (α × α) :=
  LinearMap.toContinuousLinearMap (transitionGapLiouvillianLinear energy)

@[simp] theorem transitionGapLiouvillian_apply {α : Type*} [Fintype α]
    (energy : α → ℝ) (x : EuclideanSpace ℂ (α × α)) (ab : α × α) :
    transitionGapLiouvillian energy x ab =
      ((energy ab.1 - energy ab.2 : ℝ) : ℂ) * x ab := rfl

/-- Real energy gaps make the finite spectral Liouvillian self-adjoint. -/
theorem transitionGapLiouvillian_isSelfAdjoint {α : Type*} [Fintype α]
    (energy : α → ℝ) :
    IsSelfAdjoint (transitionGapLiouvillian energy) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro ab _
  change y ab * (starRingEnd ℂ)
      (((energy ab.1 - energy ab.2 : ℝ) : ℂ) * x ab) =
    (((energy ab.1 - energy ab.2 : ℝ) : ℂ) * y ab) *
      (starRingEnd ℂ) (x ab)
  rw [map_mul, Complex.conj_ofReal]
  ring

/-- Transition vector with amplitudes equal to the square roots of the nonnegative intensities. -/
def thermalTransitionVector {α : Type*}
    (intensity : α → α → ℝ) : EuclideanSpace ℂ (α × α) :=
  WithLp.toLp 2 fun ab => (Real.sqrt (intensity ab.1 ab.2) : ℂ)

/-- The explicit `n`-th Liouvillian orbit vector in the energy basis. -/
def thermalLiouvillianVector {α : Type*}
    (intensity : α → α → ℝ) (energy : α → ℝ) (n : ℕ) :
    EuclideanSpace ℂ (α × α) :=
  WithLp.toLp 2 fun ab => (Real.sqrt (intensity ab.1 ab.2) : ℂ) *
    (((energy ab.1 - energy ab.2 : ℝ) : ℂ) ^ n)

@[simp] theorem thermalLiouvillianVector_zero {α : Type*}
    (intensity : α → α → ℝ) (energy : α → ℝ) :
    thermalLiouvillianVector intensity energy 0 = thermalTransitionVector intensity := by
  ext ab
  simp [thermalLiouvillianVector, thermalTransitionVector]

/-- One Liouvillian application raises the explicit response-moment order by one. -/
theorem transitionGapLiouvillian_thermalLiouvillianVector
    {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ) (n : ℕ) :
    transitionGapLiouvillian energy (thermalLiouvillianVector intensity energy n) =
      thermalLiouvillianVector intensity energy (n + 1) := by
  ext ab
  simp only [transitionGapLiouvillian_apply, thermalLiouvillianVector,
    WithLp.ofLp_toLp, pow_succ']
  ring

/-- The operator power orbit is the explicit energy-gap orbit. -/
theorem pow_transitionGapLiouvillian_thermalTransitionVector
    {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ) (n : ℕ) :
    ((transitionGapLiouvillian energy) ^ n) (thermalTransitionVector intensity) =
      thermalLiouvillianVector intensity energy n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply, ih,
        transitionGapLiouvillian_thermalLiouvillianVector]

/-- Exact inner-product value between two finite Liouvillian orbit vectors. -/
theorem inner_thermalLiouvillianVector {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ)
    (hintensity : ∀ a b, 0 ≤ intensity a b) (i j : ℕ) :
    inner ℂ (thermalLiouvillianVector intensity energy i)
      (thermalLiouvillianVector intensity energy j) =
      (thermalGapMoment intensity energy (i + j) : ℂ) := by
  rw [PiLp.inner_apply, Fintype.sum_prod_type, thermalGapMoment, Complex.ofReal_sum]
  simp_rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [thermalLiouvillianVector, WithLp.ofLp_toLp, RCLike.inner_apply,
    map_mul, Complex.conj_ofReal, map_pow]
  push_cast
  have hsqrt : (Real.sqrt (intensity a b) : ℂ) ^ 2 = (intensity a b : ℂ) := by
    norm_cast
    exact Real.sq_sqrt (hintensity a b)
  rw [← hsqrt, pow_add]
  ring

/-- **Finite response spectral-moment sum rule.** -/
theorem inner_transitionVector_pow_gapLiouvillian {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ)
    (hintensity : ∀ a b, 0 ≤ intensity a b) (n : ℕ) :
    inner ℂ (thermalTransitionVector intensity)
      (((transitionGapLiouvillian energy) ^ n) (thermalTransitionVector intensity)) =
      (thermalGapMoment intensity energy n : ℂ) := by
  rw [pow_transitionGapLiouvillian_thermalTransitionVector,
    ← thermalLiouvillianVector_zero intensity energy]
  simpa using inner_thermalLiouvillianVector intensity energy hintensity 0 n

/-- Symmetric transition intensities impose the odd-response-moment selection rule on the
self-adjoint Liouvillian orbit. -/
theorem inner_transitionVector_pow_gapLiouvillian_eq_zero_of_odd
    {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ)
    (hintensity : ∀ a b, 0 ≤ intensity a b)
    (hsymm : ∀ a b, intensity a b = intensity b a)
    {n : ℕ} (hn : Odd n) :
    inner ℂ (thermalTransitionVector intensity)
      (((transitionGapLiouvillian energy) ^ n) (thermalTransitionVector intensity)) = 0 := by
  rw [inner_transitionVector_pow_gapLiouvillian intensity energy hintensity,
    thermalGapMoment_odd_eq_zero intensity energy hsymm hn]
  norm_num

/-- The squared self-adjoint Liouvillian has the even thermal moments as its vacuum moments. -/
theorem inner_transitionVector_pow_squaredGapLiouvillian
    {α : Type*} [Fintype α]
    (intensity : α → α → ℝ) (energy : α → ℝ)
    (hintensity : ∀ a b, 0 ≤ intensity a b) (n : ℕ) :
    inner ℂ (thermalTransitionVector intensity)
      ((((transitionGapLiouvillian energy) ^ 2) ^ n) (thermalTransitionVector intensity)) =
      (thermalEvenGapMoment intensity energy n : ℂ) := by
  rw [← pow_mul, inner_transitionVector_pow_gapLiouvillian intensity energy hintensity,
    thermalEvenGapMoment]

end

end HTGeometry
