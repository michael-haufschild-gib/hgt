import GaloisForLFunctions.RHTower.ProlateIndexedJointSpectrum
import GaloisForLFunctions.RHTower.ConstrainedProlateConstrainedSpectrum

/-!
# The concentration operator is injective on the constrained subspace

`evenProlateConcentration a = (evenTimeBandFourier a)† ∘ evenTimeBandFourier a`, so its quadratic
form is `‖evenTimeBandFourier a f‖²`.  On the time-limited carrier the compressed Fourier transform
is injective, so the concentration operator is injective there; compressing further to the
zero-integral hyperplane preserves injectivity, because for a vector of the subspace the compressed
quadratic form is the ambient one.

This is what makes the greedy singular family of the compressed operator complete on the constrained
subspace, and hence what lets the operator phrasing of the constrained-prolate cards be matched with
the secular phrasing in which the transfer theorems are proved.
-/

noncomputable section

open ContinuousLinearMap

open scoped InnerProduct InnerProductSpace

namespace RHTower

/-- **The concentration operator is injective on the time-limited carrier.**  Its quadratic form is
`‖evenTimeBandFourier a f‖²`, and the compressed Fourier transform is injective there. -/
theorem evenProlateConcentration_injective_on_timeLimited
    {a : ℝ} (ha : 0 < a) {f : evenSubspace} (hf : f ∈ evenTimeLimitedSubspace a)
    (hCf : evenProlateConcentration a f = 0) : f = 0 := by
  have hCeq : evenProlateConcentration a f
      = ContinuousLinearMap.adjoint (evenTimeBandFourier a) (evenTimeBandFourier a f) := rfl
  have hzero : (inner ℂ (ContinuousLinearMap.adjoint (evenTimeBandFourier a)
      (evenTimeBandFourier a f)) f : ℂ) = 0 := by
    rw [← hCeq, hCf]
    simp
  have hadj : (inner ℂ (ContinuousLinearMap.adjoint (evenTimeBandFourier a)
      (evenTimeBandFourier a f)) f : ℂ)
      = inner ℂ (evenTimeBandFourier a f) (evenTimeBandFourier a f) :=
    ContinuousLinearMap.adjoint_inner_left _ _ _
  have hT : evenTimeBandFourier a f = 0 := by
    have hself : (inner ℂ (evenTimeBandFourier a f) (evenTimeBandFourier a f) : ℂ) = 0 := by
      rw [← hadj]
      exact hzero
    exact inner_self_eq_zero.1 hself
  exact evenTimeBandFourier_injective_on_timeLimited ha hf hT


/-- **The compressed concentration operator is injective on the constrained subspace.**  For a
vector of the subspace the compressed quadratic form is the ambient one, so injectivity descends. -/
theorem constrainedProlateConcentration_injective {a : ℝ} (ha : 0 < a)
    {x : constrainedProlateSubspace a}
    (hx : constrainedProlateConcentration a x = 0) : x = 0 := by
  have hmem : (x : evenSubspace) ∈ evenTimeLimitedSubspace a := (Submodule.mem_inf.1 x.2).1
  have hproj := (constrainedProlateSubspace a).inner_orthogonalProjectionOnto_eq_of_mem_right x
    (evenProlateConcentration a (x : evenSubspace))
  have hval : (constrainedProlateSubspace a).orthogonalProjectionOnto
      (evenProlateConcentration a (x : evenSubspace)) = constrainedProlateConcentration a x := rfl
  have hzero : (inner ℂ (evenProlateConcentration a (x : evenSubspace))
      (x : evenSubspace) : ℂ) = 0 := by
    rw [← hproj, hval, hx]
    simp
  have hCeq : evenProlateConcentration a (x : evenSubspace)
      = ContinuousLinearMap.adjoint (evenTimeBandFourier a)
          (evenTimeBandFourier a (x : evenSubspace)) := rfl
  have hadj : (inner ℂ (ContinuousLinearMap.adjoint (evenTimeBandFourier a)
      (evenTimeBandFourier a (x : evenSubspace))) (x : evenSubspace) : ℂ)
      = inner ℂ (evenTimeBandFourier a (x : evenSubspace))
          (evenTimeBandFourier a (x : evenSubspace)) :=
    ContinuousLinearMap.adjoint_inner_left _ _ _
  have hT : evenTimeBandFourier a (x : evenSubspace) = 0 := by
    have hself : (inner ℂ (evenTimeBandFourier a (x : evenSubspace))
        (evenTimeBandFourier a (x : evenSubspace)) : ℂ) = 0 := by
      rw [← hadj, ← hCeq]
      exact hzero
    exact inner_self_eq_zero.1 hself
  exact Subtype.ext (evenTimeBandFourier_injective_on_timeLimited ha hmem hT)


/-- **The constrained greedy family is complete.**  A vector of the constrained subspace orthogonal
to every constrained mode is zero.  This is the density hypothesis a Hilbert basis needs, and it is
exactly injectivity applied to the vector the greedy completeness theorem annihilates. -/
theorem constrainedProlateMode_complete {a : ℝ} (ha : 0 < a)
    {x : constrainedProlateSubspace a}
    (hx : ∀ n, (inner ℂ (constrainedProlateMode a n) x : ℂ) = 0) : x = 0 := by
  have hzero : constrainedProlateConcentration a x = 0 :=
    @ContinuousLinearMap.apply_eq_zero_of_forall_inner_svVec
      (constrainedProlateSubspace a)
      (constrainedProlateSubspace a).normedAddCommGroup
      (constrainedProlateSubspace a).innerProductSpace
      (constrainedProlateSubspace_completeSpace a)
      (constrainedProlateConcentration a)
      (isCompactOperator_constrainedProlateConcentration a ha)
      (constrainedProlateConcentration_isPositive a).isSymmetric
      (fun y => (constrainedProlateConcentration_isPositive a).re_inner_nonneg_right y)
      x hx
  exact constrainedProlateConcentration_injective ha hzero

/-- **Every constrained singular value is live.**  A vanishing value would give a unit greedy vector
in the kernel, which injectivity forbids. -/
theorem constrainedProlateConcentrationValue_ne_zero {a : ℝ} (ha : 0 < a) (n : ℕ)
    (hunit : ‖constrainedProlateMode a n‖ = 1) :
    constrainedProlateConcentrationValue a n ≠ 0 := by
  intro hval
  have happ : constrainedProlateConcentration a (constrainedProlateMode a n) = 0 := by
    have h := @ContinuousLinearMap.apply_svVec
      (constrainedProlateSubspace a)
      (constrainedProlateSubspace a).normedAddCommGroup
      (constrainedProlateSubspace a).innerProductSpace
      (constrainedProlateConcentration a) n
    rw [show constrainedProlateMode a n
        = ContinuousLinearMap.svVec (H := constrainedProlateSubspace a)
            (constrainedProlateConcentration a) n from rfl, h,
      show ContinuousLinearMap.svVal (H := constrainedProlateSubspace a)
          (constrainedProlateConcentration a) n = constrainedProlateConcentrationValue a n from rfl,
      hval]
    simp
  have hzero : constrainedProlateMode a n = 0 := constrainedProlateConcentration_injective ha happ
  rw [hzero] at hunit
  simp at hunit


/-- **The unconstrained greedy family is complete on the time-limited carrier.**  A carrier vector
orthogonal to every concentration mode is annihilated by the concentration operator, hence zero.
This is the density hypothesis for the Hilbert basis in which the transfer theorems' diagonal `d`
and constraint coordinates `ℓ` live. -/
theorem evenProlateConcentrationMode_complete_on_timeLimited {a : ℝ} (ha : 0 < a)
    {x : evenSubspace} (hx : x ∈ evenTimeLimitedSubspace a)
    (horth : ∀ n, (inner ℂ (evenProlateConcentrationMode a n) x : ℂ) = 0) : x = 0 := by
  have hzero : evenProlateConcentration a x = 0 :=
    ContinuousLinearMap.apply_eq_zero_of_forall_inner_svVec
      (isCompactOperator_evenProlateConcentration a ha)
      (evenProlateConcentration_isPositive a).isSymmetric
      (fun y => (evenProlateConcentration_isPositive a).re_inner_nonneg_right y)
      horth
  exact evenProlateConcentration_injective_on_timeLimited ha hx hzero

end RHTower

end
