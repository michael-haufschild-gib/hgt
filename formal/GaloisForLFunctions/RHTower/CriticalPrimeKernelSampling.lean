import GaloisForLFunctions.RHTower.CriticalPrimeSamplingSchattenBridge

/-!
# Normalized critical-prime kernel sampling

A Bessel estimate for a family of unit kernel vectors constructs the literal weighted all-prime
analysis operator.  Its adjoint sends each coordinate vector to the corresponding weighted kernel,
so the common non-Hilbert--Schmidt and non-trace-class endpoints follow without any extra operator
interface.
-/

open scoped InnerProductSpace

namespace RHTower

noncomputable section

open ContinuousLinearMap

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Weighted normalized-kernel restriction at one prime. -/
def criticalPrimeKernelRestriction (k : Nat.Primes → H) (p : Nat.Primes) : H →L[ℂ] ℂ :=
  (Real.sqrt (criticalPrimeSamplingWeight p) : ℂ) • innerSL ℂ (k p)

@[simp] theorem criticalPrimeKernelRestriction_apply
    (k : Nat.Primes → H) (p : Nat.Primes) (x : H) :
    criticalPrimeKernelRestriction k p x =
      (Real.sqrt (criticalPrimeSamplingWeight p) : ℂ) * inner ℂ (k p) x := by
  simp [criticalPrimeKernelRestriction]

theorem criticalPrimeKernelSampling_memℓp
    (k : Nat.Primes → H)
    (hsummable : ∀ x, Summable fun p => ‖criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ))
    (x : H) :
    Memℓp (fun p => criticalPrimeKernelRestriction k p x) 2 := by
  exact memℓp_gen (hsummable x)

/-- Algebraic all-prime analysis map obtained from the pointwise square-summability law. -/
def criticalPrimeKernelSamplingLinearMap
    (k : Nat.Primes → H)
    (hsummable : ∀ x, Summable fun p => ‖criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ)) :
    H →ₗ[ℂ] CriticalPrimeEllTwo where
  toFun x := ⟨fun p => criticalPrimeKernelRestriction k p x,
    criticalPrimeKernelSampling_memℓp k hsummable x⟩
  map_add' := by
    intro x y
    ext p
    change (Real.sqrt (criticalPrimeSamplingWeight p) : ℂ) * inner ℂ (k p) (x + y) =
      (Real.sqrt (criticalPrimeSamplingWeight p) : ℂ) * inner ℂ (k p) x +
        (Real.sqrt (criticalPrimeSamplingWeight p) : ℂ) * inner ℂ (k p) y
    rw [inner_add_right, mul_add]
  map_smul' := by
    intro c x
    ext p
    simp

@[simp] theorem criticalPrimeKernelSamplingLinearMap_apply
    (k : Nat.Primes → H)
    (hsummable : ∀ x, Summable fun p => ‖criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ))
    (x : H) (p : Nat.Primes) :
    criticalPrimeKernelSamplingLinearMap k hsummable x p =
      criticalPrimeKernelRestriction k p x := rfl

theorem norm_criticalPrimeKernelSamplingLinearMap_le
    (k : Nat.Primes → H)
    (hsummable : ∀ x, Summable fun p => ‖criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' p, ‖criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ) ≤
        (C * ‖x‖) ^ (2 : ℝ))
    (x : H) :
    ‖criticalPrimeKernelSamplingLinearMap k hsummable x‖ ≤ C * ‖x‖ := by
  have hleft : 0 ≤ ‖criticalPrimeKernelSamplingLinearMap k hsummable x‖ := norm_nonneg _
  have hright : 0 ≤ C * ‖x‖ := mul_nonneg hC (norm_nonneg _)
  have hdiag :
      ‖criticalPrimeKernelSamplingLinearMap k hsummable x‖ ^ (2 : ℝ) =
        ∑' p, ‖criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : Nat.Primes => ℂ) (by norm_num)
      (criticalPrimeKernelSamplingLinearMap k hsummable x)
  have hpow :
      ‖criticalPrimeKernelSamplingLinearMap k hsummable x‖ ^ (2 : ℝ) ≤
        (C * ‖x‖) ^ (2 : ℝ) := by
    rw [hdiag]
    exact hBessel x
  have hleft2 :
      ‖criticalPrimeKernelSamplingLinearMap k hsummable x‖ ^ (2 : ℝ) =
        ‖criticalPrimeKernelSamplingLinearMap k hsummable x‖ ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  have hright2 : (C * ‖x‖) ^ (2 : ℝ) = (C * ‖x‖) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  rw [hleft2, hright2] at hpow
  have hsqrt := Real.sqrt_le_sqrt hpow
  rwa [Real.sqrt_sq hleft, Real.sqrt_sq hright] at hsqrt

/-- Bounded normalized all-prime kernel sampler supplied by a Bessel estimate. -/
def criticalPrimeKernelSamplingOperator
    (k : Nat.Primes → H)
    (hsummable : ∀ x, Summable fun p => ‖criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' p, ‖criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ) ≤
        (C * ‖x‖) ^ (2 : ℝ)) :
    H →L[ℂ] CriticalPrimeEllTwo :=
  LinearMap.mkContinuous (criticalPrimeKernelSamplingLinearMap k hsummable) C
    (norm_criticalPrimeKernelSamplingLinearMap_le k hsummable hC hBessel)

@[simp] theorem criticalPrimeKernelSamplingOperator_apply
    (k : Nat.Primes → H)
    (hsummable : ∀ x, Summable fun p => ‖criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' p, ‖criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ) ≤
        (C * ‖x‖) ^ (2 : ℝ))
    (x : H) (p : Nat.Primes) :
    criticalPrimeKernelSamplingOperator k hsummable hC hBessel x p =
      criticalPrimeKernelRestriction k p x := rfl

variable [CompleteSpace H]

/-- Pulling a coordinate vector through the adjoint recovers the weighted kernel vector. -/
theorem adjoint_criticalPrimeKernelSamplingOperator_coordinateBasis
    (k : Nat.Primes → H)
    (hsummable : ∀ x, Summable fun p => ‖criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' p, ‖criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ) ≤
        (C * ‖x‖) ^ (2 : ℝ))
    (p : Nat.Primes) :
    adjoint (criticalPrimeKernelSamplingOperator k hsummable hC hBessel)
        (HTGeometry.ellTwoCoordinateBasis Nat.Primes p) =
      (Real.sqrt (criticalPrimeSamplingWeight p) : ℂ) • k p := by
  classical
  apply ext_inner_left ℂ
  intro x
  rw [adjoint_inner_right, HTGeometry.ellTwoCoordinateBasis_apply,
    lp.inner_single_right, criticalPrimeKernelSamplingOperator_apply,
    criticalPrimeKernelRestriction_apply]
  rw [inner_smul_right]
  simp [RCLike.inner_apply]

/-- Unit normalized kernels give exactly the literal critical-prime coordinate energy. -/
theorem normSq_adjoint_criticalPrimeKernelSamplingOperator_coordinateBasis
    (k : Nat.Primes → H) (hk : ∀ p, ‖k p‖ = 1)
    (hsummable : ∀ x, Summable fun p => ‖criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' p, ‖criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ) ≤
        (C * ‖x‖) ^ (2 : ℝ))
    (p : Nat.Primes) :
    ‖adjoint (criticalPrimeKernelSamplingOperator k hsummable hC hBessel)
        (HTGeometry.ellTwoCoordinateBasis Nat.Primes p)‖ ^ 2 =
      criticalPrimeSamplingWeight p := by
  rw [adjoint_criticalPrimeKernelSamplingOperator_coordinateBasis,
    norm_smul, hk, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt]
  exact (criticalPrimeSamplingWeight_pos p).le

/-- Every bounded normalized critical-prime kernel sampler is non-Hilbert--Schmidt. -/
theorem criticalPrimeKernelSamplingOperator_not_isHilbertSchmidt
    (k : Nat.Primes → H) (hk : ∀ p, ‖k p‖ = 1)
    (hsummable : ∀ x, Summable fun p => ‖criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' p, ‖criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ) ≤
        (C * ‖x‖) ^ (2 : ℝ)) :
    ¬ (criticalPrimeKernelSamplingOperator k hsummable hC hBessel).IsHilbertSchmidt :=
  not_isHilbertSchmidt_of_adjoint_coordinate_normSq_eq_criticalPrimeSamplingWeight _
    (normSq_adjoint_criticalPrimeKernelSamplingOperator_coordinateBasis
      k hk hsummable hC hBessel)

/-- Its positive Gram incidence is never trace class. -/
theorem criticalPrimeKernelSamplingIncidence_not_memSchattenClass_one
    (k : Nat.Primes → H) (hk : ∀ p, ‖k p‖ = 1)
    (hsummable : ∀ x, Summable fun p => ‖criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hBessel : ∀ x,
      ∑' p, ‖criticalPrimeKernelRestriction k p x‖ ^ (2 : ℝ) ≤
        (C * ‖x‖) ^ (2 : ℝ)) :
    ¬ MemSchattenClass 1 (criticalPrimeSamplingIncidence
      (criticalPrimeKernelSamplingOperator k hsummable hC hBessel)) :=
  criticalPrimeSamplingIncidence_not_memSchattenClass_one _
    (normSq_adjoint_criticalPrimeKernelSamplingOperator_coordinateBasis
      k hk hsummable hC hBessel)

end

end RHTower
