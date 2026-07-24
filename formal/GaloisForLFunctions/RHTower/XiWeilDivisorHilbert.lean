import GaloisForLFunctions.RHTower.XiWeilCriterionConverse

/-!
# The divisor Hilbert space carrying the Weil form

A test function enters the Weil polarization only through its values on the
multiplicity-exact divisor, and the genus-one bound places the regularized Cauchy
kernels inside `ℓ²` of the divisor: their restrictions are absolutely summable,
hence bounded, hence square-summable.

Conjugation of the centered coordinate permutes the divisor, so on that space the
Weil pairing is

`Q a = ∑' q, a q * conj (a (lineConj q))`,

which the arithmetic–geometric bound `|xy| ≤ (|x|² + |y|²)/2` shows is absolutely
convergent for every `ℓ²` sequence.  Boundedness of this form is what allows a
value at one test function to be transported to any test function approximating
it — the mechanism by which a detection performed inside the critical strip is
carried out to base points lying outside it.
-/

open Complex

namespace RHTower

noncomputable section

/-- The Hilbert space of square-summable functions on the divisor. -/
abbrev XiDivisorL2 : Type := lp (fun _ : XiZeroCopy => ℂ) 2

/-! ## §1 Kernels restrict into `ℓ²` -/

/-- The regularized Cauchy kernel restricted to the divisor is absolutely
summable — this is the genus-one convergence of the relative resolvent trace. -/
theorem summable_norm_kernel_restriction {z : ℂ} (hz : XiC z ≠ 0) :
    Summable (fun q : XiZeroCopy =>
      ‖xiCauchyRegularizedKernel z (xiSpectralPoint q)‖) :=
  summable_norm_iff.mpr (summable_xiRelativeResolventTerm hz)

/-- An absolutely summable family of complex numbers is square-summable. -/
theorem summable_sq_of_summable_norm {f : XiZeroCopy → ℂ}
    (h : Summable (fun q => ‖f q‖)) :
    Summable (fun q => ‖f q‖ ^ (2 : ℝ)) := by
  set M := ∑' q : XiZeroCopy, ‖f q‖ with hM
  have hbound : ∀ q, ‖f q‖ ≤ M :=
    fun q => h.le_tsum q (fun j _ => norm_nonneg _)
  refine Summable.of_nonneg_of_le (fun q => by positivity) (fun q => ?_)
    (h.mul_left M)
  have hpow : ‖f q‖ ^ (2 : ℝ) = ‖f q‖ * ‖f q‖ := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    ring
  rw [hpow]
  exact mul_le_mul_of_nonneg_right (hbound q) (norm_nonneg _)

/-- **Kernels live in the divisor Hilbert space.** -/
theorem memℓp_kernel_restriction {z : ℂ} (hz : XiC z ≠ 0) :
    Memℓp (fun q : XiZeroCopy =>
      xiCauchyRegularizedKernel z (xiSpectralPoint q)) 2 := by
  rw [memℓp_gen_iff (by norm_num)]
  exact summable_sq_of_summable_norm (summable_norm_kernel_restriction hz)

/-- The kernel of a base point as a vector of the divisor Hilbert space. -/
def xiKernelVec {z : ℂ} (hz : XiC z ≠ 0) : XiDivisorL2 :=
  ⟨fun q => xiCauchyRegularizedKernel z (xiSpectralPoint q),
    memℓp_kernel_restriction hz⟩

@[simp] theorem xiKernelVec_apply {z : ℂ} (hz : XiC z ≠ 0) (q : XiZeroCopy) :
    xiKernelVec hz q = xiCauchyRegularizedKernel z (xiSpectralPoint q) := rfl

/-! ## §2 The Weil form on the divisor Hilbert space -/

/-- Square-summability transfers along the conjugation involution of the
divisor. -/
theorem summable_sq_lineConj (a : XiDivisorL2) :
    Summable (fun q : XiZeroCopy =>
      ‖a (xiZeroCopyLineConjEquiv q)‖ ^ (2 : ℝ)) := by
  have hsum : Summable (fun q : XiZeroCopy => ‖a q‖ ^ (2 : ℝ)) := by
    have h := lp.memℓp a
    rwa [memℓp_gen_iff (by norm_num : (0:ℝ) < (2:ENNReal).toReal)] at h
  exact (Equiv.summable_iff xiZeroCopyLineConjEquiv).mpr hsum

/-- The Weil summand is absolutely summable on the divisor Hilbert space, by the
arithmetic–geometric bound against the two square-summable families. -/
theorem summable_weilL2Summand (a : XiDivisorL2) :
    Summable (fun q : XiZeroCopy =>
      a q * (starRingEnd ℂ) (a (xiZeroCopyLineConjEquiv q))) := by
  have h1 : Summable (fun q : XiZeroCopy => ‖a q‖ ^ (2 : ℝ)) := by
    have h := lp.memℓp a
    rwa [memℓp_gen_iff (by norm_num : (0:ℝ) < (2:ENNReal).toReal)] at h
  have h2 := summable_sq_lineConj a
  refine summable_norm_iff.mp ?_
  refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_)
    ((h1.add h2).mul_left (1 / 2))
  rw [norm_mul, RCLike.norm_conj]
  have hxy : ∀ x y : ℝ, 0 ≤ x → 0 ≤ y →
      x * y ≤ 1 / 2 * (x ^ (2 : ℝ) + y ^ (2 : ℝ)) := by
    intro x y hx hy
    have hx2 : x ^ (2 : ℝ) = x * x := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    have hy2 : y ^ (2 : ℝ) = y * y := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      ring
    rw [hx2, hy2]
    nlinarith [sq_nonneg (x - y)]
  exact hxy _ _ (norm_nonneg _) (norm_nonneg _)

/-- **The Weil form on the divisor Hilbert space.**  Conjugation permutes the
divisor, so pairing a sequence with its conjugate-reindexed conjugate is the
Weil polarization written intrinsically. -/
def xiWeilL2Form (a : XiDivisorL2) : ℂ :=
  ∑' q : XiZeroCopy, a q * (starRingEnd ℂ) (a (xiZeroCopyLineConjEquiv q))

/-- **The form computes the Weil polarization of a Cauchy kernel.** -/
theorem xiWeilL2Form_kernelVec {z : ℂ} (hz : XiC z ≠ 0) :
    xiWeilL2Form (xiKernelVec hz) =
      xiWeilPolarization (xiCauchyRegularizedKernel z)
        (xiCauchyRegularizedKernel z) := by
  rw [xiWeilL2Form, xiWeilPolarization]
  refine tsum_congr fun q => ?_
  rw [xiKernelVec_apply, xiKernelVec_apply, xiWeilSharp,
    xiSpectralPoint_lineConj]

end

end RHTower
