import GaloisForLFunctions.RHTower.MobiusPositiveExcursion
import GaloisForLFunctions.RHTower.MobiusLaplaceAdditiveTriangle

/-!
# The binary additive Möbius self-convolution is positive infinitely often

At order one the Hermitian mixed convolution is the binary additive self-convolution
`∑_{a+b=N} μ(a) μ(b)`, which is an integer.  Positivity of an integer means it is at least one, so
the recurrence of positive excursions becomes the arithmetic statement

```
∑_{a+b=N} μ(a) μ(b) ≥ 1   for infinitely many N.
```
-/

namespace RHTower

/-- The binary additive Möbius self-convolution as an integer. -/
def mobiusIntConvolution (N : ℕ) : ℤ :=
  ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) N,
    ArithmeticFunction.moebius ab.1 * ArithmeticFunction.moebius ab.2

/-- The complex Möbius coefficient of this development is the corpus one. -/
theorem mobiusCoeff_eq_mobiusComplexCoefficient :
    mobiusCoeff = mobiusComplexCoefficient := rfl

/-- At order one the Hermitian mixed convolution is the corpus additive self-convolution. -/
theorem mixedAdditiveConvolutionPower_one_mobius (N : ℕ) :
    mixedAdditiveConvolutionPower mobiusCoeff 1 N = mobiusAdditiveConvolution N := by
  rw [mixedAdditiveConvolutionPower_one, mobiusAdditiveConvolution]
  refine Finset.sum_congr rfl fun ab _ => ?_
  simp [mobiusCoeff, mobiusComplexCoefficient]

/-- At order one the coefficient is the cast of an integer. -/
theorem mixedAdditiveConvolutionPower_one_mobius_eq_intCast (N : ℕ) :
    mixedAdditiveConvolutionPower mobiusCoeff 1 N = ((mobiusIntConvolution N : ℤ) : ℂ) := by
  rw [mixedAdditiveConvolutionPower_one, mobiusIntConvolution]
  push_cast
  refine Finset.sum_congr rfl fun ab _ => ?_
  simp [mobiusCoeff]

/-- Its real part is that integer. -/
theorem mixedAdditiveConvolutionPower_one_mobius_re (N : ℕ) :
    (mixedAdditiveConvolutionPower mobiusCoeff 1 N).re = (mobiusIntConvolution N : ℝ) := by
  rw [mixedAdditiveConvolutionPower_one_mobius_eq_intCast]
  simp

/-- **The binary excursion law.**  Beyond every finite set of indices the binary additive Möbius
self-convolution attains a value at least one. -/
theorem exists_notMem_one_le_mobiusIntConvolution (S : Finset ℕ) :
    ∃ N : ℕ, N ∉ S ∧ 1 ≤ mobiusIntConvolution N := by
  obtain ⟨N, hNmem, hNpos⟩ :=
    exists_notMem_pos_mixedAdditiveConvolutionPower (k := 1) one_pos S
  refine ⟨N, hNmem, ?_⟩
  rw [mixedAdditiveConvolutionPower_one_mobius_re] at hNpos
  exact_mod_cast hNpos

/-- The set of such indices is infinite. -/
theorem infinite_one_le_mobiusIntConvolution :
    {N : ℕ | 1 ≤ mobiusIntConvolution N}.Infinite := by
  intro hfin
  obtain ⟨N, hNmem, hNone⟩ := exists_notMem_one_le_mobiusIntConvolution hfin.toFinset
  exact hNmem (hfin.mem_toFinset.mpr hNone)

end RHTower
