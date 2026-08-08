import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.ArithmeticFunction.Defs

/-!
# The Dirichlet convolution of sequences is associative

`LSeries.convolution` is the Dirichlet convolution written on plain sequences `ℕ → ℂ`, where mathlib's
monoid structure lives on `ArithmeticFunction ℂ` — the sequences vanishing at `0`.  Sending a sequence
with `f 0 = 0` to that monoid identifies the two products, so associativity transfers:

`(f ⍟ g) ⍟ h = f ⍟ (g ⍟ h)`   whenever `f 0 = g 0 = h 0 = 0`.

The hypothesis is not a restriction in practice — a convolution vanishes at `0` for free, since the
divisor antidiagonal of `0` is empty — and it is what makes the regrouping of a threefold convolution
available: the same product of three Dirichlet series can be read as a pair convolved with a third
factor, or as one factor convolved with a pair.
-/

noncomputable section
namespace RHTower.Sieve
open Finset

/-- A sequence vanishing at `0`, as an arithmetic function. -/
def toArith (f : ℕ → ℂ) (hf : f 0 = 0) : ArithmeticFunction ℂ :=
  { toFun := f, map_zero' := hf }

theorem toArith_apply (f : ℕ → ℂ) (hf : f 0 = 0) (n : ℕ) : (toArith f hf) n = f n := rfl

/-- The monoid product of arithmetic functions is the convolution of the sequences. -/
theorem toArith_mul_apply (f g : ℕ → ℂ) (hf : f 0 = 0) (hg : g 0 = 0) (n : ℕ) :
    (toArith f hf * toArith g hg) n = LSeries.convolution f g n := by
  rw [ArithmeticFunction.mul_apply, LSeries.convolution_def]
  rfl

/-- A convolution vanishes at `0`: the divisor antidiagonal of `0` is empty. -/
theorem convolution_zero (f g : ℕ → ℂ) : LSeries.convolution f g 0 = 0 := by
  rw [LSeries.convolution_def]
  simp

theorem toArith_convolution {f g : ℕ → ℂ} (hf : f 0 = 0) (hg : g 0 = 0) :
    toArith (LSeries.convolution f g) (convolution_zero f g) = toArith f hf * toArith g hg := by
  ext n
  rw [toArith_apply, toArith_mul_apply]

/-- **The Dirichlet convolution of sequences is associative.** -/
theorem convolution_assoc {f g h : ℕ → ℂ} (hf : f 0 = 0) (hg : g 0 = 0) (hh : h 0 = 0) :
    LSeries.convolution (LSeries.convolution f g) h
      = LSeries.convolution f (LSeries.convolution g h) := by
  funext n
  rw [← toArith_mul_apply _ _ (convolution_zero f g) hh,
    ← toArith_mul_apply _ _ hf (convolution_zero g h),
    toArith_convolution hf hg, toArith_convolution hg hh, mul_assoc]

end RHTower.Sieve
end
