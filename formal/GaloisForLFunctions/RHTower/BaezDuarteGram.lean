import GaloisForLFunctions.RHTower.BaezDuarteL2Carrier

/-!
# The Báez-Duarte Gram entries as a real integral of fractional parts

The quantitative side of the Nyman--Beurling criterion is a least-squares problem: the distance from the
target to the span of finitely many generators is determined by the Gram matrix of the generators and the
vector of their inner products with the target.  In the carrier of `BaezDuarteL2Carrier` all of these are
honest `L²` inner products, so the Gram matrix is a well-posed unconditional object.

This file identifies it.  Every generator is *real* valued — `bdGenFun θ u = (({θu} − θ{u})/u : ℝ)` — so the
Gram entry is the real integral

`bdGram θ₁ θ₂ = ∫₁^∞ ({θ₁u} − θ₁{u})({θ₂u} − θ₂{u}) u^{-2} du`

(written with the `u^{-1}` factors inside the generators), and the inner product on the carrier is its
complexification.  That is the classical Báez-Duarte Gram integral, now attached to a Lean carrier: it is
symmetric, its diagonal is the squared norm, and it is a positive semidefinite form.

Nothing here evaluates the integral; the point is that the object the quantitative theory needs is now
available, real, and unconditional.
-/

open MeasureTheory Set Complex
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- The Báez-Duarte generator as a real-valued function. -/
def bdGenReal (θ : ℝ) : ℝ → ℝ := fun u => (Int.fract (θ * u) - θ * Int.fract u) / u

theorem bdGenFun_eq_ofReal (θ : ℝ) (u : ℝ) :
    bdGenFun θ u = ((bdGenReal θ u : ℝ) : ℂ) := by
  rw [bdGenFun, bdGenReal, div_eq_mul_inv]
  push_cast
  ring

/-- **The Gram entry of two Báez-Duarte generators**, as a real integral of fractional parts. -/
def bdGram (θ₁ θ₂ : ℝ) : ℝ := ∫ u in Ioi (1 : ℝ), bdGenReal θ₁ u * bdGenReal θ₂ u

/-- **The carrier inner product of two generators is the complexification of the Gram integral.** -/
theorem inner_bdGen_eq_bdGram (θ₁ θ₂ : ℝ) :
    inner ℂ (bdGen θ₁) (bdGen θ₂) = ((bdGram θ₁ θ₂ : ℝ) : ℂ) := by
  rw [MeasureTheory.L2.inner_def, bdGram, ← integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [(memLp_bdGenFun θ₁).coeFn_toLp, (memLp_bdGenFun θ₂).coeFn_toLp] with u hu1 hu2
  rw [bdGen, bdGen, hu1, hu2, bdGenFun_eq_ofReal, bdGenFun_eq_ofReal, RCLike.inner_apply,
    Complex.conj_ofReal]
  push_cast
  ring

theorem bdGram_symm (θ₁ θ₂ : ℝ) : bdGram θ₁ θ₂ = bdGram θ₂ θ₁ := by
  rw [bdGram, bdGram]
  refine integral_congr_ae ?_
  filter_upwards with u
  ring

/-- The diagonal of the Gram matrix is the squared norm of the generator. -/
theorem bdGram_self (θ : ℝ) : bdGram θ θ = ‖bdGen θ‖ ^ 2 := by
  have h : (RCLike.re (inner ℂ (bdGen θ) (bdGen θ)) : ℝ) = ‖bdGen θ‖ ^ 2 :=
    inner_self_eq_norm_sq _
  rw [inner_bdGen_eq_bdGram] at h
  rw [← h]
  show bdGram θ θ = ((bdGram θ θ : ℝ) : ℂ).re
  exact (Complex.ofReal_re _).symm

theorem bdGram_self_nonneg (θ : ℝ) : 0 ≤ bdGram θ θ := by
  rw [bdGram_self]
  positivity

/-- **The Gram form is positive semidefinite.**  For real coefficients the quadratic form of the Gram
matrix is the squared norm of the corresponding combination of generators, hence nonnegative. -/
theorem bdGram_quadraticForm_eq_norm_sq {I : Type*} (s : Finset I) (θ : I → ℝ) (c : I → ℝ) :
    ∑ i ∈ s, ∑ j ∈ s, c i * c j * bdGram (θ i) (θ j)
      = ‖∑ i ∈ s, (c i : ℂ) • bdGen (θ i)‖ ^ 2 := by
  classical
  have hexp : inner ℂ (∑ i ∈ s, (c i : ℂ) • bdGen (θ i)) (∑ j ∈ s, (c j : ℂ) • bdGen (θ j))
      = ((∑ i ∈ s, ∑ j ∈ s, c i * c j * bdGram (θ i) (θ j) : ℝ) : ℂ) := by
    rw [sum_inner]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_left, inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_right, inner_bdGen_eq_bdGram, Complex.conj_ofReal]
    ring
  have hnorm : (RCLike.re (inner ℂ (∑ i ∈ s, (c i : ℂ) • bdGen (θ i))
      (∑ i ∈ s, (c i : ℂ) • bdGen (θ i))) : ℝ)
      = ‖∑ i ∈ s, (c i : ℂ) • bdGen (θ i)‖ ^ 2 := inner_self_eq_norm_sq _
  rw [hexp] at hnorm
  rw [← hnorm]
  show ∑ i ∈ s, ∑ j ∈ s, c i * c j * bdGram (θ i) (θ j)
      = ((∑ i ∈ s, ∑ j ∈ s, c i * c j * bdGram (θ i) (θ j) : ℝ) : ℂ).re
  exact (Complex.ofReal_re _).symm

theorem bdGram_quadraticForm_nonneg {I : Type*} (s : Finset I) (θ : I → ℝ) (c : I → ℝ) :
    0 ≤ ∑ i ∈ s, ∑ j ∈ s, c i * c j * bdGram (θ i) (θ j) := by
  rw [bdGram_quadraticForm_eq_norm_sq]
  positivity

end RHTower

end
