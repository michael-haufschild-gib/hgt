import GaloisForLFunctions.HTGeometry.CausalRationalKernel

/-!
# Exact block propagation of exponential convolution

For an arbitrary complex exponent, the causal convolution over two adjacent
intervals is the sum of the propagated old state and the new block response.
No decay or small-step condition is needed for this identity. Finite banks of
exponentials retain one scalar state per mode, including unstable modes.
-/

open MeasureTheory
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The modal state accumulated between two endpoints. -/
def exponentialBlock (λ : ℂ) (f : C(ℝ, ℂ)) (a b : ℝ) : ℂ :=
  ∫ s in a..b, Complex.exp (λ * ((b - s : ℝ) : ℂ)) * f s

/-- An exponential propagator factors across any intermediate endpoint. -/
theorem exponential_propagator_split (λ : ℂ) (a b s : ℝ) :
    Complex.exp (λ * ((b - s : ℝ) : ℂ)) =
      Complex.exp (λ * ((b - a : ℝ) : ℂ)) *
        Complex.exp (λ * ((a - s : ℝ) : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact composition of block responses; the endpoints need not be ordered. -/
theorem exponentialBlock_split (λ : ℂ) (f : C(ℝ, ℂ)) (a b c : ℝ) :
    exponentialBlock λ f a c =
      Complex.exp (λ * ((c - b : ℝ) : ℂ)) * exponentialBlock λ f a b +
        exponentialBlock λ f b c := by
  have hi : Continuous (fun s : ℝ => Complex.exp (λ * ((c - s : ℝ) : ℂ)) * f s) := by
    fun_prop
  unfold exponentialBlock
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hi.intervalIntegrable a b) (hi.intervalIntegrable b c)]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  rw [exponential_propagator_split λ b c s, mul_assoc]

/-- The existing causal convolution is the modal block starting at zero. -/
theorem exponentialBlock_zero_eq_causalConv (λ : ℂ) (f : C(ℝ, ℂ)) (t : ℝ) :
    exponentialBlock λ f 0 t =
      causalConv (fun s => Complex.exp (λ * (s : ℂ))) f t := rfl

/-- Carrying a modal state reproduces full-window convolution exactly. -/
theorem causalConv_exponential_split (λ : ℂ) (f : C(ℝ, ℂ)) (t s : ℝ) :
    causalConv (fun x => Complex.exp (λ * (x : ℂ))) f (t + s) =
      Complex.exp (λ * (s : ℂ)) *
        causalConv (fun x => Complex.exp (λ * (x : ℂ))) f t +
      exponentialBlock λ f t (t + s) := by
  simpa only [add_sub_cancel_left, exponentialBlock_zero_eq_causalConv] using
    exponentialBlock_split λ f 0 t (t + s)

/-- The response of a finite complex modal kernel. -/
def modalBlockResponse {n : ℕ} (residue pole : Fin n → ℂ)
    (f : C(ℝ, ℂ)) (a b : ℝ) : ℂ :=
  ∑ j, residue j * exponentialBlock (pole j) f a b

/-- One boundary state per mode suffices for exact continuation of a modal bank. -/
theorem modalBlockResponse_split {n : ℕ} (residue pole : Fin n → ℂ)
    (f : C(ℝ, ℂ)) (a b c : ℝ) :
    modalBlockResponse residue pole f a c =
      (∑ j, residue j * Complex.exp (pole j * ((c - b : ℝ) : ℂ)) *
        exponentialBlock (pole j) f a b) + modalBlockResponse residue pole f b c := by
  unfold modalBlockResponse
  simp_rw [exponentialBlock_split _ _ a b c, mul_add, ← mul_assoc]
  exact Finset.sum_add_distrib

/-- The modal-bank formula is the integral against its finite exponential kernel. -/
theorem modalBlockResponse_eq_integral {n : ℕ} (residue pole : Fin n → ℂ)
    (f : C(ℝ, ℂ)) (a b : ℝ) :
    modalBlockResponse residue pole f a b =
      ∫ s in a..b, (∑ j, residue j * Complex.exp (pole j * ((b - s : ℝ) : ℂ))) * f s := by
  simp only [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · unfold modalBlockResponse exponentialBlock
    apply Finset.sum_congr rfl
    intro j _
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s _
    ring
  · intro j _
    exact (by fun_prop : Continuous (fun s : ℝ =>
      residue j * Complex.exp (pole j * ((b - s : ℝ) : ℂ)) * f s)).intervalIntegrable a b

end

end GaloisForLFunctions.HTGeometry
