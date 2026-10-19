import GaloisForLFunctions.RHTower.RootOfUnityIntervalCompletion
import GaloisForLFunctions.HTGeometry.FiniteRowRecombination

/-!
# Zero-origin multipliers and Fourier difference energy

The finite translation principle of Lemma 6.1 of *The Quasi-Riemann Hypothesis*
combines with its recombination Lemma B.3.  A multiplier extended by zero at
the origin has Fourier coefficients summing to zero.  Its action therefore
depends only on differences of Fourier coefficients, with an explicit
mean-square bound even when the multiplier varies between observations.

All transforms use the corpus's existing `RootOfUnityCompletion.zmodCoeff`.
-/

noncomputable section
open scoped BigOperators NNReal

namespace GaloisForLFunctions.RHTower.RootOfUnityCompletion

variable {N : ℕ} [NeZero N]

/-- Multiplication becomes a finite sum of frequency translates. -/
theorem zmodCoeff_mul_eq_convolution (A f : ZMod N → ℂ) (k : ZMod N) :
    zmodCoeff (fun x => A x * f x) k =
      ∑ h : ZMod N, ((N : ℂ)⁻¹ * zmodCoeff A h) * zmodCoeff f (k - h) := by
  classical
  rw [zmodCoeff]
  calc
    (∑ x : ZMod N, A x * f x * ZMod.stdAddChar (-(k * x))) =
        ∑ x : ZMod N, ∑ h : ZMod N,
          ((N : ℂ)⁻¹ * zmodCoeff A h) *
            (f x * ZMod.stdAddChar (-((k - h) * x))) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [fourier_inversion A x]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro h _
      calc
        _ = ((N : ℂ)⁻¹ * zmodCoeff A h) * f x *
            (ZMod.stdAddChar (h * x) * ZMod.stdAddChar (-(k * x))) := by ring
        _ = _ := by
          rw [← AddChar.map_add_eq_mul]
          have heq : h * x + -(k * x) = -((k - h) * x) := by ring
          rw [heq]
          ring
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [zmodCoeff, Finset.mul_sum]

/-- Normalized Fourier coefficients of a multiplier extended by zero at the origin. -/
def zeroOriginFourierWeight (A : ZMod N → ℂ) (h : ZMod N) : ℂ :=
  (N : ℂ)⁻¹ * zmodCoeff (Function.update A 0 0) h

/-- Zero extension enforces the exact cancellation of the translation coefficients. -/
theorem sum_zeroOriginFourierWeight (A : ZMod N → ℂ) :
    ∑ h : ZMod N, zeroOriginFourierWeight A h = 0 := by
  have h := fourier_inversion (Function.update A 0 0) 0
  simpa [zeroOriginFourierWeight, ← Finset.mul_sum] using h.symm

/-- Any common Fourier value can be subtracted before recombining the translates. -/
theorem zmodCoeff_zeroOrigin_mul_eq_centered (A f : ZMod N → ℂ)
    (k : ZMod N) (c : ℂ) :
    zmodCoeff (fun x => Function.update A 0 0 x * f x) k =
      ∑ h : ZMod N, zeroOriginFourierWeight A h * (zmodCoeff f (k - h) - c) := by
  rw [zmodCoeff_mul_eq_convolution]
  change (∑ h, zeroOriginFourierWeight A h * zmodCoeff f (k - h)) = _
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
    sum_zeroOriginFourierWeight, zero_mul, sub_zero]

/-- The multiplier's output is bounded by frequency differences from any chosen center. -/
theorem norm_zmodCoeff_zeroOrigin_mul_sq_le (A f : ZMod N → ℂ)
    (k : ZMod N) (c : ℂ) :
    ‖zmodCoeff (fun x => Function.update A 0 0 x * f x) k‖ ^ 2 ≤
      (∑ h : ZMod N, ‖zeroOriginFourierWeight A h‖) *
        ∑ h : ZMod N, ‖zeroOriginFourierWeight A h‖ * ‖zmodCoeff f (k - h) - c‖ ^ 2 := by
  rw [zmodCoeff_zeroOrigin_mul_eq_centered A f k c]
  exact HTGeometry.norm_sum_smul_sq_le_mass Finset.univ
    (zeroOriginFourierWeight A) (fun h => zmodCoeff f (k - h) - c)

/-- Observation-dependent multipliers share one canonical envelope for difference energy. -/
theorem sum_weight_zmodCoeff_zeroOrigin_mul_sq_le {ρ : Type*} [Fintype ρ]
    (w : ρ → ℝ≥0) (A f : ρ → ZMod N → ℂ) (k : ρ → ZMod N) (c : ρ → ℂ) :
    (∑ r, (w r : ℝ) *
        ‖zmodCoeff (fun x => Function.update (A r) 0 0 x * f r x) (k r)‖ ^ 2) ≤
      (∑ h : ZMod N, ‖fun r => zeroOriginFourierWeight (A r) h‖) *
        ∑ h : ZMod N, ‖fun r => zeroOriginFourierWeight (A r) h‖ *
          ∑ r, (w r : ℝ) * ‖zmodCoeff (f r) (k r - h) - c r‖ ^ 2 := by
  calc
    _ = ∑ r, (w r : ℝ) * ‖∑ h : ZMod N, zeroOriginFourierWeight (A r) h *
        (zmodCoeff (f r) (k r - h) - c r)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro r _
      rw [zmodCoeff_zeroOrigin_mul_eq_centered (A r) (f r) (k r) (c r)]
    _ ≤ _ := HTGeometry.sum_weight_norm_sum_smul_sq_le_row_envelope Finset.univ w
      (fun h r => zeroOriginFourierWeight (A r) h)
      (fun h r => zmodCoeff (f r) (k r - h) - c r)

end GaloisForLFunctions.RHTower.RootOfUnityCompletion
