import GaloisForLFunctions.HTGeometry.OddDirichletKernel
import GaloisForLFunctions.RHTower.GaussLattice

/-!
# Convergence of the odd harmonic exponential series

The odd exponential harmonics `∑ e^{i(2k+1)θ}/(2k+1)` converge off the zeros of the sine.  The
partial sums of `∑ e^{i(2k+1)θ}` are a rotated geometric progression on the unit circle, so
`RHTower.norm_geom_sum_le` bounds them by `2/‖1 - e^{2iθ}‖ = 1/|sin θ|`, uniformly in the truncation,
and Dirichlet's test applies.

This is the hypothesis Abel's limit theorem needs in order to evaluate the boundary series as the
radial limit of `artanh`, which is the remaining step for the odd-harmonic Fourier identity.  The
real and imaginary parts are the series treated in
`GaloisForLFunctions.HTGeometry.OddDirichletKernel`.
-/

open Finset Filter Topology

namespace RHTower

/-- The chord length on the unit circle. -/
theorem norm_one_sub_exp_mul_I (φ : ℝ) :
    ‖1 - Complex.exp ((φ : ℂ) * Complex.I)‖ = 2 * |Real.sin (φ / 2)| := by
  have hexp : Complex.exp ((φ : ℂ) * Complex.I)
      = (Real.cos φ : ℂ) + (Real.sin φ : ℂ) * Complex.I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hcos : Real.cos φ = 1 - 2 * Real.sin (φ / 2) ^ (2 : ℕ) := by
    have h := Real.cos_two_mul' (φ / 2)
    rw [show 2 * (φ / 2) = φ by ring] at h
    nlinarith [Real.sin_sq_add_cos_sq (φ / 2), h]
  have hsq : ‖1 - Complex.exp ((φ : ℂ) * Complex.I)‖ ^ (2 : ℕ) = (2 * |Real.sin (φ / 2)|) ^ (2 : ℕ) := by
    rw [hexp, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    nlinarith [Real.sin_sq_add_cos_sq φ, hcos, sq_abs (Real.sin (φ / 2))]
  have hnn1 : (0 : ℝ) ≤ ‖1 - Complex.exp ((φ : ℂ) * Complex.I)‖ := norm_nonneg _
  have hnn2 : (0 : ℝ) ≤ 2 * |Real.sin (φ / 2)| := by positivity
  nlinarith [hsq, hnn1, hnn2]

/-- The odd exponential harmonics are a rotated geometric progression. -/
theorem sum_exp_odd_eq (θ : ℝ) (N : ℕ) :
    ∑ k ∈ range N, Complex.exp (((2 * (k : ℝ) + 1) * θ : ℝ) * Complex.I)
      = Complex.exp ((θ : ℂ) * Complex.I)
        * ∑ k ∈ range N, (Complex.exp (((2 * θ : ℝ)) * Complex.I)) ^ k := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **Uniform bound on the odd exponential partial sums.** -/
theorem norm_sum_exp_odd_le {θ : ℝ} (hθ : Real.sin θ ≠ 0) (N : ℕ) :
    ‖∑ k ∈ range N, Complex.exp (((2 * (k : ℝ) + 1) * θ : ℝ) * Complex.I)‖
      ≤ 1 / |Real.sin θ| := by
  have habs : (0 : ℝ) < |Real.sin θ| := abs_pos.mpr hθ
  have hchord : ‖1 - Complex.exp (((2 * θ : ℝ)) * Complex.I)‖ = 2 * |Real.sin θ| := by
    rw [norm_one_sub_exp_mul_I (2 * θ), show (2 * θ) / 2 = θ by ring]
  have hw1 : ‖Complex.exp (((2 * θ : ℝ)) * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I _
  have hwne : Complex.exp (((2 * θ : ℝ)) * Complex.I) ≠ 1 := by
    intro h
    rw [h] at hchord
    simp only [sub_self, norm_zero] at hchord
    have habs0 : |Real.sin θ| = 0 := by linarith
    exact hθ (abs_eq_zero.mp habs0)
  have hgeom := norm_geom_sum_le hw1 hwne N
  rw [hchord] at hgeom
  rw [sum_exp_odd_eq, norm_mul, mul_comm]
  have hrot : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I _
  rw [hrot, mul_one]
  refine hgeom.trans (le_of_eq ?_)
  field_simp

/-- **Dirichlet test, complex form.**  The odd harmonic exponential series is Cauchy. -/
theorem cauchySeq_sum_oddHarmonicExp {θ : ℝ} (hθ : Real.sin θ ≠ 0) :
    CauchySeq fun N => ∑ k ∈ range N,
      (1 / (2 * (k : ℝ) + 1)) • Complex.exp (((2 * (k : ℝ) + 1) * θ : ℝ) * Complex.I) := by
  refine GaloisForLFunctions.HTGeometry.antitone_oddReciprocal.cauchySeq_series_mul_of_tendsto_zero_of_bounded
    GaloisForLFunctions.HTGeometry.tendsto_oddReciprocal (b := 1 / |Real.sin θ|) fun n => ?_
  exact norm_sum_exp_odd_le hθ n

/-- The odd harmonic exponential series converges: Abel's hypothesis at the boundary point. -/
theorem exists_tendsto_sum_oddHarmonicExp {θ : ℝ} (hθ : Real.sin θ ≠ 0) :
    ∃ L : ℂ, Tendsto (fun N => ∑ k ∈ range N,
        Complex.exp (((2 * (k : ℝ) + 1) * θ : ℝ) * Complex.I) / (2 * (k : ℝ) + 1))
      atTop (𝓝 L) := by
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete (cauchySeq_sum_oddHarmonicExp hθ)
  refine ⟨L, hL.congr fun N => ?_⟩
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.real_smul]
  push_cast
  ring

end RHTower
