import GaloisForLFunctions.RHTower.SmoothAFEGaussianPrefixIntegral
import GaloisForLFunctions.RHTower.SmoothAFEGaussianPrefixLimit
import GaloisForLFunctions.RHTower.SteinhausCofactorRealScale
import GaloisForLFunctions.RHTower.SmoothAFETruncation


open MeasureTheory Filter Topology Finset
noncomputable section
namespace RHTower

private theorem norm_cutoff_eq_re {x : ℝ} (hx : 0 < x) :
    ‖smoothAFECutoff x‖ = (smoothAFECutoff x).re := by
  have h : ((smoothAFECutoff x).re : ℂ) = smoothAFECutoff x :=
    Complex.ext rfl (smoothAFECutoff_im_eq_zero hx).symm
  calc
    _ = ‖((smoothAFECutoff x).re : ℂ)‖ := congrArg norm h.symm
    _ = _ := Complex.norm_of_nonneg (smoothAFECutoff_re_nonneg hx)

private theorem summable_cofactor_cutoff_norm (ω : SteinhausModel.Omega)
    {s : ℂ} (hs : s.re < 1) {R : ℝ} (hR : 0 < R) :
    Summable (fun n : ℕ => ‖SteinhausModel.X (n + 1) ω *
      ((n + 1 : ℕ) : ℂ) ^ (s - 1)‖ *
        (smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R)).re) := by
  have h := (summable_smoothAFE_direct (A := 2) (s := 1 - s)
    (by norm_num) hR (by simp only [Complex.sub_re, Complex.one_re]; linarith)).norm
  apply h.congr
  intro n
  rw [norm_mul, show -(1 - s) = s - 1 by ring,
    norm_cutoff_eq_re (by positivity), norm_mul, SteinhausModel.norm_X, one_mul]

private theorem range_succ_sum (b : ℕ → ℂ) (N : ℕ) :
    (∑ n ∈ range N, b (n + 1)) = ∑ n ∈ Icc 1 N, b n := by
  rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel_right]
  apply sum_congr rfl
  intro n _
  rw [Nat.add_comm]

/-- The complete Gaussian-smoothed arithmetic cofactor is exactly a Gaussian average of its
literal sharp partial sums. No reflected tail has been discarded. -/
theorem tsum_finitePrimeTwistExtension_gaussian_eq_prefix_integral
    (S : Finset ℕ) (ω : SteinhausModel.Omega) (t : ℝ)
    {s : ℂ} (hs : s.re < 1) {R : ℝ} (hR : 0 < R) :
    (∑' n : ℕ, SteinhausModel.X (n + 1) (finitePrimeTwistExtension S ω t) *
      ((n + 1 : ℕ) : ℂ) ^ (s - 1) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R)) =
      ∫ y : ℝ, (smoothAFELogGaussian y : ℂ) *
        ∑ n ∈ Icc 1 ⌊R * Real.exp y⌋₊,
          SteinhausModel.X n (finitePrimeTwistExtension S ω t) * (n : ℂ) ^ (s - 1) := by
  rw [tsum_smoothAFECutoff_eq_logGaussian_prefix_integral _ hR
    (summable_cofactor_cutoff_norm _ hs hR)]
  apply integral_congr_ae
  filter_upwards with y
  congr 1
  exact range_succ_sum (fun n =>
    SteinhausModel.X n (finitePrimeTwistExtension S ω t) * (n : ℂ) ^ (s - 1)) _

/-- The actual full Gaussian cofactor realizes the Gaussian Mellin mode exp(z²)/z.
Its finite-prime prefix contributes the same explicit scalar at every node. -/
theorem tendsto_finitePrimeTwistExtension_gaussian_mean
    (S : Finset ℕ) (ω : SteinhausModel.Omega) (t : ℝ)
    {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1) :
    Tendsto (fun R : ℝ =>
      (∑' n : ℕ, SteinhausModel.X (n + 1) (finitePrimeTwistExtension S ω t) *
        ((n + 1 : ℕ) : ℂ) ^ (s - 1) * smoothAFECutoff (((n + 1 : ℕ) : ℝ) / R)) *
        (R : ℂ) ^ (-(s + (t : ℂ) * Complex.I))) atTop
      (𝓝 (finitePrimePhaseMean S (fun p => ω p - t * Real.log p / (2 * Real.pi)) *
        (Complex.exp ((s + (t : ℂ) * Complex.I) ^ 2) / (s + (t : ℂ) * Complex.I)))) := by
  let P : ℕ → ℂ := fun N => ∑ n ∈ Icc 1 N,
    SteinhausModel.X n (finitePrimeTwistExtension S ω t) * (n : ℂ) ^ (s - 1)
  let z : ℂ := s + (t : ℂ) * Complex.I
  let A : ℂ := finitePrimePhaseMean S (fun p => ω p - t * Real.log p / (2 * Real.pi))
  obtain ⟨C, _hC, hbound⟩ :=
    exists_norm_finitePrimeTwistExtension_weighted_prefix_real_le S ω t (s := s) hs hs1
  have hz : z.re = s.re := by simp [z]
  have h := tendsto_logGaussian_prefix_integral P z (A / z)
    (tendsto_finitePrimeTwistExtension_weighted_mean_realScale S ω t (s := s) hs hs1)
    (by simpa only [hz, P] using hbound)
  have hscalar : (A / z) * Complex.exp (z ^ 2) = A * (Complex.exp (z ^ 2) / z) := by ring
  rw [hscalar] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
  rw [tsum_finitePrimeTwistExtension_gaussian_eq_prefix_integral S ω t hs1 hR]

end RHTower
