/-
# Rescaling a kernel rescales the spectral variable

The regularized determinant of `cK` at `z` is the regularized determinant of `K` at `cz`.  This is
visible in the defining exponent: the `n`-th term of `∑_{n≥2} zⁿ tr(Kⁿ)/n` picks up exactly `cⁿ`
when `K` is scaled by `c`, so the exponent is a function of the product `cz` alone.  Uniqueness of
the entire representative then transports the identity from the disc to the whole plane.

This is what makes a *linear pencil* of kernels accessible to the one-variable theory: restricting
a pencil to a line through the origin turns the pencil parameter into the spectral variable.

Main results:
* `HilbertSchmidt.hsNorm_smul`, `HilbertSchmidt.hsPow_smul` — the Hilbert--Schmidt scaling laws.
* `HilbertSchmidt.fredholmExp_smul`, `HilbertSchmidt.fredholmDet_smul` — the disc-local identity.
* `entireDet2_smul` — the identity for the entire representative.
-/
import GaloisForLFunctions.HTGeometry.RegularizedDeterminantTraceRecovery

open Metric

namespace HilbertSchmidt

variable {ι : Type*}

theorem hsNormSq_kernel_smul (c : ℂ) (K : ι × ι → ℂ) :
    hsNormSq (c • K) = ‖c‖ ^ (2 : ℕ) * hsNormSq K := by
  rw [hsNormSq, hsNormSq, ← tsum_mul_left]
  refine tsum_congr fun p => ?_
  rw [Pi.smul_apply, norm_smul, mul_pow]

theorem hsNorm_smul (c : ℂ) (K : ι × ι → ℂ) : hsNorm (c • K) = ‖c‖ * hsNorm K := by
  rw [hsNorm, hsNorm, hsNormSq_kernel_smul, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (norm_nonneg c)]

theorem hsComp_smul_left (c : ℂ) (K L : ι × ι → ℂ) : hsComp (c • K) L = c • hsComp K L := by
  funext p
  rw [hsComp, Pi.smul_apply, hsComp, smul_eq_mul, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem hsComp_smul_right (c : ℂ) (K L : ι × ι → ℂ) : hsComp K (c • L) = c • hsComp K L := by
  funext p
  rw [hsComp, Pi.smul_apply, hsComp, smul_eq_mul, ← tsum_mul_left]
  refine tsum_congr fun k => ?_
  rw [Pi.smul_apply, smul_eq_mul]
  ring

theorem hsPow_smul (c : ℂ) (K : ι × ι → ℂ) :
    ∀ n : ℕ, hsPow (c • K) n = c ^ (n + 1) • hsPow K n
  | 0 => by simp [hsPow]
  | (n + 1) => by
      rw [hsPow, hsPow_smul c K n, hsComp_smul_right, hsComp_smul_left, hsPow, smul_smul]
      congr 1

theorem hsTrace_hsPow_smul (c : ℂ) (K : ι × ι → ℂ) (n : ℕ) :
    (∑' i, hsPow (c • K) n (i, i)) = c ^ (n + 1) * ∑' i, hsPow K n (i, i) := by
  rw [hsPow_smul, ← tsum_mul_left]
  exact tsum_congr fun i => by rw [Pi.smul_apply, smul_eq_mul]

/-- **Rescaling the kernel rescales the spectral variable**, at the level of the exponent. -/
theorem fredholmExp_smul (K : ι × ι → ℂ) (c z : ℂ) :
    fredholmExp (c • K) z = fredholmExp K (c * z) := by
  rw [fredholmExp, fredholmExp]
  refine tsum_congr fun n => ?_
  rw [hsTrace_hsPow_smul, mul_pow]
  ring

theorem fredholmDet_smul (K : ι × ι → ℂ) (c z : ℂ) :
    fredholmDet (c • K) z = fredholmDet K (c * z) := by
  rw [fredholmDet, fredholmDet, fredholmExp_smul]

end HilbertSchmidt

namespace GaloisForLFunctions.HTGeometry

open HilbertSchmidt

variable {ι : Type*} [DecidableEq ι]

/-- **The entire regularized determinant of a rescaled kernel** is the determinant of the original
kernel at the rescaled spectral coordinate. -/
theorem entireDet2_smul {K : ι × ι → ℂ} (hK : IsHS K) (c : ℂ) :
    entireDet2 (c • K) = fun z => entireDet2 K (c * z) := by
  obtain ⟨hdiff, r₁, hr₁, -, he₁⟩ := isRegularizedDet_entireDet2 hK
  refine (isRegularizedDet_entireDet2 (hK.smul c)).unique ?_
  have hcpos : (0 : ℝ) < ‖c‖ + 1 := by positivity
  set r : ℝ := min (r₁ / (‖c‖ + 1)) (detRadius (c • K)) with hr
  have hrpos : 0 < r := lt_min (by positivity) (detRadius_pos _)
  refine ⟨hdiff.comp (differentiable_id.const_mul c), r, hrpos, ?_, fun z hz => ?_⟩
  · calc r * hsNorm (c • K) ≤ detRadius (c • K) * hsNorm (c • K) :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) (hsNorm_nonneg _)
      _ < 1 := detRadius_mul_hsNorm_lt _
  · have hzr : ‖z‖ < r₁ / (‖c‖ + 1) :=
      lt_of_lt_of_le (by rwa [mem_ball_zero_iff] at hz) (min_le_left _ _)
    have hcz : ‖c * z‖ < r₁ := by
      rw [norm_mul]
      have h1 : ‖c‖ * ‖z‖ ≤ ‖c‖ * (r₁ / (‖c‖ + 1)) :=
        mul_le_mul_of_nonneg_left hzr.le (norm_nonneg c)
      have h2 : ‖c‖ * (r₁ / (‖c‖ + 1)) < r₁ := by
        rw [mul_div_assoc', div_lt_iff₀ hcpos]
        nlinarith [hr₁, norm_nonneg c]
      linarith
    show entireDet2 K (c * z) = fredholmDet (c • K) z
    rw [he₁ (c * z) (by rwa [mem_ball_zero_iff]), fredholmDet_smul]

end GaloisForLFunctions.HTGeometry
