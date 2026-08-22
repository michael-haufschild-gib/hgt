import GaloisForLFunctions.HTGeometry.LpDiagonalMultiplier
import GaloisForLFunctions.HTGeometry.SpectralHeatKernel.MinMax

/-!
# The heat semigroup of a spectral datum

The heat flow `e^{−tΔ}` attached to a nonnegative spectrum `λ` and an eigenbasis `(φₙ)` is the
diagonal multiplier `cₙ ↦ e^{−tλₙ} cₙ` read through the coefficient isomorphism of the basis.  Since
the multiplier is bounded by one for `t ≥ 0`, the flow is a contraction, and the multipliers compose,
so the flow is a semigroup.

Proved here: the coefficient formula, contractivity, the semigroup law, and the spectral expression
of the squared norm, which is the quantity whose time derivative drives every Nash-type
ultracontractivity argument.
-/

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The heat multiplier `n ↦ e^{−tλₙ}`. -/
noncomputable def heatMultiplier (lam : ℕ → ℝ) (t : ℝ) : ℕ → ℂ :=
  fun n => (Real.exp (-(t * lam n)) : ℂ)

theorem norm_heatMultiplier_le_one {lam : ℕ → ℝ} {t : ℝ} (ht : 0 ≤ t) (hlam : ∀ n, 0 ≤ lam n)
    (n : ℕ) : ‖heatMultiplier lam t n‖ ≤ 1 := by
  rw [heatMultiplier, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.exp_nonneg _)]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg ht (hlam n)))

/-- **The heat semigroup of a spectral datum.** -/
noncomputable def spectralHeatFlow (b : HilbertBasis ℕ ℂ E) (lam : ℕ → ℝ) {t : ℝ}
    (ht : 0 ≤ t) (hlam : ∀ n, 0 ≤ lam n) (v : E) : E :=
  b.repr.symm (GaloisForLFunctions.lpDiagonalCLM (heatMultiplier lam t) zero_le_one
    (norm_heatMultiplier_le_one ht hlam) (b.repr v))

/-- The coefficients of the heat flow are the damped coefficients. -/
theorem repr_spectralHeatFlow (b : HilbertBasis ℕ ℂ E) (lam : ℕ → ℝ) {t : ℝ}
    (ht : 0 ≤ t) (hlam : ∀ n, 0 ≤ lam n) (v : E) (n : ℕ) :
    b.repr (spectralHeatFlow b lam ht hlam v) n
      = (Real.exp (-(t * lam n)) : ℂ) * b.repr v n := by
  rw [spectralHeatFlow, LinearIsometryEquiv.apply_symm_apply]
  rfl

/-- **The heat flow is a contraction.** -/
theorem norm_spectralHeatFlow_le (b : HilbertBasis ℕ ℂ E) (lam : ℕ → ℝ) {t : ℝ}
    (ht : 0 ≤ t) (hlam : ∀ n, 0 ≤ lam n) (v : E) :
    ‖spectralHeatFlow b lam ht hlam v‖ ≤ ‖v‖ := by
  rw [spectralHeatFlow, LinearIsometryEquiv.norm_map]
  have hop := GaloisForLFunctions.norm_lpDiagonalCLM_le (heatMultiplier lam t) zero_le_one
    (norm_heatMultiplier_le_one ht hlam)
  have hb := (GaloisForLFunctions.lpDiagonalCLM (heatMultiplier lam t) zero_le_one
    (norm_heatMultiplier_le_one ht hlam)).le_opNorm (b.repr v)
  have hrepr : ‖b.repr v‖ = ‖v‖ := b.repr.norm_map v
  calc ‖GaloisForLFunctions.lpDiagonalCLM (heatMultiplier lam t) zero_le_one
        (norm_heatMultiplier_le_one ht hlam) (b.repr v)‖
      ≤ ‖GaloisForLFunctions.lpDiagonalCLM (heatMultiplier lam t) zero_le_one
          (norm_heatMultiplier_le_one ht hlam)‖ * ‖b.repr v‖ := hb
    _ ≤ 1 * ‖b.repr v‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg _)
    _ = ‖v‖ := by rw [one_mul, hrepr]

/-- **The semigroup law.** -/
theorem spectralHeatFlow_add (b : HilbertBasis ℕ ℂ E) (lam : ℕ → ℝ) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : 0 ≤ s + t) (hlam : ∀ n, 0 ≤ lam n) (v : E) :
    spectralHeatFlow b lam hs hlam (spectralHeatFlow b lam ht hlam v)
      = spectralHeatFlow b lam hst hlam v := by
  refine b.repr.injective ?_
  ext n
  rw [repr_spectralHeatFlow, repr_spectralHeatFlow, repr_spectralHeatFlow]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  congr 3
  ring

/-- **The squared norm of the heat flow is the damped spectral sum.** -/
theorem norm_spectralHeatFlow_sq (b : HilbertBasis ℕ ℂ E) (lam : ℕ → ℝ) {t : ℝ}
    (ht : 0 ≤ t) (hlam : ∀ n, 0 ≤ lam n) (v : E) :
    ‖spectralHeatFlow b lam ht hlam v‖ ^ 2
      = ∑' n, Real.exp (-(2 * t * lam n)) * ‖(inner ℂ (b n) v : ℂ)‖ ^ 2 := by
  rw [← tsum_norm_inner_sq b (spectralHeatFlow b lam ht hlam v)]
  refine tsum_congr fun n => ?_
  rw [← HilbertBasis.repr_apply_apply, repr_spectralHeatFlow, HilbertBasis.repr_apply_apply]
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _),
    mul_pow, ← Real.exp_nat_mul]
  congr 2
  push_cast
  ring

end GaloisForLFunctions.HTGeometry
