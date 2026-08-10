import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Diagonal multipliers on `ℓ²` over an arbitrary index

Multiplication by a bounded family is a bounded operator on `ℓ²(ι)` of norm at most the bound.
The corpus already has this for `ι = ℕ` (`RHTower.diagonalOperator`); the Fourier side of the
circle is indexed by `ℤ`, so the same construction is recorded here for an arbitrary index type.

The proof is the pointwise estimate `‖λ_i f_i‖ ≤ C ‖f_i‖` summed through the `ℓ²` norm.
-/

open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions

variable {ι : Type*}

/-- Multiplying a square-summable family by a bounded family keeps it square summable. -/
theorem memLp_lpDiagonal {lam : ι → ℂ} {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i, ‖lam i‖ ≤ C)
    (f : lp (fun _ : ι => ℂ) 2) : Memℓp (fun i => lam i * f i) 2 := by
  refine memℓp_gen ?_
  have hsum : Summable fun i => ‖f i‖ ^ (2 : ℝ) := (lp.memℓp f).summable (by norm_num)
  have hCnn : (0 : ℝ) ≤ C := hC0
  refine Summable.of_nonneg_of_le (fun i => Real.rpow_nonneg (norm_nonneg _) 2) ?_
    (hsum.mul_left (C ^ (2 : ℝ)))
  intro i
  rw [norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow (norm_nonneg _) (hC i) (by norm_num))
    (Real.rpow_nonneg (norm_nonneg _) 2)

/-- Diagonal multiplication by a bounded family, as a linear map. -/
def lpDiagonalLM (lam : ι → ℂ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i, ‖lam i‖ ≤ C) :
    lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2 where
  toFun f := ⟨fun i => lam i * f i, memLp_lpDiagonal hC0 hC f⟩
  map_add' := by
    intro f g
    ext i
    simp [mul_add]
  map_smul' := by
    intro c f
    ext i
    simp [mul_left_comm]

@[simp] theorem lpDiagonalLM_apply (lam : ι → ℂ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i, ‖lam i‖ ≤ C)
    (f : lp (fun _ : ι => ℂ) 2) (i : ι) :
    (lpDiagonalLM lam hC0 hC f : ι → ℂ) i = lam i * f i := rfl

/-- The diagonal map is bounded by the multiplier bound. -/
theorem norm_lpDiagonalLM_le (lam : ι → ℂ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i, ‖lam i‖ ≤ C)
    (f : lp (fun _ : ι => ℂ) 2) :
    ‖lpDiagonalLM lam hC0 hC f‖ ≤ C * ‖f‖ := by
  have hCnn : (0 : ℝ) ≤ C := hC0
  have hnn : (0 : ℝ) ≤ ‖lpDiagonalLM lam hC0 hC f‖ := norm_nonneg _
  have hrhs : (0 : ℝ) ≤ C * ‖f‖ := mul_nonneg hCnn (norm_nonneg _)
  have htsumD : ‖lpDiagonalLM lam hC0 hC f‖ ^ (2 : ℝ)
      = ∑' i, ‖(lpDiagonalLM lam hC0 hC f) i‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ι => ℂ) (by norm_num)
      (lpDiagonalLM lam hC0 hC f)
  have htsumf : ‖f‖ ^ (2 : ℝ) = ∑' i, ‖f i‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := fun _ : ι => ℂ) (by norm_num) f
  have hsumf : Summable fun i => ‖f i‖ ^ (2 : ℝ) := (lp.memℓp f).summable (by norm_num)
  have hsumD : Summable fun i => ‖(lpDiagonalLM lam hC0 hC f) i‖ ^ (2 : ℝ) :=
    (lp.memℓp _).summable (by norm_num)
  have hterm : ∀ i, ‖(lpDiagonalLM lam hC0 hC f) i‖ ^ (2 : ℝ)
      ≤ C ^ (2 : ℝ) * ‖f i‖ ^ (2 : ℝ) := by
    intro i
    rw [lpDiagonalLM_apply, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (norm_nonneg _) (hC i) (by norm_num))
      (Real.rpow_nonneg (norm_nonneg _) 2)
  have hpow : ‖lpDiagonalLM lam hC0 hC f‖ ^ (2 : ℝ) ≤ (C * ‖f‖) ^ (2 : ℝ) := by
    rw [htsumD, Real.mul_rpow hCnn (norm_nonneg _), htsumf, ← tsum_mul_left]
    exact Summable.tsum_le_tsum hterm hsumD (hsumf.mul_left (C ^ (2 : ℝ)))
  have hx2 : ‖lpDiagonalLM lam hC0 hC f‖ ^ (2 : ℝ) = ‖lpDiagonalLM lam hC0 hC f‖ ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  have hy2 : (C * ‖f‖) ^ (2 : ℝ) = (C * ‖f‖) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  rw [hx2, hy2] at hpow
  have hs := Real.sqrt_le_sqrt hpow
  rwa [Real.sqrt_sq hnn, Real.sqrt_sq hrhs] at hs

/-- Diagonal multiplication by a bounded family, as a bounded operator on `ℓ²(ι)`. -/
def lpDiagonalCLM (lam : ι → ℂ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i, ‖lam i‖ ≤ C) :
    lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 :=
  LinearMap.mkContinuous (lpDiagonalLM lam hC0 hC) C (norm_lpDiagonalLM_le lam hC0 hC)

@[simp] theorem lpDiagonalCLM_apply (lam : ι → ℂ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i, ‖lam i‖ ≤ C)
    (f : lp (fun _ : ι => ℂ) 2) (i : ι) :
    (lpDiagonalCLM lam hC0 hC f) i = lam i * f i := rfl

theorem norm_lpDiagonalCLM_le (lam : ι → ℂ) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ i, ‖lam i‖ ≤ C) :
    ‖lpDiagonalCLM lam hC0 hC‖ ≤ C :=
  LinearMap.mkContinuous_norm_le _ hC0 _

/-- The diagonal operator acts on a coordinate vector by its multiplier. -/
@[simp] theorem lpDiagonalCLM_single [DecidableEq ι] (lam : ι → ℂ) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ i, ‖lam i‖ ≤ C) (j : ι) :
    lpDiagonalCLM lam hC0 hC (lp.single 2 j (1 : ℂ)) = lp.single 2 j (lam j) := by
  ext i
  rw [lpDiagonalCLM_apply]
  simp only [lp.single_apply, Pi.single_apply]
  split_ifs with h
  · subst h
    rw [mul_one]
  · rw [mul_zero]

end GaloisForLFunctions

end
