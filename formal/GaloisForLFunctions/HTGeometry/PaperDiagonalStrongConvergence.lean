import GaloisForLFunctions.HTGeometry.LpDiagonalMultiplier
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Strong convergence of uniformly bounded diagonal histories

Pointwise convergence of bounded coefficients passes to every full square-summable vector.
The proof retains the entire coordinate sum through dominated convergence, including vectors
with infinite support.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section
open Filter
open scoped Topology

/-- A uniformly bounded, pointwise convergent family of diagonals converges strongly on `ℓ²`. -/
theorem paperLpDiagonal_strong_tendsto {ι : Type*}
    (a : ℕ → ι → ℂ) (b : ι → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ n i, ‖a n i‖ ≤ C) (hb : ∀ i, ‖b i‖ ≤ C)
    (hlim : ∀ i, Tendsto (fun n => a n i) atTop (𝓝 (b i)))
    (v : lp (fun _ : ι => ℂ) 2) :
    Tendsto (fun n => lpDiagonalCLM (a n) hC (ha n) v) atTop
      (𝓝 (lpDiagonalCLM b hC hb v)) := by
  have hs : Summable (fun i => ‖v i‖^2) := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (lp.hasSum_norm (by norm_num : 0 < (2 : ENNReal).toReal) v).summable
  have ht (i : ι) : Tendsto (fun n => ‖(a n i - b i) * v i‖^2) atTop (𝓝 0) := by
    have h := ((hlim i).sub (tendsto_const_nhds (x := b i))).mul
      (tendsto_const_nhds (x := v i))
    simpa only [sub_self, zero_mul, norm_zero, zero_pow (by norm_num : 2 ≠ 0)] using
      h.norm.pow 2
  have hbound (n : ℕ) (i : ι) :
      ‖‖(a n i - b i) * v i‖^2‖ ≤ (2*C)^2 * ‖v i‖^2 := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hn : ‖a n i - b i‖ ≤ 2*C :=
      (norm_sub_le _ _).trans (by linarith [ha n i, hb i])
    rw [norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (by nlinarith [norm_nonneg (a n i - b i)])
      (sq_nonneg _)
  have htSum := tendsto_tsum_of_dominated_convergence (hs.mul_left ((2*C)^2)) ht
    (Eventually.of_forall hbound)
  have heq (n : ℕ) :
      ‖lpDiagonalCLM (a n) hC (ha n) v - lpDiagonalCLM b hC hb v‖^2 =
        ∑' i, ‖(a n i - b i) * v i‖^2 := by
    have h := lp.norm_rpow_eq_tsum (by norm_num : 0 < (2 : ENNReal).toReal)
      (lpDiagonalCLM (a n) hC (ha n) v - lpDiagonalCLM b hC hb v)
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two, lp.coeFn_sub, Pi.sub_apply,
      lpDiagonalCLM_apply, sub_mul] using h
  have hsq : Tendsto (fun n =>
      ‖lpDiagonalCLM (a n) hC (ha n) v - lpDiagonalCLM b hC hb v‖^2) atTop (𝓝 0) := by
    simpa only [heq, tsum_zero] using htSum
  have hnorm := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hnorm

end
end GaloisForLFunctions.HTGeometry
