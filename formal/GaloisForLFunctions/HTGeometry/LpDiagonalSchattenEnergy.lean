import GaloisForLFunctions.HTGeometry.WeightedOrbitInductionSchatten
import GaloisForLFunctions.HTGeometry.LpDiagonalMultiplier

/-! # Exact Schatten energy of scalar diagonal multipliers

Specialize the block-diagonal singular-value law to one-dimensional complex
blocks. The extended energy identity includes divergent coefficient families.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open RHTower
open scoped ENNReal

theorem rectApproxNumber_complex_scalar (c : ℂ) (n : ℕ) :
    rectApproxNumber (c • ContinuousLinearMap.id ℂ ℂ) n =
      if n = 0 then ‖c‖ else 0 := by
  split_ifs with hn
  · subst n
    rw [rectApproxNumber_zero_eq_norm, norm_smul, ContinuousLinearMap.norm_id, mul_one]
  · have hr : HasRectRankLE (c • ContinuousLinearMap.id ℂ ℂ) n :=
      ⟨⊤, inferInstance, by simpa using Nat.one_le_iff_ne_zero.mpr hn,
        fun _ => Submodule.mem_top⟩
    have hz := rectApproxNumber_le (c • ContinuousLinearMap.id ℂ ℂ) n _ hr
    exact le_antisymm (by simpa using hz) (rectApproxNumber_nonneg _ _)

variable {ι : Type} [Countable ι]

theorem tsum_ofReal_rpow_approxNumber_lpDiagonalCLM (a : ι → ℂ)
    {C : ℝ} (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C) {p : ℝ} (hp : 0 < p) :
    (∑' n, ENNReal.ofReal (approxNumber (lpDiagonalCLM a hC ha) n ^ p)) =
      ∑' i, ENNReal.ofReal (‖a i‖ ^ p) := by
  have hb (i : ι) : ‖a i • ContinuousLinearMap.id ℂ ℂ‖ ≤ C := by
    simpa only [norm_smul, ContinuousLinearMap.norm_id, mul_one] using ha i
  have he : rectangularBlockOperator (fun i => a i • ContinuousLinearMap.id ℂ ℂ) hC hb =
      lpDiagonalCLM a hC ha := by
    ext x i
    rfl
  have h := tsum_ofReal_rpow_rectApproxNumber_rectangularBlockOperator
    (fun i => a i • ContinuousLinearMap.id ℂ ℂ) hC hb
    (fun i => isCompactOperator_of_locallyCompactSpace_rng _) hp
  rw [he] at h
  refine h.trans (tsum_congr fun i => ?_)
  rw [tsum_eq_single 0]
  · simp only [rectApproxNumber_complex_scalar, ↓reduceIte]
  · intro n hn
    simp only [rectApproxNumber_complex_scalar, if_neg hn, Real.zero_rpow hp.ne',
      ENNReal.ofReal_zero]

theorem memSchattenClass_lpDiagonalCLM_iff (a : ι → ℂ)
    {C : ℝ} (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C) {p : ℝ} (hp : 0 < p) :
    MemSchattenClass p (lpDiagonalCLM a hC ha) ↔ Summable (fun i => ‖a i‖ ^ p) := by
  rw [MemSchattenClass,
    summable_iff_tsum_ofReal_ne_top (fun n => Real.rpow_nonneg (approxNumber_nonneg _ n) p),
    tsum_ofReal_rpow_approxNumber_lpDiagonalCLM a hC ha hp,
    summable_iff_tsum_ofReal_ne_top (fun i => Real.rpow_nonneg (norm_nonneg _) p)]

theorem tsum_rpow_approxNumber_lpDiagonalCLM (a : ι → ℂ)
    {C : ℝ} (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C) {p : ℝ} (hp : 0 < p) :
    (∑' n, approxNumber (lpDiagonalCLM a hC ha) n ^ p) = ∑' i, ‖a i‖ ^ p := by
  have h := congrArg ENNReal.toReal
    (tsum_ofReal_rpow_approxNumber_lpDiagonalCLM a hC ha hp)
  simpa only [tsum_toReal_ofReal_eq
    (fun n => Real.rpow_nonneg (approxNumber_nonneg _ n) p),
    tsum_toReal_ofReal_eq (fun i => Real.rpow_nonneg (norm_nonneg (a i)) p)] using h

theorem traceNorm_lpDiagonalCLM (a : ι → ℂ)
    {C : ℝ} (hC : 0 ≤ C) (ha : ∀ i, ‖a i‖ ≤ C) :
    traceNorm (lp (fun _ : ι => ℂ) 2) (lpDiagonalCLM a hC ha) = ∑' i, ‖a i‖ := by
  simpa only [traceNorm, Real.rpow_one] using
    tsum_rpow_approxNumber_lpDiagonalCLM a hC ha (p := 1) zero_lt_one

end
end GaloisForLFunctions.HTGeometry
