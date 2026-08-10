import GaloisForLFunctions.RHTower.GaussQuasiInnerBlocks

/-!
# The quasi-inner block is bounded

Conjugation by a linear isometry does not increase the operator norm, so the two diagonal blocks
are bounded by the sup of their symbol, and

`‖G‖ = ‖p · B D B^(-2) D* B‖ ≤ p² M²`,   `M = gaussSampleValueBound`.

Uniform boundedness of `G` is what lets the errors of the one-step estimate be propagated through
the iterated principal action: the `m`-fold composition multiplies an error by at most `‖G‖^(m-1)`.
-/

namespace RHTower

open MeasureTheory

noncomputable section

/-- Conjugation by a continuous linear equivalence that is an isometry does not increase the
operator norm. -/
theorem norm_conjugateOperator_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℂ K]
    (u : E ≃ₗᵢ[ℂ] K) (T : K →L[ℂ] K) :
    ‖conjugateOperator u.toContinuousLinearEquiv T‖ ≤ ‖T‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg T) fun x => ?_
  have hx : ‖conjugateOperator u.toContinuousLinearEquiv T x‖ = ‖T (u x)‖ := by
    rw [conjugateOperator]
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    exact u.symm.norm_map _
  rw [hx, ← u.norm_map x]
  exact T.le_opNorm _

theorem norm_gaussDiagonalBlock_le {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    ‖gaussDiagonalBlock hm k p‖ ≤ gaussSampleValueBound hm k p :=
  le_trans (norm_conjugateOperator_le _ _)
    (GaloisForLFunctions.norm_lpDiagonalCLM_le _ (gaussSampleValueBound_nonneg hm k p)
      (norm_gaussSampleValue_le hm k p))

theorem norm_gaussDiagonalBlockStar_le {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    ‖gaussDiagonalBlockStar hm k p‖ ≤ gaussSampleValueBound hm k p :=
  le_trans (norm_conjugateOperator_le _ _)
    (GaloisForLFunctions.norm_lpDiagonalCLM_le _ (gaussSampleValueBound_nonneg hm k p)
      (norm_conj_gaussSampleValue_le hm k p))

/-- **The quasi-inner block is bounded.** -/
theorem norm_gaussQuasiInnerG_le {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    ‖gaussQuasiInnerG hm k p‖ ≤
      (p : ℝ) * ((p : ℝ) * (gaussSampleValueBound hm k p * gaussSampleValueBound hm k p)) := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  have hppos : (0 : ℝ) < (p : ℝ) := lt_trans zero_lt_one hp
  have hM := gaussSampleValueBound_nonneg hm k p
  have hsqrt : Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ) = (p : ℝ) :=
    Real.mul_self_sqrt hppos.le
  have hB := norm_gaussPrimeScaleBlock_le hp
  have hI := norm_gaussPrimeScaleInvSqBlock_le hp
  have hD := norm_gaussDiagonalBlock_le hm k p
  have hDs := norm_gaussDiagonalBlockStar_le hm k p
  rw [gaussQuasiInnerG, norm_smul]
  have hscal : ‖((p : ℝ) : ℂ)‖ = (p : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hppos]
  rw [hscal]
  refine mul_le_mul_of_nonneg_left ?_ hppos.le
  have hchain :
      ‖gaussPrimeScaleBlock hp ∘L gaussDiagonalBlock hm k p ∘L
          gaussPrimeScaleInvSqBlock hp ∘L gaussDiagonalBlockStar hm k p ∘L
            gaussPrimeScaleBlock hp‖
        ≤ Real.sqrt (p : ℝ) *
          (gaussSampleValueBound hm k p *
            (1 * (gaussSampleValueBound hm k p * Real.sqrt (p : ℝ)))) := by
    refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
    refine mul_le_mul hB ?_ (norm_nonneg _) (Real.sqrt_nonneg _)
    refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
    refine mul_le_mul hD ?_ (norm_nonneg _) hM
    refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
    refine mul_le_mul hI ?_ (norm_nonneg _) zero_le_one
    refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
    exact mul_le_mul hDs hB (norm_nonneg _) hM
  refine le_trans hchain (le_of_eq ?_)
  rw [one_mul]
  nlinarith [hsqrt, hM]

end

end RHTower
