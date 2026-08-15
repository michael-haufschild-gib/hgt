import GaloisForLFunctions.RHTower.SelbergClass.FunctionalEquationLocal
import GaloisForLFunctions.RHTower.SelbergClass.GammaPoleOrder

/-!
# Critical-line analyticity of concrete Selberg completions

For a concrete Selberg gamma presentation, positivity of every `lambda` and
nonnegativity of every real gamma shift put each gamma argument strictly in the
right half-plane at `s = 1 / 2 + t I`.  Hence no gamma pole meets that line.
Together with the displayed continuation model, this makes the completed value
analytic there.  The codiscrete functional equation can therefore be upgraded
to a pointwise equality on the critical line.

This is a local analyticity statement only; it neither constructs a contour
shift nor supplies meromorphic continuation beyond the existing carrier.
-/

open Complex Filter Set
open scoped BigOperators Topology

namespace RHTower

noncomputable section

/-- The real part of an affine Selberg gamma argument on the critical line. -/
theorem SelbergGammaData.criticalLineArgument_re (G : SelbergGammaData)
    (j : Fin G.rank) (t : ℝ) :
    (((G.lambda j : ℂ) * ((1 / 2 : ℂ) + (t : ℂ) * I) + G.mu j).re) =
      G.lambda j / 2 + (G.mu j).re := by
  simp [Complex.mul_re, div_eq_mul_inv]

/-- Every affine Selberg gamma argument has strictly positive real part on the
critical line. -/
theorem SelbergGammaData.criticalLineArgument_re_pos (G : SelbergGammaData)
    (j : Fin G.rank) (t : ℝ) :
    0 < ((G.lambda j : ℂ) * ((1 / 2 : ℂ) + (t : ℂ) * I) + G.mu j).re := by
  rw [G.criticalLineArgument_re]
  have hhalf : 0 < G.lambda j / 2 := by
    linarith [G.lambda_pos j]
  linarith [G.mu_re_nonneg j]

/-- No affine Selberg gamma argument on the critical line is a nonpositive
integer, hence none is a gamma pole. -/
theorem SelbergGammaData.criticalLineArgument_ne_neg_nat (G : SelbergGammaData)
    (j : Fin G.rank) (t : ℝ) :
    ∀ n : ℕ,
      (G.lambda j : ℂ) * ((1 / 2 : ℂ) + (t : ℂ) * I) + G.mu j ≠ -(n : ℂ) := by
  intro n h
  have hp := G.criticalLineArgument_re_pos j t
  rw [h] at hp
  simp at hp
  exact (not_lt_of_ge (Nat.cast_nonneg n)) hp

/-- Each individual affine gamma factor is analytic at every critical-line
point of a concrete Selberg presentation. -/
theorem SelbergGammaData.analyticAt_gammaAffine_criticalLine (G : SelbergGammaData)
    (j : Fin G.rank) (t : ℝ) :
    AnalyticAt ℂ
      (fun s : ℂ ↦ Gamma ((G.lambda j : ℂ) * s + G.mu j))
      ((1 / 2 : ℂ) + (t : ℂ) * I) := by
  have hnot : ∀ n : ℕ,
      (G.lambda j : ℂ) * ((1 / 2 : ℂ) + (t : ℂ) * I) + G.mu j ≠ -(n : ℂ) :=
    G.criticalLineArgument_ne_neg_nat j t
  have hmer : MeromorphicAt
      (fun s : ℂ ↦ Gamma ((G.lambda j : ℂ) * s + G.mu j))
      ((1 / 2 : ℂ) + (t : ℂ) * I) := by
    simpa only [Function.comp_def] using
      (Meromorphic.Gamma ((G.lambda j : ℂ) * ((1 / 2 : ℂ) + (t : ℂ) * I) + G.mu j)).comp_analyticAt
        (x := ((1 / 2 : ℂ) + (t : ℂ) * I))
        (g := fun s : ℂ ↦ (G.lambda j : ℂ) * s + G.mu j) (by fun_prop)
  have hcont : ContinuousAt
      (fun s : ℂ ↦ Gamma ((G.lambda j : ℂ) * s + G.mu j))
      ((1 / 2 : ℂ) + (t : ℂ) * I) := by
    have hinner : ContinuousAt (fun s : ℂ ↦ (G.lambda j : ℂ) * s + G.mu j)
        ((1 / 2 : ℂ) + (t : ℂ) * I) := by fun_prop
    simpa only [Function.comp_def] using
      ContinuousAt.comp (g := Gamma) (f := fun s : ℂ ↦ (G.lambda j : ℂ) * s + G.mu j)
        (x := ((1 / 2 : ℂ) + (t : ℂ) * I)) (continuousAt_Gamma _ hnot) hinner
  exact hmer.analyticAt hcont

/-- The full concrete Selberg gamma factor is analytic at every critical-line
point. -/
theorem SelbergGammaData.analyticAt_gammaFactor_criticalLine (G : SelbergGammaData)
    (t : ℝ) :
    AnalyticAt ℂ G.gammaFactor ((1 / 2 : ℂ) + (t : ℂ) * I) := by
  rw [SelbergGammaData.gammaFactor]
  apply AnalyticAt.mul
  · have hQdiff : Differentiable ℂ fun s : ℂ ↦ (G.Q : ℂ) ^ s :=
      differentiable_id.const_cpow (.inl (ofReal_ne_zero.mpr G.Q_pos.ne'))
    have hQanalytic : AnalyticOnNhd ℂ (fun s : ℂ ↦ (G.Q : ℂ) ^ s) univ :=
      analyticOnNhd_univ_iff_differentiable.mpr hQdiff
    exact hQanalytic _ (mem_univ _)
  · exact Finset.univ.analyticAt_prod fun j _ ↦ G.analyticAt_gammaAffine_criticalLine j t

/-- The critical line avoids the sole displayed singularity of the represented
continuation. -/
theorem criticalLinePoint_ne_one (t : ℝ) :
    ((1 / 2 : ℂ) + (t : ℂ) * I) ≠ 1 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [Complex.add_re, Complex.mul_re] at hre

/-- The completed value attached to concrete Selberg data is analytic at every
critical-line point. -/
theorem analyticAt_selbergCompletedValue_criticalLine
    (G : SelbergGammaData) (A : SelbergAnalyticContinuation) (t : ℝ) :
    AnalyticAt ℂ (selbergCompletedValue G A) ((1 / 2 : ℂ) + (t : ℂ) * I) := by
  unfold selbergCompletedValue
  exact (G.analyticAt_gammaFactor_criticalLine t).mul
    (A.analyticAt_value_of_ne_one (criticalLinePoint_ne_one t))

/-- The Selberg conjugate reflection fixes every point of the critical line. -/
theorem criticalLinePoint_reflection (t : ℝ) :
    1 - star ((1 / 2 : ℂ) + (t : ℂ) * I) = (1 / 2 : ℂ) + (t : ℂ) * I := by
  norm_num [Complex.ext_iff]

/-- The completed Selberg functional equation holds as an exact pointwise
equality on the entire critical line. -/
theorem ExtendedSelbergClass.completedFE_eq_criticalLine
    (F : ExtendedSelbergClass) (t : ℝ) :
    selbergCompletedValue F.gammaData F.continuation ((1 / 2 : ℂ) + (t : ℂ) * I) =
      F.gammaData.rootNumber *
        selbergConjugateReflection (selbergCompletedValue F.gammaData F.continuation)
          ((1 / 2 : ℂ) + (t : ℂ) * I) := by
  apply F.completedFE_eq_of_analytic_pair
  · exact analyticAt_selbergCompletedValue_criticalLine F.gammaData F.continuation t
  · rw [criticalLinePoint_reflection]
    exact analyticAt_selbergCompletedValue_criticalLine F.gammaData F.continuation t

end

end RHTower
