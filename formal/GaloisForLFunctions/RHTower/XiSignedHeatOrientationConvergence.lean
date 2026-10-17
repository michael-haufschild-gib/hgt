import GaloisForLFunctions.RHTower.XiSignedHeatOrientation
import GaloisForLFunctions.RHTower.XiHurwitzFunctionalEquationEvenWitness

/-!
# Uniform signed-heat construction of the even Hurwitz witness

Symmetric Gaussian time cutoffs converge in operator norm to the Deninger
FE-orientation isometry, with error at most `2 * exp(-N^2)`. Applied to the
canonical odd Hurwitz vector, they give explicit even vectors whose Weil
energies converge to the complete negative Hurwitz energy, without RH.
-/

open Complex Filter
open scoped Topology

namespace RHTower

noncomputable section

theorem norm_xiSignedHeatOrientationLp_le
    (N : ℕ) (v : lp (fun _ : XiZeroCopy => ℂ) 2) :
    ‖xiSignedHeatOrientationLp N v‖ ≤ 2 * ‖v‖ := by
  calc
    _ ≤ ‖(2 : ℝ) • v‖ := lp.norm_mono (by norm_num) (fun q => by
      change ‖xiSignedHeatOrientationWindow N q * v q‖ ≤ ‖(2 : ℝ) • v q‖
      rw [norm_mul, norm_smul]
      norm_num only [Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact mul_le_mul_of_nonneg_right
        (norm_xiSignedHeatOrientationWindow_le N q) (norm_nonneg _))
    _ = _ := by rw [norm_smul]; norm_num

/-- The scalar Gaussian tail estimate lifts uniformly to every Hilbert vector. -/
theorem norm_xiSignedHeatOrientationLp_sub_le
    (N : ℕ) (v : lp (fun _ : XiZeroCopy => ℂ) 2) :
    ‖xiSignedHeatOrientationLp N v - xiFEOrientationLp v‖ ≤
      (2 * Real.exp (-(N : ℝ) ^ 2)) * ‖v‖ := by
  have hb : 0 ≤ 2 * Real.exp (-(N : ℝ) ^ 2) := by positivity
  calc
    _ ≤ ‖(2 * Real.exp (-(N : ℝ) ^ 2) : ℝ) • v‖ :=
      lp.norm_mono (by norm_num) (fun q => by
        change ‖xiSignedHeatOrientationWindow N q * v q -
          deningerArithmeticFEOrientation q * v q‖ ≤
            ‖(2 * Real.exp (-(N : ℝ) ^ 2) : ℝ) • v q‖
        rw [← sub_mul, norm_mul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
        exact mul_le_mul_of_nonneg_right
          (norm_xiSignedHeatOrientationWindow_sub_le N q) (norm_nonneg _))
    _ = _ := by rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]

/-- Bounded complex-linear signed Gaussian cutoff on the complete divisor carrier. -/
def xiSignedHeatOrientationOperator (N : ℕ) :
    lp (fun _ : XiZeroCopy => ℂ) 2 →L[ℂ] lp (fun _ : XiZeroCopy => ℂ) 2 :=
  (show lp (fun _ : XiZeroCopy => ℂ) 2 →ₗ[ℂ]
      lp (fun _ : XiZeroCopy => ℂ) 2 from
    { toFun := xiSignedHeatOrientationLp N
      map_add' := by
        intro v w
        apply Subtype.ext
        funext q
        change xiSignedHeatOrientationWindow N q * (v q + w q) =
          xiSignedHeatOrientationWindow N q * v q +
            xiSignedHeatOrientationWindow N q * w q
        ring
      map_smul' := by
        intro c v
        apply Subtype.ext
        funext q
        change xiSignedHeatOrientationWindow N q * (c * v q) =
          c * (xiSignedHeatOrientationWindow N q * v q)
        ring }).mkContinuous 2 (norm_xiSignedHeatOrientationLp_le N)

@[simp] theorem xiSignedHeatOrientationOperator_apply
    (N : ℕ) (v : lp (fun _ : XiZeroCopy => ℂ) 2) :
    xiSignedHeatOrientationOperator N v = xiSignedHeatOrientationLp N v := rfl

/-- Operator-norm error is independent of the vector and all zero multiplicities. -/
theorem norm_xiSignedHeatOrientationOperator_sub_le (N : ℕ) :
    ‖xiSignedHeatOrientationOperator N -
        xiFEOrientationLinearIsometry.toContinuousLinearMap‖ ≤
      2 * Real.exp (-(N : ℝ) ^ 2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  exact norm_xiSignedHeatOrientationLp_sub_le N v

theorem tendsto_signedGaussianCutoffError :
    Tendsto (fun N : ℕ => 2 * Real.exp (-(N : ℝ) ^ 2)) atTop (𝓝 0) := by
  have hpow : Tendsto (fun N : ℕ => (N : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (show (2 : ℕ) ≠ 0 by norm_num)).comp
      tendsto_natCast_atTop_atTop
  have h := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hpow)
  simpa only [Function.comp_def, mul_zero] using h.const_mul 2

/-- Signed Gaussian time windows converge in operator norm, without spectral reality. -/
theorem tendsto_xiSignedHeatOrientationOperator :
    Tendsto xiSignedHeatOrientationOperator atTop
      (𝓝 xiFEOrientationLinearIsometry.toContinuousLinearMap) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _)
    norm_xiSignedHeatOrientationOperator_sub_le tendsto_signedGaussianCutoffError

/-- In particular the reconstruction converges strongly on the full Hilbert carrier. -/
theorem tendsto_xiSignedHeatOrientationLp (v : lp (fun _ : XiZeroCopy => ℂ) 2) :
    Tendsto (fun N => xiSignedHeatOrientationLp N v) atTop (𝓝 (xiFEOrientationLp v)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero (fun _ => norm_nonneg _)
    (fun N => norm_xiSignedHeatOrientationLp_sub_le N v) ?_
  simpa only [zero_mul] using tendsto_signedGaussianCutoffError.mul_const ‖v‖

/-- Explicit finite-time signed-heat approximation to the canonical even witness. -/
def xiHurwitzSignedHeatVector (N : ℕ) : lp (fun _ : XiZeroCopy => ℂ) 2 :=
  xiSignedHeatOrientationLp N xiHurwitzOrientationVector

theorem xiHurwitzSignedHeatVector_FE_even (N : ℕ) :
    XiFunctionalEquationParity 1 (xiHurwitzSignedHeatVector N) := by
  simpa only [neg_neg, xiHurwitzSignedHeatVector] using
    xiSignedHeatOrientationLp_parity N xiHurwitzOrientationVector_FE_odd

theorem norm_xiHurwitzSignedHeatVector_sub_le (N : ℕ) :
    ‖xiHurwitzSignedHeatVector N - xiHurwitzEvenOrientationVector‖ ≤
      (2 * Real.exp (-(N : ℝ) ^ 2)) * ‖xiHurwitzOrientationVector‖ :=
  norm_xiSignedHeatOrientationLp_sub_le N xiHurwitzOrientationVector

theorem tendsto_xiHurwitzSignedHeatVector :
    Tendsto xiHurwitzSignedHeatVector atTop (𝓝 xiHurwitzEvenOrientationVector) :=
  tendsto_xiSignedHeatOrientationLp xiHurwitzOrientationVector

/-- Finite-time even witnesses recover exactly the full negative Hurwitz energy in the limit. -/
theorem tendsto_xiWeilHilbertQuadratic_signedHeat :
    Tendsto (fun N => xiWeilHilbertQuadratic (xiHurwitzSignedHeatVector N)) atTop
      (𝓝 (-xiHurwitzOrientationEnergy)) := by
  have h := continuous_xiWeilHilbertQuadratic.continuousAt.tendsto.comp
    tendsto_xiHurwitzSignedHeatVector
  rwa [xiWeilHilbertQuadratic_xiHurwitzEvenOrientationVector] at h

/-- Off RH, all sufficiently large signed-heat cutoffs already have negative Weil energy. -/
theorem xiWeilHilbertQuadratic_signedHeat_eventually_neg
    (hRH : ¬RiemannHypothesis) :
    ∀ᶠ N in atTop, xiWeilHilbertQuadratic (xiHurwitzSignedHeatVector N) < 0 := by
  have hE : 0 < xiHurwitzOrientationEnergy := by
    by_contra! h
    apply hRH
    exact riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero.mpr
      (le_antisymm h xiHurwitzOrientationEnergy_nonneg)
  exact tendsto_xiWeilHilbertQuadratic_signedHeat.eventually_lt_const (by linarith)

/-- Eventual Weil nonnegativity on this one explicit even heat sequence is equivalent to RH. -/
theorem riemannHypothesis_iff_signedHeat_eventually_nonnegative :
    RiemannHypothesis ↔
      ∀ᶠ N in atTop, 0 ≤ xiWeilHilbertQuadratic (xiHurwitzSignedHeatVector N) := by
  constructor
  · intro hRH
    exact Eventually.of_forall
      (fun N => xiWeilHilbertQuadratic_nonneg_of_riemannHypothesis hRH
        (xiHurwitzSignedHeatVector N))
  · intro hnonneg
    have hlimit : 0 ≤ -xiHurwitzOrientationEnergy :=
      ge_of_tendsto tendsto_xiWeilHilbertQuadratic_signedHeat hnonneg
    apply riemannHypothesis_iff_xiHurwitzOrientationEnergy_eq_zero.mpr
    linarith [xiHurwitzOrientationEnergy_nonneg]

end

end RHTower
