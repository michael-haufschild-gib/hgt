import GaloisForLFunctions.HTGeometry.StrelitzJetCurveBranchDichotomy
import GaloisForLFunctions.HTGeometry.DigammaFieldValuationRational
import GaloisForLFunctions.HTGeometry.HardyBoundaryScalingRadialPhase
import GaloisForLFunctions.HTGeometry.RootGrowthEngine

/-!
# Phase-sensitive coefficient asymptotics for the Strelitz jet curve

The Wiman first logarithmic jet differs from a positive natural central index by relative error
`1/(n+1)`.  Its normalized complex phase therefore tends to one.  Combining this with the corpus
leading-monomial theorem shows that every fixed coefficient polynomial, divided by the matching
power of the jet norm, converges to its complex leading coefficient.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Filter

/-- Radial phase normalization preserves convergence to the nonzero point `1`. -/
theorem tendsto_phaseNormalize_one_of_tendsto_one
    {α : Type*} {l : Filter α} {z : α → ℂ}
    (hz : Tendsto z l (nhds 1)) :
    Tendsto (fun x => phaseNormalize 1 (z x)) l (nhds 1) := by
  have hzsub : Tendsto (fun x => z x - 1) l (nhds 0) := by
    simpa using hz.sub_const 1
  have hnorm : Tendsto (fun x => ‖z x - 1‖) l (nhds 0) := by
    simpa using hzsub.norm
  have hright : Tendsto (fun x => 2 * ‖z x - 1‖) l (nhds 0) := by
    simpa using (tendsto_const_nhds.mul hnorm :
      Tendsto (fun x => 2 * ‖z x - 1‖) l (nhds (2 * 0)))
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun x => dist_nonneg) ?_ hright
  filter_upwards with x
  rw [Complex.dist_eq]
  exact norm_phaseNormalize_sub_le_finiteSpectralPhaseActionLaw (by norm_num : ‖(1 : ℂ)‖ = 1)

/-- Multiplication by a positive real scalar does not change radial phase. -/
theorem phaseNormalize_div_natCast
    {u : ℂ} {ν : ℕ} (hν : 0 < ν) :
    phaseNormalize 1 (u / (ν : ℂ)) = phaseNormalize 1 u := by
  by_cases hu : u = 0
  · simp [hu, phaseNormalize]
  have hνc : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  unfold phaseNormalize
  rw [if_neg (div_ne_zero hu hνc), if_neg hu,
    norm_div, Complex.norm_natCast]
  have hνr : (0 : ℝ) < (ν : ℝ) := by exact_mod_cast hν
  rw [div_div]
  push_cast
  field_simp

/-- The normalized phase of the first Strelitz jet tends to the positive real phase. -/
theorem tendsto_strelitzRelativePhase_one
    {ν : ℕ → ℕ} {u : ℕ → ℂ} (hνTop : Tendsto ν atTop atTop)
    (hu : ∀ n : ℕ, ‖u n - (ν n : ℂ)‖ ≤
      (1 / ((n : ℝ) + 1)) * (ν n : ℝ)) :
    Tendsto (fun n => phaseNormalize 1 (u n)) atTop (nhds 1) := by
  let E : ℕ → ℝ := fun n => (1 / ((n : ℝ) + 1)) * (ν n : ℝ)
  have hνpos : ∀ᶠ n : ℕ in atTop, 0 < (ν n : ℝ) := by
    have hlarge := hνTop.eventually_ge_atTop 1
    filter_upwards [hlarge] with n hn
    exact_mod_cast hn
  have hE : Tendsto (fun n => E n / (ν n : ℝ)) atTop (nhds 0) := by
    have hbase : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine hbase.congr' ?_
    filter_upwards [hνpos] with n hn
    dsimp [E]
    field_simp
  have hratio : Tendsto (fun n => u n / (ν n : ℂ)) atTop (nhds 1) :=
    tendsto_ratio_one_of_norm_sub_le hνpos
      (Filter.Eventually.of_forall fun n => by simpa [E] using hu n) hE
  have hphase := tendsto_phaseNormalize_one_of_tendsto_one hratio
  refine hphase.congr' ?_
  filter_upwards [hνpos] with n hn
  exact phaseNormalize_div_natCast (u := u n) (by exact_mod_cast hn)

/-- Along the Strelitz relative-error family, a fixed polynomial divided by the corresponding
power of the jet norm converges to its complex leading coefficient. -/
theorem tendsto_polynomial_eval_div_strelitzJetNorm_pow_natDegree
    {ν : ℕ → ℕ} {u : ℕ → ℂ} (hνTop : Tendsto ν atTop atTop)
    (hu : ∀ n : ℕ, ‖u n - (ν n : ℂ)‖ ≤
      (1 / ((n : ℝ) + 1)) * (ν n : ℝ))
    (P : Polynomial ℂ) :
    Tendsto (fun n => P.eval (u n) / ((‖u n‖ : ℂ) ^ P.natDegree))
      atTop (nhds P.leadingCoeff) := by
  have huTop : Tendsto (fun n => ‖u n‖) atTop atTop :=
    tendsto_norm_atTop_of_nat_tendsto_atTop_of_strelitzRelativeError hνTop hu
  have hlead := GaloisForLFunctions.tendsto_eval_div_pow_natDegree_of_norm_atTop huTop P
  have hphase := (tendsto_strelitzRelativePhase_one hνTop hu).pow P.natDegree
  have hprod := hlead.mul hphase
  have hprod' : Tendsto (fun n =>
      (P.eval (u n) / (u n) ^ P.natDegree) *
        (phaseNormalize 1 (u n)) ^ P.natDegree)
      atTop (nhds P.leadingCoeff) := by
    simpa using hprod
  have hu0 : ∀ᶠ n : ℕ in atTop, u n ≠ 0 := by
    filter_upwards [huTop.eventually_gt_atTop 0] with n hn
    exact norm_pos_iff.mp hn
  refine hprod'.congr' ?_
  filter_upwards [hu0] with n hn
  rw [phaseNormalize, if_neg hn, div_pow]
  have hnorm : ((‖u n‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hn)
  field_simp [pow_ne_zero _ hn, pow_ne_zero _ hnorm]

/-- Every coefficient row of the fixed Strelitz jet curve retains its exact complex leading
coefficient after normalization by the matching power of the first jet norm. -/
theorem tendsto_strelitzJetCurveCoefficient_div_norm_pow
    (S : MvPolynomial (Fin 2) ℂ) {ν : ℕ → ℕ} {u : ℕ → ℂ}
    (hνTop : Tendsto ν atTop atTop)
    (hu : ∀ n : ℕ, ‖u n - (ν n : ℂ)‖ ≤
      (1 / ((n : ℝ) + 1)) * (ν n : ℝ)) (k : ℕ) :
    let P := finOnePolynomial ((strelitzJetCurvePolynomial S).coeff k)
    Tendsto (fun n => P.eval (u n) / ((‖u n‖ : ℂ) ^ P.natDegree))
      atTop (nhds P.leadingCoeff) := by
  exact tendsto_polynomial_eval_div_strelitzJetNorm_pow_natDegree hνTop hu _

end

end GaloisForLFunctions.HTGeometry
