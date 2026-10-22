import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectBinaryGrowthCooling
/-!
# Literal dominant pair growth decreases relative to the dominant atom

The tilted atom moments obey the integral derivative chain. The previously
proved full-pair cooling inequality therefore gives strict decrease of the
actual pair-to-atom growth ratio on q >= 3/2. No complete-source signed
sector comparison is assumed or asserted here.
-/

namespace RHTower.ThetaCuspDefect
open MeasureTheory Set Filter
noncomputable section

private theorem integrable_atomMoment {n : ℕ} (hn : 2 ≤ n) (m : ℕ) {B : ℝ} (hB : 0 < B) :
    Integrable (fun t : ℝ => t^m*Real.exp (-B*t)) (thetaCuspAtomLikelihoodSpectralMeasure n) := by
  have he : n-2+2=n := Nat.sub_add_cancel hn
  have hle : thetaCuspAtomLikelihoodSpectralMeasure n ≤ thetaCuspHigherLikelihoodSpectralMeasure := by
    simpa only [he,thetaCuspHigherLikelihoodSpectralMeasure] using
      Measure.le_sum (fun k : ℕ => thetaCuspAtomLikelihoodSpectralMeasure (k+2)) (n-2)
  exact (integrable_pow_mul_exp_neg_thetaCuspHigherLikelihoodSpectralMeasure m hB).mono_measure hle

theorem hasDerivAt_atomMoment {n : ℕ} (hn : 2 ≤ n) (m : ℕ) {B : ℝ} (hB : 0 < B) :
    HasDerivAt (fun q => atomMoment n q m) (-atomMoment n B (m+1)) B := by
  let s : Set ℝ := Metric.ball B (B / 2)
  let bound : ℝ → ℝ := fun t =>
    t ^ (m + 1) * Real.exp (-(B / 2) * t)
  have hs : s ∈ nhds B := Metric.ball_mem_nhds B (half_pos hB)
  have hpositive : ∀ z ∈ s, B / 2 < z := by
    intro z hz
    have habs : |z - B| < B / 2 := by
      simpa [s, Real.dist_eq] using hz
    have hneg : -(B / 2) < z - B := neg_lt_of_abs_lt habs
    linarith
  have hFmeas : ∀ᶠ z in nhds B,
      AEStronglyMeasurable
        (fun t : ℝ => t ^ m * Real.exp (-z * t))
        (thetaCuspAtomLikelihoodSpectralMeasure n) := by
    filter_upwards with z
    exact (by fun_prop : Continuous
      (fun t : ℝ => t ^ m * Real.exp (-z * t))).aestronglyMeasurable
  have hF'meas :
      AEStronglyMeasurable
        (fun t : ℝ => -(t ^ (m + 1)) * Real.exp (-B * t))
        (thetaCuspAtomLikelihoodSpectralMeasure n) :=
    (by fun_prop : Continuous
      (fun t : ℝ => -(t ^ (m + 1)) * Real.exp (-B * t))).aestronglyMeasurable
  have hboundInt : Integrable bound (thetaCuspAtomLikelihoodSpectralMeasure n) := by
    simpa [bound] using
      integrable_atomMoment hn
        (m + 1) (half_pos hB)
  have hdom : ∀ᵐ t ∂(thetaCuspAtomLikelihoodSpectralMeasure n),
      ∀ z ∈ s,
        ‖-(t ^ (m + 1)) * Real.exp (-z * t)‖ ≤ bound t := by
    filter_upwards
      [ae_nonneg_thetaCuspAtomLikelihoodSpectralMeasure hn] with t ht
    intro z hz
    have hzLower := hpositive z hz
    have hexp : Real.exp (-z * t) ≤ Real.exp (-(B / 2) * t) := by
      apply Real.exp_le_exp.mpr
      nlinarith
    rw [Real.norm_eq_abs, abs_mul, abs_neg,
      abs_of_nonneg (pow_nonneg ht _), abs_of_pos (Real.exp_pos _)]
    dsimp [bound]
    exact mul_le_mul_of_nonneg_left hexp (pow_nonneg ht _)
  have hdiff : ∀ᵐ t ∂(thetaCuspAtomLikelihoodSpectralMeasure n),
      ∀ z ∈ s,
        HasDerivAt (fun q : ℝ => t ^ m * Real.exp (-q * t))
          (-(t ^ (m + 1)) * Real.exp (-z * t)) z := by
    filter_upwards with t z hz
    have hinner : HasDerivAt (fun q : ℝ => -q * t) (-t) z := by
      simpa using (hasDerivAt_id z).neg.mul_const t
    have hexp : HasDerivAt (fun q : ℝ => Real.exp (-q * t))
        (-t * Real.exp (-z * t)) z := by
      simpa [Function.comp_def, mul_comm] using
        (Real.hasDerivAt_exp (-z * t)).comp z hinner
    have hmul := (hasDerivAt_const z (t ^ m)).mul hexp
    exact hmul.congr_deriv (by rw [pow_succ]; ring)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (thetaCuspAtomLikelihoodSpectralMeasure n))
    (F := fun z t : ℝ => t ^ m * Real.exp (-z * t))
    (F' := fun z t : ℝ => -(t ^ (m + 1)) * Real.exp (-z * t))
    (bound := bound) hs hFmeas
    (integrable_atomMoment hn m hB)
    hF'meas hdom hboundInt hdiff

  have ht : HasDerivAt
      (fun q => ∫ t : ℝ, t^m*Real.exp (-q*t) ∂thetaCuspAtomLikelihoodSpectralMeasure n)
      (-atomMoment n B (m+1)) B := hmain.2.congr_deriv (by
    simp only [atomMoment,neg_mul]
    rw [← integral_neg])
  simpa only [atomMoment,neg_mul] using ht

theorem hasDerivAt_atomMomentConvolution {n : ℕ} (hn : 2 ≤ n) (j : ℕ)
    {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun r => momentConvolution (atomMoment n r) (atomMoment n r) j)
      (-momentConvolution (fun i => atomMoment n q (i+1)) (atomMoment n q) j-
       momentConvolution (atomMoment n q) (fun i => atomMoment n q (i+1)) j) q := by
  have hs := HasDerivAt.fun_sum (u := Finset.range (j+1)) (fun i _ =>
    ((hasDerivAt_atomMoment hn i hq).mul (hasDerivAt_atomMoment hn (j-i) hq)).const_mul (j.choose i:ℝ))
  convert! hs using 1
  · funext r
    unfold momentConvolution
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.mul_apply]
    ring
  · unfold momentConvolution
    rw [← Finset.sum_neg_distrib,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring

theorem hasDerivAt_atomGrowth {n : ℕ} (hn : 2 ≤ n) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun r => growthFunctional r (atomMoment n r)) (growthSlope q (atomMoment n q)) q := by
  unfold growthFunctional growthSlope
  apply HasDerivAt.fun_sum
  intro j hj
  have hj7 : j+2 ≤ 7 := by have := Finset.mem_range.mp hj; omega
  exact ((hasDerivAt_growthCoefficient q (j+2) hj7).mul
    (hasDerivAt_atomMoment hn (j+2) hq)).congr_deriv (by
      simp only [Nat.add_assoc,Nat.reduceAdd]
      ring)

theorem hasDerivAt_atomFullPairGrowth {n : ℕ} (hn : 2 ≤ n) {q : ℝ} (hq : 0 < q) :
    HasDerivAt (fun r => fullPairGrowth r (atomMoment n r) (atomMoment n r))
      (fullPairGrowthSlope q (atomMoment n q) (atomMoment n q)) q := by
  unfold fullPairGrowth growthFunctional fullPairGrowthSlope
  apply HasDerivAt.fun_sum
  intro j hj
  have hj7 : j+2 ≤ 7 := by have := Finset.mem_range.mp hj; omega
  exact ((hasDerivAt_growthCoefficient q (j+2) hj7).mul
    (hasDerivAt_atomMomentConvolution hn (j+2) hq)).congr_deriv (by ring)

def dominantFullPairGrowthRatio (q : ℝ) : ℝ :=
  fullPairGrowth q (atomMoment 2 q) (atomMoment 2 q)/growthFunctional q (atomMoment 2 q)

theorem hasDerivAt_dominantFullPairGrowthRatio {q : ℝ} (hq : 3/2 ≤ q) :
    HasDerivAt dominantFullPairGrowthRatio
      (-fullPairGrowthCooling q (atomMoment 2 q)/(growthFunctional q (atomMoment 2 q))^2) q := by
  have hq0 : 0 < q := by linarith
  have ha := hasDerivAt_atomGrowth (by norm_num : 2 ≤ (2:ℕ)) hq0
  have hb := hasDerivAt_atomFullPairGrowth (by norm_num : 2 ≤ (2:ℕ)) hq0
  have hpos := atom_growthFunctional_pos (by norm_num : 2 ≤ (2:ℕ)) hq
  unfold dominantFullPairGrowthRatio
  exact (hb.div ha hpos.ne').congr_deriv (by unfold fullPairGrowthCooling; ring)

theorem dominantFullPairGrowthRatio_deriv_neg {q : ℝ} (hq : 3/2 ≤ q) :
    deriv dominantFullPairGrowthRatio q < 0 := by
  rw [(hasDerivAt_dominantFullPairGrowthRatio hq).deriv]
  have ha := atom_growthFunctional_pos (by norm_num : 2 ≤ (2:ℕ)) hq
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (atom_fullPairGrowthCooling_pos hq)) (pow_pos ha 2)

theorem dominantFullPairGrowthRatio_strictAntiOn :
    StrictAntiOn dominantFullPairGrowthRatio (Ici (3/2)) := by
  apply strictAntiOn_of_deriv_neg (convex_Ici _)
  · intro q hq
    exact (hasDerivAt_dominantFullPairGrowthRatio hq).continuousAt.continuousWithinAt
  · intro q hq
    have hq' : 3/2 < q := by simpa only [interior_Ici,mem_Ioi] using hq
    exact dominantFullPairGrowthRatio_deriv_neg hq'.le
end
end RHTower.ThetaCuspDefect
