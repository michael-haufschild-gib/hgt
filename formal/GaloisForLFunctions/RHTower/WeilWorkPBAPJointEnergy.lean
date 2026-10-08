import GaloisForLFunctions.RHTower.WeilWorkPBAPJointCoercivity

/-!
Literal energy of the joint modulation family.
Both signed poles are retained, with opposite exponential translation weights.
-/

open Complex MeasureTheory Zeta23
open scoped ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- Exponentially weighted physical L1 mass, retaining the sign of the pole. -/
def jointLaplaceNorm (f : JointSmoothTest) (v : ℝ) : ℝ :=
  ∫ u : ℝ, ‖f.1.1 u‖ * Real.exp (v*u)

theorem jointLaplaceNorm_nonneg (f : JointSmoothTest) (v : ℝ) :
    0 ≤ jointLaplaceNorm f v :=
  integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

private theorem joint_laplace_integrable (f : JointSmoothTest) (v : ℝ) :
    Integrable (fun u : ℝ => ‖f.1.1 u‖ * Real.exp (v*u)) :=
  (f.2.continuous.norm.mul (Real.continuous_exp.comp
    (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
      f.1.2.2.norm.mul_right

private theorem joint_modulation_paperFT_le (f : JointSmoothTest) (r : ℝ → ℝ)
    (hr : ∀ u, |r u| ≤ 1) (z : ℂ) :
    ‖paperFT (fun u => f.1.1 u * (r u:ℂ)) z‖ ≤ jointLaplaceNorm f (-z.im) := by
  apply norm_integral_le_of_norm_le (joint_laplace_integrable f (-z.im))
  filter_upwards [] with u
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  have hz : (I*z*(u:ℂ)).re = -z.im*u := by simp [Complex.mul_re]
  rw [hz]
  calc
    _ ≤ (‖f.1.1 u‖*1)*Real.exp (-z.im*u) := by gcongr; exact hr u
    _ = _ := by ring

private theorem joint_cluster_factor_le (L : ℝ) (z : ℂ) :
    ‖1-Complex.exp (I*z*L)‖ ≤ 1+Real.exp (-z.im*L) := by
  calc
    _ ≤ ‖(1:ℂ)‖+‖Complex.exp (I*z*L)‖ := norm_sub_le _ _
    _ = _ := by rw [norm_one, Complex.norm_exp]; congr 2; simp [Complex.mul_re]

private theorem joint_cosine_pole_le (f : JointSmoothTest) (L T : ℝ) (z : ℂ) :
    ‖paperFT (clusterDifference (cosineProfile f.1.1 T) L) z‖ ≤
      (1+Real.exp (-z.im*L))*jointLaplaceNorm f (-z.im) := by
  rw [paperFT_clusterDifference (contDiff_cosineProfile f.2 T).continuous
    (hasCompactSupport_cosineProfile f.1.2.2 T), norm_mul]
  exact mul_le_mul (joint_cluster_factor_le L z)
    (joint_modulation_paperFT_le f (fun u => Real.cos (T*u))
      (fun u => abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩) z)
    (norm_nonneg _) (by positivity)

private theorem joint_sine_pole_le (f : JointSmoothTest) (L T : ℝ) (z : ℂ) :
    ‖paperFT (clusterDifference (sineProfile f.1.1 T) L) z‖ ≤
      (1+Real.exp (-z.im*L))*jointLaplaceNorm f (-z.im) := by
  rw [paperFT_clusterDifference (contDiff_sineProfile f.2 T).continuous
    (hasCompactSupport_sineProfile f.1.2.2 T), norm_mul]
  exact mul_le_mul (joint_cluster_factor_le L z)
    (joint_modulation_paperFT_le f (fun u => Real.sin (T*u))
      (fun u => abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩) z)
    (norm_nonneg _) (by positivity)

private theorem joint_testPole_lower (g : JointSmoothTest) :
    -2*‖paperFT g.1.1 (I/2)‖*‖paperFT g.1.1 (-I/2)‖ ≤ testPole g.1.1 := by
  have hp := EF.paperFT_weilTest g.2.continuous g.2.continuous g.1.2.2 g.1.2.2 (I/2)
  have hm := EF.paperFT_weilTest g.2.continuous g.2.continuous g.1.2.2 g.1.2.2 (-I/2)
  have hcp : conj (I/2:ℂ) = -I/2 := by
    simp only [map_div₀, map_ofNat, Complex.conj_I]
  have hcm : conj (-I/2:ℂ) = I/2 := by
    simp only [map_div₀, map_ofNat, map_neg, Complex.conj_I, neg_neg]
  rw [hcp] at hp
  rw [hcm] at hm
  have hpRe := (abs_le.mp (Complex.abs_re_le_norm
    (paperFT g.1.1 (I/2) * conj (paperFT g.1.1 (-I/2))))).1
  have hmRe := (abs_le.mp (Complex.abs_re_le_norm
    (paperFT g.1.1 (-I/2) * conj (paperFT g.1.1 (I/2))))).1
  simp only [norm_mul, Complex.norm_conj] at hpRe hmRe
  unfold testPole
  rw [hp, hm, Complex.add_re]
  nlinarith only [hpRe, hmRe]

/-- Both signed poles stay uniformly bounded below over all real modulations. -/
theorem joint_pair_poles_lower (f : JointSmoothTest) (L T : ℝ) :
    -4*(1+Real.exp (L/2))*(1+Real.exp (-L/2))*
      jointLaplaceNorm f (1/2)*jointLaplaceNorm f (-1/2) ≤
      testPole (clusterDifference (cosineProfile f.1.1 T) L) +
      testPole (clusterDifference (sineProfile f.1.1 T) L) := by
  let gc := clusterDifferenceTest (cosineProfileTest f T) L
  let gs := clusterDifferenceTest (sineProfileTest f T) L
  let A := (1+Real.exp (-L/2))*jointLaplaceNorm f (-1/2)
  let B := (1+Real.exp (L/2))*jointLaplaceNorm f (1/2)
  have hA : 0 ≤ A := mul_nonneg (by positivity) (jointLaplaceNorm_nonneg f _)
  have hpi : ((I/2:ℂ).im) = 1/2 := by norm_num
  have hmi : ((-I/2:ℂ).im) = -(1/2) := by norm_num
  have hneg : -(1/2:ℝ)*L = -L/2 := by ring
  have hp : ‖paperFT gc.1.1 (I/2)‖ ≤ A := by
    simpa only [hpi, hneg, neg_div, A, gc, clusterDifferenceTest, cosineProfileTest]
      using joint_cosine_pole_le f L T (I/2)
  have hm : ‖paperFT gc.1.1 (-I/2)‖ ≤ B := by
    simpa only [hmi, neg_neg, div_mul_eq_mul_div, one_mul, B,
      gc, clusterDifferenceTest, cosineProfileTest]
      using joint_cosine_pole_le f L T (-I/2)
  have sp : ‖paperFT gs.1.1 (I/2)‖ ≤ A := by
    simpa only [hpi, hneg, neg_div, A, gs, clusterDifferenceTest, sineProfileTest]
      using joint_sine_pole_le f L T (I/2)
  have sm : ‖paperFT gs.1.1 (-I/2)‖ ≤ B := by
    simpa only [hmi, neg_neg, div_mul_eq_mul_div, one_mul, B,
      gs, clusterDifferenceTest, sineProfileTest]
      using joint_sine_pole_le f L T (-I/2)
  have hc := mul_le_mul hp hm (norm_nonneg _) hA
  have hs := mul_le_mul sp sm (norm_nonneg _) hA
  have hpc := joint_testPole_lower gc
  have hps := joint_testPole_lower gs
  change -4*(1+Real.exp (L/2))*(1+Real.exp (-L/2))*
    jointLaplaceNorm f (1/2)*jointLaplaceNorm f (-1/2) ≤ testPole gc.1.1 + testPole gs.1.1
  dsimp [A, B] at hc hs
  nlinarith only [hc, hs, hpc, hps]

/-- Fixed base cost for the full gamma integral and both signed poles. -/
def jointEnergyCost (f : JointSmoothTest) (L : ℝ) : ℝ :=
  2*testMass f.1.1*(10+Real.log 4) + 4*jointLogMoment f +
    4*(1+Real.exp (L/2))*(1+Real.exp (-L/2))*
      jointLaplaceNorm f (1/2)*jointLaplaceNorm f (-1/2)

theorem jointEnergyCost_nonneg (f : JointSmoothTest) (L : ℝ) :
    0 ≤ jointEnergyCost f L := by
  have hm : 0 ≤ testMass f.1.1 := integral_nonneg fun u => sq_nonneg _
  have hj := jointLogMoment_nonneg f
  have hp := jointLaplaceNorm_nonneg f (1/2)
  have hn := jointLaplaceNorm_nonneg f (-1/2)
  have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold jointEnergyCost
  positivity

/-- Literal full-energy coercivity, with no energy lower-bound premise. -/
theorem joint_pair_full_energy_lower (f : JointSmoothTest) {L W : ℝ}
    (hf : tsupport f.1.1 ⊆ Set.Icc 0 W) (hWL : W < L) (hL : 0 ≤ L) (T : ℝ) :
    2*testMass f.1.1*Real.log (2+|T|)-jointEnergyCost f L ≤
      weilArchRe (EF.weilTest
        (clusterDifference (cosineProfile f.1.1 T) L)
        (clusterDifference (cosineProfile f.1.1 T) L)) +
      weilArchRe (EF.weilTest
        (clusterDifference (sineProfile f.1.1 T) L)
        (clusterDifference (sineProfile f.1.1 T) L)) := by
  have hg := joint_pair_gamma_lower f hf hWL hL T
  have hp := joint_pair_poles_lower f L T
  have hec := weilArchRe_eq_testPole_add_testGamma
    (clusterDifferenceTest (cosineProfileTest f T) L).1
  have hes := weilArchRe_eq_testPole_add_testGamma
    (clusterDifferenceTest (sineProfileTest f T) L).1
  dsimp only [clusterDifferenceTest, cosineProfileTest, sineProfileTest] at hec hes
  rw [hec, hes]
  dsimp [jointEnergyCost]
  linarith

/-- Exact finite real sum, including collisions between constructed tests. -/
theorem jointClusterMixture_sum_real {ι : Type} [Fintype ι] (f : JointSmoothTest)
    (L : ℝ) (w t : ι → ℝ) (F : WeilTestFn → ℝ) :
    (jointClusterMixture f L w t).sum (fun g r => r*F g) =
      F (clusterDifferenceTest f L).1 + ∑ i, w i *
        (F (clusterDifferenceTest (cosineProfileTest f (t i)) L).1 +
          F (clusterDifferenceTest (sineProfileTest f (t i)) L).1) := by
  change (Finsupp.linearCombination ℝ F) (jointClusterMixture f L w t) = _
  simp only [jointClusterMixture, map_add, map_sum, Finsupp.linearCombination_single,
    smul_eq_mul, one_mul, mul_add]

/-- The cost of a finite mixture is charged to its actual total correction mass. -/
theorem jointClusterMixture_energy_lower {ι : Type} [Fintype ι] (f : JointSmoothTest)
    {L W : ℝ} (hf : tsupport f.1.1 ⊆ Set.Icc 0 W) (hWL : W < L) (hL : 0 ≤ L)
    (w t : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    weilArchRe (EF.weilTest (clusterDifference f.1.1 L) (clusterDifference f.1.1 L)) +
      2*testMass f.1.1*(∑ i, w i*Real.log (2+|t i|)) - jointEnergyCost f L*(∑ i, w i) ≤
      (jointClusterMixture f L w t).sum (fun g r => r*weilArchRe (EF.weilTest g.1 g.1)) := by
  rw [jointClusterMixture_sum_real]
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (joint_pair_full_energy_lower f hf hWL hL (t i)) (hw i))
  have he : (∑ i, w i*(2*testMass f.1.1*Real.log (2+|t i|)-jointEnergyCost f L)) =
      2*testMass f.1.1*(∑ i, w i*Real.log (2+|t i|))-jointEnergyCost f L*(∑ i, w i) := by
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i hi <;> ring
  rw [he] at hh
  dsimp only [clusterDifferenceTest, cosineProfileTest, sineProfileTest]
  linarith

end RHTower.WeilWorkPBAP
