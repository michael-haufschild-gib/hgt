import GaloisForLFunctions.RHTower.WeilPaperSpectralAffineContinuity
import GaloisForLFunctions.RHTower.WeilPaperSpectralReflection
import GaloisForLFunctions.RHTower.WeilPaperPacketNormalizedSeparation
import GaloisForLFunctions.RHTower.WeilWorkPBAPJointWidthSector

/-!
# Unbounded full energy among normalized integer-null spectral laws

Paired modulation has constant positive mass and logarithmically growing full
energy. Placing both clusters below the first integer lag makes the entire
family complex-null before normalization. No positivity conjecture is used.
-/

open Complex MeasureTheory Zeta23
open scoped BigOperators
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- The literal positive pair used in the modulation energy estimate. -/
def paperPairedClusterMixture (f : JointSmoothTest) (L T : ℝ) : WeilTestFn →₀ ℝ :=
  Finsupp.single (clusterDifferenceTest (cosineProfileTest f T) L).1 1 +
    Finsupp.single (clusterDifferenceTest (sineProfileTest f T) L).1 1

theorem paperPairedClusterMixture_nonneg (f : JointSmoothTest) (L T : ℝ) :
    ∀ g, 0 ≤ paperPairedClusterMixture f L T g := by
  classical
  intro g
  simp only [paperPairedClusterMixture, Finsupp.add_apply, Finsupp.single_apply]
  split_ifs <;> positivity

theorem mixtureSample_paperPairedClusterMixture (f : JointSmoothTest) (L T y : ℝ) :
    mixtureSample (paperPairedClusterMixture f L T) y =
      EF.weilTest (clusterDifference (cosineProfile f.1.1 T) L)
        (clusterDifference (cosineProfile f.1.1 T) L) y +
      EF.weilTest (clusterDifference (sineProfile f.1.1 T) L)
        (clusterDifference (sineProfile f.1.1 T) L) y := by
  simp only [paperPairedClusterMixture, mixtureSample, map_add,
    Finsupp.linearCombination_single, one_smul]
  rfl

/-- Exact complex correlation, including both cross-cluster lags. -/
theorem mixtureSample_paperPairedClusterMixture_formula (f : JointSmoothTest) (L T y : ℝ) :
    mixtureSample (paperPairedClusterMixture f L T) y =
      2 * ((Real.cos (T*y) : ℂ) * EF.weilTest f.1.1 f.1.1 y) -
        (Real.cos (T*(y-L)) : ℂ) * EF.weilTest f.1.1 f.1.1 (y-L) -
        (Real.cos (T*(y+L)) : ℂ) * EF.weilTest f.1.1 f.1.1 (y+L) := by
  rw [mixtureSample_paperPairedClusterMixture]
  have hc := weilTest_clusterDifference (contDiff_cosineProfile f.2 T).continuous
    (hasCompactSupport_cosineProfile f.1.2.2 T) L y
  have hs := weilTest_clusterDifference (contDiff_sineProfile f.2 T).continuous
    (hasCompactSupport_sineProfile f.1.2.2 T) L y
  have h0 := weilTest_cosine_sine_add f.2.continuous f.1.2.2 T y
  have hm := weilTest_cosine_sine_add f.2.continuous f.1.2.2 T (y-L)
  have hp := weilTest_cosine_sine_add f.2.continuous f.1.2.2 T (y+L)
  linear_combination hc + hs + 2*h0 - hm - hp

/-- The pair's mass does not depend on modulation frequency. -/
theorem paperPairedClusterMixture_mass (f : JointSmoothTest) {L W : ℝ}
    (hf : tsupport f.1.1 ⊆ Set.Icc 0 W) (hWL : W < L) (hL : 0 ≤ L) (T : ℝ) :
    mixtureSample (paperPairedClusterMixture f L T) 0 = ((2*testMass f.1.1 : ℝ) : ℂ) := by
  rw [mixtureSample_paperPairedClusterMixture, autocorr_zero_eq_testMass,
    autocorr_zero_eq_testMass, ← Complex.ofReal_add, joint_pair_testMass f hf hWL hL T]

/-- A pair wholly below the first integer lag is complex-null at every integer. -/
theorem paperPairedClusterMixture_complex_null (f : JointSmoothTest) {L W : ℝ}
    (hf : tsupport f.1.1 ⊆ Set.Icc 0 W) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hgap : W + L < Real.log 2) (T : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    mixtureSample (paperPairedClusterMixture f L T) (Real.log n) = 0 := by
  have hlog : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by positivity) (by exact_mod_cast hn)
  have hy : W < |Real.log n| := by rw [abs_of_nonneg (by linarith)]; linarith
  have hm : W < |Real.log n - L| := by rw [abs_of_nonneg (by linarith)]; linarith
  have hp : W < |Real.log n + L| := by rw [abs_of_nonneg (by linarith)]; linarith
  rw [mixtureSample_paperPairedClusterMixture_formula,
    weilTest_eq_zero_outside_interval hf hy,
    weilTest_eq_zero_outside_interval hf hm,
    weilTest_eq_zero_outside_interval hf hp]
  simp

/-- The native full-energy lower bound applies to the literal finite mixture. -/
theorem paperPairedClusterMixture_energy_lower (f : JointSmoothTest) {L W : ℝ}
    (hf : tsupport f.1.1 ⊆ Set.Icc 0 W) (hWL : W < L) (hL : 0 ≤ L) (T : ℝ) :
    2*testMass f.1.1*Real.log (2+|T|)-jointEnergyCost f L ≤
      energy (paperPairedClusterMixture f L T) := by
  simpa only [paperPairedClusterMixture, energy, map_add,
    Finsupp.linearCombination_single, one_smul, clusterDifferenceTest, cosineProfileTest,
    sineProfileTest] using joint_pair_full_energy_lower f hf hWL hL T

/-- Full energy is unbounded above within actual normalized complex-null mixtures. -/
theorem exists_complexNullMixture_energy_gt (B : ℝ) :
    ∃ c : ComplexNullMixture, B < energy c.1.1 := by
  have hlog : 0 < Real.log (2 : ℝ) := Real.log_pos one_lt_two
  let W := Real.log (2 : ℝ) / 4
  let L := Real.log (2 : ℝ) / 2
  have hW : 0 < W := by dsimp [W]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hWL : W < L := by dsimp [W, L]; linarith
  have hgap : W + L < Real.log 2 := by dsimp [W, L]; linarith
  let f := jointDilatedTest jointUnitBumpTest W hW
  have hf : tsupport f.1.1 ⊆ Set.Icc 0 W :=
    jointDilatedProfile_support jointUnitBumpTest_support hW
  have hmass : 0 < testMass f.1.1 := by
    change 0 < testMass (jointDilatedProfile jointUnitBumpTest.1.1 W)
    rw [jointDilatedProfile_mass _ hW]
    exact mul_pos hW jointUnitBumpTest_mass_pos
  let M := 2*testMass f.1.1
  have hM : 0 < M := mul_pos two_pos hmass
  let C := jointEnergyCost f L
  let T := Real.exp ((B*M+C+1)/M)
  let a := paperPairedClusterMixture f L T
  let d := paperNormalizeMass M hM a (paperPairedClusterMixture_nonneg f L T)
    (paperPairedClusterMixture_mass f hf hWL hL T)
  have hd : ∀ n : ℕ, 2 ≤ n → mixtureSample d.1 (Real.log n) = 0 := by
    intro n hn
    change mixtureSample (M⁻¹ • a) (Real.log n) = 0
    rw [mixtureSample_smul, paperPairedClusterMixture_complex_null f hf hW.le hL hgap T n hn,
      smul_zero]
  refine ⟨⟨d, hd⟩, ?_⟩
  have hfreq : (B*M+C+1)/M < Real.log (2+|T|) := by
    rw [← Real.log_exp ((B*M+C+1)/M)]
    apply Real.log_lt_log (Real.exp_pos _)
    dsimp [T]
    rw [abs_of_pos (Real.exp_pos _)]
    linarith
  have he := paperPairedClusterMixture_energy_lower f hf hWL hL T
  have hh := mul_lt_mul_of_pos_left hfreq hM
  rw [mul_div_cancel₀ _ hM.ne'] at hh
  have hraw : B*M < energy a := by
    dsimp only [M, C, a] at he hh ⊢
    linarith only [he, hh]
  change B < energy (M⁻¹ • a)
  rw [map_smul, smul_eq_mul, ← div_eq_inv_mul]
  exact (lt_div_iff₀ hM).mpr hraw

/-- Unbounded energy persists for real tests and both spectral reflection symmetries. -/
theorem exists_symmetric_real_complexNullMixture_energy_gt (B : ℝ) :
    ∃ c : ComplexNullMixture, B < energy c.1.1 ∧
      (∀ f, c.1.1 f ≠ 0 → ∀ x, (f.1 x).im = 0) ∧
      Measure.map (fun ξ : ℝ => -ξ) (spectralProbability c.1 : Measure ℝ) =
        (spectralProbability c.1 : Measure ℝ) ∧
      Measure.map (fun z : PrimePhaseSpace => -z)
        ((spectralRepresentingMeasure c).1 : Measure PrimePhaseSpace) =
        ((spectralRepresentingMeasure c).1 : Measure PrimePhaseSpace) := by
  obtain ⟨c, hc⟩ := exists_complexNullMixture_energy_gt B
  have he : energy c.1.1 ∈ {e : ℝ | ∃ d : NormalizedMixture,
      defect d.1 = 0 ∧ energy d.1 = e} := ⟨c.1, defect_complexNullMixture c, rfl⟩
  rw [attainable_energy_eq_symmetric_real_test_complex_null] at he
  obtain ⟨d, hd, hr, hs, ht⟩ := he
  exact ⟨d, hd.symm ▸ hc, hr, hs, ht⟩

end RHTower.WeilWorkPBAP
