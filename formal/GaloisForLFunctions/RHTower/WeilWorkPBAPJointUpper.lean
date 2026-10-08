import GaloisForLFunctions.RHTower.WeilWorkPBAPJointSeedGamma
import GaloisForLFunctions.RHTower.WeilPositivityRegularPerturbationRigidity

/-!
# Exact-mass upper bounds for the actual modulated pair

The constant part of Gamma is integrated against the exact pair mass.
Only its centered remainder uses the density majorant, costing the base
first Fourier moment divided by modulation height. This moment is invariant
under physical dilation. Both signed poles are retained in the full estimate.
-/

open Complex MeasureTheory Real Set Filter Topology Zeta23
open scoped ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- First absolute Fourier moment of the actual source. -/
def jointFourierFirstMoment (f : ℝ → ℂ) : ℝ :=
  ∫ v : ℝ, ‖paperFT f (v:ℂ)‖^2 * |v|

theorem joint_fourier_first_integrable (f : JointSmoothTest) :
    Integrable (fun v : ℝ => ‖paperFT f.1.1 (v:ℂ)‖^2 * |v|) := by
  obtain ⟨a, ha⟩ := WeilSpectral.exists_abs_bound_of_hasCompactSupport f.1.2.2
  apply integrable_normSq_paperFT_mul_of_linear f.1.2.1
    (tsupport_subset_of_vanish
      (fun u hu => by by_contra h; exact (not_le_of_gt hu) (ha u h)))
    continuous_abs (Mp := 1)
  intro v
  simp only [abs_abs, one_mul]
  linarith

theorem jointFourierFirstMoment_nonneg (f : ℝ → ℂ) :
    0 ≤ jointFourierFirstMoment f :=
  integral_nonneg fun v => mul_nonneg (sq_nonneg _) (abs_nonneg v)

/-- Dilation preserves the first absolute Fourier moment exactly. -/
theorem jointFourierFirstMoment_dilate (f : ℝ → ℂ) {W : ℝ} (hW : 0 < W) :
    jointFourierFirstMoment (jointDilatedProfile f W) = jointFourierFirstMoment f := by
  unfold jointFourierFirstMoment
  calc
    _ = ∫ v : ℝ, W * (‖paperFT f ((W*v:ℝ):ℂ)‖^2 * |W*v|) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun v => by
        dsimp only
        rw [jointDilatedProfile_paperFT f hW]
        simp only [norm_smul, Real.norm_eq_abs, abs_of_pos hW, mul_pow,
          abs_mul, Complex.ofReal_mul]
        ring
    _ = _ := by
      rw [integral_const_mul, Measure.integral_comp_mul_left
        (fun v : ℝ => ‖paperFT f (v:ℂ)‖^2 * |v|) W,
        abs_inv, abs_of_pos hW, smul_eq_mul]
      field_simp [hW.ne']

/-- The Gamma remainder relative to any real frequency center is at most linear. -/
theorem joint_gamma_shift_upper (ξ s : ℝ) :
    EF.gammaBracket ξ ≤ Real.log (1+|s|)+4+|ξ-s|/(1+|s|) := by
  have hv : 0 < 1+|s| := by positivity
  have hu : 0 < 1+|ξ| := by positivity
  have hlog := Real.log_le_sub_one_of_pos (div_pos hu hv)
  rw [Real.log_div hu.ne' hv.ne'] at hlog
  have ht : |ξ| ≤ |s|+|ξ-s| := by
    calc |ξ| = |s+(ξ-s)| := by congr 1; ring
         _ ≤ _ := abs_add_le _ _
  have hd : (1+|ξ|)/(1+|s|)-1 ≤ |ξ-s|/(1+|s|) := by
    apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hv).mpr
    rw [add_mul, div_mul_cancel₀ _ hv.ne']
    linarith
  have hg := archimedeanWeilSymbol_le_log_add ξ
  rw [archimedeanWeilSymbol_paper] at hg
  linarith

private theorem upper_pair_gamma_integrable (f : JointSmoothTest) (L T : ℝ) :
    Integrable (fun ξ => jointPairDensity f L T ξ * EF.gammaBracket ξ) := by
  have hi (g : JointSmoothTest) :
      Integrable (fun ξ : ℝ => ‖paperFT g.1.1 (ξ:ℂ)‖^2 * EF.gammaBracket ξ) := by
    have h := LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket
      g.1.2.1 g.1.2.2 g.1.2.1 g.1.2.2
    refine h.re.congr (Eventually.of_forall fun ξ => ?_)
    change (paperFT (EF.weilTest g.1.1 g.1.1) (ξ:ℂ) *
      (EF.gammaBracket ξ:ℂ)).re = _
    rw [paperFT_weilTest_self_ofReal g.2.continuous g.1.2.2]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  have h := (hi (clusterDifferenceTest (cosineProfileTest f T) L)).add
    (hi (clusterDifferenceTest (sineProfileTest f T) L))
  exact h.congr (Eventually.of_forall fun ξ => by
    change ‖paperFT (clusterDifference (cosineProfile f.1.1 T) L) (ξ:ℂ)‖^2 *
      EF.gammaBracket ξ +
      ‖paperFT (clusterDifference (sineProfile f.1.1 T) L) (ξ:ℂ)‖^2 *
      EF.gammaBracket ξ = jointPairDensity f L T ξ * EF.gammaBracket ξ
    dsimp [jointPairDensity]
    ring)

private theorem upper_pair_pointwise (f : JointSmoothTest) (L : ℝ) {T : ℝ}
    (hT : 0 ≤ T) (ξ : ℝ) :
    jointPairDensity f L T ξ * EF.gammaBracket ξ ≤
      jointPairDensity f L T ξ * (Real.log (1+T)+4) +
      2/(1+T) * (‖paperFT f.1.1 (ξ+T:ℝ)‖^2 * |ξ+T| +
        ‖paperFT f.1.1 (ξ-T:ℝ)‖^2 * |ξ-T|) := by
  let A := Real.log (1+T)+4
  let q := jointPairDensity f L T ξ
  let p := ‖paperFT f.1.1 (ξ+T:ℝ)‖^2
  let n := ‖paperFT f.1.1 (ξ-T:ℝ)‖^2
  let r := min |ξ+T| |ξ-T|
  have hr : 0 ≤ r := le_min (abs_nonneg _) (abs_nonneg _)
  have hq : 0 ≤ q := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hp : 0 ≤ p := sq_nonneg _
  have hn : 0 ≤ n := sq_nonneg _
  have hv : 0 < 1+T := by linarith
  have h1 := joint_gamma_shift_upper ξ (-T)
  have h2 := joint_gamma_shift_upper ξ T
  simp only [abs_neg, abs_of_nonneg hT, sub_neg_eq_add] at h1 h2
  have hg : EF.gammaBracket ξ ≤ A+r/(1+T) := by
    rcases le_total |ξ+T| |ξ-T| with h | h
    · simpa only [r, min_eq_left h, A] using h1
    · simpa only [r, min_eq_right h, A] using h2
  have hbound : q ≤ 2*(p+n) := joint_pair_real_density_le f L T ξ
  have hrem := mul_le_mul_of_nonneg_right hbound (div_nonneg hr hv.le)
  have hpr := mul_le_mul_of_nonneg_left (min_le_left |ξ+T| |ξ-T|) hp
  have hnr := mul_le_mul_of_nonneg_left (min_le_right |ξ+T| |ξ-T|) hn
  have hsum : (p+n)*r ≤ p*|ξ+T|+n*|ξ-T| := by
    dsimp only [r] at *
    nlinarith only [hpr, hnr]
  have hh := mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2/(1+T) by positivity)
  have hmain := mul_le_mul_of_nonneg_left hg hq
  change q*EF.gammaBracket ξ ≤ q*A+2/(1+T)*(p*|ξ+T|+n*|ξ-T|)
  calc
    _ ≤ q*A+q*(r/(1+T)) := by nlinarith only [hmain]
    _ ≤ q*A+2*(p+n)*(r/(1+T)) := by linarith only [hrem]
    _ = q*A+(2/(1+T))*((p+n)*r) := by ring
    _ ≤ _ := by linarith only [hh]

/-- Sharp mass coefficient, with a vanishing first-moment remainder. -/
theorem joint_pair_gamma_upper (f : JointSmoothTest) {L W T : ℝ}
    (hf : tsupport f.1.1 ⊆ Icc 0 W) (hWL : W < L) (hL : 0 ≤ L) (hT : 0 ≤ T) :
    testGamma (clusterDifference (cosineProfile f.1.1 T) L) +
      testGamma (clusterDifference (sineProfile f.1.1 T) L) ≤
      2*testMass f.1.1*(Real.log (1+T)+4) +
        4*jointFourierFirstMoment f.1.1/(2*Real.pi*(1+T)) := by
  let q := jointPairDensity f L T
  let v : ℝ → ℝ := fun ξ => ‖paperFT f.1.1 (ξ:ℂ)‖^2 * |ξ|
  let A := Real.log (1+T)+4
  have hv : Integrable v := joint_fourier_first_integrable f
  have hp : Integrable (fun ξ => v (ξ+T)) := hv.comp_add_right T
  have hn : Integrable (fun ξ => v (ξ-T)) := by
    simpa only [sub_eq_add_neg] using hv.comp_add_right (-T)
  have hq : Integrable q := jointPairDensity_integrable f L T
  have hsum : Integrable (fun ξ => v (ξ+T)+v (ξ-T)) := hp.add hn
  have hrem : Integrable (fun ξ => 2/(1+T)*(v (ξ+T)+v (ξ-T))) :=
    hsum.const_mul _
  have hib : Integrable (fun ξ => q ξ*A+2/(1+T)*(v (ξ+T)+v (ξ-T))) :=
    (hq.mul_const A).add hrem
  have hi := integral_mono (upper_pair_gamma_integrable f L T) hib
    (fun ξ => upper_pair_pointwise f L hT ξ)
  rw [integral_add (hq.mul_const A) hrem,
    integral_mul_const, integral_const_mul, integral_add hp hn,
    integral_add_right_eq_self v T] at hi
  have hnint : (∫ ξ, v (ξ-T)) = ∫ ξ, v ξ := by
    simpa only [sub_eq_add_neg] using integral_add_right_eq_self v (-T)
  rw [hnint] at hi
  have hm := jointPairDensity_mass f hf hWL hL T
  have hh := mul_le_mul_of_nonneg_left hi (show 0 ≤ 1/(2*Real.pi) by positivity)
  rw [joint_pair_gamma_eq_integral]
  calc
    _ ≤ (1/(2*Real.pi))*((∫ ξ, q ξ)*A+2/(1+T)*((∫ ξ, v ξ)+(∫ ξ, v ξ))) := hh
    _ = _ := by
      change (1/(2*Real.pi))*((∫ ξ, jointPairDensity f L T ξ)*A+
        2/(1+T)*(jointFourierFirstMoment f.1.1+jointFourierFirstMoment f.1.1)) = _
      rw [mul_add, ← mul_assoc, hm]
      dsimp [A]
      field_simp
      ring

/-- The full upper bound includes both signed poles of the actual pair. -/
theorem joint_pair_full_energy_upper (f : JointSmoothTest) {L W T : ℝ}
    (hf : tsupport f.1.1 ⊆ Icc 0 W) (hWL : W < L) (hL : 0 ≤ L) (hT : 0 < T) :
    jointPairFullEnergy f L T ≤
      2*testMass f.1.1*(Real.log (1+T)+4) +
      4*jointFourierFirstMoment f.1.1/(2*Real.pi*(1+T)) +
      4*(1+Real.exp (L/2))*(1+Real.exp (-L/2))*
        (Real.exp (W/2)*(∫ u : ℝ, ‖deriv (deriv f.1.1) u‖)/T^2)^2 := by
  have hg := joint_pair_gamma_upper f hf hWL hL hT.le
  have hp := (abs_le.mp (joint_pair_poles_high_abs f hf hT.ne' L)).2
  have hc := weilArchRe_eq_testPole_add_testGamma
    (clusterDifferenceTest (cosineProfileTest f T) L).1
  have hs := weilArchRe_eq_testPole_add_testGamma
    (clusterDifferenceTest (sineProfileTest f T) L).1
  dsimp only [clusterDifferenceTest, cosineProfileTest, sineProfileTest] at hc hs
  unfold jointPairFullEnergy
  rw [hc, hs]
  linarith

end RHTower.WeilWorkPBAP
