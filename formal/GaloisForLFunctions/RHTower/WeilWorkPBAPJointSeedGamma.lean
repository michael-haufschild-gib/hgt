import GaloisForLFunctions.RHTower.WeilWorkPBAPJointHighFrequency
import GaloisForLFunctions.RHTower.WeilWorkPBAPJointScale
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Uniform Gamma scaling for actual cluster seeds

A fixed Fourier majorant handles the logarithmic singularity at zero and the
Gamma dilation remainder. The resulting O(width) estimate is uniform in every
cluster separation and keeps the exact physical mass coefficient. In the
separated unit-profile family this yields the actual leading seed term
`-2 * width * baseMass * log width`, without an energy-sign premise.
-/

open Complex MeasureTheory Real Set Filter Topology Zeta23
open scoped ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- A fixed integrable Fourier weight dominates the Gamma dilation remainder. -/
def jointSeedLogWeight (v : ℝ) : ℝ :=
  14+Real.log 4+|Real.log v|+Real.log (2+|v|)

theorem jointSeedLogWeight_nonneg (v : ℝ) : 0 ≤ jointSeedLogWeight v := by
  have hl : 0 ≤ Real.log (2+|v|) := Real.log_nonneg (by linarith [abs_nonneg v])
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  unfold jointSeedLogWeight
  linarith [abs_nonneg (Real.log v)]

/-- The actual Gamma symbol has a width-independent integrable remainder away from zero. -/
theorem joint_gamma_scaled_abs {W v : ℝ} (hW : 0 < W) (hW1 : W ≤ 1) (hv : v ≠ 0) :
    |EF.gammaBracket (v/W)+Real.log W| ≤ jointSeedLogWeight v := by
  have hvp : 0 < |v| := abs_pos.mpr hv
  have hlo := joint_gamma_lower_log (v/W)
  have hup := archimedeanWeilSymbol_le_log_add (v/W)
  rw [archimedeanWeilSymbol_paper] at hup
  have hdiv : |v/W|=|v|/W := by rw [abs_div, abs_of_pos hW]
  have hlogdiv : Real.log (|v|/W)=Real.log v-Real.log W := by
    rw [Real.log_div hvp.ne' hW.ne', Real.log_abs]
  have hlower := Real.log_le_log (div_pos hvp hW)
    (show |v|/W ≤ 2+|v/W| by rw [hdiv]; linarith)
  rw [hlogdiv] at hlower
  have hsum : 1+|v/W|=(W+|v|)/W := by rw [hdiv]; field_simp
  have hlogsum : Real.log (1+|v/W|)=Real.log (W+|v|)-Real.log W := by
    rw [hsum, Real.log_div (by positivity) hW.ne']
  rw [hlogsum] at hup
  have hupper := Real.log_le_log (show 0<W+|v| by positivity)
    (show W+|v| ≤ 2+|v| by linarith)
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have h2 : 0 ≤ Real.log (2+|v|) := Real.log_nonneg (by linarith [abs_nonneg v])
  rw [abs_le]
  dsimp [jointSeedLogWeight]
  constructor <;> linarith [le_abs_self (Real.log v), neg_le_abs (Real.log v),
    abs_nonneg (Real.log v)]

private theorem seed_base_fourier_integrable (f : JointSmoothTest) :
    Integrable (fun v : ℝ => ‖paperFT f.1.1 (v:ℂ)‖^2) := by
  obtain ⟨a, ha⟩ := WeilSpectral.exists_abs_bound_of_hasCompactSupport f.1.2.2
  exact integrable_normSq_paperFT f.1.2.1 (tsupport_subset_of_vanish
    (fun u hu => by by_contra h; exact (not_le_of_gt hu) (ha u h)))

private theorem seed_base_fourier_bound (f : JointSmoothTest) (v : ℝ) :
    ‖paperFT f.1.1 (v:ℂ)‖ ≤ ∫ u : ℝ, ‖f.1.1 u‖ := by
  obtain ⟨a, ha⟩ := WeilSpectral.exists_abs_bound_of_hasCompactSupport f.1.2.2
  have h := norm_paperFT_le
    (f.2.continuous.integrable_of_hasCompactSupport f.1.2.2) ha (v:ℂ)
  simpa only [Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero, one_mul] using h

/-- The logarithmic singularity at zero is integrable against the actual Fourier square. -/
theorem joint_fourier_abs_log_integrable (f : JointSmoothTest) :
    Integrable (fun v : ℝ => ‖paperFT f.1.1 (v:ℂ)‖^2*|Real.log v|) := by
  let q : ℝ → ℝ := fun v => ‖paperFT f.1.1 (v:ℂ)‖^2
  let S : Set ℝ := Ioc (-1) 1
  let A : ℝ := ∫ u : ℝ, ‖f.1.1 u‖
  have hA : 0 ≤ A := integral_nonneg fun u => norm_nonneg _
  have hq (v : ℝ) : 0 ≤ q v := sq_nonneg _
  have hqa (v : ℝ) : q v ≤ A^2 :=
    (sq_le_sq₀ (norm_nonneg _) hA).mpr (seed_base_fourier_bound f v)
  have hlog : IntegrableOn (fun v : ℝ => |Real.log v|) S :=
    (intervalIntegral.intervalIntegrable_log' (a := -1) (b := 1)).1.abs
  have hsmall : Integrable (S.indicator (fun v => |Real.log v|)) :=
    (integrable_indicator_iff measurableSet_Ioc).mpr hlog
  have hlarge := joint_fourier_log_integrable f
  have hQ := seed_base_fourier_integrable f
  have hm : AEStronglyMeasurable (fun v : ℝ => q v*|Real.log v|) volume :=
    hQ.aestronglyMeasurable.mul Real.measurable_log.abs.aestronglyMeasurable
  apply (hlarge.add (hsmall.const_mul (A^2))).mono' hm
  apply Eventually.of_forall
  intro v
  change ‖q v*|Real.log v|‖ ≤ q v*Real.log (2+|v|)+A^2*S.indicator (fun v => |Real.log v|) v
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hq v) (abs_nonneg _))]
  have hl : 0 ≤ q v*Real.log (2+|v|) :=
    mul_nonneg (hq v) (Real.log_nonneg (by linarith [abs_nonneg v]))
  by_cases hv : v ∈ S
  · rw [Set.indicator_of_mem hv]
    exact (mul_le_mul_of_nonneg_right (hqa v) (abs_nonneg _)).trans (by linarith)
  · rw [Set.indicator_of_notMem hv, mul_zero, add_zero]
    have ha : 1 ≤ |v| := by
      change ¬ (-1 < v ∧ v ≤ 1) at hv
      by_cases hv1 : -1 < v
      · have := lt_of_not_ge (fun h => hv ⟨hv1,h⟩)
        linarith [le_abs_self v]
      · have := le_of_not_gt hv1
        linarith [neg_le_abs v]
    have hn : 0 ≤ Real.log v := by rw [← Real.log_abs]; exact Real.log_nonneg ha
    rw [abs_of_nonneg hn, ← Real.log_abs]
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log (by linarith : 0 < |v|) (by linarith)) (hq v)

/-- The actual fixed Fourier majorant is integrable, with no assumed logarithmic moment. -/
theorem jointSeedLogWeight_integrable (f : JointSmoothTest) :
    Integrable (fun v : ℝ => ‖paperFT f.1.1 (v:ℂ)‖^2*jointSeedLogWeight v) := by
  have h := ((seed_base_fourier_integrable f).mul_const (14+Real.log 4)).add
    ((joint_fourier_abs_log_integrable f).add (joint_fourier_log_integrable f))
  refine h.congr (Eventually.of_forall fun v => ?_)
  dsimp [jointSeedLogWeight]
  ring

/-- Explicit finite remainder budget for a fixed smooth source profile. -/
def jointSeedLogCost (f : JointSmoothTest) : ℝ :=
  (4/(2*Real.pi))*∫ v : ℝ, ‖paperFT f.1.1 (v:ℂ)‖^2*jointSeedLogWeight v

theorem jointSeedLogCost_nonneg (f : JointSmoothTest) : 0 ≤ jointSeedLogCost f := by
  apply mul_nonneg (by positivity)
  exact integral_nonneg fun v => mul_nonneg (sq_nonneg _) (jointSeedLogWeight_nonneg v)

private theorem seed_gamma_integrable (f : JointSmoothTest) :
    Integrable (fun ξ : ℝ => ‖paperFT f.1.1 (ξ:ℂ)‖^2*EF.gammaBracket ξ) := by
  have h := LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket
    f.1.2.1 f.1.2.2 f.1.2.1 f.1.2.2
  refine h.re.congr (Eventually.of_forall fun ξ => ?_)
  change (paperFT (EF.weilTest f.1.1 f.1.1) (ξ:ℂ)*
    (EF.gammaBracket ξ:ℂ)).re = _
  rw [paperFT_weilTest_self_ofReal f.2.continuous f.1.2.2]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

/-- Uniform cluster interference costs at most four times the base Fourier square. -/
theorem joint_cluster_density_le (f : JointSmoothTest) (L ξ : ℝ) :
    ‖paperFT (clusterDifference f.1.1 L) (ξ:ℂ)‖^2 ≤
      4*‖paperFT f.1.1 (ξ:ℂ)‖^2 := by
  rw [paperFT_clusterDifference f.2.continuous f.1.2.2, norm_mul, mul_pow]
  have he : ‖Complex.exp (I*(ξ:ℂ)*L)‖=1 := by
    rw [show I*(ξ:ℂ)*L=((ξ*L:ℝ):ℂ)*I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hh : ‖1-Complex.exp (I*(ξ:ℂ)*L)‖ ≤ 2 := by
    calc _ ≤ ‖(1:ℂ)‖+‖Complex.exp (I*(ξ:ℂ)*L)‖ := norm_sub_le _ _
         _ = _ := by rw [norm_one,he]; ring
  have hh2 : ‖1-Complex.exp (I*(ξ:ℂ)*L)‖^2 ≤ 4 := by
    nlinarith [norm_nonneg (1-Complex.exp (I*(ξ:ℂ)*L))]
  exact mul_le_mul_of_nonneg_right hh2 (sq_nonneg _)

/-- The actual cluster Gamma energy has a uniform O(width) scaling remainder.
The cluster separation is arbitrary, and the mass coefficient is exact. -/
theorem joint_cluster_gamma_scale_bound (f : JointSmoothTest) {W : ℝ}
    (hW : 0 < W) (hW1 : W ≤ 1) (L : ℝ) :
    |testGamma (clusterDifference (jointDilatedProfile f.1.1 W) L) +
        testMass (clusterDifference (jointDilatedProfile f.1.1 W) L)*Real.log W| ≤
      W*jointSeedLogCost f := by
  let fw := jointDilatedTest f W hW
  let g := clusterDifferenceTest fw L
  let q : ℝ → ℝ := fun v => ‖paperFT f.1.1 (v:ℂ)‖^2*jointSeedLogWeight v
  let ρ : ℝ → ℝ := fun ξ => ‖paperFT g.1.1 (ξ:ℂ)‖^2
  let d : ℝ → ℝ := fun ξ => 4*W^2*q (W*ξ)
  have hq : Integrable q := jointSeedLogWeight_integrable f
  have hd : Integrable d := (hq.comp_mul_left' hW.ne').const_mul (4*W^2)
  have hρ : Integrable ρ := seed_base_fourier_integrable g
  have hρg : Integrable (fun ξ => ρ ξ*EF.gammaBracket ξ) := seed_gamma_integrable g
  have hs (ξ : ℝ) : ‖paperFT fw.1.1 (ξ:ℂ)‖^2 =
      W^2*‖paperFT f.1.1 ((W*ξ:ℝ):ℂ)‖^2 := by
    change ‖paperFT (jointDilatedProfile f.1.1 W) (ξ:ℂ)‖^2 = _
    rw [jointDilatedProfile_paperFT f.1.1 hW, norm_smul,
      Real.norm_eq_abs, abs_of_pos hW, mul_pow, Complex.ofReal_mul]
  have hbound : ∀ᵐ ξ : ℝ, ‖ρ ξ*(EF.gammaBracket ξ+Real.log W)‖ ≤ d ξ := by
    filter_upwards [volume.ae_ne (0:ℝ)] with ξ hξ
    have hv : W*ξ ≠ 0 := mul_ne_zero hW.ne' hξ
    have hb := joint_gamma_scaled_abs hW hW1 hv
    have he : W*ξ/W=ξ := by field_simp
    rw [he] at hb
    have hr := joint_cluster_density_le fw L ξ
    change ρ ξ ≤ 4*‖paperFT fw.1.1 (ξ:ℂ)‖^2 at hr
    rw [hs] at hr
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
    calc
      _ ≤ ρ ξ*jointSeedLogWeight (W*ξ) := mul_le_mul_of_nonneg_left hb (sq_nonneg _)
      _ ≤ (4*(W^2*‖paperFT f.1.1 ((W*ξ:ℝ):ℂ)‖^2))*jointSeedLogWeight (W*ξ) :=
        mul_le_mul_of_nonneg_right hr (jointSeedLogWeight_nonneg _)
      _ = _ := by dsimp [d,q]; ring
  have hi := norm_integral_le_of_norm_le hd hbound
  rw [Real.norm_eq_abs] at hi
  have hm := LebesgueAtomWeil.integral_norm_sq_paperFT_eq g.1.2.1 g.1.2.2
  have hsplit : (∫ ξ, ρ ξ*(EF.gammaBracket ξ+Real.log W)) =
      (∫ ξ, ρ ξ*EF.gammaBracket ξ)+(∫ ξ, ρ ξ)*Real.log W := by
    simp_rw [mul_add]
    rw [integral_add hρg (hρ.mul_const (Real.log W)), integral_mul_const]
  have he : testGamma g.1.1+testMass g.1.1*Real.log W =
      (1/(2*Real.pi))*∫ ξ, ρ ξ*(EF.gammaBracket ξ+Real.log W) := by
    unfold testGamma
    change (1/(2*Real.pi))*(∫ ξ, ρ ξ*EF.gammaBracket ξ)+testMass g.1.1*Real.log W = _
    rw [hsplit, mul_add, ← mul_assoc, hm]
    rfl
  change |testGamma g.1.1+testMass g.1.1*Real.log W| ≤ _
  rw [he, abs_mul, abs_of_pos (by positivity : 0<1/(2*Real.pi))]
  have hn : (1/(2*Real.pi))*(∫ ξ, d ξ)=W*jointSeedLogCost f := by
    dsimp [d]
    rw [integral_const_mul, Measure.integral_comp_mul_left q W,
      abs_inv, abs_of_pos hW, smul_eq_mul]
    dsimp [jointSeedLogCost, q]
    field_simp
  exact (mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 1/(2*Real.pi))).trans_eq hn

/-- Disjoint actual clusters have twice the base physical mass. -/
theorem joint_cluster_testMass (f : JointSmoothTest) {L W : ℝ}
    (hf : tsupport f.1.1 ⊆ Icc 0 W) (hWL : W < L) (hL : 0 ≤ L) :
    testMass (clusterDifference f.1.1 L)=2*testMass f.1.1 := by
  have h := joint_pair_testMass f hf hWL hL 0
  simpa [cosineProfile, sineProfile, clusterDifference, testMass] using h

/-- The seed's leading Gamma coefficient is exactly twice its dilated base mass. -/
theorem joint_cluster_gamma_scale_mass_bound (f : JointSmoothTest)
    (hf : tsupport f.1.1 ⊆ Icc 0 1) {L W : ℝ}
    (hW : 0 < W) (hW1 : W ≤ 1) (hWL : W < L) :
    |testGamma (clusterDifference (jointDilatedProfile f.1.1 W) L) +
        2*W*testMass f.1.1*Real.log W| ≤ W*jointSeedLogCost f := by
  have h := joint_cluster_gamma_scale_bound f hW hW1 L
  have hm := joint_cluster_testMass (jointDilatedTest f W hW)
    (jointDilatedProfile_support hf hW) hWL (by linarith)
  change testMass (clusterDifference (jointDilatedProfile f.1.1 W) L)=
    2*testMass (jointDilatedProfile f.1.1 W) at hm
  rw [hm, jointDilatedProfile_mass f.1.1 hW] at h
  simpa only [mul_assoc] using h

end RHTower.WeilWorkPBAP
