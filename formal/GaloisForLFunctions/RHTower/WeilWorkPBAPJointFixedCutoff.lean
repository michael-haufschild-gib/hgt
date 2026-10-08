import GaloisForLFunctions.RHTower.WeilWorkPBAPJointLogQuadrature
import GaloisForLFunctions.RHTower.ConstrainedWeilPlateauProfile
import Mathlib.Analysis.Calculus.Deriv.Support
import Zeta23.Poisson.PaperFT

/-!
# Uniform pole-weighted plateau cutoff

The literal even plateau equals one on the correlation window. Its
normalized hyperbolic weight has uniform first and second derivative
bounds, independent of the window center. The exact leading integral
has a quadratic width error, and its complex Fourier integral has
inverse-square decay. Every derivative cost belongs to this fixed
auxiliary cutoff; no source-profile regularity budget is assumed.
-/

open Real Set MeasureTheory Topology
open scoped ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP

/-- A literal even plateau: one on `[-1,1]`, supported in `[-2,2]`. -/
def jointPlateau (y : ℝ) : ℝ := plateauBump 4 (y+2)

theorem jointPlateau_contDiff : ContDiff ℝ ∞ jointPlateau :=
  (plateauBump_contDiff 4).comp (contDiff_id.add contDiff_const)

theorem jointPlateau_nonneg (y : ℝ) : 0 ≤ jointPlateau y := plateauBump_nonneg _ _

theorem jointPlateau_le_one (y : ℝ) : jointPlateau y ≤ 1 := plateauBump_le_one _ _

theorem jointPlateau_even (y : ℝ) : jointPlateau (-y) = jointPlateau y := by
  unfold jointPlateau plateauBump
  have h1 : 4-(-y+2) = y+2 := by ring
  have h2 : 4-(y+2) = -y+2 := by ring
  rw [h1, h2, mul_comm]

theorem jointPlateau_eq_one {y : ℝ} (hy : |y| ≤ 1) : jointPlateau y = 1 := by
  apply plateauBump_eq_one <;> have h := abs_le.mp hy <;> linarith

theorem jointPlateau_support : Function.support jointPlateau ⊆ Icc (-2) 2 := by
  intro y hy
  have h := plateauBump_support_subset 4 (show y+2 ∈ Function.support (plateauBump 4) from hy)
  constructor <;> linarith [h.1, h.2]

theorem jointPlateau_hasCompactSupport : HasCompactSupport jointPlateau :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc jointPlateau_support

theorem jointPlateau_derivative_bounds :
    ∃ C₁ > 0, ∃ C₂ > 0, (∀ y, |deriv jointPlateau y| ≤ C₁) ∧
      (∀ y, |deriv (deriv jointPlateau) y| ≤ C₂) := by
  have hd := (contDiff_infty_iff_deriv.mp jointPlateau_contDiff).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  obtain ⟨C₁, hC₁, h₁⟩ := Bornology.IsBounded.exists_pos_norm_le (E := ℝ)
    (jointPlateau_hasCompactSupport.deriv.isCompact_range hd.continuous).isBounded
  obtain ⟨C₂, hC₂, h₂⟩ := Bornology.IsBounded.exists_pos_norm_le (E := ℝ)
    (jointPlateau_hasCompactSupport.deriv.deriv.isCompact_range hdd.continuous).isBounded
  exact ⟨C₁, hC₁, C₂, hC₂, fun y => h₁ _ ⟨y,rfl⟩, fun y => h₂ _ ⟨y,rfl⟩⟩

/-- The pole weight normalized at the window center. -/
def jointCoshRatio (L y : ℝ) : ℝ := cosh ((L+y)/2)/cosh (L/2)

private theorem abs_sinh_le_cosh (x : ℝ) : |sinh x| ≤ cosh x := by
  rw [Real.abs_sinh, ← Real.cosh_abs]
  exact (Real.sinh_lt_cosh (x := |x|)).le

theorem jointCoshRatio_pos (L y : ℝ) : 0 < jointCoshRatio L y :=
  div_pos (cosh_pos _) (cosh_pos _)

theorem jointCoshRatio_le (L y : ℝ) : jointCoshRatio L y ≤ exp (|y|/2) := by
  unfold jointCoshRatio
  apply (div_le_iff₀ (cosh_pos _)).mpr
  have h : sinh (L/2)*sinh (y/2) ≤ cosh (L/2)*|sinh (y/2)| :=
    (le_abs_self _).trans (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_sinh_le_cosh _) (abs_nonneg _))
  rw [add_div, cosh_add]
  have he : cosh (y/2)+|sinh (y/2)| = exp (|y|/2) := by
    rw [Real.abs_sinh, ← Real.cosh_abs, cosh_add_sinh, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)]
  nlinarith [cosh_pos (L/2)]

theorem jointCoshRatio_hasDerivAt (L y : ℝ) :
    HasDerivAt (jointCoshRatio L) (sinh ((L+y)/2)/(2*cosh (L/2))) y := by
  have h := ((Real.hasDerivAt_cosh ((L+y)/2)).comp y
    (((hasDerivAt_id y).const_add L).div_const 2)).div_const (cosh (L/2))
  convert h using 1 <;> try rfl
  ring

theorem jointCoshRatio_deriv_le (L y : ℝ) :
    |deriv (jointCoshRatio L) y| ≤ exp (|y|/2)/2 := by
  rw [(jointCoshRatio_hasDerivAt L y).deriv, abs_div,
    abs_of_pos (mul_pos (by norm_num) (cosh_pos _))]
  calc
    _ ≤ cosh ((L+y)/2)/(2*cosh (L/2)) :=
      div_le_div_of_nonneg_right (abs_sinh_le_cosh _) (by positivity)
    _ = jointCoshRatio L y / 2 := by unfold jointCoshRatio; ring
    _ ≤ _ := div_le_div_of_nonneg_right (jointCoshRatio_le L y) (by norm_num)

theorem jointCoshRatio_deriv_hasDerivAt (L y : ℝ) :
    HasDerivAt (deriv (jointCoshRatio L)) (jointCoshRatio L y/4) y := by
  have he : deriv (jointCoshRatio L) = fun u => sinh ((L+u)/2)/(2*cosh (L/2)) :=
    funext fun u => (jointCoshRatio_hasDerivAt L u).deriv
  rw [he]
  have h := ((Real.hasDerivAt_sinh ((L+y)/2)).comp y
    (((hasDerivAt_id y).const_add L).div_const 2)).div_const (2*cosh (L/2))
  convert h using 1 <;> try rfl
  unfold jointCoshRatio
  ring

theorem jointCoshRatio_contDiff (L : ℝ) : ContDiff ℝ ∞ (jointCoshRatio L) :=
  (Real.contDiff_cosh.comp ((contDiff_const.add contDiff_id).div_const 2)).div_const _

/-- A fixed auxiliary cutoff carrying the entire pole weight. -/
def jointFixedCutoff (L W y : ℝ) : ℝ := jointPlateau (y/W)*jointCoshRatio L y

theorem jointFixedCutoff_contDiff (L W : ℝ) : ContDiff ℝ ∞ (jointFixedCutoff L W) :=
  (jointPlateau_contDiff.comp (contDiff_id.div_const W)).mul (jointCoshRatio_contDiff L)

theorem jointFixedCutoff_nonneg (L W y : ℝ) : 0 ≤ jointFixedCutoff L W y :=
  mul_nonneg (jointPlateau_nonneg _) (jointCoshRatio_pos _ _).le

theorem jointFixedCutoff_eq_ratio {L W y : ℝ} (hW : 0 < W) (hy : |y| ≤ W) :
    jointFixedCutoff L W y = jointCoshRatio L y := by
  have h : |y/W| ≤ 1 := by
    rw [abs_div, abs_of_pos hW, div_le_one hW]
    exact hy
  simp only [jointFixedCutoff, jointPlateau_eq_one h, one_mul]

theorem jointFixedCutoff_tsupport {L W : ℝ} (hW : 0 < W) :
    tsupport (jointFixedCutoff L W) ⊆ Icc (-2*W) (2*W) := by
  apply closure_minimal _ isClosed_Icc
  intro y hy
  have hp : jointPlateau (y/W) ≠ 0 := by
    intro h
    exact hy (by simp only [jointFixedCutoff, h, zero_mul])
  have h := jointPlateau_support hp
  exact ⟨by nlinarith [(le_div_iff₀ hW).mp h.1],
    by nlinarith [(div_le_iff₀ hW).mp h.2]⟩

theorem jointFixedCutoff_hasCompactSupport {L W : ℝ} (hW : 0 < W) :
    HasCompactSupport (jointFixedCutoff L W) :=
  isCompact_Icc.of_isClosed_subset isClosed_closure (jointFixedCutoff_tsupport hW)

theorem jointFixedCutoff_hasDerivAt (L W y : ℝ) :
    HasDerivAt (jointFixedCutoff L W)
      (deriv jointPlateau (y/W)/W*jointCoshRatio L y+
        jointPlateau (y/W)*deriv (jointCoshRatio L) y) y := by
  have hp := ((contDiff_infty_iff_deriv.mp jointPlateau_contDiff).1 (y/W)).hasDerivAt
  have hr := (jointCoshRatio_hasDerivAt L y).differentiableAt.hasDerivAt
  convert (hp.comp y ((hasDerivAt_id y).div_const W)).mul hr using 1 <;> try rfl
  dsimp only [Function.comp_apply, id_eq]
  ring

theorem jointFixedCutoff_deriv_hasDerivAt (L W y : ℝ) :
    HasDerivAt (deriv (jointFixedCutoff L W))
      (deriv (deriv jointPlateau) (y/W)/W^2*jointCoshRatio L y+
        2*(deriv jointPlateau (y/W)/W)*deriv (jointCoshRatio L) y+
        jointPlateau (y/W)*(jointCoshRatio L y/4)) y := by
  have he : deriv (jointFixedCutoff L W) = fun u =>
      deriv jointPlateau (u/W)/W*jointCoshRatio L u+
        jointPlateau (u/W)*deriv (jointCoshRatio L) u :=
    funext fun u => (jointFixedCutoff_hasDerivAt L W u).deriv
  rw [he]
  have hd := contDiff_infty_iff_deriv.mp jointPlateau_contDiff
  have hp := (hd.1 (y/W)).hasDerivAt.comp y ((hasDerivAt_id y).div_const W)
  have hdp := (((contDiff_infty_iff_deriv.mp hd.2).1 (y/W)).hasDerivAt.comp y
    ((hasDerivAt_id y).div_const W)).div_const W
  have hr := (jointCoshRatio_hasDerivAt L y).differentiableAt.hasDerivAt
  convert (hdp.mul hr).add (hp.mul (jointCoshRatio_deriv_hasDerivAt L y)) using 1 <;> try rfl
  dsimp only [Function.comp_apply, id_eq]
  ring

private theorem ratio_window_bounds {L W y : ℝ} (_hW : 0 < W) (hW1 : W ≤ 1)
    (hy : y ∈ Icc (-2*W) (2*W)) :
    jointCoshRatio L y ≤ exp 1 ∧ |deriv (jointCoshRatio L) y| ≤ exp 1/2 := by
  have habs : |y|/2 ≤ 1 := by
    have h : |y| ≤ 2*W := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩
    linarith
  exact ⟨(jointCoshRatio_le L y).trans (exp_le_exp.mpr habs),
    (jointCoshRatio_deriv_le L y).trans
      (div_le_div_of_nonneg_right (exp_le_exp.mpr habs) (by norm_num))⟩

/-- One constant works for every center and every width at most one. -/
theorem jointFixedCutoff_uniform_bounds :
    ∃ C > 0, ∀ (L W : ℝ), 0 < W → W ≤ 1 → ∀ y,
      |jointFixedCutoff L W y| ≤ C ∧
      |deriv (jointFixedCutoff L W) y| ≤ C/W ∧
      |deriv (deriv (jointFixedCutoff L W)) y| ≤ C/W^2 := by
  obtain ⟨C₁, hC₁, C₂, hC₂, hb₁, hb₂⟩ := jointPlateau_derivative_bounds
  let C := exp 1*(C₁+C₂+1)
  have hC : 0 < C := mul_pos (exp_pos _) (by linarith)
  have heC : exp 1 ≤ C := by dsimp only [C]; nlinarith [exp_pos 1]
  refine ⟨C, hC, ?_⟩
  intro L W hW hW1 y
  by_cases hy : y ∈ Icc (-2*W) (2*W)
  · obtain ⟨hr, hdr⟩ := ratio_window_bounds (L := L) hW hW1 hy
    have hp := jointPlateau_le_one (y/W)
    have hp0 := jointPlateau_nonneg (y/W)
    have hr0 := (jointCoshRatio_pos L y).le
    have hv : |jointFixedCutoff L W y| ≤ exp 1 := by
      rw [abs_of_nonneg (jointFixedCutoff_nonneg L W y)]
      exact (mul_le_mul_of_nonneg_right hp hr0).trans (by simpa only [one_mul] using hr)
    have hd : |deriv (jointFixedCutoff L W) y| ≤ C₁/W*exp 1+exp 1/2 := by
      rw [(jointFixedCutoff_hasDerivAt L W y).deriv]
      calc
        _ ≤ |deriv jointPlateau (y/W)/W*jointCoshRatio L y|+
            |jointPlateau (y/W)*deriv (jointCoshRatio L) y| := abs_add_le _ _
        _ = |deriv jointPlateau (y/W)|/W*jointCoshRatio L y+
            jointPlateau (y/W)*|deriv (jointCoshRatio L) y| := by
          rw [abs_mul, abs_mul, abs_div, abs_of_pos hW, abs_of_nonneg hp0, abs_of_nonneg hr0]
        _ ≤ C₁/W*exp 1+1*(exp 1/2) := by gcongr; exact hb₁ _
        _ = _ := by ring
    have hdd : |deriv (deriv (jointFixedCutoff L W)) y| ≤
        C₂/W^2*exp 1+2*(C₁/W)*(exp 1/2)+exp 1/4 := by
      rw [(jointFixedCutoff_deriv_hasDerivAt L W y).deriv]
      calc
        _ ≤ |deriv (deriv jointPlateau) (y/W)/W^2*jointCoshRatio L y|+
            |2*(deriv jointPlateau (y/W)/W)*deriv (jointCoshRatio L) y|+
            |jointPlateau (y/W)*(jointCoshRatio L y/4)| := by
          exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
        _ = |deriv (deriv jointPlateau) (y/W)|/W^2*jointCoshRatio L y+
            2*(|deriv jointPlateau (y/W)|/W)*|deriv (jointCoshRatio L) y|+
            jointPlateau (y/W)*(jointCoshRatio L y/4) := by
          simp only [abs_mul, abs_div, abs_of_pos hW, abs_of_nonneg (sq_nonneg W),
            abs_of_nonneg hp0, abs_of_nonneg hr0,
            abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
        _ ≤ C₂/W^2*exp 1+2*(C₁/W)*(exp 1/2)+1*(exp 1/4) := by
          gcongr
          · exact hb₂ _
          · exact hb₁ _
        _ = _ := by ring
    refine ⟨hv.trans heC, hd.trans ?_, hdd.trans ?_⟩
    · apply (le_div_iff₀ hW).mpr
      dsimp only [C]
      field_simp
      nlinarith [exp_pos 1]
    · apply (le_div_iff₀ (sq_pos_of_pos hW)).mpr
      dsimp only [C]
      field_simp
      nlinarith [exp_pos 1, sq_nonneg (1-W), mul_nonneg hW.le (sub_nonneg.mpr hW1)]
  · have hn : y ∉ tsupport (jointFixedCutoff L W) :=
      fun h => hy (jointFixedCutoff_tsupport hW h)
    have hz : jointFixedCutoff L W y = 0 := by
      by_contra h
      exact hn (subset_tsupport _ h)
    have hz₁ := deriv_of_notMem_tsupport hn
    have hz₂ := deriv_of_notMem_tsupport (fun h => hn (tsupport_deriv_subset h))
    rw [hz, hz₁, hz₂, abs_zero]
    exact ⟨hC.le, by positivity, by positivity⟩

theorem jointCoshRatio_sub_one_le {L W y : ℝ} (hW : 0 < W) (hW1 : W ≤ 1)
    (hy : |y| ≤ 2*W) : |jointCoshRatio L y-1| ≤ exp 1*W := by
  have hd : ∀ z ∈ Icc (-2*W) (2*W), DifferentiableAt ℝ (jointCoshRatio L) z :=
    fun z _ => (jointCoshRatio_hasDerivAt L z).differentiableAt
  have hb : ∀ z ∈ Icc (-2*W) (2*W), ‖deriv (jointCoshRatio L) z‖ ≤ exp 1/2 :=
    fun _ hz => (ratio_window_bounds hW hW1 hz).2
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hd hb (convex_Icc _ _)
    (show (0:ℝ) ∈ Icc (-2*W) (2*W) by constructor <;> linarith)
    (show y ∈ Icc (-2*W) (2*W) from ⟨by linarith [(abs_le.mp hy).1], (abs_le.mp hy).2⟩)
  have hz : jointCoshRatio L 0 = 1 := by simp only [jointCoshRatio, add_zero, div_self (cosh_pos _).ne']
  rw [hz, Real.norm_eq_abs, Real.norm_eq_abs, sub_zero] at h
  exact h.trans (by nlinarith [exp_pos 1])

theorem jointPlateau_integrable : Integrable jointPlateau :=
  jointPlateau_contDiff.continuous.integrable_of_hasCompactSupport jointPlateau_hasCompactSupport

theorem jointPlateau_integral_bounds :
    2 ≤ ∫ y, jointPlateau y ∧ (∫ y, jointPlateau y) ≤ 4 := by
  have hconst (a b : ℝ) : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Icc a b) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hlo := setIntegral_mono_on (hconst (-1) 1) jointPlateau_integrable.integrableOn
    measurableSet_Icc (fun y hy => (jointPlateau_eq_one (abs_le.mpr hy)).ge)
  have hu := setIntegral_mono_on jointPlateau_integrable.integrableOn (hconst (-2) 2)
    measurableSet_Icc (fun y _ => jointPlateau_le_one y)
  have hre : (∫ y in Icc (-2:ℝ) 2, jointPlateau y) = ∫ y, jointPlateau y := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    by_contra h
    exact hy (jointPlateau_support h)
  have hlall : (∫ y in Icc (-1:ℝ) 1, jointPlateau y) ≤ ∫ y, jointPlateau y :=
    setIntegral_le_integral jointPlateau_integrable (Filter.Eventually.of_forall jointPlateau_nonneg)
  have hc₁ : (∫ _y in Icc (-1:ℝ) 1, (1:ℝ)) = 2 := by
    rw [setIntegral_const]; norm_num [Measure.real, Real.volume_Icc]
  have hc₂ : (∫ _y in Icc (-2:ℝ) 2, (1:ℝ)) = 4 := by
    rw [setIntegral_const]; norm_num [Measure.real, Real.volume_Icc]
  rw [hc₁] at hlo
  rw [hc₂, hre] at hu
  exact ⟨hlo.trans hlall, hu⟩

theorem jointFixedCutoff_integrable (L : ℝ) {W : ℝ} (hW : 0 < W) :
    Integrable (jointFixedCutoff L W) :=
  (jointFixedCutoff_contDiff L W).continuous.integrable_of_hasCompactSupport
    (jointFixedCutoff_hasCompactSupport hW)

/-- The exact leading cutoff mass survives uniformly; its error is quadratic in width. -/
theorem jointFixedCutoff_integral_error (L : ℝ) {W : ℝ} (hW : 0 < W) (hW1 : W ≤ 1) :
    |(∫ y, jointFixedCutoff L W y)-W*(∫ y, jointPlateau y)| ≤ 4*exp 1*W^2 := by
  have hi := jointFixedCutoff_integrable L hW
  have hs : Integrable (fun y => jointPlateau (y/W)) := jointPlateau_integrable.comp_div hW.ne'
  have hscale : (∫ y, jointPlateau (y/W)) = W*(∫ y, jointPlateau y) := by
    rw [Measure.integral_comp_div, abs_of_pos hW, smul_eq_mul]
  have hb (y : ℝ) : |jointFixedCutoff L W y-jointPlateau (y/W)| ≤
      jointPlateau (y/W)*(exp 1*W) := by
    by_cases hp : jointPlateau (y/W) = 0
    · simp only [jointFixedCutoff, hp, zero_mul, sub_zero, abs_zero, le_refl]
    · have hy := jointPlateau_support hp
      have hy' : |y| ≤ 2*W := abs_le.mpr
        ⟨by nlinarith [(le_div_iff₀ hW).mp hy.1], (div_le_iff₀ hW).mp hy.2⟩
      rw [show jointFixedCutoff L W y-jointPlateau (y/W) =
        jointPlateau (y/W)*(jointCoshRatio L y-1) from by unfold jointFixedCutoff; ring,
        abs_mul, abs_of_nonneg (jointPlateau_nonneg _)]
      exact mul_le_mul_of_nonneg_left (jointCoshRatio_sub_one_le hW hW1 hy') (jointPlateau_nonneg _)
  rw [← hscale, ← integral_sub hi hs]
  calc
    _ ≤ ∫ y, |jointFixedCutoff L W y-jointPlateau (y/W)| := by
      simpa only [Real.norm_eq_abs] using
        (norm_integral_le_integral_norm (fun y => jointFixedCutoff L W y-jointPlateau (y/W)))
    _ ≤ ∫ y, jointPlateau (y/W)*(exp 1*W) :=
      integral_mono (hi.sub hs).norm (hs.mul_const _) hb
    _ = W*(∫ y, jointPlateau y)*(exp 1*W) := by rw [integral_mul_const, hscale]
    _ ≤ W*4*(exp 1*W) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left jointPlateau_integral_bounds.2 hW.le) (by positivity)
    _ = _ := by ring

/-- The actual complex Fourier integral has uniform inverse-square decay. -/
theorem jointFixedCutoff_fourier_decay :
    ∃ C > 0, ∀ (L W : ℝ), 0 < W → W ≤ 1 → ∀ t : ℝ,
      ‖∫ y : ℝ, (jointFixedCutoff L W y:ℂ)*Complex.exp (((t*y:ℝ):ℂ)*Complex.I)‖*t^2 ≤ C/W := by
  obtain ⟨C, hC, hb⟩ := jointFixedCutoff_uniform_bounds
  refine ⟨4*C, by positivity, ?_⟩
  intro L W hW hW1 t
  let v := jointFixedCutoff L W
  have hc : ContDiff ℝ ∞ v := jointFixedCutoff_contDiff L W
  have hcs : HasCompactSupport v := jointFixedCutoff_hasCompactSupport hW
  have hd := contDiff_infty_iff_deriv.mp hc
  have hdd := contDiff_infty_iff_deriv.mp hd.2
  have hi : Integrable (deriv (deriv v)) :=
    hdd.2.continuous.integrable_of_hasCompactSupport hcs.deriv.deriv
  have hsub : tsupport (deriv (deriv v)) ⊆ Icc (-2*W) (2*W) :=
    tsupport_deriv_subset.trans (tsupport_deriv_subset.trans (jointFixedCutoff_tsupport hW))
  have hre : (∫ y in Icc (-2*W) (2*W), |deriv (deriv v) y|) =
      ∫ y, |deriv (deriv v) y| := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hz : deriv (deriv v) y = 0 := by
      by_contra h
      exact hy (hsub (subset_tsupport _ h))
    rw [hz, abs_zero]
  have hbint : (∫ y, |deriv (deriv v) y|) ≤ 4*C/W := by
    rw [← hre]
    calc
      _ ≤ ∫ _y in Icc (-2*W) (2*W), C/W^2 := by
        apply setIntegral_mono_on hi.norm.integrableOn
          (integrableOn_const isCompact_Icc.measure_ne_top) measurableSet_Icc
        exact fun y _ => (hb L W hW hW1 y).2.2
      _ = (4*W)*(C/W^2) := by
        rw [setIntegral_const]
        simp only [Measure.real, Real.volume_Icc, smul_eq_mul,
          ENNReal.toReal_ofReal (show 0 ≤ 2*W-(-2*W) by linarith)]
        ring
      _ = _ := by field_simp
  have hdc : deriv (fun y => (v y:ℂ)) = fun y => ((deriv v y:ℝ):ℂ) :=
    funext fun y => (hd.1 y).hasDerivAt.ofReal_comp.deriv
  have hddc : deriv (deriv (fun y => (v y:ℂ))) = fun y => ((deriv (deriv v) y:ℝ):ℂ) := by
    rw [hdc]
    exact funext fun y => (hdd.1 y).hasDerivAt.ofReal_comp.deriv
  have hfc : ContDiff ℝ 2 (fun y => (v y:ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hc.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have hfs (y : ℝ) (hy : (v y:ℂ) ≠ 0) : |y| ≤ 2*W := by
    have h := jointFixedCutoff_tsupport hW
      (subset_tsupport _ (show v y ≠ 0 from fun hz => hy (by simp only [hz, Complex.ofReal_zero])))
    exact abs_le.mpr ⟨by linarith [h.1], h.2⟩
  have he := Zeta23.norm_paperFT_mul_sq_le hfc hfs (t:ℂ)
  rw [hddc] at he
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, Complex.ofReal_im,
    abs_zero, zero_mul, exp_zero, one_mul] at he
  have hform : Zeta23.paperFT (fun y => (v y:ℂ)) (t:ℂ) =
      ∫ y : ℝ, (v y:ℂ)*Complex.exp (((t*y:ℝ):ℂ)*Complex.I) := by
    unfold Zeta23.paperFT
    congr 1; funext y
    congr 1
    congr 1
    push_cast
    ring
  rw [hform] at he
  exact he.trans hbint

end RHTower.WeilWorkPBAP
