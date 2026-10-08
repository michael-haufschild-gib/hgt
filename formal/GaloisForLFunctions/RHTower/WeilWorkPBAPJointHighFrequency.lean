import GaloisForLFunctions.RHTower.WeilWorkPBAPJointModulation

/-!
# Full paired energy beyond the base Fourier scale

The exact paired mass gives the sharp logarithmic Gamma floor, with only an
inverse-cubic central-mass loss. Both signed pole terms obey a quartic modulation
decay bound in the actual base second derivative. These estimates can be made
uniform for shrinking profiles; no energy sign or nullness premise is used.
The explicit negative-seed width sector is still being assembled separately.
-/

open Complex MeasureTheory Real Set Filter Topology Zeta23
open scoped ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

private theorem high_gamma_integrable (f : JointSmoothTest) :
    Integrable (fun ξ : ℝ => ‖paperFT f.1.1 (ξ:ℂ)‖^2 * EF.gammaBracket ξ) := by
  have h := LebesgueAtomWeil.integrable_paperFT_weilTest_mul_gammaBracket
    f.1.2.1 f.1.2.2 f.1.2.1 f.1.2.2
  refine h.re.congr (Eventually.of_forall fun ξ => ?_)
  change (paperFT (EF.weilTest f.1.1 f.1.1) (ξ:ℂ) *
    (EF.gammaBracket ξ:ℂ)).re = _
  rw [paperFT_weilTest_self_ofReal f.2.continuous f.1.2.2]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

private theorem high_pair_gamma_integrable (f : JointSmoothTest) (L T : ℝ) :
    Integrable (fun ξ => jointPairDensity f L T ξ * EF.gammaBracket ξ) := by
  have h := (high_gamma_integrable (clusterDifferenceTest (cosineProfileTest f T) L)).add
    (high_gamma_integrable (clusterDifferenceTest (sineProfileTest f T) L))
  exact h.congr (Eventually.of_forall fun ξ => by
    change ‖paperFT (clusterDifference (cosineProfile f.1.1 T) L) (ξ:ℂ)‖^2 *
      EF.gammaBracket ξ +
      ‖paperFT (clusterDifference (sineProfile f.1.1 T) L) (ξ:ℂ)‖^2 *
      EF.gammaBracket ξ = jointPairDensity f L T ξ * EF.gammaBracket ξ
    dsimp [jointPairDensity]
    ring)

/-- Literal paired Gamma energy uses the exact paired density. -/
theorem joint_pair_gamma_eq_integral (f : JointSmoothTest) (L T : ℝ) :
    testGamma (clusterDifference (cosineProfile f.1.1 T) L) +
      testGamma (clusterDifference (sineProfile f.1.1 T) L) =
      (1/(2*Real.pi))*∫ ξ, jointPairDensity f L T ξ*EF.gammaBracket ξ := by
  unfold testGamma
  have hc := high_gamma_integrable (clusterDifferenceTest (cosineProfileTest f T) L)
  have hs := high_gamma_integrable (clusterDifferenceTest (sineProfileTest f T) L)
  dsimp only [clusterDifferenceTest, cosineProfileTest, sineProfileTest] at hc hs
  rw [← mul_add, ← integral_add hc hs]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun ξ => by dsimp [jointPairDensity]; ring

/-- Central mass is the only loss from the sharp logarithmic Gamma floor. -/
theorem joint_pair_gamma_central_loss (f : JointSmoothTest) {L W T : ℝ}
    (hf : tsupport f.1.1 ⊆ Icc 0 W) (hWL : W < L) (hL : 0 ≤ L) (hT : 2 ≤ T) :
    2*testMass f.1.1*(Real.log (T/2)-(10+Real.log 4)) -
      (Real.log (T/2)/(2*Real.pi)) *
        (∫ ξ in Ioc (-T/2) (T/2), jointPairDensity f L T ξ) ≤
      testGamma (clusterDifference (cosineProfile f.1.1 T) L) +
        testGamma (clusterDifference (sineProfile f.1.1 T) L) := by
  let S := Ioc (-T/2) (T/2)
  let q := jointPairDensity f L T
  let b := Real.log (T/2)
  let C := 10+Real.log 4
  have hq : Integrable q := jointPairDensity_integrable f L T
  have hqi : Integrable (S.indicator q) := hq.indicator measurableSet_Ioc
  have hg := high_pair_gamma_integrable f L T
  have hp (ξ : ℝ) : q ξ*(b-C)-b*S.indicator q ξ ≤ q ξ*EF.gammaBracket ξ := by
    have hqn : 0 ≤ q ξ := by dsimp [q, jointPairDensity]; positivity
    have hl := joint_gamma_lower_log ξ
    by_cases hξ : ξ ∈ S
    · rw [Set.indicator_of_mem hξ]
      have hn : 0 ≤ Real.log (2+|ξ|) := Real.log_nonneg (by linarith [abs_nonneg ξ])
      have hh := mul_le_mul_of_nonneg_left (show -C ≤ EF.gammaBracket ξ by dsimp [C]; linarith) hqn
      nlinarith
    · rw [Set.indicator_of_notMem hξ]
      have ha : T/2 ≤ |ξ| := by
        change ¬ (-T/2 < ξ ∧ ξ ≤ T/2) at hξ
        by_cases hx : -T/2 < ξ
        · have := lt_of_not_ge (fun h => hξ ⟨hx,h⟩)
          linarith [le_abs_self ξ]
        · have := le_of_not_gt hx
          linarith [neg_le_abs ξ]
      have hh : b ≤ Real.log (2+|ξ|) :=
        Real.log_le_log (by linarith : 0<T/2) (by linarith)
      have hh' := mul_le_mul_of_nonneg_left
        (show b-C ≤ EF.gammaBracket ξ by dsimp [C]; linarith) hqn
      simpa only [mul_zero, sub_zero] using hh'
  have hi := integral_mono ((hq.mul_const (b-C)).sub (hqi.const_mul b)) hg hp
  change (∫ ξ, q ξ*(b-C)-b*S.indicator q ξ) ≤ _ at hi
  rw [integral_sub (hq.mul_const (b-C)) (hqi.const_mul b),
    integral_mul_const, integral_const_mul, integral_indicator measurableSet_Ioc] at hi
  have hi' := mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ 1/(2*Real.pi))
  have hm := jointPairDensity_mass f hf hWL hL T
  rw [joint_pair_gamma_eq_integral]
  have hn : (1/(2*Real.pi))*((∫ ξ, q ξ)*(b-C)-b*∫ ξ in S, q ξ) =
      2*testMass f.1.1*(b-C)-(b/(2*Real.pi))*(∫ ξ in S, q ξ) := by
    calc
      _ = ((1/(2*Real.pi))*(∫ ξ, q ξ))*(b-C)-
        (b/(2*Real.pi))*(∫ ξ in S, q ξ) := by ring
      _ = _ := by rw [hm]
  rw [hn] at hi'
  exact hi'

/-- A width-adapted high-frequency bound with no base logarithmic-moment loss. -/
theorem joint_pair_gamma_high_lower (f : JointSmoothTest) {L W T : ℝ}
    (hf : tsupport f.1.1 ⊆ Icc 0 W) (hWL : W < L) (hL : 0 ≤ L) (hT : 2 ≤ T) :
    2*testMass f.1.1*(Real.log (T/2)-(10+Real.log 4)) -
      (Real.log (T/2)/(2*Real.pi)) *
        (64*(∫ u : ℝ, ‖deriv (deriv f.1.1) u‖)^2/T^3) ≤
      testGamma (clusterDifference (cosineProfile f.1.1 T) L) +
        testGamma (clusterDifference (sineProfile f.1.1 T) L) := by
  have hm := jointPairDensity_low_mass f hf L T (by linarith)
  have hb : 0 ≤ Real.log (T/2)/(2*Real.pi) :=
    div_nonneg (Real.log_nonneg (by linarith)) (by positivity)
  exact (sub_le_sub_left (mul_le_mul_of_nonneg_left hm hb) _).trans
    (joint_pair_gamma_central_loss f hf hWL hL hT)

/-- Complex Fourier decay with its real frequency and actual second derivative. -/
theorem joint_paperFT_real_decay (f : JointSmoothTest) {W : ℝ}
    (hf : tsupport f.1.1 ⊆ Icc 0 W) (z : ℂ) :
    ‖paperFT f.1.1 z‖*z.re^2 ≤
      Real.exp (|z.im| *W)*(∫ u : ℝ, ‖deriv (deriv f.1.1) u‖) := by
  have hs : ∀ u, f.1.1 u ≠ 0 → |u| ≤ W := by
    intro u hu
    have hh := hf (subset_tsupport _ hu)
    simpa only [abs_of_nonneg hh.1] using hh.2
  have hn : z.re^2 ≤ ‖z‖^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg z.im]
  exact (mul_le_mul_of_nonneg_left hn (norm_nonneg _)).trans
    (norm_paperFT_mul_sq_le f.1.2.1 hs z)

private theorem high_vertical_pair (f : JointSmoothTest) {W T : ℝ}
    (hf : tsupport f.1.1 ⊆ Icc 0 W) (hT : T ≠ 0) (z : ℂ) (hz : z.re=0) :
    ‖paperFT f.1.1 (z+T)‖ ≤
      Real.exp (|z.im| *W)*(∫ u : ℝ, ‖deriv (deriv f.1.1) u‖)/T^2 ∧
    ‖paperFT f.1.1 (z-T)‖ ≤
      Real.exp (|z.im| *W)*(∫ u : ℝ, ‖deriv (deriv f.1.1) u‖)/T^2 := by
  have hp := joint_paperFT_real_decay f hf (z+T)
  have hm := joint_paperFT_real_decay f hf (z-T)
  simp only [Complex.add_re, Complex.sub_re, Complex.ofReal_re, hz,
    zero_add, zero_sub, neg_sq, Complex.add_im, Complex.sub_im,
    Complex.ofReal_im, add_zero, sub_zero] at hp hm
  exact ⟨(le_div_iff₀ (sq_pos_of_ne_zero hT)).mpr hp,
    (le_div_iff₀ (sq_pos_of_ne_zero hT)).mpr hm⟩

private theorem high_cosine_vertical (f : JointSmoothTest) {W T : ℝ}
    (hf : tsupport f.1.1 ⊆ Icc 0 W) (hT : T ≠ 0) (z : ℂ) (hz : z.re=0) :
    ‖paperFT (cosineProfile f.1.1 T) z‖ ≤
      Real.exp (|z.im| *W)*(∫ u : ℝ, ‖deriv (deriv f.1.1) u‖)/T^2 := by
  obtain ⟨hp, hm⟩ := high_vertical_pair f hf hT z hz
  rw [paperFT_cosineProfile f.2.continuous f.1.2.2, norm_div, Complex.norm_ofNat]
  have hn := norm_add_le (paperFT f.1.1 (z+T)) (paperFT f.1.1 (z-T))
  linarith

private theorem high_sine_vertical (f : JointSmoothTest) {W T : ℝ}
    (hf : tsupport f.1.1 ⊆ Icc 0 W) (hT : T ≠ 0) (z : ℂ) (hz : z.re=0) :
    ‖paperFT (sineProfile f.1.1 T) z‖ ≤
      Real.exp (|z.im| *W)*(∫ u : ℝ, ‖deriv (deriv f.1.1) u‖)/T^2 := by
  obtain ⟨hp, hm⟩ := high_vertical_pair f hf hT z hz
  rw [paperFT_sineProfile f.2.continuous f.1.2.2,
    norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
  have hn := norm_sub_le (paperFT f.1.1 (z-T)) (paperFT f.1.1 (z+T))
  linarith

private theorem high_cluster_factor (L : ℝ) (z : ℂ) :
    ‖1-Complex.exp (I*z*L)‖ ≤ 1+Real.exp (-z.im*L) := by
  calc
    _ ≤ ‖(1:ℂ)‖+‖Complex.exp (I*z*L)‖ := norm_sub_le _ _
    _ = _ := by rw [norm_one, Complex.norm_exp]; congr 2; simp [Complex.mul_re]

private theorem high_cosine_pole (f : JointSmoothTest) {W T : ℝ}
    (hf : tsupport f.1.1 ⊆ Icc 0 W) (hT : T ≠ 0) (L : ℝ) (z : ℂ) (hz : z.re=0) :
    ‖paperFT (clusterDifference (cosineProfile f.1.1 T) L) z‖ ≤
      (1+Real.exp (-z.im*L)) *
        (Real.exp (|z.im| *W)*(∫ u : ℝ, ‖deriv (deriv f.1.1) u‖)/T^2) := by
  rw [paperFT_clusterDifference (contDiff_cosineProfile f.2 T).continuous
    (hasCompactSupport_cosineProfile f.1.2.2 T), norm_mul]
  exact mul_le_mul (high_cluster_factor L z) (high_cosine_vertical f hf hT z hz)
    (norm_nonneg _) (by positivity)

private theorem high_sine_pole (f : JointSmoothTest) {W T : ℝ}
    (hf : tsupport f.1.1 ⊆ Icc 0 W) (hT : T ≠ 0) (L : ℝ) (z : ℂ) (hz : z.re=0) :
    ‖paperFT (clusterDifference (sineProfile f.1.1 T) L) z‖ ≤
      (1+Real.exp (-z.im*L)) *
        (Real.exp (|z.im| *W)*(∫ u : ℝ, ‖deriv (deriv f.1.1) u‖)/T^2) := by
  rw [paperFT_clusterDifference (contDiff_sineProfile f.2 T).continuous
    (hasCompactSupport_sineProfile f.1.2.2 T), norm_mul]
  exact mul_le_mul (high_cluster_factor L z) (high_sine_vertical f hf hT z hz)
    (norm_nonneg _) (by positivity)

private theorem high_abs_testPole (g : JointSmoothTest) :
    |testPole g.1.1| ≤ 2*‖paperFT g.1.1 (I/2)‖*‖paperFT g.1.1 (-I/2)‖ := by
  have hp := EF.paperFT_weilTest g.2.continuous g.2.continuous g.1.2.2 g.1.2.2 (I/2)
  have hm := EF.paperFT_weilTest g.2.continuous g.2.continuous g.1.2.2 g.1.2.2 (-I/2)
  have hcp : conj (I/2:ℂ) = -I/2 := by
    simp only [map_div₀, map_ofNat, Complex.conj_I]
  have hcm : conj (-I/2:ℂ) = I/2 := by
    simp only [map_div₀, map_ofNat, map_neg, Complex.conj_I, neg_neg]
  rw [hcp] at hp
  rw [hcm] at hm
  unfold testPole
  rw [hp, hm, Complex.add_re]
  calc
    _ ≤ |(paperFT g.1.1 (I/2)*conj (paperFT g.1.1 (-I/2))).re| +
        |(paperFT g.1.1 (-I/2)*conj (paperFT g.1.1 (I/2))).re| := abs_add_le _ _
    _ ≤ ‖paperFT g.1.1 (I/2)*conj (paperFT g.1.1 (-I/2))‖ +
        ‖paperFT g.1.1 (-I/2)*conj (paperFT g.1.1 (I/2))‖ :=
      add_le_add (Complex.abs_re_le_norm _) (Complex.abs_re_le_norm _)
    _ = _ := by simp only [norm_mul, Complex.norm_conj]; ring

/-- Both signed poles decay quartically under modulation, with an explicit width cost. -/
theorem joint_pair_poles_high_abs (f : JointSmoothTest) {W T : ℝ}
    (hf : tsupport f.1.1 ⊆ Icc 0 W) (hT : T ≠ 0) (L : ℝ) :
    |testPole (clusterDifference (cosineProfile f.1.1 T) L) +
      testPole (clusterDifference (sineProfile f.1.1 T) L)| ≤
      4*(1+Real.exp (L/2))*(1+Real.exp (-L/2))*
        (Real.exp (W/2)*(∫ u : ℝ, ‖deriv (deriv f.1.1) u‖)/T^2)^2 := by
  let D := Real.exp (W/2)*(∫ u : ℝ, ‖deriv (deriv f.1.1) u‖)/T^2
  let A := (1+Real.exp (-L/2))*D
  let B := (1+Real.exp (L/2))*D
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hA : 0 ≤ A := mul_nonneg (by positivity) hD
  have hp : ((I/2:ℂ).im) = 1/2 := by norm_num
  have hm : ((-I/2:ℂ).im) = -(1/2) := by norm_num
  have hpr : ((I/2:ℂ).re) = 0 := by norm_num
  have hmr : ((-I/2:ℂ).re) = 0 := by norm_num
  have hcP : ‖paperFT (clusterDifference (cosineProfile f.1.1 T) L) (I/2)‖ ≤ A := by
    simpa only [hp, abs_of_pos (by norm_num : (0:ℝ)<1/2),
      show -(1/2:ℝ)*L = -L/2 by ring, show (1/2:ℝ)*W=W/2 by ring, A, D]
      using high_cosine_pole f hf hT L (I/2) hpr
  have hcM : ‖paperFT (clusterDifference (cosineProfile f.1.1 T) L) (-I/2)‖ ≤ B := by
    simpa only [hm, abs_neg, abs_of_pos (by norm_num : (0:ℝ)<1/2), neg_neg,
      show (1/2:ℝ)*L = L/2 by ring, show (1/2:ℝ)*W=W/2 by ring, B, D]
      using high_cosine_pole f hf hT L (-I/2) hmr
  have hsP : ‖paperFT (clusterDifference (sineProfile f.1.1 T) L) (I/2)‖ ≤ A := by
    simpa only [hp, abs_of_pos (by norm_num : (0:ℝ)<1/2),
      show -(1/2:ℝ)*L = -L/2 by ring, show (1/2:ℝ)*W=W/2 by ring, A, D]
      using high_sine_pole f hf hT L (I/2) hpr
  have hsM : ‖paperFT (clusterDifference (sineProfile f.1.1 T) L) (-I/2)‖ ≤ B := by
    simpa only [hm, abs_neg, abs_of_pos (by norm_num : (0:ℝ)<1/2), neg_neg,
      show (1/2:ℝ)*L = L/2 by ring, show (1/2:ℝ)*W=W/2 by ring, B, D]
      using high_sine_pole f hf hT L (-I/2) hmr
  have hc := (high_abs_testPole (clusterDifferenceTest (cosineProfileTest f T) L)).trans
    (show 2*‖paperFT (clusterDifference (cosineProfile f.1.1 T) L) (I/2)‖*
      ‖paperFT (clusterDifference (cosineProfile f.1.1 T) L) (-I/2)‖ ≤ 2*A*B by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcP (by norm_num)) hcM
        (norm_nonneg _) (mul_nonneg (by norm_num) hA))
  have hs := (high_abs_testPole (clusterDifferenceTest (sineProfileTest f T) L)).trans
    (show 2*‖paperFT (clusterDifference (sineProfile f.1.1 T) L) (I/2)‖*
      ‖paperFT (clusterDifference (sineProfile f.1.1 T) L) (-I/2)‖ ≤ 2*A*B by
      exact mul_le_mul (mul_le_mul_of_nonneg_left hsP (by norm_num)) hsM
        (norm_nonneg _) (mul_nonneg (by norm_num) hA))
  calc
    _ ≤ |testPole (clusterDifference (cosineProfile f.1.1 T) L)| +
        |testPole (clusterDifference (sineProfile f.1.1 T) L)| := abs_add_le _ _
    _ ≤ 2*A*B+2*A*B := add_le_add hc hs
    _ = _ := by dsimp [A,B,D]; ring

/-- Full energy at high positive modulation, with both signed poles retained. -/
theorem joint_pair_full_energy_high_lower (f : JointSmoothTest) {L W T : ℝ}
    (hf : tsupport f.1.1 ⊆ Icc 0 W) (hWL : W < L) (hL : 0 ≤ L) (hT : 2 ≤ T) :
    2*testMass f.1.1*(Real.log (T/2)-(10+Real.log 4)) -
      (Real.log (T/2)/(2*Real.pi)) *
        (64*(∫ u : ℝ, ‖deriv (deriv f.1.1) u‖)^2/T^3) -
      4*(1+Real.exp (L/2))*(1+Real.exp (-L/2))*
        (Real.exp (W/2)*(∫ u : ℝ, ‖deriv (deriv f.1.1) u‖)/T^2)^2 ≤
      jointPairFullEnergy f L T := by
  have hg := joint_pair_gamma_high_lower f hf hWL hL hT
  have hp := (abs_le.mp (joint_pair_poles_high_abs f hf (by linarith : T≠0) L)).1
  have hc := weilArchRe_eq_testPole_add_testGamma
    (clusterDifferenceTest (cosineProfileTest f T) L).1
  have hs := weilArchRe_eq_testPole_add_testGamma
    (clusterDifferenceTest (sineProfileTest f T) L).1
  dsimp only [clusterDifferenceTest, cosineProfileTest, sineProfileTest] at hc hs
  unfold jointPairFullEnergy
  rw [hc, hs]
  linarith

/-- Modulation sign leaves the actual full pair energy unchanged. -/
theorem jointPairFullEnergy_neg (f : JointSmoothTest) {L W : ℝ}
    (hf : tsupport f.1.1 ⊆ Icc 0 W) (hW : 0 < W) (hL : 2*W < L) (T : ℝ) :
    jointPairFullEnergy f L (-T)=jointPairFullEnergy f L T := by
  have hp := jointPairFullEnergy_sub_zero f hf hW hL T
  have hm := jointPairFullEnergy_sub_zero f hf hW hL (-T)
  simp only [neg_mul, Real.cos_neg] at hm
  linarith

end RHTower.WeilWorkPBAP
