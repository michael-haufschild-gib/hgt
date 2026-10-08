import GaloisForLFunctions.RHTower.WeilWorkPBAPJointProfiles

/-!
# Exact Fourier density and central-band decay of broad modulation pairs

Cosine/sine modulation gives two exact frequency translates at every complex
Fourier argument. The two-cluster difference retains its common interference
factor. On the real axis this gives an explicit inverse-quartic pointwise
bound in the central band, using only the base profile's second derivative.
These identities include the pole arguments but do not assert an energy sign.
-/

open Complex MeasureTheory Zeta23
open scoped ComplexConjugate ContDiff
noncomputable section
namespace RHTower.WeilWorkPBAP

private theorem integrable_joint_transform {β : ℝ → ℂ} (hc : Continuous β)
    (hs : HasCompactSupport β) (z : ℂ) :
    Integrable (fun u : ℝ => β u * Complex.exp (I*z*u)) :=
  (hc.mul (Complex.continuous_exp.comp (by fun_prop))).integrable_of_hasCompactSupport
    hs.mul_right

/-- Exact positive and negative frequency translates of a cosine modulation. -/
theorem paperFT_cosineProfile {β : ℝ → ℂ} (hc : Continuous β)
    (hs : HasCompactSupport β) (T : ℝ) (z : ℂ) :
    paperFT (cosineProfile β T) z = (paperFT β (z+T)+paperFT β (z-T))/2 := by
  rw [paperFT_def, paperFT_def, paperFT_def,
    ← integral_add (integrable_joint_transform hc hs (z+T)) (integrable_joint_transform hc hs (z-T)),
    ← integral_div]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    simp only [cosineProfile, Complex.ofReal_cos, Complex.cos, Complex.ofReal_mul]
    rw [show I*(z+T)*u = (T:ℂ)*u*I+I*z*u by ring,
      show I*(z-T)*u = -((T:ℂ)*u)*I+I*z*u by ring,
      Complex.exp_add, Complex.exp_add]
    ring

/-- Exact positive and negative frequency translates of a sine modulation. -/
theorem paperFT_sineProfile {β : ℝ → ℂ} (hc : Continuous β)
    (hs : HasCompactSupport β) (T : ℝ) (z : ℂ) :
    paperFT (sineProfile β T) z = (paperFT β (z-T)-paperFT β (z+T))*I/2 := by
  rw [paperFT_def, paperFT_def, paperFT_def,
    ← integral_sub (integrable_joint_transform hc hs (z-T)) (integrable_joint_transform hc hs (z+T)),
    ← integral_mul_const, ← integral_div]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    simp only [sineProfile, Complex.ofReal_sin, Complex.sin, Complex.ofReal_mul]
    rw [show I*(z+T)*u = (T:ℂ)*u*I+I*z*u by ring,
      show I*(z-T)*u = -((T:ℂ)*u)*I+I*z*u by ring,
      Complex.exp_add, Complex.exp_add]
    ring

/-- Translation interference remains as its exact Fourier multiplier. -/
theorem paperFT_clusterDifference {β : ℝ → ℂ} (hc : Continuous β)
    (hs : HasCompactSupport β) (L : ℝ) (z : ℂ) :
    paperFT (clusterDifference β L) z = (1-Complex.exp (I*z*L))*paperFT β z := by
  have he : (fun u : ℝ => clusterDifference β L u * Complex.exp (I*z*u)) =
      (fun u : ℝ => β u*Complex.exp (I*z*u) - β (u-L)*Complex.exp (I*z*u)) := by
    funext u
    simp only [clusterDifference, sub_mul]
  have ht : Integrable (fun u : ℝ => β (u-L)*Complex.exp (I*z*u)) :=
    integrable_joint_transform (β := fun u : ℝ => β (u-L))
      (hc.comp (continuous_id.sub continuous_const))
      (hs.comp_homeomorph (Homeomorph.subRight L)) z
  rw [paperFT_def, he, integral_sub (integrable_joint_transform hc hs z) ht]
  change paperFT β z - paperFT (fun u => β (u-L)) z = _
  rw [paperFT_translate']
  ring

/-- Pairing removes modulation cross terms, including at the complex pole arguments. -/
theorem normSq_paperFT_cosine_sine {β : ℝ → ℂ} (hc : Continuous β)
    (hs : HasCompactSupport β) (T : ℝ) (z : ℂ) :
    ‖paperFT (cosineProfile β T) z‖^2 + ‖paperFT (sineProfile β T) z‖^2 =
      (‖paperFT β (z+T)‖^2 + ‖paperFT β (z-T)‖^2)/2 := by
  rw [paperFT_cosineProfile hc hs, paperFT_sineProfile hc hs]
  simp only [norm_div, norm_mul, Complex.norm_I, mul_one, norm_ofNat]
  have h := parallelogram_law_with_norm ℂ (paperFT β (z+T)) (paperFT β (z-T))
  rw [norm_sub_rev (paperFT β (z-T)) (paperFT β (z+T))]
  nlinarith

/-- Exact paired two-cluster Fourier density with its common interference factor. -/
theorem normSq_paperFT_joint_pair (f : JointSmoothTest) (L T : ℝ) (z : ℂ) :
    ‖paperFT (clusterDifference (cosineProfile f.1.1 T) L) z‖^2 +
      ‖paperFT (clusterDifference (sineProfile f.1.1 T) L) z‖^2 =
      ‖1-Complex.exp (I*z*L)‖^2 *
        (‖paperFT f.1.1 (z+T)‖^2 + ‖paperFT f.1.1 (z-T)‖^2)/2 := by
  rw [paperFT_clusterDifference (contDiff_cosineProfile f.2 T).continuous
      (hasCompactSupport_cosineProfile f.1.2.2 T),
    paperFT_clusterDifference (contDiff_sineProfile f.2 T).continuous
      (hasCompactSupport_sineProfile f.1.2.2 T)]
  simp only [norm_mul, mul_pow]
  rw [← mul_add, normSq_paperFT_cosine_sine f.2.continuous f.1.2.2]
  ring

/-- Uniform pointwise control keeps the exact translation interference factor. -/
theorem joint_pair_real_density_le (f : JointSmoothTest) (L T ξ : ℝ) :
    ‖paperFT (clusterDifference (cosineProfile f.1.1 T) L) (ξ:ℂ)‖^2 +
      ‖paperFT (clusterDifference (sineProfile f.1.1 T) L) (ξ:ℂ)‖^2 ≤
      2*(‖paperFT f.1.1 (ξ+T:ℝ)‖^2 + ‖paperFT f.1.1 (ξ-T:ℝ)‖^2) := by
  rw [normSq_paperFT_joint_pair]
  have he : ‖Complex.exp (I*(ξ:ℂ)*L)‖ = 1 := by
    rw [show I*(ξ:ℂ)*L = ((ξ*L:ℝ):ℂ)*I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hb : ‖1-Complex.exp (I*(ξ:ℂ)*L)‖ ≤ 2 := by
    calc _ ≤ ‖(1:ℂ)‖+‖Complex.exp (I*(ξ:ℂ)*L)‖ := norm_sub_le _ _
         _ = 2 := by rw [he, norm_one]; ring
  have hb2 : ‖1-Complex.exp (I*(ξ:ℂ)*L)‖^2 ≤ 4 := by
    nlinarith [norm_nonneg (1-Complex.exp (I*(ξ:ℂ)*L))]
  have hh := mul_le_mul_of_nonneg_right hb2
    (add_nonneg (sq_nonneg ‖paperFT f.1.1 ((ξ:ℂ)+T)‖)
      (sq_nonneg ‖paperFT f.1.1 ((ξ:ℂ)-T)‖))
  push_cast
  nlinarith

/-- Twice-integrated Fourier decay forces paired mass out of every central band. -/
theorem joint_pair_density_central_bound (f : JointSmoothTest) {W : ℝ}
    (hf : tsupport f.1.1 ⊆ Set.Icc 0 W) (L T : ℝ) (hT : 0 < T)
    (ξ : ℝ) (hξ : |ξ| ≤ T/2) :
    ‖paperFT (clusterDifference (cosineProfile f.1.1 T) L) (ξ:ℂ)‖^2 +
      ‖paperFT (clusterDifference (sineProfile f.1.1 T) L) (ξ:ℂ)‖^2 ≤
      64*(∫ u : ℝ, ‖deriv (deriv f.1.1) u‖)^2/T^4 := by
  let B : ℝ := ∫ u : ℝ, ‖deriv (deriv f.1.1) u‖
  have hB : 0 ≤ B := integral_nonneg fun _ => norm_nonneg _
  have hs : ∀ u, f.1.1 u ≠ 0 → |u| ≤ W := by
    intro u hu
    have hh := hf (subset_tsupport _ hu)
    simpa only [abs_of_nonneg hh.1] using hh.2
  have hd : ∀ s : ℝ, ‖paperFT f.1.1 (s:ℂ)‖*s^2 ≤ B := by
    intro s
    have hh := norm_paperFT_mul_sq_le f.1.2.1 hs (s:ℂ)
    simpa only [Complex.ofReal_im, abs_zero, zero_mul, Real.exp_zero, one_mul,
      Complex.norm_real, Real.norm_eq_abs, sq_abs] using hh
  have hb : ∀ s : ℝ, (T/2)^2 ≤ s^2 → ‖paperFT f.1.1 (s:ℂ)‖ ≤ 4*B/T^2 := by
    intro s hsq
    have hh := (mul_le_mul_of_nonneg_left hsq (norm_nonneg (paperFT f.1.1 (s:ℂ)))).trans (hd s)
    apply (le_div_iff₀ (sq_pos_of_pos hT)).mpr
    nlinarith
  have hp := hb (ξ+T) (by
    have hh : T/2 ≤ |ξ+T| := by linarith [(abs_le.mp hξ).1, le_abs_self (ξ+T)]
    simpa only [sq_abs] using (sq_le_sq₀ (by positivity) (abs_nonneg (ξ+T))).mpr hh)
  have hm := hb (ξ-T) (by
    have hh : T/2 ≤ |ξ-T| := by linarith [(abs_le.mp hξ).2, neg_le_abs (ξ-T)]
    simpa only [sq_abs] using (sq_le_sq₀ (by positivity) (abs_nonneg (ξ-T))).mpr hh)
  have hp2 : ‖paperFT f.1.1 (ξ+T:ℝ)‖^2 ≤ (4*B/T^2)^2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hp
  have hm2 : ‖paperFT f.1.1 (ξ-T:ℝ)‖^2 ≤ (4*B/T^2)^2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hm
  calc _ ≤ 2*(‖paperFT f.1.1 (ξ+T:ℝ)‖^2+‖paperFT f.1.1 (ξ-T:ℝ)‖^2) :=
      joint_pair_real_density_le f L T ξ
    _ ≤ 4*(4*B/T^2)^2 := by linarith
    _ = _ := by dsimp [B]; ring

end RHTower.WeilWorkPBAP
