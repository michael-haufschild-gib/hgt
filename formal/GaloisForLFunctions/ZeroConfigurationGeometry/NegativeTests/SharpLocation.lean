import GaloisForLFunctions.ZeroConfigurationGeometry.NegativeTests.NegativeCluster
import GaloisForLFunctions.ZeroConfigurationGeometry.NegativeTests.ZetaClusters

/-!
# Cubic-logarithmic zero location from Weil positivity

A deep zero lies in an isolated cluster. Two normalized convolution cameras take
opposite values on that cluster and its reflection; their absolute Fourier tails
control the quadratic Weil tail. This gives a negative test at aperture `λL_T`
for every `λ > 1`, with an explicit starting height and no separation premise.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry
open Zeta23 SquareRootThreshold

/-- Opposite cameras on two reflected clusters give a negative test without any
separation assumption inside either cluster. -/
theorem zeta_negative_of_isolated_cluster {lam Lη T η r : ℝ}
    (hlam : 1 / 2 < lam) (hLη : 0 ≤ Lη)
    (hT : zetaCubicCameraHeight lam Lη ≤ T) {p : ℂ}
    (hp : p ∈ zetaZeroConfig.carrier) (hpT : p.im = T)
    (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hlogη : max 0 (Real.log (1 / η)) ≤ Lη * Real.log (T / (2 * π)) ^ 3)
    (hr0 : 0 ≤ r) (hr : r ≤ η * T ^ (-(slowExponent lam + 2)))
    (hrδ : r < |depth p|)
    (hiso : ∀ z ∈ zetaZeroConfig.carrier, |z.im - T| ≤ T / 2 →
      ‖z - p‖ ≤ r ∨ η ≤ ‖z - p‖) :
    ∃ f : ℝ → ℂ,
      ApertureWindow (2 * (lam * (Real.log (T / (2 * π)) / 2))) f ∧
      (zetaZeroConfig.W f f).re < 0 := by
  have hpr := zetaZeroConfig.reflect_mem p hp
  have hprT : (reflect p).im = T := (im_reflect p).trans hpT
  have hinv (z : ℂ) : reflect (reflect z) = z := by simp [reflect]
  have hnorm (z : ℂ) : ‖reflect z - p‖ = ‖z - reflect p‖ := by
    have hh := norm_reflect_sub_reflect z (reflect p)
    rw [hinv] at hh
    exact hh
  have hisor : ∀ z ∈ zetaZeroConfig.carrier, |z.im - T| ≤ T / 2 →
      ‖z - reflect p‖ ≤ r ∨ η ≤ ‖z - reflect p‖ := by
    intro z hz hzT
    have hh := hiso (reflect z) (zetaZeroConfig.reflect_mem z hz)
      (by simpa only [im_reflect] using hzT)
    simpa only [hnorm] using hh
  obtain ⟨f, hfw, hfb, hfa, hfs, hftail⟩ :=
    zeta_cluster_camera_explicit hlam hLη hT hp hpT hη0 hη1 hlogη hr0 hr hiso
  obtain ⟨g, hgw, hgb, hga, hgs, hgtail⟩ :=
    zeta_cluster_camera_explicit hlam hLη hT hpr hprT hη0 hη1 hlogη hr0 hr hisor
  have h20 : 20 ≤ T :=
    (le_max_left 20 (2 * π * Real.exp (max 1 (2 / (lam + 1 / 2 - 1))))).trans
      ((le_max_left _ _).trans hT)
  have hqwin : ApertureWindow (2 * (lam * (Real.log (T / (2 * π)) / 2)))
      (fun t => f t - g t) := by
    simpa only [neg_one_mul, sub_eq_add_neg] using hfw.add_smul hgw (-1)
  have hqft (w : ℂ) : paperFT (fun t => f t - g t) w = paperFT f w - paperFT g w := by
    simpa only [neg_one_mul, sub_eq_add_neg] using
      paperFT_add_smul hfw.1.continuous hfw.hasCompactSupport hgw.1.continuous
        hgw.hasCompactSupport (-1) w
  have hdisj (z : ℂ) (hzp : ‖z - p‖ ≤ r) : ¬ ‖z - reflect p‖ ≤ r := by
    intro hzr
    have hh : ‖reflect p - p‖ ≤ ‖z - reflect p‖ + ‖z - p‖ := by
      calc ‖reflect p - p‖ = ‖(z - p) - (z - reflect p)‖ := by congr 1; ring
        _ ≤ ‖z - p‖ + ‖z - reflect p‖ := norm_sub_le _ _
        _ = _ := add_comm _ _
    rw [norm_reflect_sub_eq_twice_depth] at hh
    linarith only [hh, hzp, hzr, hrδ]
  have hnegative (z : ℂ) (hz : z ∈ zetaZeroConfig.carrier)
      (hzT : |z.im - T| ≤ T / 4) (hzp : ‖z - p‖ ≤ r) :
      (pointImage (fun t => f t - g t) (fun t => f t - g t) z).re ≤ -(7 / 16 : ℝ) := by
    have hzref := zetaZeroConfig.reflect_mem z hz
    have hzrefT : |(reflect z).im - T| ≤ T / 4 := by simpa only [im_reflect] using hzT
    have hzr : ‖reflect z - reflect p‖ ≤ r := by
      simpa only [norm_reflect_sub_reflect] using hzp
    have hzrnot : ¬ ‖reflect z - p‖ ≤ r := by
      rw [hnorm]
      exact hdisj z hzp
    have hgzero := hgb z hz hzT (hdisj z hzp)
    have hfzero := hfb (reflect z) hzref hzrefT hzrnot
    have hu : ‖paperFT (fun t => f t - g t) (gammaOf z) - (1 : ℂ)‖ ≤ (1 : ℝ) / 4 := by
      rw [hqft, hgzero, sub_zero]
      exact hfa z hzp
    have hv : ‖paperFT (fun t => f t - g t) (gammaOf (reflect z)) - (-1 : ℂ)‖ ≤ (1 : ℝ) / 4 := by
      have he : paperFT (fun t => f t - g t) (gammaOf (reflect z)) - (-1 : ℂ) =
          -(paperFT g (gammaOf (reflect z)) - 1) := by rw [hqft, hfzero]; ring
      rw [he, norm_neg]
      exact hga (reflect z) hzr
    have hh := re_pairImage_le_neg_sq_of_quarter_error
      (u := paperFT (fun t => f t - g t) (gammaOf z))
      (v := paperFT (fun t => f t - g t) (gammaOf (reflect z))) (δ := (1 : ℝ))
      (by simpa only [abs_one, Complex.ofReal_one] using hu)
      (by simpa only [abs_one, Complex.ofReal_one] using hv)
    rw [gammaOf_reflect_eq_conj] at hh
    simpa only [one_pow, mul_one, pointImage] using hh
  have hreflectRe (z : ℂ) :
      (pointImage (fun t => f t - g t) (fun t => f t - g t) (reflect z)).re =
        (pointImage (fun t => f t - g t) (fun t => f t - g t) z).re := by
    have he : pointImage (fun t => f t - g t) (fun t => f t - g t) (reflect z) =
        conj (pointImage (fun t => f t - g t) (fun t => f t - g t) z) := by
      rw [pointImage, pointImage, gammaOf_reflect_eq_conj, Complex.conj_conj,
        map_mul, Complex.conj_conj]
      ring
    rw [he, Complex.conj_re]
  have hnear : ∀ z ∈ zetaZeroConfig.carrier, |z.im - T| ≤ T / 4 →
      (pointImage (fun t => f t - g t) (fun t => f t - g t) z).re ≤ 0 := by
    intro z hz hzT
    by_cases hzp : ‖z - p‖ ≤ r
    · exact (hnegative z hz hzT hzp).trans (by norm_num)
    by_cases hzr : ‖z - reflect p‖ ≤ r
    · have hh := hnegative (reflect z) (zetaZeroConfig.reflect_mem z hz)
        (by simpa only [im_reflect] using hzT) (by simpa only [hnorm] using hzr)
      rw [hreflectRe] at hh
      exact hh.trans (by norm_num)
    · rw [pointImage, hqft, hfb z hz hzT hzp, hgb z hz hzT hzr,
        sub_self, zero_mul, Complex.zero_re]
  obtain ⟨hss, hst⟩ := fourier_far_tail_sub_le hfw hgw hfs hgs
  have hL : (∑' z, fourierFarTerm (multDiff zetaZeroConfig emptyZeroConfig)
      (fun t => f t - g t) T (T / 4) z) ≤ 1 / 2 := by
    linarith only [hst, hftail, hgtail]
  have hpR : |p.im - T| ≤ T / 4 := by rw [hpT, sub_self, abs_zero]; linarith only [h20]
  have hpneg := hnegative p hp hpR (by rw [sub_self, norm_zero]; exact hr0)
  exact ⟨fun t => f t - g t, hqwin,
    re_W_neg_of_local_nonpositivity hp hpR hnear hpneg hss hL⟩

/-- Explicit height for cubic-logarithmic zero location from positivity at `λL_T`. -/
def zetaNegativeCameraHeight (lam c : ℝ) : ℝ :=
  zetaCubicCameraHeight (lam / 2)
    (c + 2 + 8 * (slowExponent (lam / 2) + 2) * zetaClusterCountConstant (lam / 2))

/-- Every zero deeper than the stated cubic-logarithmic scale produces a negative diagonal
Weil test. Nearby zeros of arbitrary multiplicity are absorbed into a coherent cluster. -/
theorem zeta_negative_test_of_cubic_depth {lam c T : ℝ}
    (hlam : 1 < lam) (hc : 0 ≤ c) (hT : zetaNegativeCameraHeight lam c ≤ T)
    {p : ℂ} (hp : p ∈ zetaZeroConfig.carrier) (hpT : p.im = T)
    (hdepth : Real.exp (-(c * Real.log (T / (2 * π)) ^ 3)) ≤ |depth p|) :
    ∃ f : ℝ → ℂ,
      ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) f ∧
      (zetaZeroConfig.W f f).re < 0 := by
  have hlamhalf : 1 / 2 < lam / 2 := by linarith only [hlam]
  have hκ0 : 0 ≤ slowExponent (lam / 2) := by
    unfold slowExponent
    linarith only [mul_pos Real.pi_pos (show 0 < lam / 2 by linarith only [hlam]), hlam]
  have hC0 := zetaClusterCountConstant_nonneg hlamhalf
  have hLη0 : 0 ≤ c + 2 + 8 * (slowExponent (lam / 2) + 2) *
      zetaClusterCountConstant (lam / 2) := by positivity
  have hTh : zetaCubicCameraHeight (lam / 2)
      (c + 2 + 8 * (slowExponent (lam / 2) + 2) * zetaClusterCountConstant (lam / 2)) ≤ T := hT
  have hcountT : zetaCameraCountHeight (lam / 2 + 1 / 2) ≤ T := (le_max_left _ _).trans hTh
  have hbase : 2 * π * Real.exp 1 ≤ T :=
    (cameraCubicIsolationHeight_ge (lam / 2 + 1 / 2) (lam / 2)
      (zetaCameraCountConstant (lam / 2 + 1 / 2)) (33 / 100)
      (c + 2 + 8 * (slowExponent (lam / 2) + 2) * zetaClusterCountConstant (lam / 2))).trans
      ((le_max_right _ _).trans hTh)
  have hT0 : 0 < T := (by positivity : 0 < 2 * π * Real.exp 1).trans_le hbase
  obtain ⟨u, hu⟩ : ∃ u, u = Real.log (T / (2 * π)) := ⟨_, rfl⟩
  have hu1 : 1 ≤ u := by
    rw [hu, Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]
    linarith only [hbase]
  have hTu : T = 2 * π * Real.exp u := by
    rw [hu, Real.exp_log (by positivity : 0 < T / (2 * π))]
    field_simp
  rw [← hu] at hdepth
  obtain ⟨η, r, hη0, hη1, hr0, hre, hrδ, hlogη, hiso⟩ :=
    exists_zeta_camera_cluster hlamhalf hc hu1 hTu hcountT hp hpT hdepth
  rw [hu] at hlogη
  obtain ⟨f, hfw, hfneg⟩ := zeta_negative_of_isolated_cluster hlamhalf hLη0 hTh hp hpT
    hη0 hη1 hlogη hr0 hre.le hrδ (fun z hz _ => hiso z hz)
  refine ⟨f, ?_, hfneg⟩
  simpa only [show 2 * (lam / 2 * (Real.log (T / (2 * π)) / 2)) =
    lam * (Real.log (T / (2 * π)) / 2) by ring] using hfw

/-- Positivity at aperture `λL_T`, for any `λ>1`, confines every zero at height `T`
to the cubic-logarithmic depth scale. No zero separation or mimic is assumed. -/
theorem zeta_depth_lt_of_positive_camera {lam c T : ℝ}
    (hlam : 1 < lam) (hc : 0 ≤ c) (hT : zetaNegativeCameraHeight lam c ≤ T)
    (hpos : ∀ f : ℝ → ℂ,
      ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) f →
        0 ≤ (zetaZeroConfig.W f f).re) :
    ∀ p ∈ zetaZeroConfig.carrier, p.im = T →
      |depth p| < Real.exp (-(c * Real.log (T / (2 * π)) ^ 3)) := by
  intro p hp hpT
  by_contra hn
  obtain ⟨f, hfw, hfneg⟩ := zeta_negative_test_of_cubic_depth hlam hc hT hp hpT (not_lt.mp hn)
  exact (not_lt_of_ge (hpos f hfw)) hfneg

/-- A positive fixed aperture controls every height below its exponential camera horizon. -/
theorem zeta_depth_lt_of_positive_fixed_aperture {lam c T a : ℝ}
    (hlam : 1 < lam) (hc : 0 ≤ c) (hT : zetaNegativeCameraHeight lam c ≤ T)
    (hheight : T ≤ 2 * π * Real.exp (2 * a / lam))
    (hpos : ∀ f : ℝ → ℂ, ApertureWindow a f → 0 ≤ (zetaZeroConfig.W f f).re) :
    ∀ p ∈ zetaZeroConfig.carrier, p.im = T →
      |depth p| < Real.exp (-(c * Real.log (T / (2 * π)) ^ 3)) := by
  have hlam0 : 0 < lam := by linarith only [hlam]
  have hπ0 : 0 < 2 * π := by positivity
  have h20 : 20 ≤ T :=
    (le_max_left 20 (2 * π * Real.exp (max 1 (2 / (lam / 2 + 1 / 2 - 1))))).trans
      ((le_max_left _ _).trans hT)
  have hT0 : 0 < T := by linarith only [h20]
  have hdiv : T / (2 * π) ≤ Real.exp (2 * a / lam) := by
    rw [div_le_iff₀ hπ0]
    linarith only [hheight]
  have hlog : Real.log (T / (2 * π)) ≤ 2 * a / lam := by
    simpa only [Real.log_exp] using Real.log_le_log (div_pos hT0 hπ0) hdiv
  have hap : lam * (Real.log (T / (2 * π)) / 2) ≤ a := by
    calc lam * (Real.log (T / (2 * π)) / 2) =
        (lam / 2) * Real.log (T / (2 * π)) := by ring
      _ ≤ (lam / 2) * (2 * a / lam) := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ = a := by field_simp
  apply zeta_depth_lt_of_positive_camera hlam hc hT
  intro f hf
  apply hpos f
  refine ⟨hf.1, fun t ht => ?_⟩
  have hh := hf.2 ht
  exact ⟨by linarith only [hh.1, hap], by linarith only [hh.2, hap]⟩

private theorem cubic_depth_scale_compare {c T : ℝ} (hc : 0 ≤ c)
    (hs : (2 * π) ^ 2 ≤ T) :
    Real.exp (-(8 * c * Real.log (T / (2 * π)) ^ 3)) ≤
      Real.exp (-(c * Real.log T ^ 3)) := by
  have hπ0 : 0 < 2 * π := by positivity
  have hT0 : 0 < T := (sq_pos_of_pos hπ0).trans_le hs
  have hT1 : 1 ≤ T := (one_le_pow₀
    (show (1 : ℝ) ≤ 2 * π by linarith only [Real.pi_gt_three]) (n := 2)).trans hs
  have hlogT0 : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hlog2 : 2 * Real.log (2 * π) ≤ Real.log T := by
    have hh := Real.log_le_log (sq_pos_of_pos hπ0) hs
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hu : Real.log (T / (2 * π)) = Real.log T - Real.log (2 * π) :=
    Real.log_div hT0.ne' hπ0.ne'
  have h2u : Real.log T ≤ 2 * Real.log (T / (2 * π)) := by
    linarith only [hlog2, hu]
  have hp := pow_le_pow_left₀ hlogT0 h2u 3
  have hm := mul_le_mul_of_nonneg_left hp hc
  exact Real.exp_le_exp.mpr (by linarith only [hm])

/-- The same receiver in the unshifted `exp(−c log³T)` normalization. -/
theorem zeta_depth_lt_exp_log_cube_of_positive_camera {lam c T : ℝ}
    (hlam : 1 < lam) (hc : 0 ≤ c)
    (hT : max (zetaNegativeCameraHeight lam (8 * c)) ((2 * π) ^ 2) ≤ T)
    (hpos : ∀ f : ℝ → ℂ,
      ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) f →
        0 ≤ (zetaZeroConfig.W f f).re) :
    ∀ p ∈ zetaZeroConfig.carrier, p.im = T →
      |depth p| < Real.exp (-(c * Real.log T ^ 3)) := by
  intro p hp hpT
  exact (zeta_depth_lt_of_positive_camera hlam (by positivity) ((le_max_left _ _).trans hT)
    hpos p hp hpT).trans_le (cubic_depth_scale_compare hc ((le_max_right _ _).trans hT))

/-- A positive aperture confines every zero below its exponential height horizon to
the unshifted cubic-logarithmic depth scale. -/
theorem zeta_depth_lt_exp_log_cube_of_positive_fixed_aperture {lam c T a : ℝ}
    (hlam : 1 < lam) (hc : 0 ≤ c)
    (hT : max (zetaNegativeCameraHeight lam (8 * c)) ((2 * π) ^ 2) ≤ T)
    (hheight : T ≤ 2 * π * Real.exp (2 * a / lam))
    (hpos : ∀ f : ℝ → ℂ, ApertureWindow a f → 0 ≤ (zetaZeroConfig.W f f).re) :
    ∀ p ∈ zetaZeroConfig.carrier, p.im = T →
      |depth p| < Real.exp (-(c * Real.log T ^ 3)) := by
  intro p hp hpT
  exact (zeta_depth_lt_of_positive_fixed_aperture hlam (by positivity)
    ((le_max_left _ _).trans hT) hheight hpos p hp hpT).trans_le
      (cubic_depth_scale_compare hc ((le_max_right _ _).trans hT))

/-- The fixed-aperture location bound applies to zeros at either sign of the ordinate. -/
theorem zeta_depth_lt_exp_log_cube_of_positive_aperture_abs {lam c T a : ℝ}
    (hlam : 1 < lam) (hc : 0 ≤ c)
    (hT : max (zetaNegativeCameraHeight lam (8 * c)) ((2 * π) ^ 2) ≤ T)
    (hheight : T ≤ 2 * π * Real.exp (2 * a / lam))
    (hpos : ∀ f : ℝ → ℂ, ApertureWindow a f → 0 ≤ (zetaZeroConfig.W f f).re) :
    ∀ p ∈ zetaZeroConfig.carrier, |p.im| = T →
      |depth p| < Real.exp (-(c * Real.log T ^ 3)) := by
  intro p hp hpT
  by_cases him : 0 ≤ p.im
  · rw [abs_of_nonneg him] at hpT
    exact zeta_depth_lt_exp_log_cube_of_positive_fixed_aperture hlam hc hT hheight hpos p hp hpT
  · rw [abs_of_neg (lt_of_not_ge him)] at hpT
    have hconjT : (conj p).im = T := by simpa only [Complex.conj_im] using hpT
    have hh := zeta_depth_lt_exp_log_cube_of_positive_fixed_aperture hlam hc hT hheight hpos
      (conj p) (RHTower.conj_mem_zetaZeroConfig hp) hconjT
    simpa only [depth, Complex.conj_re] using hh

end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.zeta_negative_of_isolated_cluster
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.zeta_negative_test_of_cubic_depth
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.zeta_depth_lt_of_positive_camera
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.zeta_depth_lt_of_positive_fixed_aperture
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.zeta_depth_lt_exp_log_cube_of_positive_camera
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.zeta_depth_lt_exp_log_cube_of_positive_fixed_aperture
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.zeta_depth_lt_exp_log_cube_of_positive_aperture_abs
