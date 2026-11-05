import GaloisForLFunctions.ZeroConfigurationGeometry.NegativeTests.CubicCamera
import GaloisForLFunctions.ZeroConfigurationGeometry.EffectiveHeights.LocalZetaCount
import GaloisForLFunctions.ZeroConfigurationGeometry.EffectiveHeights.SpectralMass
import GaloisForLFunctions.SquareRootThreshold.ZetaCoherentCoresAddUp

/-!
# Cubic-logarithmic cluster cameras for the zeros of ζ

The numerical ζ count and Lorentzian mass discharge the analytic inputs of the
cluster camera. An empty-annulus argument puts every sufficiently deep zero
inside a cluster whose isolation logarithm is cubic in logarithmic height.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section
namespace GaloisForLFunctions.ZeroConfigurationGeometry
open Zeta23 SquareRootThreshold

/-- The finite height of the actual ζ cluster camera. -/
def zetaCubicCameraHeight (lam Lη : ℝ) : ℝ :=
  max (zetaCameraCountHeight (lam + 1 / 2))
    (cameraCubicIsolationHeight (lam + 1 / 2) lam
      (zetaCameraCountConstant (lam + 1 / 2)) (33 / 100) Lη)

/-- Distinct zeros in a unit disc have at most this multiple of normalized logarithmic height. -/
def zetaClusterCountConstant (lam : ℝ) : ℝ :=
  (lam + 1 / 2) / π + zetaCameraCountConstant (lam + 1 / 2)

theorem zetaClusterCountConstant_nonneg {lam : ℝ} (hlam : 1 / 2 < lam) :
    0 ≤ zetaClusterCountConstant lam := by
  have hθ : 1 < lam + 1 / 2 := by linarith only [hlam]
  have hA0 := zetaCameraCountConstant_nonneg hθ
  have hθ0 : 0 ≤ lam + 1 / 2 := by linarith only [hθ]
  unfold zetaClusterCountConstant
  positivity

/-- The actual ζ cluster camera has no analytic count or mass premise. -/
theorem zeta_cluster_camera_explicit {lam Lη T : ℝ}
    (hlam : 1 / 2 < lam) (hLη : 0 ≤ Lη)
    (hT : zetaCubicCameraHeight lam Lη ≤ T) {p : ℂ}
    (hp : p ∈ zetaZeroConfig.carrier) (hpT : p.im = T)
    {η r : ℝ} (hη0 : 0 < η) (hη1 : η ≤ 1)
    (hlogη : max 0 (Real.log (1 / η)) ≤ Lη * Real.log (T / (2 * π)) ^ 3)
    (hr0 : 0 ≤ r) (hr : r ≤ η * T ^ (-(slowExponent lam + 2)))
    (hiso : ∀ z ∈ zetaZeroConfig.carrier, |z.im - T| ≤ T / 2 →
      ‖z - p‖ ≤ r ∨ η ≤ ‖z - p‖) :
    ∃ f : ℝ → ℂ,
      ApertureWindow (2 * (lam * (Real.log (T / (2 * π)) / 2))) f ∧
      (∀ z ∈ zetaZeroConfig.carrier, |z.im - T| ≤ T / 4 → ¬ ‖z - p‖ ≤ r →
        paperFT f (gammaOf z) = 0) ∧
      (∀ z : ℂ, ‖z - p‖ ≤ r → ‖paperFT f (gammaOf z) - 1‖ ≤ 1 / 4) ∧
      Summable (fourierFarTerm (multDiff zetaZeroConfig emptyZeroConfig) f T (T / 4)) ∧
      (∑' z, fourierFarTerm (multDiff zetaZeroConfig emptyZeroConfig) f T (T / 4) z) ≤ 1 / 4 := by
  have hθ : 1 < lam + 1 / 2 := by linarith only [hlam]
  have h20 : 20 ≤ T :=
    (le_max_left 20 (2 * π * Real.exp (max 1 (2 / (lam + 1 / 2 - 1))))).trans
      ((le_max_left _ _).trans hT)
  have hp' : IsNontrivialZero p := hp
  have hpre : |p.re - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]
    constructor <;> linarith only [hp'.2.1, hp'.2.2]
  have hcount := card_zeta_camera_band_le hθ ((le_max_left _ _).trans hT)
  obtain ⟨f, hfw, hb, ha, hs, ht⟩ := fourier_cluster_camera_explicit
    (by linarith only [hθ] : 0 ≤ lam + 1 / 2) (by linarith only [hlam])
    (zetaCameraCountConstant_nonneg hθ) hLη T ((le_max_right _ _).trans hT)
    zetaZeroConfig emptyZeroConfig temperedConfig_zeta temperedConfig_emptyZeroConfig
    zeta_empty_lorentzian_mass_lt.le
    (fun a x y hxy ha => hcount a x y hxy fun z hz =>
      ⟨(multDiff_empty_ne_zero_iff zetaZeroConfig z).mp (ha z hz).1, (ha z hz).2⟩)
    p (by rw [hpT, sub_self, abs_zero]; linarith only [h20]) hpre
    η hη0 hη1 hlogη r hr0 hr
    (fun z hcz hzT => hiso z ((multDiff_empty_ne_zero_iff zetaZeroConfig z).mp hcz) hzT)
  rw [hpT] at hb hs ht
  exact ⟨f, hfw, fun z hz => hb z ((multDiff_empty_ne_zero_iff zetaZeroConfig z).mpr hz),
    ha, hs, ht⟩

/-- A zero deeper than the cubic-logarithmic scale lies in a cluster with a
polynomial annulus ratio and a controlled cubic-logarithmic isolation cost. -/
theorem exists_zeta_camera_cluster {lam c T u : ℝ}
    (hlam : 1 / 2 < lam) (hc : 0 ≤ c) (hu1 : 1 ≤ u)
    (hTu : T = 2 * π * Real.exp u) (hT : zetaCameraCountHeight (lam + 1 / 2) ≤ T)
    {p : ℂ} (hp : p ∈ zetaZeroConfig.carrier) (hpT : p.im = T)
    (hdepth : Real.exp (-(c * u ^ 3)) ≤ |depth p|) :
    ∃ η r : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 ≤ r ∧
      r = η * T ^ (-(slowExponent lam + 2)) ∧ r < |depth p| ∧
      max 0 (Real.log (1 / η)) ≤
        (c + 2 + 8 * (slowExponent lam + 2) * zetaClusterCountConstant lam) * u ^ 3 ∧
      ∀ z ∈ zetaZeroConfig.carrier, ‖z - p‖ ≤ r ∨ η ≤ ‖z - p‖ := by
  classical
  have hθ : 1 < lam + 1 / 2 := by linarith only [hlam]
  have h20 : 20 ≤ T := (le_max_left _ _).trans hT
  have hT0 : 0 < T := by linarith only [h20]
  have hT1 : 1 ≤ T := by linarith only [h20]
  have hu0 : 0 < u := by linarith only [hu1]
  have hu : u = Real.log (T / (2 * π)) := by
    rw [hTu, mul_div_cancel_left₀ _ (by positivity : (2 * π : ℝ) ≠ 0), Real.log_exp]
  have hδ0 : 0 < |depth p| := (Real.exp_pos _).trans_le hdepth
  have hp' : IsNontrivialZero p := hp
  have hδhalf : |depth p| ≤ 1 / 2 := by
    rw [depth, abs_le]
    constructor <;> linarith only [hp'.2.1, hp'.2.2]
  have hband (z : ℂ) (hz : ‖z - p‖ ≤ 1) : |z.im - T| ≤ 1 := by
    have hh := (Complex.abs_im_le_norm (z - p)).trans hz
    simpa only [Complex.sub_im, hpT] using hh
  have hfin : {z : ℂ | z ∈ zetaZeroConfig.carrier ∧ ‖z - p‖ ≤ 1}.Finite :=
    (zetaZeroConfig.window_finite (T - 2) (T + 1)).subset fun z hz =>
      ⟨hz.1, by linarith only [(abs_le.mp (hband z hz.2)).1],
        by linarith only [(abs_le.mp (hband z hz.2)).2]⟩
  set P := hfin.toFinset with hPdef
  have hmem (z : ℂ) : z ∈ P ↔ z ∈ zetaZeroConfig.carrier ∧ ‖z - p‖ ≤ 1 := by
    simp only [hPdef, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have hcard : (P.card : ℝ) ≤ zetaClusterCountConstant lam * u := by
    have hh := card_zeta_camera_band_le hθ hT P (T - 1) (T + 1)
      (by linarith only []) (fun z hz => by
        have hz' := (hmem z).mp hz
        have hb := hband z hz'.2
        refine ⟨hz'.1, by linarith only [hb, h20], ?_⟩
        exact ⟨by linarith only [(abs_le.mp hb).1], by linarith only [(abs_le.mp hb).2]⟩)
    rw [← hu] at hh
    calc (P.card : ℝ) ≤ (lam + 1 / 2) / (2 * π) * u * ((T + 1) - (T - 1)) +
        zetaCameraCountConstant (lam + 1 / 2) * u := hh
      _ = zetaClusterCountConstant lam * u := by unfold zetaClusterCountConstant; ring
  have hC0 : 0 ≤ zetaClusterCountConstant lam := zetaClusterCountConstant_nonneg hlam
  set B := slowExponent lam + 2 with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef, slowExponent]
    linarith only [mul_pos Real.pi_pos (show 0 < lam by linarith only [hlam]), hlam]
  set G := T ^ B with hGdef
  have hG0 : 0 < G := Real.rpow_pos_of_pos hT0 _
  have hG1 : 1 ≤ G := Real.one_le_rpow hT1 hB0
  set R := |depth p| / 4 with hRdef
  have hR0 : 0 < R := by rw [hRdef]; positivity
  have hR1 : R ≤ 1 := by rw [hRdef]; linarith only [hδhalf]
  obtain ⟨j, hj, hann⟩ := GaloisForLFunctions.SquareRootThreshold.exists_empty_annulus P p
    (le_refl P.card) hR0 hG1
  set η := R / G ^ j with hηdef
  set r := R / G ^ (j + 1) with hrdef
  have hη0 : 0 < η := by rw [hηdef]; positivity
  have hηR : η ≤ R := div_le_self hR0.le (one_le_pow₀ hG1)
  have hη1 : η ≤ 1 := hηR.trans hR1
  have hr0 : 0 ≤ r := by rw [hrdef]; positivity
  have hrη : r ≤ η :=
    div_le_div_of_nonneg_left hR0.le (pow_pos hG0 _) (pow_le_pow_right₀ hG1 (by omega))
  have hrδ : r < |depth p| := by
    have hh := hrη.trans hηR
    rw [hRdef] at hh
    linarith only [hh, hδ0]
  have hre : r = η * T ^ (-(slowExponent lam + 2)) := by
    rw [hrdef, hηdef, pow_succ, hGdef, ← hBdef, Real.rpow_neg hT0.le]
    field_simp
  have hiso : ∀ z ∈ zetaZeroConfig.carrier, ‖z - p‖ ≤ r ∨ η ≤ ‖z - p‖ := by
    intro z hz
    by_cases hz1 : ‖z - p‖ ≤ 1
    · rcases hann z ((hmem z).mpr ⟨hz, hz1⟩) with hin | hout
      · exact Or.inl hin
      · exact Or.inr hout.le
    · exact Or.inr (hη1.trans (lt_of_not_ge hz1).le)
  have hlogδ : -(c * u ^ 3) ≤ Real.log |depth p| := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hdepth
  have hlog4 : Real.log (4 : ℝ) ≤ 2 := by
    have h2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    have he : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    linarith only [h2, he]
  have hlogG : Real.log G ≤ 8 * B * u := by
    have hh := max_log_inv_rpow_neg_le' hu1 hTu hB0
    rw [one_div, Real.rpow_neg hT0.le, inv_inv, ← hGdef] at hh
    exact (le_max_right _ _).trans hh
  have hj' : (j : ℝ) ≤ zetaClusterCountConstant lam * u := by
    have hjc : (j : ℝ) ≤ P.card := by exact_mod_cast hj
    exact hjc.trans hcard
  have hjlog : (j : ℝ) * Real.log G ≤ 8 * B * zetaClusterCountConstant lam * u ^ 3 := by
    have h1 := mul_le_mul hj' hlogG (Real.log_nonneg hG1) (mul_nonneg hC0 hu0.le)
    have hu23 : u ^ 2 ≤ u ^ 3 := by
      have hh := mul_le_mul_of_nonneg_right hu1 (sq_nonneg u)
      nlinarith only [hh]
    have h2 := mul_le_mul_of_nonneg_left hu23
      (show 0 ≤ 8 * B * zetaClusterCountConstant lam by positivity)
    linarith only [h1, h2]
  have hL0 : 0 ≤ c + 2 + 8 * B * zetaClusterCountConstant lam := by positivity
  have hlogη : max 0 (Real.log (1 / η)) ≤
      (c + 2 + 8 * B * zetaClusterCountConstant lam) * u ^ 3 := by
    refine max_le (by positivity) ?_
    rw [hηdef, hRdef, one_div, Real.log_inv,
      Real.log_div (div_ne_zero hδ0.ne' (by norm_num)) (pow_ne_zero j hG0.ne'),
      Real.log_div hδ0.ne' (by norm_num), Real.log_pow]
    have hu3 : 1 ≤ u ^ 3 := one_le_pow₀ hu1
    linarith only [hlogδ, hlog4, hjlog, hu3]
  exact ⟨η, r, hη0, hη1, hr0, hre, hrδ, hlogη, hiso⟩

end GaloisForLFunctions.ZeroConfigurationGeometry

#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.zetaClusterCountConstant_nonneg
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.zeta_cluster_camera_explicit
#print axioms GaloisForLFunctions.ZeroConfigurationGeometry.exists_zeta_camera_cluster
