import GaloisForLFunctions.RHTower.ZetaThinStripWeylBound
import GaloisForLFunctions.Bottcher.Montel

/-!
# Residue errors under small zero displacements

Thin-strip Weyl growth and the holomorphic disc Lipschitz estimate give
`|ζ(s)/s| ≤ C |η| (1+|Im s|)^(-5/6+ε)` when `Re s = 1/2`,
`ζ(s+η)=0`, and the displacement lies in a fixed small disc.
-/

open Complex Metric Set

namespace RHTower

/-- Moving a critical-line point to a nearby zeta zero controls its normalized
zeta value by displacement times a decaying height weight. -/
theorem exists_zeta_residue_displacement_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∃ C > 0, ∀ s η : ℂ, s.re = 1 / 2 → ‖η‖ < r →
      riemannZeta (s + η) = 0 →
      ‖riemannZeta s / s‖ ≤ C * ‖η‖ / (1 + |s.im|) ^ (5 / 6 - ε) := by
  obtain ⟨r₀, hr₀, _, C₀, hC₀, hglobal⟩ := exists_global_norm_zeta_thin_strip_le_weyl hε
  let R := min r₀ (1 / 8)
  have hR : 0 < R := lt_min hr₀ (by norm_num)
  have hR₀ : R ≤ r₀ := min_le_left _ _
  have hR8 : R ≤ 1 / 8 := min_le_right _ _
  let e : ℝ := 1 / 6 + ε
  let α : ℝ := 5 / 6 - ε
  have he : 0 ≤ e := by dsimp [e]; linarith only [hε]
  let M := 8 * C₀ * (2 : ℝ) ^ e / R
  have hM : 0 < M := by dsimp [M]; positivity
  refine ⟨R / 2, by positivity, M, hM, fun s η hs hη hzero => ?_⟩
  let H := 1 + |s.im|
  have hH : 0 < H := by dsimp [H]; positivity
  have hpow : H ^ e * H ^ α = H := by
    rw [← Real.rpow_add hH, show e + α = 1 by dsimp [e, α]; ring, Real.rpow_one]
  have hgeom : ∀ z ∈ ball s R,
      0 < z.re ∧ z.re < 1 ∧ |z.re - 1 / 2| ≤ r₀ ∧
      H / 4 ≤ ‖z‖ ∧ 1 + |z.im| ≤ 2 * H := by
    intro z hz
    have hn := mem_ball_iff_norm.mp hz
    have hre := abs_lt.mp ((abs_re_le_norm (z - s)).trans_lt hn)
    have him := (abs_im_le_norm (z - s)).trans hn.le
    simp only [Complex.sub_re, hs] at hre
    simp only [Complex.sub_im] at him
    have hzre : (3 / 8 : ℝ) ≤ z.re := by linarith only [hre.1, hR8]
    have hznorm : (3 / 8 : ℝ) ≤ ‖z‖ :=
      hzre.trans ((le_abs_self z.re).trans (abs_re_le_norm z))
    have him1 : |s.im| ≤ |z.im| + R := by
      calc |s.im| = |z.im + (s.im - z.im)| := by congr 1; ring
        _ ≤ |z.im| + |s.im - z.im| := by
          simpa only [Real.norm_eq_abs] using norm_add_le z.im (s.im - z.im)
        _ ≤ |z.im| + R := add_le_add le_rfl (by simpa only [abs_sub_comm] using him)
    have him2 : |z.im| ≤ |s.im| + R := by
      calc |z.im| = |s.im + (z.im - s.im)| := by congr 1; ring
        _ ≤ |s.im| + |z.im - s.im| := by
          simpa only [Real.norm_eq_abs] using norm_add_le s.im (z.im - s.im)
        _ ≤ |s.im| + R := add_le_add le_rfl him
    refine ⟨by linarith only [hzre], by linarith only [hre.2, hR8],
      (abs_le.mpr ⟨hre.1.le, hre.2.le⟩).trans hR₀, ?_, ?_⟩
    · dsimp [H]
      linarith only [him1, abs_im_le_norm z, hznorm, hR8]
    · dsimp [H]
      linarith only [him2, hR8, abs_nonneg s.im]
  let A := 4 * C₀ * (2 : ℝ) ^ e / H ^ α
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hbound : ∀ z ∈ ball s R, ‖riemannZeta z / z‖ ≤ A := by
    intro z hz
    obtain ⟨hzre, _, hzstrip, hnorm, him⟩ := hgeom z hz
    have hzn : 0 < ‖z‖ := (div_pos hH (by norm_num)).trans_le hnorm
    have hzeta := hglobal z hzstrip
    have hζ : ‖riemannZeta z‖ ≤ C₀ * (2 : ℝ) ^ e * H ^ e := by
      calc ‖riemannZeta z‖ ≤ C₀ * (1 + |z.im|) ^ e := hzeta
        _ ≤ C₀ * (2 * H) ^ e := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity) him he) hC₀.le
        _ = C₀ * (2 : ℝ) ^ e * H ^ e := by rw [Real.mul_rpow (by norm_num) hH.le]; ring
    rw [norm_div]
    apply (div_le_iff₀ hzn).mpr
    refine hζ.trans ?_
    calc
      C₀ * (2 : ℝ) ^ e * H ^ e = A * (H / 4) := by
        dsimp [A]
        have hdiv : H ^ e = H / H ^ α :=
          (eq_div_iff (Real.rpow_pos_of_pos hH α).ne').mpr hpow
        rw [hdiv]
        ring
      _ ≤ A * ‖z‖ := mul_le_mul_of_nonneg_left hnorm hA
  have hdiff : DifferentiableOn ℂ (fun z => riemannZeta z / z) (ball s R) := by
    intro z hz
    have hg := hgeom z hz
    have hz0 : z ≠ 0 := by intro h; simpa only [h, zero_re, lt_self_iff_false] using hg.1
    have hz1 : z ≠ 1 := by intro h; simpa only [h, one_re, lt_self_iff_false] using hg.2.1
    exact ((differentiableAt_riemannZeta hz1).div differentiableAt_id hz0).differentiableWithinAt
  have h := Bottcher.norm_sub_le_of_bounded_on_ball hR hdiff hbound
    (z := s) (w := s + η) (mem_ball_self (by positivity)) (by
      rw [mem_ball_iff_norm, add_sub_cancel_left]
      exact hη)
  rw [hzero, zero_div, sub_zero, show s - (s + η) = -η by ring, norm_neg] at h
  calc ‖riemannZeta s / s‖ ≤ (2 * A / R) * ‖η‖ := h
    _ = M * ‖η‖ / H ^ α := by dsimp [M, A]; ring

end RHTower
