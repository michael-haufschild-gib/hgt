import GaloisForLFunctions.RHTower.KiKimLeeInteriorLindelofHorizon
import GaloisForLFunctions.RHTower.ZetaElevenEighteenthsProfiles

/-!
# The heat horizon at `2/3`: real and simple zeros of `H_t` above `2π e^{(2/3+ε)/t}`

The interior-Lindelöf horizon (`KiKimLeeInteriorLindelofHorizon`) compares the Gaussian strip
average of `xiLine` against a Phragmén–Lindelöf size profile `E(w)` of `ζ(1/2 + w + iX)`, and needs
`(c − w)² > 4c E(w)` on `[0, 1/2]`.  With the two-piece profile through `μ(5/7) ≤ 1/14` the binding
constraint sits on `[0, 3/14]` and gives `c > 27/40`.

This module inserts `μ(11/18) ≤ 1/9` (`norm_riemannZeta_elevenEighteenths_le`, the exponent pair
`A·B·A²·B(0,1)`), giving the three-piece exponent `eeStripExp`:

* `w ≤ 1/9`: `1/6 + η − w/2`, where `(c − w)² − 4c E = w² + c(c − 2/3 − 4η)`;
* `1/9 ≤ w ≤ 3/14`: `1/9 + η − (5/13)(w − 1/9)`, where
  `(c − w)² − 4c E = (w − 3c/13)² + c((160/169)c − 8/13 − 4η)`, positive for `c > 13/20`;
* `w ≥ 3/14`: the corpus piece through `μ(5/7) ≤ 1/14`, positive for `c > 2/3`.

So the threshold drops to `2/3 = 4μ(1/2)` (`exists_twoThirds_params`), the floor set by Weyl's
exponent at `w = 0`.  The Gaussian machinery is the corpus one with `eeStripExp` in place of
`interiorStripExp`; strip-independent lemmas are reused.  Consequences
(`riemannHeat_zeros_real_simple_twoThirds`,
`exists_nonrealZeroCount_and_collisionMass_le_twoThirds`): for `0 < t ≤ 1/8` the zeros of `H_t`
with `|Re z| ≥ max(X₀, 2π e^{(2/3+ε)/t})` are real and simple, and
`nonrealZeroCount t ≤ C₀ R log(2 + 3R)`, `R = max(X₀, 2π e^{(2/3+ε)/t}) + 1`.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry

namespace RHTower.DeBruijn

noncomputable section

/-! ## 1. The three-piece strip exponent and strip comparison -/

/-- Three-piece Lindelöf strip exponent on `[0, 1/2 + 2η]`, through `μ(1/2) ≤ 1/6`,
`μ(11/18) ≤ 1/9`, `μ(5/7) ≤ 1/14` and `μ(1 + 2η) = 0`. -/
def eeStripExp (η w : ℝ) : ℝ :=
  if w ≤ 1 / 9 then 1 / 6 + η - w / 2
  else if w ≤ 3 / 14 then 1 / 9 + η - 5 / 13 * (w - 1 / 9)
  else interiorStripRateTwo η * (1 / 2 + 2 * η - w)

theorem eeStripExp_nonneg {η w : ℝ} (hη : 0 ≤ η) (hw : w ≤ 1 / 2 + 2 * η) :
    0 ≤ eeStripExp η w := by
  unfold eeStripExp
  split_ifs with h1 h2
  · linarith
  · linarith
  · exact mul_nonneg (interiorStripRateTwo_pos hη).le (by linarith)

theorem eeStripExp_le_quarter_add {η w : ℝ} (hη0 : 0 ≤ η) (hη8 : η ≤ 1 / 8) (hw0 : 0 ≤ w) :
    eeStripExp η w ≤ (1 / 2 + 2 * η) / 2 := by
  unfold eeStripExp
  split_ifs with h1 h2
  · linarith
  · linarith
  · have hrate : interiorStripRateTwo η * (1 / 2 + 2 * η - w) ≤
        interiorStripRateTwo η * (2 / 7 + 2 * η) :=
      mul_le_mul_of_nonneg_left (by linarith) (interiorStripRateTwo_pos hη0).le
    have hsimp : interiorStripRateTwo η * (2 / 7 + 2 * η) = 1 / 14 + 2 * η := by
      unfold interiorStripRateTwo
      exact div_mul_cancel₀ _ (by positivity)
    linarith

/-- **Three-piece strip comparison.**
For `0 < η ≤ 1/4`, `X ≥ 16`, `0 ≤ w ≤ 1/2 + 2η`, and any Euler anchor `1/2 + 2η ≤ u ≤ X`,
`‖xiLine X w‖ ≤ K * X^{eeStripExp η w} * (X / 2π)^{(w − u)/2} * ‖xiLine X u‖`. -/
theorem exists_norm_xiLine_le_strip_ee {η : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4) :
    ∃ K : ℝ, 0 < K ∧ ∀ X w u : ℝ, 16 ≤ X → 0 ≤ w → w ≤ 1 / 2 + 2 * η →
      1 / 2 + 2 * η ≤ u → u ≤ X →
        ‖xiLine X w‖ ≤ K * X ^ (eeStripExp η w) *
          (X / (2 * Real.pi)) ^ ((w - u) / 2) * ‖xiLine X u‖ := by
  obtain ⟨C₁, hC₁, hp₁⟩ := RHTower.exists_norm_riemannZeta_le_profile_ee_one hη (by linarith)
  obtain ⟨C₂, hC₂, hp₂⟩ := RHTower.exists_norm_riemannZeta_le_profile_ee_two hη (by linarith)
  obtain ⟨C₃, hC₃, hp₃⟩ := exists_norm_riemannZeta_le_profile_two (η := 2 * η)
    (by positivity) (by linarith)
  set C := max C₁ (max C₂ C₃)
  have hC : 0 < C := lt_of_lt_of_le hC₁ (le_max_left _ _)
  set c := 1 / (1 + 1 / (2 * η))
  have hc : 0 < c := by positivity
  refine ⟨2 * Real.exp 6 * C / c, by positivity, fun X w u hX hw0 hwη hu1 huX => ?_⟩
  have hX0 : 0 < X := by linarith
  have hu0 : 0 ≤ u := by linarith
  rw [norm_xiLine_eq_factors hX0 hw0, norm_xiLine_eq_factors hX0 hu0]
  set sw : ℂ := ((w + 1 / 2 : ℝ) : ℂ) + X * I with hsw
  set su : ℂ := ((u + 1 / 2 : ℝ) : ℂ) + X * I with hsu
  set Pw := ‖sw * (sw - 1) / 2‖ with hPw
  set Pu := ‖su * (su - 1) / 2‖ with hPu
  set Gw := ‖Complex.Gamma ((((w + 1 / 2) / 2 : ℝ) : ℂ) + ((X / 2 : ℝ) : ℂ) * I)‖ with hGw
  set Gu := ‖Complex.Gamma ((((u + 1 / 2) / 2 : ℝ) : ℂ) + ((X / 2 : ℝ) : ℂ) * I)‖ with hGu
  set Zw := ‖riemannZeta sw‖ with hZw
  set Zu := ‖riemannZeta su‖ with hZu
  have hsuim : X ≤ ‖su‖ := by
    have := Complex.abs_im_le_norm su; simpa [hsu, abs_of_pos hX0] using this
  have hsu1im : X ≤ ‖su - 1‖ := by
    have := Complex.abs_im_le_norm (su - 1); simpa [hsu, abs_of_pos hX0] using this
  have hsw_le : ‖sw‖ ≤ X + 2 := by
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith), norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX0, Complex.norm_I, mul_one]
    linarith
  have hsw1_le : ‖sw - 1‖ ≤ X + 1 := by
    have e : sw - 1 = (((w - 1 / 2 : ℝ)) : ℂ) + X * I := by rw [hsw]; push_cast; ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hX0, Complex.norm_I, mul_one]
    have : |w - 1 / 2| ≤ 1 := by rw [abs_le]; constructor <;> linarith
    linarith
  have hPwu : Pw ≤ 2 * Pu := by
    rw [hPw, hPu, norm_div, norm_div, norm_mul, norm_mul, Complex.norm_ofNat]
    have h1 : ‖sw‖ * ‖sw - 1‖ ≤ (X + 2) * (X + 1) :=
      mul_le_mul hsw_le hsw1_le (norm_nonneg _) (by linarith)
    have h2 : X * X ≤ ‖su‖ * ‖su - 1‖ := mul_le_mul hsuim hsu1im hX0.le (norm_nonneg _)
    have h3 : (X + 2) * (X + 1) ≤ 2 * (X * X) := by nlinarith
    linarith
  have hGamma : Gw ≤ (X / 2) ^ ((w - u) / 2) * Real.exp 6 * Gu := by
    have h := norm_Gamma_vertical_le_rpow_mul (a := (w + 1 / 2) / 2) (b := (u + 1 / 2) / 2)
      (y := X / 2) (by linarith) (by linarith) (by linarith)
    have hab : (w + 1 / 2) / 2 - (u + 1 / 2) / 2 = (w - u) / 2 := by ring
    rw [hab] at h
    have hexp : Real.exp (6 * ((u + 1 / 2) / 2 - (w + 1 / 2) / 2) / (X / 2)) ≤ Real.exp 6 := by
      apply Real.exp_le_exp.mpr
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    calc Gw ≤ (X / 2) ^ ((w - u) / 2) *
          Real.exp (6 * ((u + 1 / 2) / 2 - (w + 1 / 2) / 2) / (X / 2)) * Gu := h
      _ ≤ (X / 2) ^ ((w - u) / 2) * Real.exp 6 * Gu := by gcongr
  have hZw_le : Zw ≤ C * X ^ (eeStripExp η w) := by
    unfold eeStripExp
    split_ifs with hw1 hw2
    · have h := hp₁ (w + 1 / 2) X (by linarith) (by linarith) (by linarith)
      have e : 1 / 6 + η - (w + 1 / 2 - 1 / 2) / 2 = 1 / 6 + η - w / 2 := by ring
      rw [e] at h
      have h' : Zw ≤ C₁ * X ^ (1 / 6 + η - w / 2) := by simpa [hZw, hsw] using h
      exact h'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · have h := hp₂ (w + 1 / 2) X (by linarith) (by linarith) (by linarith)
      have e : 1 / 9 + η - 5 / 13 * (w + 1 / 2 - 11 / 18) = 1 / 9 + η - 5 / 13 * (w - 1 / 9) := by
        ring
      rw [e] at h
      have h' : Zw ≤ C₂ * X ^ (1 / 9 + η - 5 / 13 * (w - 1 / 9)) := by simpa [hZw, hsw] using h
      exact h'.trans (mul_le_mul_of_nonneg_right
        ((le_max_left _ _).trans (le_max_right _ _)) (by positivity))
    · have h := hp₃ (w + 1 / 2) X (by linarith) (by linarith) (by linarith)
      have e : (1 / 14 + 2 * η) * (1 + 2 * η - (w + 1 / 2)) / (2 / 7 + 2 * η) =
          interiorStripRateTwo η * (1 / 2 + 2 * η - w) := by
        unfold interiorStripRateTwo; field_simp; ring
      rw [e] at h
      have h' : Zw ≤ C₃ * X ^ (interiorStripRateTwo η * (1 / 2 + 2 * η - w)) := by
        simpa [hZw, hsw] using h
      exact h'.trans (mul_le_mul_of_nonneg_right
        ((le_max_right _ _).trans (le_max_right _ _)) (by positivity))
  have hZu_ge : c ≤ Zu := by
    have hsad := inv_le_norm_riemannZeta_saddle X hη hu1
    have hsu_eq : (((1 / 2 + u : ℝ) : ℂ) + (X : ℂ) * I) = su := by rw [hsu]; push_cast; ring
    rw [hsu_eq] at hsad
    exact hsad
  have hpi : Real.pi ^ (-((w + 1 / 2) / 2)) =
      Real.pi ^ (-((u + 1 / 2) / 2)) * Real.pi ^ ((u - w) / 2) := by
    rw [← Real.rpow_add Real.pi_pos]; congr 1; ring
  have hpow : (X / 2) ^ ((w - u) / 2) * Real.pi ^ ((u - w) / 2) =
      (X / (2 * Real.pi)) ^ ((w - u) / 2) := by
    have e : (u - w) / 2 = -((w - u) / 2) := by ring
    rw [e, Real.rpow_neg Real.pi_pos.le, ← Real.inv_rpow Real.pi_pos.le,
      ← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    field_simp
  have hPu0 : 0 ≤ Pu := norm_nonneg _
  have hGu0 : 0 ≤ Gu := norm_nonneg _
  have hZw0 : 0 ≤ Zw := norm_nonneg _
  rw [hpi]
  calc Pw * (Real.pi ^ (-((u + 1 / 2) / 2)) * Real.pi ^ ((u - w) / 2)) * Gw * Zw
      ≤ (2 * Pu) * (Real.pi ^ (-((u + 1 / 2) / 2)) * Real.pi ^ ((u - w) / 2)) *
          ((X / 2) ^ ((w - u) / 2) * Real.exp 6 * Gu) * (C * X ^ (eeStripExp η w)) := by
        gcongr
    _ = 2 * Real.exp 6 * C * X ^ (eeStripExp η w) *
          ((X / 2) ^ ((w - u) / 2) * Real.pi ^ ((u - w) / 2)) *
          (Pu * Real.pi ^ (-((u + 1 / 2) / 2)) * Gu) := by ring
    _ = 2 * Real.exp 6 * C * X ^ (eeStripExp η w) * (X / (2 * Real.pi)) ^ ((w - u) / 2) *
          (Pu * Real.pi ^ (-((u + 1 / 2) / 2)) * Gu) := by rw [hpow]
    _ ≤ 2 * Real.exp 6 * C * X ^ (eeStripExp η w) * (X / (2 * Real.pi)) ^ ((w - u) / 2) *
          (Pu * Real.pi ^ (-((u + 1 / 2) / 2)) * Gu * (Zu / c)) := by
        have h1 : 1 ≤ Zu / c := by rw [le_div_iff₀ hc]; linarith
        have h0 : 0 ≤ Pu * Real.pi ^ (-((u + 1 / 2) / 2)) * Gu := by positivity
        exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right h0 h1) (by positivity)
    _ = 2 * Real.exp 6 * C / c * X ^ (eeStripExp η w) *
          (X / (2 * Real.pi)) ^ ((w - u) / 2) *
          (Pu * Real.pi ^ (-((u + 1 / 2) / 2)) * Gu * Zu) := by
        field_simp

/-! ## 2. Unified strip estimates (the corpus Gaussian machinery, with `eeStripExp`) -/

/-- **Unified pointwise strip bound against an arbitrary Euler anchor `u`.**
Whenever `-(w − v)² + 4c · eeStripExp η w + 2c(w − u) + c² ≤ −m`, the Gaussian-weighted
strip value `g_t(w − v) ‖xiLine X w‖` is bounded by `e^{−m/(4t)}` times the `u`-anchored scale. -/
theorem gaussDensity_mul_norm_xiLine_le_anchor_ee {K η m t X v u w : ℝ} (ht : 0 < t)
    (hK : ∀ X w u : ℝ, 16 ≤ X → 0 ≤ w → w ≤ 1 / 2 + 2 * η → 1 / 2 + 2 * η ≤ u → u ≤ X →
      ‖xiLine X w‖ ≤ K * X ^ (eeStripExp η w) *
        (X / (2 * Real.pi)) ^ ((w - u) / 2) * ‖xiLine X u‖)
    (hK0 : 0 ≤ K) (hX : 16 ≤ X) (_ : 0 ≤ (horizontalSlope X).re)
    (hu1 : 1 / 2 + 2 * η ≤ u) (huX : u ≤ X)
    (hη0 : 0 ≤ η) (hη8 : η ≤ 1 / 8)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1 / 2 + 2 * η)
    (hexp_le : -(w - v) ^ 2 + 4 * (2 * t * (horizontalSlope X).re) * eeStripExp η w +
      2 * (2 * t * (horizontalSlope X).re) * (w - u) +
      (2 * t * (horizontalSlope X).re) ^ 2 ≤ -m) :
    gaussDensity t (w - v) * ‖xiLine X w‖ ≤
      (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * K * (2 * Real.pi) ^ ((1 / 2 + 2 * η) / 2) *
        Real.exp (-(m / (4 * t))) *
        (‖xiLine X u‖ * Real.exp (-(t * (horizontalSlope X).re ^ 2))) := by
  set α := (horizontalSlope X).re with hαdef
  set c := 2 * t * α with hcdef
  set N := ‖xiLine X u‖ with hN
  have hX0 : 0 < X := by linarith
  have hF := hK X w u hX hw0 hw1 hu1 huX
  have hXe : X / (2 * Real.pi) = Real.exp (2 * α) := by
    have := height_eq hX0
    rw [← hαdef] at this
    rw [this]; field_simp
  have hpow1 : (X / (2 * Real.pi)) ^ ((w - u) / 2) = Real.exp (α * (w - u)) := by
    rw [hXe, ← Real.exp_mul]; congr 1; ring
  have hXsplit : X = (2 * Real.pi) * (X / (2 * Real.pi)) := by field_simp
  set E := eeStripExp η w with hE
  have hE0 : 0 ≤ E := eeStripExp_nonneg hη0 hw1
  have hE2 : E ≤ (1 / 2 + 2 * η) / 2 := eeStripExp_le_quarter_add hη0 hη8 hw0
  have hpow2 : X ^ E ≤ (2 * Real.pi) ^ ((1 / 2 + 2 * η) / 2) * Real.exp (α * (2 * E)) := by
    rw [hXsplit, Real.mul_rpow (by positivity) (by positivity), hXe, ← Real.exp_mul]
    have e : 2 * α * E = α * (2 * E) := by ring
    rw [e]
    gcongr
    linarith [Real.pi_gt_three]
  have hg : gaussDensity t (w - v) =
      (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.exp (-((w - v) ^ 2 / (4 * t))) := rfl
  have hexp : Real.exp (-((w - v) ^ 2 / (4 * t))) * Real.exp (α * (2 * E)) *
      Real.exp (α * (w - u)) ≤ Real.exp (-(m / (4 * t))) * Real.exp (-(t * α ^ 2)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hαt : α = c / (2 * t) := by rw [hcdef]; field_simp
    have h4t : 0 < 4 * t := by positivity
    have hL : -((w - v) ^ 2 / (4 * t)) + α * (2 * E) + α * (w - u) =
        (-(w - v) ^ 2 + 4 * c * E + 2 * c * (w - u) + c ^ 2 - c ^ 2) / (4 * t) := by
      rw [hαt]; field_simp; ring
    have hR : -(m / (4 * t)) + -(t * α ^ 2) = (-m - c ^ 2) / (4 * t) := by
      rw [hαt]; field_simp; ring
    rw [hL, hR]
    exact div_le_div_of_nonneg_right (by linarith) h4t.le
  calc gaussDensity t (w - v) * ‖xiLine X w‖
      ≤ ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.exp (-((w - v) ^ 2 / (4 * t)))) *
          (K * ((2 * Real.pi) ^ ((1 / 2 + 2 * η) / 2) * Real.exp (α * (2 * E))) *
            Real.exp (α * (w - u)) * N) := by
        rw [hg]
        refine mul_le_mul_of_nonneg_left (hF.trans ?_) (by positivity)
        rw [hpow1]
        gcongr
    _ = (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * K * (2 * Real.pi) ^ ((1 / 2 + 2 * η) / 2) *
          (Real.exp (-((w - v) ^ 2 / (4 * t))) * Real.exp (α * (2 * E)) *
            Real.exp (α * (w - u))) * N := by ring
    _ ≤ (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * K * (2 * Real.pi) ^ ((1 / 2 + 2 * η) / 2) *
          (Real.exp (-(m / (4 * t))) * Real.exp (-(t * α ^ 2))) * N := by gcongr
    _ = _ := by ring

/-- **The three strip terms for an anchor `u`.** -/
theorem ee_strip_terms_le_anchor {K η m t X v u : ℝ} (ht : 0 < t) (hη : 0 < η)
    (hK : ∀ X w u : ℝ, 16 ≤ X → 0 ≤ w → w ≤ 1 / 2 + 2 * η → 1 / 2 + 2 * η ≤ u → u ≤ X →
      ‖xiLine X w‖ ≤ K * X ^ (eeStripExp η w) *
        (X / (2 * Real.pi)) ^ ((w - u) / 2) * ‖xiLine X u‖)
    (hK0 : 0 ≤ K) (hX : 16 ≤ X) (hv : |v| ≤ 1 / 2) (hα : 0 ≤ (horizontalSlope X).re)
    (hu1 : 1 / 2 + 2 * η ≤ u) (huX : u ≤ X) (hη8 : η ≤ 1 / 8)
    (hexp : ∀ w ∈ Icc (0 : ℝ) (1 / 2 + 2 * η),
      -(w - v) ^ 2 + 4 * (2 * t * (horizontalSlope X).re) * eeStripExp η w +
        2 * (2 * t * (horizontalSlope X).re) * (w - u) +
        (2 * t * (horizontalSlope X).re) ^ 2 ≤ -m) :
    (∫ w in Ioc (0 : ℝ) (1 / 2 + 2 * η), (|(w - v) / (2 * t)| + ‖horizontalSlope X‖) *
        gaussDensity t (w - v) * ‖xiLine X w‖) ≤
      ‖xiLine X u‖ * Real.exp (-(t * (horizontalSlope X).re ^ 2)) *
        sharpStripErr K (2 * η) m t (horizontalSlope X).re ∧
    (∫ w in Ioc (0 : ℝ) (1 / 2 + 2 * η), gaussDensity t (w - v) * ‖xiLine X w‖) ≤
      ‖xiLine X u‖ * Real.exp (-(t * (horizontalSlope X).re ^ 2)) *
        sharpStripErr K (2 * η) m t (horizontalSlope X).re ∧
    gaussDensity t (1 / 2 + 2 * η - v) * ‖xiLine X (1 / 2 + 2 * η)‖ ≤
      ‖xiLine X u‖ * Real.exp (-(t * (horizontalSlope X).re ^ 2)) *
        sharpStripErr K (2 * η) m t (horizontalSlope X).re := by
  set α := (horizontalSlope X).re
  set P := ‖xiLine X u‖ * Real.exp (-(t * α ^ 2)) with hP
  set Q := (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * K * (2 * Real.pi) ^ ((1 / 2 + 2 * η) / 2) *
    Real.exp (-(m / (4 * t))) with hQ
  set A := (1 + 2 * η) / (2 * t) + α + 1 with hA
  have hQ0 : 0 ≤ Q := by positivity
  have hP0 : 0 ≤ P := by positivity
  have hA1 : 1 ≤ A := by
    have : 0 ≤ (1 + 2 * η) / (2 * t) := by positivity
    linarith
  have hpt : ∀ w ∈ Icc (0 : ℝ) (1 / 2 + 2 * η), gaussDensity t (w - v) * ‖xiLine X w‖ ≤ Q * P :=
    fun w hw => gaussDensity_mul_norm_xiLine_le_anchor_ee ht hK hK0 hX hα hu1 huX hη.le hη8
      hw.1 hw.2 (hexp w hw)
  have hslope : ∀ w ∈ Icc (0 : ℝ) (1 / 2 + 2 * η),
      (|(w - v) / (2 * t)| + ‖horizontalSlope X‖) * gaussDensity t (w - v) * ‖xiLine X w‖ ≤
        A * (Q * P) := by
    intro w hw
    have hwt : |(w - v) / (2 * t)| ≤ (1 + 2 * η) / (2 * t) := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * t)]
      gcongr
      rw [abs_le] at hv ⊢
      constructor <;> linarith [hw.1, hw.2]
    have ha := norm_horizontalSlope_le hα
    have hAB : |(w - v) / (2 * t)| + ‖horizontalSlope X‖ ≤ A := by rw [hA]; linarith
    rw [mul_assoc]
    have hGF : 0 ≤ gaussDensity t (w - v) * ‖xiLine X w‖ :=
      mul_nonneg (gaussDensity_pos ht _).le (norm_nonneg _)
    exact mul_le_mul hAB (hpt w hw) hGF (by linarith)
  have hvol : volume.real (Ioc (0 : ℝ) (1 / 2 + 2 * η)) = 1 / 2 + 2 * η := by
    rw [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    ring
  have hint_bound : ∀ (f : ℝ → ℝ) (B : ℝ), (∀ w, 0 ≤ f w) →
      (∀ w ∈ Icc (0 : ℝ) (1 / 2 + 2 * η), f w ≤ B) →
      ∫ w in Ioc (0 : ℝ) (1 / 2 + 2 * η), f w ≤ (1 / 2 + 2 * η) * B := by
    intro f B hf0 hfB
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := f) (C := B)
      measure_Ioc_lt_top (fun w hw => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 w)]; exact hfB w (Ioc_subset_Icc_self hw))
    rw [hvol] at h
    have := le_abs_self (∫ w in Ioc (0 : ℝ) (1 / 2 + 2 * η), f w)
    rw [← Real.norm_eq_abs] at this
    linarith
  have herr : sharpStripErr K (2 * η) m t α = (1 + 2 * η) * A * Q := by
    rw [sharpStripErr, hA, hQ]
  have hQP : 0 ≤ Q * P := mul_nonneg hQ0 hP0
  refine ⟨?_, ?_, ?_⟩
  · refine (hint_bound _ _ (fun w => mul_nonneg (mul_nonneg (by positivity)
      (gaussDensity_pos ht _).le) (norm_nonneg _)) hslope).trans ?_
    rw [herr]
    have hAQP : 0 ≤ A * (Q * P) := mul_nonneg (by linarith) hQP
    have h2 : (1 / 2 + 2 * η) * (A * (Q * P)) ≤ (1 + 2 * η) * (A * (Q * P)) :=
      mul_le_mul_of_nonneg_right (by linarith) hAQP
    calc (1 / 2 + 2 * η) * (A * (Q * P)) ≤ (1 + 2 * η) * (A * (Q * P)) := h2
      _ = P * ((1 + 2 * η) * A * Q) := by ring
  · refine (hint_bound _ _ (fun w => mul_nonneg (gaussDensity_pos ht _).le (norm_nonneg _))
      hpt).trans ?_
    rw [herr]
    have h1 : Q * P ≤ A * (Q * P) := le_mul_of_one_le_left hQP hA1
    nlinarith
  · have h0 := hpt (1 / 2 + 2 * η) ⟨by linarith, le_rfl⟩
    have h1 : Q * P ≤ A * (Q * P) := le_mul_of_one_le_left hQP hA1
    have h2 : A * (Q * P) ≤ (1 + 2 * η) * (A * (Q * P)) :=
      le_mul_of_one_le_left (by positivity) (by linarith)
    rw [herr]
    calc gaussDensity t (1 / 2 + 2 * η - v) * ‖xiLine X (1 / 2 + 2 * η)‖ ≤ Q * P := h0
      _ ≤ P * ((1 + 2 * η) * A * Q) := by nlinarith

/-! ## 3. Regime I (near-axis slope positivity) and Regime II (off-axis amplitude dominance) -/

private theorem strip_exponent_collar_le_ee {w v δ₀ c E m : ℝ} (hw0 : 0 ≤ w) (hδ0 : 0 ≤ δ₀)
    (hv_lo : -δ₀ ≤ v) (hcw : w + δ₀ ≤ c) (hm : m ≤ (c - w) ^ 2 - 4 * c * E - 2 * δ₀ * c) :
    -(w - v) ^ 2 + 4 * c * E + 2 * c * (w - (v + c)) + c ^ 2 ≤ -m := by
  have hc_sub : 0 ≤ c - w - δ₀ := by linarith
  have hsq : (c - w - δ₀) ^ 2 ≤ (c - w + v) ^ 2 := by
    simpa [sq] using mul_self_le_mul_self hc_sub (by linarith : c - w - δ₀ ≤ c - w + v)
  have hid1 : -(w - v) ^ 2 + 2 * c * (w - (v + c)) + c ^ 2 = -(c - w + v) ^ 2 := by ring
  have hid2 : (c - w - δ₀) ^ 2 = (c - w) ^ 2 - 2 * δ₀ * c + 2 * δ₀ * w + δ₀ ^ 2 := by ring
  have hdw : 0 ≤ 2 * δ₀ * w := by positivity
  linarith [sq_nonneg δ₀]

private theorem strip_exponent_pos_shift_le_ee {w y c E m : ℝ} (hy0 : 0 ≤ y) (hcw : w ≤ c)
    (hm : m ≤ (c - w) ^ 2 - 4 * c * E) :
    -(w - y) ^ 2 + 4 * c * E + 2 * c * (w - (y + c)) + c ^ 2 ≤ -m := by
  have hc_sub : 0 ≤ c - w := by linarith
  have hsq : (c - w) ^ 2 ≤ (c - w + y) ^ 2 := by
    simpa [sq] using mul_self_le_mul_self hc_sub (by linarith : c - w ≤ c - w + y)
  have hid : -(w - y) ^ 2 + 2 * c * (w - (y + c)) + c ^ 2 = -(c - w + y) ^ 2 := by ring
  linarith

private theorem strip_exponent_neg_shift_le_ee {w y c E m : ℝ} (hw0 : 0 ≤ w) (hy0 : 0 ≤ y)
    (hc0 : 0 ≤ c) (hm : m ≤ (c - w) ^ 2 - 4 * c * E) :
    -(w - (-y)) ^ 2 + 4 * c * E + 2 * c * (w - (y + c)) + c ^ 2 ≤ -m := by
  have hid : -(w - (-y)) ^ 2 + 2 * c * (w - (y + c)) + c ^ 2 =
      -(c - w) ^ 2 - 2 * y * (w + c) - y ^ 2 := by ring
  have hywc : 0 ≤ 2 * y * (w + c) := by positivity
  linarith [sq_nonneg y]

/-- **Regime I: Slope positivity `Re(Q'(v) conj Q(v)) > 0` on the near-axis collar `|v| ≤ δ₀`.** -/
theorem re_slope_mul_conj_pos_ee {K η δ₀ γ m t X v : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hγ : 0 ≤ γ)
    (hK : ∀ X w u : ℝ, 16 ≤ X → 0 ≤ w → w ≤ 1 / 2 + 2 * η → 1 / 2 + 2 * η ≤ u → u ≤ X →
      ‖xiLine X w‖ ≤ K * X ^ (eeStripExp η w) *
        (X / (2 * Real.pi)) ^ ((w - u) / 2) * ‖xiLine X u‖)
    (hK0 : 0 ≤ K) (hX : 200 ≤ X) (hvδ : |v| ≤ δ₀) (hδ₀2 : δ₀ ≤ 1 / 2)
    (hα1 : 1 ≤ (horizontalSlope X).re)
    (hsep : 1 / 2 + 2 * η + γ ≤ -δ₀ + 2 * t * (horizontalSlope X).re)
    (hm : ∀ w ∈ Icc (0 : ℝ) (1 / 2 + 2 * η),
      m ≤ (2 * t * (horizontalSlope X).re - w) ^ 2 -
        4 * (2 * t * (horizontalSlope X).re) * eeStripExp η w -
        2 * δ₀ * (2 * t * (horizontalSlope X).re))
    (hW9 : 9 / 2 ≤ 2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2)
    (hWX : 2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 ≤ X / 32 - 1 / 2)
    (hS1 : chernoffLowerR1 γ t + kklR2 t (horizontalSlope X).re + sharpR3 (2 * η) t +
      sharpStripErr K (2 * η) m t (horizontalSlope X).re +
      Real.exp (9 / 2 * (1 / (2 * η) + 3)) * kklRC t (horizontalSlope X).re ≤ 1 / 5)
    (hS2 : 2 * sharpStripErr K (2 * η) m t (horizontalSlope X).re +
      Real.exp (9 / 2 * (1 / (2 * η) + 3)) *
        (kklRC t (horizontalSlope X).re + kklRB t (horizontalSlope X).re) +
      (1 / (2 * η) + 3) * (1 + sharpR3 (2 * η) t) < 18 / 25 * (horizontalSlope X).re) :
    0 < ((∫ w in Ioi (0 : ℝ), (((w - v) / (2 * t) * gaussDensity t (w - v) : ℝ) : ℂ) * xiLine X w) *
      starRingEnd ℂ (halfGaussTransform t (xiLine X) v)).re := by
  have hα0 : 0 ≤ (horizontalSlope X).re := by linarith
  have hv : |v| ≤ 1 / 2 := hvδ.trans hδ₀2
  have hv_lo : -δ₀ ≤ v := (abs_le.mp hvδ).1
  set a := horizontalSlope X with hadef
  set α := a.re with hαdef
  set u := v + 2 * t * α with hudef
  set N := ‖xiLine X u‖ with hN
  set W := 2 * t * α + α ^ 2 with hWdef
  set η' := 2 * η with hη'
  have hη'pos : 0 < η' := by positivity
  set b := 9 / 2 * (1 / η' + 3) with hbdef
  have hv2 := (abs_le.mp hv).2
  have hWu : u ≤ W := by rw [hudef, hWdef]; linarith [one_le_pow₀ hα1 (n := 2)]
  have hu_sep : 1 / 2 + η' + γ ≤ u := by rw [hudef, hη']; linarith
  have hu : u ∈ Icc (1 / 2 + η') (X / 32 - 1 / 2) :=
    ⟨by linarith, hWu.trans hWX⟩
  have hw1W : 1 / 2 + η' ≤ W := hu.1.trans hWu
  have hN0 : 0 ≤ N := norm_nonneg _
  have hNpos : 0 < N := by
    rw [hN, norm_pos_iff]
    unfold xiLine
    rw [xiLine_point]
    exact xi_ne_zero_of_one_lt_re (by simp; linarith [hu.1])
  set P := N * Real.exp (-(t * α ^ 2)) with hP
  have hP0 : 0 < P := by positivity
  have hmodel : ∀ w ∈ Icc (1 / 2 + η') W, ‖xiLine X w - xiLine X u *
      Complex.exp (((w - u : ℝ) : ℂ) * a)‖ ≤
        ‖xiLine X u‖ * Real.exp ((w - u) * a.re) * (Real.exp ((1 / η' + 3) * |w - u|) - 1) :=
    fun w hw => norm_xiLine_sub_model_le_near hX hη'pos hu ⟨hw.1, hw.2.trans hWX⟩
  have hderiv : ∀ w ∈ Icc (1 / 2 + η') W, ‖xiLineDeriv X w - a * xiLine X w‖ ≤
      (1 / η' + 3) * ‖xiLine X w‖ :=
    fun w hw => norm_xiLineDeriv_sub_le_near hX hη'pos hw.1 (hw.2.trans hWX)
  have hQ := norm_halfGaussTransform_sub_main_le ht (continuous_xiLine X)
    (integrable_exp_mul_norm_xiLine ht X) (y := v) (by positivity) (by linarith) hw1W hmodel
  have hD := norm_slope_sub_mul_le ht (hasDerivAt_xiLine X) (continuous_xiLineDeriv X)
    (integrable_exp_mul_norm_xiLine ht X) (y := v) (by linarith) hw1W hderiv
  have hT1 := chernoff_lowerTail_le ht hγ hu_sep hN0
  have hT2 := upperTail_le ht hv hN0 (α := α)
  have hT3 := sharp_modelError_le (η := η') (α := α) (y := v) ht hη'pos hN0
  have hM := sharp_windowMass_le (η := η') ht hη'pos hX hu hWX
  have hcX : u ≤ X := by have := hu.2; linarith
  have hexp_strip : ∀ w ∈ Icc (0 : ℝ) (1 / 2 + 2 * η),
      -(w - v) ^ 2 + 4 * (2 * t * α) * eeStripExp η w +
        2 * (2 * t * α) * (w - u) + (2 * t * α) ^ 2 ≤ -m := fun w hw => by
    rw [hudef]
    exact strip_exponent_collar_le_ee hw.1 ((abs_nonneg v).trans hvδ) hv_lo
      (by linarith [hw.2]) (hm w hw)
  obtain ⟨hSA, hOA, hB1⟩ := ee_strip_terms_le_anchor ht hη hK hK0 (by linarith) hv hα0
    hu.1 hcX hη8 hexp_strip
  have hFWb : ‖xiLine X W‖ ≤ (Real.exp b * N) * Real.exp ((W - u) * (α + 1 / 8)) :=
    norm_xiLine_far_end_le hX hη'pos hu hW9 hWu hWX
  obtain ⟨hSC, hOC, hB2⟩ := far_terms_le_of_bound (b := b) ht ht8 hX hv hα1 hW9 hFWb
  have hph := gaussPhase_ge ht8 ht
  have hmain := norm_main_eq (t := t) (X := X) (y := v) (xiLine X u)
  rw [← hadef, ← hαdef, ← hudef] at hmain
  have hmain' : ‖xiLine X u * Complex.exp (-((u : ℂ) * a)) *
      Complex.exp (v * a + t * a ^ 2)‖ = P * Real.exp (-(t * (Real.pi / 4) ^ 2)) := by
    rw [hmain, hP, hN]
  set S₁ := chernoffLowerR1 γ t + kklR2 t α + sharpR3 η' t + sharpStripErr K η' m t α +
    Real.exp b * kklRC t α with hS₁
  set S₂ := 2 * sharpStripErr K η' m t α + Real.exp b * (kklRC t α + kklRB t α) +
    (1 / η' + 3) * (1 + sharpR3 η' t) with hS₂
  refine re_mul_conj_pos_of_estimates (Main := xiLine X u * Complex.exp (-((u : ℂ) * a)) *
      Complex.exp (v * a + t * a ^ 2)) (E₁ := P * S₁) (E₂ := P * S₂) hα0 ?_ ?_ ?_ ?_
  · refine hQ.trans ?_
    have e : ‖xiLine X u‖ * Real.exp (-(u * a.re)) *
        ((∫ w in Iic (1 / 2 + η' : ℝ), gaussDensity t (w - v) * Real.exp (w * a.re)) +
          (∫ w in Ioi W, gaussDensity t (w - v) * Real.exp (w * a.re)) +
          ∫ w, gaussDensity t (w - v) * Real.exp (w * a.re) *
            (Real.exp ((1 / η' + 3) * |w - u|) - 1)) =
        N * Real.exp (-(u * α)) * (∫ w in Iic (1 / 2 + η' : ℝ),
            gaussDensity t (w - v) * Real.exp (w * α)) +
        N * Real.exp (-(u * α)) * (∫ w in Ioi W, gaussDensity t (w - v) * Real.exp (w * α)) +
        N * Real.exp (-(u * α)) *
          ∫ w, gaussDensity t (w - v) * Real.exp (w * α) *
            (Real.exp ((1 / η' + 3) * |w - u|) - 1) := by ring
    rw [e]
    have hOC' : ∫ w in Ioi W, gaussDensity t (w - v) * ‖xiLine X w‖ ≤
        P * (Real.exp b * kklRC t α) := hOC.trans (le_of_eq (by rw [hP]; ring))
    rw [← hudef] at hT1 hT3
    have hsum : P * chernoffLowerR1 γ t + P * kklR2 t α + P * sharpR3 η' t +
        P * sharpStripErr K η' m t α + P * (Real.exp b * kklRC t α) = P * S₁ := by
      rw [hS₁]; ring
    linarith
  · refine hD.trans ?_
    have hSC' : ∫ w in Ioi W, (|(w - v) / (2 * t)| + ‖a‖) * gaussDensity t (w - v) *
        ‖xiLine X w‖ ≤ P * (Real.exp b * kklRC t α) := hSC.trans (le_of_eq (by rw [hP]; ring))
    have hB2' : gaussDensity t (W - v) * ‖xiLine X W‖ ≤ P * (Real.exp b * kklRB t α) :=
      hB2.trans (le_of_eq (by rw [hP]; ring))
    have hM' : (1 / η' + 3) * ∫ w in Ioc (1 / 2 + η') W, gaussDensity t (w - v) * ‖xiLine X w‖ ≤
        (1 / η' + 3) * (P * (1 + sharpR3 η' t)) := by gcongr
    have hsum : P * sharpStripErr K η' m t α + P * (Real.exp b * kklRC t α) +
        P * sharpStripErr K η' m t α + P * (Real.exp b * kklRB t α) +
        (1 / η' + 3) * (P * (1 + sharpR3 η' t)) = P * S₂ := by rw [hS₂]; ring
    linarith
  · rw [hmain']
    have h1 := mul_le_mul_of_nonneg_left hph hP0.le
    have : P * S₁ ≤ P * (1 / 5) := mul_le_mul_of_nonneg_left hS1 hP0.le
    linarith
  · rw [hmain']
    have h1 := mul_le_mul_of_nonneg_left hph hP0.le
    have h2 : P * S₁ ≤ P * (1 / 5) := mul_le_mul_of_nonneg_left hS1 hP0.le
    have h3 : P * S₂ < P * (18 / 25 * α) := mul_lt_mul_of_pos_left hS2 hP0
    have h4 : 18 / 25 * P ≤ P * Real.exp (-(t * (Real.pi / 4) ^ 2)) - P * S₁ := by linarith
    have h5 : α * (18 / 25 * P) ≤ α * (P * Real.exp (-(t * (Real.pi / 4) ^ 2)) - P * S₁) :=
      mul_le_mul_of_nonneg_left h4 hα0
    have h6 : P * (18 / 25 * α) = α * (18 / 25 * P) := by ring
    linarith

private theorem setIntegral_Ioi_neg_shift_le_ee {t X y W : ℝ} (ht : 0 < t) (hy0 : 0 ≤ y)
    (hW0 : 0 ≤ W) :
    ∫ w in Ioi W, gaussDensity t (w - (-y)) * ‖xiLine X w‖ ≤
      ∫ w in Ioi W, gaussDensity t (w - y) * ‖xiLine X w‖ := by
  have hGF_pos := (integrable_gaussDensity_sub_mul ht (continuous_xiLine X)
    (integrable_exp_mul_norm_xiLine ht X) y).norm.congr
    (Eventually.of_forall fun w => norm_gauss_mul t y w ht _)
  refine integral_mono_of_nonneg (Eventually.of_forall fun w =>
    mul_nonneg (gaussDensity_pos ht _).le (norm_nonneg _)) hGF_pos.integrableOn ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun w hw => ?_)
  have hw0 : 0 < w := lt_of_le_of_lt hW0 hw
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  unfold gaussDensity
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  have hsq : (w - y) ^ 2 ≤ (w - (-y)) ^ 2 := by
    have hwy : 0 ≤ 4 * w * y := by positivity
    linarith [show (w - (-y)) ^ 2 - (w - y) ^ 2 = 4 * w * y by ring]
  have hdiv : (w - y) ^ 2 / (4 * t) ≤ (w - (-y)) ^ 2 / (4 * t) :=
    div_le_div_of_nonneg_right hsq (by positivity)
  linarith

private theorem setIntegral_window_neg_shift_le_ee {η' δ₀ t X y W : ℝ} (ht : 0 < t)
    (hη'pos : 0 < η') (hyδ : δ₀ ≤ y) (hy0 : 0 ≤ y) (hy2 : y ≤ 1 / 2)
    (hα0 : 0 ≤ (horizontalSlope X).re)
    (hmodel : ∀ w ∈ Icc (1 / 2 + η') W,
      ‖xiLine X w - xiLine X (y + 2 * t * (horizontalSlope X).re) *
          Complex.exp (((w - (y + 2 * t * (horizontalSlope X).re) : ℝ) : ℂ) * horizontalSlope X)‖ ≤
        ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
          Real.exp ((w - (y + 2 * t * (horizontalSlope X).re)) * (horizontalSlope X).re) *
          (Real.exp ((1 / η' + 3) * |w - (y + 2 * t * (horizontalSlope X).re)|) - 1)) :
    ∫ w in Ioc (1 / 2 + η') W, gaussDensity t (w - (-y)) * ‖xiLine X w‖ ≤
      (‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
          Real.exp (-(t * (horizontalSlope X).re ^ 2))) *
        (Real.exp ((1 / η' + 3) - 2 * δ₀ * (horizontalSlope X).re) * (1 + sharpR3 η' t)) := by
  have hη₁0 : 0 ≤ 1 / η' + 3 := by positivity
  have hN0 : 0 ≤ ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ := norm_nonneg _
  have hint1 := integrable_gaussDensity_sub_mul_rexp ht (-y) (horizontalSlope X).re
  have hint2 := integrable_modelError ht (-y) (horizontalSlope X).re
    (-y + 2 * t * (horizontalSlope X).re) (1 / η' + 3) hη₁0
  have hmaj : Integrable (fun w =>
      ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
        Real.exp (-((y + 2 * t * (horizontalSlope X).re) * (horizontalSlope X).re)) *
        Real.exp (1 / η' + 3) *
        (gaussDensity t (w - (-y)) * Real.exp (w * (horizontalSlope X).re) +
          gaussDensity t (w - (-y)) * Real.exp (w * (horizontalSlope X).re) *
            (Real.exp ((1 / η' + 3) * |w - (-y + 2 * t * (horizontalSlope X).re)|) - 1))) :=
    (hint1.add hint2).const_mul _
  have hnonneg : ∀ w, 0 ≤
      ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
        Real.exp (-((y + 2 * t * (horizontalSlope X).re) * (horizontalSlope X).re)) *
        Real.exp (1 / η' + 3) *
        (gaussDensity t (w - (-y)) * Real.exp (w * (horizontalSlope X).re) +
          gaussDensity t (w - (-y)) * Real.exp (w * (horizontalSlope X).re) *
            (Real.exp ((1 / η' + 3) * |w - (-y + 2 * t * (horizontalSlope X).re)|) - 1)) := by
    intro w
    have h1 : 1 ≤ Real.exp ((1 / η' + 3) * |w - (-y + 2 * t * (horizontalSlope X).re)|) :=
      Real.one_le_exp (by positivity)
    have := gaussDensity_sub_mul_rexp_nonneg ht (-y) (horizontalSlope X).re w
    positivity
  have hstep1 : ∫ w in Ioc (1 / 2 + η') W, gaussDensity t (w - (-y)) * ‖xiLine X w‖ ≤
      ∫ w in Ioc (1 / 2 + η') W,
        ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
          Real.exp (-((y + 2 * t * (horizontalSlope X).re) * (horizontalSlope X).re)) *
          Real.exp (1 / η' + 3) *
          (gaussDensity t (w - (-y)) * Real.exp (w * (horizontalSlope X).re) +
            gaussDensity t (w - (-y)) * Real.exp (w * (horizontalSlope X).re) *
              (Real.exp ((1 / η' + 3) * |w - (-y + 2 * t * (horizontalSlope X).re)|) - 1)) := by
    refine integral_mono_of_nonneg (Eventually.of_forall fun w =>
      mul_nonneg (gaussDensity_pos ht _).le (norm_nonneg _)) hmaj.integrableOn ?_
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun w hw => ?_)
    have hm_w := hmodel w (Ioc_subset_Icc_self hw)
    have hn : ‖xiLine X (y + 2 * t * (horizontalSlope X).re) *
        Complex.exp (((w - (y + 2 * t * (horizontalSlope X).re) : ℝ) : ℂ) * horizontalSlope X)‖ =
        ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
          Real.exp ((w - (y + 2 * t * (horizontalSlope X).re)) * (horizontalSlope X).re) := by
      rw [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul]
    have htri := norm_sub_norm_le (xiLine X w)
      (xiLine X (y + 2 * t * (horizontalSlope X).re) *
        Complex.exp (((w - (y + 2 * t * (horizontalSlope X).re) : ℝ) : ℂ) * horizontalSlope X))
    rw [hn] at htri
    have hFw : ‖xiLine X w‖ ≤ ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
        Real.exp ((w - (y + 2 * t * (horizontalSlope X).re)) * (horizontalSlope X).re) *
        Real.exp ((1 / η' + 3) * |w - (y + 2 * t * (horizontalSlope X).re)|) := by
      linarith [show ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
        Real.exp ((w - (y + 2 * t * (horizontalSlope X).re)) * (horizontalSlope X).re) *
        (Real.exp ((1 / η' + 3) * |w - (y + 2 * t * (horizontalSlope X).re)|) - 1) +
        ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
          Real.exp ((w - (y + 2 * t * (horizontalSlope X).re)) * (horizontalSlope X).re) =
        ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
          Real.exp ((w - (y + 2 * t * (horizontalSlope X).re)) * (horizontalSlope X).re) *
          Real.exp ((1 / η' + 3) * |w - (y + 2 * t * (horizontalSlope X).re)|) by ring]
    have habs_le : |w - (y + 2 * t * (horizontalSlope X).re)| ≤
        |w - (-y + 2 * t * (horizontalSlope X).re)| + 1 := by
      have heq : w - (y + 2 * t * (horizontalSlope X).re) =
          (w - (-y + 2 * t * (horizontalSlope X).re)) + (-2 * y) := by ring
      have h2y : |-2 * y| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      calc |w - (y + 2 * t * (horizontalSlope X).re)|
          = |(w - (-y + 2 * t * (horizontalSlope X).re)) + (-2 * y)| := by rw [heq]
        _ ≤ |w - (-y + 2 * t * (horizontalSlope X).re)| + |-2 * y| := abs_add_le _ _
        _ ≤ |w - (-y + 2 * t * (horizontalSlope X).re)| + 1 := by linarith
    have hexp_abs : Real.exp ((1 / η' + 3) * |w - (y + 2 * t * (horizontalSlope X).re)|) ≤
        Real.exp (1 / η' + 3) *
          Real.exp ((1 / η' + 3) * |w - (-y + 2 * t * (horizontalSlope X).re)|) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by
        linarith [mul_le_mul_of_nonneg_left habs_le hη₁0,
          show (1 / η' + 3) * (|w - (-y + 2 * t * (horizontalSlope X).re)| + 1) =
            (1 / η' + 3) + (1 / η' + 3) * |w - (-y + 2 * t * (horizontalSlope X).re)| by ring])
    have hsplit_exp :
        Real.exp ((w - (y + 2 * t * (horizontalSlope X).re)) * (horizontalSlope X).re) =
          Real.exp (-((y + 2 * t * (horizontalSlope X).re) * (horizontalSlope X).re)) *
            Real.exp (w * (horizontalSlope X).re) := by
      rw [← Real.exp_add]; ring_nf
    rw [hsplit_exp] at hFw
    exact (mul_le_mul_of_nonneg_left
      (hFw.trans (mul_le_mul_of_nonneg_left hexp_abs (by positivity)))
      (gaussDensity_pos ht _).le).trans_eq (by ring)
  refine hstep1.trans ((setIntegral_le_integral hmaj (Eventually.of_forall hnonneg)).trans ?_)
  rw [integral_const_mul, integral_add hint1 hint2]
  have hexp_shift :
      Real.exp (-((y + 2 * t * (horizontalSlope X).re) * (horizontalSlope X).re)) *
        Real.exp (1 / η' + 3) =
      Real.exp ((1 / η' + 3) - 2 * y * (horizontalSlope X).re) *
        Real.exp (-((-y + 2 * t * (horizontalSlope X).re) * (horizontalSlope X).re)) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have heq : ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
      Real.exp (-((y + 2 * t * (horizontalSlope X).re) * (horizontalSlope X).re)) *
      Real.exp (1 / η' + 3) *
      ((∫ w, gaussDensity t (w - (-y)) * Real.exp (w * (horizontalSlope X).re)) +
        (∫ w, gaussDensity t (w - (-y)) * Real.exp (w * (horizontalSlope X).re) *
          (Real.exp ((1 / η' + 3) * |w - (-y + 2 * t * (horizontalSlope X).re)|) - 1))) =
      Real.exp ((1 / η' + 3) - 2 * y * (horizontalSlope X).re) *
        ((‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
            Real.exp (-((-y + 2 * t * (horizontalSlope X).re) * (horizontalSlope X).re)) *
            ∫ w, gaussDensity t (w - (-y)) * Real.exp (w * (horizontalSlope X).re)) +
          (‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
            Real.exp (-((-y + 2 * t * (horizontalSlope X).re) * (horizontalSlope X).re)) *
            ∫ w, gaussDensity t (w - (-y)) * Real.exp (w * (horizontalSlope X).re) *
              (Real.exp ((1 / η' + 3) * |w - (-y + 2 * t * (horizontalSlope X).re)|) - 1))) := by
    rw [mul_assoc ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖, hexp_shift]; ring
  rw [heq, tiltedMass_eq ht]
  have hme := sharp_modelError_le (η := η') (α := (horizontalSlope X).re) (y := -y)
    (N := ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖) ht hη'pos hN0
  have hexp_δ : Real.exp ((1 / η' + 3) - 2 * y * (horizontalSlope X).re) ≤
      Real.exp ((1 / η' + 3) - 2 * δ₀ * (horizontalSlope X).re) :=
    Real.exp_le_exp.mpr (by linarith [mul_le_mul_of_nonneg_right hyδ hα0])
  refine (mul_le_mul hexp_δ (add_le_add le_rfl hme) ?_ (Real.exp_pos _).le).trans_eq (by ring)
  exact add_nonneg (by positivity)
    (mul_nonneg (by positivity) (integral_nonneg fun w => mul_nonneg
      (gaussDensity_sub_mul_rexp_nonneg ht (-y) (horizontalSlope X).re w)
      (by linarith [Real.one_le_exp (show 0 ≤ (1 / η' + 3) *
        |w - (-y + 2 * t * (horizontalSlope X).re)| by positivity)])))

private theorem norm_halfGaussTransform_le_three_parts_ee {t X v w₁ W B₁ B₂ B₃ : ℝ} (ht : 0 < t)
    (hw₁ : 0 < w₁) (hw₁W : w₁ ≤ W)
    (h1 : ∫ w in Ioc 0 w₁, gaussDensity t (w - v) * ‖xiLine X w‖ ≤ B₁)
    (h2 : ∫ w in Ioc w₁ W, gaussDensity t (w - v) * ‖xiLine X w‖ ≤ B₂)
    (h3 : ∫ w in Ioi W, gaussDensity t (w - v) * ‖xiLine X w‖ ≤ B₃) :
    ‖halfGaussTransform t (xiLine X) v‖ ≤ B₁ + B₂ + B₃ := by
  have hGF := integrable_gaussDensity_sub_mul ht (continuous_xiLine X)
    (integrable_exp_mul_norm_xiLine ht X) v
  have hsplit : halfGaussTransform t (xiLine X) v =
      (∫ w in Ioc 0 w₁, (gaussDensity t (w - v) : ℂ) * xiLine X w) +
      (∫ w in Ioc w₁ W, (gaussDensity t (w - v) : ℂ) * xiLine X w) +
      (∫ w in Ioi W, (gaussDensity t (w - v) : ℂ) * xiLine X w) := by
    unfold halfGaussTransform
    exact setIntegral_Ioi_split hw₁.le hw₁W hGF.integrableOn
  rw [hsplit]
  have hn1 : ‖∫ w in Ioc 0 w₁, (gaussDensity t (w - v) : ℂ) * xiLine X w‖ ≤ B₁ :=
    ((norm_integral_le_integral_norm _).trans
      (le_of_eq (by congr 1; funext w; exact norm_gauss_mul t v w ht _))).trans h1
  have hn2 : ‖∫ w in Ioc w₁ W, (gaussDensity t (w - v) : ℂ) * xiLine X w‖ ≤ B₂ :=
    ((norm_integral_le_integral_norm _).trans
      (le_of_eq (by congr 1; funext w; exact norm_gauss_mul t v w ht _))).trans h2
  have hn3 : ‖∫ w in Ioi W, (gaussDensity t (w - v) : ℂ) * xiLine X w‖ ≤ B₃ :=
    ((norm_integral_le_integral_norm _).trans
      (le_of_eq (by congr 1; funext w; exact norm_gauss_mul t v w ht _))).trans h3
  exact (((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)).trans
    (add_le_add (add_le_add hn1 hn2) hn3))

/-- **Regime II: Direct off-axis amplitude dominance `‖Q(−y)‖ < ‖Q(y)‖` on `δ₀ ≤ y ≤ 1/2`.**
Both `Q(y)` and `Q(−y)` are estimated against the positive-shift Euler anchor `u_+ = y + 2tα`,
eliminating any need for `−y + 2tα` to enter `Re s > 1`. -/
theorem norm_neg_lt_norm_pos_ee {K η δ₀ γ m t X y : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (hη : 0 < η) (hη8 : η ≤ 1 / 8) (hδ₀ : 0 < δ₀) (hγ : 0 ≤ γ) (hδγ : δ₀ ≤ γ)
    (hK : ∀ X w u : ℝ, 16 ≤ X → 0 ≤ w → w ≤ 1 / 2 + 2 * η → 1 / 2 + 2 * η ≤ u → u ≤ X →
      ‖xiLine X w‖ ≤ K * X ^ (eeStripExp η w) *
        (X / (2 * Real.pi)) ^ ((w - u) / 2) * ‖xiLine X u‖)
    (hK0 : 0 ≤ K) (hX : 200 ≤ X) (hyδ : δ₀ ≤ y) (hy2 : y ≤ 1 / 2)
    (hα1 : 1 ≤ (horizontalSlope X).re)
    (hsep : 1 / 2 + 2 * η + γ ≤ δ₀ + 2 * t * (horizontalSlope X).re)
    (hm : ∀ w ∈ Icc (0 : ℝ) (1 / 2 + 2 * η),
      m ≤ (2 * t * (horizontalSlope X).re - w) ^ 2 -
        4 * (2 * t * (horizontalSlope X).re) * eeStripExp η w)
    (hW9 : 9 / 2 ≤ 2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2)
    (hWX : 2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 ≤ X / 32 - 1 / 2)
    (hS1 : chernoffLowerR1 γ t + kklR2 t (horizontalSlope X).re + sharpR3 (2 * η) t +
      sharpStripErr K (2 * η) m t (horizontalSlope X).re +
      Real.exp (9 / 2 * (1 / (2 * η) + 3)) * kklRC t (horizontalSlope X).re ≤ 1 / 5)
    (hS_neg : sharpStripErr K (2 * η) m t (horizontalSlope X).re +
      Real.exp (1 / (2 * η) + 3 - 2 * δ₀ * (horizontalSlope X).re) * (1 + sharpR3 (2 * η) t) +
      Real.exp (9 / 2 * (1 / (2 * η) + 3)) * kklRC t (horizontalSlope X).re < 18 / 25) :
    ‖halfGaussTransform t (xiLine X) (-y)‖ < ‖halfGaussTransform t (xiLine X) y‖ := by
  have hy0 : 0 ≤ y := hδ₀.le.trans hyδ
  have hy_abs : |y| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, hy2⟩
  have hny_abs : |-y| ≤ 1 / 2 := by rwa [abs_neg]
  have hα0 : 0 ≤ (horizontalSlope X).re := by linarith
  have hη'pos : 0 < 2 * η := by positivity
  have hWu : y + 2 * t * (horizontalSlope X).re ≤
      2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 := by
    linarith [one_le_pow₀ hα1 (n := 2)]
  have hu_sep : 1 / 2 + 2 * η + γ ≤ y + 2 * t * (horizontalSlope X).re := by linarith
  have hu : y + 2 * t * (horizontalSlope X).re ∈ Icc (1 / 2 + 2 * η) (X / 32 - 1 / 2) :=
    ⟨by linarith, hWu.trans hWX⟩
  have hw1W : 1 / 2 + 2 * η ≤ 2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 :=
    hu.1.trans hWu
  have hN0 : 0 ≤ ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ := norm_nonneg _
  have hNpos : 0 < ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ := by
    rw [norm_pos_iff]; unfold xiLine; rw [xiLine_point]
    exact xi_ne_zero_of_one_lt_re (by simp; linarith [hu.1])
  have hP0 : 0 < ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
      Real.exp (-(t * (horizontalSlope X).re ^ 2)) := by positivity
  have hcX : y + 2 * t * (horizontalSlope X).re ≤ X := by have := hu.2; linarith
  have hmodel : ∀ w ∈ Icc (1 / 2 + 2 * η)
      (2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2),
      ‖xiLine X w - xiLine X (y + 2 * t * (horizontalSlope X).re) *
          Complex.exp (((w - (y + 2 * t * (horizontalSlope X).re) : ℝ) : ℂ) * horizontalSlope X)‖ ≤
        ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
          Real.exp ((w - (y + 2 * t * (horizontalSlope X).re)) * (horizontalSlope X).re) *
          (Real.exp ((1 / (2 * η) + 3) * |w - (y + 2 * t * (horizontalSlope X).re)|) - 1) :=
    fun w hw => norm_xiLine_sub_model_le_near hX hη'pos hu ⟨hw.1, hw.2.trans hWX⟩
  -- 1. Lower bound on `‖Q(y)‖`.
  have hQy := norm_halfGaussTransform_sub_main_le ht (continuous_xiLine X)
    (integrable_exp_mul_norm_xiLine ht X) (y := y) (by positivity) (by linarith) hw1W hmodel
  have hT1 := chernoff_lowerTail_le ht hγ hu_sep hN0
  have hT2 := upperTail_le ht hy_abs hN0 (α := (horizontalSlope X).re)
  have hT3 := sharp_modelError_le (η := 2 * η) (α := (horizontalSlope X).re) (y := y) ht hη'pos hN0
  obtain ⟨_, hOA_pos, _⟩ := ee_strip_terms_le_anchor ht hη hK hK0 (by linarith) hy_abs hα0
    hu.1 hcX hη8 fun w hw =>
      strip_exponent_pos_shift_le_ee hy0 (by linarith [hw.2, hsep, hδγ]) (hm w hw)
  have hFWb : ‖xiLine X (2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2)‖ ≤
      (Real.exp (9 / 2 * (1 / (2 * η) + 3)) * ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖) *
        Real.exp ((2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 -
          (y + 2 * t * (horizontalSlope X).re)) * ((horizontalSlope X).re + 1 / 8)) :=
    norm_xiLine_far_end_le hX hη'pos hu hW9 hWu hWX
  obtain ⟨_, hOC_pos, _⟩ := far_terms_le_of_bound (b := 9 / 2 * (1 / (2 * η) + 3)) ht ht8 hX
    hy_abs hα1 hW9 hFWb
  have hQy_low : 18 / 25 * (‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
      Real.exp (-(t * (horizontalSlope X).re ^ 2))) ≤ ‖halfGaussTransform t (xiLine X) y‖ := by
    have hmain := norm_main_eq (t := t) (X := X) (y := y)
      (xiLine X (y + 2 * t * (horizontalSlope X).re))
    have hph := mul_le_mul_of_nonneg_left (gaussPhase_ge ht8 ht) hP0.le
    have hOC' : ∫ w in Ioi (2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2),
        gaussDensity t (w - y) * ‖xiLine X w‖ ≤
        (‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
          Real.exp (-(t * (horizontalSlope X).re ^ 2))) *
          (Real.exp (9 / 2 * (1 / (2 * η) + 3)) * kklRC t (horizontalSlope X).re) :=
      hOC_pos.trans (le_of_eq (by ring))
    have hdiff : ‖halfGaussTransform t (xiLine X) y -
        xiLine X (y + 2 * t * (horizontalSlope X).re) *
          Complex.exp (-(((y + 2 * t * (horizontalSlope X).re : ℝ) : ℂ) * horizontalSlope X)) *
          Complex.exp (y * horizontalSlope X + t * horizontalSlope X ^ 2)‖ ≤
        (‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
          Real.exp (-(t * (horizontalSlope X).re ^ 2))) * (1 / 5) := by
      refine hQy.trans ?_
      have hS1P := mul_le_mul_of_nonneg_left hS1 hP0.le
      have hring : ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
          Real.exp (-((y + 2 * t * (horizontalSlope X).re) * (horizontalSlope X).re)) *
          ((∫ w in Iic (1 / 2 + 2 * η : ℝ), gaussDensity t (w - y) *
              Real.exp (w * (horizontalSlope X).re)) +
            (∫ w in Ioi (2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2),
              gaussDensity t (w - y) * Real.exp (w * (horizontalSlope X).re)) +
            ∫ w, gaussDensity t (w - y) * Real.exp (w * (horizontalSlope X).re) *
              (Real.exp ((1 / (2 * η) + 3) * |w - (y + 2 * t * (horizontalSlope X).re)|) - 1)) =
          ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
            Real.exp (-((y + 2 * t * (horizontalSlope X).re) * (horizontalSlope X).re)) *
            (∫ w in Iic (1 / 2 + 2 * η : ℝ), gaussDensity t (w - y) *
              Real.exp (w * (horizontalSlope X).re)) +
          ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
            Real.exp (-((y + 2 * t * (horizontalSlope X).re) * (horizontalSlope X).re)) *
            (∫ w in Ioi (2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2),
              gaussDensity t (w - y) * Real.exp (w * (horizontalSlope X).re)) +
          ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
            Real.exp (-((y + 2 * t * (horizontalSlope X).re) * (horizontalSlope X).re)) *
            ∫ w, gaussDensity t (w - y) * Real.exp (w * (horizontalSlope X).re) *
              (Real.exp ((1 / (2 * η) + 3) * |w - (y + 2 * t * (horizontalSlope X).re)|) - 1) := by
        ring
      rw [hring]
      linarith
    have htri := norm_sub_norm_le
      (xiLine X (y + 2 * t * (horizontalSlope X).re) *
        Complex.exp (-(((y + 2 * t * (horizontalSlope X).re : ℝ) : ℂ) * horizontalSlope X)) *
        Complex.exp (y * horizontalSlope X + t * horizontalSlope X ^ 2))
      (halfGaussTransform t (xiLine X) y)
    rw [norm_sub_rev, hmain] at htri
    linarith [show ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
      Real.exp (-(t * (horizontalSlope X).re ^ 2)) * Real.exp (-(t * (Real.pi / 4) ^ 2)) =
      (‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
        Real.exp (-(t * (horizontalSlope X).re ^ 2))) * Real.exp (-(t * (Real.pi / 4) ^ 2)) by ring]
  -- 2. Upper bound on `‖Q(−y)‖`.
  obtain ⟨_, hOA_neg, _⟩ := ee_strip_terms_le_anchor ht hη hK hK0 (by linarith) hny_abs hα0
    hu.1 hcX hη8 fun w hw => strip_exponent_neg_shift_le_ee hw.1 hy0 (by positivity) (hm w hw)
  have hWin_neg := setIntegral_window_neg_shift_le_ee ht hη'pos hyδ hy0 hy2 hα0 hmodel
  have hOC_neg : ∫ w in Ioi (2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2),
      gaussDensity t (w - (-y)) * ‖xiLine X w‖ ≤
      (‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
        Real.exp (-(t * (horizontalSlope X).re ^ 2))) *
        (Real.exp (9 / 2 * (1 / (2 * η) + 3)) * kklRC t (horizontalSlope X).re) :=
    (setIntegral_Ioi_neg_shift_le_ee ht hy0 (by linarith)).trans (hOC_pos.trans (le_of_eq (by ring)))
  have hQneg_le := norm_halfGaussTransform_le_three_parts_ee ht (by linarith) hw1W
    hOA_neg hWin_neg hOC_neg
  have hlt_P := mul_lt_mul_of_pos_left hS_neg hP0
  linarith [show (‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
      Real.exp (-(t * (horizontalSlope X).re ^ 2))) *
      (sharpStripErr K (2 * η) m t (horizontalSlope X).re +
        Real.exp (1 / (2 * η) + 3 - 2 * δ₀ * (horizontalSlope X).re) * (1 + sharpR3 (2 * η) t) +
        Real.exp (9 / 2 * (1 / (2 * η) + 3)) * kklRC t (horizontalSlope X).re) =
    (‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
      Real.exp (-(t * (horizontalSlope X).re ^ 2))) *
        sharpStripErr K (2 * η) m t (horizontalSlope X).re +
    (‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
      Real.exp (-(t * (horizontalSlope X).re ^ 2))) *
        (Real.exp (1 / (2 * η) + 3 - 2 * δ₀ * (horizontalSlope X).re) * (1 + sharpR3 (2 * η) t)) +
    (‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
      Real.exp (-(t * (horizontalSlope X).re ^ 2))) *
        (Real.exp (9 / 2 * (1 / (2 * η) + 3)) * kklRC t (horizontalSlope X).re) by ring]


/-! ## 4. Parameter choice above `2/3` -/

/-- **Parameters for the `2/3` horizon.**
For every `c₀ > 2/3`, there exist `η, δ₀, m > 0` such that:
* the near-axis collar `|v| ≤ δ₀` keeps `v + c ≥ 1/2 + 2η + 1/10` for all `c ≥ c₀`; and
* `(c − w)² − 4c · eeStripExp η w − 2δ₀ c ≥ m` on `[0, 1/2 + 2η]` for all `c ≥ c₀`. -/
theorem exists_twoThirds_params {c₀ : ℝ} (hc₀ : 2 / 3 < c₀) :
    ∃ η δ₀ m : ℝ, 0 < η ∧ η ≤ 1 / 40 ∧ 0 < δ₀ ∧ δ₀ ≤ 1 / 40 ∧ 0 < m ∧
      1 / 2 + 2 * η + 1 / 10 ≤ -δ₀ + c₀ ∧
      (∀ c : ℝ, c₀ ≤ c → ∀ w ∈ Icc (0 : ℝ) (1 / 2 + 2 * η),
        m ≤ (c - w) ^ 2 - 4 * c * eeStripExp η w - 2 * δ₀ * c) := by
  set d := c₀ - 2 / 3 with hd
  have hd0 : 0 < d := by linarith
  set η := min (1 / 1000) (d / 40) with hηdef
  have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
  have hη1000 : η ≤ 1 / 1000 := min_le_left _ _
  have hηd : η ≤ d / 40 := min_le_right _ _
  set m := min (d / 4) (1 / 250) with hmdef
  have hm0 : 0 < m := lt_min (by positivity) (by norm_num)
  have hmd : m ≤ d / 4 := min_le_left _ _
  have hm250 : m ≤ 1 / 250 := min_le_right _ _
  refine ⟨η, η, m, hη0, by linarith, hη0, by linarith, hm0, by linarith, fun c hc w hw => ?_⟩
  have hc_pos : 1 / 2 ≤ c := by linarith
  have hcd : d ≤ c - 2 / 3 := by linarith
  unfold eeStripExp
  split_ifs with hw1 hw2
  · have hid : (c - w) ^ 2 - 4 * c * (1 / 6 + η - w / 2) - 2 * η * c =
        w ^ 2 + c * (c - 2 / 3 - 6 * η) := by ring
    rw [hid]
    have hgap : d / 2 ≤ c - 2 / 3 - 6 * η := by linarith
    nlinarith [sq_nonneg w, mul_le_mul hc_pos hgap (by positivity) (by linarith)]
  · have hid : (c - w) ^ 2 - 4 * c * (1 / 9 + η - 5 / 13 * (w - 1 / 9)) - 2 * η * c =
        (w - 3 * c / 13) ^ 2 + c * (160 / 169 * c - 8 / 13 - 6 * η) := by ring
    rw [hid]
    have hgap : 1 / 125 ≤ 160 / 169 * c - 8 / 13 - 6 * η := by nlinarith
    nlinarith [sq_nonneg (w - 3 * c / 13), mul_le_mul hc_pos hgap (by norm_num) (by linarith)]
  · have hp2 := four_mul_interiorStripExp_piece2_le hη0.le (le_of_not_ge hw2) hw.2
    have hmul : 4 * c * (interiorStripRateTwo η * (1 / 2 + 2 * η - w)) ≤
        c * (1 / 2 - w + 8 * η) := by
      have := mul_le_mul_of_nonneg_left hp2 (by linarith : 0 ≤ c)
      linarith
    have hid : (c - w) ^ 2 - c * (1 / 2 - w + 8 * η) - 2 * η * c =
        (w - c / 2) ^ 2 + c * (3 / 4 * (c - 2 / 3) - 10 * η) := by ring
    have hgap : d / 2 ≤ 3 / 4 * (c - 2 / 3) - 10 * η := by linarith
    nlinarith [sq_nonneg (w - c / 2), mul_le_mul hc_pos hgap (by positivity) (by linarith)]

/-! ## 5. Horizon assembly above `2/3` -/

/-- **Large-height collar slope positivity and full-strip nonvanishing above `2/3`.** -/
theorem re_slope_zero_and_ne_zero_ee {c₀ η δ₀ m K α₀ t X : ℝ}
    (hη : 0 < η) (hη40 : η ≤ 1 / 40) (hδ₀ : 0 < δ₀) (hδ₀40 : δ₀ ≤ 1 / 40) (hm : 0 < m)
    (hc₀ : 2 / 3 < c₀)
    (_ : 1 / 2 + 2 * η + 1 / 10 ≤ -δ₀ + c₀)
    (hmc : ∀ c : ℝ, c₀ ≤ c → ∀ w ∈ Icc (0 : ℝ) (1 / 2 + 2 * η),
      m ≤ (c - w) ^ 2 - 4 * c * eeStripExp η w - 2 * δ₀ * c)
    (hK : ∀ X w u : ℝ, 16 ≤ X → 0 ≤ w → w ≤ 1 / 2 + 2 * η → 1 / 2 + 2 * η ≤ u → u ≤ X →
      ‖xiLine X w‖ ≤ K * X ^ (eeStripExp η w) *
        (X / (2 * Real.pi)) ^ ((w - u) / 2) * ‖xiLine X u‖)
    (hK0 : 0 ≤ K)
    (hα₀ : ∀ α ≥ α₀, 160 ≤ α ∧ 20 * (1 / (2 * η) + 3) ^ 2 ≤ α ∧
      Real.exp (-((1 / 10 : ℝ) ^ 2 / 80) * α) + Real.exp (-α ^ 2 + 1) +
        2 * (1 / (2 * η) + 3) * Real.sqrt (20 / α) * Real.exp 4 +
        40 * Real.pi * K * α ^ 2 * Real.exp (-(m / 80) * α) +
        Real.exp (9 / 2 * (1 / (2 * η) + 3)) *
          (16 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164)) ≤ 1 / 5 ∧
      2 * (40 * Real.pi * K * α ^ 2 * Real.exp (-(m / 80) * α)) +
        Real.exp (9 / 2 * (1 / (2 * η) + 3)) *
          (16 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164) +
            2 * α * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 * α / 80) +
              (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α)) +
        (1 / (2 * η) + 3) * (1 + 2 * (1 / (2 * η) + 3) * Real.sqrt (20 / α) * Real.exp 4) <
        18 / 25 * α ∧
      40 * Real.pi * K * α ^ 2 * Real.exp (-(m / 80) * α) +
        Real.exp (1 / (2 * η) + 3 - 2 * δ₀ * α) *
          (1 + 2 * (1 / (2 * η) + 3) * Real.sqrt (20 / α) * Real.exp 4) +
        Real.exp (9 / 2 * (1 / (2 * η) + 3)) *
          (16 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164)) <
        18 / 25)
    (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (hX₀ : 2 * Real.pi * Real.exp (2 * max α₀ 160) ≤ X)
    (hXc : 2 * Real.pi * Real.exp (c₀ / t) ≤ X) :
    0 < ((∫ w in Ioi (0 : ℝ), (((w - 0) / (2 * t) * gaussDensity t (w - 0) : ℝ) : ℂ) *
      xiLine X w) * starRingEnd ℂ (halfGaussTransform t (xiLine X) 0)).re ∧
    ∀ y : ℝ, y ≠ 0 → |y| ≤ 1 / 2 → riemannHeat t ((X : ℂ) + I * y) ≠ 0 := by
  have h2π : 0 < 2 * Real.pi := by positivity
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hX₀
  set α := (horizontalSlope X).re with hαdef
  have hαlog : α = Real.log (X / (2 * Real.pi)) / 2 := by rw [hαdef, horizontalSlope_re]
  have hαge : ∀ L : ℝ, 2 * Real.pi * Real.exp L ≤ X → L / 2 ≤ α := by
    intro L hL
    have h1 : Real.exp L ≤ X / (2 * Real.pi) := by rw [le_div_iff₀ h2π]; linarith
    have h2 := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at h2
    rw [hαlog]; linarith
  have hαbig : max α₀ 160 ≤ α := by have := hαge _ hX₀; linarith
  have hα160 : 160 ≤ α := (le_max_right _ _).trans hαbig
  have hαα₀ : α₀ ≤ α := (le_max_left _ _).trans hαbig
  have hα0 : 0 < α := by linarith
  have hX200 : 200 ≤ X := by
    have h1 : (1 : ℝ) + 320 ≤ Real.exp (2 * max α₀ 160) := by
      have := Real.add_one_le_exp (2 * max α₀ 160)
      have : (320 : ℝ) ≤ 2 * max α₀ 160 := by linarith [le_max_right α₀ 160]
      linarith
    have := Real.pi_gt_three
    nlinarith
  have hct : c₀ / (2 * α) ≤ t := by
    have h := hαge _ hXc
    rw [div_le_iff₀ (by positivity)]
    have : c₀ / t / 2 * t = c₀ / 2 := by field_simp
    nlinarith
  rcases le_or_gt (20 / α) t with h20 | h20
  · -- Large-product regime `t α ≥ 20`: slope positivity holds on all of `[−1/2, 1/2]`.
    have htα : 20 ≤ t * α := by rw [div_le_iff₀ hα0] at h20; linarith
    have hall : ∀ v : ℝ, |v| ≤ 1 / 2 →
        0 < ((∫ w in Ioi (0 : ℝ), (((w - v) / (2 * t) * gaussDensity t (w - v) : ℝ) : ℂ) *
          xiLine X w) * starRingEnd ℂ (halfGaussTransform t (xiLine X) v)).re := fun v hv =>
      re_slope_mul_conj_pos ht ht8 hX200 hv (by linarith) (by linarith)
        (window_fits ht8 ht hX0 (by linarith))
        ((kklError_le_uniform ht le_rfl ht8 (by linarith)).trans
          (kklErrorUniform_le_of_mul_ge ht ht8 htα))
    refine ⟨hall 0 (by simp), fun y hy0 hy => riemannHeat_ne_zero_of_re_slope_pos ht hall hy0 hy⟩
  · -- Sharp regime `c₀ ≤ 2tα < 40`: combine Regime I (`|v| ≤ δ₀`) and Regime II (`δ₀ ≤ |y| ≤ 1/2`).
    obtain ⟨-, hη₁α, hsum1, hsum2, hsum_neg⟩ := hα₀ α hαα₀
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := interior_error_bounds (c₀ := c₀) (η' := 2 * η)
      (γ := 1 / 10) (m := m) (K := K) (by positivity) (by linarith) (by norm_num) hm hK0
      (by linarith) hα160 hη₁α hct h20.le
    have h2tα : c₀ ≤ 2 * t * α := by rw [div_le_iff₀ (by positivity)] at hct; linarith
    have hW9 : 9 / 2 ≤ 2 * t * α + α ^ 2 := by
      have : (0 : ℝ) ≤ 2 * t * α := by positivity
      have : (9 : ℝ) / 2 ≤ α ^ 2 := by nlinarith only [hα160]
      linarith
    have hWX := window_fits ht8 ht hX0 (by linarith)
    set b := 9 / 2 * (1 / (2 * η) + 3)
    have heb := (Real.exp_pos b).le
    have hS1 : chernoffLowerR1 (1 / 10) t + kklR2 t α + sharpR3 (2 * η) t +
        sharpStripErr K (2 * η) m t α + Real.exp b * kklRC t α ≤ 1 / 5 := by
      have := mul_le_mul_of_nonneg_left b5 heb
      linarith
    have hS2 : 2 * sharpStripErr K (2 * η) m t α + Real.exp b * (kklRC t α + kklRB t α) +
        (1 / (2 * η) + 3) * (1 + sharpR3 (2 * η) t) < 18 / 25 * α :=
      combine_weyl_S2 b4 b5 b6 b3 heb (by positivity) hsum2
    have hS_neg : sharpStripErr K (2 * η) m t α +
        Real.exp (1 / (2 * η) + 3 - 2 * δ₀ * α) * (1 + sharpR3 (2 * η) t) +
        Real.exp b * kklRC t α < 18 / 25 := by
      have h5' := mul_le_mul_of_nonneg_left b5 heb
      have hmid : Real.exp (1 / (2 * η) + 3 - 2 * δ₀ * α) * (1 + sharpR3 (2 * η) t) ≤
          Real.exp (1 / (2 * η) + 3 - 2 * δ₀ * α) *
            (1 + 2 * (1 / (2 * η) + 3) * Real.sqrt (20 / α) * Real.exp 4) :=
        mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
      linarith
    -- Regime I: slope positivity on `[−δ₀, δ₀]`.
    have hcollar : ∀ v : ℝ, |v| ≤ δ₀ →
        0 < ((∫ w in Ioi (0 : ℝ), (((w - v) / (2 * t) * gaussDensity t (w - v) : ℝ) : ℂ) *
          xiLine X w) * starRingEnd ℂ (halfGaussTransform t (xiLine X) v)).re := fun v hvδ =>
      re_slope_mul_conj_pos_ee ht ht8 hη (by linarith) (by norm_num) hK hK0 hX200
        hvδ (by linarith) (by linarith) (by linarith) (hmc _ h2tα) hW9 hWX hS1 hS2
    -- Strict norm inequality `‖Q(−y)‖ < ‖Q(y)‖` on all of `0 < y ≤ 1/2`.
    set Q := halfGaussTransform t (xiLine X)
    have hnorm_pos : ∀ y : ℝ, 0 < y → y ≤ 1 / 2 → ‖Q (-y)‖ < ‖Q y‖ := by
      intro y hy_pos hy2
      rcases le_or_gt y δ₀ with hy_col | hy_off
      · have hQd : ∀ v ∈ Icc (-δ₀) δ₀, HasDerivAt Q
            (∫ w in Ioi (0 : ℝ), (((w - v) / (2 * t) * gaussDensity t (w - v) : ℝ) : ℂ) *
              xiLine X w) v := fun v _ =>
          hasDerivAt_halfGaussTransform ht (continuous_xiLine X)
            (integrable_exp_mul_norm_xiLine ht X) v
        exact norm_lt_norm_of_re_mul_conj_pos hQd (fun v hv => hcollar v (abs_le.mpr hv))
          hy_pos hy_col
      · exact norm_neg_lt_norm_pos_ee ht ht8 hη (by linarith) hδ₀ (by norm_num)
          (by linarith) hK hK0 hX200 hy_off.le hy2 (by linarith) (by linarith)
          (fun w hw => (hmc _ h2tα w hw).trans (sub_le_self _ (by positivity)))
          hW9 hWX hS1 hS_neg
    refine ⟨hcollar 0 (by rw [abs_zero]; exact hδ₀.le), fun y hy0 hy => ?_⟩
    rw [riemannHeat_eq_halfGaussAverage ht X y]
    apply add_conj_ne_zero_of_norm_ne
    have hy' := abs_le.mp hy
    rcases lt_or_gt_of_ne hy0 with hneg | hpos
    · have h := hnorm_pos (-y) (by linarith) (by linarith)
      rw [neg_neg] at h
      exact ne_of_gt h
    · exact ne_of_lt (hnorm_pos y hpos hy'.2)

/-- **The heat horizon at `2/3`, real and simple.**
For every `ε > 0`, there exists `X₀` such that for all `0 < t ≤ 1/8`, every zero `z` of
`riemannHeat t` with `|Re z| ≥ X₀` and `|Re z| ≥ 2π e^{(2/3 + ε)/t}` is real and simple. -/
theorem riemannHeat_zeros_real_simple_twoThirds {ε : ℝ} (hε : 0 < ε) :
    ∃ X₀ : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 / 8 → ∀ z : ℂ, riemannHeat t z = 0 → X₀ ≤ |z.re| →
      2 * Real.pi * Real.exp ((2 / 3 + ε) / t) ≤ |z.re| →
        z.im = 0 ∧ deriv (riemannHeat t) z ≠ 0 := by
  set c₀ := 2 / 3 + ε
  have hc₀ : 2 / 3 < c₀ := by dsimp only [c₀]; linarith
  obtain ⟨η, δ₀, m, hη, hη40, hδ₀, hδ₀40, hm, hsep, hmc⟩ :=
    exists_twoThirds_params hc₀
  obtain ⟨K, hKpos, hK⟩ := exists_norm_xiLine_le_strip_ee hη (by linarith)
  obtain ⟨α₀, hα₀⟩ := eventually_atTop.mp
    (eventually_interior_errors_small (η' := 2 * η) (δ₀ := δ₀) (γ := 1 / 10) (m := m) (K := K)
      (b := 9 / 2 * (1 / (2 * η) + 3)) (by positivity) hδ₀ (by norm_num) hm)
  set X₀ := 2 * Real.pi * Real.exp (2 * max α₀ 160)
  refine ⟨X₀, fun t ht ht8 z hz hX₀ hXc => ?_⟩
  have hpack : ∀ X : ℝ, X₀ ≤ X → 2 * Real.pi * Real.exp (c₀ / t) ≤ X →
      0 < ((∫ w in Ioi (0 : ℝ), (((w - 0) / (2 * t) * gaussDensity t (w - 0) : ℝ) : ℂ) *
        xiLine X w) * starRingEnd ℂ (halfGaussTransform t (xiLine X) 0)).re ∧
      ∀ y : ℝ, y ≠ 0 → |y| ≤ 1 / 2 → riemannHeat t ((X : ℂ) + I * y) ≠ 0 :=
    fun X hX1 hX2 => re_slope_zero_and_ne_zero_ee hη hη40 hδ₀ hδ₀40 hm hc₀ hsep hmc
      hK hKpos.le hα₀ ht ht8 hX1 hX2
  have him := riemannHeat_zeros_im_sq_le ht hz
  have him2 : z.im ^ 2 ≤ 1 / 4 := him.trans (max_le (by linarith) (by norm_num))
  have him' : |z.im| ≤ 1 / 2 := by
    rw [← sq_le_sq₀ (abs_nonneg _) (by norm_num), sq_abs]; linarith
  have hreal : z.im = 0 := by
    by_contra hne
    rcases le_or_gt 0 z.re with h0 | h0
    · rw [abs_of_nonneg h0] at hX₀ hXc
      apply (hpack z.re hX₀ hXc).2 z.im hne him'
      rw [← hz]; congr 1; apply Complex.ext <;> simp
    · rw [abs_of_neg h0] at hX₀ hXc
      apply (hpack (-z.re) hX₀ hXc).2 (-z.im) (by simpa using hne) (by simpa using him')
      rw [← hz, ← riemannHeat_neg ht.le]; congr 1; apply Complex.ext <;> simp
  refine ⟨hreal, ?_⟩
  have hzre : z = ((z.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [hreal]
  rcases le_or_gt 0 z.re with h0 | h0
  · rw [abs_of_nonneg h0] at hX₀ hXc
    rw [hzre]
    exact deriv_riemannHeat_ne_zero_of_re_slope_pos_zero ht (hpack z.re hX₀ hXc).1
      (by rw [← hzre]; exact hz)
  · rw [abs_of_neg h0] at hX₀ hXc
    have hz' : riemannHeat t ((-z.re : ℝ) : ℂ) = 0 := by
      rw [ofReal_neg, riemannHeat_neg ht.le, ← hzre]; exact hz
    have hsimple := deriv_riemannHeat_ne_zero_of_re_slope_pos_zero ht (hpack (-z.re) hX₀ hXc).1 hz'
    rw [ofReal_neg, deriv_riemannHeat_neg ht.le, ← hzre] at hsimple
    exact fun h => hsimple (by rw [h, neg_zero])

/-- Reality projection of `riemannHeat_zeros_real_simple_twoThirds`. -/
theorem riemannHeat_zeros_real_twoThirds {ε : ℝ} (hε : 0 < ε) :
    ∃ X₀ : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 / 8 → ∀ z : ℂ, riemannHeat t z = 0 → X₀ ≤ |z.re| →
      2 * Real.pi * Real.exp ((2 / 3 + ε) / t) ≤ |z.re| → z.im = 0 := by
  obtain ⟨X₀, hX₀⟩ := riemannHeat_zeros_real_simple_twoThirds hε
  exact ⟨X₀, fun t ht ht8 z hz h1 h2 => (hX₀ t ht ht8 z hz h1 h2).1⟩

/-! ## 6. Small-time collision localization and nonreal zero count bounds -/

/-- **Spatial localization of collision points above `2/3`.**
For every `ε > 0`, there is `X₀ ≥ 1` such that for every `t > 0` and every collision point
`z ∈ realMultipleZeros t`, `z.im = 0` and `|z.re| < max X₀ (2π e^{(2/3 + ε)/t})`. -/
theorem exists_realMultipleZeros_abs_lt_twoThirds {ε : ℝ} (hε : 0 < ε) :
    ∃ X₀ : ℝ, 1 ≤ X₀ ∧ ∀ t : ℝ, 0 < t → ∀ z ∈ realMultipleZeros t,
      z.im = 0 ∧ |z.re| < max X₀ (2 * Real.pi * Real.exp ((2 / 3 + ε) / t)) := by
  obtain ⟨X₁, hX₁⟩ := riemannHeat_zeros_real_simple_twoThirds hε
  refine ⟨max X₁ 1, le_max_right _ _, fun t ht z hz => ?_⟩
  rcases le_or_gt t (1 / 8) with ht8 | ht8
  · obtain ⟨hz0, hzim, hdz⟩ := (mem_realMultipleZeros ht ht8).mp hz
    refine ⟨hzim, ?_⟩
    by_contra hge
    push Not at hge
    have h1 : X₁ ≤ |z.re| := (le_max_left X₁ 1).trans ((le_max_left _ _).trans hge)
    have h2 : 2 * Real.pi * Real.exp ((2 / 3 + ε) / t) ≤ |z.re| :=
      (le_max_right _ _).trans hge
    exact (hX₁ t ht ht8 z hz0 h1 h2).2 hdz
  · simp only [realMultipleZeros, dif_neg (not_and.mpr fun _ => not_le.mpr ht8)] at hz
    exact absurd hz (Finset.notMem_empty _)

/-- **Sharpened unconditional small-time bound on `nonrealZeroCount t`, remaining collision mass
`∑_{s > t} collisionMass s`, and instantaneous `collisionMass t`.**
For every `ε > 0`, there exist `C₀ > 0` and `X₀ ≥ 1` such that for all `0 < t ≤ 1/8`, with
`R(t) = max X₀ (2π e^{(2/3 + ε)/t}) + 1` (lowering the exponent from `27/40`, `exists_nonrealZeroCount_and_collisionMass_le_interiorLindelof`,
to `2/3`):
1. `nonrealZeroCount t ≤ C₀ * R(t) * log(2 + 3 R(t))`,
2. `∑_{s > t} collisionMass s ≤ C₀ * R(t) * log(2 + 3 R(t))`, and
3. `collisionMass t ≤ C₀ * R(t) * log(2 + 3 R(t))`. -/
theorem exists_nonrealZeroCount_and_collisionMass_le_twoThirds {ε : ℝ} (hε : 0 < ε) :
    ∃ C₀ X₀ : ℝ, 0 < C₀ ∧ 1 ≤ X₀ ∧ ∀ (t : ℝ) (ht : 0 < t), t ≤ 1 / 8 →
      let R := max X₀ (2 * Real.pi * Real.exp ((2 / 3 + ε) / t)) + 1
      ((nonrealZeroCount t : ℕ) : ℝ) ≤ C₀ * R * Real.log (2 + 3 * R) ∧
      ((∑ s ∈ (finite_collisionTimes ht).toFinset, collisionMass s : ℕ) : ℝ) ≤
        C₀ * R * Real.log (2 + 3 * R) ∧
      ((collisionMass t : ℕ) : ℝ) ≤ C₀ * R * Real.log (2 + 3 * R) := by
  obtain ⟨C₀, hC₀, hball⟩ := exists_sum_zeroMult_riemannHeat_ball_le
  obtain ⟨X₁, hX₁⟩ := riemannHeat_zeros_real_simple_twoThirds hε
  set X₀ := max X₁ 1
  have hX₀1 : 1 ≤ X₀ := le_max_right _ _
  refine ⟨C₀, X₀, hC₀, hX₀1, fun t ht ht8 => ?_⟩
  intro R
  have hR1 : 1 ≤ R := by
    have : 1 ≤ max X₀ (2 * Real.pi * Real.exp ((2 / 3 + ε) / t)) :=
      hX₀1.trans (le_max_left _ _)
    linarith
  have hN : ((nonrealZeroCount t : ℕ) : ℝ) ≤ C₀ * R * Real.log (2 + 3 * R) := by
    rw [nonrealZeroCount_eq ht]
    refine hball t ht.le ht8 R hR1 _ fun z hz => ?_
    obtain ⟨hz0, hzim⟩ := (riemannHeat_nonreal_zeros_finite ht).mem_toFinset.mp hz
    have hre : |z.re| < max X₀ (2 * Real.pi * Real.exp ((2 / 3 + ε) / t)) := by
      by_contra hge
      push Not at hge
      have h1 : X₁ ≤ |z.re| := (le_max_left X₁ 1).trans ((le_max_left _ _).trans hge)
      have h2 : 2 * Real.pi * Real.exp ((2 / 3 + ε) / t) ≤ |z.re| :=
        (le_max_right _ _).trans hge
      exact hzim (hX₁ t ht ht8 z hz0 h1 h2).1
    have him : |z.im| ≤ 1 / 2 := abs_im_le_half_of_riemannHeat_eq_zero ht hz0
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ < R := by simp only [R]; linarith
  have hC : ((collisionMass t : ℕ) : ℝ) ≤ C₀ * R * Real.log (2 + 3 * R) := by
    have hle : ((collisionMass t : ℕ) : ℝ) ≤
        ((∑ z ∈ realMultipleZeros t, zeroMult (riemannHeat t) z : ℕ) : ℝ) := by
      exact_mod_cast collisionMass_le_sum_zeroMult t
    refine hle.trans (hball t ht.le ht8 R hR1 _ fun z hz => ?_)
    obtain ⟨hz0, hzim, hdz⟩ := (mem_realMultipleZeros ht ht8).mp hz
    have hre : |z.re| < max X₀ (2 * Real.pi * Real.exp ((2 / 3 + ε) / t)) := by
      by_contra hge
      push Not at hge
      have h1 : X₁ ≤ |z.re| := (le_max_left X₁ 1).trans ((le_max_left _ _).trans hge)
      have h2 : 2 * Real.pi * Real.exp ((2 / 3 + ε) / t) ≤ |z.re| :=
        (le_max_right _ _).trans hge
      exact (hX₁ t ht ht8 z hz0 h1 h2).2 hdz
    calc ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ < R := by rw [hzim, abs_zero]; simp only [R]; linarith
  refine ⟨hN, ?_, hC⟩
  have hN' := hN
  rwa [nonrealZeroCount_eq_sum_collisionMass ht] at hN'


end

end RHTower.DeBruijn
