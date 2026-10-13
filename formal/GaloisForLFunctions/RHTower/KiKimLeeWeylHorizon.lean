import GaloisForLFunctions.RHTower.KiKimLeeSharpSimpleZeros
import GaloisForLFunctions.RHTower.XiLineStripConvexity
import GaloisForLFunctions.RHTower.ZetaSubconvexStripBound

/-!
# The heat horizon at `3/2` from Weyl's bound

**Theorem** (`riemannHeat_zeros_real_weyl`, `riemannHeat_zeros_real_simple_weyl`). For every `ε > 0`
there is `X₀` such that for all `0 < t ≤ 1/8`, every zero `z` of the de Bruijn–Newman deformation
`H_t` with `|Re z| ≥ X₀` and `|Re z| ≥ 2π e^{(3/2 + ε)/t}` is real and simple. With the convexity
bound the same argument gives `1 + √3/2` (`riemannHeat_zeros_real_sharp`).

**Proof.** Only the strip terms of the one-sided Gaussian average change.

* Weyl's bound, interpolated across `½ ≤ Re s ≤ 1 + η` (`exists_norm_riemannZeta_le_subconvex`),
  gives the strip comparison `‖F(w)‖ ≤ K X^{ρ(½+η−w)} (X/2π)^{(w−u)/2} ‖F(u)‖` for
  `F(w) = ξ(½ + w + iX)`, with `ρ = (1/6 + η)/(½ + η)` (`exists_norm_xiLine_le_strip_weyl`).
* With `λ = 2ρ` and `c = 2tα`, the Gaussian exponent of the strip is
  `−(w−y)² + 2cλ(½+η−w) + 2c(w−y) − c²`. Completing the square in `v = w − y` bounds it by
  `−c²λ(2−λ) + 2cλ(1+η)`, which is negative once `c > 2(1+η)/(2−λ)`; as `η → 0` this tends to
  `3/2` (`gaussDensity_mul_norm_xiLine_le_weyl`, `exists_weyl_params`).
* The other error terms and the assembly are those of the convexity proof.

The window estimates of that proof are stated for `2tα ≥ 3/2`, so a stronger subconvexity exponent
alone does not lower the horizon below `3/2` in this argument.
-/

open Complex MeasureTheory Filter Topology Set

namespace RHTower.DeBruijn

noncomputable section

/-- The Weyl rate `(1/6 + η)/(1/2 + η)`: the strip exponent per unit of distance to `½ + η`. -/
def weylRate (η : ℝ) : ℝ := (1 / 6 + η) / (1 / 2 + η)

theorem weylRate_pos {η : ℝ} (hη : 0 ≤ η) : 0 < weylRate η := by
  unfold weylRate; positivity

theorem weylRate_le_half {η : ℝ} (hη : 0 ≤ η) (hη6 : η ≤ 1 / 6) : weylRate η ≤ 1 / 2 := by
  unfold weylRate; rw [div_le_iff₀ (by linarith)]; linarith

/-! ## The strip comparison from Weyl's bound -/

/-- **Strip comparison, Weyl form.** For `0 < η ≤ ½`, `X ≥ 16`, `0 ≤ w ≤ ½ + η` and `1 ≤ u ≤ X`:
`‖F(w)‖ ≤ K X^{ρ(½+η−w)} (X/2π)^{(w−u)/2} ‖F(u)‖` with `ρ = weylRate η`. -/
theorem exists_norm_xiLine_le_strip_weyl {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) :
    ∃ K : ℝ, 0 < K ∧ ∀ X w u : ℝ, 16 ≤ X → 0 ≤ w → w ≤ 1 / 2 + η → 1 ≤ u → u ≤ X →
      ‖xiLine X w‖ ≤
        K * X ^ (weylRate η * (1 / 2 + η - w)) * (X / (2 * Real.pi)) ^ ((w - u) / 2) * ‖xiLine X u‖ := by
  obtain ⟨C, hC, hconv⟩ := exists_norm_riemannZeta_le_subconvex hη hη2
  obtain ⟨c, hc, hlow⟩ := exists_norm_riemannZeta_ge_three_halves
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
  -- the polynomial factors
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
  -- the Gamma ratio
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
  -- the two `ζ` values
  have hZw_le : Zw ≤ C * X ^ (weylRate η * (1 / 2 + η - w)) := by
    have h := hconv (w + 1 / 2) X (by linarith) (by linarith) (by linarith)
    have e : (1 / 6 + η) * (1 + η - (w + 1 / 2)) / (1 / 2 + η) =
        weylRate η * (1 / 2 + η - w) := by unfold weylRate; field_simp; ring
    rw [e] at h
    simpa [hZw, hsw] using h
  have hZu_ge : c ≤ Zu := hlow su (by simp [hsu]; linarith)
  -- the powers of `π`
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
  -- assemble
  have hPu0 : 0 ≤ Pu := norm_nonneg _
  have hGu0 : 0 ≤ Gu := norm_nonneg _
  have hZw0 : 0 ≤ Zw := norm_nonneg _
  have hπu : 0 < Real.pi ^ (-((u + 1 / 2) / 2)) := Real.rpow_pos_of_pos Real.pi_pos _
  have hXp : 0 < X ^ (weylRate η * (1 / 2 + η - w)) := Real.rpow_pos_of_pos hX0 _
  have hR : 0 < (X / (2 * Real.pi)) ^ ((w - u) / 2) := Real.rpow_pos_of_pos (by positivity) _
  have hX2 : 0 < (X / 2) ^ ((w - u) / 2) := Real.rpow_pos_of_pos (by positivity) _
  have hπuw : 0 < Real.pi ^ ((u - w) / 2) := Real.rpow_pos_of_pos Real.pi_pos _
  rw [hpi]
  calc Pw * (Real.pi ^ (-((u + 1 / 2) / 2)) * Real.pi ^ ((u - w) / 2)) * Gw * Zw
      ≤ (2 * Pu) * (Real.pi ^ (-((u + 1 / 2) / 2)) * Real.pi ^ ((u - w) / 2)) *
          ((X / 2) ^ ((w - u) / 2) * Real.exp 6 * Gu) * (C * X ^ (weylRate η * (1 / 2 + η - w))) := by
        gcongr
    _ = 2 * Real.exp 6 * C * X ^ (weylRate η * (1 / 2 + η - w)) *
          ((X / 2) ^ ((w - u) / 2) * Real.pi ^ ((u - w) / 2)) *
          (Pu * Real.pi ^ (-((u + 1 / 2) / 2)) * Gu) := by ring
    _ = 2 * Real.exp 6 * C * X ^ (weylRate η * (1 / 2 + η - w)) * (X / (2 * Real.pi)) ^ ((w - u) / 2) *
          (Pu * Real.pi ^ (-((u + 1 / 2) / 2)) * Gu) := by rw [hpow]
    _ ≤ 2 * Real.exp 6 * C * X ^ (weylRate η * (1 / 2 + η - w)) * (X / (2 * Real.pi)) ^ ((w - u) / 2) *
          (Pu * Real.pi ^ (-((u + 1 / 2) / 2)) * Gu * (Zu / c)) := by
        have h1 : 1 ≤ Zu / c := by rw [le_div_iff₀ hc]; linarith
        have h0 : 0 ≤ Pu * Real.pi ^ (-((u + 1 / 2) / 2)) * Gu := by positivity
        exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_right h0 h1) (by positivity)
    _ = 2 * Real.exp 6 * C / c * X ^ (weylRate η * (1 / 2 + η - w)) *
          (X / (2 * Real.pi)) ^ ((w - u) / 2) *
          (Pu * Real.pi ^ (-((u + 1 / 2) / 2)) * Gu * Zu) := by
        field_simp

/-! ## The strip terms -/

/-- **The pointwise strip bound, Weyl form.** -/
theorem gaussDensity_mul_norm_xiLine_le_weyl {K η m t X y w : ℝ} (ht : 0 < t)
    (hK : ∀ X w u : ℝ, 16 ≤ X → 0 ≤ w → w ≤ 1 / 2 + η → 1 ≤ u → u ≤ X →
      ‖xiLine X w‖ ≤
        K * X ^ (weylRate η * (1 / 2 + η - w)) * (X / (2 * Real.pi)) ^ ((w - u) / 2) * ‖xiLine X u‖)
    (hK0 : 0 ≤ K) (hX : 16 ≤ X) (hy : |y| ≤ 1 / 2)
    (hc1 : 3 / 2 ≤ 2 * t * (horizontalSlope X).re)
    (hcX : y + 2 * t * (horizontalSlope X).re ≤ X)
    (hη0 : 0 ≤ η) (hη6 : η ≤ 1 / 6)
    (hm : m ≤ (2 * t * (horizontalSlope X).re) ^ 2 * (2 * weylRate η) * (2 - 2 * weylRate η) -
      2 * (2 * t * (horizontalSlope X).re) * (2 * weylRate η) * (1 + η))
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1 / 2 + η) :
    gaussDensity t (w - y) * ‖xiLine X w‖ ≤
      (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * K * (2 * Real.pi) ^ ((1 / 2 + η) / 2) *
        Real.exp (-(m / (4 * t))) *
        (‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
          Real.exp (-(t * (horizontalSlope X).re ^ 2))) := by
  set α := (horizontalSlope X).re with hα
  set u := y + 2 * t * α with hu
  set c := 2 * t * α with hc
  set N := ‖xiLine X u‖ with hN
  have hX0 : 0 < X := by linarith
  have hy1 := (abs_le.mp hy).1
  have hu1 : 1 ≤ u := by rw [hu]; linarith
  have hF := hK X w u hX hw0 hw1 hu1 hcX
  -- rewrite the powers of `X` through `X = 2π e^{2α}`
  have hXe : X / (2 * Real.pi) = Real.exp (2 * α) := by
    have := height_eq hX0
    rw [← hα] at this
    rw [this]; field_simp
  have hpow1 : (X / (2 * Real.pi)) ^ ((w - u) / 2) = Real.exp (α * (w - u)) := by
    rw [hXe, ← Real.exp_mul]; congr 1; ring
  have hXsplit : X = (2 * Real.pi) * (X / (2 * Real.pi)) := by field_simp
  set ρ := weylRate η with hρ
  have hρ0 : 0 < ρ := weylRate_pos hη0
  have hρ2 : ρ ≤ 1 / 2 := weylRate_le_half hη0 hη6
  have hpow2 : X ^ (ρ * (1 / 2 + η - w)) ≤
      (2 * Real.pi) ^ ((1 / 2 + η) / 2) * Real.exp (α * (2 * ρ * (1 / 2 + η - w))) := by
    rw [hXsplit, Real.mul_rpow (by positivity) (by positivity), hXe, ← Real.exp_mul]
    have e : 2 * α * (ρ * (1 / 2 + η - w)) = α * (2 * ρ * (1 / 2 + η - w)) := by ring
    rw [e]
    gcongr
    · linarith [Real.pi_gt_three]
    · nlinarith
  -- the Gaussian
  have hg : gaussDensity t (w - y) =
      (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.exp (-((w - y) ^ 2 / (4 * t))) := rfl
  -- the exponent
  have hexp : Real.exp (-((w - y) ^ 2 / (4 * t))) * Real.exp (α * (2 * ρ * (1 / 2 + η - w))) *
      Real.exp (α * (w - u)) ≤ Real.exp (-(m / (4 * t))) * Real.exp (-(t * α ^ 2)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hαt : α = c / (2 * t) := by rw [hc]; field_simp
    have huc : u = y + c := by rw [hu, hc]
    have h4t : 0 < 4 * t := by positivity
    have hL : -((w - y) ^ 2 / (4 * t)) + α * (2 * ρ * (1 / 2 + η - w)) + α * (w - u) =
        (-(w - y) ^ 2 + 2 * c * (2 * ρ) * (1 / 2 + η - w) + 2 * c * (w - y) - c ^ 2 - c ^ 2) /
          (4 * t) := by
      rw [huc, hαt]; field_simp; ring
    have hR : -(m / (4 * t)) + -(t * α ^ 2) = (-m - c ^ 2) / (4 * t) := by
      rw [hαt]; field_simp; ring
    rw [hL, hR]
    apply div_le_div_of_nonneg_right _ h4t.le
    have hc0 : 0 ≤ c := by linarith
    have hy1' := (abs_le.mp hy).1
    have hcl : 0 ≤ c * (2 * ρ) * (y + 1 / 2) := by
      have := mul_nonneg (mul_nonneg hc0 (by linarith : (0 : ℝ) ≤ 2 * ρ)) (by linarith : (0 : ℝ) ≤ y + 1 / 2)
      exact this
    nlinarith [sq_nonneg (w - y - c * (1 - 2 * ρ))]
  have hG0 : 0 ≤ (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) := by positivity
  have hN0 : 0 ≤ N := norm_nonneg _
  calc gaussDensity t (w - y) * ‖xiLine X w‖
      ≤ ((4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * Real.exp (-((w - y) ^ 2 / (4 * t)))) *
          (K * ((2 * Real.pi) ^ ((1 / 2 + η) / 2) * Real.exp (α * (2 * ρ * (1 / 2 + η - w)))) *
            Real.exp (α * (w - u)) * N) := by
        rw [hg]
        refine mul_le_mul_of_nonneg_left (hF.trans ?_) (by positivity)
        rw [hpow1]
        gcongr
    _ = (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * K * (2 * Real.pi) ^ ((1 / 2 + η) / 2) *
          (Real.exp (-((w - y) ^ 2 / (4 * t))) * Real.exp (α * (2 * ρ * (1 / 2 + η - w))) *
            Real.exp (α * (w - u))) * N := by ring
    _ ≤ (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * K * (2 * Real.pi) ^ ((1 / 2 + η) / 2) *
          (Real.exp (-(m / (4 * t))) * Real.exp (-(t * α ^ 2))) * N := by gcongr
    _ = _ := by ring

/-- **The three strip terms, Weyl form.** -/
theorem weyl_strip_terms_le {K η m t X y : ℝ} (ht : 0 < t) (hη : 0 < η)
    (hK : ∀ X w u : ℝ, 16 ≤ X → 0 ≤ w → w ≤ 1 / 2 + η → 1 ≤ u → u ≤ X →
      ‖xiLine X w‖ ≤
        K * X ^ (weylRate η * (1 / 2 + η - w)) * (X / (2 * Real.pi)) ^ ((w - u) / 2) * ‖xiLine X u‖)
    (hK0 : 0 ≤ K) (hX : 16 ≤ X) (hy : |y| ≤ 1 / 2) (hα : 0 ≤ (horizontalSlope X).re)
    (hc1 : 3 / 2 ≤ 2 * t * (horizontalSlope X).re)
    (hcX : y + 2 * t * (horizontalSlope X).re ≤ X)
    (hη6 : η ≤ 1 / 6)
    (hm : m ≤ (2 * t * (horizontalSlope X).re) ^ 2 * (2 * weylRate η) * (2 - 2 * weylRate η) -
      2 * (2 * t * (horizontalSlope X).re) * (2 * weylRate η) * (1 + η)) :
    (∫ w in Ioc (0 : ℝ) (1 / 2 + η), (|(w - y) / (2 * t)| + ‖horizontalSlope X‖) *
        gaussDensity t (w - y) * ‖xiLine X w‖) ≤
      ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
        Real.exp (-(t * (horizontalSlope X).re ^ 2)) *
        sharpStripErr K η m t (horizontalSlope X).re ∧
    (∫ w in Ioc (0 : ℝ) (1 / 2 + η), gaussDensity t (w - y) * ‖xiLine X w‖) ≤
      ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
        Real.exp (-(t * (horizontalSlope X).re ^ 2)) *
        sharpStripErr K η m t (horizontalSlope X).re ∧
    gaussDensity t (1 / 2 + η - y) * ‖xiLine X (1 / 2 + η)‖ ≤
      ‖xiLine X (y + 2 * t * (horizontalSlope X).re)‖ *
        Real.exp (-(t * (horizontalSlope X).re ^ 2)) *
        sharpStripErr K η m t (horizontalSlope X).re := by
  set α := (horizontalSlope X).re with hαdef
  set P := ‖xiLine X (y + 2 * t * α)‖ * Real.exp (-(t * α ^ 2)) with hP
  set Q := (4 * Real.pi * t) ^ (-(1 / 2 : ℝ)) * K * (2 * Real.pi) ^ ((1 / 2 + η) / 2) *
    Real.exp (-(m / (4 * t))) with hQ
  set A := (1 + η) / (2 * t) + α + 1 with hA
  have hQ0 : 0 ≤ Q := by positivity
  have hP0 : 0 ≤ P := by positivity
  have hA1 : 1 ≤ A := by
    have : 0 ≤ (1 + η) / (2 * t) := by positivity
    linarith
  have hpt : ∀ w ∈ Icc (0 : ℝ) (1 / 2 + η), gaussDensity t (w - y) * ‖xiLine X w‖ ≤ Q * P :=
    fun w hw => gaussDensity_mul_norm_xiLine_le_weyl ht hK hK0 hX hy hc1 hcX hη.le hη6 hm hw.1 hw.2
  have hslope : ∀ w ∈ Icc (0 : ℝ) (1 / 2 + η),
      (|(w - y) / (2 * t)| + ‖horizontalSlope X‖) * gaussDensity t (w - y) * ‖xiLine X w‖ ≤
        A * (Q * P) := by
    intro w hw
    have hwt : |(w - y) / (2 * t)| ≤ (1 + η) / (2 * t) := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 * t)]
      gcongr
      rw [abs_le] at hy ⊢
      constructor <;> linarith [hw.1, hw.2]
    have ha := norm_horizontalSlope_le hα
    have hAB : |(w - y) / (2 * t)| + ‖horizontalSlope X‖ ≤ A := by rw [hA]; linarith
    rw [mul_assoc]
    have hGF : 0 ≤ gaussDensity t (w - y) * ‖xiLine X w‖ :=
      mul_nonneg (gaussDensity_pos ht _).le (norm_nonneg _)
    exact mul_le_mul hAB (hpt w hw) hGF (by linarith)
  have hvol : volume.real (Ioc (0 : ℝ) (1 / 2 + η)) = 1 / 2 + η := by
    rw [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    ring
  have hint_bound : ∀ (f : ℝ → ℝ) (B : ℝ), (∀ w, 0 ≤ f w) →
      (∀ w ∈ Icc (0 : ℝ) (1 / 2 + η), f w ≤ B) →
      ∫ w in Ioc (0 : ℝ) (1 / 2 + η), f w ≤ (1 / 2 + η) * B := by
    intro f B hf0 hfB
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := f) (C := B)
      measure_Ioc_lt_top (fun w hw => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 w)]; exact hfB w (Ioc_subset_Icc_self hw))
    rw [hvol] at h
    have := le_abs_self (∫ w in Ioc (0 : ℝ) (1 / 2 + η), f w)
    rw [← Real.norm_eq_abs] at this
    linarith
  have herr : sharpStripErr K η m t α = (1 + η) * A * Q := by
    rw [sharpStripErr, hA, hQ]
  have hQP : 0 ≤ Q * P := mul_nonneg hQ0 hP0
  refine ⟨?_, ?_, ?_⟩
  · refine (hint_bound _ _ (fun w => mul_nonneg (mul_nonneg (by positivity)
      (gaussDensity_pos ht _).le) (norm_nonneg _)) hslope).trans ?_
    rw [herr]
    have hAQP : 0 ≤ A * (Q * P) := mul_nonneg (by linarith) hQP
    have h2 : (1 / 2 + η) * (A * (Q * P)) ≤ (1 + η) * (A * (Q * P)) :=
      mul_le_mul_of_nonneg_right (by linarith) hAQP
    calc (1 / 2 + η) * (A * (Q * P)) ≤ (1 + η) * (A * (Q * P)) := h2
      _ = P * ((1 + η) * A * Q) := by ring
  · refine (hint_bound _ _ (fun w => mul_nonneg (gaussDensity_pos ht _).le (norm_nonneg _))
      hpt).trans ?_
    rw [herr]
    have h1 : Q * P ≤ A * (Q * P) := le_mul_of_one_le_left hQP hA1
    nlinarith
  · have h0 := hpt (1 / 2 + η) ⟨by linarith, le_rfl⟩
    have h1 : Q * P ≤ A * (Q * P) := le_mul_of_one_le_left hQP hA1
    have h2 : A * (Q * P) ≤ (1 + η) * (A * (Q * P)) := le_mul_of_one_le_left (by positivity) (by linarith)
    rw [herr]
    calc gaussDensity t (1 / 2 + η - y) * ‖xiLine X (1 / 2 + η)‖ ≤ Q * P := h0
      _ ≤ P * ((1 + η) * A * Q) := by nlinarith

/-! ## Slope positivity and the horizon -/

/-- **Positivity of `Re(Q' Q̄)` at one height, Weyl strip.** -/
theorem re_slope_mul_conj_pos_weyl {K η m t X y : ℝ} (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (hη : 0 < η)
    (hK : ∀ X w u : ℝ, 16 ≤ X → 0 ≤ w → w ≤ 1 / 2 + η → 1 ≤ u → u ≤ X →
      ‖xiLine X w‖ ≤
        K * X ^ (weylRate η * (1 / 2 + η - w)) * (X / (2 * Real.pi)) ^ ((w - u) / 2) * ‖xiLine X u‖)
    (hK0 : 0 ≤ K) (hX : 200 ≤ X) (hy : |y| ≤ 1 / 2) (hα1 : 1 ≤ (horizontalSlope X).re)
    (_hc1 : 1 + η ≤ 2 * t * (horizontalSlope X).re)
    (hc32 : 3 / 2 ≤ 2 * t * (horizontalSlope X).re)
    (hη6 : η ≤ 1 / 6)
    (hm : m ≤ (2 * t * (horizontalSlope X).re) ^ 2 * (2 * weylRate η) * (2 - 2 * weylRate η) -
      2 * (2 * t * (horizontalSlope X).re) * (2 * weylRate η) * (1 + η))
    (hW9 : 9 / 2 ≤ 2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2)
    (hWX : 2 * t * (horizontalSlope X).re + (horizontalSlope X).re ^ 2 ≤ X / 32 - 1 / 2)
    (hS1 : sharpR1 η t (horizontalSlope X).re + kklR2 t (horizontalSlope X).re + sharpR3 η t +
      sharpStripErr K η m t (horizontalSlope X).re +
      Real.exp (9 / 2 * (1 / η + 3)) * kklRC t (horizontalSlope X).re ≤ 1 / 5)
    (hS2 : 2 * sharpStripErr K η m t (horizontalSlope X).re +
      Real.exp (9 / 2 * (1 / η + 3)) *
        (kklRC t (horizontalSlope X).re + kklRB t (horizontalSlope X).re) +
      (1 / η + 3) * (1 + sharpR3 η t) < 18 / 25 * (horizontalSlope X).re) :
    0 < ((∫ w in Ioi (0 : ℝ), (((w - y) / (2 * t) * gaussDensity t (w - y) : ℝ) : ℂ) * xiLine X w) *
      starRingEnd ℂ (halfGaussTransform t (xiLine X) y)).re := by
  have hα0 : 0 ≤ (horizontalSlope X).re := by linarith
  set a := horizontalSlope X with hadef
  set α := a.re with hαdef
  set u := y + 2 * t * α with hudef
  set N := ‖xiLine X u‖ with hN
  set W := 2 * t * α + α ^ 2 with hWdef
  set b := 9 / 2 * (1 / η + 3) with hbdef
  have hy1 := (abs_le.mp hy).1
  have hy2 := (abs_le.mp hy).2
  have hWu : u ≤ W := by rw [hudef, hWdef]; nlinarith
  have hu : u ∈ Icc (1 / 2 + η) (X / 32 - 1 / 2) :=
    ⟨by rw [hudef]; linarith, hWu.trans hWX⟩
  have hw1W : 1 / 2 + η ≤ W := hu.1.trans hWu
  have hN0 : 0 ≤ N := norm_nonneg _
  have hNpos : 0 < N := by
    rw [hN, norm_pos_iff]
    unfold xiLine
    rw [xiLine_point]
    exact xi_ne_zero_of_one_lt_re (by simp; linarith [hu.1])
  set P := N * Real.exp (-(t * α ^ 2)) with hP
  have hP0 : 0 < P := by positivity
  -- the window hypotheses
  have hmodel : ∀ w ∈ Icc (1 / 2 + η) W, ‖xiLine X w - xiLine X u *
      Complex.exp (((w - u : ℝ) : ℂ) * a)‖ ≤
        ‖xiLine X u‖ * Real.exp ((w - u) * a.re) * (Real.exp ((1 / η + 3) * |w - u|) - 1) :=
    fun w hw => norm_xiLine_sub_model_le_near hX hη hu ⟨hw.1, hw.2.trans hWX⟩
  have hderiv : ∀ w ∈ Icc (1 / 2 + η) W, ‖xiLineDeriv X w - a * xiLine X w‖ ≤
      (1 / η + 3) * ‖xiLine X w‖ :=
    fun w hw => norm_xiLineDeriv_sub_le_near hX hη hw.1 (hw.2.trans hWX)
  have hQ := norm_halfGaussTransform_sub_main_le ht (continuous_xiLine X)
    (integrable_exp_mul_norm_xiLine ht X) (y := y) (by positivity) (by linarith) hw1W hmodel
  have hD := norm_slope_sub_mul_le ht (hasDerivAt_xiLine X) (continuous_xiLineDeriv X)
    (integrable_exp_mul_norm_xiLine ht X) (y := y) (by linarith) hw1W hderiv
  -- the pieces
  have hT1 := sharp_lowerTail_le (η := η) ht hy hα0 hN0
  have hT2 := upperTail_le ht hy hN0 (α := α)
  have hT3 := sharp_modelError_le (α := α) (y := y) ht hη hN0
  have hM := sharp_windowMass_le ht hη hX hu hWX
  have hcX : u ≤ X := by
    have := hu.2; linarith
  obtain ⟨hSA, hOA, hB1⟩ := weyl_strip_terms_le ht hη hK hK0 (by linarith) hy hα0 hc32 hcX hη6 hm
  have hFWb : ‖xiLine X W‖ ≤ (Real.exp b * N) * Real.exp ((W - u) * (α + 1 / 8)) :=
    norm_xiLine_far_end_le hX hη hu hW9 hWu hWX
  obtain ⟨hSC, hOC, hB2⟩ := far_terms_le_of_bound (b := b) ht ht8 hX hy hα1 hW9 hFWb
  have hph := gaussPhase_ge ht8 ht
  have hR2 := kklR2_nonneg t α
  have hRC := kklRC_nonneg ht hα0 (α := α)
  have hRB := kklRB_nonneg ht (α := α)
  have hR1 : 0 ≤ sharpR1 η t α := (Real.exp_pos _).le
  have hR3 : 0 ≤ sharpR3 η t := by unfold sharpR3; positivity
  have hRS : 0 ≤ sharpStripErr K η m t α := by unfold sharpStripErr; positivity
  have heb : 0 ≤ Real.exp b := (Real.exp_pos _).le
  -- the main term
  have hmain := norm_main_eq (t := t) (X := X) (y := y) (xiLine X u)
  rw [← hadef, ← hαdef, ← hudef] at hmain
  have hmain' : ‖xiLine X u * Complex.exp (-((u : ℂ) * a)) *
      Complex.exp (y * a + t * a ^ 2)‖ = P * Real.exp (-(t * (Real.pi / 4) ^ 2)) := by
    rw [hmain, hP, hN]
  set S₁ := sharpR1 η t α + kklR2 t α + sharpR3 η t + sharpStripErr K η m t α +
    Real.exp b * kklRC t α with hS₁
  set S₂ := 2 * sharpStripErr K η m t α + Real.exp b * (kklRC t α + kklRB t α) +
    (1 / η + 3) * (1 + sharpR3 η t) with hS₂
  refine re_mul_conj_pos_of_estimates (Main := xiLine X u * Complex.exp (-((u : ℂ) * a)) *
      Complex.exp (y * a + t * a ^ 2)) (E₁ := P * S₁) (E₂ := P * S₂) hα0 ?_ ?_ ?_ ?_
  · refine hQ.trans ?_
    have e : ‖xiLine X u‖ * Real.exp (-(u * a.re)) *
        ((∫ w in Iic (1 / 2 + η : ℝ), gaussDensity t (w - y) * Real.exp (w * a.re)) +
          (∫ w in Ioi W, gaussDensity t (w - y) * Real.exp (w * a.re)) +
          ∫ w, gaussDensity t (w - y) * Real.exp (w * a.re) *
            (Real.exp ((1 / η + 3) * |w - u|) - 1)) =
        N * Real.exp (-(u * α)) * (∫ w in Iic (1 / 2 + η : ℝ),
            gaussDensity t (w - y) * Real.exp (w * α)) +
        N * Real.exp (-(u * α)) * (∫ w in Ioi W, gaussDensity t (w - y) * Real.exp (w * α)) +
        N * Real.exp (-(u * α)) *
          ∫ w, gaussDensity t (w - y) * Real.exp (w * α) *
            (Real.exp ((1 / η + 3) * |w - u|) - 1) := by
      ring
    rw [e]
    have hOC' : ∫ w in Ioi W, gaussDensity t (w - y) * ‖xiLine X w‖ ≤
        P * (Real.exp b * kklRC t α) := by
      refine hOC.trans (le_of_eq ?_); rw [hP]; ring
    have hT1' := hT1
    have hT3' := hT3
    rw [← hudef] at hT1' hT3'
    have hsum : P * sharpR1 η t α + P * kklR2 t α + P * sharpR3 η t +
        P * sharpStripErr K η m t α + P * (Real.exp b * kklRC t α) = P * S₁ := by
      rw [hS₁]; ring
    linarith
  · refine hD.trans ?_
    have hSC' : ∫ w in Ioi W, (|(w - y) / (2 * t)| + ‖a‖) * gaussDensity t (w - y) *
        ‖xiLine X w‖ ≤ P * (Real.exp b * kklRC t α) := by
      refine hSC.trans (le_of_eq ?_); rw [hP]; ring
    have hB2' : gaussDensity t (W - y) * ‖xiLine X W‖ ≤ P * (Real.exp b * kklRB t α) := by
      refine hB2.trans (le_of_eq ?_); rw [hP]; ring
    have hM' : (1 / η + 3) * ∫ w in Ioc (1 / 2 + η) W, gaussDensity t (w - y) * ‖xiLine X w‖ ≤
        (1 / η + 3) * (P * (1 + sharpR3 η t)) := by
      gcongr
    have hsum : P * sharpStripErr K η m t α + P * (Real.exp b * kklRC t α) +
        P * sharpStripErr K η m t α + P * (Real.exp b * kklRB t α) +
        (1 / η + 3) * (P * (1 + sharpR3 η t)) = P * S₂ := by
      rw [hS₂]; ring
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

/-- The second error sum from its bounds (pure arithmetic). -/
theorem combine_weyl_S2 {S RC RB R3 F3 F4 F5 F6 B η₁ α : ℝ} (hA : S ≤ F4)
    (h5 : RC ≤ F5) (h6 : RB ≤ F6) (h3 : R3 ≤ F3) (hB : 0 ≤ B) (hη : 0 ≤ η₁)
    (hsum : 2 * F4 + B * (F5 + F6) + η₁ * (1 + F3) < 18 / 25 * α) :
    2 * S + B * (RC + RB) + η₁ * (1 + R3) < 18 / 25 * α := by
  have h1 : B * (RC + RB) ≤ B * (F5 + F6) := mul_le_mul_of_nonneg_left (by linarith) hB
  have h2 : η₁ * (1 + R3) ≤ η₁ * (1 + F3) := mul_le_mul_of_nonneg_left (by linarith) hη
  linarith

/-- **Weyl large-height slope positivity.** With the parameters of `exists_weyl_params`, for `X`
past an absolute height and `X ≥ 2π e^{c₀/t}`, the window slope pairing is positive at every
`|v| ≤ ½`. -/
theorem re_slope_pos_weyl_window {c₀ η m K α₀ t X : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4)
    (hη6 : η ≤ 1 / 6) (hm : 0 < m)
    (hmc : ∀ c : ℝ, c₀ ≤ c → m ≤ c ^ 2 * (2 * weylRate η) * (2 - 2 * weylRate η) -
      2 * c * (2 * weylRate η) * (1 + η))
    (hc₀ : 3 / 2 ≤ c₀)
    (hK : ∀ X w u : ℝ, 16 ≤ X → 0 ≤ w → w ≤ 1 / 2 + η → 1 ≤ u → u ≤ X →
      ‖xiLine X w‖ ≤
        K * X ^ (weylRate η * (1 / 2 + η - w)) * (X / (2 * Real.pi)) ^ ((w - u) / 2) * ‖xiLine X u‖)
    (hK0 : 0 ≤ K)
    (hα₀ : ∀ α ≥ α₀, 160 ≤ α ∧ 20 * (1 / η + 3) ^ 2 ≤ α ∧
      Real.exp (-(α / 2) * (3 / 4 * c₀ - 1 - η)) + Real.exp (-α ^ 2 + 1) +
        2 * (1 / η + 3) * Real.sqrt (20 / α) * Real.exp 4 +
        24 * Real.pi * K * α ^ 2 * Real.exp (-(m / 80) * α) +
        Real.exp (9 / 2 * (1 / η + 3)) *
          (12 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164)) ≤ 1 / 5 ∧
      2 * (24 * Real.pi * K * α ^ 2 * Real.exp (-(m / 80) * α)) +
        Real.exp (9 / 2 * (1 / η + 3)) *
          (12 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164) +
            2 * α * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 * α / 80) +
              (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α)) +
        (1 / η + 3) * (1 + 2 * (1 / η + 3) * Real.sqrt (20 / α) * Real.exp 4) <
        18 / 25 * α)
    (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (hX₀ : 2 * Real.pi * Real.exp (2 * max α₀ 160) ≤ X)
    (hXc : 2 * Real.pi * Real.exp (c₀ / t) ≤ X) :
    ∀ v : ℝ, |v| ≤ 1 / 2 →
      0 < ((∫ w in Ioi (0 : ℝ), (((w - v) / (2 * t) * gaussDensity t (w - v) : ℝ) : ℂ) *
        xiLine X w) * starRingEnd ℂ (halfGaussTransform t (xiLine X) v)).re := by
  intro v hv
  have h2π : 0 < 2 * Real.pi := by positivity
  have hX0 : 0 < X := lt_of_lt_of_le (by positivity) hX₀
  set α := (horizontalSlope X).re with hαdef
  have hαlog : α = Real.log (X / (2 * Real.pi)) / 2 := by rw [hαdef, horizontalSlope_re]
  -- `α` from the two height conditions
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
  have hct : c₀ / (2 * α) ≤ t := by
    have h := hαge _ hXc
    rw [div_le_iff₀ (by positivity)]
    have : c₀ / t / 2 * t = c₀ / 2 := by field_simp
    nlinarith
  rcases le_or_gt (20 / α) t with h20 | h20
  · -- the corpus regime `t log(X/2π) ≥ 40`
    have htα : 20 ≤ t * α := by
      rw [div_le_iff₀ hα0] at h20; linarith
    have hX200 : 200 ≤ X := by
      have h1 : (1 : ℝ) + 320 ≤ Real.exp (2 * max α₀ 160) := by
        have := Real.add_one_le_exp (2 * max α₀ 160)
        have : (320 : ℝ) ≤ 2 * max α₀ 160 := by linarith [le_max_right α₀ 160]
        linarith
      have := Real.pi_gt_three
      nlinarith
    refine re_slope_mul_conj_pos ht ht8 hX200 hv (by linarith) ?_
      (window_fits ht8 ht hX0 (by linarith))
      ((kklError_le_uniform ht le_rfl ht8 (by linarith)).trans
        (kklErrorUniform_le_of_mul_ge ht ht8 htα))
    linarith
  · -- the sharp regime `c₀ ≤ t log(X/2π) < 40`
    obtain ⟨-, hη₁α, hsum1, hsum2⟩ := hα₀ α hαα₀
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := sharp_error_bounds (c₀ := c₀) (K := K) hη hη4 hm hK0 hc₀
      hα160 hη₁α hct h20.le
    have hX200 : 200 ≤ X := by
      have h1 : (1 : ℝ) + 320 ≤ Real.exp (2 * max α₀ 160) := by
        have := Real.add_one_le_exp (2 * max α₀ 160)
        have : (320 : ℝ) ≤ 2 * max α₀ 160 := by linarith [le_max_right α₀ 160]
        linarith
      have := Real.pi_gt_three
      nlinarith
    have h2tα : c₀ ≤ 2 * t * α := by
      rw [div_le_iff₀ (by positivity)] at hct; linarith
    have heb := Real.exp_pos (9 / 2 * (1 / η + 3))
    refine re_slope_mul_conj_pos_weyl ht ht8 hη hK hK0 hX200 hv (by linarith) (by linarith)
      (by linarith) hη6 (hmc _ h2tα)
      (by
        have h1 : (0 : ℝ) ≤ 2 * t * α := by positivity
        have h2 : (9 : ℝ) / 2 ≤ α ^ 2 := by nlinarith only [hα160]
        linarith only [h1, h2])
      (window_fits ht8 ht hX0 (by linarith)) ?_ ?_
    · have := mul_le_mul_of_nonneg_left b5 heb.le
      linarith
    · exact combine_weyl_S2 b4 b5 b6 b3 heb.le (by positivity) hsum2

/-- **Weyl large-height nonvanishing.** Under the hypotheses of `re_slope_pos_weyl_window`,
`H_t(X + iy) ≠ 0` for `0 < |y| ≤ ½`. -/
theorem riemannHeat_ne_zero_weyl {c₀ η m K α₀ t X : ℝ} (hη : 0 < η) (hη4 : η ≤ 1 / 4)
    (hη6 : η ≤ 1 / 6) (hm : 0 < m)
    (hmc : ∀ c : ℝ, c₀ ≤ c → m ≤ c ^ 2 * (2 * weylRate η) * (2 - 2 * weylRate η) -
      2 * c * (2 * weylRate η) * (1 + η))
    (hc₀ : 3 / 2 ≤ c₀)
    (hK : ∀ X w u : ℝ, 16 ≤ X → 0 ≤ w → w ≤ 1 / 2 + η → 1 ≤ u → u ≤ X →
      ‖xiLine X w‖ ≤
        K * X ^ (weylRate η * (1 / 2 + η - w)) * (X / (2 * Real.pi)) ^ ((w - u) / 2) * ‖xiLine X u‖)
    (hK0 : 0 ≤ K)
    (hα₀ : ∀ α ≥ α₀, 160 ≤ α ∧ 20 * (1 / η + 3) ^ 2 ≤ α ∧
      Real.exp (-(α / 2) * (3 / 4 * c₀ - 1 - η)) + Real.exp (-α ^ 2 + 1) +
        2 * (1 / η + 3) * Real.sqrt (20 / α) * Real.exp 4 +
        24 * Real.pi * K * α ^ 2 * Real.exp (-(m / 80) * α) +
        Real.exp (9 / 2 * (1 / η + 3)) *
          (12 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164)) ≤ 1 / 5 ∧
      2 * (24 * Real.pi * K * α ^ 2 * Real.exp (-(m / 80) * α)) +
        Real.exp (9 / 2 * (1 / η + 3)) *
          (12 * Real.exp 1 * α * Real.exp (-(15 / 8) * α ^ 2 + 20 * α + 164) +
            2 * α * Real.exp (-((α ^ 2 - 1 / 2) ^ 2 * α / 80) +
              (α ^ 2 + 1 / 2) * (α + 1 / 8) + 20 * α)) +
        (1 / η + 3) * (1 + 2 * (1 / η + 3) * Real.sqrt (20 / α) * Real.exp 4) <
        18 / 25 * α)
    (ht : 0 < t) (ht8 : t ≤ 1 / 8)
    (hX₀ : 2 * Real.pi * Real.exp (2 * max α₀ 160) ≤ X)
    (hXc : 2 * Real.pi * Real.exp (c₀ / t) ≤ X) {y : ℝ} (hy0 : y ≠ 0) (hy : |y| ≤ 1 / 2) :
    riemannHeat t ((X : ℂ) + I * y) ≠ 0 :=
  riemannHeat_ne_zero_of_re_slope_pos ht
    (re_slope_pos_weyl_window hη hη4 hη6 hm hmc hc₀ hK hK0 hα₀ ht ht8 hX₀ hXc) hy0 hy

/-- **Parameters for the Weyl horizon.** For `c₀ > 3/2` there are `η` and `m > 0` such that
`m ≤ c² λ(2 − λ) − 2cλ(1 + η)` for all `c ≥ c₀`, where `λ = 2 weylRate η`. -/
theorem exists_weyl_params {c₀ : ℝ} (hc₀ : 3 / 2 < c₀) :
    ∃ η m : ℝ, 0 < η ∧ η ≤ 1 / 4 ∧ η ≤ 1 / 6 ∧ 0 < m ∧
      (∀ c : ℝ, c₀ ≤ c → m ≤ c ^ 2 * (2 * weylRate η) * (2 - 2 * weylRate η) -
        2 * c * (2 * weylRate η) * (1 + η)) ∧
      3 / 2 ≤ c₀ ∧ 0 < 3 / 4 * c₀ - 1 - η := by
  set d := c₀ - 3 / 2 with hd
  have hd0 : 0 < d := by linarith
  set η := min (1 / 6) (d / (12 * c₀ + 6)) with hηdef
  have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
  have hη6 : η ≤ 1 / 6 := min_le_left _ _
  have hηd : η ≤ d / (12 * c₀ + 6) := min_le_right _ _
  set ρ := weylRate η with hρ
  have hρ0 : 0 < ρ := weylRate_pos hη0.le
  have hρ2 : ρ ≤ 1 / 2 := weylRate_le_half hη0.le hη6
  -- `2ρ ≤ 2/3 + 4η`
  have hρle : 2 * ρ ≤ 2 / 3 + 4 * η := by
    have h : ρ ≤ (1 / 6 + η) / (1 / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    have e : (1 / 6 + η) / (1 / 2) = 1 / 3 + 2 * η := by ring
    linarith
  -- the margin `(2 − 2ρ)c₀ − 2(1 + η) ≥ 2d/3`
  have hmarg : 2 * d / 3 ≤ (2 - 2 * ρ) * c₀ - 2 * (1 + η) := by
    have h1 : η * (12 * c₀ + 6) ≤ d := by
      rw [le_div_iff₀ (by positivity)] at hηd; linarith
    nlinarith
  refine ⟨η, c₀ * (2 * ρ) * (2 * d / 3), hη0, by linarith, hη6, by positivity,
    fun c hc => ?_, by linarith, ?_⟩
  swap
  · have : d / (12 * c₀ + 6) ≤ d := div_le_self hd0.le (by linarith)
    linarith
  have hc0 : 0 < c₀ := by linarith
  have h2ρ : 0 ≤ 2 - 2 * ρ := by linarith
  have hmc : 2 * d / 3 ≤ (2 - 2 * ρ) * c - 2 * (1 + η) := by
    nlinarith [mul_nonneg h2ρ (sub_nonneg.mpr hc)]
  have e : c ^ 2 * (2 * ρ) * (2 - 2 * ρ) - 2 * c * (2 * ρ) * (1 + η) =
      c * (2 * ρ) * ((2 - 2 * ρ) * c - 2 * (1 + η)) := by ring
  rw [e]
  have h1 : c₀ * (2 * ρ) ≤ c * (2 * ρ) := by nlinarith
  have h2 : 0 ≤ 2 * d / 3 := by positivity
  calc c₀ * (2 * ρ) * (2 * d / 3) ≤ c * (2 * ρ) * (2 * d / 3) := by nlinarith
    _ ≤ c * (2 * ρ) * ((2 - 2 * ρ) * c - 2 * (1 + η)) := by
        apply mul_le_mul_of_nonneg_left hmc; nlinarith

/-- **The heat horizon at `3/2`.** For every `ε > 0` there is `X₀` such that for all `0 < t ≤ 1/8`,
every zero `z` of `H_t` with `|Re z| ≥ X₀` and `|Re z| ≥ 2π e^{(3/2 + ε)/t}` is real. -/
theorem riemannHeat_zeros_real_weyl {ε : ℝ} (hε : 0 < ε) :
    ∃ X₀ : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 / 8 → ∀ z : ℂ, riemannHeat t z = 0 → X₀ ≤ |z.re| →
      2 * Real.pi * Real.exp ((3 / 2 + ε) / t) ≤ |z.re| → z.im = 0 := by
  set c₀ := 3 / 2 + ε with hc₀def
  obtain ⟨η, m, hη, hη4, hη6, hm, hmc, hc₀, hδ⟩ := exists_weyl_params (c₀ := c₀) (by linarith)
  obtain ⟨K, hKpos, hK⟩ := exists_norm_xiLine_le_strip_weyl hη (by linarith)
  obtain ⟨α₀, hα₀⟩ := eventually_atTop.mp
    (eventually_sharp_errors_small (c₀ := c₀) (K := K) (b := 9 / 2 * (1 / η + 3)) hη hm hδ)
  refine ⟨2 * Real.pi * Real.exp (2 * max α₀ 160), fun t ht ht8 z hz hX₀ hXc => ?_⟩
  have hnz : ∀ {X y : ℝ}, 2 * Real.pi * Real.exp (2 * max α₀ 160) ≤ X →
      2 * Real.pi * Real.exp (c₀ / t) ≤ X → y ≠ 0 → |y| ≤ 1 / 2 →
      riemannHeat t ((X : ℂ) + I * y) ≠ 0 := fun hX hXc' hy0 hy =>
    riemannHeat_ne_zero_weyl hη hη4 hη6 hm hmc hc₀ hK hKpos.le hα₀ ht ht8 hX hXc' hy0 hy
  have him := riemannHeat_zeros_im_sq_le ht hz
  have him2 : z.im ^ 2 ≤ 1 / 4 := him.trans (max_le (by linarith) (by norm_num))
  have him' : |z.im| ≤ 1 / 2 := by
    rw [← sq_le_sq₀ (abs_nonneg _) (by norm_num), sq_abs]; linarith
  by_contra hne
  rcases le_or_gt 0 z.re with h0 | h0
  · rw [abs_of_nonneg h0] at hX₀ hXc
    apply hnz hX₀ hXc hne him'
    rw [← hz]
    congr 1
    apply Complex.ext <;> simp
  · rw [abs_of_neg h0] at hX₀ hXc
    apply hnz (X := (-z).re) (by simpa using hX₀) (by simpa using hXc)
      (y := (-z).im) (by simpa using hne) (by simpa using him')
    rw [← hz, ← riemannHeat_neg ht.le]
    congr 1
    apply Complex.ext <;> simp

/-- **The heat horizon at `3/2`, real and simple.** For every `ε > 0` there is `X₀` such that for all
`0 < t ≤ 1/8`, every zero `z` of `H_t` with `|Re z| ≥ X₀` and `|Re z| ≥ 2π e^{(3/2 + ε)/t}` is real
and simple. -/
theorem riemannHeat_zeros_real_simple_weyl {ε : ℝ} (hε : 0 < ε) :
    ∃ X₀ : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 / 8 → ∀ z : ℂ, riemannHeat t z = 0 → X₀ ≤ |z.re| →
      2 * Real.pi * Real.exp ((3 / 2 + ε) / t) ≤ |z.re| →
        z.im = 0 ∧ deriv (riemannHeat t) z ≠ 0 := by
  set c₀ := 3 / 2 + ε with hc₀def
  obtain ⟨X₁, hX₁⟩ := riemannHeat_zeros_real_weyl hε
  obtain ⟨η, m, hη, hη4, hη6, hm, hmc, hc₀, hδ⟩ := exists_weyl_params (c₀ := c₀) (by linarith)
  obtain ⟨K, hKpos, hK⟩ := exists_norm_xiLine_le_strip_weyl hη (by linarith)
  obtain ⟨α₀, hα₀⟩ := eventually_atTop.mp
    (eventually_sharp_errors_small (c₀ := c₀) (K := K) (b := 9 / 2 * (1 / η + 3)) hη hm hδ)
  refine ⟨max X₁ (2 * Real.pi * Real.exp (2 * max α₀ 160)),
    fun t ht ht8 z hz hX₀ hXc => ?_⟩
  have hreal : z.im = 0 := hX₁ t ht ht8 z hz ((le_max_left _ _).trans hX₀) hXc
  refine ⟨hreal, ?_⟩
  have hX₂ : 2 * Real.pi * Real.exp (2 * max α₀ 160) ≤ |z.re| := (le_max_right _ _).trans hX₀
  have hsimple : ∀ x : ℝ, 2 * Real.pi * Real.exp (2 * max α₀ 160) ≤ x →
      2 * Real.pi * Real.exp (c₀ / t) ≤ x → riemannHeat t x = 0 →
        deriv (riemannHeat t) x ≠ 0 := fun x hx hxc hzx =>
    deriv_riemannHeat_ne_zero_of_re_slope_pos_zero ht
      (re_slope_pos_weyl_window hη hη4 hη6 hm hmc hc₀ hK hKpos.le hα₀ ht ht8 hx hxc 0 (by simp)) hzx
  have hzre : z = ((z.re : ℝ) : ℂ) := by apply Complex.ext <;> simp [hreal]
  rcases le_or_gt 0 z.re with h0 | h0
  · rw [abs_of_nonneg h0] at hX₂ hXc
    rw [hzre]
    exact hsimple z.re hX₂ hXc (by rw [← hzre]; exact hz)
  · rw [abs_of_neg h0] at hX₂ hXc
    have hz' : riemannHeat t ((-z.re : ℝ) : ℂ) = 0 := by
      rw [ofReal_neg, riemannHeat_neg ht.le, ← hzre]; exact hz
    have := hsimple (-z.re) hX₂ hXc hz'
    rw [ofReal_neg, deriv_riemannHeat_neg ht.le, ← hzre] at this
    exact fun h => this (by rw [h, neg_zero])


end

end RHTower.DeBruijn
