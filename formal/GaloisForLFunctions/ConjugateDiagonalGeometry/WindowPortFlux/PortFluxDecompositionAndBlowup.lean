import GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.LogStageBesselCertificate
import GaloisForLFunctions.HTGeometry.RungeGridContour
import GaloisForLFunctions.RHTower.XiLogDerivRePositiveStrict

/-!
# Port-Hermitian Flux Decomposition, Left-Port `L²` Decay, and Right-Edge `Ω(e^t / t)` Blow-Up

For a centered theta window `[-1/2, 3/2] × [y₁, y₂]` and integer-theta prefix `A_N`:

1. **Port-Hermitian functional-equation decomposition** (`thetaLogDeriv_one_sub_conj`,
   `leftEdgeFlux_eq_conj_rightEdgeFlux_neg`, `leftHalfPort_eq_conj_rightHalfPort_neg`,
   `centeredThetaExpSum_eq_rightHalfPort_add_conj_neg`):
   Functional symmetry `A_N(1 - z) = A_N(z)` and Schwarz reflection give
   `L_N(1 - z̄) = -conj(L_N(z))`, turning the left vertical edge into `conj(ℱ_right(-t))` (`O(e^{-t})`
   for `t ≥ 0`) and splitting `centeredThetaExpSum = 𝒫_+(t) + conj(𝒫_+(-t))`.
2. **Unweighted `L²(0, ∞)` left-port decay and pure right-port Laplace equivalence**
   (`exists_leftEdge_and_leftHalfPort_decay`, `integrableOn_leftHalfPort_sq`,
   `integrableOn_windowEnergy_iff_rightHalfPort`):
   One integration by parts on `[-1/2, 1/2] × {y₁, y₂}` bounds `‖𝒫_-(t)‖ ≤ C_L / (t + 1)` for
   `t ≥ 0`, so `𝒫_- ∈ L²(0, ∞)` unconditionally and `e^{-xt}|𝒵_N(t)|² ∈ L¹(0, ∞)` iff
   `e^{-xt}|𝒫_+(t)|² ∈ L¹(0, ∞)` for every `x ≥ 0`.
3. **Unconditional `Ω(e^t / t)` blow-up of right-plus-left flux on every Burnol unit window**
   (`re_logDeriv_xi_three_halves_ge`, `re_thetaLogDeriv_burnol_pos`,
   `exists_burnol_rightAddLeftFlux_exp_blowup`):
   Strict right-of-strip positivity `Re(ξ'/ξ)(3/2 + iy) ≥ 1 / (9 + 4(y - Im ρ₀)²)` transfers at
   explicit prefix `fluxSqrtPrefix m = Θ(√m)` to `Re L_N(3/2 + iy) > 0` at both Burnol heights
   `y₁(m), y₂(m)` for every `m : ℕ`. Twice integration by parts plus exact periodic mean-square
   orthogonality forces both `‖ℱ_right + ℱ_left‖` and `‖ℱ_right + 𝒫_-‖` to exceed `c_{m,N} e^t / t`
   along cofinal `t → +∞`: the `e^t` right-edge flux never cancels against its functional-equation
   image.
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter intervalIntegral
open scoped BigOperators Topology

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.WindowPortFlux

open GaloisForLFunctions.ConjugateDiagonalGeometry
open GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision

/-! ## §1 Port-Hermitian functional-equation decomposition -/

/-- Source logarithmic derivative `L_N(z) = -M_{N,1}(z) / A_N(z) = A_N'(z) / A_N(z)`. -/
def thetaLogDeriv (N : ℕ) (z : ℂ) : ℂ :=
  -_root_.RHTower.finiteThetaFirstMoment N z / _root_.RHTower.finiteThetaAmplitude N z

theorem thetaLogDeriv_eq_logDeriv (N : ℕ) (z : ℂ) :
    thetaLogDeriv N z = logDeriv (_root_.RHTower.finiteThetaAmplitude N) z := by
  rw [thetaLogDeriv, logDeriv_apply, _root_.RHTower.deriv_finiteThetaAmplitude]

theorem analyticOnNhd_finiteThetaAmplitude' (N : ℕ) :
    AnalyticOnNhd ℂ (_root_.RHTower.finiteThetaAmplitude N) Set.univ := fun w _ => by
  have hfun : _root_.RHTower.finiteThetaAmplitude N = finiteThetaShellPencil N 0 :=
    (funext (finiteThetaShellPencil_zero N)).symm
  rw [hfun]
  exact analyticOnNhd_finiteThetaShellPencil N 0 w (Set.mem_univ w)

theorem analyticAt_thetaLogDeriv {N : ℕ} {z : ℂ}
    (hnz : _root_.RHTower.finiteThetaAmplitude N z ≠ 0) :
    AnalyticAt ℂ (thetaLogDeriv N) z := by
  have han : AnalyticAt ℂ (_root_.RHTower.finiteThetaAmplitude N) z :=
    analyticOnNhd_finiteThetaAmplitude' N z (Set.mem_univ z)
  have hfun : thetaLogDeriv N =
      fun w => deriv (_root_.RHTower.finiteThetaAmplitude N) w /
        _root_.RHTower.finiteThetaAmplitude N w := by
    funext w
    rw [thetaLogDeriv_eq_logDeriv, logDeriv_apply]
  rw [hfun]
  exact han.deriv.div han hnz

/-- Functional-equation and Schwarz reflection law `L_N(1 - z̄) = -conj(L_N(z))`. -/
theorem thetaLogDeriv_one_sub_conj (N : ℕ) (z : ℂ) :
    thetaLogDeriv N (1 - star z) = -star (thetaLogDeriv N z) := by
  set A := _root_.RHTower.finiteThetaAmplitude N with hA_def
  have hdiff : Differentiable ℂ A := _root_.RHTower.differentiable_finiteThetaAmplitude N
  have hA_symm : A (1 - star z) = star (A z) := by
    rw [hA_def, finiteThetaAmplitude_one_sub N (star z)]
    have hc := finiteThetaAmplitude_conj N (star z)
    simp only [Complex.star_def, Complex.conj_conj] at hc ⊢
    exact hc.symm
  have hd_sub : ∀ w : ℂ, deriv A (1 - w) = -deriv A w := fun w => by
    have h1 : HasDerivAt (fun u : ℂ => A (1 - u)) (deriv A (1 - w) * (-1)) w :=
      (hdiff (1 - w)).hasDerivAt.comp w
        (((hasDerivAt_const w (1 : ℂ)).sub (hasDerivAt_id w)).congr_deriv (by ring))
    have h2 : HasDerivAt (fun u : ℂ => A (1 - u)) (deriv A w) w := by
      have heq : (fun u : ℂ => A (1 - u)) = A := funext (finiteThetaAmplitude_one_sub N)
      rw [heq]
      exact (hdiff w).hasDerivAt
    linear_combination -(h1.unique h2)
  have hd_conj : deriv A (star z) = star (deriv A z) := by
    have h3 : HasDerivAt ((starRingEnd ℂ) ∘ A ∘ (starRingEnd ℂ))
        ((starRingEnd ℂ) (deriv A z)) ((starRingEnd ℂ) z) :=
      (hdiff z).hasDerivAt.conj_conj
    have h4 : HasDerivAt ((starRingEnd ℂ) ∘ A ∘ (starRingEnd ℂ))
        (deriv A ((starRingEnd ℂ) z)) ((starRingEnd ℂ) z) := by
      have heq : ((starRingEnd ℂ) ∘ A ∘ (starRingEnd ℂ)) = A :=
        funext (finiteThetaAmplitude_conj N)
      rw [heq]
      exact (hdiff _).hasDerivAt
    simpa only [Complex.star_def] using (h3.unique h4).symm
  rw [thetaLogDeriv_eq_logDeriv, thetaLogDeriv_eq_logDeriv, logDeriv_apply, logDeriv_apply,
    ← hA_def, hd_sub (star z), hd_conj, hA_symm, neg_div, star_div₀]

/-- Oriented vertical-line flux `(2π)⁻¹ ∫_{y₁}^{y₂} e^{t(σ - 1/2 + iy)} L_N(σ + iy) dy`. -/
def vertFlux (σ y₁ y₂ : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  ((2 * Real.pi : ℂ)⁻¹) *
    ∫ y in y₁..y₂, cexp ((t : ℂ) * (((σ : ℂ) + (y : ℂ) * I) - 1 / 2)) *
      thetaLogDeriv N ((σ : ℂ) + (y : ℂ) * I)

/-- Right vertical-edge flux at `σ = 3/2`. -/
def rightEdgeFlux (y₁ y₂ : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  vertFlux (3 / 2) y₁ y₂ N t

/-- Left vertical-edge flux at `σ = -1/2` (positively oriented along rectangle boundary). -/
def leftEdgeFlux (y₁ y₂ : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  -vertFlux (-1 / 2) y₁ y₂ N t

/-- Horizontal cap flux across `[a, b] × {y₁, y₂}` (bottom minus top, divided by `2πi`). -/
def horizCapFlux (a b y₁ y₂ : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  (2 * Real.pi * I)⁻¹ *
    ((∫ x in a..b, cexp ((t : ℂ) * (((x : ℂ) + (y₁ : ℂ) * I) - 1 / 2)) *
        thetaLogDeriv N ((x : ℂ) + (y₁ : ℂ) * I)) -
      (∫ x in a..b, cexp ((t : ℂ) * (((x : ℂ) + (y₂ : ℂ) * I) - 1 / 2)) *
        thetaLogDeriv N ((x : ℂ) + (y₂ : ℂ) * I)))

/-- Right half-window port `𝒫_+(t)`: right vertical edge plus right horizontal caps `[1/2, 3/2]`. -/
def rightHalfPort (y₁ y₂ : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  rightEdgeFlux y₁ y₂ N t + horizCapFlux (1 / 2) (3 / 2) y₁ y₂ N t

/-- Left half-window port `𝒫_-(t)`: left vertical edge plus left horizontal caps `[-1/2, 1/2]`. -/
def leftHalfPort (y₁ y₂ : ℝ) (N : ℕ) (t : ℝ) : ℂ :=
  leftEdgeFlux y₁ y₂ N t + horizCapFlux (-1 / 2) (1 / 2) y₁ y₂ N t

private theorem star_intervalIntegral (a b : ℝ) (f : ℝ → ℂ) :
    star (∫ x in a..b, f x) = ∫ x in a..b, star (f x) := by
  simp only [Complex.star_def, intervalIntegral.intervalIntegral_conj]

/-- Unconditional four-edge expansion of `centeredThetaExpSum`. -/
theorem centeredThetaExpSum_eq_edges (y₁ y₂ : ℝ) (N : ℕ) (t : ℝ) :
    centeredThetaExpSum y₁ y₂ N t =
      rightEdgeFlux y₁ y₂ N t + leftEdgeFlux y₁ y₂ N t +
        horizCapFlux (-1 / 2) (3 / 2) y₁ y₂ N t := by
  have hll : centeredWindowLowerLeft y₁ = ((-1 / 2 : ℝ) : ℂ) + (y₁ : ℂ) * I := by
    unfold centeredWindowLowerLeft; push_cast; ring
  have hur : centeredWindowUpperRight y₂ = ((3 / 2 : ℝ) : ℂ) + (y₂ : ℂ) * I := by
    unfold centeredWindowUpperRight; push_cast; ring
  unfold centeredThetaExpSum rightEdgeFlux leftEdgeFlux vertFlux horizCapFlux thetaLogDeriv
  rw [hll, hur, HTGeometry.rectIntegral_eq_edges]
  unfold HTGeometry.hEdge HTGeometry.vEdge
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hcancel : ∀ w : ℂ, (2 * Real.pi * I)⁻¹ * (I * w) = (2 * Real.pi : ℂ)⁻¹ * w := fun w => by
    field_simp [hpi, I_ne_zero]
  rw [mul_sub, mul_add, mul_sub, hcancel, hcancel]
  ring

/-- Functional-equation reflection turns the left vertical edge into `conj(ℱ_right(-t))`. -/
theorem leftEdgeFlux_eq_conj_rightEdgeFlux_neg (y₁ y₂ : ℝ) (N : ℕ) (t : ℝ) :
    leftEdgeFlux y₁ y₂ N t = star (rightEdgeFlux y₁ y₂ N (-t)) := by
  unfold leftEdgeFlux rightEdgeFlux vertFlux
  have hstar_pi : star ((2 * Real.pi : ℂ)⁻¹) = (2 * Real.pi : ℂ)⁻¹ := by
    simp
  rw [star_mul', hstar_pi, star_intervalIntegral, ← neg_mul_eq_mul_neg, ← mul_neg,
    ← intervalIntegral.integral_neg]
  congr 1
  refine intervalIntegral.integral_congr fun y _ => ?_
  have hpt : ((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I = 1 - star (((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) := by
    simp only [Complex.star_def, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  have hexp : cexp ((t : ℂ) * ((((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) - 1 / 2)) =
      star (cexp (((-t : ℝ) : ℂ) * ((((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) - 1 / 2))) := by
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp only [map_mul, map_sub, map_add, map_div₀, map_one, map_ofNat, Complex.conj_ofReal,
      Complex.conj_I]
    push_cast; ring
  rw [hexp, hpt, thetaLogDeriv_one_sub_conj, star_mul']
  ring

/-- Functional-equation reflection turns the left horizontal cap `[-1/2, 1/2]` into
`conj(ℱ_horiz(1/2, 3/2, -t))`. -/
theorem horizCapFlux_left_eq_conj_right_neg (y₁ y₂ : ℝ) (N : ℕ) (t : ℝ) :
    horizCapFlux (-1 / 2) (1 / 2) y₁ y₂ N t =
      star (horizCapFlux (1 / 2) (3 / 2) y₁ y₂ N (-t)) := by
  have hseg : ∀ y : ℝ,
      (∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
          cexp ((t : ℂ) * (((x : ℂ) + (y : ℂ) * I) - 1 / 2)) *
            thetaLogDeriv N ((x : ℂ) + (y : ℂ) * I)) =
        -(∫ u in (1 / 2 : ℝ)..(3 / 2 : ℝ),
          star (cexp (((-t : ℝ) : ℂ) * (((u : ℂ) + (y : ℂ) * I) - 1 / 2)) *
            thetaLogDeriv N ((u : ℂ) + (y : ℂ) * I))) := fun y => by
    have hcomp := intervalIntegral.integral_comp_sub_left
      (a := (1 / 2 : ℝ)) (b := (3 / 2 : ℝ))
      (fun x : ℝ => cexp ((t : ℂ) * (((x : ℂ) + (y : ℂ) * I) - 1 / 2)) *
        thetaLogDeriv N ((x : ℂ) + (y : ℂ) * I)) (1 : ℝ)
    have ha : (1 : ℝ) - 3 / 2 = -1 / 2 := by norm_num
    have hb : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    rw [ha, hb] at hcomp
    rw [← hcomp, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun u _ => ?_
    have hpt : (((1 - u : ℝ) : ℂ) + (y : ℂ) * I) = 1 - star ((u : ℂ) + (y : ℂ) * I) := by
      simp only [Complex.star_def, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast; ring
    have hexp : cexp ((t : ℂ) * ((((1 - u : ℝ) : ℂ) + (y : ℂ) * I) - 1 / 2)) =
        star (cexp (((-t : ℝ) : ℂ) * (((u : ℂ) + (y : ℂ) * I) - 1 / 2))) := by
      rw [Complex.star_def, ← Complex.exp_conj]
      congr 1
      simp only [map_mul, map_sub, map_add, map_div₀, map_one, map_ofNat, Complex.conj_ofReal,
        Complex.conj_I]
      push_cast; ring
    rw [hexp, hpt, thetaLogDeriv_one_sub_conj, star_mul']
    ring
  unfold horizCapFlux
  have hstar_pre : star ((2 * Real.pi * I)⁻¹) = -(2 * Real.pi * I)⁻¹ := by
    have hpi : (2 * Real.pi : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero
    simp only [Complex.star_def, map_inv₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    field_simp [hpi, I_ne_zero]
  rw [star_mul', hstar_pre, star_sub, star_intervalIntegral, star_intervalIntegral,
    hseg y₁, hseg y₂]
  ring

/-- Exact functional-equation conjugation `𝒫_-(t) = conj(𝒫_+(-t))`. -/
theorem leftHalfPort_eq_conj_rightHalfPort_neg (y₁ y₂ : ℝ) (N : ℕ) (t : ℝ) :
    leftHalfPort y₁ y₂ N t = star (rightHalfPort y₁ y₂ N (-t)) := by
  unfold leftHalfPort rightHalfPort
  rw [star_add, leftEdgeFlux_eq_conj_rightEdgeFlux_neg, horizCapFlux_left_eq_conj_right_neg]

private lemma continuousWithinAt_comp_line {h : ℂ → ℂ} {s : Set ℝ} {t : ℝ} {φ : ℝ → ℂ}
    (hφ : Continuous φ) (hh : AnalyticAt ℂ h (φ t)) :
    ContinuousWithinAt (fun u => h (φ u)) s t :=
  (hh.continuousAt.comp hφ.continuousAt).continuousWithinAt

theorem exists_boundaryPath_of_edges {z₁ z₂ z : ℂ}
    (hre : z₁.re ≤ z₂.re) (_ : z₁.im ≤ z₂.im)
    (hx : z₁.re ≤ z.re ∧ z.re ≤ z₂.re) (hy : z₁.im ≤ z.im ∧ z.im ≤ z₂.im)
    (hedge : z.re = z₁.re ∨ z.re = z₂.re ∨ z.im = z₁.im ∨ z.im = z₂.im) :
    ∃ τ : ℝ, _root_.RHTower.rectangleBoundaryPath z₁ z₂ τ = z := by
  by_cases hy1 : z.im = z₁.im
  · rcases eq_or_lt_of_le hre with hxeq | hxlt
    · refine ⟨0, ?_⟩
      rw [_root_.RHTower.rectangleBoundaryPath, Int.fract_zero, _root_.RHTower.rectangleEdgePath_zero]
      exact Complex.ext (by linarith [hx.1, hx.2]) hy1.symm
    · set τ : ℝ := (z.re - z₁.re) / (4 * (z₂.re - z₁.re))
      have hdx : 0 < z₂.re - z₁.re := sub_pos.mpr hxlt
      have hτ_nn : 0 ≤ τ := div_nonneg (by linarith [hx.1]) (by positivity)
      have hτ_le : τ ≤ 1 / 4 := by
        dsimp only [τ]
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith [hx.2]
      refine ⟨τ, ?_⟩
      rw [_root_.RHTower.rectangleBoundaryPath, Int.fract_eq_self.mpr ⟨hτ_nn, by linarith⟩,
        _root_.RHTower.rectangleEdgePath, if_pos hτ_le]
      apply Complex.ext
      · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
          Complex.ofReal_im, Complex.I_im, mul_zero]
        dsimp only [τ]; field_simp [hdx.ne']; ring
      · simp [hy1]
  · have hy1_lt : z₁.im < z.im := lt_of_le_of_ne hy.1 (Ne.symm hy1)
    have hdy : 0 < z₂.im - z₁.im := by linarith [hy.2]
    by_cases hx2 : z.re = z₂.re
    · set τ : ℝ := 1 / 4 + (z.im - z₁.im) / (4 * (z₂.im - z₁.im))
      have hτ_gt : 1 / 4 < τ := by
        dsimp only [τ]
        linarith [div_pos (sub_pos.mpr hy1_lt) (by positivity : 0 < 4 * (z₂.im - z₁.im))]
      have hτ_le : τ ≤ 1 / 2 := by
        dsimp only [τ]
        have h1 : (z.im - z₁.im) / (4 * (z₂.im - z₁.im)) ≤ 1 / 4 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith [hy.2]
        linarith
      refine ⟨τ, ?_⟩
      rw [_root_.RHTower.rectangleBoundaryPath, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩,
        _root_.RHTower.rectangleEdgePath, if_neg (not_le.mpr hτ_gt), if_pos hτ_le]
      apply Complex.ext
      · simp [hx2]
      · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
          Complex.ofReal_re, Complex.I_im, mul_one, zero_add]
        dsimp only [τ]; field_simp [hdy.ne']; ring
    · have hx2_lt : z.re < z₂.re := lt_of_le_of_ne hx.2 hx2
      have hdx : 0 < z₂.re - z₁.re := by linarith [hx.1]
      by_cases hy2 : z.im = z₂.im
      · set τ : ℝ := 1 / 2 + (z₂.re - z.re) / (4 * (z₂.re - z₁.re))
        have hτ_gt : 1 / 2 < τ := by
          dsimp only [τ]
          linarith [div_pos (sub_pos.mpr hx2_lt) (by positivity : 0 < 4 * (z₂.re - z₁.re))]
        have hτ_le : τ ≤ 3 / 4 := by
          dsimp only [τ]
          have h1 : (z₂.re - z.re) / (4 * (z₂.re - z₁.re)) ≤ 1 / 4 := by
            rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith [hx.1]
          linarith
        refine ⟨τ, ?_⟩
        rw [_root_.RHTower.rectangleBoundaryPath, Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩,
          _root_.RHTower.rectangleEdgePath, if_neg (by linarith), if_neg (not_le.mpr hτ_gt),
          if_pos hτ_le]
        apply Complex.ext
        · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
            Complex.ofReal_im, Complex.I_im, mul_zero]
          dsimp only [τ]; field_simp [hdx.ne']; ring
        · simp [hy2]
      · have hy2_lt : z.im < z₂.im := lt_of_le_of_ne hy.2 hy2
        have hx1 : z.re = z₁.re := by
          rcases hedge with h | h | h | h
          · exact h
          · exact absurd h hx2
          · exact absurd h hy1
          · exact absurd h hy2
        set τ : ℝ := 3 / 4 + (z₂.im - z.im) / (4 * (z₂.im - z₁.im))
        have hτ_gt : 3 / 4 < τ := by
          dsimp only [τ]
          linarith [div_pos (sub_pos.mpr hy2_lt) (by positivity : 0 < 4 * (z₂.im - z₁.im))]
        have hτ_lt : τ < 1 := by
          dsimp only [τ]
          have h1 : (z₂.im - z.im) / (4 * (z₂.im - z₁.im)) < 1 / 4 := by
            rw [div_lt_div_iff₀ (by positivity) (by norm_num)]; linarith [hy1_lt]
          linarith
        refine ⟨τ, ?_⟩
        rw [_root_.RHTower.rectangleBoundaryPath, Int.fract_eq_self.mpr ⟨by linarith, hτ_lt⟩,
          _root_.RHTower.rectangleEdgePath, if_neg (by linarith), if_neg (by linarith),
          if_neg (not_le.mpr hτ_gt)]
        apply Complex.ext
        · simp [hx1]
        · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
            Complex.ofReal_re, Complex.I_im, mul_one, zero_add]
          dsimp only [τ]; field_simp [hdy.ne']; ring

theorem edge_ne_zero_of_bdry_regular {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) {N : ℕ}
    (hbdry : ∀ τ : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath
        (centeredWindowLowerLeft y₁) (centeredWindowUpperRight y₂) τ) ≠ 0)
    {z : ℂ} (hx : -1 / 2 ≤ z.re ∧ z.re ≤ 3 / 2) (hyz : y₁ ≤ z.im ∧ z.im ≤ y₂)
    (hedge : z.re = -1 / 2 ∨ z.re = 3 / 2 ∨ z.im = y₁ ∨ z.im = y₂) :
    _root_.RHTower.finiteThetaAmplitude N z ≠ 0 := by
  obtain ⟨τ, hτ⟩ := exists_boundaryPath_of_edges
    (z₁ := centeredWindowLowerLeft y₁) (z₂ := centeredWindowUpperRight y₂)
    (by simp; norm_num) (by simpa using hy)
    (by simpa using hx) (by simpa using hyz) (by simpa using hedge)
  rw [← hτ]
  exact hbdry τ

/-- Port-Hermitian decomposition `𝒵_N(t) = 𝒫_+(t) + 𝒫_-(t)` on any boundary-regular centered
window. -/
theorem centeredThetaExpSum_eq_rightHalfPort_add_leftHalfPort {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂)
    (N : ℕ)
    (hbdry : ∀ τ : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath
        (centeredWindowLowerLeft y₁) (centeredWindowUpperRight y₂) τ) ≠ 0)
    (t : ℝ) :
    centeredThetaExpSum y₁ y₂ N t = rightHalfPort y₁ y₂ N t + leftHalfPort y₁ y₂ N t := by
  have hsplit : ∀ y : ℝ, (y = y₁ ∨ y = y₂) →
      (∫ x in (-1 / 2 : ℝ)..(3 / 2 : ℝ),
          cexp ((t : ℂ) * (((x : ℂ) + (y : ℂ) * I) - 1 / 2)) *
            thetaLogDeriv N ((x : ℂ) + (y : ℂ) * I)) =
        (∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
          cexp ((t : ℂ) * (((x : ℂ) + (y : ℂ) * I) - 1 / 2)) *
            thetaLogDeriv N ((x : ℂ) + (y : ℂ) * I)) +
        (∫ x in (1 / 2 : ℝ)..(3 / 2 : ℝ),
          cexp ((t : ℂ) * (((x : ℂ) + (y : ℂ) * I) - 1 / 2)) *
            thetaLogDeriv N ((x : ℂ) + (y : ℂ) * I)) := by
    intro y hy_or
    have hcont : ContinuousOn
        (fun x : ℝ => cexp ((t : ℂ) * (((x : ℂ) + (y : ℂ) * I) - 1 / 2)) *
          thetaLogDeriv N ((x : ℂ) + (y : ℂ) * I))
        (Icc (-1 / 2 : ℝ) (3 / 2 : ℝ)) := by
      refine ContinuousOn.mul (by fun_prop) ?_
      intro x hx
      have hnz : _root_.RHTower.finiteThetaAmplitude N ((x : ℂ) + (y : ℂ) * I) ≠ 0 := by
        refine edge_ne_zero_of_bdry_regular hy hbdry ⟨by simpa using hx.1, by simpa using hx.2⟩ ?_ ?_
        · rcases hy_or with rfl | rfl <;> simp [hy]
        · rcases hy_or with rfl | rfl
          · exact Or.inr (Or.inr (Or.inl (by simp)))
          · exact Or.inr (Or.inr (Or.inr (by simp)))
      exact continuousWithinAt_comp_line (by fun_prop) (analyticAt_thetaLogDeriv hnz)
    have hi1 : IntervalIntegrable
        (fun x : ℝ => cexp ((t : ℂ) * (((x : ℂ) + (y : ℂ) * I) - 1 / 2)) *
          thetaLogDeriv N ((x : ℂ) + (y : ℂ) * I)) volume (-1 / 2) (1 / 2) :=
      (hcont.mono (Icc_subset_Icc_right (by norm_num))).intervalIntegrable_of_Icc (by norm_num)
    have hi2 : IntervalIntegrable
        (fun x : ℝ => cexp ((t : ℂ) * (((x : ℂ) + (y : ℂ) * I) - 1 / 2)) *
          thetaLogDeriv N ((x : ℂ) + (y : ℂ) * I)) volume (1 / 2) (3 / 2) :=
      (hcont.mono (Icc_subset_Icc_left (by norm_num))).intervalIntegrable_of_Icc (by norm_num)
    exact (intervalIntegral.integral_add_adjacent_intervals hi1 hi2).symm
  rw [centeredThetaExpSum_eq_edges]
  unfold rightHalfPort leftHalfPort horizCapFlux
  rw [hsplit y₁ (Or.inl rfl), hsplit y₂ (Or.inr rfl)]
  ring

theorem centeredThetaExpSum_eq_rightHalfPort_add_conj_neg {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂)
    (N : ℕ)
    (hbdry : ∀ τ : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath
        (centeredWindowLowerLeft y₁) (centeredWindowUpperRight y₂) τ) ≠ 0)
    (t : ℝ) :
    centeredThetaExpSum y₁ y₂ N t =
      rightHalfPort y₁ y₂ N t + star (rightHalfPort y₁ y₂ N (-t)) := by
  rw [centeredThetaExpSum_eq_rightHalfPort_add_leftHalfPort hy N hbdry t,
    leftHalfPort_eq_conj_rightHalfPort_neg]


/-! ## §2 Unconditional unweighted `L²(0, ∞)` left-port decay and pure right-port Laplace equivalence -/

private lemma continuous_parametric_intervalIntegral_of_continuousOn {a b : ℝ} (hab : a ≤ b)
    {Φ : ℝ → ℝ → ℂ} {g : ℝ → ℂ}
    (hΦ : Continuous (Function.uncurry Φ)) (hg : ContinuousOn g (Icc a b)) :
    Continuous (fun t : ℝ => ∫ u in a..b, Φ t u * g u) := by
  set c : ℝ → ℝ := fun u => max a (min u b) with hc_def
  have hc_cont : Continuous c := continuous_const.max (continuous_id.min continuous_const)
  have hc_mem : ∀ u : ℝ, c u ∈ Icc a b :=
    fun u => ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  have hclamped : Continuous (fun t : ℝ => ∫ u in a..b, Φ t u * g (c u)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    have h1 : Continuous (fun p : ℝ × ℝ => Φ p.1 p.2) := hΦ
    have h2 : Continuous (fun p : ℝ × ℝ => g (c p.2)) :=
      (hg.comp_continuous hc_cont hc_mem).comp continuous_snd
    exact h1.mul h2
  refine hclamped.congr fun t => ?_
  refine intervalIntegral.integral_congr fun u hu => ?_
  rw [uIcc_of_le hab] at hu
  have hcu : c u = u := by
    dsimp only [c]
    rw [min_eq_left hu.2, max_eq_right hu.1]
  rw [hcu]

theorem continuous_vertFlux_of_ne_zero {σ y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) {N : ℕ}
    (hnz : ∀ y ∈ Icc y₁ y₂, _root_.RHTower.finiteThetaAmplitude N ((σ : ℂ) + (y : ℂ) * I) ≠ 0) :
    Continuous (vertFlux σ y₁ y₂ N) := by
  unfold vertFlux
  refine continuous_const.mul ?_
  refine continuous_parametric_intervalIntegral_of_continuousOn hy (by fun_prop) ?_
  intro y hy_mem
  exact continuousWithinAt_comp_line (by fun_prop) (analyticAt_thetaLogDeriv (hnz y hy_mem))

theorem continuous_horizCapFlux_of_ne_zero {a b y₁ y₂ : ℝ} (hab : a ≤ b) {N : ℕ}
    (hnz1 : ∀ x ∈ Icc a b, _root_.RHTower.finiteThetaAmplitude N ((x : ℂ) + (y₁ : ℂ) * I) ≠ 0)
    (hnz2 : ∀ x ∈ Icc a b, _root_.RHTower.finiteThetaAmplitude N ((x : ℂ) + (y₂ : ℂ) * I) ≠ 0) :
    Continuous (horizCapFlux a b y₁ y₂ N) := by
  unfold horizCapFlux
  refine continuous_const.mul (Continuous.sub ?_ ?_)
  · refine continuous_parametric_intervalIntegral_of_continuousOn hab (by fun_prop) ?_
    intro x hx
    exact continuousWithinAt_comp_line (by fun_prop) (analyticAt_thetaLogDeriv (hnz1 x hx))
  · refine continuous_parametric_intervalIntegral_of_continuousOn hab (by fun_prop) ?_
    intro x hx
    exact continuousWithinAt_comp_line (by fun_prop) (analyticAt_thetaLogDeriv (hnz2 x hx))

private lemma exists_norm_left_horiz_integral_le {y : ℝ} {N : ℕ}
    (hnz : ∀ x ∈ Icc (-1 / 2 : ℝ) (1 / 2 : ℝ),
      _root_.RHTower.finiteThetaAmplitude N ((x : ℂ) + (y : ℂ) * I) ≠ 0) :
    ∃ C_H : ℝ, 0 < C_H ∧ ∀ t : ℝ, 0 ≤ t →
      ‖∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
          cexp ((t : ℂ) * (((x : ℂ) + (y : ℂ) * I) - 1 / 2)) *
            thetaLogDeriv N ((x : ℂ) + (y : ℂ) * I)‖ ≤ C_H / (t + 1) := by
  set g : ℝ → ℂ := fun x => thetaLogDeriv N ((x : ℂ) + (y : ℂ) * I) with hg_def
  set g' : ℝ → ℂ := fun x => deriv (thetaLogDeriv N) ((x : ℂ) + (y : ℂ) * I) with hg'_def
  have hg_cont : ContinuousOn g (Icc (-1 / 2 : ℝ) (1 / 2 : ℝ)) :=
    fun x hx => continuousWithinAt_comp_line (by fun_prop) (analyticAt_thetaLogDeriv (hnz x hx))
  have hg'_cont : ContinuousOn g' (Icc (-1 / 2 : ℝ) (1 / 2 : ℝ)) :=
    fun x hx => continuousWithinAt_comp_line (by fun_prop)
      (analyticAt_thetaLogDeriv (hnz x hx)).deriv
  obtain ⟨M₀, hM₀_bd⟩ := isCompact_Icc.exists_bound_of_continuousOn hg_cont
  obtain ⟨M₁, hM₁_bd⟩ := isCompact_Icc.exists_bound_of_continuousOn hg'_cont
  have hM₀_nn : 0 ≤ M₀ := (norm_nonneg (g 0)).trans (hM₀_bd 0 ⟨by norm_num, by norm_num⟩)
  have hM₁_nn : 0 ≤ M₁ := (norm_nonneg (g' 0)).trans (hM₁_bd 0 ⟨by norm_num, by norm_num⟩)
  let C_H : ℝ := 4 * (M₀ + M₁ + 1)
  refine ⟨C_H, by dsimp [C_H]; positivity, fun t ht => ?_⟩
  have hexp_le_one : ∀ x ∈ Icc (-1 / 2 : ℝ) (1 / 2 : ℝ),
      ‖cexp ((t : ℂ) * (((x : ℂ) + (y : ℂ) * I) - 1 / 2))‖ ≤ 1 := by
    intro x hx
    rw [Complex.norm_exp, Real.exp_le_one_iff]
    have hre : ((t : ℂ) * (((x : ℂ) + (y : ℂ) * I) - 1 / 2)).re = t * (x - 1 / 2) := by
      simp [Complex.mul_re, Complex.sub_re]
    rw [hre]
    exact mul_nonpos_of_nonneg_of_nonpos ht (by linarith [hx.2])
  by_cases ht1 : t ≤ 1
  · have hbound : ∀ x ∈ Icc (-1 / 2 : ℝ) (1 / 2 : ℝ),
        ‖cexp ((t : ℂ) * (((x : ℂ) + (y : ℂ) * I) - 1 / 2)) * g x‖ ≤ M₀ := by
      intro x hx_cc
      rw [norm_mul]
      calc ‖cexp ((t : ℂ) * (((x : ℂ) + (y : ℂ) * I) - 1 / 2))‖ * ‖g x‖
          ≤ 1 * M₀ := mul_le_mul (hexp_le_one x hx_cc) (hM₀_bd x hx_cc) (norm_nonneg _) zero_le_one
        _ = M₀ := one_mul M₀
    have hint_le : ‖∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
        cexp ((t : ℂ) * (((x : ℂ) + (y : ℂ) * I) - 1 / 2)) * g x‖ ≤ M₀ * |(1 / 2 : ℝ) - (-1 / 2)| :=
      intervalIntegral.norm_integral_le_of_norm_le_const' (by norm_num) hbound
    have habs1 : |(1 / 2 : ℝ) - (-1 / 2)| = 1 := by norm_num
    rw [habs1, mul_one] at hint_le
    have hle_CH : M₀ ≤ C_H / (t + 1) := by
      rw [le_div_iff₀ (by linarith)]
      dsimp [C_H]; nlinarith
    exact hint_le.trans hle_CH
  · replace ht1 : 1 < t := not_le.mp ht1
    have ht_pos : 0 < t := by linarith
    have htC_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht_pos.ne'
    set E : ℝ → ℂ := fun x => cexp ((t : ℂ) * (((x : ℂ) + (y : ℂ) * I) - 1 / 2)) with hE_def
    set H : ℝ → ℂ := fun x => ((t : ℂ)⁻¹ * E x) * g x with hH_def
    have hderiv_H : ∀ x ∈ uIcc (-1 / 2 : ℝ) (1 / 2 : ℝ),
        HasDerivAt H (E x * g x + (t : ℂ)⁻¹ * (E x * g' x)) x := by
      rw [uIcc_of_le (by norm_num)]
      intro x hx
      have hE_d : HasDerivAt E ((t : ℂ) * E x) x := by
        have hw : HasDerivAt
            (fun w : ℂ => cexp ((t : ℂ) * ((w + (y : ℂ) * I) - 1 / 2)))
            (cexp ((t : ℂ) * ((((x : ℂ) + (y : ℂ) * I)) - 1 / 2)) * (t : ℂ)) (x : ℂ) := by
          have hlin : HasDerivAt (fun w : ℂ => (t : ℂ) * ((w + (y : ℂ) * I) - 1 / 2))
              (t : ℂ) (x : ℂ) := by
            simpa using (((hasDerivAt_id (x : ℂ)).add_const ((y : ℂ) * I)).sub_const
              (1 / 2 : ℂ)).const_mul (t : ℂ)
          exact hlin.cexp
        exact (hw.comp_ofReal).congr_deriv (by rw [hE_def]; ring)
      have hg_d : HasDerivAt g (g' x) x := by
        have hw := (analyticAt_thetaLogDeriv (hnz x hx)).differentiableAt.hasDerivAt.comp (x : ℂ)
          ((hasDerivAt_id (x : ℂ)).add_const ((y : ℂ) * I))
        exact (hw.comp_ofReal).congr_deriv (by dsimp only [g']; ring)
      have hprod : HasDerivAt H
          (((t : ℂ)⁻¹ * ((t : ℂ) * E x)) * g x + ((t : ℂ)⁻¹ * E x) * g' x) x :=
        HasDerivAt.mul (hE_d.const_mul (t : ℂ)⁻¹) hg_d
      exact hprod.congr_deriv (by
        rw [inv_mul_cancel_left₀ htC_ne]
        ring)
    have hi_eg : IntervalIntegrable (fun x => E x * g x) volume (-1 / 2) (1 / 2) :=
      ((ContinuousOn.mul (by fun_prop) hg_cont)).intervalIntegrable_of_Icc (by norm_num)
    have hi_eg' : IntervalIntegrable (fun x => (t : ℂ)⁻¹ * (E x * g' x)) volume (-1 / 2) (1 / 2) :=
      ((ContinuousOn.const_smul ((ContinuousOn.mul (by fun_prop) hg'_cont))
        (t : ℂ)⁻¹)).intervalIntegrable_of_Icc (by norm_num)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv_H (hi_eg.add hi_eg')
    rw [intervalIntegral.integral_add hi_eg hi_eg'] at hftc
    have hibp : (∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), E x * g x) =
        H (1 / 2) - H (-1 / 2) -
          (t : ℂ)⁻¹ * ∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), E x * g' x := by
      rw [← intervalIntegral.integral_const_mul]
      linear_combination hftc
    have hH_half : ‖H (1 / 2)‖ ≤ M₀ / t := by
      dsimp only [H]
      rw [norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht_pos.le]
      have h12 : ‖E (1 / 2)‖ * ‖g (1 / 2)‖ ≤ M₀ := by
        calc ‖E (1 / 2)‖ * ‖g (1 / 2)‖
            ≤ 1 * M₀ := mul_le_mul (hexp_le_one (1 / 2) ⟨by norm_num, le_rfl⟩)
                (hM₀_bd (1 / 2) ⟨by norm_num, le_rfl⟩) (norm_nonneg _) zero_le_one
          _ = M₀ := one_mul M₀
      calc t⁻¹ * ‖E (1 / 2)‖ * ‖g (1 / 2)‖
          = (‖E (1 / 2)‖ * ‖g (1 / 2)‖) / t := by ring
        _ ≤ M₀ / t := div_le_div_of_nonneg_right h12 ht_pos.le
    have hH_mhalf : ‖H (-1 / 2)‖ ≤ M₀ / t := by
      dsimp only [H]
      rw [norm_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht_pos.le]
      have h12 : ‖E (-1 / 2)‖ * ‖g (-1 / 2)‖ ≤ M₀ := by
        calc ‖E (-1 / 2)‖ * ‖g (-1 / 2)‖
            ≤ 1 * M₀ := mul_le_mul (hexp_le_one (-1 / 2) ⟨le_rfl, by norm_num⟩)
                (hM₀_bd (-1 / 2) ⟨le_rfl, by norm_num⟩) (norm_nonneg _) zero_le_one
          _ = M₀ := one_mul M₀
      calc t⁻¹ * ‖E (-1 / 2)‖ * ‖g (-1 / 2)‖
          = (‖E (-1 / 2)‖ * ‖g (-1 / 2)‖) / t := by ring
        _ ≤ M₀ / t := div_le_div_of_nonneg_right h12 ht_pos.le
    have hint_g' : ‖∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), E x * g' x‖ ≤ M₁ := by
      have hb : ∀ x ∈ Icc (-1 / 2 : ℝ) (1 / 2 : ℝ), ‖E x * g' x‖ ≤ M₁ := by
        intro x hx_cc
        rw [norm_mul]
        calc ‖E x‖ * ‖g' x‖ ≤ 1 * M₁ :=
              mul_le_mul (hexp_le_one x hx_cc) (hM₁_bd x hx_cc) (norm_nonneg _) zero_le_one
          _ = M₁ := one_mul M₁
      have hi := intervalIntegral.norm_integral_le_of_norm_le_const' (by norm_num) hb
      have habs1 : |(1 / 2 : ℝ) - (-1 / 2)| = 1 := by norm_num
      rwa [habs1, mul_one] at hi
    have hrem_norm : ‖(t : ℂ)⁻¹ * ∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), E x * g' x‖ ≤ M₁ / t := by
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg ht_pos.le, inv_mul_eq_div]
      exact div_le_div_of_nonneg_right hint_g' ht_pos.le
    rw [hibp]
    calc ‖H (1 / 2) - H (-1 / 2) - (t : ℂ)⁻¹ * ∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), E x * g' x‖
        ≤ ‖H (1 / 2) - H (-1 / 2)‖ + ‖(t : ℂ)⁻¹ * ∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), E x * g' x‖ :=
          norm_sub_le _ _
      _ ≤ (‖H (1 / 2)‖ + ‖H (-1 / 2)‖) +
            ‖(t : ℂ)⁻¹ * ∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ), E x * g' x‖ :=
          add_le_add (norm_sub_le _ _) le_rfl
      _ ≤ (M₀ / t + M₀ / t) + M₁ / t :=
          add_le_add (add_le_add hH_half hH_mhalf) hrem_norm
      _ = (2 * M₀ + M₁) / t := by ring
      _ ≤ C_H / (t + 1) := by
          rw [div_le_div_iff₀ ht_pos (by linarith)]
          dsimp [C_H]; nlinarith

/-- **Pointwise exponential left-edge decay and `O(1 / (t + 1))` left-port bound.**
On any boundary-regular centered window, `‖ℱ_left(t)‖ ≤ C_L e^{-t}` and
`‖𝒫_-(t)‖ ≤ C_L / (t + 1)` for all `t ≥ 0`. -/
theorem exists_leftEdge_and_leftHalfPort_decay {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) (N : ℕ)
    (hbdry : ∀ τ : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath
        (centeredWindowLowerLeft y₁) (centeredWindowUpperRight y₂) τ) ≠ 0) :
    ∃ C_L : ℝ, 0 < C_L ∧ ∀ t : ℝ, 0 ≤ t →
      ‖leftEdgeFlux y₁ y₂ N t‖ ≤ C_L * Real.exp (-t) ∧
      ‖leftHalfPort y₁ y₂ N t‖ ≤ C_L / (t + 1) := by
  have hnz_v : ∀ y ∈ Icc y₁ y₂,
      _root_.RHTower.finiteThetaAmplitude N (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro y hy_mem
    refine edge_ne_zero_of_bdry_regular hy hbdry ⟨by simp, by simp; norm_num⟩
      ⟨by simpa using hy_mem.1, by simpa using hy_mem.2⟩ (Or.inl (by simp))
  have hnz_h1 : ∀ x ∈ Icc (-1 / 2 : ℝ) (1 / 2 : ℝ),
      _root_.RHTower.finiteThetaAmplitude N ((x : ℂ) + (y₁ : ℂ) * I) ≠ 0 := by
    intro x hx
    refine edge_ne_zero_of_bdry_regular hy hbdry ⟨by simpa using hx.1, by simp; linarith [hx.2]⟩
      ⟨by simp, by simpa using hy⟩ (Or.inr (Or.inr (Or.inl (by simp))))
  have hnz_h2 : ∀ x ∈ Icc (-1 / 2 : ℝ) (1 / 2 : ℝ),
      _root_.RHTower.finiteThetaAmplitude N ((x : ℂ) + (y₂ : ℂ) * I) ≠ 0 := by
    intro x hx
    refine edge_ne_zero_of_bdry_regular hy hbdry ⟨by simpa using hx.1, by simp; linarith [hx.2]⟩
      ⟨by simpa using hy, by simp⟩ (Or.inr (Or.inr (Or.inr (by simp))))
  have hv_cont : ContinuousOn
      (fun y : ℝ => thetaLogDeriv N (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)) (Icc y₁ y₂) :=
    fun y hy_mem => continuousWithinAt_comp_line (by fun_prop)
      (analyticAt_thetaLogDeriv (hnz_v y hy_mem))
  obtain ⟨M_v, hMv_bd⟩ := isCompact_Icc.exists_bound_of_continuousOn hv_cont
  have hMv_nn : 0 ≤ M_v := (norm_nonneg _).trans (hMv_bd y₁ ⟨le_rfl, hy⟩)
  obtain ⟨C₁, hC₁_pos, hC₁_bd⟩ := exists_norm_left_horiz_integral_le hnz_h1
  obtain ⟨C₂, hC₂_pos, hC₂_bd⟩ := exists_norm_left_horiz_integral_le hnz_h2
  let C_v : ℝ := (M_v * (y₂ - y₁) + 1) / (2 * Real.pi)
  have hCv_pos : 0 < C_v := by dsimp [C_v]; have : 0 ≤ y₂ - y₁ := sub_nonneg.mpr hy; positivity
  let C_L : ℝ := C_v + (C₁ + C₂) / (2 * Real.pi)
  refine ⟨C_L, by dsimp [C_L]; positivity, fun t ht => ?_⟩
  have hleft_le : ‖leftEdgeFlux y₁ y₂ N t‖ ≤ C_v * Real.exp (-t) := by
    unfold leftEdgeFlux vertFlux
    rw [norm_neg, norm_mul, norm_inv, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
    have hb : ∀ y ∈ Icc y₁ y₂,
        ‖cexp ((t : ℂ) * ((((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) - 1 / 2)) *
          thetaLogDeriv N (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤ M_v * Real.exp (-t) := by
      intro y hy_cc
      rw [norm_mul, Complex.norm_exp]
      have hre : ((t : ℂ) * ((((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) - 1 / 2)).re = -t := by
        simp [Complex.mul_re, Complex.sub_re]; ring
      rw [hre, mul_comm M_v]
      exact mul_le_mul_of_nonneg_left (hMv_bd y hy_cc) (Real.exp_pos _).le
    have hint := intervalIntegral.norm_integral_le_of_norm_le_const' hy hb
    rw [abs_of_nonneg (sub_nonneg.mpr hy)] at hint
    calc (2 * Real.pi)⁻¹ * ‖∫ y in y₁..y₂,
            cexp ((t : ℂ) * ((((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I) - 1 / 2)) *
              thetaLogDeriv N (((-1 / 2 : ℝ) : ℂ) + (y : ℂ) * I)‖
        ≤ (2 * Real.pi)⁻¹ * ((M_v * Real.exp (-t)) * (y₂ - y₁)) :=
          mul_le_mul_of_nonneg_left hint (by positivity)
      _ ≤ C_v * Real.exp (-t) := by
          dsimp [C_v]
          rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
          have hexp_pos : 0 < Real.exp (-t) := Real.exp_pos _
          have : (2 * Real.pi)⁻¹ * (M_v * Real.exp (-t) * (y₂ - y₁)) * (2 * Real.pi) =
              M_v * (y₂ - y₁) * Real.exp (-t) := by field_simp [Real.pi_ne_zero]
          nlinarith
  have hexp_inv : Real.exp (-t) ≤ 1 / (t + 1) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by linarith) (by linarith [Real.add_one_le_exp t])
  refine ⟨hleft_le.trans (mul_le_mul_of_nonneg_right
    (le_add_of_nonneg_right (by positivity)) (Real.exp_pos _).le), ?_⟩
  unfold leftHalfPort horizCapFlux
  have hpre_norm : ‖(2 * Real.pi * I)⁻¹‖ = (2 * Real.pi)⁻¹ := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le, norm_I, mul_one]
  have hcap_le : ‖(2 * Real.pi * I)⁻¹ *
      ((∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
          cexp ((t : ℂ) * (((x : ℂ) + (y₁ : ℂ) * I) - 1 / 2)) *
            thetaLogDeriv N ((x : ℂ) + (y₁ : ℂ) * I)) -
        (∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
          cexp ((t : ℂ) * (((x : ℂ) + (y₂ : ℂ) * I) - 1 / 2)) *
            thetaLogDeriv N ((x : ℂ) + (y₂ : ℂ) * I)))‖ ≤
      ((C₁ + C₂) / (2 * Real.pi)) / (t + 1) := by
    rw [norm_mul, hpre_norm]
    have hsub := (norm_sub_le _ _).trans (add_le_add (hC₁_bd t ht) (hC₂_bd t ht))
    calc (2 * Real.pi)⁻¹ *
            ‖(∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
                cexp ((t : ℂ) * (((x : ℂ) + (y₁ : ℂ) * I) - 1 / 2)) *
                  thetaLogDeriv N ((x : ℂ) + (y₁ : ℂ) * I)) -
              (∫ x in (-1 / 2 : ℝ)..(1 / 2 : ℝ),
                cexp ((t : ℂ) * (((x : ℂ) + (y₂ : ℂ) * I) - 1 / 2)) *
                  thetaLogDeriv N ((x : ℂ) + (y₂ : ℂ) * I))‖
        ≤ (2 * Real.pi)⁻¹ * (C₁ / (t + 1) + C₂ / (t + 1)) :=
          mul_le_mul_of_nonneg_left hsub (by positivity)
      _ = ((C₁ + C₂) / (2 * Real.pi)) / (t + 1) := by ring
  calc ‖leftEdgeFlux y₁ y₂ N t + _‖
      ≤ ‖leftEdgeFlux y₁ y₂ N t‖ + ‖_‖ := norm_add_le _ _
    _ ≤ C_v * Real.exp (-t) + ((C₁ + C₂) / (2 * Real.pi)) / (t + 1) :=
        add_le_add hleft_le hcap_le
    _ ≤ C_v * (1 / (t + 1)) + ((C₁ + C₂) / (2 * Real.pi)) / (t + 1) :=
        add_le_add (mul_le_mul_of_nonneg_left hexp_inv hCv_pos.le) le_rfl
    _ = C_L / (t + 1) := by dsimp [C_L]; ring

private lemma continuous_leftHalfPort {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) (N : ℕ)
    (hbdry : ∀ τ : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath
        (centeredWindowLowerLeft y₁) (centeredWindowUpperRight y₂) τ) ≠ 0) :
    Continuous (leftHalfPort y₁ y₂ N) := by
  unfold leftHalfPort leftEdgeFlux
  refine (continuous_vertFlux_of_ne_zero hy ?_).neg.add
    (continuous_horizCapFlux_of_ne_zero (by norm_num) ?_ ?_)
  · intro y hy_mem
    exact edge_ne_zero_of_bdry_regular hy hbdry ⟨by simp, by simp; norm_num⟩
      ⟨by simpa using hy_mem.1, by simpa using hy_mem.2⟩ (Or.inl (by simp))
  · intro x hx
    exact edge_ne_zero_of_bdry_regular hy hbdry ⟨by simpa using hx.1, by simp; linarith [hx.2]⟩
      ⟨by simp, by simpa using hy⟩ (Or.inr (Or.inr (Or.inl (by simp))))
  · intro x hx
    exact edge_ne_zero_of_bdry_regular hy hbdry ⟨by simpa using hx.1, by simp; linarith [hx.2]⟩
      ⟨by simpa using hy, by simp⟩ (Or.inr (Or.inr (Or.inr (by simp))))

/-- **Unconditional unweighted `L²(0, ∞)` integrability of the left half-window port.** -/
theorem integrableOn_leftHalfPort_sq {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) (N : ℕ)
    (hbdry : ∀ τ : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath
        (centeredWindowLowerLeft y₁) (centeredWindowUpperRight y₂) τ) ≠ 0) :
    IntegrableOn (fun t : ℝ => ‖leftHalfPort y₁ y₂ N t‖ ^ 2) (Ioi (0 : ℝ)) := by
  obtain ⟨C_L, hC_L, hbd⟩ := exists_leftEdge_and_leftHalfPort_decay hy N hbdry
  have hcont_left := continuous_leftHalfPort hy N hbdry
  have hdom : IntegrableOn (fun t : ℝ => C_L ^ 2 * (t + 1) ^ (-2 : ℝ)) (Ioi (0 : ℝ)) :=
    (integrableOn_add_rpow_Ioi_of_lt (a := -2) (c := 0) (m := 1) (by norm_num)
      (by norm_num)).const_mul _
  refine hdom.mono' (hcont_left.norm.pow 2).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
  have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
  have ht1 : 0 < t + 1 := by linarith
  have hsq : ‖leftHalfPort y₁ y₂ N t‖ ^ 2 ≤ (C_L / (t + 1)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (hbd t ht0).2 2
  have hrpow : (C_L / (t + 1)) ^ 2 = C_L ^ 2 * (t + 1) ^ (-2 : ℝ) := by
    rw [div_pow, div_eq_mul_inv,
      show (-2 : ℝ) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg ht1.le, Real.rpow_natCast]
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← hrpow]
  exact hsq

private lemma norm_add_sq_le_two_mul_add (u v : ℂ) :
    ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have h1 : ‖u + v‖ ^ 2 ≤ (‖u‖ + ‖v‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) (norm_add_le u v) 2
  have h2 : 0 ≤ (‖u‖ - ‖v‖) ^ 2 := sq_nonneg _
  nlinarith

/-- **Pure right-port Laplace equivalence.** For every `x ≥ 0`, Laplace-weighted energy
integrability of `centeredThetaExpSum` on `(0, ∞)` is unconditionally equivalent to Laplace-weighted
energy integrability of the pure right half-window port `rightHalfPort`. -/
theorem integrableOn_windowEnergy_iff_rightHalfPort {y₁ y₂ : ℝ} (hy : y₁ ≤ y₂) (N : ℕ)
    (hbdry : ∀ τ : ℝ, _root_.RHTower.finiteThetaAmplitude N
      (_root_.RHTower.rectangleBoundaryPath
        (centeredWindowLowerLeft y₁) (centeredWindowUpperRight y₂) τ) ≠ 0)
    {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun t : ℝ => Real.exp (-(x * t)) * ‖centeredThetaExpSum y₁ y₂ N t‖ ^ 2)
      (Ioi (0 : ℝ)) ↔
    IntegrableOn (fun t : ℝ => Real.exp (-(x * t)) * ‖rightHalfPort y₁ y₂ N t‖ ^ 2)
      (Ioi (0 : ℝ)) := by
  have hleft_L2 := integrableOn_leftHalfPort_sq hy N hbdry
  have hcont_left := continuous_leftHalfPort hy N hbdry
  have hcont_right : Continuous (rightHalfPort y₁ y₂ N) := by
    unfold rightHalfPort rightEdgeFlux
    refine (continuous_vertFlux_of_ne_zero hy ?_).add
      (continuous_horizCapFlux_of_ne_zero (by norm_num) ?_ ?_)
    · intro y hy_mem
      exact edge_ne_zero_of_bdry_regular hy hbdry ⟨by simp; norm_num, by simp⟩
        ⟨by simpa using hy_mem.1, by simpa using hy_mem.2⟩ (Or.inr (Or.inl (by simp)))
    · intro u hu
      exact edge_ne_zero_of_bdry_regular hy hbdry ⟨by simp; linarith [hu.1], by simpa using hu.2⟩
        ⟨by simp, by simpa using hy⟩ (Or.inr (Or.inr (Or.inl (by simp))))
    · intro u hu
      exact edge_ne_zero_of_bdry_regular hy hbdry ⟨by simp; linarith [hu.1], by simpa using hu.2⟩
        ⟨by simpa using hy, by simp⟩ (Or.inr (Or.inr (Or.inr (by simp))))
  have hcont_Z : Continuous (centeredThetaExpSum y₁ y₂ N) := by
    have heq : centeredThetaExpSum y₁ y₂ N =
        fun t => (centeredThetaWindow hy N hbdry).expSum t := by
      funext t; exact (centeredThetaWindow_expSum hy N hbdry t).symm
    rw [heq]
    exact (centeredThetaWindow hy N hbdry).continuous_expSum
  have hleft_wt : IntegrableOn
      (fun t : ℝ => Real.exp (-(x * t)) * ‖leftHalfPort y₁ y₂ N t‖ ^ 2) (Ioi (0 : ℝ)) := by
    refine hleft_L2.mono'
      (((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
        (hcont_left.norm.pow 2)).aestronglyMeasurable) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 ≤ t := (mem_Ioi.mp ht).le
      have hexp1 : Real.exp (-(x * t)) ≤ 1 :=
        Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hx ht0))
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
      calc Real.exp (-(x * t)) * ‖leftHalfPort y₁ y₂ N t‖ ^ 2
          ≤ 1 * ‖leftHalfPort y₁ y₂ N t‖ ^ 2 :=
            mul_le_mul_of_nonneg_right hexp1 (sq_nonneg _)
        _ = ‖leftHalfPort y₁ y₂ N t‖ ^ 2 := one_mul _
  constructor
  · intro hZ
    have hdom := (hZ.const_mul 2).add (hleft_wt.const_mul 2)
    refine hdom.mono'
      (((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
        (hcont_right.norm.pow 2)).aestronglyMeasurable) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t _ => ?_
    have hdecomp := centeredThetaExpSum_eq_rightHalfPort_add_leftHalfPort hy N hbdry t
    have hrw : rightHalfPort y₁ y₂ N t =
        centeredThetaExpSum y₁ y₂ N t + (-leftHalfPort y₁ y₂ N t) := by
      linear_combination -hdecomp
    have hsq : ‖rightHalfPort y₁ y₂ N t‖ ^ 2 ≤
        2 * ‖centeredThetaExpSum y₁ y₂ N t‖ ^ 2 + 2 * ‖leftHalfPort y₁ y₂ N t‖ ^ 2 := by
      rw [hrw]
      simpa only [norm_neg] using
        norm_add_sq_le_two_mul_add (centeredThetaExpSum y₁ y₂ N t) (-leftHalfPort y₁ y₂ N t)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    calc Real.exp (-(x * t)) * ‖rightHalfPort y₁ y₂ N t‖ ^ 2
        ≤ Real.exp (-(x * t)) *
            (2 * ‖centeredThetaExpSum y₁ y₂ N t‖ ^ 2 + 2 * ‖leftHalfPort y₁ y₂ N t‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
      _ = 2 * (Real.exp (-(x * t)) * ‖centeredThetaExpSum y₁ y₂ N t‖ ^ 2) +
            2 * (Real.exp (-(x * t)) * ‖leftHalfPort y₁ y₂ N t‖ ^ 2) := by ring
  · intro hR
    have hdom := (hR.const_mul 2).add (hleft_wt.const_mul 2)
    refine hdom.mono'
      (((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
        (hcont_Z.norm.pow 2)).aestronglyMeasurable) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t _ => ?_
    have hdecomp := centeredThetaExpSum_eq_rightHalfPort_add_leftHalfPort hy N hbdry t
    have hsq : ‖centeredThetaExpSum y₁ y₂ N t‖ ^ 2 ≤
        2 * ‖rightHalfPort y₁ y₂ N t‖ ^ 2 + 2 * ‖leftHalfPort y₁ y₂ N t‖ ^ 2 := by
      rw [hdecomp]
      exact norm_add_sq_le_two_mul_add _ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
    calc Real.exp (-(x * t)) * ‖centeredThetaExpSum y₁ y₂ N t‖ ^ 2
        ≤ Real.exp (-(x * t)) *
            (2 * ‖rightHalfPort y₁ y₂ N t‖ ^ 2 + 2 * ‖leftHalfPort y₁ y₂ N t‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
      _ = 2 * (Real.exp (-(x * t)) * ‖rightHalfPort y₁ y₂ N t‖ ^ 2) +
            2 * (Real.exp (-(x * t)) * ‖leftHalfPort y₁ y₂ N t‖ ^ 2) := by ring


/-! ## §3 Periodic mean-square orthogonality and twice-IBP lower bound -/

/-- Exact periodic mean-square identity over one period `P = 2π / (y₂ - y₁)`:
`∫_T^{T+P} ‖e^{ity₂} w₂ - e^{ity₁} w₁‖² dt = P (‖w₁‖² + ‖w₂‖²)`. -/
theorem periodic_endpoint_mean_sq {y₁ y₂ : ℝ} (hy : y₁ < y₂) (w₁ w₂ : ℂ) (T : ℝ) :
    ∫ t in T..(T + 2 * Real.pi / (y₂ - y₁)),
        ‖cexp ((t : ℂ) * (y₂ : ℂ) * I) * w₂ - cexp ((t : ℂ) * (y₁ : ℂ) * I) * w₁‖ ^ 2 =
      (2 * Real.pi / (y₂ - y₁)) * (‖w₁‖ ^ 2 + ‖w₂‖ ^ 2) := by
  set Δ : ℝ := y₂ - y₁ with hΔ_def
  have hΔ_pos : 0 < Δ := sub_pos.mpr hy
  set P : ℝ := 2 * Real.pi / Δ with hP_def
  have hΔC : (Δ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hΔ_pos.ne'
  set u : ℝ → ℂ := fun t => cexp ((t : ℂ) * (y₂ : ℂ) * I) * w₂ with hu_def
  set v : ℝ → ℂ := fun t => cexp ((t : ℂ) * (y₁ : ℂ) * I) * w₁ with hv_def
  have hnorm_u : ∀ t : ℝ, ‖u t‖ = ‖w₂‖ := fun t => by
    dsimp only [u]
    rw [norm_mul, Complex.norm_exp]
    have : ((t : ℂ) * (y₂ : ℂ) * I).re = 0 := by simp
    rw [this, Real.exp_zero, one_mul]
  have hnorm_v : ∀ t : ℝ, ‖v t‖ = ‖w₁‖ := fun t => by
    dsimp only [v]
    rw [norm_mul, Complex.norm_exp]
    have : ((t : ℂ) * (y₁ : ℂ) * I).re = 0 := by simp
    rw [this, Real.exp_zero, one_mul]
  have hcross : ∀ t : ℝ, u t * star (v t) =
      (w₂ * star w₁) * cexp ((t : ℂ) * (Δ : ℂ) * I) := fun t => by
    dsimp only [u, v]
    rw [star_mul']
    have hcexp_star : star (cexp ((t : ℂ) * (y₁ : ℂ) * I)) =
        cexp (-((t : ℂ) * (y₁ : ℂ) * I)) := by
      rw [Complex.star_def, ← Complex.exp_conj]
      congr 1
      simp [map_mul, Complex.conj_ofReal, Complex.conj_I]
    rw [hcexp_star]
    calc (cexp ((t : ℂ) * (y₂ : ℂ) * I) * w₂) * (cexp (-((t : ℂ) * (y₁ : ℂ) * I)) * star w₁)
        = (w₂ * star w₁) *
            (cexp ((t : ℂ) * (y₂ : ℂ) * I) * cexp (-((t : ℂ) * (y₁ : ℂ) * I))) := by ring
      _ = (w₂ * star w₁) * cexp ((t : ℂ) * (Δ : ℂ) * I) := by
          rw [← Complex.exp_add]
          congr 2
          rw [hΔ_def]; push_cast; ring
  have hre_add_star : ∀ z : ℂ, (z + star z).re = 2 * z.re := fun z => by
    rw [Complex.add_re, Complex.star_def, Complex.conj_re]; ring
  have hsq_exp : ∀ t : ℝ, ‖u t - v t‖ ^ 2 =
      (‖w₁‖ ^ 2 + ‖w₂‖ ^ 2) - 2 * ((w₂ * star w₁) * cexp ((t : ℂ) * (Δ : ℂ) * I)).re := by
    intro t
    have hc : ((‖u t - v t‖ ^ 2 : ℝ) : ℂ) =
        ((‖u t‖ ^ 2 : ℝ) : ℂ) + ((‖v t‖ ^ 2 : ℝ) : ℂ) -
          (u t * star (v t) + star (u t * star (v t))) := by
      simp only [Complex.ofReal_pow, ← Complex.mul_conj', ← Complex.star_def,
        star_sub, star_mul', star_star]
      ring
    rw [hnorm_u t, hnorm_v t, hcross t] at hc
    have hre := congrArg Complex.re hc
    simp only [Complex.ofReal_re, Complex.sub_re, Complex.add_re, hre_add_star] at hre
    linarith
  have hosc_zero : ∫ t in T..(T + P), cexp ((t : ℂ) * (Δ : ℂ) * I) = 0 := by
    set F : ℝ → ℂ := fun t => ((Δ : ℂ) * I)⁻¹ * cexp ((t : ℂ) * (Δ : ℂ) * I) with hF_def
    have hd : ∀ t ∈ uIcc T (T + P), HasDerivAt F (cexp ((t : ℂ) * (Δ : ℂ) * I)) t := by
      intro t _
      have hw : HasDerivAt (fun w : ℂ => cexp (w * (Δ : ℂ) * I))
          (cexp ((t : ℂ) * (Δ : ℂ) * I) * ((Δ : ℂ) * I)) (t : ℂ) := by
        have hlin : HasDerivAt (fun w : ℂ => w * (Δ : ℂ) * I) ((Δ : ℂ) * I) (t : ℂ) := by
          simpa [mul_assoc] using (hasDerivAt_id (t : ℂ)).mul_const ((Δ : ℂ) * I)
        exact hlin.cexp
      exact ((hw.comp_ofReal).const_mul (((Δ : ℂ) * I)⁻¹)).congr_deriv (by
        field_simp [hΔC, I_ne_zero])
    have hint : IntervalIntegrable (fun t : ℝ => cexp ((t : ℂ) * (Δ : ℂ) * I)) volume T (T + P) :=
      (by fun_prop : Continuous fun t : ℝ => cexp ((t : ℂ) * (Δ : ℂ) * I)).intervalIntegrable _ _
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
    dsimp only [F]
    have hper : ((T + P : ℝ) : ℂ) * (Δ : ℂ) * I =
        (T : ℂ) * (Δ : ℂ) * I + 2 * Real.pi * I := by
      rw [hP_def]
      push_cast
      field_simp [hΔC]
    rw [hper, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one, sub_self]
  have hre_zero : ∫ t in T..(T + P),
      2 * ((w₂ * star w₁) * cexp ((t : ℂ) * (Δ : ℂ) * I)).re = 0 := by
    rw [intervalIntegral.integral_const_mul]
    have hcomm := Complex.reCLM.intervalIntegral_comp_comm
      ((by fun_prop : Continuous fun t : ℝ =>
        (w₂ * star w₁) * cexp ((t : ℂ) * (Δ : ℂ) * I)).intervalIntegrable T (T + P))
    change 2 * (∫ t in T..(T + P), Complex.reCLM ((w₂ * star w₁) * cexp ((t : ℂ) * (Δ : ℂ) * I))) = 0
    rw [hcomm, intervalIntegral.integral_const_mul, hosc_zero, mul_zero,
      Complex.reCLM_apply, Complex.zero_re, mul_zero]
  rw [intervalIntegral.integral_congr fun t _ => hsq_exp t,
    intervalIntegral.integral_sub intervalIntegrable_const
      ((by fun_prop : Continuous fun t : ℝ =>
        2 * ((w₂ * star w₁) * cexp ((t : ℂ) * (Δ : ℂ) * I)).re).intervalIntegrable _ _),
    hre_zero, sub_zero, intervalIntegral.integral_const, smul_eq_mul]
  ring

theorem exists_periodic_oscillation_ge {y₁ y₂ : ℝ} (hy : y₁ < y₂) (w₁ w₂ : ℂ) (T : ℝ) :
    ∃ t ∈ Icc T (T + 2 * Real.pi / (y₂ - y₁)),
      Real.sqrt (‖w₁‖ ^ 2 + ‖w₂‖ ^ 2) ≤
        ‖cexp ((t : ℂ) * (y₂ : ℂ) * I) * w₂ - cexp ((t : ℂ) * (y₁ : ℂ) * I) * w₁‖ := by
  set P : ℝ := 2 * Real.pi / (y₂ - y₁)
  have hP_pos : 0 < P := div_pos (by positivity) (sub_pos.mpr hy)
  set B : ℝ → ℝ := fun t =>
    ‖cexp ((t : ℂ) * (y₂ : ℂ) * I) * w₂ - cexp ((t : ℂ) * (y₁ : ℂ) * I) * w₁‖ ^ 2
  have hB_cont : Continuous B := by dsimp [B]; fun_prop
  have hne : (Icc T (T + P)).Nonempty := ⟨T, left_mem_Icc.mpr (by linarith)⟩
  obtain ⟨t₀, ht₀_mem, ht₀_max⟩ := isCompact_Icc.exists_isMaxOn hne hB_cont.continuousOn
  refine ⟨t₀, ht₀_mem, ?_⟩
  have hmean := periodic_endpoint_mean_sq hy w₁ w₂ T
  have hint_le : ∫ t in T..(T + P), B t ≤ B t₀ * ((T + P) - T) := by
    refine intervalIntegral.integral_mono_on (by linarith)
      (hB_cont.intervalIntegrable _ _) intervalIntegrable_const (fun t ht => ht₀_max ht)
      |>.trans ?_
    rw [intervalIntegral.integral_const, smul_eq_mul]
    linarith
  have hle_Bt₀ : ‖w₁‖ ^ 2 + ‖w₂‖ ^ 2 ≤ B t₀ := by
    have : P * (‖w₁‖ ^ 2 + ‖w₂‖ ^ 2) ≤ P * B t₀ := by linarith [hmean, hint_le]
    exact le_of_mul_le_mul_left this hP_pos
  have hsqrt := Real.sqrt_le_sqrt hle_Bt₀
  dsimp [B] at hsqrt
  rwa [Real.sqrt_sq (norm_nonneg _)] at hsqrt

/-- Twice-IBP oscillatory integral lower bound over every period `[T, T + 2π / (y₂ - y₁)]`. -/
theorem exists_oscillatory_integral_ge_div_t {y₁ y₂ : ℝ} (hy : y₁ < y₂)
    {f f' f'' : ℝ → ℂ}
    (hf1 : ∀ y ∈ Icc y₁ y₂, HasDerivAt f (f' y) y)
    (hf2 : ∀ y ∈ Icc y₁ y₂, HasDerivAt f' (f'' y) y)
    (hf''_cont : ContinuousOn f'' (Icc y₁ y₂))
    (hnz : 0 < ‖f y₁‖ ^ 2 + ‖f y₂‖ ^ 2) :
    ∃ μ T₀ : ℝ, 0 < μ ∧ 1 ≤ T₀ ∧
      ∀ T : ℝ, T₀ ≤ T →
        ∃ t ∈ Icc T (T + 2 * Real.pi / (y₂ - y₁)),
          μ / t ≤ ‖∫ y in y₁..y₂, cexp ((t : ℂ) * (y : ℂ) * I) * f y‖ := by
  set μ : ℝ := Real.sqrt (‖f y₁‖ ^ 2 + ‖f y₂‖ ^ 2) / 2
  have hμ_pos : 0 < μ := div_pos (Real.sqrt_pos.mpr hnz) zero_lt_two
  obtain ⟨M₂, hM₂_bd⟩ := isCompact_Icc.exists_bound_of_continuousOn hf''_cont
  have hM₂_nn : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂_bd y₁ ⟨le_rfl, hy.le⟩)
  let R₂ : ℝ := ‖f' y₂‖ + ‖f' y₁‖ + M₂ * (y₂ - y₁)
  have hR₂_nn : 0 ≤ R₂ := by dsimp [R₂]; have : 0 ≤ y₂ - y₁ := sub_nonneg.mpr hy.le; positivity
  let T₀ : ℝ := max 1 (R₂ / μ + 1)
  refine ⟨μ, T₀, hμ_pos, le_max_left 1 _, fun T hT => ?_⟩
  obtain ⟨t, ht_mem, ht_osc⟩ := exists_periodic_oscillation_ge hy (f y₁) (f y₂) T
  refine ⟨t, ht_mem, ?_⟩
  have hT1 : 1 ≤ T := (le_max_left 1 _).trans hT
  have hTR : R₂ / μ + 1 ≤ T := (le_max_right 1 _).trans hT
  have ht_ge_T : T ≤ t := ht_mem.1
  have ht_pos : 0 < t := by linarith
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht_pos.ne'
  set E : ℝ → ℂ := fun y => cexp ((t : ℂ) * (y : ℂ) * I) with hE_def
  set L : ℝ → ℂ := fun y => (I * (t : ℂ))⁻¹ * f y + ((t : ℂ) ^ 2)⁻¹ * f' y with hL_def
  set G : ℝ → ℂ := fun y => L y * E y with hG_def
  have hf_cont : ContinuousOn f (Icc y₁ y₂) :=
    fun y hy_m => (hf1 y hy_m).continuousAt.continuousWithinAt
  have hf'_cont : ContinuousOn f' (Icc y₁ y₂) :=
    fun y hy_m => (hf2 y hy_m).continuousAt.continuousWithinAt
  have hG_deriv : ∀ y ∈ uIcc y₁ y₂,
      HasDerivAt G (E y * f y + ((t : ℂ) ^ 2)⁻¹ * (E y * f'' y)) y := by
    rw [uIcc_of_le hy.le]
    intro y hy_m
    have hE_d : HasDerivAt E ((t : ℂ) * I * E y) y := by
      have hw : HasDerivAt (fun w : ℂ => cexp ((t : ℂ) * w * I))
          (cexp ((t : ℂ) * (y : ℂ) * I) * ((t : ℂ) * I)) (y : ℂ) := by
        have hlin : HasDerivAt (fun w : ℂ => (t : ℂ) * w * I) ((t : ℂ) * I) (y : ℂ) := by
          simpa [mul_assoc] using ((hasDerivAt_id (y : ℂ)).const_mul (t : ℂ)).mul_const I
        exact hlin.cexp
      exact (hw.comp_ofReal).congr_deriv (by rw [hE_def]; ring)
    have hL_d : HasDerivAt L ((I * (t : ℂ))⁻¹ * f' y + ((t : ℂ) ^ 2)⁻¹ * f'' y) y :=
      HasDerivAt.add ((hf1 y hy_m).const_mul (I * (t : ℂ))⁻¹)
        ((hf2 y hy_m).const_mul (((t : ℂ) ^ 2)⁻¹))
    refine (hL_d.mul hE_d).congr_deriv ?_
    have hc1 : (I * (t : ℂ))⁻¹ * ((t : ℂ) * I) = 1 := by
      rw [mul_comm (t : ℂ) I]
      exact inv_mul_cancel₀ (mul_ne_zero I_ne_zero htC)
    have hc2 : (I * (t : ℂ))⁻¹ + ((t : ℂ) ^ 2)⁻¹ * ((t : ℂ) * I) = 0 := by
      apply mul_right_cancel₀ (mul_ne_zero I_ne_zero (pow_ne_zero 2 htC))
      rw [zero_mul]
      have h1 : (I * (t : ℂ))⁻¹ * (I * (t : ℂ)) = 1 :=
        inv_mul_cancel₀ (mul_ne_zero I_ne_zero htC)
      have h2 : ((t : ℂ) ^ 2)⁻¹ * (t : ℂ) ^ 2 = 1 :=
        inv_mul_cancel₀ (pow_ne_zero 2 htC)
      calc ((I * (t : ℂ))⁻¹ + ((t : ℂ) ^ 2)⁻¹ * ((t : ℂ) * I)) * (I * (t : ℂ) ^ 2)
          = ((I * (t : ℂ))⁻¹ * (I * (t : ℂ))) * (t : ℂ) +
              (((t : ℂ) ^ 2)⁻¹ * (t : ℂ) ^ 2) * (t : ℂ) * I ^ 2 := by ring
        _ = 0 := by rw [h1, h2, Complex.I_sq]; ring
    dsimp only [L]
    calc (((I * (t : ℂ))⁻¹ * f' y + ((t : ℂ) ^ 2)⁻¹ * f'' y) * E y +
            ((I * (t : ℂ))⁻¹ * f y + ((t : ℂ) ^ 2)⁻¹ * f' y) * ((t : ℂ) * I * E y))
        = ((I * (t : ℂ))⁻¹ * ((t : ℂ) * I)) * (E y * f y) +
            ((I * (t : ℂ))⁻¹ + ((t : ℂ) ^ 2)⁻¹ * ((t : ℂ) * I)) * (f' y * E y) +
            ((t : ℂ) ^ 2)⁻¹ * (E y * f'' y) := by ring
      _ = E y * f y + ((t : ℂ) ^ 2)⁻¹ * (E y * f'' y) := by rw [hc1, hc2]; ring
  have hi1 : IntervalIntegrable (fun y => E y * f y) volume y₁ y₂ :=
    (ContinuousOn.mul (by fun_prop) hf_cont).intervalIntegrable_of_Icc hy.le
  have hi2 : IntervalIntegrable (fun y => ((t : ℂ) ^ 2)⁻¹ * (E y * f'' y)) volume y₁ y₂ :=
    ((ContinuousOn.mul (by fun_prop) hf''_cont).const_smul
      (((t : ℂ) ^ 2)⁻¹)).intervalIntegrable_of_Icc hy.le
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hG_deriv (hi1.add hi2)
  rw [intervalIntegral.integral_add hi1 hi2, intervalIntegral.integral_const_mul] at hftc
  have hibp2 : (∫ y in y₁..y₂, E y * f y) =
      (I * (t : ℂ))⁻¹ * (E y₂ * f y₂ - E y₁ * f y₁) +
        ((t : ℂ) ^ 2)⁻¹ * (E y₂ * f' y₂ - E y₁ * f' y₁ - ∫ y in y₁..y₂, E y * f'' y) := by
    have hsub : G y₂ - G y₁ - ((t : ℂ) ^ 2)⁻¹ * (∫ y in y₁..y₂, E y * f'' y) =
        (I * (t : ℂ))⁻¹ * (E y₂ * f y₂ - E y₁ * f y₁) +
          ((t : ℂ) ^ 2)⁻¹ * (E y₂ * f' y₂ - E y₁ * f' y₁ - ∫ y in y₁..y₂, E y * f'' y) := by
      dsimp only [G, L]; ring
    rw [← hsub]
    linear_combination hftc
  have hnorm_E : ∀ y : ℝ, ‖E y‖ = 1 := fun y => by
    dsimp only [E]
    rw [Complex.norm_exp]
    have : ((t : ℂ) * (y : ℂ) * I).re = 0 := by simp
    rw [this, Real.exp_zero]
  have hmain_ge : 2 * μ / t ≤ ‖(I * (t : ℂ))⁻¹ * (E y₂ * f y₂ - E y₁ * f y₁)‖ := by
    rw [norm_mul, norm_inv, norm_mul, norm_I, one_mul, Complex.norm_real,
      Real.norm_of_nonneg ht_pos.le, div_eq_mul_inv, mul_comm (2 * μ)]
    have h2μ : 2 * μ = Real.sqrt (‖f y₁‖ ^ 2 + ‖f y₂‖ ^ 2) := by dsimp [μ]; ring
    rw [h2μ]
    exact mul_le_mul_of_nonneg_left ht_osc (inv_nonneg.mpr ht_pos.le)
  have hrem_le :
      ‖((t : ℂ) ^ 2)⁻¹ * (E y₂ * f' y₂ - E y₁ * f' y₁ - ∫ y in y₁..y₂, E y * f'' y)‖ ≤
        R₂ / t ^ 2 := by
    rw [norm_mul, norm_inv, norm_pow, Complex.norm_real, Real.norm_of_nonneg ht_pos.le,
      div_eq_inv_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hint_f'' : ‖∫ y in y₁..y₂, E y * f'' y‖ ≤ M₂ * (y₂ - y₁) := by
      have hbd_int : ‖∫ y in y₁..y₂, E y * f'' y‖ ≤ M₂ * |y₂ - y₁| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const' hy.le fun y hy_cc => ?_
        rw [norm_mul, hnorm_E y, one_mul]
        exact hM₂_bd y hy_cc
      rwa [abs_of_nonneg (sub_nonneg.mpr hy.le)] at hbd_int
    have he2 : ‖E y₂ * f' y₂‖ = ‖f' y₂‖ := by rw [norm_mul, hnorm_E y₂, one_mul]
    have he1 : ‖E y₁ * f' y₁‖ = ‖f' y₁‖ := by rw [norm_mul, hnorm_E y₁, one_mul]
    calc ‖E y₂ * f' y₂ - E y₁ * f' y₁ - ∫ y in y₁..y₂, E y * f'' y‖
        ≤ ‖E y₂ * f' y₂ - E y₁ * f' y₁‖ + ‖∫ y in y₁..y₂, E y * f'' y‖ := norm_sub_le _ _
      _ ≤ (‖E y₂ * f' y₂‖ + ‖E y₁ * f' y₁‖) + M₂ * (y₂ - y₁) :=
          add_le_add (norm_sub_le _ _) hint_f''
      _ = R₂ := by rw [he2, he1]
  have hR_le_μt : R₂ / t ^ 2 ≤ μ / t := by
    rw [div_le_div_iff₀ (by positivity) ht_pos]
    have hRt : R₂ ≤ μ * t := by
      have hlt : R₂ / μ < t := by linarith
      rw [div_lt_iff₀ hμ_pos, mul_comm] at hlt
      exact hlt.le
    nlinarith
  change μ / t ≤ ‖∫ y in y₁..y₂, E y * f y‖
  rw [hibp2]
  have htri := norm_sub_le
    ((I * (t : ℂ))⁻¹ * (E y₂ * f y₂ - E y₁ * f y₁) +
      ((t : ℂ) ^ 2)⁻¹ * (E y₂ * f' y₂ - E y₁ * f' y₁ - ∫ y in y₁..y₂, E y * f'' y))
    (((t : ℂ) ^ 2)⁻¹ * (E y₂ * f' y₂ - E y₁ * f' y₁ - ∫ y in y₁..y₂, E y * f'' y))
  rw [add_sub_cancel_right] at htri
  have h2μt : 2 * μ / t = 2 * (μ / t) := by ring
  linarith [htri, hmain_ge, hrem_le, hR_le_μt, h2μt]


/-! ## §4 Strict right-edge positivity and `Ω(e^t / t)` blow-up on every Burnol unit window -/

/-- Canonical reference `XiZeroCopy` witness from Hardy's theorem
(`nonempty_xiZeroCopy_xiLogDerivLineOnePositive`). -/
def canonicalXiZeroCopy : _root_.RHTower.XiZeroCopy :=
  Classical.choice _root_.RHTower.nonempty_xiZeroCopy_xiLogDerivLineOnePositive

/-- Complex zero coordinate `ρ₀` of `canonicalXiZeroCopy`. -/
def canonicalXiZero : ℂ :=
  (canonicalXiZeroCopy.1 : ℂ)

/-- **Quantitative strict positivity of `Re (ξ'/ξ)(3/2 + iy)` at every real ordinate `y : ℝ`.** -/
theorem re_logDeriv_xi_three_halves_ge (y : ℝ) :
    1 / (9 + 4 * (y - canonicalXiZero.im) ^ 2) ≤
      (logDeriv _root_.RHTower.xi ((3 / 2 : ℂ) + (y : ℂ) * I)).re := by
  set s : ℂ := (3 / 2 : ℂ) + (y : ℂ) * I with hs_def
  have hs_re : s.re = 3 / 2 := by simp [s]
  have hs_im : s.im = y := by simp [s]
  have hxi : _root_.RHTower.xi s ≠ 0 :=
    _root_.RHTower.xi_ne_zero_of_one_le_re (by rw [hs_re]; norm_num)
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]
  set f : _root_.RHTower.XiZeroCopy → ℂ :=
    fun q => ((q.1 : ℂ) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹ with hf_def
  have hsum : Summable f := by
    have h := _root_.RHTower.XiAtlasFinitePart.summable_logDerivTerm hxi
    refine h.congr fun q => ?_
    show (_root_.RHTower.XiAtlasFinitePart.xiZero q - 1 / 2)⁻¹ -
        (_root_.RHTower.XiAtlasFinitePart.xiZero q - s)⁻¹ =
      ((q.1 : ℂ) - 1 / 2)⁻¹ + (s - (q.1 : ℂ))⁻¹
    rw [_root_.RHTower.XiAtlasFinitePart.xiZero,
      show ((q.1 : ℂ) - s) = -(s - (q.1 : ℂ)) by ring, inv_neg]
    ring
  have hsumJ : Summable (fun q => f (_root_.RHTower.xiZeroCopyLineConjEquiv q)) :=
    (_root_.RHTower.xiZeroCopyLineConjEquiv.summable_iff).mpr hsum
  set g : _root_.RHTower.XiZeroCopy → ℝ :=
    fun q => (f q + f (_root_.RHTower.xiZeroCopyLineConjEquiv q)).re with hg_def
  have hg_sum : Summable g := (hsum.add hsumJ).mapL Complex.reCLM
  have hg_eq : ∀ q : _root_.RHTower.XiZeroCopy,
      g q = ((s - (q.1 : ℂ))⁻¹).re + ((s - (1 - (starRingEnd ℂ) (q.1 : ℂ)))⁻¹).re := by
    intro q
    have hρ' := _root_.RHTower.xiZero_lineConj_eq q
    have hcenter : (((_root_.RHTower.xiZeroCopyLineConjEquiv q).1 : ℂ) - 1 / 2) =
        -((starRingEnd ℂ) ((q.1 : ℂ) - 1 / 2)) := by
      rw [hρ', map_sub, hhalf]; ring
    have hconst : ((((_root_.RHTower.xiZeroCopyLineConjEquiv q).1 : ℂ) - 1 / 2)⁻¹).re =
        -((((q.1 : ℂ)) - 1 / 2)⁻¹).re := by
      rw [hcenter, inv_neg, ← map_inv₀, Complex.neg_re, Complex.conj_re]
    dsimp only [g, f]
    simp only [Complex.add_re]
    rw [hconst, hρ']
    ring
  have hinv_re_lb : ∀ (u v : ℝ), 1 / 2 < u → u < 3 / 2 →
      2 / (9 + 4 * v ^ 2) ≤ (((u : ℂ) + (v : ℂ) * I)⁻¹).re := by
    intro u v hu1 hu2
    have hns : Complex.normSq ((u : ℂ) + (v : ℂ) * I) = u ^ 2 + v ^ 2 := by
      rw [Complex.normSq_apply]; simp [sq]
    have hre_z : ((u : ℂ) + (v : ℂ) * I).re = u := by simp
    rw [Complex.inv_re, hre_z, hns, div_le_div_iff₀ (by positivity) (by nlinarith)]
    have h1 : 0 < u * (9 - 2 * u) := mul_pos (by linarith) (by linarith)
    have h2 : 0 ≤ (4 * u - 2) * v ^ 2 := mul_nonneg (by linarith) (sq_nonneg v)
    nlinarith
  have hg_lb : ∀ q : _root_.RHTower.XiZeroCopy,
      4 / (9 + 4 * (y - ((q.1 : ℂ)).im) ^ 2) ≤ g q := by
    intro q
    have hstrip : (((q.1 : ℂ)).re - 1 / 2) ^ 2 < 1 / 4 :=
      _root_.RHTower.xi_divisor_support_centered_re_sq_lt_quarter q.1
    have hr0 : 0 < ((q.1 : ℂ)).re := by nlinarith
    have hr1 : ((q.1 : ℂ)).re < 1 := by nlinarith
    have hs1 : s - (q.1 : ℂ) =
        ((3 / 2 - ((q.1 : ℂ)).re : ℝ) : ℂ) + ((y - ((q.1 : ℂ)).im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [hs_re, hs_im]
    have hs2 : s - (1 - (starRingEnd ℂ) (q.1 : ℂ)) =
        ((1 / 2 + ((q.1 : ℂ)).re : ℝ) : ℂ) + ((y - ((q.1 : ℂ)).im : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp [hs_re, hs_im]; ring
    rw [hg_eq q, hs1, hs2]
    have hb1 := hinv_re_lb (3 / 2 - ((q.1 : ℂ)).re) (y - ((q.1 : ℂ)).im) (by linarith) (by linarith)
    have hb2 := hinv_re_lb (1 / 2 + ((q.1 : ℂ)).re) (y - ((q.1 : ℂ)).im) (by linarith) (by linarith)
    have h4eq : 4 / (9 + 4 * (y - ((q.1 : ℂ)).im) ^ 2) =
        2 / (9 + 4 * (y - ((q.1 : ℂ)).im) ^ 2) +
          2 / (9 + 4 * (y - ((q.1 : ℂ)).im) ^ 2) := by ring
    linarith
  have hg_nonneg : ∀ q : _root_.RHTower.XiZeroCopy, 0 ≤ g q :=
    fun q => (by positivity : (0 : ℝ) ≤ 4 / (9 + 4 * (y - ((q.1 : ℂ)).im) ^ 2)).trans (hg_lb q)
  have htsum_eq : ∑' q, g q = 2 * (logDeriv _root_.RHTower.xi s).re := by
    rw [_root_.RHTower.logDeriv_xi_eq_partialFraction hxi]
    change ∑' q, g q = 2 * (∑' q, f q).re
    have hreindex : (∑' q, f (_root_.RHTower.xiZeroCopyLineConjEquiv q)) = ∑' q, f q :=
      _root_.RHTower.xiZeroCopyLineConjEquiv.tsum_eq f
    calc ∑' q, g q
        = (∑' q, (f q + f (_root_.RHTower.xiZeroCopyLineConjEquiv q))).re :=
          (Complex.re_tsum (hsum.add hsumJ)).symm
      _ = ((∑' q, f q) + ∑' q, f (_root_.RHTower.xiZeroCopyLineConjEquiv q)).re := by
          rw [hsum.tsum_add hsumJ]
      _ = ((∑' q, f q) + ∑' q, f q).re := by rw [hreindex]
      _ = 2 * (∑' q, f q).re := by rw [Complex.add_re]; ring
  have hsingle := hg_sum.le_tsum canonicalXiZeroCopy (fun q _ => hg_nonneg q)
  have hq0 := hg_lb canonicalXiZeroCopy
  change 4 / (9 + 4 * (y - canonicalXiZero.im) ^ 2) ≤ g canonicalXiZeroCopy at hq0
  rw [htsum_eq] at hsingle
  have hpos : 0 < 1 / (9 + 4 * (y - canonicalXiZero.im) ^ 2) := by positivity
  have h4eq' : 4 / (9 + 4 * (y - canonicalXiZero.im) ^ 2) =
      4 * (1 / (9 + 4 * (y - canonicalXiZero.im) ^ 2)) := by ring
  linarith

private lemma norm_deriv_xi_le_strip_two {z : ℂ} (hz : |z.re| ≤ 2) :
    ‖deriv _root_.RHTower.xi z‖ ≤ _root_.RHTower.thetaAmplitudeEnvelope 2 := by
  have heq : deriv _root_.RHTower.xi z = -thetaSourceFirstMoment z :=
    neg_eq_iff_eq_neg.mp (thetaSourceFirstMoment_eq_neg_deriv_xi z).symm
  rw [heq, norm_neg, thetaSourceFirstMoment]
  have hfull : Integrable (fun x : ℝ =>
      (x : ℂ) * (_root_.RHTower.thetaCuspFullSource x : ℂ) *
        Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))) := by
    simpa only [pow_one, _root_.RHTower.thetaCuspTiltSource_k] using
      _root_.RHTower.thetaCuspTiltSource.integrable_mul_exp ((1 / 2 : ℂ) - z) 1
  have hC0 : 0 ≤ _root_.RHTower.thetaCuspTiltDecayConstant (2 + 5 / 2) :=
    (_root_.RHTower.thetaCuspTiltDecayConstant_pos _).le
  calc ‖∫ x : ℝ, (x : ℂ) * (_root_.RHTower.thetaCuspFullSource x : ℂ) *
          Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖
      ≤ ∫ x : ℝ, ‖(x : ℂ) * (_root_.RHTower.thetaCuspFullSource x : ℂ) *
          Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, _root_.RHTower.thetaCuspTiltDecayConstant (2 + 5 / 2) * Real.exp (-|x|) := by
        apply integral_mono_ae hfull.norm
          (_root_.RHTower.integrable_thetaAmplitudeProfile.const_mul _)
        filter_upwards with x
        rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_pos (_root_.RHTower.thetaCuspFullSource_pos x)]
        have hre : (1 / 2 - z.re) * x ≤ (2 + 1 / 2) * |x| := by
          calc (1 / 2 - z.re) * x ≤ |(1 / 2 - z.re) * x| := le_abs_self _
            _ = |1 / 2 - z.re| * |x| := abs_mul _ _
            _ ≤ (2 + 1 / 2) * |x| := by
                refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg x)
                rw [abs_le]; constructor <;> linarith [(abs_le.mp hz).1, (abs_le.mp hz).2]
        have hexp : ‖Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖ ≤ Real.exp ((2 + 1 / 2) * |x|) := by
          rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr
          have he : (((1 / 2 : ℂ) - z) * (x : ℂ)).re = (1 / 2 - z.re) * x := by simp
          simpa only [he] using hre
        have hsrc := _root_.RHTower.thetaCuspFullSource_le_tiltDecayConstant (2 + 5 / 2) x
        have hx_exp : |x| * Real.exp (-2 * |x|) ≤ Real.exp (-|x|) := by
          have hx : |x| ≤ Real.exp |x| := by linarith [Real.add_one_le_exp |x|]
          calc |x| * Real.exp (-2 * |x|) ≤ Real.exp |x| * Real.exp (-2 * |x|) :=
                mul_le_mul_of_nonneg_right hx (Real.exp_pos _).le
            _ = Real.exp (-|x|) := by rw [← Real.exp_add]; congr 1; ring
        calc |x| * _root_.RHTower.thetaCuspFullSource x *
                ‖Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖
            = |x| * (_root_.RHTower.thetaCuspFullSource x *
                ‖Complex.exp (((1 / 2 : ℂ) - z) * (x : ℂ))‖) := mul_assoc _ _ _
          _ ≤ |x| * ((_root_.RHTower.thetaCuspTiltDecayConstant (2 + 5 / 2) *
                Real.exp (-((2 + 5 / 2) * |x|))) * Real.exp ((2 + 1 / 2) * |x|)) := by
              refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg x)
              exact mul_le_mul hsrc hexp (norm_nonneg _) (mul_nonneg hC0 (Real.exp_pos _).le)
          _ = _root_.RHTower.thetaCuspTiltDecayConstant (2 + 5 / 2) *
                (|x| * Real.exp (-2 * |x|)) := by
              have hadd : Real.exp (-((2 + 5 / 2) * |x|)) * Real.exp ((2 + 1 / 2) * |x|) =
                  Real.exp (-2 * |x|) := by rw [← Real.exp_add]; congr 1; ring
              calc |x| * ((_root_.RHTower.thetaCuspTiltDecayConstant (2 + 5 / 2) *
                      Real.exp (-((2 + 5 / 2) * |x|))) * Real.exp ((2 + 1 / 2) * |x|))
                  = _root_.RHTower.thetaCuspTiltDecayConstant (2 + 5 / 2) *
                      (|x| * (Real.exp (-((2 + 5 / 2) * |x|)) *
                        Real.exp ((2 + 1 / 2) * |x|))) := by ring
                _ = _ := by rw [hadd]
          _ ≤ _root_.RHTower.thetaCuspTiltDecayConstant (2 + 5 / 2) * Real.exp (-|x|) :=
              mul_le_mul_of_nonneg_left hx_exp hC0
    _ = _root_.RHTower.thetaAmplitudeEnvelope 2 := by
        rw [MeasureTheory.integral_const_mul]; rfl

/-- Explicit multiplier constant `K_flux ≥ doorOpenerSqrtConst` ensuring `Re L_N(3/2 + iy) > 0`
at both Burnol heights `y₁(m), y₂(m)` for every `m : ℕ` and `N ≥ fluxSqrtPrefix m`. -/
def fluxSqrtConst : ℕ :=
  let E₂ := _root_.RHTower.thetaAmplitudeEnvelope 2
  let C₀ := _root_.RHTower.thetaCuspIntegerTailConstant * E₂
  let cg := burnolGoodLowerConst
  let K_den := 9 + 4 * (|canonicalXiZero.im| + 4) ^ 2
  let M_big := (8 * (E₂ + 1) * (C₀ + 1) * K_den / cg ^ 2 + 2 * (C₀ + 1) / cg + 1) * Real.exp 8
  max doorOpenerSqrtConst (Nat.ceil (Real.sqrt (|Real.log M_big| + 6)) + 2)

/-- Explicit `Θ(√m)` prefix schedule `fluxSqrtConst * (Nat.sqrt m + 1)`. -/
def fluxSqrtPrefix (m : ℕ) : ℕ :=
  fluxSqrtConst * (Nat.sqrt m + 1)

theorem doorSqrtPrefix_le_fluxSqrtPrefix (m : ℕ) : doorSqrtPrefix m ≤ fluxSqrtPrefix m :=
  Nat.mul_le_mul_right _ (le_max_left _ _)

theorem burnolPrefix_le_fluxSqrtPrefix (m : ℕ) :
    burnolPrefixConst * (Nat.sqrt m + 1) ≤ fluxSqrtPrefix m :=
  (burnolPrefix_le_doorSqrtPrefix m).trans (doorSqrtPrefix_le_fluxSqrtPrefix m)

/-- **Strict positivity of `Re L_N(3/2 + iy)` at both Burnol unit-window heights for all `m : ℕ`.** -/
theorem re_thetaLogDeriv_burnol_pos (m : ℕ) {N : ℕ} (hN : fluxSqrtPrefix m ≤ N)
    {y : ℝ} (hy_or : y = burnolUnitLower m ∨ y = burnolUnitUpper m) :
    0 < (thetaLogDeriv N ((3 / 2 : ℂ) + (y : ℂ) * I)).re := by
  set E₂ : ℝ := _root_.RHTower.thetaAmplitudeEnvelope 2
  have hE₂_nn : 0 ≤ E₂ := _root_.RHTower.thetaAmplitudeEnvelope_nonneg 2
  set C₀ : ℝ := _root_.RHTower.thetaCuspIntegerTailConstant * E₂
  have hC₀_nn : 0 ≤ C₀ := mul_nonneg _root_.RHTower.thetaCuspIntegerTailConstant_nonneg hE₂_nn
  set cg : ℝ := burnolGoodLowerConst
  have hcg_pos : 0 < cg := burnolGoodLowerConst_pos
  set K_den : ℝ := 9 + 4 * (|canonicalXiZero.im| + 4) ^ 2
  have hK_den_pos : 0 < K_den := by dsimp [K_den]; positivity
  set M_big : ℝ := (8 * (E₂ + 1) * (C₀ + 1) * K_den / cg ^ 2 + 2 * (C₀ + 1) / cg + 1) * Real.exp 8
  have hM_big_gt1 : 1 < M_big := by
    dsimp [M_big]
    have h1 : 0 ≤ 8 * (E₂ + 1) * (C₀ + 1) * K_den / cg ^ 2 + 2 * (C₀ + 1) / cg := by positivity
    have he8 : 1 < Real.exp 8 := Real.one_lt_exp_iff.mpr (by norm_num)
    nlinarith
  have hM_pos : 0 < M_big := by linarith
  set z : ℂ := (3 / 2 : ℂ) + (y : ℂ) * I
  have hz_re : |z.re| ≤ 2 := by simp [z]; norm_num
  obtain ⟨hy₁_lo, hy₁_hi, hy₂_lo, hy₂_hi, _⟩ := burnolUnit_coords m
  have hy_abs : |y| ≤ (m : ℝ) + 3 := by
    rcases hy_or with rfl | rfl
    · exact abs_le.mpr ⟨by linarith, by linarith⟩
    · exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hxi_ge : cg * Real.exp (-((m + 3 : ℕ) : ℝ)) ≤ ‖_root_.RHTower.xi z‖ := by
    obtain ⟨τ, hτ⟩ := exists_boundaryPath_of_edges
      (z₁ := centeredWindowLowerLeft (burnolUnitLower m))
      (z₂ := centeredWindowUpperRight (burnolUnitUpper m))
      (by simp; norm_num) (by simpa using burnolUnitLower_le_upper m)
      (by simp [z]; norm_num)
      (by rcases hy_or with rfl | rfl <;> simp [z, burnolUnitLower_le_upper m])
      (Or.inr (Or.inl (by simp [z])))
    rw [← hτ]
    exact burnolUnit_xi_bdry_ge m τ
  have hxi_le : ‖_root_.RHTower.xi z‖ ≤ E₂ := by
    rw [← bilateral_fullTheta_eq_xi]
    exact _root_.RHTower.norm_fullThetaAmplitude_le_strip (by norm_num) hz_re
  have hdxi_le : ‖deriv _root_.RHTower.xi z‖ ≤ E₂ := norm_deriv_xi_le_strip_two hz_re
  have hA_diff : ‖_root_.RHTower.finiteThetaAmplitude N z - _root_.RHTower.xi z‖ ≤
      thetaStripTailBound N := by
    simpa only [thetaStripTailBound, mul_right_comm] using
      norm_finiteThetaAmplitude_sub_xi_le_strip N (R := 2) (by norm_num) hz_re
  have hM_diff : ‖-_root_.RHTower.finiteThetaFirstMoment N z - deriv _root_.RHTower.xi z‖ ≤
      thetaStripTailBound N := by
    simpa only [thetaStripTailBound, mul_right_comm] using
      norm_finiteThetaFirstMoment_sub_deriv_xi_le_strip N (R := 2) (by norm_num) hz_re
  have hN_sq : Real.log M_big + 4 * ((m : ℝ) + 1) < ((N + 1 : ℕ) : ℝ) ^ 2 := by
    have hK_ge : Nat.ceil (Real.sqrt (|Real.log M_big| + 6)) + 2 ≤ fluxSqrtConst := le_max_right _ _
    have hsq_nat : (Nat.ceil (Real.sqrt (|Real.log M_big| + 6)) + 2) * (Nat.sqrt m + 1) ≤ N :=
      (Nat.mul_le_mul_right _ hK_ge).trans hN
    have hm_sq : m + 1 ≤ (Nat.sqrt m + 1) ^ 2 := Nat.lt_succ_sqrt' m
    have h1 : (|Real.log M_big| + 6) * ((m : ℝ) + 1) < ((N + 1 : ℕ) : ℝ) ^ 2 := by
      have hc : Real.sqrt (|Real.log M_big| + 6) <
          ((Nat.ceil (Real.sqrt (|Real.log M_big| + 6)) + 2 : ℕ) : ℝ) := by
        push_cast
        linarith [Nat.le_ceil (Real.sqrt (|Real.log M_big| + 6))]
      have hc_sq : |Real.log M_big| + 6 <
          ((Nat.ceil (Real.sqrt (|Real.log M_big| + 6)) + 2 : ℕ) : ℝ) ^ 2 := by
        rw [← Real.sq_sqrt (by positivity : 0 ≤ |Real.log M_big| + 6)]
        exact pow_lt_pow_left₀ hc (Real.sqrt_nonneg _) two_ne_zero
      have hmul : (|Real.log M_big| + 6) * ((m : ℝ) + 1) <
          ((Nat.ceil (Real.sqrt (|Real.log M_big| + 6)) + 2 : ℕ) : ℝ) ^ 2 *
            ((Nat.sqrt m + 1 : ℕ) : ℝ) ^ 2 := by
        have hmR : (m : ℝ) + 1 ≤ ((Nat.sqrt m + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast hm_sq
        have hm_pos : 0 < (m : ℝ) + 1 := by positivity
        exact lt_of_lt_of_le (mul_lt_mul_of_pos_right hc_sq hm_pos)
          (mul_le_mul_of_nonneg_left hmR (by positivity))
      have hNR : ((Nat.ceil (Real.sqrt (|Real.log M_big| + 6)) + 2 : ℕ) : ℝ) ^ 2 *
          ((Nat.sqrt m + 1 : ℕ) : ℝ) ^ 2 ≤ ((N + 1 : ℕ) : ℝ) ^ 2 := by
        rw [← mul_pow]
        have hleR : ((Nat.ceil (Real.sqrt (|Real.log M_big| + 6)) + 2 : ℕ) : ℝ) *
            ((Nat.sqrt m + 1 : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
          exact_mod_cast (hsq_nat.trans (Nat.le_succ N))
        exact pow_le_pow_left₀ (by positivity) hleR 2
      exact hmul.trans_le hNR
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hlog_le : Real.log M_big ≤ |Real.log M_big| := le_abs_self _
    have hlog_nn : 0 ≤ |Real.log M_big| := abs_nonneg _
    nlinarith
  have hexp_N : Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2) < Real.exp (-4 * ((m : ℝ) + 1)) / M_big := by
    rw [lt_div_iff₀ hM_pos, ← Real.exp_log hM_pos, ← Real.exp_add]
    exact Real.exp_lt_exp.mpr (by linarith)
  have htail_lt : thetaStripTailBound N <
      (C₀ + 1) * Real.exp (-4 * ((m : ℝ) + 1)) / M_big := by
    calc thetaStripTailBound N = C₀ * Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2) := rfl
      _ ≤ (C₀ + 1) * Real.exp (-((N + 1 : ℕ) : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
      _ < (C₀ + 1) * (Real.exp (-4 * ((m : ℝ) + 1)) / M_big) :=
          mul_lt_mul_of_pos_left hexp_N (by positivity)
      _ = (C₀ + 1) * Real.exp (-4 * ((m : ℝ) + 1)) / M_big := by ring
  -- Lower bound `‖A_N z‖ ≥ (cg / 2) e^{-(m+3)}`
  have htail_half : thetaStripTailBound N ≤ (cg / 2) * Real.exp (-((m + 3 : ℕ) : ℝ)) := by
    refine htail_lt.le.trans ?_
    rw [div_le_iff₀ hM_pos]
    have hM_part : (2 * (C₀ + 1) / cg) * Real.exp 8 ≤ M_big := by
      dsimp [M_big]
      have : 0 ≤ (8 * (E₂ + 1) * (C₀ + 1) * K_den / cg ^ 2 + 1) * Real.exp 8 := by positivity
      linarith
    have hexp_cmp : Real.exp (-4 * ((m : ℝ) + 1)) ≤
        Real.exp (-((m + 3 : ℕ) : ℝ)) * Real.exp 8 := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      push_cast; linarith
    calc (C₀ + 1) * Real.exp (-4 * ((m : ℝ) + 1))
        ≤ (C₀ + 1) * (Real.exp (-((m + 3 : ℕ) : ℝ)) * Real.exp 8) :=
          mul_le_mul_of_nonneg_left hexp_cmp (by positivity)
      _ = (cg / 2) * Real.exp (-((m + 3 : ℕ) : ℝ)) * ((2 * (C₀ + 1) / cg) * Real.exp 8) := by
          field_simp [hcg_pos.ne']
      _ ≤ (cg / 2) * Real.exp (-((m + 3 : ℕ) : ℝ)) * M_big :=
          mul_le_mul_of_nonneg_left hM_part (by positivity)
  have hAN_ge : (cg / 2) * Real.exp (-((m + 3 : ℕ) : ℝ)) ≤
      ‖_root_.RHTower.finiteThetaAmplitude N z‖ := by
    have htri := norm_sub_le (_root_.RHTower.xi z)
      (_root_.RHTower.xi z - _root_.RHTower.finiteThetaAmplitude N z)
    rw [sub_sub_cancel, norm_sub_rev] at htri
    linarith [hxi_ge, hA_diff, htail_half, htri]
  have hAN_pos : 0 < ‖_root_.RHTower.finiteThetaAmplitude N z‖ :=
    lt_of_lt_of_le (by positivity) hAN_ge
  have hxi_pos : 0 < ‖_root_.RHTower.xi z‖ := lt_of_lt_of_le (by positivity) hxi_ge
  have hAN_ne : _root_.RHTower.finiteThetaAmplitude N z ≠ 0 := norm_pos_iff.mp hAN_pos
  have hxi_ne : _root_.RHTower.xi z ≠ 0 := norm_pos_iff.mp hxi_pos
  -- Bound `‖thetaLogDeriv N z - logDeriv xi z‖`
  have hquot_diff : ‖thetaLogDeriv N z - logDeriv _root_.RHTower.xi z‖ ≤
      4 * (E₂ + 1) * thetaStripTailBound N /
        (cg ^ 2 * Real.exp (-2 * ((m + 3 : ℕ) : ℝ))) := by
    rw [thetaLogDeriv, logDeriv_apply]
    have halg : -_root_.RHTower.finiteThetaFirstMoment N z /
          _root_.RHTower.finiteThetaAmplitude N z -
        deriv _root_.RHTower.xi z / _root_.RHTower.xi z =
      ((-_root_.RHTower.finiteThetaFirstMoment N z - deriv _root_.RHTower.xi z) *
          _root_.RHTower.xi z +
        deriv _root_.RHTower.xi z *
          (_root_.RHTower.xi z - _root_.RHTower.finiteThetaAmplitude N z)) /
        (_root_.RHTower.finiteThetaAmplitude N z * _root_.RHTower.xi z) := by
      field_simp [hAN_ne, hxi_ne]; ring
    rw [halg, norm_div, norm_mul]
    have hnum : ‖(-_root_.RHTower.finiteThetaFirstMoment N z - deriv _root_.RHTower.xi z) *
          _root_.RHTower.xi z +
        deriv _root_.RHTower.xi z *
          (_root_.RHTower.xi z - _root_.RHTower.finiteThetaAmplitude N z)‖ ≤
        2 * (E₂ + 1) * thetaStripTailBound N := by
      have h1 : ‖(-_root_.RHTower.finiteThetaFirstMoment N z - deriv _root_.RHTower.xi z) *
          _root_.RHTower.xi z‖ ≤ (E₂ + 1) * thetaStripTailBound N := by
        rw [norm_mul, mul_comm]
        exact mul_le_mul (hxi_le.trans (by linarith)) hM_diff (norm_nonneg _) (by positivity)
      have h2 : ‖deriv _root_.RHTower.xi z *
          (_root_.RHTower.xi z - _root_.RHTower.finiteThetaAmplitude N z)‖ ≤
          (E₂ + 1) * thetaStripTailBound N := by
        rw [norm_mul, norm_sub_rev]
        exact mul_le_mul (hdxi_le.trans (by linarith)) hA_diff (norm_nonneg _) (by positivity)
      calc ‖_ + _‖ ≤ _ + _ := norm_add_le _ _
        _ ≤ (E₂ + 1) * thetaStripTailBound N + (E₂ + 1) * thetaStripTailBound N :=
            add_le_add h1 h2
        _ = 2 * (E₂ + 1) * thetaStripTailBound N := by ring
    have hden : (cg ^ 2 / 2) * Real.exp (-2 * ((m + 3 : ℕ) : ℝ)) ≤
        ‖_root_.RHTower.finiteThetaAmplitude N z‖ * ‖_root_.RHTower.xi z‖ := by
      calc (cg ^ 2 / 2) * Real.exp (-2 * ((m + 3 : ℕ) : ℝ))
          = ((cg / 2) * Real.exp (-((m + 3 : ℕ) : ℝ))) *
              (cg * Real.exp (-((m + 3 : ℕ) : ℝ))) := by
            rw [mul_mul_mul_comm, ← Real.exp_add]; congr 1 <;> ring
        _ ≤ ‖_root_.RHTower.finiteThetaAmplitude N z‖ * ‖_root_.RHTower.xi z‖ :=
            mul_le_mul hAN_ge hxi_ge (by positivity) hAN_pos.le
    calc ‖_‖ / (‖_root_.RHTower.finiteThetaAmplitude N z‖ * ‖_root_.RHTower.xi z‖)
        ≤ (2 * (E₂ + 1) * thetaStripTailBound N) /
            ((cg ^ 2 / 2) * Real.exp (-2 * ((m + 3 : ℕ) : ℝ))) :=
          div_le_div₀ (by positivity) hnum (by positivity) hden
      _ = 4 * (E₂ + 1) * thetaStripTailBound N /
            (cg ^ 2 * Real.exp (-2 * ((m + 3 : ℕ) : ℝ))) := by field_simp [hcg_pos.ne']; ring
  -- Compare with `1 / (9 + 4 * (y - Im ρ₀)²) ≥ 1 / (K_den * exp(2 * (m + 1)))`
  have hden_le : 9 + 4 * (y - canonicalXiZero.im) ^ 2 ≤ K_den * Real.exp (2 * ((m : ℝ) + 1)) := by
    have hydiff : |y - canonicalXiZero.im| ≤ ((m : ℝ) + 1) * (|canonicalXiZero.im| + 4) := by
      have h1 : |y - canonicalXiZero.im| ≤ |y| + |canonicalXiZero.im| := abs_sub _ _
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have hc0 : 0 ≤ |canonicalXiZero.im| := abs_nonneg _
      nlinarith
    have hsq_y : (y - canonicalXiZero.im) ^ 2 ≤
        ((m : ℝ) + 1) ^ 2 * (|canonicalXiZero.im| + 4) ^ 2 := by
      rw [← sq_abs, ← mul_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) hydiff 2
    have hm_exp : ((m : ℝ) + 1) ^ 2 ≤ Real.exp (2 * ((m : ℝ) + 1)) := by
      have h1 : (m : ℝ) + 1 ≤ Real.exp ((m : ℝ) + 1) := by
        linarith [Real.add_one_le_exp ((m : ℝ) + 1)]
      calc ((m : ℝ) + 1) ^ 2 ≤ (Real.exp ((m : ℝ) + 1)) ^ 2 :=
            pow_le_pow_left₀ (by positivity) h1 2
        _ = Real.exp (2 * ((m : ℝ) + 1)) := by rw [sq, ← Real.exp_add]; congr 1; ring
    have hm1_sq : 1 ≤ ((m : ℝ) + 1) ^ 2 := by
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m; nlinarith
    calc 9 + 4 * (y - canonicalXiZero.im) ^ 2
        ≤ 9 * ((m : ℝ) + 1) ^ 2 + 4 * (((m : ℝ) + 1) ^ 2 * (|canonicalXiZero.im| + 4) ^ 2) := by
          nlinarith
      _ = K_den * ((m : ℝ) + 1) ^ 2 := by dsimp [K_den]; ring
      _ ≤ K_den * Real.exp (2 * ((m : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hm_exp hK_den_pos.le
  have hxi_re_lb : 1 / (K_den * Real.exp (2 * ((m : ℝ) + 1))) ≤
      (logDeriv _root_.RHTower.xi z).re :=
    (div_le_div_of_nonneg_left zero_le_one (by positivity) hden_le).trans
      (re_logDeriv_xi_three_halves_ge y)
  have hquot_lt : 4 * (E₂ + 1) * thetaStripTailBound N /
        (cg ^ 2 * Real.exp (-2 * ((m + 3 : ℕ) : ℝ))) <
      1 / (2 * K_den * Real.exp (2 * ((m : ℝ) + 1))) := by
    have hstep1 : 4 * (E₂ + 1) * thetaStripTailBound N /
          (cg ^ 2 * Real.exp (-2 * ((m + 3 : ℕ) : ℝ))) <
        4 * (E₂ + 1) * ((C₀ + 1) * Real.exp (-4 * ((m : ℝ) + 1)) / M_big) /
          (cg ^ 2 * Real.exp (-2 * ((m + 3 : ℕ) : ℝ))) := by
      exact div_lt_div_of_pos_right
        (mul_lt_mul_of_pos_left htail_lt (by positivity)) (by positivity)
    refine hstep1.trans_le ?_
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hM_part : (8 * (E₂ + 1) * (C₀ + 1) * K_den / cg ^ 2) * Real.exp 8 ≤ M_big := by
      dsimp [M_big]
      have : 0 ≤ (2 * (C₀ + 1) / cg + 1) * Real.exp 8 := by positivity
      linarith
    have hexp_id : Real.exp (-4 * ((m : ℝ) + 1)) * (2 * K_den * Real.exp (2 * ((m : ℝ) + 1))) =
        2 * K_den * Real.exp (-2 * ((m + 3 : ℕ) : ℝ)) * Real.exp 8 := by
      have hexp_eq : Real.exp (-4 * ((m : ℝ) + 1)) * Real.exp (2 * ((m : ℝ) + 1)) =
          Real.exp (-2 * ((m + 3 : ℕ) : ℝ)) * Real.exp 8 := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1; push_cast; ring
      calc Real.exp (-4 * ((m : ℝ) + 1)) * (2 * K_den * Real.exp (2 * ((m : ℝ) + 1)))
          = 2 * K_den * (Real.exp (-4 * ((m : ℝ) + 1)) * Real.exp (2 * ((m : ℝ) + 1))) := by ring
        _ = 2 * K_den * Real.exp (-2 * ((m + 3 : ℕ) : ℝ)) * Real.exp 8 := by rw [hexp_eq]; ring
    have hdiv_le : 4 * (E₂ + 1) * ((C₀ + 1) * Real.exp (-4 * ((m : ℝ) + 1)) / M_big) *
          (2 * K_den * Real.exp (2 * ((m : ℝ) + 1))) ≤
        cg ^ 2 * Real.exp (-2 * ((m + 3 : ℕ) : ℝ)) := by
      rw [show 4 * (E₂ + 1) * ((C₀ + 1) * Real.exp (-4 * ((m : ℝ) + 1)) / M_big) *
            (2 * K_den * Real.exp (2 * ((m : ℝ) + 1))) =
          (4 * (E₂ + 1) * (C₀ + 1) *
            (Real.exp (-4 * ((m : ℝ) + 1)) * (2 * K_den * Real.exp (2 * ((m : ℝ) + 1))))) / M_big
            by ring,
        hexp_id, div_le_iff₀ hM_pos]
      calc 4 * (E₂ + 1) * (C₀ + 1) * (2 * K_den * Real.exp (-2 * ((m + 3 : ℕ) : ℝ)) * Real.exp 8)
          = (cg ^ 2 * Real.exp (-2 * ((m + 3 : ℕ) : ℝ))) *
              ((8 * (E₂ + 1) * (C₀ + 1) * K_den / cg ^ 2) * Real.exp 8) := by
            field_simp [hcg_pos.ne']; ring
        _ ≤ (cg ^ 2 * Real.exp (-2 * ((m + 3 : ℕ) : ℝ))) * M_big :=
            mul_le_mul_of_nonneg_left hM_part (by positivity)
    linarith
  have hre_diff : |(thetaLogDeriv N z - logDeriv _root_.RHTower.xi z).re| ≤
      ‖thetaLogDeriv N z - logDeriv _root_.RHTower.xi z‖ := Complex.abs_re_le_norm _
  have hre_sub := (abs_le.mp hre_diff).1
  rw [Complex.sub_re] at hre_sub
  have hpos_den : 0 < 1 / (2 * K_den * Real.exp (2 * ((m : ℝ) + 1))) := by positivity
  have hhalf_eq : 1 / (K_den * Real.exp (2 * ((m : ℝ) + 1))) =
      2 * (1 / (2 * K_den * Real.exp (2 * ((m : ℝ) + 1)))) := by ring
  linarith

/-- **Unconditional `Ω(e^t / t)` exponential blow-up of right-plus-left flux on every Burnol unit
window.** For every `m : ℕ` and every `N ≥ fluxSqrtPrefix m`, neither `ℱ_left(t)` nor the full
functional-equation left half-port `𝒫_-(t)` cancels `ℱ_right(t)`: both `‖ℱ_right + ℱ_left‖` and
`‖ℱ_right + 𝒫_-‖` exceed `c * e^t / t` at some `t` in every period `[T, T + 2π / (y₂(m) - y₁(m))]`
for `T ≥ T₀`. -/
theorem exists_burnol_rightAddLeftFlux_exp_blowup (m : ℕ) {N : ℕ} (hN : fluxSqrtPrefix m ≤ N) :
    ∃ c T₀ : ℝ, 0 < c ∧ 1 ≤ T₀ ∧
      ∀ T : ℝ, T₀ ≤ T →
        ∃ t ∈ Icc T (T + 2 * Real.pi / (burnolUnitUpper m - burnolUnitLower m)),
          c * Real.exp t / t ≤
            ‖rightEdgeFlux (burnolUnitLower m) (burnolUnitUpper m) N t +
              leftEdgeFlux (burnolUnitLower m) (burnolUnitUpper m) N t‖ ∧
          c * Real.exp t / t ≤
            ‖rightEdgeFlux (burnolUnitLower m) (burnolUnitUpper m) N t +
              leftHalfPort (burnolUnitLower m) (burnolUnitUpper m) N t‖ := by
  set y₁ := burnolUnitLower m
  set y₂ := burnolUnitUpper m
  have hy_lt : y₁ < y₂ := burnolUnitLower_lt_upper m
  have hbdry := burnolUnit_bdry_regular m (burnolPrefix_le_fluxSqrtPrefix m |>.trans hN)
  have hnz_r : ∀ y ∈ Icc y₁ y₂,
      _root_.RHTower.finiteThetaAmplitude N ((3 / 2 : ℂ) + (y : ℂ) * I) ≠ 0 := by
    intro y hy_m
    exact edge_ne_zero_of_bdry_regular hy_lt.le hbdry ⟨by simp; norm_num, by simp; norm_num⟩
      ⟨by simpa using hy_m.1, by simpa using hy_m.2⟩ (Or.inr (Or.inl (by simp)))
  set f : ℝ → ℂ := fun y => (2 * Real.pi : ℂ)⁻¹ * thetaLogDeriv N ((3 / 2 : ℂ) + (y : ℂ) * I)
  set f' : ℝ → ℂ :=
    fun y => (2 * Real.pi : ℂ)⁻¹ * I * deriv (thetaLogDeriv N) ((3 / 2 : ℂ) + (y : ℂ) * I)
  set f'' : ℝ → ℂ :=
    fun y => -(2 * Real.pi : ℂ)⁻¹ *
      deriv (deriv (thetaLogDeriv N)) ((3 / 2 : ℂ) + (y : ℂ) * I)
  have hf1 : ∀ y ∈ Icc y₁ y₂, HasDerivAt f (f' y) y := by
    intro y hy_m
    have hw : HasDerivAt (fun w : ℂ => thetaLogDeriv N ((3 / 2 : ℂ) + w * I))
        (deriv (thetaLogDeriv N) ((3 / 2 : ℂ) + (y : ℂ) * I) * I) (y : ℂ) := by
      have han := (analyticAt_thetaLogDeriv (hnz_r y hy_m)).differentiableAt.hasDerivAt
      exact han.comp (y : ℂ)
        ((hasDerivAt_const (y : ℂ) (3 / 2 : ℂ)).add ((hasDerivAt_id (y : ℂ)).mul_const I)
          |>.congr_deriv (by ring))
    exact ((hw.comp_ofReal).const_mul (2 * Real.pi : ℂ)⁻¹).congr_deriv (by dsimp [f']; ring)
  have hf2 : ∀ y ∈ Icc y₁ y₂, HasDerivAt f' (f'' y) y := by
    intro y hy_m
    have hw : HasDerivAt (fun w : ℂ => deriv (thetaLogDeriv N) ((3 / 2 : ℂ) + w * I))
        (deriv (deriv (thetaLogDeriv N)) ((3 / 2 : ℂ) + (y : ℂ) * I) * I) (y : ℂ) := by
      have han := ((analyticAt_thetaLogDeriv (hnz_r y hy_m)).deriv).differentiableAt.hasDerivAt
      exact han.comp (y : ℂ)
        ((hasDerivAt_const (y : ℂ) (3 / 2 : ℂ)).add ((hasDerivAt_id (y : ℂ)).mul_const I)
          |>.congr_deriv (by ring))
    refine ((hw.comp_ofReal).const_mul ((2 * Real.pi : ℂ)⁻¹ * I)).congr_deriv ?_
    dsimp [f'']
    have hI2 : (I : ℂ) ^ 2 = -1 := Complex.I_sq
    linear_combination (2 * Real.pi : ℂ)⁻¹ *
      deriv (deriv (thetaLogDeriv N)) ((3 / 2 : ℂ) + (y : ℂ) * I) * hI2
  have hf''_cont : ContinuousOn f'' (Icc y₁ y₂) := by
    intro y hy_m
    dsimp [f'']
    refine continuousWithinAt_const.mul ?_
    exact ((((analyticAt_thetaLogDeriv (hnz_r y hy_m)).deriv).deriv).continuousAt.comp
      (by fun_prop : Continuous fun y : ℝ => (3 / 2 : ℂ) + (y : ℂ) * I).continuousAt).continuousWithinAt
  have hfy₂_pos : 0 < ‖f y₂‖ := by
    have hre_pos := re_thetaLogDeriv_burnol_pos m hN (y := y₂) (Or.inr rfl)
    have hf_re : 0 < (f y₂).re := by
      dsimp [f]
      have hcast : ((2 * Real.pi : ℂ)⁻¹) = (((2 * Real.pi)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
      rw [hcast, Complex.re_ofReal_mul]
      exact mul_pos (by positivity) hre_pos
    exact lt_of_lt_of_le hf_re ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  have hsum_sq_pos : 0 < ‖f y₁‖ ^ 2 + ‖f y₂‖ ^ 2 := by positivity
  obtain ⟨μ, T₁, hμ_pos, hT₁, hosc⟩ :=
    exists_oscillatory_integral_ge_div_t hy_lt hf1 hf2 hf''_cont hsum_sq_pos
  obtain ⟨C_L, hC_L, hleft_bd⟩ := exists_leftEdge_and_leftHalfPort_decay hy_lt.le N hbdry
  let T₀ : ℝ := max T₁ (2 * C_L / μ + 1)
  refine ⟨μ / 2, T₀, half_pos hμ_pos, hT₁.trans (le_max_left _ _), fun T hT => ?_⟩
  obtain ⟨t, ht_mem, ht_int⟩ := hosc T ((le_max_left _ _).trans hT)
  refine ⟨t, ht_mem, ?_⟩
  have ht_ge_T₀ : T₀ ≤ t := hT.trans ht_mem.1
  have ht1 : 1 ≤ t := (hT₁.trans (le_max_left _ _)).trans ht_ge_T₀
  have ht_pos : 0 < t := by linarith
  have ht_CL : 2 * C_L / μ + 1 ≤ t := (le_max_right _ _).trans ht_ge_T₀
  have hright_eq : rightEdgeFlux y₁ y₂ N t =
      (Real.exp t : ℂ) * ∫ y in y₁..y₂, cexp ((t : ℂ) * (y : ℂ) * I) * f y := by
    unfold rightEdgeFlux vertFlux
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun y _ => ?_
    dsimp [f]
    have hexp_split : cexp ((t : ℂ) * ((((3 / 2 : ℝ) : ℂ) + (y : ℂ) * I) - 1 / 2)) =
        (Real.exp t : ℂ) * cexp ((t : ℂ) * (y : ℂ) * I) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      congr 1; push_cast; ring
    rw [hexp_split]
    ring
  have hright_norm : μ * Real.exp t / t ≤ ‖rightEdgeFlux y₁ y₂ N t‖ := by
    rw [hright_eq, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos t).le]
    calc μ * Real.exp t / t = Real.exp t * (μ / t) := by ring
      _ ≤ Real.exp t * ‖∫ y in y₁..y₂, cexp ((t : ℂ) * (y : ℂ) * I) * f y‖ :=
          mul_le_mul_of_nonneg_left ht_int (Real.exp_pos t).le
  obtain ⟨hl_edge, hl_port⟩ := hleft_bd t ht_pos.le
  have hCL_le : C_L / (t + 1) ≤ (μ / 2) * Real.exp t / t := by
    have h1 : C_L / (t + 1) ≤ C_L / t :=
      div_le_div_of_nonneg_left hC_L.le ht_pos (by linarith)
    have h2 : C_L ≤ (μ / 2) * Real.exp t := by
      have hexp_ge_t : t ≤ Real.exp t := by linarith [Real.add_one_le_exp t]
      have hCL_μt : C_L ≤ (μ / 2) * t := by
        have : 2 * C_L / μ < t := by linarith
        rw [div_lt_iff₀ hμ_pos] at this
        linarith
      exact hCL_μt.trans (mul_le_mul_of_nonneg_left hexp_ge_t (by positivity))
    exact h1.trans (div_le_div_of_nonneg_right h2 ht_pos.le)
  have hedge_le : C_L * Real.exp (-t) ≤ (μ / 2) * Real.exp t / t := by
    have hexp_inv : Real.exp (-t) ≤ 1 / (t + 1) := by
      rw [Real.exp_neg, one_div]
      exact inv_anti₀ (by linarith) (by linarith [Real.add_one_le_exp t])
    calc C_L * Real.exp (-t) ≤ C_L * (1 / (t + 1)) :=
          mul_le_mul_of_nonneg_left hexp_inv hC_L.le
      _ = C_L / (t + 1) := by ring
      _ ≤ (μ / 2) * Real.exp t / t := hCL_le
  constructor
  · have htri := norm_sub_le (rightEdgeFlux y₁ y₂ N t + leftEdgeFlux y₁ y₂ N t)
      (leftEdgeFlux y₁ y₂ N t)
    rw [add_sub_cancel_right] at htri
    have hl_le := hl_edge.trans hedge_le
    linarith [htri, hright_norm, hl_le]
  · have htri := norm_sub_le (rightEdgeFlux y₁ y₂ N t + leftHalfPort y₁ y₂ N t)
      (leftHalfPort y₁ y₂ N t)
    rw [add_sub_cancel_right] at htri
    have hl_le := hl_port.trans hCL_le
    linarith [htri, hright_norm, hl_le]

end GaloisForLFunctions.ConjugateDiagonalGeometry.WindowPortFlux
