import GaloisForLFunctions.BlackHoleRingdown.TheMeanSquareLawOfTheCuspModes
import GaloisForLFunctions.RHTower.ZetaZerosLeeYangPutnam
import GaloisForLFunctions.RHTower.SelbergStripPolynomialGrowth
import GaloisForLFunctions.HTGeometry.GammaHalfIntegerLineBound
import GaloisForLFunctions.RHTower.ZetaEulerRegionDiscSeamMargin

/-!
# The vertical decay of the Rankin–Selberg function

For a cusp form `g` of the modular horizon let `Λ_g(s) = ∫_𝒟 |g|² E*(s - ½)` be its completed
Rankin–Selberg function and

  `P_g(s) = s (s - ½)(s - 1) Λ_g(s)`.

* `P_g` is **entire** (`differentiable_entireRS`) and **odd** under `s ↦ 1 - s`
  (`entireRS_one_sub`): `(u² - ¼) u E*(u) = ((u-½)ξ(1+2u)/4) Y^{½+u} + ((u+½)ξ(2u)/4) Y^{½-u} + u(u²-¼) T(u)`
  has entire coefficients, so the cusp domination gives an entire integral.
* `P_g` **decays like `e^{-π|t|}`** on the strip `-¼ ≤ Re s ≤ 5/4` (`exists_norm_entireRS_le`):
  `‖P_g(σ + it)‖ ≤ C (1 + |t|)^N e^{-π|t|}`.

**Proof of the decay.** Inside the strip `P_g` grows at most polynomially: the coefficients involve `ξ` on
`-3/2 ≤ Re w ≤ 5/2`, polynomially bounded there, and the Whittaker tail is bounded uniformly in `Im u`. On
`Re s = 5/4` the Rankin–Selberg series converges absolutely and
`P_g(s) = (s-1)/4 · ξ(2s) G(s) (2π)^{-s} L_g(s)`, where in `ξ(2s) G(s)` the factor `Γ(s)` cancels:
`ξ(2s)G(s) = s(2s-1) π^{-s} ζ(2s) 2^{s-3} Γ(s/2+ν) Γ(s/2)² Γ(s/2-ν)`, and the four Gamma factors on
`Re = 5/8` decay like `e^{-π|t|}` in total. On `Re s = -¼` use `P_g(1 - s) = -P_g(s)`. Phragmén–Lindelöf
applied to `P_g(s) e^{∓iπs}/(s+3)^N` gives the bound in the whole strip.
-/

open Complex MeasureTheory Set Filter Topology Asymptotics
open scoped MatrixGroups UpperHalfPlane

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open _root_.RHTower GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower.DeckPointPair

namespace CuspRSV

open HeckeCusp CuspL CuspRSC CuspMS

variable {lamE : ℝ} {g : UpperHalfPlane → ℂ} {ρ : ℤ → ℂ}

/-! ### `ξ` on a wide strip -/

theorem norm_mul_sub_one_le (w : ℂ) {B : ℝ} (hB : |w.re| ≤ B) :
    ‖w * (w - 1) / 2‖ ≤ (B + 1) ^ 2 * (1 + |w.im|) ^ 2 := by
  have hB0' : 0 ≤ B := (abs_nonneg _).trans hB
  have h1 : ‖w‖ ≤ (B + 1) * (1 + |w.im|) := by
    refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
    nlinarith [abs_nonneg w.im, abs_nonneg w.re]
  have h2 : ‖w - 1‖ ≤ (B + 1) * (1 + |w.im|) := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have : |(w - 1).re| ≤ B + 1 := by
      simp only [sub_re, one_re]
      calc |w.re - 1| ≤ |w.re| + |(1 : ℝ)| := abs_sub _ _
        _ ≤ B + 1 := by rw [abs_one]; linarith
    have him : (w - 1).im = w.im := by simp
    rw [him]
    nlinarith [abs_nonneg w.im, abs_nonneg w.re]
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hB
  have hprod : ‖w‖ * ‖w - 1‖ ≤ ((B + 1) * (1 + |w.im|)) * ((B + 1) * (1 + |w.im|)) :=
    mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
  have hnn : 0 ≤ ‖w‖ * ‖w - 1‖ := by positivity
  rw [norm_div, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]
  nlinarith

/-- `|ξ(w)| ≤ C (1 + |Im w|)²` on `3/2 ≤ Re w ≤ 5/2`. -/
theorem exists_xi_bound_right : ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, 3 / 2 ≤ w.re → w.re ≤ 5 / 2 →
    ‖xi w‖ ≤ C * (1 + |w.im|) ^ 2 := by
  obtain ⟨G, hG⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc (3 / 4 : ℝ) (5 / 4))
    (f := Real.Gamma) fun x hx => (Real.differentiableAt_Gamma fun m h => by
      have := hx.1; have : (0 : ℝ) ≤ m := m.cast_nonneg; linarith).continuousAt.continuousWithinAt
  have hG0 : 0 ≤ G := (norm_nonneg _).trans (hG (3 / 4) ⟨le_rfl, by norm_num⟩)
  refine ⟨(5 / 2 + 1) ^ 2 * (G * 3), by positivity, fun w h1 h2 => ?_⟩
  have hw0 : w ≠ 0 := fun h => by rw [h] at h1; simp at h1; linarith
  have hw1 : w ≠ 1 := fun h => by rw [h] at h1; simp at h1; linarith
  have hre : 0 < w.re := by linarith
  have hΓ : Gammaℝ w ≠ 0 := Gammaℝ_ne_zero_of_re_pos hre
  have hΛ : completedRiemannZeta w = riemannZeta w * Gammaℝ w := by
    rw [riemannZeta_def_of_ne_zero hw0, div_mul_cancel₀ _ hΓ]
  have hζ : ‖riemannZeta w‖ ≤ 3 := by
    have := _root_.RHTower.norm_riemannZeta_le_of_le_re (σ₁ := 3 / 2) (by norm_num) h1
    norm_num at this ⊢; linarith
  have hGam : ‖Gammaℝ w‖ ≤ G := by
    rw [Gammaℝ_def, norm_mul, norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    have hz : 0 < (w / 2).re := by simp; linarith
    have hb := norm_Gamma_le_Gamma_re_div hz
    have hden : 1 ≤ 1 + (w / 2).im ^ 2 / ((w / 2).re + 1) ^ 2 := by
      have : 0 ≤ (w / 2).im ^ 2 / ((w / 2).re + 1) ^ 2 := by positivity
      linarith
    have hΓre : Real.Gamma (w / 2).re ≤ G := by
      have hmem : (w / 2).re ∈ Icc (3 / 4 : ℝ) (5 / 4) := by
        simp only [div_ofNat_re]; constructor <;> linarith
      have := hG _ hmem
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans this
    have hΓpos : 0 < Real.Gamma (w / 2).re := Real.Gamma_pos_of_pos hz
    have hpi : Real.pi ^ (-w / 2).re ≤ 1 := by
      apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three])
      simp; linarith
    calc Real.pi ^ (-w / 2).re * ‖Complex.Gamma (w / 2)‖ ≤ 1 * (Real.Gamma (w / 2).re / 1) := by
          refine mul_le_mul hpi (hb.trans ?_) (norm_nonneg _) zero_le_one
          exact div_le_div_of_nonneg_left hΓpos.le one_pos hden
      _ ≤ G := by rw [one_mul, div_one]; exact hΓre
  rw [xi_eq_half_mul hw0 hw1, hΛ, norm_mul, norm_mul]
  have hpoly := norm_mul_sub_one_le w (B := 5 / 2) (by rw [abs_of_pos hre]; exact h2)
  calc ‖w * (w - 1) / 2‖ * (‖riemannZeta w‖ * ‖Gammaℝ w‖) ≤
        ((5 / 2 + 1) ^ 2 * (1 + |w.im|) ^ 2) * (3 * G) := by
        gcongr
    _ = (5 / 2 + 1) ^ 2 * (G * 3) * (1 + |w.im|) ^ 2 := by ring

/-- `|ξ(w)| ≤ C (1 + |Im w|)^N` on `-3/2 ≤ Re w ≤ 5/2`. -/
theorem exists_xi_bound_wide : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ w : ℂ, -3 / 2 ≤ w.re → w.re ≤ 5 / 2 →
    ‖xi w‖ ≤ C * (1 + |w.im|) ^ N := by
  obtain ⟨C₁, N₁, hC₁, h₁⟩ := RHTower.LeeYang.exists_xi_bound_strip
  obtain ⟨C₂, hC₂, h₂⟩ := exists_xi_bound_right
  have hbox : IsCompact (Icc (-1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-2 : ℝ) 2) :=
    isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨B, hB⟩ := hbox.exists_bound_of_continuousOn (f := xi) xi_differentiable.continuous.continuousOn
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by rw [mem_reProdIm]; norm_num))
  refine ⟨C₁ + B + C₂, max N₁ 2, by positivity, fun w h1 h2 => ?_⟩
  have hT : 1 ≤ 1 + |w.im| := by linarith [abs_nonneg w.im]
  have hpow : ∀ k : ℕ, k ≤ max N₁ 2 → (1 + |w.im|) ^ k ≤ (1 + |w.im|) ^ max N₁ 2 :=
    fun k hk => pow_le_pow_right₀ hT hk
  have hP1 : 1 ≤ (1 + |w.im|) ^ max N₁ 2 := one_le_pow₀ hT
  rcases lt_or_ge w.re (-1 / 2) with hl | hl
  · -- reflection to the right
    have h := h₂ (1 - w) (by simp; linarith) (by simp; linarith)
    rw [xi_one_sub] at h
    have him : |(1 - w).im| = |w.im| := by simp
    rw [him] at h
    calc ‖xi w‖ ≤ C₂ * (1 + |w.im|) ^ 2 := h
      _ ≤ C₂ * (1 + |w.im|) ^ max N₁ 2 := mul_le_mul_of_nonneg_left (hpow 2 (le_max_right _ _)) hC₂
      _ ≤ (C₁ + B + C₂) * (1 + |w.im|) ^ max N₁ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  rcases lt_or_ge (3 / 2) w.re with hr | hr
  · calc ‖xi w‖ ≤ C₂ * (1 + |w.im|) ^ 2 := h₂ w hr.le h2
      _ ≤ C₂ * (1 + |w.im|) ^ max N₁ 2 := mul_le_mul_of_nonneg_left (hpow 2 (le_max_right _ _)) hC₂
      _ ≤ (C₁ + B + C₂) * (1 + |w.im|) ^ max N₁ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  rcases le_or_gt 2 |w.im| with ht | ht
  · have h := h₁ w hl hr ht
    have he : Real.exp (-(Real.pi * |w.im| / 4)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by have := Real.pi_pos; have := abs_nonneg w.im; nlinarith)
    have hp : |w.im| ^ N₁ ≤ (1 + |w.im|) ^ N₁ := pow_le_pow_left₀ (abs_nonneg _) (by linarith) _
    calc ‖xi w‖ ≤ C₁ * |w.im| ^ N₁ * Real.exp (-(Real.pi * |w.im| / 4)) := h
      _ ≤ C₁ * (1 + |w.im|) ^ N₁ * 1 := by gcongr
      _ ≤ C₁ * (1 + |w.im|) ^ max N₁ 2 := by
          rw [mul_one]; exact mul_le_mul_of_nonneg_left (hpow N₁ (le_max_left _ _)) hC₁
      _ ≤ (C₁ + B + C₂) * (1 + |w.im|) ^ max N₁ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · have hmem : w ∈ Icc (-1 / 2 : ℝ) (3 / 2) ×ℂ Icc (-2 : ℝ) 2 := by
      rw [mem_reProdIm]
      exact ⟨⟨hl, hr⟩, ⟨by linarith [neg_abs_le w.im], by linarith [le_abs_self w.im]⟩⟩
    calc ‖xi w‖ ≤ B := hB w hmem
      _ ≤ B * (1 + |w.im|) ^ max N₁ 2 := le_mul_of_one_le_right hB0 hP1
      _ ≤ (C₁ + B + C₂) * (1 + |w.im|) ^ max N₁ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-! ### The entire function `P_g` -/

/-- Coefficients of `u (u² - ¼) E*(u)`: `(u-½)ξ(1+2u)/4`, `(u+½)ξ(2u)/4`, `u(u²-¼)`; all entire. -/
def pA₁ (u : ℂ) : ℂ := (u - 1 / 2) * xi (1 + 2 * u) / 4
def pA₂ (u : ℂ) : ℂ := (u + 1 / 2) * xi (2 * u) / 4
def pA₃ (u : ℂ) : ℂ := u * (u ^ 2 - 1 / 4)

theorem differentiable_pA₁ : Differentiable ℂ pA₁ := fun u =>
  (((differentiableAt_id.sub_const _).mul (differentiable_xi_shift u)).div_const 4)

theorem differentiable_pA₂ : Differentiable ℂ pA₂ := fun u =>
  (((differentiableAt_id.add_const _).mul
    ((xi_differentiable.comp (by fun_prop : Differentiable ℂ fun v : ℂ => 2 * v)) u)).div_const 4)

theorem differentiable_pA₃ : Differentiable ℂ pA₃ := by unfold pA₃; fun_prop

theorem shape_entire_eq {u : ℂ} (hu : u ≠ 1 / 2) (h0 : u ≠ 0) (hm : u ≠ -(1 / 2)) (x Y : ℝ) :
    shape pA₁ pA₂ pA₃ u x Y = u * (u ^ 2 - 1 / 4) * EisAuto.completedEisenstein u x Y := by
  unfold shape pA₁ pA₂ pA₃ EisAuto.completedEisenstein eisensteinNumerator
  have ha : (1 + 2 * u) * (1 + 2 * u)⁻¹ = 1 :=
    mul_inv_cancel₀ fun h => hm (by linear_combination h / 2)
  have hb : (2 * u - 1) * (2 * u - 1)⁻¹ = 1 := mul_inv_cancel₀ fun h => hu (by linear_combination h / 2)
  have hc : u * u⁻¹ = 1 := mul_inv_cancel₀ h0
  generalize (Y : ℂ) ^ (1 / 2 - u) = Q
  generalize (Y : ℂ) ^ (1 / 2 + u) = P
  generalize eisTail u x Y = T
  generalize xi (1 + 2 * u) = ξ₁
  generalize xi (2 * u) = ξ₂
  simp only [div_eq_mul_inv, mul_inv]
  linear_combination
    (-((u - 1 / 2) / 4 * ξ₁ * P * (u * u⁻¹)) - (u + 1 / 2) / 4 * ξ₂ * Q * (u * u⁻¹) -
      (u ^ 2 - 1 / 4) * u * T * (u * u⁻¹)) * ha +
    (-((u + 1 / 2) / 4 * ξ₂ * Q * ((1 + 2 * u) * (1 + 2 * u)⁻¹) * (u * u⁻¹))) * hb +
    (-((u - 1 / 2) / 4 * ξ₁ * P) - (u + 1 / 2) / 4 * ξ₂ * Q - (u ^ 2 - 1 / 4) * u * T) * hc

/-- `P_g(s) = ∫_𝒟 |g|² · (u(u²-¼)E*(u))|_{u = s - ½}`. -/
def entireRS (g : UpperHalfPlane → ℂ) (s : ℂ) : ℂ :=
  ∫ z in ModularGroup.fd, ((‖g z‖ ^ 2 : ℝ) : ℂ) * shape pA₁ pA₂ pA₃ (s - 1 / 2) z.re z.im

/-- **`P_g` is entire.** -/
theorem differentiable_entireRS (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) :
    Differentiable ℂ (entireRS g) := by
  have hI := differentiableOn_integral_shape hg hρ0 hρ isOpen_univ differentiable_pA₁.differentiableOn
    differentiable_pA₂.differentiableOn differentiable_pA₃.differentiableOn
  have hI' : Differentiable ℂ (fun u => ∫ z in ModularGroup.fd, ((‖g z‖ ^ 2 : ℝ) : ℂ) *
      shape pA₁ pA₂ pA₃ u z.re z.im) := differentiableOn_univ.1 hI
  exact hI'.comp (differentiable_id.sub_const _)

theorem entireRS_eq {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1 / 2) (h2 : s ≠ 1) :
    entireRS g s = s * (s - 1 / 2) * (s - 1) * completedRS g s := by
  unfold entireRS completedRS
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [shape_entire_eq (fun h => h2 (by linear_combination h)) (fun h => h1 (by linear_combination h))
    (fun h => h0 (by linear_combination h))]
  ring

/-- **`P_g(1 - s) = -P_g(s)`.** -/
theorem entireRS_one_sub (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) (s : ℂ) :
    entireRS g (1 - s) = -entireRS g s := by
  have hd := differentiable_entireRS hg hρ0 hρ
  have hdense : Dense (({0, 1 / 2, 1} : Set ℂ)ᶜ) :=
    (Set.toFinite _).countable.dense_compl ℂ
  have h := Continuous.ext_on hdense (f := fun s => entireRS g (1 - s)) (g := fun s => -entireRS g s)
    (hd.continuous.comp (continuous_const.sub continuous_id)) hd.continuous.neg (fun s hs => by
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or] at hs
      obtain ⟨h0, h1, h2⟩ := hs
      show entireRS g (1 - s) = -entireRS g s
      rw [entireRS_eq (fun h => h2 (by linear_combination -h)) (fun h => h1 (by linear_combination -h))
        (fun h => h0 (by linear_combination -h)), completedRS_one_sub h0 h1 h2, entireRS_eq h0 h1 h2]
      ring)
  exact congrFun h s


/-! ### Polynomial growth in the strip -/

theorem exists_shape_bound_uniform {R : ℝ} (hR : 0 ≤ R) : ∃ Ct : ℝ, 0 ≤ Ct ∧
    ∀ (A₁ A₂ A₃ : ℂ → ℂ) (u : ℂ) (x Y : ℝ), |u.re| ≤ R → 1 / 2 ≤ Y →
      ‖shape A₁ A₂ A₃ u x Y‖ ≤
        (‖A₁ u‖ + ‖A₂ u‖ + ‖A₃ u‖) * (Y ^ (R + 1 / 2) + (2 ^ (R + 1 / 2) + 2 * Ct)) := by
  obtain ⟨Ct, hCt0, hCt⟩ := norm_weightedTail_le hR
  refine ⟨Ct, hCt0, fun A₁ A₂ A₃ u x Y hre hY => ?_⟩
  have hre' := abs_le.1 hre
  have hw1 : |(1 / 2 + u).re| ≤ R + 1 / 2 := by
    have : (1 / 2 + u).re = 1 / 2 + u.re := by simp
    rw [this, abs_le]; constructor <;> linarith
  have hw2 : |(1 / 2 - u).re| ≤ R + 1 / 2 := by
    have : (1 / 2 - u).re = 1 / 2 - u.re := by simp
    rw [this, abs_le]; constructor <;> linarith
  have hP1 := norm_cpow_le hY (by positivity) hw1
  have hP2 := norm_cpow_le hY (by positivity) hw2
  have hT : ‖eisTail u x Y‖ ≤ 2 * Ct := by
    unfold eisTail
    refine (norm_add_le _ _).trans ?_
    linarith [hCt u false x Y hre hY, hCt u true x Y hre hY]
  have hYa : 0 ≤ Y ^ (R + 1 / 2) := Real.rpow_nonneg (by linarith) _
  have h2a : 0 ≤ (2 : ℝ) ^ (R + 1 / 2) := Real.rpow_nonneg (by norm_num) _
  have hS1 : Y ^ (R + 1 / 2) + 2 ^ (R + 1 / 2) ≤ Y ^ (R + 1 / 2) + (2 ^ (R + 1 / 2) + 2 * Ct) := by
    linarith
  have hS2 : 2 * Ct ≤ Y ^ (R + 1 / 2) + (2 ^ (R + 1 / 2) + 2 * Ct) := by linarith
  unfold shape
  calc _ ≤ ‖A₁ u * (Y : ℂ) ^ (1 / 2 + u)‖ + ‖A₂ u * (Y : ℂ) ^ (1 / 2 - u)‖ +
        ‖A₃ u * eisTail u x Y‖ := norm_add₃_le
    _ ≤ ‖A₁ u‖ * (Y ^ (R + 1 / 2) + (2 ^ (R + 1 / 2) + 2 * Ct)) +
        ‖A₂ u‖ * (Y ^ (R + 1 / 2) + (2 ^ (R + 1 / 2) + 2 * Ct)) +
        ‖A₃ u‖ * (Y ^ (R + 1 / 2) + (2 ^ (R + 1 / 2) + 2 * Ct)) := by
        rw [norm_mul, norm_mul, norm_mul]
        gcongr
        · exact hP1.trans hS1
        · exact hP2.trans hS1
        · exact hT.trans hS2
    _ = _ := by ring

theorem exists_integral_bound (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {R : ℝ} (hR : 0 ≤ R) :
    ∃ I₀ : ℝ, 0 ≤ I₀ ∧ ∀ (A₁ A₂ A₃ : ℂ → ℂ) (u : ℂ), |u.re| ≤ R →
      ‖∫ z in ModularGroup.fd, ((‖g z‖ ^ 2 : ℝ) : ℂ) * shape A₁ A₂ A₃ u z.re z.im‖ ≤
        (‖A₁ u‖ + ‖A₂ u‖ + ‖A₃ u‖) * I₀ := by
  obtain ⟨Ct, hCt0, hb⟩ := exists_shape_bound_uniform hR
  have hfd : MeasurableSet ModularGroup.fd := ModularGroup.isClosed_fd.measurableSet
  set β := (2 : ℝ) ^ (R + 1 / 2) + 2 * Ct
  have hβ : 0 ≤ β := by have := Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (R + 1 / 2); positivity
  set W : ℍ → ℝ := fun z => ‖g z‖ ^ 2 * (1 * z.im ^ (R + 1 / 2) + β)
  obtain ⟨B, hB⟩ := exists_bound_on_fd hg hρ0 hρ zero_le_one hβ (by positivity : 0 ≤ R + 1 / 2)
  have hvol : volume ModularGroup.fd ≠ ⊤ := by rw [volume_fd_eq]; exact ENNReal.ofReal_ne_top
  have hWint : IntegrableOn W ModularGroup.fd := by
    refine Measure.integrableOn_of_bounded (M := B) hvol ?_ ?_
    · exact ((((continuous_of_maass hg.2.1).norm.pow 2).mul
        ((continuous_const.mul (UpperHalfPlane.continuous_im.rpow_const fun z =>
          Or.inl (ne_of_gt z.im_pos))).add continuous_const))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem hfd] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (by have := z.im_pos; positivity)]
      exact hB z hz
  refine ⟨∫ z in ModularGroup.fd, W z, setIntegral_nonneg hfd fun z _ => by
    have := z.im_pos; positivity, fun A₁ A₂ A₃ u hu => ?_⟩
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hWint.const_mul _) ((ae_restrict_iff' hfd).2
    (Eventually.of_forall fun z hz => ?_))
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
  have h := hb A₁ A₂ A₃ u z.re z.im hu (half_lt_im_of_mem_fd hz).le
  calc ‖g z‖ ^ 2 * ‖shape A₁ A₂ A₃ u z.re z.im‖ ≤
        ‖g z‖ ^ 2 * ((‖A₁ u‖ + ‖A₂ u‖ + ‖A₃ u‖) * (z.im ^ (R + 1 / 2) + β)) :=
        mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ = (‖A₁ u‖ + ‖A₂ u‖ + ‖A₃ u‖) * W z := by simp only [W]; ring

/-- `‖P_g(s)‖ ≤ K (1 + |Im s|)^N` on `-¼ ≤ Re s ≤ 5/4`. -/
theorem exists_entireRS_poly (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) :
    ∃ K : ℝ, ∃ N : ℕ, 0 ≤ K ∧ ∀ s : ℂ, -1 / 4 ≤ s.re → s.re ≤ 5 / 4 →
      ‖entireRS g s‖ ≤ K * (1 + |s.im|) ^ N := by
  obtain ⟨I₀, hI₀, hI⟩ := exists_integral_bound hg hρ0 hρ (R := 3 / 4) (by norm_num)
  obtain ⟨Cξ, Nξ, hCξ, hξ⟩ := exists_xi_bound_wide
  refine ⟨(2 * (Cξ * 2 ^ Nξ) + 2) * I₀, Nξ + 3, by positivity, fun s h1 h2 => ?_⟩
  set u := s - 1 / 2 with hu
  have hure : u.re = s.re - 1 / 2 := by simp [hu]
  have huim : u.im = s.im := by simp [hu]
  have hure' : |u.re| ≤ 3 / 4 := by rw [hure, abs_le]; constructor <;> linarith
  set X := 1 + |s.im|
  have hX : 1 ≤ X := by simp only [X]; linarith [abs_nonneg s.im]
  have hX0 : 0 ≤ X := by linarith
  have hnu : ‖u‖ ≤ X := by
    refine (Complex.norm_le_abs_re_add_abs_im u).trans ?_
    rw [huim]; simp only [X]; linarith
  have hpow : ∀ k : ℕ, k ≤ Nξ + 3 → X ^ k ≤ X ^ (Nξ + 3) := fun k hk => pow_le_pow_right₀ hX hk
  have hxi : ∀ w : ℂ, -3 / 2 ≤ w.re → w.re ≤ 5 / 2 → |w.im| = 2 * |s.im| →
      ‖xi w‖ ≤ Cξ * 2 ^ Nξ * X ^ Nξ := by
    intro w hw1 hw2 hwim
    have h := hξ w hw1 hw2
    rw [hwim] at h
    calc _ ≤ Cξ * (1 + 2 * |s.im|) ^ Nξ := h
      _ ≤ Cξ * (2 * X) ^ Nξ := by
          gcongr; simp only [X]; linarith [abs_nonneg s.im]
      _ = Cξ * 2 ^ Nξ * X ^ Nξ := by rw [mul_pow]; ring
  have hx1 := hxi (1 + 2 * u) (by simp [hure]; linarith) (by simp [hure]; linarith)
    (by simp [huim, abs_mul])
  have hx2 := hxi (2 * u) (by simp [hure]; linarith) (by simp [hure]; linarith)
    (by simp [huim, abs_mul])
  have hh : ‖u - 1 / 2‖ ≤ 2 * X := by
    refine (norm_sub_le _ _).trans ?_; norm_num; linarith
  have hh' : ‖u + 1 / 2‖ ≤ 2 * X := by
    refine (norm_add_le _ _).trans ?_; norm_num; linarith
  have hA₁ : ‖pA₁ u‖ ≤ Cξ * 2 ^ Nξ * X ^ (Nξ + 3) := by
    unfold pA₁
    rw [norm_div, norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num]
    calc ‖u - 1 / 2‖ * ‖xi (1 + 2 * u)‖ / 4 ≤ (2 * X) * (Cξ * 2 ^ Nξ * X ^ Nξ) / 4 := by gcongr
      _ = Cξ * 2 ^ Nξ * X ^ (Nξ + 1) / 2 := by ring
      _ ≤ Cξ * 2 ^ Nξ * X ^ (Nξ + 3) := by
          have h3 := mul_le_mul_of_nonneg_left (hpow (Nξ + 1) (by omega))
            (by positivity : 0 ≤ Cξ * 2 ^ Nξ)
          have : 0 ≤ Cξ * 2 ^ Nξ * X ^ (Nξ + 1) := by positivity
          linarith
  have hA₂ : ‖pA₂ u‖ ≤ Cξ * 2 ^ Nξ * X ^ (Nξ + 3) := by
    unfold pA₂
    rw [norm_div, norm_mul, show ‖(4 : ℂ)‖ = 4 by norm_num]
    calc ‖u + 1 / 2‖ * ‖xi (2 * u)‖ / 4 ≤ (2 * X) * (Cξ * 2 ^ Nξ * X ^ Nξ) / 4 := by gcongr
      _ = Cξ * 2 ^ Nξ * X ^ (Nξ + 1) / 2 := by ring
      _ ≤ Cξ * 2 ^ Nξ * X ^ (Nξ + 3) := by
          have h3 := mul_le_mul_of_nonneg_left (hpow (Nξ + 1) (by omega))
            (by positivity : 0 ≤ Cξ * 2 ^ Nξ)
          have : 0 ≤ Cξ * 2 ^ Nξ * X ^ (Nξ + 1) := by positivity
          linarith
  have hA₃ : ‖pA₃ u‖ ≤ 2 * X ^ (Nξ + 3) := by
    unfold pA₃
    rw [norm_mul]
    have h3 : ‖u ^ 2 - 1 / 4‖ ≤ X ^ 2 + 1 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_pow]; norm_num
      nlinarith [norm_nonneg u]
    calc ‖u‖ * ‖u ^ 2 - 1 / 4‖ ≤ X * (X ^ 2 + 1) := mul_le_mul hnu h3 (norm_nonneg _) hX0
      _ ≤ 2 * X ^ 3 := by nlinarith
      _ ≤ 2 * X ^ (Nξ + 3) := by have := hpow 3 (by omega); linarith
  have hP := hI pA₁ pA₂ pA₃ u hure'
  unfold entireRS
  calc _ ≤ (‖pA₁ u‖ + ‖pA₂ u‖ + ‖pA₃ u‖) * I₀ := hP
    _ ≤ (Cξ * 2 ^ Nξ * X ^ (Nξ + 3) + Cξ * 2 ^ Nξ * X ^ (Nξ + 3) + 2 * X ^ (Nξ + 3)) * I₀ := by
        gcongr
    _ = (2 * (Cξ * 2 ^ Nξ) + 2) * I₀ * X ^ (Nξ + 3) := by ring

/-! ### Decay on the line `Re s = 5/4` -/

theorem xi_mul_gammaFactor {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1 / 2) (ν : ℂ) :
    xi (2 * s) * CuspRSI.gammaFactor ν s = s * (2 * s - 1) * (Real.pi : ℂ) ^ (-s) *
      riemannZeta (2 * s) * (2 : ℂ) ^ (s - 3) * (Gamma ((s + ν + ν) / 2) * Gamma ((s + ν - ν) / 2) *
        Gamma ((s - ν + ν) / 2) * Gamma ((s - ν - ν) / 2)) := by
  have h20 : 2 * s ≠ 0 := mul_ne_zero two_ne_zero fun h => by rw [h] at hs; simp at hs
  have h21 : 2 * s ≠ 1 := fun h => h1 (by linear_combination h / 2)
  have hΓ : Gammaℝ (2 * s) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simp; linarith)
  have hΛ : completedRiemannZeta (2 * s) = riemannZeta (2 * s) * Gammaℝ (2 * s) := by
    rw [riemannZeta_def_of_ne_zero h20, div_mul_cancel₀ _ hΓ]
  have hG : Gammaℝ (2 * s) = (Real.pi : ℂ) ^ (-s) * Gamma s := by
    rw [Gammaℝ_def, show -(2 * s) / 2 = -s by ring, show 2 * s / 2 = s by ring]
  have hΓs : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos hs
  rw [xi_eq_half_mul h20 h21, hΛ, hG]
  unfold CuspRSI.gammaFactor
  field_simp

theorem norm_tsum_rs_le (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {s : ℂ} (hs : 1 < s.re) :
    ‖∑' n : ℤ, ((‖ρ n‖ ^ 2 : ℝ) : ℂ) * ((|(n : ℝ)| : ℝ) : ℂ) ^ (-s)‖ ≤
      ∑' n : ℤ, ‖ρ n‖ ^ 2 * |(n : ℝ)| ^ (-s.re) := by
  have hsum := summable_sq_all hg hρ0 hρ hs
  have hterm : ∀ n : ℤ, ‖((‖ρ n‖ ^ 2 : ℝ) : ℂ) * ((|(n : ℝ)| : ℝ) : ℂ) ^ (-s)‖ =
      ‖ρ n‖ ^ 2 * |(n : ℝ)| ^ (-s.re) := by
    intro n
    by_cases hn : n = 0
    · subst hn; simp [hρ0]
    · have hpos : 0 < |(n : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hn)
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _),
        norm_cpow_eq_rpow_re_of_pos hpos, neg_re]
  refine (norm_tsum_le_tsum_norm (hsum.congr fun n => (hterm n).symm)).trans (le_of_eq ?_)
  exact tsum_congr hterm

/-- `‖P_g(s)‖ ≤ D (1 + |Im s|)^N e^{-π|Im s|}` on `Re s = 5/4`, `|Im s| ≥ 1`. -/
theorem exists_entireRS_right (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) :
    ∃ D : ℝ, ∃ N : ℕ, 0 ≤ D ∧ ∀ s : ℂ, s.re = 5 / 4 → 1 ≤ |s.im| →
      ‖entireRS g s‖ ≤ D * (1 + |s.im|) ^ N * Real.exp (-(Real.pi * |s.im|)) := by
  obtain ⟨CΓ, NΓ, hCΓ, hΓ⟩ := _root_.RHTower.exists_bound_norm_Gamma_vertical_line (5 / 8) (by norm_num)
  set t₀ := Real.sqrt (lamE - 1 / 4)
  set L₀ := ∑' n : ℤ, ‖ρ n‖ ^ 2 * |(n : ℝ)| ^ (-(5 / 4 : ℝ))
  have hL₀ : 0 ≤ L₀ := tsum_nonneg fun n => by positivity
  refine ⟨2 * L₀ * CΓ ^ 4 * (1 + |t₀|) ^ (2 * NΓ), 4 * NΓ + 3, by positivity, fun s hs ht => ?_⟩
  set T := s.im
  have hs0 : s ≠ 0 := fun h => by rw [h] at hs; norm_num at hs
  have hs1 : s ≠ 1 / 2 := fun h => by rw [h] at hs; norm_num at hs
  have hs2 : s ≠ 1 := fun h => by rw [h] at hs; norm_num at hs
  have hsre : 1 < s.re := by rw [hs]; norm_num
  have him : s.im ≠ 0 := fun h => by simp only [T] at ht; rw [h] at ht; norm_num at ht
  have hseq : s = ((5 / 4 : ℝ) : ℂ) + (T : ℂ) * I := by
    apply Complex.ext <;> simp [hs, T]
  have hν : nu lamE = (t₀ : ℂ) * I := rfl
  -- the identity on the line
  have hP : entireRS g s = (s - 1) / 4 * (xi (2 * s) * CuspRSI.gammaFactor (nu lamE) s) *
      ((2 * Real.pi : ℂ) ^ (-s) * ∑' n : ℤ, ((‖ρ n‖ ^ 2 : ℝ) : ℂ) * ((|(n : ℝ)| : ℝ) : ℂ) ^ (-s)) := by
    rw [entireRS_eq hs0 hs1 hs2, completedRS_eq hg hρ0 hρ hsre him]
    have h2s : 2 * s ≠ 0 := mul_ne_zero two_ne_zero hs0
    have h2s1 : 2 * s - 1 ≠ 0 := fun h => hs1 (by linear_combination h / 2)
    have hinv : (2 * s * (2 * s - 1))⁻¹ * (2 * s * (2 * s - 1)) = 1 :=
      inv_mul_cancel₀ (mul_ne_zero h2s h2s1)
    generalize CuspRSI.gammaFactor (nu lamE) s = G
    generalize (∑' n : ℤ, ((‖ρ n‖ ^ 2 : ℝ) : ℂ) * ((|(n : ℝ)| : ℝ) : ℂ) ^ (-s)) = Sg
    generalize (2 * Real.pi : ℂ) ^ (-s) = Q
    generalize xi (2 * s) = ξ
    rw [div_eq_mul_inv]
    linear_combination ((s - 1) / 4 * ξ * Q * G * Sg) * hinv
  rw [hP, xi_mul_gammaFactor (by rw [hs]; norm_num) hs1]
  -- Gamma factors on `Re = 5/8`
  have ha : ∀ y : ℝ, ‖Gamma (((5 / 8 : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
      CΓ * (1 + |y|) ^ NΓ * Real.exp (-(Real.pi * |y| / 2)) := hΓ
  have e1 : (s + nu lamE + nu lamE) / 2 = ((5 / 8 : ℝ) : ℂ) + ((T / 2 + t₀ : ℝ) : ℂ) * I := by
    rw [hseq, hν]; apply Complex.ext <;> simp <;> ring
  have e2 : (s + nu lamE - nu lamE) / 2 = ((5 / 8 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I := by
    rw [show (s + nu lamE - nu lamE) / 2 = s / 2 by ring, hseq]; push_cast; ring
  have e3 : (s - nu lamE + nu lamE) / 2 = ((5 / 8 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I := by
    rw [show (s - nu lamE + nu lamE) / 2 = s / 2 by ring, hseq]; push_cast; ring
  have e4 : (s - nu lamE - nu lamE) / 2 = ((5 / 8 : ℝ) : ℂ) + ((T / 2 - t₀ : ℝ) : ℂ) * I := by
    rw [hseq, hν]; apply Complex.ext <;> simp <;> ring
  rw [e1, e2, e3, e4]
  set X := 1 + |T|
  have hX : 1 ≤ X := by simp only [X]; linarith [abs_nonneg T]
  have hX0 : 0 ≤ X := by linarith
  have hT1 : 1 + |T / 2 + t₀| ≤ (1 + |t₀|) * X := by
    have := abs_add_le (T / 2) t₀
    have : |T / 2| ≤ |T| := by rw [abs_div, abs_two]; linarith [abs_nonneg T]
    nlinarith [abs_nonneg t₀, abs_nonneg T]
  have hT4 : 1 + |T / 2 - t₀| ≤ (1 + |t₀|) * X := by
    have := abs_sub (T / 2) t₀
    have : |T / 2| ≤ |T| := by rw [abs_div, abs_two]; linarith [abs_nonneg T]
    nlinarith [abs_nonneg t₀, abs_nonneg T]
  have hT2 : 1 + |T / 2| ≤ X := by
    have : |T / 2| ≤ |T| := by rw [abs_div, abs_two]; linarith [abs_nonneg T]
    simp only [X]; linarith
  have hexp : Real.exp (-(Real.pi * |T / 2 + t₀| / 2)) * Real.exp (-(Real.pi * |T / 2| / 2)) *
      Real.exp (-(Real.pi * |T / 2| / 2)) * Real.exp (-(Real.pi * |T / 2 - t₀| / 2)) ≤
      Real.exp (-(Real.pi * |T|)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 : |T| ≤ |T / 2 + t₀| + |T / 2 - t₀| := by
      calc |T| = |(T / 2 + t₀) + (T / 2 - t₀)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    have h2 : |T / 2| = |T| / 2 := by rw [abs_div, abs_two]
    rw [h2]
    nlinarith [Real.pi_pos]
  have hgam : ‖Gamma (((5 / 8 : ℝ) : ℂ) + ((T / 2 + t₀ : ℝ) : ℂ) * I) *
      Gamma (((5 / 8 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I) * Gamma (((5 / 8 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I) *
      Gamma (((5 / 8 : ℝ) : ℂ) + ((T / 2 - t₀ : ℝ) : ℂ) * I)‖ ≤
      CΓ ^ 4 * (1 + |t₀|) ^ (2 * NΓ) * X ^ (4 * NΓ) * Real.exp (-(Real.pi * |T|)) := by
    rw [norm_mul, norm_mul, norm_mul]
    have g1 := ha (T / 2 + t₀)
    have g2 := ha (T / 2)
    have g4 := ha (T / 2 - t₀)
    have p1 : (1 + |T / 2 + t₀|) ^ NΓ ≤ ((1 + |t₀|) * X) ^ NΓ := pow_le_pow_left₀ (by positivity) hT1 _
    have p2 : (1 + |T / 2|) ^ NΓ ≤ X ^ NΓ := pow_le_pow_left₀ (by positivity) hT2 _
    have p4 : (1 + |T / 2 - t₀|) ^ NΓ ≤ ((1 + |t₀|) * X) ^ NΓ := pow_le_pow_left₀ (by positivity) hT4 _
    calc _ ≤ (CΓ * (1 + |T / 2 + t₀|) ^ NΓ * Real.exp (-(Real.pi * |T / 2 + t₀| / 2))) *
          (CΓ * (1 + |T / 2|) ^ NΓ * Real.exp (-(Real.pi * |T / 2| / 2))) *
          (CΓ * (1 + |T / 2|) ^ NΓ * Real.exp (-(Real.pi * |T / 2| / 2))) *
          (CΓ * (1 + |T / 2 - t₀|) ^ NΓ * Real.exp (-(Real.pi * |T / 2 - t₀| / 2))) := by gcongr
      _ ≤ (CΓ * ((1 + |t₀|) * X) ^ NΓ * Real.exp (-(Real.pi * |T / 2 + t₀| / 2))) *
          (CΓ * X ^ NΓ * Real.exp (-(Real.pi * |T / 2| / 2))) *
          (CΓ * X ^ NΓ * Real.exp (-(Real.pi * |T / 2| / 2))) *
          (CΓ * ((1 + |t₀|) * X) ^ NΓ * Real.exp (-(Real.pi * |T / 2 - t₀| / 2))) := by gcongr
      _ = CΓ ^ 4 * (1 + |t₀|) ^ (2 * NΓ) * X ^ (4 * NΓ) *
          (Real.exp (-(Real.pi * |T / 2 + t₀| / 2)) * Real.exp (-(Real.pi * |T / 2| / 2)) *
            Real.exp (-(Real.pi * |T / 2| / 2)) * Real.exp (-(Real.pi * |T / 2 - t₀| / 2))) := by
          rw [mul_pow]; ring
      _ ≤ _ := by gcongr
  -- the remaining factors
  have hsn : ‖s‖ ≤ 2 * X := by
    refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
    rw [hs]; simp only [X, T]; norm_num; linarith [abs_nonneg s.im]
  have hs1n : ‖s - 1‖ ≤ X := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp [hs, X, T]; norm_num
  have h2s1n : ‖2 * s - 1‖ ≤ 2 * X := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp [hs, X, T, abs_mul]; norm_num; linarith [abs_nonneg s.im]
  have hpi : ‖(Real.pi : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [norm_cpow_eq_rpow_re_of_pos Real.pi_pos, neg_re, hs]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by norm_num)
  have h2pi : ‖(2 * Real.pi : ℂ) ^ (-s)‖ ≤ 1 := by
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      norm_cpow_eq_rpow_re_of_pos (by positivity), neg_re, hs]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by norm_num)
  have h2 : ‖(2 : ℂ) ^ (s - 3)‖ ≤ 1 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, norm_cpow_eq_rpow_re_of_pos (by norm_num), sub_re, hs]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hζ : ‖riemannZeta (2 * s)‖ ≤ 2 := by
    have := _root_.RHTower.norm_riemannZeta_le_of_le_re (σ₁ := 5 / 2) (by norm_num)
      (s := 2 * s) (by simp [hs]; norm_num)
    norm_num at this ⊢; linarith
  have hLs := norm_tsum_rs_le hg hρ0 hρ hsre
  rw [hs] at hLs
  generalize Gamma (((5 / 8 : ℝ) : ℂ) + ((T / 2 + t₀ : ℝ) : ℂ) * I) *
      Gamma (((5 / 8 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I) * Gamma (((5 / 8 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * I) *
      Gamma (((5 / 8 : ℝ) : ℂ) + ((T / 2 - t₀ : ℝ) : ℂ) * I) = Gp at hgam ⊢
  simp only [norm_mul, norm_div, show ‖(4 : ℂ)‖ = 4 by norm_num]
  have hgam0 : 0 ≤ CΓ ^ 4 * (1 + |t₀|) ^ (2 * NΓ) * X ^ (4 * NΓ) * Real.exp (-(Real.pi * |T|)) := by
    positivity
  calc _ ≤ X / 4 * (2 * X * (2 * X) * 1 * 2 * 1 *
        (CΓ ^ 4 * (1 + |t₀|) ^ (2 * NΓ) * X ^ (4 * NΓ) * Real.exp (-(Real.pi * |T|)))) * (1 * L₀) := by
        gcongr
    _ = 2 * L₀ * CΓ ^ 4 * (1 + |t₀|) ^ (2 * NΓ) * X ^ (4 * NΓ + 3) * Real.exp (-(Real.pi * |T|)) := by
        ring

/-! ### Phragmén–Lindelöf -/

/-- **Phragmén–Lindelöf on a vertical strip**, with exponential growth inside. -/
theorem norm_le_of_strip {f : ℂ → ℂ} {a b C K L : ℝ} (hab : a < b)
    (hf : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → DifferentiableAt ℂ f z)
    (hgrow : ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ‖f z‖ ≤ K * Real.exp (L * |z.im|))
    (ha : ∀ z : ℂ, z.re = a → ‖f z‖ ≤ C) (hb : ∀ z : ℂ, z.re = b → ‖f z‖ ≤ C)
    {z : ℂ} (hza : a ≤ z.re) (hzb : z.re ≤ b) : ‖f z‖ ≤ C := by
  have hdc : DiffContOnCl ℂ f (Complex.re ⁻¹' Ioo a b) := by
    have hcl : closure (Complex.re ⁻¹' Ioo a b) ⊆ Complex.re ⁻¹' Icc a b :=
      closure_minimal (preimage_mono Ioo_subset_Icc_self) (isClosed_Icc.preimage continuous_re)
    refine ⟨fun w hw => (hf w hw.1.le hw.2.le).differentiableWithinAt, fun w hw => ?_⟩
    have := hcl hw
    exact (hf w this.1 this.2).continuousAt.continuousWithinAt
  set c := Real.pi / (2 * (b - a))
  have hba : 0 < b - a := by linarith
  have hc0 : 0 < c := by positivity
  have hc : c < Real.pi / (b - a) := div_lt_div_of_pos_left Real.pi_pos hba (by linarith)
  refine PhragmenLindelof.vertical_strip hdc ⟨c, hc, 1, ?_⟩ ha hb hza hzb
  set X := 2 * |L| / c ^ 2 + 1
  have hev : ∀ᶠ w : ℂ in comap (abs ∘ Complex.im) atTop ⊓ 𝓟 (Complex.re ⁻¹' Ioo a b),
      X ≤ |w.im| ∧ w ∈ Complex.re ⁻¹' Ioo a b :=
    (((eventually_ge_atTop X).comap (abs ∘ Complex.im)).filter_mono inf_le_left).and
      (mem_inf_of_right (mem_principal_self _))
  refine IsBigO.of_bound (max K 0) ?_
  filter_upwards [hev] with w ⟨hwX, hwS⟩
  have hx0 : 0 ≤ |w.im| := abs_nonneg _
  have hX0 : 0 < X := by positivity
  have hLx : L * |w.im| ≤ Real.exp (c * |w.im|) := by
    have hq := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ c * |w.im|)
    have h1 : L * |w.im| ≤ |L| * |w.im| := mul_le_mul_of_nonneg_right (le_abs_self L) hx0
    have h2 : |L| * |w.im| ≤ (c * |w.im|) ^ 2 / 2 := by
      have hXw : 2 * |L| / c ^ 2 ≤ |w.im| := by simp only [X] at hwX; linarith
      rw [div_le_iff₀ (by positivity)] at hXw
      nlinarith [abs_nonneg L]
    nlinarith
  have hfw := hgrow w hwS.1.le hwS.2.le
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), one_mul]
  calc ‖f w‖ ≤ K * Real.exp (L * |w.im|) := hfw
    _ ≤ max K 0 * Real.exp (L * |w.im|) := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
    _ ≤ max K 0 * Real.exp (Real.exp (c * |w.im|)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hLx) (le_max_right _ _)


/-! ### The decay -/

/-- **`P_g(σ + it)` decays like `(1 + |t|)^N e^{-π|t|}` on `-¼ ≤ σ ≤ 5/4`.** -/
theorem exists_norm_entireRS_le (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ s : ℂ, -1 / 4 ≤ s.re → s.re ≤ 5 / 4 →
      ‖entireRS g s‖ ≤ C * (1 + |s.im|) ^ N * Real.exp (-(Real.pi * |s.im|)) := by
  have hd := differentiable_entireRS hg hρ0 hρ
  obtain ⟨K, Np, hK, hpoly⟩ := exists_entireRS_poly hg hρ0 hρ
  obtain ⟨D, Nd, hD, hright⟩ := exists_entireRS_right hg hρ0 hρ
  have hbox : IsCompact (Icc (-1 / 4 : ℝ) (5 / 4) ×ℂ Icc (-1 : ℝ) 1) :=
    isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨B₀, hB₀⟩ := hbox.exists_bound_of_continuousOn hd.continuous.continuousOn
  have hB₀0 : 0 ≤ B₀ := (norm_nonneg _).trans (hB₀ 0 (by rw [mem_reProdIm]; norm_num))
  set D' := D + B₀ * Real.exp Real.pi with hD'
  have hD'0 : 0 ≤ D' := by positivity
  -- the bound on both boundary lines, at every height
  have hR : ∀ s : ℂ, s.re = 5 / 4 →
      ‖entireRS g s‖ ≤ D' * (1 + |s.im|) ^ Nd * Real.exp (-(Real.pi * |s.im|)) := by
    intro s hs
    have hX : 1 ≤ (1 + |s.im|) ^ Nd := one_le_pow₀ (by linarith [abs_nonneg s.im])
    rcases le_or_gt 1 |s.im| with ht | ht
    · calc _ ≤ D * (1 + |s.im|) ^ Nd * Real.exp (-(Real.pi * |s.im|)) := hright s hs ht
        _ ≤ D' * (1 + |s.im|) ^ Nd * Real.exp (-(Real.pi * |s.im|)) := by
            gcongr
            have : 0 ≤ B₀ * Real.exp Real.pi := by positivity
            linarith
    · have hmem : s ∈ Icc (-1 / 4 : ℝ) (5 / 4) ×ℂ Icc (-1 : ℝ) 1 := by
        rw [mem_reProdIm, hs]
        exact ⟨⟨by norm_num, le_rfl⟩, ⟨by linarith [neg_abs_le s.im], by linarith [le_abs_self s.im]⟩⟩
      have he : 1 ≤ Real.exp Real.pi * Real.exp (-(Real.pi * |s.im|)) := by
        rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith [Real.pi_pos])
      have hE0 : 0 ≤ Real.exp (-(Real.pi * |s.im|)) := (Real.exp_pos _).le
      calc ‖entireRS g s‖ ≤ B₀ := hB₀ s hmem
        _ ≤ B₀ * Real.exp Real.pi * Real.exp (-(Real.pi * |s.im|)) := by nlinarith
        _ ≤ D' * Real.exp (-(Real.pi * |s.im|)) := by
            gcongr; linarith
        _ ≤ D' * (1 + |s.im|) ^ Nd * Real.exp (-(Real.pi * |s.im|)) := by
            have : 0 ≤ D' * Real.exp (-(Real.pi * |s.im|)) := by positivity
            nlinarith
  have hL : ∀ s : ℂ, s.re = -1 / 4 →
      ‖entireRS g s‖ ≤ D' * (1 + |s.im|) ^ Nd * Real.exp (-(Real.pi * |s.im|)) := by
    intro s hs
    have h := hR (1 - s) (by simp [hs]; norm_num)
    rw [entireRS_one_sub hg hρ0 hρ, norm_neg] at h
    have him : |(1 - s).im| = |s.im| := by simp
    rwa [him] at h
  have hz3 : ∀ z : ℂ, -1 / 4 ≤ z.re → z + 3 ≠ 0 := fun z hz h => by
    have := congrArg Complex.re h; simp at this; linarith
  have h3' : ∀ z : ℂ, -1 / 4 ≤ z.re → 1 + |z.im| ≤ 2 * ‖z + 3‖ := fun z hz => by
    have h1 := Complex.abs_re_le_norm (z + 3)
    have h2 := Complex.abs_im_le_norm (z + 3)
    have hre : (z + 3).re = z.re + 3 := by simp
    have him : (z + 3).im = z.im := by simp
    rw [hre, abs_of_pos (by linarith)] at h1
    rw [him] at h2
    linarith
  -- Phragmén–Lindelöf for `P_g(z) e^{-iεπz}/(z+3)^N`
  have key : ∀ ε : ℝ, |ε| = 1 → ∀ s : ℂ, -1 / 4 ≤ s.re → s.re ≤ 5 / 4 →
      ‖entireRS g s‖ * Real.exp (ε * Real.pi * s.im) ≤ D' * 2 ^ Nd * ‖s + 3‖ ^ Nd := by
    intro ε hε s hs1 hs2
    set F : ℂ → ℂ := fun z => entireRS g z * Complex.exp (-((ε * Real.pi : ℝ) * I) * z) / (z + 3) ^ Nd
      with hF
    have hnF : ∀ z : ℂ, -1 / 4 ≤ z.re →
        ‖F z‖ = ‖entireRS g z‖ * Real.exp (ε * Real.pi * z.im) / ‖z + 3‖ ^ Nd := by
      intro z hz
      simp only [hF, norm_div, norm_mul, norm_pow, Complex.norm_exp]
      congr 3
      simp [Complex.mul_re]
    have hexp : ∀ y : ℝ, Real.exp (ε * Real.pi * y) ≤ Real.exp (Real.pi * |y|) := fun y => by
      apply Real.exp_le_exp.2
      calc ε * Real.pi * y ≤ |ε * Real.pi * y| := le_abs_self _
        _ = Real.pi * |y| := by rw [abs_mul, abs_mul, hε, abs_of_pos Real.pi_pos, one_mul]
    have hbd : ∀ z : ℂ, (z.re = -1 / 4 ∨ z.re = 5 / 4) → ‖F z‖ ≤ D' * 2 ^ Nd := by
      intro z hz
      have hzre : -1 / 4 ≤ z.re := by
        rcases hz with h | h
        · exact h.symm.le
        · rw [h]; norm_num
      have hP : ‖entireRS g z‖ ≤ D' * (1 + |z.im|) ^ Nd * Real.exp (-(Real.pi * |z.im|)) := by
        rcases hz with h | h
        · exact hL z h
        · exact hR z h
      have hpos : 0 < ‖z + 3‖ ^ Nd := pow_pos (norm_pos_iff.2 (hz3 z hzre)) _
      rw [hnF z hzre, div_le_iff₀ hpos]
      have h1 : Real.exp (-(Real.pi * |z.im|)) * Real.exp (ε * Real.pi * z.im) ≤ 1 := by
        rw [← Real.exp_add]; apply Real.exp_le_one_iff.2; linarith [hexp z.im, Real.exp_le_exp.1 (hexp z.im)]
      have h2 : (1 + |z.im|) ^ Nd ≤ (2 * ‖z + 3‖) ^ Nd :=
        pow_le_pow_left₀ (by linarith [abs_nonneg z.im]) (h3' z hzre) _
      calc ‖entireRS g z‖ * Real.exp (ε * Real.pi * z.im) ≤
            D' * (1 + |z.im|) ^ Nd * Real.exp (-(Real.pi * |z.im|)) * Real.exp (ε * Real.pi * z.im) :=
            mul_le_mul_of_nonneg_right hP (Real.exp_pos _).le
        _ = D' * (1 + |z.im|) ^ Nd * (Real.exp (-(Real.pi * |z.im|)) * Real.exp (ε * Real.pi * z.im)) := by
            ring
        _ ≤ D' * (1 + |z.im|) ^ Nd * 1 := by gcongr
        _ ≤ D' * (2 * ‖z + 3‖) ^ Nd := by rw [mul_one]; gcongr
        _ = D' * 2 ^ Nd * ‖z + 3‖ ^ Nd := by rw [mul_pow]; ring
    have hPL := norm_le_of_strip (f := F) (a := -1 / 4) (b := 5 / 4) (C := D' * 2 ^ Nd) (K := K)
      (L := Np + Real.pi) (by norm_num)
      (fun z hz1 _ => ((hd z).mul ((differentiable_exp.comp (differentiable_id.const_mul _)) z)).div
        ((differentiable_id.add_const _).pow Nd z) (pow_ne_zero _ (hz3 z hz1)))
      (fun z hz1 _ => by
        have hpos : 1 ≤ ‖z + 3‖ ^ Nd := one_le_pow₀ (by
          have h := Complex.abs_re_le_norm (z + 3)
          have hre : (z + 3).re = z.re + 3 := by simp
          rw [hre, abs_of_pos (by linarith)] at h
          linarith)
        rw [hnF z hz1, div_le_iff₀ (by linarith)]
        have hP := hpoly z hz1 (by assumption)
        have hy : (1 + |z.im|) ^ Np ≤ Real.exp (Np * |z.im|) := by
          calc (1 + |z.im|) ^ Np ≤ (Real.exp |z.im|) ^ Np :=
                pow_le_pow_left₀ (by linarith [abs_nonneg z.im]) (by linarith [Real.add_one_le_exp |z.im|]) _
            _ = Real.exp (Np * |z.im|) := by rw [← Real.exp_nat_mul]
        have he : Real.exp (Np * |z.im|) * Real.exp (Real.pi * |z.im|) =
            Real.exp ((Np + Real.pi) * |z.im|) := by rw [← Real.exp_add]; ring_nf
        calc ‖entireRS g z‖ * Real.exp (ε * Real.pi * z.im) ≤
              K * (1 + |z.im|) ^ Np * Real.exp (Real.pi * |z.im|) :=
              mul_le_mul hP (hexp z.im) (Real.exp_pos _).le (by positivity)
          _ ≤ K * Real.exp (Np * |z.im|) * Real.exp (Real.pi * |z.im|) := by gcongr
          _ = K * Real.exp ((Np + Real.pi) * |z.im|) := by rw [mul_assoc, he]
          _ ≤ K * Real.exp ((Np + Real.pi) * |z.im|) * ‖z + 3‖ ^ Nd :=
              le_mul_of_one_le_right (by positivity) hpos)
      (fun z hz => hbd z (Or.inl hz)) (fun z hz => hbd z (Or.inr hz)) hs1 hs2
    rw [hnF s hs1, div_le_iff₀ (pow_pos (norm_pos_iff.2 (hz3 s hs1)) _)] at hPL
    exact hPL
  refine ⟨D' * 2 ^ Nd * (17 / 4) ^ Nd, Nd, by positivity, fun s hs1 hs2 => ?_⟩
  have hs3 : ‖s + 3‖ ≤ 17 / 4 * (1 + |s.im|) := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have hre : (s + 3).re = s.re + 3 := by simp
    have him : (s + 3).im = s.im := by simp
    rw [hre, him, abs_of_pos (by linarith)]
    nlinarith [abs_nonneg s.im]
  have hs3' : ‖s + 3‖ ^ Nd ≤ (17 / 4) ^ Nd * (1 + |s.im|) ^ Nd := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hs3 _
  have hε : |(if 0 ≤ s.im then (1 : ℝ) else -1)| = 1 := by split_ifs <;> norm_num
  have h := key _ hε s hs1 hs2
  have hsign : (if 0 ≤ s.im then (1 : ℝ) else -1) * Real.pi * s.im = Real.pi * |s.im| := by
    split_ifs with h0
    · rw [abs_of_nonneg h0]; ring
    · rw [abs_of_neg (not_le.1 h0)]; ring
  rw [hsign] at h
  have hE : 0 < Real.exp (Real.pi * |s.im|) := Real.exp_pos _
  have hinv : Real.exp (-(Real.pi * |s.im|)) * Real.exp (Real.pi * |s.im|) = 1 := by
    rw [← Real.exp_add]; simp
  calc ‖entireRS g s‖ = ‖entireRS g s‖ * Real.exp (Real.pi * |s.im|) * Real.exp (-(Real.pi * |s.im|)) := by
        rw [mul_assoc, mul_comm (Real.exp _), hinv, mul_one]
    _ ≤ D' * 2 ^ Nd * ‖s + 3‖ ^ Nd * Real.exp (-(Real.pi * |s.im|)) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ ≤ D' * 2 ^ Nd * ((17 / 4) ^ Nd * (1 + |s.im|) ^ Nd) * Real.exp (-(Real.pi * |s.im|)) := by
        gcongr
    _ = D' * 2 ^ Nd * (17 / 4) ^ Nd * (1 + |s.im|) ^ Nd * Real.exp (-(Real.pi * |s.im|)) := by ring

/-- **The Rankin–Selberg function decays like `e^{-π|t|}`**: on `-¼ ≤ Re s ≤ 5/4`, `|Im s| ≥ 1`,
`‖Λ_g(s)‖ ≤ C (1 + |Im s|)^N e^{-π|Im s|}`. -/
theorem exists_norm_completedRS_le (hg : g ∈ cuspSpace lamE) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ s : ℂ, -1 / 4 ≤ s.re → s.re ≤ 5 / 4 → 1 ≤ |s.im| →
      ‖completedRS g s‖ ≤ C * (1 + |s.im|) ^ N * Real.exp (-(Real.pi * |s.im|)) := by
  obtain ⟨C, N, hC, h⟩ := exists_norm_entireRS_le hg hρ0 hρ
  refine ⟨C, N, hC, fun s hs1 hs2 ht => ?_⟩
  have him0 : s.im ≠ 0 := fun h0 => by rw [h0] at ht; norm_num at ht
  have hs0 : s ≠ 0 := fun h => him0 (by rw [h]; simp)
  have hs1' : s ≠ 1 / 2 := fun h => him0 (by rw [h]; simp)
  have hs2' : s ≠ 1 := fun h => him0 (by rw [h]; simp)
  have hn : 1 ≤ ‖s * (s - 1 / 2) * (s - 1)‖ := by
    rw [norm_mul, norm_mul]
    have a1 : |s.im| ≤ ‖s‖ := Complex.abs_im_le_norm s
    have a2 : |s.im| ≤ ‖s - 1 / 2‖ := by simpa using Complex.abs_im_le_norm (s - 1 / 2)
    have a3 : |s.im| ≤ ‖s - 1‖ := by simpa using Complex.abs_im_le_norm (s - 1)
    have := mul_le_mul (mul_le_mul a1 a2 (abs_nonneg _) (norm_nonneg _)) a3 (abs_nonneg _) (by positivity)
    nlinarith
  have hP := h s hs1 hs2
  rw [entireRS_eq hs0 hs1' hs2', norm_mul] at hP
  calc ‖completedRS g s‖ ≤ ‖s * (s - 1 / 2) * (s - 1)‖ * ‖completedRS g s‖ :=
        le_mul_of_one_le_left (norm_nonneg _) hn
    _ ≤ _ := hP

end CuspRSV

end GaloisForLFunctions.BlackHoleRingdown
