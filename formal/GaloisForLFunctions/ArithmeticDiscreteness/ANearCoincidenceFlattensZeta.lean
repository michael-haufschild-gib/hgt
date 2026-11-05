import Mathlib
import GaloisForLFunctions.RHTower.SmoothAFEZetaStripBound

/-!
# A near-coincidence flattens zeta

The test of the discreteness route below RH is collide-or-repel for `ζ` (B54): distinct zeros at
height `T` at distance `≥ T^{−C}`. This module proves the unconditional half of its dictionary with
derivative bounds.

* **Two zeros flatten the derivative** (`norm_sub_taylor_le`, `norm_deriv_mul_le_of_two_zeros`).
  If `f` is holomorphic on a neighbourhood of `‖z − a‖ ≤ R`, bounded there by `M`, the Taylor
  remainder obeys `|f(b) − f(a) − f'(a)(b − a)| ≤ (8M/R²)|b − a|²` for `‖b − a‖ ≤ R/4`; if `f`
  vanishes at `a` and `b` this is `‖f'(a)‖ ‖b − a‖ ≤ (8M/R²) ‖b − a‖²`.
* **For zeta** (`norm_deriv_riemannZeta_mul_le_of_near_zero`). For a zero `ρ` in the strip with
  `|Im ρ| ≥ 3` and another zero `ρ'` within `1/8`,
  `‖ζ'(ρ)‖ ‖ρ' − ρ‖ ≤ 160 e² (|γ| + 2)(|γ| + 5) ‖ρ' − ρ‖²`, from the polynomial strip bound
  `RHTower.norm_riemannZeta_le_smoothAFE_strip`.
* **Collide or repel from a derivative bound** (`separation_of_norm_deriv_riemannZeta_ge`). If
  `‖ζ'(ρ)‖ ≥ c`, every other zero is at distance
  `≥ min(1/8, c / (160 e² (|γ| + 2)(|γ| + 5)))`. So a polynomial lower bound for `|ζ'|` at the
  zeros gives B54 with two more powers of the height; a multiple zero is a collision.
-/

open Complex Metric

noncomputable section

namespace GaloisForLFunctions.ArithmeticDiscreteness

/-- **Second-order Taylor bound.** If `f` is holomorphic on an open `U ⊇ closedBall a R` and
`|f| ≤ M` there, then `|f(b) − f(a) − f'(a)(b − a)| ≤ (8M/R²)|b − a|²` for `‖b − a‖ ≤ R/4`. Two
Cauchy estimates bound `f''` by `8M/R²` on `‖z − a‖ ≤ R/4`; the mean value inequality for
`f(z) − f'(a)(z − a)` along `[a, b]` gives the bound. -/
theorem norm_sub_taylor_le {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {a b : ℂ} {R M : ℝ} (hR : 0 < R) (hsub : closedBall a R ⊆ U)
    (hM : ∀ z ∈ closedBall a R, ‖f z‖ ≤ M) (hb : ‖b - a‖ ≤ R / 4) :
    ‖f b - f a - deriv f a * (b - a)‖ ≤ 8 * M / R ^ 2 * ‖b - a‖ ^ 2 := by
  have hdf : DifferentiableOn ℂ (deriv f) U := hf.deriv hU
  -- `|f'| ≤ 2M/R` on `‖z − a‖ ≤ R/2`
  have h1 : ∀ z ∈ closedBall a (R / 2), ‖deriv f z‖ ≤ M / (R / 2) := by
    intro z hz
    have hzsub : closedBall z (R / 2) ⊆ closedBall a R := by
      intro w hw
      rw [mem_closedBall] at hw hz ⊢
      linarith [dist_triangle w z a]
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity)
      (hf.diffContOnCl_ball (hzsub.trans hsub)) fun w hw => hM w (hzsub (sphere_subset_closedBall hw))
  -- `|f''| ≤ 8M/R²` on `‖z − a‖ ≤ R/4`
  have h2 : ∀ w ∈ closedBall a (R / 4), ‖deriv (deriv f) w‖ ≤ 8 * M / R ^ 2 := by
    intro w hw
    have hwsub : closedBall w (R / 4) ⊆ closedBall a (R / 2) := by
      intro u hu
      rw [mem_closedBall] at hu hw ⊢
      linarith [dist_triangle u w a]
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity)
      (hdf.diffContOnCl_ball ((hwsub.trans (closedBall_subset_closedBall (by linarith))).trans hsub))
      fun u hu => h1 u (hwsub (sphere_subset_closedBall hu))
    calc ‖deriv (deriv f) w‖ ≤ M / (R / 2) / (R / 4) := this
      _ = 8 * M / R ^ 2 := by field_simp; ring
  have hball : closedBall a (R / 4) ⊆ U := (closedBall_subset_closedBall (by linarith)).trans hsub
  have hdiff : ∀ z ∈ closedBall a (R / 4), DifferentiableAt ℂ f z := fun z hz =>
    hf.differentiableAt (hU.mem_nhds (hball hz))
  have hddiff : ∀ z ∈ closedBall a (R / 4), DifferentiableAt ℂ (deriv f) z := fun z hz =>
    hdf.differentiableAt (hU.mem_nhds (hball hz))
  have haball : a ∈ closedBall a (R / 4) := mem_closedBall_self (by positivity)
  have hbball : b ∈ closedBall a (R / 4) := by rw [mem_closedBall, dist_eq_norm]; exact hb
  -- on the segment `[a, b]`, `|f'(z) − f'(a)| ≤ (8M/R²)‖b − a‖`
  set g : ℂ → ℂ := fun z => f z - deriv f a * (z - a) with hg
  have hgderiv : ∀ z ∈ closedBall a (R / 4), HasDerivAt g (deriv f z - deriv f a) z := by
    intro z hz
    have := ((hdiff z hz).hasDerivAt).sub (((hasDerivAt_id z).sub_const a).const_mul (deriv f a))
    rw [mul_one] at this
    exact this
  have hseg : segment ℝ a b ⊆ closedBall a (R / 4) := (convex_closedBall a _).segment_subset haball hbball
  have hgbound : ∀ z ∈ segment ℝ a b, ‖deriv g z‖ ≤ 8 * M / R ^ 2 * ‖b - a‖ := by
    intro z hz
    rw [(hgderiv z (hseg hz)).deriv]
    have hmv := (convex_closedBall a (R / 4)).norm_image_sub_le_of_norm_deriv_le hddiff h2
      haball (hseg hz)
    have hza : ‖z - a‖ ≤ ‖b - a‖ := by
      obtain ⟨t, u, ht, hu, htu, rfl⟩ := hz
      have : t • a + u • b - a = u • (b - a) := by
        rw [show t = 1 - u by linarith]; simp only [sub_smul, one_smul, smul_sub]; abel
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg hu]
      exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
    have hc : 0 ≤ 8 * M / R ^ 2 := by
      have := (norm_nonneg (f a)).trans (hM a (mem_closedBall_self hR.le))
      positivity
    exact hmv.trans (mul_le_mul_of_nonneg_left hza hc)
  have hgmv := (convex_segment a b).norm_image_sub_le_of_norm_deriv_le
    (fun z hz => (hgderiv z (hseg hz)).differentiableAt) hgbound (left_mem_segment ℝ a b)
    (right_mem_segment ℝ a b)
  have hgab : g b - g a = f b - f a - deriv f a * (b - a) := by simp only [hg, sub_self, mul_zero, sub_zero]; ring
  rw [hgab] at hgmv
  calc ‖f b - f a - deriv f a * (b - a)‖ ≤ 8 * M / R ^ 2 * ‖b - a‖ * ‖b - a‖ := hgmv
    _ = 8 * M / R ^ 2 * ‖b - a‖ ^ 2 := by ring

/-- **Two zeros flatten the derivative.** -/
theorem norm_deriv_mul_le_of_two_zeros {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) {a b : ℂ} {R M : ℝ} (hR : 0 < R) (hsub : closedBall a R ⊆ U)
    (hM : ∀ z ∈ closedBall a R, ‖f z‖ ≤ M) (hb : ‖b - a‖ ≤ R / 4) (ha0 : f a = 0)
    (hb0 : f b = 0) :
    ‖deriv f a‖ * ‖b - a‖ ≤ 8 * M / R ^ 2 * ‖b - a‖ ^ 2 := by
  have h := norm_sub_taylor_le hU hf hR hsub hM hb
  simp only [ha0, hb0, sub_zero, zero_sub, norm_neg, norm_mul] at h
  exact h

/-- The zeta bound on a disc of radius `1/2` around a point of the strip at height `≥ 3`. -/
theorem norm_riemannZeta_le_on_disc {ρ : ℂ} (hre0 : 0 ≤ ρ.re) (hre1 : ρ.re ≤ 1) (hγ : 3 ≤ |ρ.im|) :
    ∀ z ∈ closedBall ρ (1 / 2),
      ‖riemannZeta z‖ ≤ 5 * Real.exp 2 * (|ρ.im| + 2) * (|ρ.im| + 5) := by
  intro z hz
  rw [mem_closedBall, dist_eq_norm] at hz
  have hre := (abs_re_le_norm (z - ρ)).trans hz
  have him := (abs_im_le_norm (z - ρ)).trans hz
  rw [sub_re] at hre
  rw [sub_im] at him
  have ht2 : 2 ≤ |z.im| := by
    have := abs_sub_abs_le_abs_sub ρ.im z.im
    rw [abs_sub_comm] at this
    linarith
  have htle : |z.im| ≤ |ρ.im| + 1 / 2 := by
    have := abs_sub_abs_le_abs_sub z.im ρ.im
    linarith
  have hb := RHTower.norm_riemannZeta_le_smoothAFE_strip (σ := z.re) (t := z.im)
    (by linarith [(abs_le.mp hre).1]) (by linarith [(abs_le.mp hre).2]) ht2
  rw [re_add_im] at hb
  refine hb.trans ?_
  have he : 0 < 5 * Real.exp 2 := by positivity
  have h1 : 1 + |z.im| ≤ |ρ.im| + 2 := by linarith
  have h2 : 4 + |z.im| ≤ |ρ.im| + 5 := by linarith
  have h3 : (1 + |z.im|) * (4 + |z.im|) ≤ (|ρ.im| + 2) * (|ρ.im| + 5) :=
    mul_le_mul h1 h2 (by positivity) (by positivity)
  have h4 := mul_le_mul_of_nonneg_left h3 he.le
  linarith [h4, show 5 * Real.exp 2 * (1 + |z.im|) * (4 + |z.im|) =
    5 * Real.exp 2 * ((1 + |z.im|) * (4 + |z.im|)) by ring,
    show 5 * Real.exp 2 * (|ρ.im| + 2) * (|ρ.im| + 5) =
    5 * Real.exp 2 * ((|ρ.im| + 2) * (|ρ.im| + 5)) by ring]

/-- **For zeta.** A zero `ρ` in the strip with `|Im ρ| ≥ 3` and another zero `ρ'` within `1/8`
satisfy `‖ζ'(ρ)‖ ‖ρ' − ρ‖ ≤ 160 e² (|γ| + 2)(|γ| + 5) ‖ρ' − ρ‖²`. -/
theorem norm_deriv_riemannZeta_mul_le_of_near_zero {ρ ρ' : ℂ} (hρ : riemannZeta ρ = 0)
    (hρ' : riemannZeta ρ' = 0) (hre0 : 0 ≤ ρ.re) (hre1 : ρ.re ≤ 1) (hγ : 3 ≤ |ρ.im|)
    (hclose : ‖ρ' - ρ‖ ≤ 1 / 8) :
    ‖deriv riemannZeta ρ‖ * ‖ρ' - ρ‖ ≤
      160 * Real.exp 2 * (|ρ.im| + 2) * (|ρ.im| + 5) * ‖ρ' - ρ‖ ^ 2 := by
  set U : Set ℂ := {s | s ≠ 1} with hU
  have hUo : IsOpen U := isOpen_ne
  have hfU : DifferentiableOn ℂ riemannZeta U := fun s hs =>
    (differentiableAt_riemannZeta hs).differentiableWithinAt
  have hsub : closedBall ρ (1 / 2) ⊆ U := by
    intro z hz h1
    rw [mem_closedBall, dist_eq_norm] at hz
    have him := (abs_im_le_norm (z - ρ)).trans hz
    rw [sub_im, h1, one_im] at him
    have : |ρ.im| ≤ 1 / 2 := by rw [abs_sub_comm] at him; simpa using him
    linarith
  have h := norm_deriv_mul_le_of_two_zeros hUo hfU (by norm_num : (0 : ℝ) < 1 / 2) hsub
    (norm_riemannZeta_le_on_disc hre0 hre1 hγ) (by linarith : ‖ρ' - ρ‖ ≤ 1 / 2 / 4) hρ hρ'
  calc ‖deriv riemannZeta ρ‖ * ‖ρ' - ρ‖ ≤
        8 * (5 * Real.exp 2 * (|ρ.im| + 2) * (|ρ.im| + 5)) / (1 / 2) ^ 2 * ‖ρ' - ρ‖ ^ 2 := h
    _ = 160 * Real.exp 2 * (|ρ.im| + 2) * (|ρ.im| + 5) * ‖ρ' - ρ‖ ^ 2 := by ring

/-- **Collide or repel from a derivative bound.** If `ρ` is a zero in the strip with `|Im ρ| ≥ 3`
and `‖ζ'(ρ)‖ ≥ c`, every other zero `ρ'` satisfies
`‖ρ' − ρ‖ ≥ min(1/8, c / (160 e² (|γ| + 2)(|γ| + 5)))`. -/
theorem separation_of_norm_deriv_riemannZeta_ge {ρ ρ' : ℂ} (hρ : riemannZeta ρ = 0)
    (hρ' : riemannZeta ρ' = 0) (hne : ρ' ≠ ρ) (hre0 : 0 ≤ ρ.re) (hre1 : ρ.re ≤ 1)
    (hγ : 3 ≤ |ρ.im|) {c : ℝ} (hder : c ≤ ‖deriv riemannZeta ρ‖) :
    min (1 / 8) (c / (160 * Real.exp 2 * (|ρ.im| + 2) * (|ρ.im| + 5))) ≤ ‖ρ' - ρ‖ := by
  by_cases hfar : 1 / 8 < ‖ρ' - ρ‖
  · exact (min_le_left _ _).trans hfar.le
  push Not at hfar
  have hpos : 0 < ‖ρ' - ρ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hK : 0 < 160 * Real.exp 2 * (|ρ.im| + 2) * (|ρ.im| + 5) := by positivity
  have h := norm_deriv_riemannZeta_mul_le_of_near_zero hρ hρ' hre0 hre1 hγ hfar
  have h2 : c * ‖ρ' - ρ‖ ≤ 160 * Real.exp 2 * (|ρ.im| + 2) * (|ρ.im| + 5) * ‖ρ' - ρ‖ ^ 2 :=
    (mul_le_mul_of_nonneg_right hder hpos.le).trans h
  have h3 : c ≤ 160 * Real.exp 2 * (|ρ.im| + 2) * (|ρ.im| + 5) * ‖ρ' - ρ‖ := by
    rw [sq, ← mul_assoc] at h2
    exact le_of_mul_le_mul_right h2 hpos
  refine (min_le_right _ _).trans ?_
  rw [div_le_iff₀ hK]
  linarith

end GaloisForLFunctions.ArithmeticDiscreteness
