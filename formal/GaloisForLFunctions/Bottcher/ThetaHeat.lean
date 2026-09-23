/-
# The Jacobi heat equation `∂_z²Θ = 4πi ∂_τΘ` — second `z`-derivative of the theta function

mathlib supplies the *first* `z`-derivative of the two-variable Jacobi theta `Θ(z,τ)` as a series
(`hasDerivAt_jacobiTheta₂_fst`, value `jacobiTheta₂' = ∑ 2πin·term`), but no second derivative and no
heat equation. This file builds the next layer of the modular-forms differential calculus the
hypertranscendence programme needs:

* `thetaHeatTerm n z τ = (2πin)²·term` — the termwise second `z`-derivative; `thetaHeatTerm_eq`
  records the termwise heat relation `(2πin)² = 4πi·(πin²)`.
* `hasDerivAt_jacobiTheta₂'_fst` — the **global second `z`-derivative**: differentiating
  `jacobiTheta₂' · τ = ∑ jacobiTheta₂'_term` once more in `z` (uniformly on a horizontal strip via
  `hasDerivAt_tsum_of_isPreconnected` and `summable_pow_mul_jacobiTheta₂_term_bound`) gives
  `∑ thetaHeatTerm`.
* `hasDerivAt_jacobiTheta₂_snd` — the `τ`-derivative `∑ πin²·term` (the mathlib `z`-derivative's
  companion, evaluating the joint Fréchet derivative in the `(0,1)` direction).
* `tsum_thetaHeatTerm_eq` — the **heat equation in series form** `∂_z²Θ = 4πi ∂_τΘ`.

The seam object `∂_s` (archimedean differential generator) meeting the discrete theta lattice is
exactly the kind of `𝓜⁺` interaction this layer makes precise; downstream it is the route toward the
Jacobi quartic identity `θ₃⁴ = θ₂⁴ + θ₄⁴` (the second-order ODE the theta-nullwerte satisfy via the
heat equation). General lemmas; Mathlib only.
-/
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Tactic
open Complex Real Filter
open scoped Real Topology

namespace Bottcher

noncomputable def thetaHeatTerm (n : ℤ) (z τ : ℂ) : ℂ :=
  (2 * π * I * n) ^ (2 : ℕ) * jacobiTheta₂_term n z τ

theorem thetaHeatTerm_eq (n : ℤ) (z τ : ℂ) :
    thetaHeatTerm n z τ = 4 * π * I * (π * I * n ^ (2 : ℕ) * jacobiTheta₂_term n z τ) := by
  unfold thetaHeatTerm; ring

/-- Norm bound: `‖thetaHeatTerm n z τ‖ ≤ 4π²|n|²·exp(-π(T n² - 2S|n|))` when `|im z| ≤ S`, `T ≤ im τ`. -/
theorem norm_thetaHeatTerm_le {S T : ℝ} (hT : 0 < T) {z τ : ℂ} (hz : |im z| ≤ S) (hτ : T ≤ im τ)
    (n : ℤ) : ‖thetaHeatTerm n z τ‖ ≤ 4 * π ^ (2 : ℕ) * ((|n| ^ (2 : ℕ) : ℝ) * Real.exp (-π * (T * n ^ (2 : ℕ) - 2 * S * |n|))) := by
  rw [thetaHeatTerm, norm_mul]
  have hb : ‖jacobiTheta₂_term n z τ‖ ≤ Real.exp (-π * (T * n ^ (2 : ℕ) - 2 * S * |n|)) :=
    norm_jacobiTheta₂_term_le hT hz hτ n
  have hcoef : ‖(2 * (π : ℂ) * I * (n : ℂ)) ^ (2 : ℕ)‖ = 4 * π ^ (2 : ℕ) * (|n| ^ (2 : ℕ) : ℝ) := by
    rw [norm_pow, norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg Real.pi_nonneg, Complex.norm_intCast]
    rw [← Int.cast_abs]; push_cast; ring
  rw [hcoef, mul_assoc]
  gcongr

theorem summable_thetaHeatTerm {z τ : ℂ} (hτ : 0 < im τ) :
    Summable (thetaHeatTerm · z τ) := by
  obtain ⟨T, hT, hτ'⟩ := exists_between hτ
  obtain ⟨S, hz⟩ := exists_gt |im z|
  exact ((summable_pow_mul_jacobiTheta₂_term_bound S hT 2).mul_left (4 * π ^ (2 : ℕ))).of_norm_bounded
    (fun n => norm_thetaHeatTerm_le hT hz.le hτ'.le n)

/-- **Per-term second `z`-derivative**: `d/dz (jacobiTheta₂'_term n · τ) = thetaHeatTerm n · τ`. -/
theorem hasDerivAt_jacobiTheta₂'_term (n : ℤ) (z τ : ℂ) :
    HasDerivAt (fun w => jacobiTheta₂'_term n w τ) (thetaHeatTerm n z τ) z := by
  have h1 : HasDerivAt (fun w : ℂ => 2 * (π : ℂ) * I * (n : ℂ) * w + (π : ℂ) * I * (n : ℂ) ^ (2 : ℕ) * τ)
      (2 * (π : ℂ) * I * (n : ℂ)) z := by
    simpa using ((hasDerivAt_id z).const_mul (2 * (π : ℂ) * I * (n : ℂ))).add_const
      ((π : ℂ) * I * (n : ℂ) ^ (2 : ℕ) * τ)
  have h2 := (h1.cexp).const_mul (2 * (π : ℂ) * I * (n : ℂ))
  have hfun : (fun w => jacobiTheta₂'_term n w τ)
      = (fun w => 2 * (π : ℂ) * I * (n : ℂ) *
          Complex.exp (2 * (π : ℂ) * I * (n : ℂ) * w + (π : ℂ) * I * (n : ℂ) ^ (2 : ℕ) * τ)) := by
    funext w; rw [jacobiTheta₂'_term, jacobiTheta₂_term]
  rw [hfun]
  apply h2.congr_deriv
  unfold thetaHeatTerm jacobiTheta₂_term
  ring

/-- **Global second `z`-derivative of the Jacobi theta function.** Differentiating the first-
derivative series `jacobiTheta₂' · τ = ∑ jacobiTheta₂'_term` in `z` term-by-term (uniformly on the
strip `|im w| < S`, via `hasDerivAt_tsum_of_isPreconnected` and the summable bound) gives the
second `z`-derivative `∑ thetaHeatTerm`. -/
theorem hasDerivAt_jacobiTheta₂'_fst (z : ℂ) {τ : ℂ} (hτ : 0 < im τ) :
    HasDerivAt (fun w => jacobiTheta₂' w τ) (∑' n, thetaHeatTerm n z τ) z := by
  obtain ⟨S, hz⟩ := exists_gt |im z|
  set t : Set ℂ := {w | |im w| < S} with ht_def
  have hto : IsOpen t := (_root_.continuous_abs.comp continuous_im).isOpen_preimage _ isOpen_Iio
  have htc : IsPreconnected t := by
    have ht_eq : {w : ℂ | |im w| < S} =
        {w : ℂ | -S < im w} ∩ {w : ℂ | im w < S} := by
      ext w
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, abs_lt]
    rw [ht_def, ht_eq]
    exact ((convex_halfSpace_im_gt (-S)).inter (convex_halfSpace_im_lt S)).isPreconnected
  have hzt : z ∈ t := hz
  set u : ℤ → ℝ := fun n => 4 * π ^ (2 : ℕ) *
    ((|n| ^ (2 : ℕ) : ℝ) * Real.exp (-π * (im τ * n ^ (2 : ℕ) - 2 * S * |n|))) with hu_def
  have hu : Summable u := (summable_pow_mul_jacobiTheta₂_term_bound S hτ 2).mul_left _
  have hg : ∀ (n : ℤ) (w : ℂ), w ∈ t →
      HasDerivAt (fun w => jacobiTheta₂'_term n w τ) (thetaHeatTerm n w τ) w :=
    fun n w _ => hasDerivAt_jacobiTheta₂'_term n w τ
  have hg' : ∀ (n : ℤ) (w : ℂ), w ∈ t → ‖thetaHeatTerm n w τ‖ ≤ u n :=
    fun n w hw => norm_thetaHeatTerm_le hτ (le_of_lt hw) le_rfl n
  have hf0 : Summable fun n => jacobiTheta₂'_term n z τ := (summable_jacobiTheta₂'_term_iff z τ).2 hτ
  have key := hasDerivAt_tsum_of_isPreconnected hu hto htc hg hg' hzt hf0 hzt
  simpa only [jacobiTheta₂'] using key

/-- Summand in the series for the `τ`-derivative of the Jacobi theta function: `πin²·term`. -/
noncomputable def jacobiTheta₂_snd_term (n : ℤ) (z τ : ℂ) : ℂ :=
  (π : ℂ) * I * (n : ℂ) ^ (2 : ℕ) * jacobiTheta₂_term n z τ

/-- **`τ`-derivative of the Jacobi theta function** (companion to mathlib's `z`-derivative
`hasDerivAt_jacobiTheta₂_fst`): differentiating `jacobiTheta₂ z ·` gives `∑ πin²·term`. Evaluate the
joint Fréchet derivative `jacobiTheta₂_fderiv` at the `τ`-direction `(0,1)`. -/
theorem hasDerivAt_jacobiTheta₂_snd (z : ℂ) {τ : ℂ} (hτ : 0 < im τ) :
    HasDerivAt (fun s => jacobiTheta₂ z s) (∑' n, jacobiTheta₂_snd_term n z τ) τ := by
  let eval_snd_CLM : (ℂ × ℂ →L[ℂ] ℂ) →L[ℂ] ℂ :=
  { toFun := fun f => f (0, 1)
    map_add' := by simp only [_root_.add_apply, forall_const]
    map_smul' := by simp }
  have step1 : HasSum (fun n => (jacobiTheta₂_term_fderiv n z τ) (0, 1))
      ((jacobiTheta₂_fderiv z τ) (0, 1)) := by
    apply eval_snd_CLM.hasSum (hasSum_jacobiTheta₂_term_fderiv z hτ)
  have step2 (n : ℤ) : (jacobiTheta₂_term_fderiv n z τ) (0, 1) = jacobiTheta₂_snd_term n z τ := by
    simp only [jacobiTheta₂_term_fderiv, smul_add, _root_.add_apply,
      FunLike.coe_smul, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      Pi.smul_apply, smul_eq_mul, mul_zero, mul_one, zero_add, jacobiTheta₂_snd_term,
      jacobiTheta₂_term, mul_comm _ (cexp _)]
  rw [funext step2] at step1
  have step3 : HasDerivAt (fun s => jacobiTheta₂ z s) ((jacobiTheta₂_fderiv z τ) (0, 1)) τ :=
    (((hasFDerivAt_jacobiTheta₂ z hτ).comp τ (hasFDerivAt_prodMk_right z τ)).hasDerivAt :)
  rwa [← step1.tsum_eq] at step3

/-- **Heat equation (series form): `∂_z² θ = 4πi · ∂_τ θ`.** The second-`z`-derivative series
`∑ thetaHeatTerm` equals `4πi` times the `τ`-derivative series `∑ jacobiTheta₂_snd_term`. Unconditional
(`tsum_mul_left` + the termwise heat equation `thetaHeatTerm_eq`). Together with
`hasDerivAt_jacobiTheta₂'_fst` and `hasDerivAt_jacobiTheta₂_snd` this is the Jacobi heat equation. -/
theorem tsum_thetaHeatTerm_eq (z τ : ℂ) :
    (∑' n, thetaHeatTerm n z τ) = 4 * π * I * ∑' n, jacobiTheta₂_snd_term n z τ := by
  rw [← tsum_mul_left]
  exact tsum_congr (fun n => by rw [thetaHeatTerm_eq, jacobiTheta₂_snd_term])

end Bottcher
