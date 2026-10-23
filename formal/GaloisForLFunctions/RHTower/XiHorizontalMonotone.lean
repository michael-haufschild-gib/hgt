import GaloisForLFunctions.RHTower.XiHadamardSharpRegion

/-!
# `|ξ|` increases to the right inside the zero-free region

`∂_σ log|ξ(σ+it)| = Re (ξ'/ξ)(σ+it)`, so the Hadamard positivity region is exactly a region of
horizontal monotonicity of `|ξ|`.  The corpus's Sondow--Dumitrescu monotonicity is parametrized by
a *uniform* half-plane zero bound (`XiZeroHalfPlaneBound`), which unconditionally only gives
`Re s ≥ 1`.  The region of `XiHadamardSharpRegion` is height dependent and reaches into the strip:

* for `|Im s| ≤ 4`, `|ξ(σ+it)|` is nondecreasing on the whole of `σ > ½`;
* for `|Im s| > 4`, on `σ ≥ 1 - 1/(58 log(|Im s| + ½))`.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- Replace a real derivative value by an equal one. -/
private theorem hasDerivAt_of_eq_real {f : ℝ → ℝ} {u v x : ℝ} (h : HasDerivAt f u x)
    (huv : u = v) : HasDerivAt f v x := huv ▸ h

/-- The horizontal derivative of `‖ξ‖²`. -/
private theorem hasDerivAt_normSq_xi_horizontal (σ t : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.normSq (xi ((u : ℂ) + (t : ℂ) * I)))
      (2 * ((xi ((σ : ℂ) + (t : ℂ) * I)).re * (deriv xi ((σ : ℂ) + (t : ℂ) * I)).re
          + (xi ((σ : ℂ) + (t : ℂ) * I)).im * (deriv xi ((σ : ℂ) + (t : ℂ) * I)).im)) σ := by
  have hin : HasDerivAt (fun u : ℝ => (u : ℂ) + (t : ℂ) * I) 1 σ := by
    simpa using ((Complex.ofRealCLM.hasDerivAt (x := σ)).add_const ((t : ℂ) * I))
  have hu : HasDerivAt (fun u : ℝ => xi ((u : ℂ) + (t : ℂ) * I))
      (deriv xi ((σ : ℂ) + (t : ℂ) * I)) σ := by
    have h := (xi_differentiable ((σ : ℂ) + (t : ℂ) * I)).hasDerivAt.comp σ hin
    rw [mul_one] at h
    exact h
  have hre : HasDerivAt (fun u : ℝ => (xi ((u : ℂ) + (t : ℂ) * I)).re)
      ((deriv xi ((σ : ℂ) + (t : ℂ) * I)).re) σ :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt σ hu
  have him : HasDerivAt (fun u : ℝ => (xi ((u : ℂ) + (t : ℂ) * I)).im)
      ((deriv xi ((σ : ℂ) + (t : ℂ) * I)).im) σ :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt σ hu
  have hfun : (fun u : ℝ => Complex.normSq (xi ((u : ℂ) + (t : ℂ) * I)))
      = fun u : ℝ => (xi ((u : ℂ) + (t : ℂ) * I)).re * (xi ((u : ℂ) + (t : ℂ) * I)).re
          + (xi ((u : ℂ) + (t : ℂ) * I)).im * (xi ((u : ℂ) + (t : ℂ) * I)).im := by
    funext u
    exact Complex.normSq_apply _
  rw [hfun]
  refine hasDerivAt_of_eq_real ((hre.mul hre).add (him.mul him)) ?_
  ring

/-- **Positivity of `Re (ξ'/ξ)` on a convex set of abscissas gives horizontal monotonicity.** -/
theorem monotoneOn_normSq_xi_horizontal {t : ℝ} {S : Set ℝ} (hS : Convex ℝ S)
    (hpos : ∀ σ ∈ interior S, 0 ≤ (logDeriv xi ((σ : ℂ) + (t : ℂ) * I)).re) :
    MonotoneOn (fun σ : ℝ => Complex.normSq (xi ((σ : ℂ) + (t : ℂ) * I))) S := by
  refine monotoneOn_of_deriv_nonneg hS ?_ ?_ ?_
  · exact (Complex.continuous_normSq.comp (xi_differentiable.continuous.comp
      (by fun_prop))).continuousOn
  · intro σ _
    exact ((hasDerivAt_normSq_xi_horizontal σ t).differentiableAt).differentiableWithinAt
  · intro σ hσ
    rw [(hasDerivAt_normSq_xi_horizontal σ t).deriv]
    set s : ℂ := (σ : ℂ) + (t : ℂ) * I with hs
    rcases eq_or_ne (xi s) 0 with hz | hz
    · simp [hz]
    · have hn : Complex.normSq (xi s) ≠ 0 := by
        simpa using (Complex.normSq_pos.mpr hz).ne'
      have hlog : (logDeriv xi s).re * Complex.normSq (xi s)
          = (xi s).re * (deriv xi s).re + (xi s).im * (deriv xi s).im := by
        rw [logDeriv_apply, Complex.div_re]
        field_simp
      have hp := hpos σ hσ
      have hns : 0 < Complex.normSq (xi s) := Complex.normSq_pos.mpr hz
      nlinarith [hp, hns, hlog]

/-- Monotone squared modulus gives monotone modulus. -/
theorem monotoneOn_norm_of_normSq {t : ℝ} {S : Set ℝ}
    (h : MonotoneOn (fun σ : ℝ => Complex.normSq (xi ((σ : ℂ) + (t : ℂ) * I))) S) :
    MonotoneOn (fun σ : ℝ => ‖xi ((σ : ℂ) + (t : ℂ) * I)‖) S := by
  intro a ha b hb hab
  have hs : Complex.normSq (xi ((a : ℂ) + (t : ℂ) * I))
      ≤ Complex.normSq (xi ((b : ℂ) + (t : ℂ) * I)) := h ha hb hab
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hs
  show ‖xi ((a : ℂ) + (t : ℂ) * I)‖ ≤ ‖xi ((b : ℂ) + (t : ℂ) * I)‖
  nlinarith [norm_nonneg (xi ((a : ℂ) + (t : ℂ) * I)),
    norm_nonneg (xi ((b : ℂ) + (t : ℂ) * I)), hs]

/-- **`|ξ|` is nondecreasing on the whole half strip `σ > ½` below height four.** -/
theorem monotoneOn_norm_xi_low {t : ℝ} (ht : |t| ≤ 4) :
    MonotoneOn (fun σ : ℝ => ‖xi ((σ : ℂ) + (t : ℂ) * I)‖) (Ioi (1 / 2 : ℝ)) := by
  refine monotoneOn_norm_of_normSq (monotoneOn_normSq_xi_horizontal (convex_Ioi _) ?_)
  intro σ hσ
  rw [interior_Ioi] at hσ
  have hre : (((σ : ℂ) + (t : ℂ) * I)).re = σ := by simp
  have him : (((σ : ℂ) + (t : ℂ) * I)).im = t := by simp
  refine re_logDeriv_xi_nonneg_of_abs_im_le_four ?_ ?_
  · rw [hre]; exact hσ
  · rw [him]; exact ht

/-- **`|ξ|` is nondecreasing on the zero-free region above height four.** -/
theorem monotoneOn_norm_xi_high {t : ℝ} (ht : 4 < |t|) :
    MonotoneOn (fun σ : ℝ => ‖xi ((σ : ℂ) + (t : ℂ) * I)‖)
      (Ici (1 - 1 / 58 / Real.log (|t| + 1 / 2))) := by
  have hlog4 : 1 < Real.log 4 := by
    have h2 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
      norm_num
    have := Real.log_two_gt_d9
    rw [h2]; linarith
  have hL : 1 < Real.log (|t| + 1 / 2) :=
    lt_of_lt_of_le hlog4 (Real.log_le_log (by norm_num) (by linarith))
  have hhalf : (1 : ℝ) / 2 < 1 - 1 / 58 / Real.log (|t| + 1 / 2) := by
    have h : 1 / 58 / Real.log (|t| + 1 / 2) < 1 / 2 := by
      rw [div_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [hL]
    linarith
  refine monotoneOn_norm_of_normSq (monotoneOn_normSq_xi_horizontal (convex_Ici _) ?_)
  intro σ hσ
  rw [interior_Ici] at hσ
  have hre : (((σ : ℂ) + (t : ℂ) * I)).re = σ := by simp
  have him : (((σ : ℂ) + (t : ℂ) * I)).im = t := by simp
  have hσ' : 1 - 1 / 58 / Real.log (|t| + 1 / 2) < σ := hσ
  refine re_logDeriv_xi_nonneg_of_zeroFree_sharp ?_ ?_ ?_
  · rw [hre]; linarith
  · rw [him]; exact ht
  · rw [hre, him]; linarith

end

end RHTower
