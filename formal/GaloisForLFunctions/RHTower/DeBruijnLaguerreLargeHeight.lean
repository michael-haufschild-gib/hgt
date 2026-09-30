import GaloisForLFunctions.RHTower.DeBruijnLocalPairLawMonotonicity

/-!
# The first Laguerre inequality for `H_t` at large height

For an entire `H` that is real on the real axis, `ψ(w) = H(x + iw) H(x − iw)` is entire, even, equal
to `|H(x + iy)|²` on real `w = y`, and `ψ''(0) = 2 (H'(x)² − H(x) H''(x))`. If `y ↦ |H(x + iy)|` is
nondecreasing on `y ≥ 0`, then `ψ''(0) ≥ 0`: otherwise `ψ'' < 0` near `0`, `ψ'` decreases from
`ψ'(0) = 0`, and `|H(x + iy)|²` decreases for small `y > 0`. Hence
(`laguerre_of_monotoneOn_norm_vertical`) the first Laguerre inequality
`H'(x)² − H(x) H''(x) ≥ 0` holds wherever vertical monotonicity does.

For the de Bruijn–Newman deformation this gives, unconditionally, the Laguerre inequality for every
`t > 0` at all large `|x|` (`exists_laguerre_riemannHeat`), and under the Riemann hypothesis for
`Ξ = H_0` at every real `x` (`laguerre_xi_of_riemannHypothesis`).
-/

open Complex Filter Topology Set

namespace RHTower.DeBruijn

noncomputable section

variable {H : ℂ → ℂ}

/-- The vertical product `ψ(w) = H(x + iw) H(x − iw)`. -/
def verticalProduct (H : ℂ → ℂ) (x : ℝ) (w : ℂ) : ℂ := H (x + I * w) * H (x - I * w)

theorem hasDerivAt_affine_plus (x : ℝ) (w : ℂ) :
    HasDerivAt (fun w : ℂ => (x : ℂ) + I * w) I w := by
  simpa using ((hasDerivAt_id w).const_mul I).const_add (x : ℂ)

theorem hasDerivAt_affine_minus (x : ℝ) (w : ℂ) :
    HasDerivAt (fun w : ℂ => (x : ℂ) - I * w) (-I) w := by
  simpa using ((hasDerivAt_id w).const_mul I).const_sub (x : ℂ)

theorem hasDerivAt_comp_plus {F : ℂ → ℂ} (hF : Differentiable ℂ F) (x : ℝ) (w : ℂ) :
    HasDerivAt (fun w : ℂ => F ((x : ℂ) + I * w)) (deriv F ((x : ℂ) + I * w) * I) w :=
  (hF _).hasDerivAt.comp w (hasDerivAt_affine_plus x w)

theorem hasDerivAt_comp_minus {F : ℂ → ℂ} (hF : Differentiable ℂ F) (x : ℝ) (w : ℂ) :
    HasDerivAt (fun w : ℂ => F ((x : ℂ) - I * w)) (deriv F ((x : ℂ) - I * w) * (-I)) w :=
  (hF _).hasDerivAt.comp w (hasDerivAt_affine_minus x w)

theorem differentiable_deriv_of_entire {F : ℂ → ℂ} (hF : Differentiable ℂ F) :
    Differentiable ℂ (deriv F) := fun z =>
  ((hF.analyticAt z).deriv).differentiableAt

theorem hasDerivAt_verticalProduct (hH : Differentiable ℂ H) (x : ℝ) (w : ℂ) :
    HasDerivAt (verticalProduct H x)
      (I * deriv H (x + I * w) * H (x - I * w) - I * H (x + I * w) * deriv H (x - I * w)) w := by
  have h := (hasDerivAt_comp_plus hH x w).mul (hasDerivAt_comp_minus hH x w)
  exact h.congr_deriv (by ring)

theorem deriv_verticalProduct (hH : Differentiable ℂ H) (x : ℝ) :
    deriv (verticalProduct H x) = fun w =>
      I * deriv H (x + I * w) * H (x - I * w) - I * H (x + I * w) * deriv H (x - I * w) :=
  funext fun w => (hasDerivAt_verticalProduct hH x w).deriv

theorem hasDerivAt_deriv_verticalProduct (hH : Differentiable ℂ H) (x : ℝ) :
    HasDerivAt (deriv (verticalProduct H x))
      (2 * (deriv H x ^ 2 - H x * deriv (deriv H) x)) 0 := by
  rw [deriv_verticalProduct hH x]
  have hH' := differentiable_deriv_of_entire hH
  have hA := hasDerivAt_comp_plus hH' x 0
  have hB := hasDerivAt_comp_minus hH x 0
  have hC := hasDerivAt_comp_plus hH x 0
  have hD := hasDerivAt_comp_minus hH' x 0
  have h := ((hA.mul hB).const_mul I).sub ((hC.mul hD).const_mul I)
  have hfun : (fun w : ℂ => I * deriv H (x + I * w) * H (x - I * w) -
      I * H (x + I * w) * deriv H (x - I * w)) = fun w : ℂ =>
      I * (deriv H ((x : ℂ) + I * w) * H ((x : ℂ) - I * w)) -
        I * (H ((x : ℂ) + I * w) * deriv H ((x : ℂ) - I * w)) := by
    funext w; ring
  rw [hfun]
  refine h.congr_deriv ?_
  simp only [mul_zero, add_zero, sub_zero]
  ring_nf
  rw [I_sq]
  ring

/-- `ψ` restricted to the real axis is `|H(x + iy)|²` when `H` commutes with conjugation. -/
theorem verticalProduct_ofReal (hconj : ∀ z, H ((starRingEnd ℂ) z) = (starRingEnd ℂ) (H z))
    (x y : ℝ) : verticalProduct H x y = ((‖H (x + I * y)‖ ^ 2 : ℝ) : ℂ) := by
  unfold verticalProduct
  have hc : (x : ℂ) - I * y = (starRingEnd ℂ) ((x : ℂ) + I * y) := by
    apply Complex.ext <;> simp
  rw [hc, hconj, Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **Laguerre from vertical monotonicity.** -/
theorem laguerre_of_monotoneOn_norm_vertical (hH : Differentiable ℂ H)
    (hconj : ∀ z, H ((starRingEnd ℂ) z) = (starRingEnd ℂ) (H z)) {x : ℝ}
    (hmono : MonotoneOn (fun y : ℝ => ‖H ((x : ℂ) + I * y)‖) (Ici 0)) :
    0 ≤ (deriv H x ^ 2 - H x * deriv (deriv H) x).re := by
  by_contra hneg
  push Not at hneg
  set c := (deriv H x ^ 2 - H x * deriv (deriv H) x).re with hc
  set ψ := verticalProduct H x with hψ
  have hψd : Differentiable ℂ ψ := fun w => (hasDerivAt_verticalProduct hH x w).differentiableAt
  have hψ' : Differentiable ℂ (deriv ψ) := differentiable_deriv_of_entire hψd
  -- the real restriction and its derivatives
  set f : ℝ → ℝ := fun y => (ψ y).re with hf
  set f' : ℝ → ℝ := fun y => (deriv ψ y).re with hf'
  set f'' : ℝ → ℝ := fun y => (deriv (deriv ψ) y).re with hf''
  have hfd : ∀ y : ℝ, HasDerivAt f (f' y) y := fun y =>
    HasDerivAt.real_of_complex (hψd y).hasDerivAt
  have hf'd : ∀ y : ℝ, HasDerivAt f' (f'' y) y := fun y =>
    HasDerivAt.real_of_complex (hψ' y).hasDerivAt
  have hf''c : Continuous f'' := by
    have := (hψd.contDiff (n := 3)).continuous_iteratedDeriv 2 (by norm_num)
    rw [iteratedDeriv_succ, iteratedDeriv_one] at this
    exact continuous_re.comp (this.comp continuous_ofReal)
  have hf''0 : f'' 0 = 2 * c := by
    simp only [hf'', ofReal_zero]
    rw [(hasDerivAt_deriv_verticalProduct hH x).deriv, hc]
    simp [Complex.mul_re]
  have hf'0 : f' 0 = 0 := by
    have heven : ∀ w, ψ (-w) = ψ w := by
      intro w; simp only [hψ, verticalProduct]; ring_nf
    have h1 := (hψd 0).hasDerivAt
    have h2 : HasDerivAt (fun w => ψ (-w)) (deriv ψ 0 * (-1)) 0 := by
      have h0 : HasDerivAt ψ (deriv ψ 0) (-0) := by rw [neg_zero]; exact (hψd 0).hasDerivAt
      exact h0.comp (0 : ℂ) (hasDerivAt_neg (0 : ℂ))
    rw [show (fun w => ψ (-w)) = ψ from funext heven] at h2
    have := h1.unique h2
    simp only [hf', ofReal_zero]
    have : deriv ψ 0 = 0 := by linear_combination this / 2
    rw [this, zero_re]
  -- `f'' < 0` on a neighbourhood of `0`
  obtain ⟨δ, hδ, hδneg⟩ : ∃ δ > 0, ∀ y ∈ Icc (0 : ℝ) δ, f'' y < 0 := by
    have hlt : f'' 0 < 0 := by rw [hf''0]; linarith
    have := (hf''c.tendsto 0).eventually (gt_mem_nhds hlt)
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp this
    refine ⟨ε / 2, by linarith, fun y hy => hball ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hy.1]
    linarith [hy.2]
  -- `f'` strictly decreases on `[0, δ]`, hence is negative on `(0, δ]`
  have hf'anti : StrictAntiOn f' (Icc 0 δ) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc 0 δ)
      (fun y _ => (hf'd y).continuousAt.continuousWithinAt) fun y hy => ?_
    rw [interior_Icc] at hy
    rw [(hf'd y).deriv]
    exact hδneg y (Ioo_subset_Icc_self hy)
  have hfanti : StrictAntiOn f (Icc 0 δ) := by
    refine strictAntiOn_of_deriv_neg (convex_Icc 0 δ)
      (fun y _ => (hfd y).continuousAt.continuousWithinAt) fun y hy => ?_
    rw [interior_Icc] at hy
    rw [(hfd y).deriv, ← hf'0]
    exact hf'anti ⟨le_refl 0, hδ.le⟩ (Ioo_subset_Icc_self hy) hy.1
  have hlt := hfanti ⟨le_refl 0, hδ.le⟩ ⟨hδ.le, le_refl δ⟩ hδ
  have hge := hmono (mem_Ici.mpr (le_refl 0)) (mem_Ici.mpr hδ.le) hδ.le
  have e : ∀ y : ℝ, f y = ‖H ((x : ℂ) + I * y)‖ ^ 2 := by
    intro y
    simp only [hf, hψ, verticalProduct_ofReal hconj x y, ofReal_re]
  rw [e, e] at hlt
  simp only at hge
  nlinarith [norm_nonneg (H ((x : ℂ) + I * ((0 : ℝ) : ℂ))), norm_nonneg (H ((x : ℂ) + I * (δ : ℂ)))]

/-- **Laguerre at large height.** For every `t > 0`, `H_t'(x)² − H_t(x) H_t''(x) ≥ 0` for all
large `|x|`. -/
theorem exists_laguerre_riemannHeat {t : ℝ} (ht : 0 < t) :
    ∃ X₀ : ℝ, ∀ x : ℝ, X₀ ≤ |x| →
      0 ≤ (deriv (riemannHeat t) x ^ 2 -
        riemannHeat t x * deriv (deriv (riemannHeat t)) x).re := by
  obtain ⟨X₀, hX₀⟩ := exists_monotoneOn_norm_riemannHeat_vertical ht
  exact ⟨X₀, fun x hx => laguerre_of_monotoneOn_norm_vertical
    (differentiable_riemannHeat ht.le) (riemannHeat_conj ht.le) (hX₀ x hx)⟩

/-- Under the Riemann hypothesis `Ξ = H_0` satisfies the first Laguerre inequality everywhere. -/
theorem laguerre_xi_of_riemannHypothesis (hRH : RiemannHypothesis) (x : ℝ) :
    0 ≤ (deriv (riemannHeat 0) x ^ 2 -
      riemannHeat 0 x * deriv (deriv (riemannHeat 0)) x).re := by
  have hreal := riemannHypothesis_iff_riemannHeat_zero_real.mp hRH
  exact laguerre_of_monotoneOn_norm_vertical (differentiable_riemannHeat le_rfl)
    (riemannHeat_conj le_rfl) (monotoneOn_norm_riemannHeat_vertical le_rfl fun ζ hζ => by
      rw [hreal ζ hζ]; nlinarith [sq_nonneg (ζ.re - x)])

end

end RHTower.DeBruijn
