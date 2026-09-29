import GaloisForLFunctions.HTGeometry.HamburgerFunctionalEquation

/-!
# Hamburger's odd theorem from the right half-plane

The odd case of Hamburger's theorem, with the functional equation replaced by a boundary
condition on the critical line.  Let `f(s) = Σ a_n n^{-s}`, and let `Γ_ℝ(s) f(s) - β Γ_ℝ(s - 1)` be
continuous on `1/2 ≤ Re s ≤ 3/2`, holomorphic inside and `O(1/(1 + t²))`.  If it is odd across the
line, `E(s) + E(1 - s) = -β (Γ_ℝ(s - 1) + Γ_ℝ(-s))` for `Re s = 1/2`, then `f = 0`
(`coeff_eq_zero_of_critical_line_odd`).

No continuation to `Re s < 1/2` and no Schwarz reflection is used.
* The theta series is an inverse Mellin integral on `Re s = 3/2`, shifted onto the critical line
  itself (`critical_line_inverse_mellin`).  The shift is
  `integral_vertical_line_eq_of_horizontal_tendsto_of_continuousOn`, which needs only continuity
  up to the boundary line.
* Evaluating at `x` and `1/x` and reflecting `t ↦ -t` gives an integral that only sees
  `E(s) + E(1 - s)`.
* That combination is the Mellin transform of the explicit function
  `-β (t^{-1/2}(e^{-πt} - 1) + (e^{-π/t} - 1))`.
* The result is the odd theta relation `θ(x) + x^{-1/2}θ(1/x) = β(1 + x^{-1/2})`
  (`critical_line_odd_theta_relation`), which forces `a = 0`
  (`coeff_eq_zero_of_odd_coeffTheta_relation`).

This is the form needed when the data live only on the right half-plane.  An example is a
Dirichlet series `ζ·D` built from a Herglotz function whose boundary real part is carried by the
zeros of `ζ`.
-/

open Complex MeasureTheory Filter Topology Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- **Contour shift onto a boundary line.**  As `integral_vertical_line_eq_of_horizontal_tendsto`,
but `G` need only be continuous on the closed strip and holomorphic on the open strip. -/
theorem integral_vertical_line_eq_of_horizontal_tendsto_of_continuousOn {G : ℂ → ℂ} {c d : ℝ}
    (hcd : c ≤ d) (hcont : ContinuousOn G (verticalStrip c d))
    (hdiff : DifferentiableOn ℂ G {z : ℂ | c < z.re ∧ z.re < d})
    (hc : Integrable fun y : ℝ => G ((c : ℂ) + (y : ℝ) * I))
    (hd : Integrable fun y : ℝ => G ((d : ℂ) + (y : ℝ) * I))
    (hbot : Tendsto (fun T : ℝ => ∫ u in c..d, G ((u : ℂ) + ((-T : ℝ) : ℂ) * I)) atTop (𝓝 0))
    (htop : Tendsto (fun T : ℝ => ∫ u in c..d, G ((u : ℂ) + ((T : ℝ) : ℂ) * I)) atTop (𝓝 0)) :
    (∫ y : ℝ, G ((d : ℂ) + (y : ℝ) * I)) = ∫ y : ℝ, G ((c : ℂ) + (y : ℝ) * I) := by
  have hrect : ∀ T : ℝ,
      ((∫ x : ℝ in c..d, G ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
          - (∫ x : ℝ in c..d, G ((x : ℂ) + ((T : ℝ) : ℂ) * I))
          + I • (∫ y : ℝ in (-T)..T, G ((d : ℂ) + (y : ℝ) * I)))
        - I • (∫ y : ℝ in (-T)..T, G ((c : ℂ) + (y : ℝ) * I)) = 0 := by
    intro T
    have hz : ((c : ℂ) + ((-T : ℝ) : ℂ) * I).re = c := by simp
    have hz' : ((c : ℂ) + ((-T : ℝ) : ℂ) * I).im = -T := by simp
    have hw : ((d : ℂ) + ((T : ℝ) : ℂ) * I).re = d := by simp
    have hw' : ((d : ℂ) + ((T : ℝ) : ℂ) * I).im = T := by simp
    have hsubc : ContinuousOn G
        (uIcc ((c : ℂ) + ((-T : ℝ) : ℂ) * I).re ((d : ℂ) + ((T : ℝ) : ℂ) * I).re ×ℂ
          uIcc ((c : ℂ) + ((-T : ℝ) : ℂ) * I).im ((d : ℂ) + ((T : ℝ) : ℂ) * I).im) := by
      rw [hz, hz', hw, hw']
      exact hcont.mono (rect_subset_verticalStrip hcd T)
    have hsubd : DifferentiableOn ℂ G
        (Ioo (min ((c : ℂ) + ((-T : ℝ) : ℂ) * I).re ((d : ℂ) + ((T : ℝ) : ℂ) * I).re)
            (max ((c : ℂ) + ((-T : ℝ) : ℂ) * I).re ((d : ℂ) + ((T : ℝ) : ℂ) * I).re) ×ℂ
          Ioo (min ((c : ℂ) + ((-T : ℝ) : ℂ) * I).im ((d : ℂ) + ((T : ℝ) : ℂ) * I).im)
            (max ((c : ℂ) + ((-T : ℝ) : ℂ) * I).im ((d : ℂ) + ((T : ℝ) : ℂ) * I).im)) := by
      rw [hz, hw, min_eq_left hcd, max_eq_right hcd]
      refine hdiff.mono fun z hz => ?_
      rw [Complex.mem_reProdIm] at hz
      exact ⟨hz.1.1, hz.1.2⟩
    have hcauchy := Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn G
      ((c : ℂ) + ((-T : ℝ) : ℂ) * I) ((d : ℂ) + ((T : ℝ) : ℂ) * I) hsubc hsubd
    rw [hz, hz', hw, hw'] at hcauchy
    exact hcauchy
  have hlimd : Tendsto (fun T : ℝ => ∫ y : ℝ in (-T)..T, G ((d : ℂ) + (y : ℝ) * I)) atTop
      (𝓝 (∫ y : ℝ, G ((d : ℂ) + (y : ℝ) * I))) :=
    intervalIntegral_tendsto_integral hd tendsto_neg_atTop_atBot tendsto_id
  have hlimc : Tendsto (fun T : ℝ => ∫ y : ℝ in (-T)..T, G ((c : ℂ) + (y : ℝ) * I)) atTop
      (𝓝 (∫ y : ℝ, G ((c : ℂ) + (y : ℝ) * I))) :=
    intervalIntegral_tendsto_integral hc tendsto_neg_atTop_atBot tendsto_id
  have hcomb := ((hbot.sub htop).add (hlimd.const_smul I)).sub (hlimc.const_smul I)
  have hzero : Tendsto (fun T : ℝ =>
      ((∫ x : ℝ in c..d, G ((x : ℂ) + ((-T : ℝ) : ℂ) * I))
          - (∫ x : ℝ in c..d, G ((x : ℂ) + ((T : ℝ) : ℂ) * I))
          + I • (∫ y : ℝ in (-T)..T, G ((d : ℂ) + (y : ℝ) * I)))
        - I • (∫ y : ℝ in (-T)..T, G ((c : ℂ) + (y : ℝ) * I))) atTop (𝓝 0) := by
    simp only [hrect]
    exact tendsto_const_nhds
  have heq := tendsto_nhds_unique hcomb hzero
  have hI : I * ((∫ y : ℝ, G ((d : ℂ) + (y : ℝ) * I)) - ∫ y : ℝ, G ((c : ℂ) + (y : ℝ) * I))
      = I * 0 := by
    rw [mul_zero, mul_sub]
    simpa [smul_eq_mul] using heq
  have := mul_left_cancel₀ Complex.I_ne_zero hI
  linear_combination this

/-- `t^{-1/2}(e^{-πt} - 1)` has Mellin transform `Γ_ℝ(s - 1)` at `s/2` for `-1 < Re s < 1`. -/
theorem hasMellin_halfPow_expNegSubOne_pi {s : ℂ} (h1 : -1 < s.re) (h2 : s.re < 1) :
    HasMellin (fun t : ℝ => (t : ℂ) ^ (-(1 / 2 : ℂ)) * expNegSubOne (Real.pi * t)) (s / 2)
      (Complex.Gammaℝ (s - 1)) := by
  have hc : MellinConvergent
      (fun t : ℝ => (t : ℂ) ^ (-(1 / 2 : ℂ)) • expNegSubOne (Real.pi * t)) (s / 2) := by
    refine MellinConvergent.cpow_smul.mpr ?_
    rw [show s / 2 + -(1 / 2 : ℂ) = (s - 1) / 2 by ring]
    exact mellinConvergent_exp_neg_pi_sub_one_half (by simp; linarith) (by simp; linarith)
  refine ⟨hc, ?_⟩
  show mellin (fun t : ℝ => (t : ℂ) ^ (-(1 / 2 : ℂ)) • expNegSubOne (Real.pi * t)) (s / 2) = _
  rw [mellin_cpow_smul, show s / 2 + -(1 / 2 : ℂ) = (s - 1) / 2 by ring]
  exact mellin_exp_neg_pi_sub_one_half (by simp; linarith) (by simp; linarith)

/-- `e^{-π/t} - 1` has Mellin transform `Γ_ℝ(-s)` at `s/2` for `0 < Re s < 2`. -/
theorem hasMellin_expNegSubOne_pi_inv {s : ℂ} (h1 : 0 < s.re) (h2 : s.re < 2) :
    HasMellin (fun t : ℝ => expNegSubOne (Real.pi * t⁻¹)) (s / 2) (Complex.Gammaℝ (-s)) := by
  have hinv : (fun t : ℝ => expNegSubOne (Real.pi * t⁻¹)) =
      fun t : ℝ => (fun u : ℝ => expNegSubOne (Real.pi * u)) (t ^ (-1 : ℝ)) := by
    funext t
    rw [Real.rpow_neg_one]
  have hc : MellinConvergent (fun t : ℝ => expNegSubOne (Real.pi * t⁻¹)) (s / 2) := by
    rw [hinv]
    refine (MellinConvergent.comp_rpow (f := fun u : ℝ => expNegSubOne (Real.pi * u))
      (by norm_num : (-1 : ℝ) ≠ 0)).mpr ?_
    rw [show s / 2 / ((-1 : ℝ) : ℂ) = (-s) / 2 by push_cast; ring]
    exact mellinConvergent_exp_neg_pi_sub_one_half (by simp; linarith) (by simp; linarith)
  refine ⟨hc, ?_⟩
  rw [mellin_comp_inv (fun u : ℝ => expNegSubOne (Real.pi * u)),
    show -(s / 2) = (-s) / 2 by ring]
  exact mellin_exp_neg_pi_sub_one_half (by simp; linarith) (by simp; linarith)

theorem ofReal_inv_cpow_eq {x : ℝ} (hx : 0 < x) (z : ℂ) :
    ((x⁻¹ : ℝ) : ℂ) ^ z = (x : ℂ) ^ (-z) := by
  have harg : (x : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact Real.pi_pos.ne
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ harg, Complex.cpow_neg]

theorem ofReal_cpow_mul_ofReal_cpow {x : ℝ} (hx : 0 < x) (a b : ℂ) :
    (x : ℂ) ^ a * (x : ℂ) ^ b = (x : ℂ) ^ (a + b) := by
  rw [Complex.cpow_add _ _ (by exact_mod_cast hx.ne')]

/-- The inverse-Mellin representation on the critical line.  Under the hypotheses of
`critical_line_odd_theta_relation`, for every `y > 0`,
`θ(y) - β y^{-1/2} e^{-πy} = (1/2π) ∫ y^{-(1/4+it)} E(1/2 + 2it) dt`. -/
theorem critical_line_inverse_mellin {θ : ℝ → ℂ} {E : ℂ → ℂ} {β : ℂ} {C : ℝ}
    (hθc : ContinuousOn θ (Ioi 0)) (hθm : MellinConvergent θ (3 / 4))
    (hEc : ContinuousOn E (verticalStrip (1 / 2) (3 / 2)))
    (hEd : DifferentiableOn ℂ E {s : ℂ | 1 / 2 < s.re ∧ s.re < 3 / 2})
    (hdecay : ∀ s ∈ verticalStrip (1 / 2) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2))
    (hR : ∀ s : ℂ, s.re = 3 / 2 → mellin θ (s / 2) = E s + β * Complex.Gammaℝ (s - 1))
    {y : ℝ} (hy : 0 < y) :
    θ y - β * ((y : ℂ) ^ (-(1 / 2 : ℂ)) * expNegPi y) =
      (1 / (2 * Real.pi)) • ∫ t : ℝ, (y : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
        E (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) := by
  set φ : ℝ → ℂ := fun u => θ u - ((0 : ℂ) * expNegPi u +
    β * ((u : ℂ) ^ (-(1 / 2 : ℂ)) * expNegPi u)) with hφ
  have hφ_eq : φ y = θ y - β * ((y : ℂ) ^ (-(1 / 2 : ℂ)) * expNegPi y) := by
    simp [hφ]
  have hdata : ∀ t : ℝ, HasMellin φ (((3 / 4 : ℝ) : ℂ) + t * I) (E (2 * (((3 / 4 : ℝ) : ℂ) + t * I))) := by
    intro t
    set w : ℂ := ((3 / 4 : ℝ) : ℂ) + t * I with hw
    have hs : (2 * w).re = 3 / 2 := by simp [hw]; norm_num
    have h2w : 2 * w / 2 = w := by ring
    have hpol := hasMellin_polarRight 0 β (s := 2 * w) (by rw [hs]; norm_num)
    rw [h2w] at hpol
    have hθ : MellinConvergent θ w := MellinConvergent.of_re_eq hθm (by simp [hw])
    have hsub := hasMellin_sub hθ hpol.1
    refine ⟨hsub.1, ?_⟩
    rw [hsub.2, hpol.2]
    have := hR (2 * w) hs
    rw [h2w] at this
    rw [this]
    ring
  have hcont : ContinuousAt φ y := by
    have h1 : ContinuousAt θ y := hθc.continuousAt (Ioi_mem_nhds hy)
    have h2 : ContinuousAt (fun u : ℝ => (u : ℂ) ^ (-(1 / 2 : ℂ))) y :=
      continuousAt_ofReal_cpow_const _ _ (Or.inr hy.ne')
    exact h1.sub ((continuousAt_const.mul continuous_expNegPi.continuousAt).add
      (continuousAt_const.mul (h2.mul continuous_expNegPi.continuousAt)))
  have hvert : VerticalIntegrable (mellin φ) (3 / 4 : ℝ) := by
    have h := integrable_cpow_mul_comp_line hEc hdecay (σ := 3 / 4) (by norm_num) (by norm_num)
      (x := 1) one_pos
    refine h.congr (Eventually.of_forall fun t => ?_)
    simp only [ofReal_one, one_cpow, one_mul]
    exact ((hdata t).2).symm
  have hconv : MellinConvergent φ ((3 / 4 : ℝ) : ℂ) := by simpa using (hdata 0).1
  have hinv := mellinInv_mellin_eq (3 / 4 : ℝ) φ hy hconv hvert hcont
  set G : ℂ → ℂ := fun w => (y : ℂ) ^ (-w) * E (2 * w) with hG
  have hI : mellinInv (3 / 4 : ℝ) (mellin φ) y =
      (1 / (2 * Real.pi)) • ∫ t : ℝ, G (((3 / 4 : ℝ) : ℂ) + t * I) := by
    unfold mellinInv
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hG, smul_eq_mul]
    rw [(hdata t).2]
  have hmaps : ∀ w ∈ verticalStrip (1 / 4) (3 / 4), 2 * w ∈ verticalStrip (1 / 2) (3 / 2) := by
    intro w hw
    rw [mem_verticalStrip] at hw ⊢
    simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
    constructor <;> linarith [hw.1, hw.2]
  have hGc : ContinuousOn G (verticalStrip (1 / 4) (3 / 4)) := by
    refine ContinuousOn.mul ?_ ?_
    · exact (Continuous.const_cpow continuous_neg
        (Or.inl (by exact_mod_cast hy.ne'))).continuousOn
    · exact hEc.comp (continuous_const.mul continuous_id).continuousOn hmaps
  have hGd : DifferentiableOn ℂ G {z : ℂ | 1 / 4 < z.re ∧ z.re < 3 / 4} := by
    refine DifferentiableOn.mul ?_ ?_
    · intro w _
      exact (differentiableAt_id.neg.const_cpow
        (Or.inl (by exact_mod_cast hy.ne'))).differentiableWithinAt
    · refine hEd.comp (differentiable_id.const_mul (2 : ℂ)).differentiableOn fun w hw => ?_
      simp only [Set.mem_setOf_eq] at hw ⊢
      simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]
      constructor <;> linarith [hw.1, hw.2]
  have hshift : (∫ t : ℝ, G (((3 / 4 : ℝ) : ℂ) + t * I)) =
      ∫ t : ℝ, G (((1 / 4 : ℝ) : ℂ) + t * I) := by
    refine integral_vertical_line_eq_of_horizontal_tendsto_of_continuousOn (by norm_num) hGc hGd
      (integrable_cpow_mul_comp_line hEc hdecay (by norm_num) (by norm_num) hy)
      (integrable_cpow_mul_comp_line hEc hdecay (by norm_num) (by norm_num) hy) ?_ ?_
    · exact tendsto_integral_horizontal_cpow_mul_comp hdecay (by norm_num) (by norm_num)
        (by norm_num) hy (h := fun T => -T) (fun T => by ring)
    · exact tendsto_integral_horizontal_cpow_mul_comp hdecay (by norm_num) (by norm_num)
        (by norm_num) hy (h := fun T => T) (fun T => rfl)
  rw [← hφ_eq, ← hinv, hI, hshift]

/-- **The odd theta relation from the critical line.**  Let `θ` be continuous on `(0, ∞)` and
Mellin-convergent at `3/4`, and suppose that `M θ(s/2) = E(s) + β Γ_ℝ(s - 1)` on `Re s = 3/2`.  Here
`E` is continuous on `1/2 ≤ Re s ≤ 3/2`, holomorphic inside, and `O(1/(1 + t²))`.  If on the critical line
`E(s) + E(1 - s) = -β (Γ_ℝ(s - 1) + Γ_ℝ(-s))`, then
`θ(x) + x^{-1/2} θ(1/x) = β (1 + x^{-1/2})` for all `x > 0`.

The critical-line condition says that `Γ_ℝ(s) f(s)` is odd across the line: its pole part is
`β Γ_ℝ(s - 1)`.  No continuation to the left of the line is used.  Both `θ(x)` and `θ(1/x)` are
inverse Mellin integrals over the critical line.  Their sum only sees `E(s) + E(1 - s)`, whose
inverse Mellin transform is that of `-β (t^{-1/2}(e^{-πt} - 1) + (e^{-π/t} - 1))`. -/
theorem critical_line_odd_theta_relation {θ : ℝ → ℂ} {E : ℂ → ℂ} {β : ℂ} {C : ℝ}
    (hθc : ContinuousOn θ (Ioi 0)) (hθm : MellinConvergent θ (3 / 4))
    (hEc : ContinuousOn E (verticalStrip (1 / 2) (3 / 2)))
    (hEd : DifferentiableOn ℂ E {s : ℂ | 1 / 2 < s.re ∧ s.re < 3 / 2})
    (hdecay : ∀ s ∈ verticalStrip (1 / 2) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2))
    (hR : ∀ s : ℂ, s.re = 3 / 2 → mellin θ (s / 2) = E s + β * Complex.Gammaℝ (s - 1))
    (hC : ∀ s : ℂ, s.re = 1 / 2 →
      E s + E (1 - s) = -(β * (Complex.Gammaℝ (s - 1) + Complex.Gammaℝ (-s))))
    {x : ℝ} (hx : 0 < x) :
    θ x + (x : ℂ) ^ (-(1 / 2 : ℂ)) * θ x⁻¹ = β * (1 + (x : ℂ) ^ (-(1 / 2 : ℂ))) := by
  have hR1 := critical_line_inverse_mellin hθc hθm hEc hEd hdecay hR hx
  have hR2 := critical_line_inverse_mellin hθc hθm hEc hEd hdecay hR (inv_pos.mpr hx)
  rw [Complex.real_smul] at hR1 hR2
  set K : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ) with hK
  have hre : ∀ t : ℝ, (2 * (((1 / 4 : ℝ) : ℂ) + t * I)).re = 1 / 2 := by
    intro t; simp; norm_num
  have hint1 : Integrable fun t : ℝ => (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
      E (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) :=
    integrable_cpow_mul_comp_line hEc hdecay (by norm_num) (by norm_num) hx
  have hpt : ∀ t : ℝ, (x : ℂ) ^ (-(1 / 2 : ℂ)) *
      (((x⁻¹ : ℝ) : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)) *
        E (2 * (((1 / 4 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I))) =
      (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) * E (1 - 2 * (((1 / 4 : ℝ) : ℂ) + t * I)) := by
    intro t
    rw [ofReal_inv_cpow_eq hx, ← mul_assoc, ofReal_cpow_mul_ofReal_cpow hx]
    push_cast
    congr 2 <;> ring
  have hint2 : Integrable fun t : ℝ => (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
      E (1 - 2 * (((1 / 4 : ℝ) : ℂ) + t * I)) := by
    have h := (integrable_cpow_mul_comp_line hEc hdecay (σ := 1 / 4) (by norm_num) (by norm_num)
      (inv_pos.mpr hx)).comp_neg
    exact ((h.const_mul ((x : ℂ) ^ (-(1 / 2 : ℂ))))).congr
      (Eventually.of_forall fun t => hpt t)
  have hreflect : (x : ℂ) ^ (-(1 / 2 : ℂ)) * ∫ t : ℝ,
      ((x⁻¹ : ℝ) : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) * E (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) =
      ∫ t : ℝ, (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
        E (1 - 2 * (((1 / 4 : ℝ) : ℂ) + t * I)) := by
    rw [← integral_const_mul, ← integral_neg_eq_self]
    exact integral_congr_ae (Eventually.of_forall fun t => hpt t)
  have hhalf : (x : ℂ) ^ (-(1 / 2 : ℂ)) * ((x⁻¹ : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) = 1 := by
    rw [ofReal_inv_cpow_eq hx, ofReal_cpow_mul_ofReal_cpow hx]
    norm_num
  -- the Gamma-sum integral
  set J : ℂ := ∫ t : ℝ, (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
      (Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I) - 1) +
        Complex.Gammaℝ (-(2 * (((1 / 4 : ℝ) : ℂ) + t * I)))) with hJ
  have hsumint : (∫ t : ℝ, (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
      E (2 * (((1 / 4 : ℝ) : ℂ) + t * I))) + ∫ t : ℝ, (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) *
        E (1 - 2 * (((1 / 4 : ℝ) : ℂ) + t * I)) = -β * J := by
    rw [← integral_add hint1 hint2, hJ, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    beta_reduce
    rw [← mul_add, hC _ (hre t)]
    ring
  have hsum : (θ x - β * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * expNegPi x)) +
      (x : ℂ) ^ (-(1 / 2 : ℂ)) * (θ x⁻¹ - β * (((x⁻¹ : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) * expNegPi x⁻¹))
      = K * (-β * J) := by
    rw [hR1, hR2, ← hsumint, ← hreflect]
    ring
  -- the correction function and its inverse Mellin transform
  set f₂ : ℝ → ℂ := fun u => (u : ℂ) ^ (-(1 / 2 : ℂ)) * expNegSubOne (Real.pi * u) +
    expNegSubOne (Real.pi * u⁻¹) with hf₂
  have hdata₂ : ∀ t : ℝ, HasMellin f₂ (((1 / 4 : ℝ) : ℂ) + t * I)
      (Complex.Gammaℝ (2 * (((1 / 4 : ℝ) : ℂ) + t * I) - 1) +
        Complex.Gammaℝ (-(2 * (((1 / 4 : ℝ) : ℂ) + t * I)))) := by
    intro t
    have hs := hre t
    have h2w : 2 * (((1 / 4 : ℝ) : ℂ) + t * I) / 2 = ((1 / 4 : ℝ) : ℂ) + t * I := by ring
    have hA := hasMellin_halfPow_expNegSubOne_pi (s := 2 * (((1 / 4 : ℝ) : ℂ) + t * I))
      (by rw [hs]; norm_num) (by rw [hs]; norm_num)
    have hB := hasMellin_expNegSubOne_pi_inv (s := 2 * (((1 / 4 : ℝ) : ℂ) + t * I))
      (by rw [hs]; norm_num) (by rw [hs]; norm_num)
    rw [h2w] at hA hB
    have hC' := hasMellin_add hA.1 hB.1
    refine ⟨hC'.1, ?_⟩
    rw [hC'.2, hA.2, hB.2]
  have hβJ : β * J = β * (2 * Real.pi) * f₂ x := by
    by_cases hβ : β = 0
    · rw [hβ]; ring
    have hvert : VerticalIntegrable (mellin f₂) (1 / 4 : ℝ) := by
      have h1 := integrable_cpow_mul_comp_line hEc hdecay (σ := 1 / 4) (by norm_num)
        (by norm_num) (x := 1) one_pos
      have h2 := h1.comp_neg
      refine ((h1.add h2).const_mul (-β⁻¹)).congr (Eventually.of_forall fun t => ?_)
      simp only [ofReal_one, one_cpow, one_mul]
      show -β⁻¹ * (E (2 * (((1 / 4 : ℝ) : ℂ) + t * I)) +
        E (2 * (((1 / 4 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I))) = _
      rw [(hdata₂ t).2]
      have h := hC _ (hre t)
      have hneg : 2 * (((1 / 4 : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) =
          1 - 2 * (((1 / 4 : ℝ) : ℂ) + t * I) := by push_cast; ring
      rw [hneg, h]
      field_simp
    have hconv₂ : MellinConvergent f₂ ((1 / 4 : ℝ) : ℂ) := by simpa using (hdata₂ 0).1
    have hcont₂ : ContinuousAt f₂ x := by
      have h1 : ContinuousAt (fun u : ℝ => (u : ℂ) ^ (-(1 / 2 : ℂ))) x :=
        continuousAt_ofReal_cpow_const _ _ (Or.inr hx.ne')
      have h2 : ContinuousAt (fun u : ℝ => expNegSubOne (Real.pi * u)) x :=
        (continuous_expNegSubOne.comp (continuous_const.mul continuous_id)).continuousAt
      have h3 : ContinuousAt (fun u : ℝ => expNegSubOne (Real.pi * u⁻¹)) x :=
        continuous_expNegSubOne.continuousAt.comp
          (continuousAt_const.mul (continuousAt_inv₀ hx.ne'))
      exact (h1.mul h2).add h3
    have hinv₂ := mellinInv_mellin_eq (1 / 4 : ℝ) f₂ hx hconv₂ hvert hcont₂
    unfold mellinInv at hinv₂
    rw [Complex.real_smul] at hinv₂
    have hJ' : J = ∫ t : ℝ, (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) •
        mellin f₂ (((1 / 4 : ℝ) : ℂ) + t * I) := by
      rw [hJ]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      beta_reduce
      rw [smul_eq_mul, (hdata₂ t).2]
    have hc : ((1 / (2 * Real.pi) : ℝ) : ℂ) * (2 * Real.pi) = 1 := by
      have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      push_cast
      field_simp
    rw [← hinv₂, hJ']
    linear_combination (-β * (∫ t : ℝ, (x : ℂ) ^ (-(((1 / 4 : ℝ) : ℂ) + t * I)) •
      mellin f₂ (((1 / 4 : ℝ) : ℂ) + t * I))) * hc
  have hf₂x : f₂ x = (x : ℂ) ^ (-(1 / 2 : ℂ)) * (expNegPi x - 1) + (expNegPi x⁻¹ - 1) := by
    simp only [hf₂, expNegSubOne_pi_mul]
  have hK2 : K * (2 * Real.pi) = 1 := by
    rw [hK]
    push_cast
    field_simp
  have hmain : K * (-β * J) = -(β * f₂ x) := by
    rw [neg_mul, hβJ]
    linear_combination (-(β * f₂ x)) * hK2
  rw [hmain, hf₂x] at hsum
  linear_combination hsum + β * expNegPi x⁻¹ * hhalf

/-- **Odd Hamburger theorem from the right half-plane.**  Let `f(s) = Σ a_n n^{-s}` converge
absolutely for `Re s > 1`.  Suppose `Γ_ℝ(s) f(s) = E(s) + β Γ_ℝ(s - 1)` on `Re s = 3/2`, where `E`
is continuous on `1/2 ≤ Re s ≤ 3/2`, holomorphic inside and `O(1/(1 + t²))` there.  Suppose also
that on the critical line `E(s) + E(1 - s) = -β (Γ_ℝ(s - 1) + Γ_ℝ(-s))`, i.e. `Γ_ℝ f` is odd
across the line.  Then `f = 0`.

Only data on `Re s ≥ 1/2` enter.  The oddness across the line is a boundary condition, and no
continuation to the left half-plane or Schwarz reflection is needed. -/
theorem coeff_eq_zero_of_critical_line_odd {a : ℕ → ℂ} {E : ℂ → ℂ} {β : ℂ} {C : ℝ}
    (ha : ∀ σ : ℝ, 1 < σ → Summable fun n : ℕ => ‖a (n + 1)‖ / ((n : ℝ) + 1) ^ σ)
    (hEc : ContinuousOn E (verticalStrip (1 / 2) (3 / 2)))
    (hEd : DifferentiableOn ℂ E {s : ℂ | 1 / 2 < s.re ∧ s.re < 3 / 2})
    (hdecay : ∀ s ∈ verticalStrip (1 / 2) (3 / 2), ‖E s‖ ≤ C / (1 + s.im ^ 2))
    (hR : ∀ s : ℂ, s.re = 3 / 2 →
      Complex.Gammaℝ s * coeffDirichlet a s = E s + β * Complex.Gammaℝ (s - 1))
    (hC : ∀ s : ℂ, s.re = 1 / 2 →
      E s + E (1 - s) = -(β * (Complex.Gammaℝ (s - 1) + Complex.Gammaℝ (-s))))
    (n : ℕ) : a (n + 1) = 0 := by
  have htheta : ∀ x : ℝ, 0 < x → coeffTheta a x =
      (-1) * ((x : ℂ) ^ (-(1 / 2 : ℂ)) * coeffTheta a x⁻¹) + β + β * (x : ℂ) ^ (-(1 / 2 : ℂ)) := by
    intro x hx
    have h := critical_line_odd_theta_relation (θ := coeffTheta a)
      (continuousOn_coeffTheta a (ha 2 (by norm_num)))
      (mellinConvergent_coeffTheta a ha (by norm_num) (by norm_num)) hEc hEd hdecay
      (fun s hs => by rw [mellin_coeffTheta a ha (by rw [hs]; norm_num)]; exact hR s hs) hC hx
    linear_combination h
  exact coeff_eq_zero_of_odd_coeffTheta_relation ha htheta n

end GaloisForLFunctions.HTGeometry
