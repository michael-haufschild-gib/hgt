import GaloisForLFunctions.HTGeometry.HalfPlaneHardyMul
import GaloisForLFunctions.HTGeometry.ResolventSubordination

/-!
# The Cauchy kernel of the half-plane inside its Hardy space

`w ↦ (w + c)⁻¹` with `Re c > 0` is the half-line Laplace transform of `x ↦ e^{-cx}`, hence lies in
the Hardy space of the right half-plane with mass `(2 Re c)⁻¹`; and it is bounded there by
`(Re c)⁻¹`, so multiplying by it keeps a Hardy function in the Hardy space.  This is Burnol's
division by `s` (arXiv:math/0203120, Lem. 4.4) in the half-plane variable `s = w + 1/2`.

## Main results

* `laplaceRay_expRay`
* `isHalfPlaneHardy_inv_shift`
* `isHalfPlaneHardy_mul_inv_shift`
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set Complex Filter Topology

noncomputable section

/-- Hardy membership only depends on the values on the open half-plane. -/
theorem IsHalfPlaneHardy.congr {F G : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M)
    (h : ∀ w : ℂ, 0 < w.re → F w = G w) : IsHalfPlaneHardy G M where
  holo := hF.holo.congr (fun w hw => (h w hw).symm)
  memLp := by
    intro σ hσ
    refine (hF.memLp σ hσ).ae_eq (Filter.Eventually.of_forall fun ξ => ?_)
    exact h _ (by simpa using hσ)
  bound := by
    intro σ hσ
    have hcongr : (∫ ξ : ℝ, ‖G (rayLine σ ξ)‖ ^ 2) = ∫ ξ : ℝ, ‖F (rayLine σ ξ)‖ ^ 2 := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      show ‖G (rayLine σ ξ)‖ ^ 2 = ‖F (rayLine σ ξ)‖ ^ 2
      rw [h _ (by simpa using hσ : (0:ℝ) < (rayLine σ ξ).re)]
    rw [hcongr]
    exact hF.bound σ hσ

/-- **The Cauchy kernel is the Laplace transform of a decaying exponential.** -/
theorem laplaceRay_expRay {c : ℂ} (hc : 0 < c.re) {w : ℂ} (hw : 0 < w.re) :
    laplaceRay (expRay c) w = (w + c)⁻¹ := by
  have hsum : 0 < (w + c).re := by
    rw [Complex.add_re]
    linarith
  rw [laplaceRay]
  have hcongr : (∫ x in Ioi (0 : ℝ), expRay c x * expRay w x)
      = ∫ x in Ioi (0 : ℝ), Complex.exp (-((w + c) * ((x : ℝ) : ℂ))) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    rw [expRay, expRay, ← Complex.exp_add]
    congr 1
    ring
  rw [hcongr, integral_Ioi_cexp_neg hsum, one_div]

/-- **The Cauchy kernel lies in the Hardy space of the half-plane.** -/
theorem isHalfPlaneHardy_inv_shift {c : ℂ} (hc : 0 < c.re) :
    IsHalfPlaneHardy (fun w => (w + c)⁻¹) (1 / (2 * c.re)) := by
  have hmem : MemLp (expRay c) 2 (volume.restrict (Ioi (0 : ℝ))) :=
    memLp_two_expRay_restrict hc 0
  have h := isHalfPlaneHardy_laplaceRay hmem
  rw [integral_norm_sq_expRay hc 0] at h
  have hval : Real.exp (-(2 * c.re * 0)) / (2 * c.re) = 1 / (2 * c.re) := by norm_num
  rw [hval] at h
  exact h.congr (fun w hw => laplaceRay_expRay hc hw)

theorem norm_inv_shift_le {c : ℂ} (hc : 0 < c.re) {w : ℂ} (hw : 0 < w.re) :
    ‖(w + c)⁻¹‖ ≤ (c.re)⁻¹ := by
  have hre : c.re ≤ (w + c).re := by
    rw [Complex.add_re]
    linarith
  have hnorm : (w + c).re ≤ ‖w + c‖ := Complex.re_le_norm _
  have hpos : (0 : ℝ) < ‖w + c‖ := lt_of_lt_of_le hc (le_trans hre hnorm)
  rw [norm_inv]
  exact inv_anti₀ hc (le_trans hre hnorm)

theorem differentiableOn_inv_shift {c : ℂ} (hc : 0 < c.re) :
    DifferentiableOn ℂ (fun w : ℂ => (w + c)⁻¹) {w : ℂ | 0 < w.re} := by
  refine DifferentiableOn.inv ?_ (fun w hw => ?_)
  · exact (differentiableOn_id.add_const c)
  · intro hzero
    have hre : (w + c).re = 0 := by rw [hzero]; simp
    have hw' : (0 : ℝ) < w.re := hw
    rw [Complex.add_re] at hre
    linarith

/-- **Burnol's division by `s`.**  Multiplying by the Cauchy kernel keeps a Hardy function in the
Hardy space. -/
theorem isHalfPlaneHardy_mul_inv_shift {F : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M) {c : ℂ}
    (hc : 0 < c.re) :
    IsHalfPlaneHardy (fun w => F w * (w + c)⁻¹) ((c.re)⁻¹ ^ 2 * M) :=
  isHalfPlaneHardy_mul_of_bounded hF (differentiableOn_inv_shift hc)
    (fun _ hw => norm_inv_shift_le hc hw)

/-! ### Linear algebra of the Hardy space -/

theorem isHalfPlaneHardy_const_mul {F : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M) (c : ℂ) :
    IsHalfPlaneHardy (fun w => c * F w) (‖c‖ ^ 2 * M) := by
  have h := isHalfPlaneHardy_mul_of_bounded hF (g := fun _ : ℂ => c)
    (differentiableOn_const c) (C := ‖c‖) (fun w _ => le_refl _)
  exact h.congr (fun w _ => by ring)

theorem isHalfPlaneHardy_add {F G : ℂ → ℂ} {M N : ℝ} (hF : IsHalfPlaneHardy F M)
    (hG : IsHalfPlaneHardy G N) :
    IsHalfPlaneHardy (fun w => F w + G w) (2 * M + 2 * N) where
  holo := hF.holo.add hG.holo
  memLp := fun σ hσ => (hF.memLp σ hσ).add (hG.memLp σ hσ)
  bound := by
    intro σ hσ
    have hmF := hF.memLp σ hσ
    have hmG := hG.memLp σ hσ
    have hsqF : Integrable (fun ξ : ℝ => ‖F (rayLine σ ξ)‖ ^ 2) volume :=
      (memLp_two_iff_integrable_sq_norm hmF.aestronglyMeasurable).1 hmF
    have hsqG : Integrable (fun ξ : ℝ => ‖G (rayLine σ ξ)‖ ^ 2) volume :=
      (memLp_two_iff_integrable_sq_norm hmG.aestronglyMeasurable).1 hmG
    have hsum := hmF.add hmG
    have hsqS : Integrable (fun ξ : ℝ => ‖F (rayLine σ ξ) + G (rayLine σ ξ)‖ ^ 2) volume :=
      (memLp_two_iff_integrable_sq_norm hsum.aestronglyMeasurable).1 hsum
    have hptwise : ∀ ξ : ℝ, ‖F (rayLine σ ξ) + G (rayLine σ ξ)‖ ^ 2
        ≤ 2 * ‖F (rayLine σ ξ)‖ ^ 2 + 2 * ‖G (rayLine σ ξ)‖ ^ 2 := by
      intro ξ
      have h1 : ‖F (rayLine σ ξ) + G (rayLine σ ξ)‖
          ≤ ‖F (rayLine σ ξ)‖ + ‖G (rayLine σ ξ)‖ := norm_add_le _ _
      have h2 : ‖F (rayLine σ ξ) + G (rayLine σ ξ)‖ ^ 2
          ≤ (‖F (rayLine σ ξ)‖ + ‖G (rayLine σ ξ)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith [sq_nonneg (‖F (rayLine σ ξ)‖ - ‖G (rayLine σ ξ)‖)]
    calc (∫ ξ : ℝ, ‖F (rayLine σ ξ) + G (rayLine σ ξ)‖ ^ 2)
        ≤ ∫ ξ : ℝ, (2 * ‖F (rayLine σ ξ)‖ ^ 2 + 2 * ‖G (rayLine σ ξ)‖ ^ 2) :=
          integral_mono hsqS ((hsqF.const_mul 2).add (hsqG.const_mul 2)) hptwise
      _ = 2 * (∫ ξ : ℝ, ‖F (rayLine σ ξ)‖ ^ 2) + 2 * ∫ ξ : ℝ, ‖G (rayLine σ ξ)‖ ^ 2 := by
          rw [MeasureTheory.integral_add (hsqF.const_mul 2) (hsqG.const_mul 2),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      _ ≤ 2 * M + 2 * N := by
          have h1 := hF.bound σ hσ
          have h2 := hG.bound σ hσ
          linarith


/-- Iterated division by the Cauchy kernel. -/
theorem isHalfPlaneHardy_mul_inv_shift_pow {F : ℂ → ℂ} {M : ℝ} (hF : IsHalfPlaneHardy F M)
    {c : ℂ} (hc : 0 < c.re) (l : ℕ) :
    ∃ N : ℝ, IsHalfPlaneHardy (fun w => F w * ((w + c)⁻¹) ^ l) N := by
  induction l with
  | zero => exact ⟨M, hF.congr (fun w _ => by simp)⟩
  | succ n ih =>
    obtain ⟨N, hN⟩ := ih
    refine ⟨_, (isHalfPlaneHardy_mul_inv_shift hN hc).congr (fun w _ => ?_)⟩
    ring


end

end GaloisForLFunctions.HTGeometry
