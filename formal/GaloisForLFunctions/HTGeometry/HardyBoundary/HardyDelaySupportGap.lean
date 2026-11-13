import GaloisForLFunctions.HTGeometry.HalfPlaneHardy

/-!
# Hardy delay bounds force a support gap

Plancherel converts removal of a positive Laplace delay into an exponentially
weighted mass bound. Every shorter initial interval then has zero mass.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- A Hardy bound after removing delay `d` forces zero mass before every `a<d`. -/
theorem integral_initial_sq_eq_zero_of_hardy_delay
    {f : ℝ → ℂ} (hf : MemLp f 2 (volume.restrict (Ioi (0 : ℝ))))
    {d M : ℝ}
    (hH : IsHalfPlaneHardy (fun w => Complex.exp ((d : ℂ) * w) * laplaceRay f w) M)
    {a : ℝ} (ha : a < d) :
    (∫ x in Ioo (0 : ℝ) a, ‖f x‖ ^ (2 : ℕ)) = 0 := by
  have hsub : Ioo (0 : ℝ) a ⊆ Ioi 0 := fun _ hx => hx.1
  have hlocal : IntegrableOn (fun x => ‖f x‖ ^ (2 : ℕ)) (Ioo (0 : ℝ) a) :=
    (integrableOn_norm_sq_of_memLp hf).mono_set hsub
  have hbound (σ : ℝ) (hσ : 0 < σ) :
      (∫ x in Ioo (0 : ℝ) a, ‖f x‖ ^ (2 : ℕ)) ≤
        Real.exp (-(2 * σ * (d - a))) * M := by
    let W : ℝ → ℝ := fun x => Real.exp (2 * σ * d) *
      (Real.exp (-(2 * σ * x)) * ‖f x‖ ^ (2 : ℕ))
    have hi : IntegrableOn W (Ioi (0 : ℝ)) :=
      (integrableOn_exp_mul_norm_sq hf hσ).const_mul _
    have hw : (∫ x in Ioi (0 : ℝ), W x) ≤ M := by
      have hh := hH.bound σ hσ
      have he (ξ : ℝ) :
          ‖Complex.exp ((d : ℂ) * rayLine σ ξ) * laplaceRay f (rayLine σ ξ)‖ ^ (2 : ℕ) =
            Real.exp (2 * σ * d) * ‖laplaceRay f (rayLine σ ξ)‖ ^ (2 : ℕ) := by
        rw [norm_mul, mul_pow, norm_exp]
        simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, rayLine_re]
        rw [sq, ← Real.exp_add]
        congr 2
        ring
      simp_rw [he] at hh
      rw [integral_const_mul, integral_norm_sq_laplaceRay_line hf hσ] at hh
      simpa only [W, integral_const_mul] using hh
    have hcmp (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) a) :
        ‖f x‖ ^ (2 : ℕ) ≤ Real.exp (-(2 * σ * (d - a))) * W x := by
      have he : Real.exp (-(2 * σ * (d - a))) * Real.exp (2 * σ * d) *
          Real.exp (-(2 * σ * x)) = Real.exp (2 * σ * (a - x)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      have hge : 1 ≤ Real.exp (2 * σ * (a - x)) :=
        Real.one_le_exp (mul_nonneg (mul_nonneg (by norm_num) hσ.le) (sub_nonneg.mpr hx.2.le))
      calc
        _ ≤ Real.exp (2 * σ * (a - x)) * ‖f x‖ ^ (2 : ℕ) :=
          le_mul_of_one_le_left (sq_nonneg _) hge
        _ = Real.exp (-(2 * σ * (d - a))) * W x := by
          rw [← he]
          dsimp only [W]
          ring
    have hle := setIntegral_mono_on hlocal
      ((hi.mono_set hsub).const_mul (Real.exp (-(2 * σ * (d - a)))))
      measurableSet_Ioo hcmp
    rw [integral_const_mul] at hle
    have hbig : (∫ x in Ioo (0 : ℝ) a, W x) ≤ ∫ x in Ioi (0 : ℝ), W x :=
      setIntegral_mono_set hi (Eventually.of_forall fun x => by dsimp only [W]; positivity)
        hsub.eventuallyLE
    exact hle.trans (mul_le_mul_of_nonneg_left (hbig.trans hw) (Real.exp_pos _).le)
  have hlim : Tendsto (fun σ : ℝ => Real.exp (-(2 * σ * (d - a))) * M) atTop (𝓝 0) := by
    have hp : 0 < 2 * (d - a) := mul_pos (by norm_num) (sub_pos.mpr ha)
    have ht := tendsto_neg_atTop_atBot.comp (Tendsto.const_mul_atTop hp tendsto_id)
    have he : Tendsto (fun σ : ℝ => -(2 * σ * (d - a))) atTop atBot := by
      apply ht.congr
      intro σ
      change -(2 * (d - a) * σ) = -(2 * σ * (d - a))
      ring
    simpa only [Function.comp_apply, zero_mul] using (Real.tendsto_exp_atBot.comp he).mul_const M
  apply le_antisymm _ (integral_nonneg fun _ => sq_nonneg _)
  apply ge_of_tendsto hlim
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with σ hσ
  exact hbound σ hσ

#print axioms integral_initial_sq_eq_zero_of_hardy_delay

end GaloisForLFunctions.HTGeometry
