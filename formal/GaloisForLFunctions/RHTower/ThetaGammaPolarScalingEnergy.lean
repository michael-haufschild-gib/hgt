import GaloisForLFunctions.RHTower.ThetaGammaPolarScalingKernel

/-!
# A convergent continuous Gamma/pole energy

The squared increment of a Schwartz profile cancels the singularity at zero.
The actual source decay controls the growing polar translation at infinity.
Consequently the signed continuous energy is an ordinary absolutely convergent
integral on the whole positive shift ray and the whole source line.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped SchwartzMap

namespace RHTower.ThetaSourceWard

abbrev thetaContinuousLinkMeasure : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioi (0 : ℝ))).prod volume

def thetaGammaPolarScalingDensity (S : ThetaSource) (chi : 𝓢(ℝ, ℂ)) (p : ℝ × ℝ) : ℝ :=
  thetaGammaPolarScalingKernel p.1 * S.k p.2 * S.k (p.2 + p.1) *
    ‖chi (p.2 + p.1) - chi p.2‖ ^ 2

def thetaGammaPolarScalingEnergy (S : ThetaSource) (chi : 𝓢(ℝ, ℂ)) : ℝ :=
  ∫ p, thetaGammaPolarScalingDensity S chi p ∂thetaContinuousLinkMeasure

/-- The singular coefficient is controlled after a squared increment and exponential damping. -/
theorem thetaGammaPolar_damped_square_bound {u : ℝ} (hu : 0 < u) :
    |thetaGammaPolarScalingKernel u| * Real.exp (-2 * u) * u ^ 2 ≤
      (2 * u ^ 2 + u / 2) * Real.exp (-u / 2) := by
  have hd : 0 < 1 - Real.exp (-2 * u) := by
    have := Real.exp_lt_one_iff.mpr (show -2 * u < 0 by linarith)
    linarith
  have hp : 0 ≤ 2 * Real.cosh (u / 2) := by positivity
  have hg : 0 ≤ Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) := by positivity
  have hab : |thetaGammaPolarScalingKernel u| ≤
      2 * Real.cosh (u / 2) + Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) := by
    simpa only [thetaGammaPolarScalingKernel, Real.norm_eq_abs,
      abs_of_nonneg hp, abs_of_nonneg hg] using
      norm_sub_le (2 * Real.cosh (u / 2)) (Real.exp (-u / 2) / (1 - Real.exp (-2 * u)))
  have hden : 2 * u * Real.exp (-2 * u) ≤ 1 - Real.exp (-2 * u) := by
    simpa only [neg_mul] using exp_neg_le_one_sub_exp_neg_div (2 * u)
  have hgam : Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) *
      Real.exp (-2 * u) * u ^ 2 ≤ u / 2 * Real.exp (-u / 2) := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ hd]
    nlinarith [mul_le_mul_of_nonneg_left hden
      (show 0 ≤ u / 2 * Real.exp (-u / 2) by positivity)]
  have hcosh : Real.cosh (u / 2) ≤ Real.exp (u / 2) := by
    rw [Real.cosh_eq]
    have := Real.exp_le_exp.mpr (show -(u / 2) ≤ u / 2 by linarith)
    linarith
  have hexp : Real.exp (u / 2) * Real.exp (-2 * u) ≤ Real.exp (-u / 2) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hpol : 2 * Real.cosh (u / 2) * Real.exp (-2 * u) * u ^ 2 ≤
      2 * u ^ 2 * Real.exp (-u / 2) := by
    calc
      _ ≤ 2 * Real.exp (u / 2) * Real.exp (-2 * u) * u ^ 2 := by gcongr
      _ = 2 * u ^ 2 * (Real.exp (u / 2) * Real.exp (-2 * u)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp (by positivity)
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hab (Real.exp_pos (-2 * u)).le) (sq_nonneg u)
  calc
    _ ≤ (2 * Real.cosh (u / 2) + Real.exp (-u / 2) / (1 - Real.exp (-2 * u))) *
        Real.exp (-2 * u) * u ^ 2 := h
    _ = (2 * Real.cosh (u / 2) * Real.exp (-2 * u) * u ^ 2) +
        (Real.exp (-u / 2) / (1 - Real.exp (-2 * u)) * Real.exp (-2 * u) * u ^ 2) := by ring
    _ ≤ 2 * u ^ 2 * Real.exp (-u / 2) + u / 2 * Real.exp (-u / 2) := add_le_add hpol hgam
    _ = _ := by ring

/-- One separable exponential bound controls every forward source pair. -/
theorem thetaSource_shiftPair_decay (S : ThetaSource) :
    ∃ C : ℝ, 0 < C ∧ ∀ x u : ℝ, 0 ≤ u →
      S.k x * S.k (x + u) ≤ C ^ 2 * Real.exp (-2 * |x|) * Real.exp (-2 * u) := by
  obtain ⟨C, hC, hb⟩ := S.decay 4
  refine ⟨C, hC, fun x u hu => ?_⟩
  have htri : u ≤ |x| + |x + u| := by
    have h := norm_sub_le (x + u) x
    simp only [Real.norm_eq_abs, add_sub_cancel_left, abs_of_nonneg hu] at h
    linarith
  have he : Real.exp (-(4 * |x|)) * Real.exp (-(4 * |x + u|)) ≤
      Real.exp (-2 * |x|) * Real.exp (-2 * u) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [abs_nonneg (x + u)]
  calc
    _ ≤ (C * Real.exp (-(4 * |x|))) * (C * Real.exp (-(4 * |x + u|))) :=
      mul_le_mul (hb x) (hb (x + u)) (S.pos _).le (by positivity)
    _ = C ^ 2 * (Real.exp (-(4 * |x|)) * Real.exp (-(4 * |x + u|))) := by ring
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left he (sq_nonneg C)

private theorem schwartz_increment_bound (chi : 𝓢(ℝ, ℂ)) (x u : ℝ) :
    ‖chi (x + u) - chi x‖ ≤ SchwartzMap.seminorm ℝ 0 1 chi * |u| := by
  have hder (y : ℝ) : ‖deriv chi y‖ ≤ SchwartzMap.seminorm ℝ 0 1 chi := by
    simpa only [pow_zero, one_mul, iteratedDeriv_one] using chi.le_seminorm' ℝ 0 1 y
  have h := convex_univ.norm_image_sub_le_of_norm_deriv_le
    (fun y _ => chi.differentiableAt (x := y)) (fun y _ => hder y)
    (mem_univ x) (mem_univ (x + u))
  simpa only [add_sub_cancel_left, Real.norm_eq_abs] using h

/-- Absolute convergence of the full signed continuous Gamma/pole energy. -/
theorem integrable_thetaGammaPolarScalingDensity (S : ThetaSource) (chi : 𝓢(ℝ, ℂ)) :
    Integrable (thetaGammaPolarScalingDensity S chi) thetaContinuousLinkMeasure := by
  obtain ⟨C, hC, hb⟩ := thetaSource_shiftPair_decay S
  let D := SchwartzMap.seminorm ℝ 0 1 chi
  have hD : 0 ≤ D := apply_nonneg (SchwartzMap.seminorm ℝ 0 1) chi
  have hi₁ := HTGeometry.integrable_abs_pow_mul_exp_neg_abs 1
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have hi₂ := HTGeometry.integrable_abs_pow_mul_exp_neg_abs 2
    (show (0 : ℝ) < 1 / 2 by norm_num)
  have hix : Integrable (fun x : ℝ => Real.exp (-2 * |x|)) := by
    simpa only [pow_zero, one_mul] using
      HTGeometry.integrable_abs_pow_mul_exp_neg_abs 0 (show (0 : ℝ) < 2 by norm_num)
  have hiu : IntegrableOn (fun u : ℝ =>
      (2 * |u| ^ 2 + |u| / 2) * Real.exp (-(1 / 2) * |u|)) (Ioi 0) := by
    convert! ((hi₂.const_mul 2).add (hi₁.div_const 2)).integrableOn using 1
    ext u
    simp only [Pi.add_apply]
    ring
  have hm : Measurable (thetaGammaPolarScalingDensity S chi) := by
    have hsc := S.cont.measurable
    have hcc := chi.continuous.measurable
    unfold thetaGammaPolarScalingDensity thetaGammaPolarScalingKernel
    fun_prop
  have hmajor := (hiu.mul_prod hix).const_mul (C ^ 2 * D ^ 2)
  apply hmajor.mono' hm.aestronglyMeasurable
  have hpos : ∀ᵐ p : ℝ × ℝ ∂thetaContinuousLinkMeasure, 0 < p.1 := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact Eventually.of_forall fun _ => hu
  filter_upwards [hpos] with p hp
  have hinc := schwartz_increment_bound chi p.2 p.1
  rw [abs_of_pos hp] at hinc
  have hsq : ‖chi (p.2 + p.1) - chi p.2‖ ^ 2 ≤ D ^ 2 * p.1 ^ 2 := by
    calc
      _ ≤ (D * p.1) ^ 2 := by gcongr
      _ = _ := by ring
  simp only [thetaGammaPolarScalingDensity, Real.norm_eq_abs, abs_mul,
    abs_of_pos (S.pos p.2), abs_of_pos (S.pos (p.2 + p.1)),
    abs_of_nonneg (sq_nonneg ‖chi (p.2 + p.1) - chi p.2‖)]
  calc
    _ = |thetaGammaPolarScalingKernel p.1| * (S.k p.2 * S.k (p.2 + p.1)) *
        ‖chi (p.2 + p.1) - chi p.2‖ ^ 2 := by ring
    _ ≤ |thetaGammaPolarScalingKernel p.1| *
        (C ^ 2 * Real.exp (-2 * |p.2|) * Real.exp (-2 * p.1)) *
          (D ^ 2 * p.1 ^ 2) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (hb _ _ hp.le) (abs_nonneg _)) hsq
        (sq_nonneg _) (by positivity)
    _ = C ^ 2 * D ^ 2 * Real.exp (-2 * |p.2|) *
        (|thetaGammaPolarScalingKernel p.1| * Real.exp (-2 * p.1) * p.1 ^ 2) := by ring
    _ ≤ C ^ 2 * D ^ 2 * Real.exp (-2 * |p.2|) *
        ((2 * p.1 ^ 2 + p.1 / 2) * Real.exp (-p.1 / 2)) :=
      mul_le_mul_of_nonneg_left (thetaGammaPolar_damped_square_bound hp) (by positivity)
    _ = _ := by
      rw [abs_of_pos hp, show -(1 / 2 : ℝ) * p.1 = -p.1 / 2 by ring]
      ring

/-- Fubini retains the complete continuum of shifts. -/
theorem thetaGammaPolarScalingEnergy_eq_iterated (S : ThetaSource) (chi : 𝓢(ℝ, ℂ)) :
    thetaGammaPolarScalingEnergy S chi =
      ∫ u in Ioi (0 : ℝ), ∫ x : ℝ,
        thetaGammaPolarScalingKernel u * S.k x * S.k (x + u) * ‖chi (x + u) - chi x‖ ^ 2 :=
  integral_prod _ (integrable_thetaGammaPolarScalingDensity S chi)

end RHTower.ThetaSourceWard
