import GaloisForLFunctions.RHTower.ShiftedGammaConjugation
import GaloisForLFunctions.HTGeometry.GammaPairingMajorant

/-!
# The shifted Gamma jump commutes with differentiation

The kernel does not see the evaluation point, so differentiating under the integral sign turns the
second difference of a profile into the second difference of its derivative.  The domination is the
corpus's own scale majorant `gammaPairingMajorant`, applied to the *derivative*: it is uniform in
the base point, which is exactly what differentiation under the integral sign requires.

This is the `R` commutes with `D` hypothesis of the exact cutoff forcing identity.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

/-- The shifted jump of a Lipschitz bounded profile converges absolutely. -/
theorem integrableOn_shiftedSecondDifference_mul_kernel {f : ℝ → ℝ} {K B σ : ℝ}
    (hfc : Continuous f)
    (hK : ∀ x y : ℝ, |f x - f y| ≤ K * |x - y|) (hB : ∀ x, |f x| ≤ B)
    (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (L : ℝ) :
    IntegrableOn (fun s => shiftedSecondDifference σ f L s * gammaTransportKernel s) (Ioi 0) := by
  have hmeas : AEStronglyMeasurable
      (fun s => shiftedSecondDifference σ f L s * gammaTransportKernel s)
      (volume.restrict (Ioi 0)) := by
    have hsd : Continuous fun s : ℝ => shiftedSecondDifference σ f L s := by
      have : Continuous fun s : ℝ => 2 * f L - Real.exp (-(σ * s)) * f (L + s)
          - Real.exp (σ * s) * f (L - s) :=
        ((continuous_const.sub
          ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
            (hfc.comp (continuous_const.add continuous_id)))).sub
          ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
            (hfc.comp (continuous_const.sub continuous_id))))
      exact this
    exact hsd.aestronglyMeasurable.mul measurable_gammaTransportKernel.aestronglyMeasurable
  refine Integrable.mono' (integrableOn_gammaPairingMajorant (K := K) (B := B) hσ1) hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  exact abs_shiftedSecondDifference_mul_kernel_le hK hB hσ0 hs L

set_option maxHeartbeats 1000000 in
/-- **The shifted Gamma jump commutes with differentiation.** -/
theorem hasDerivAt_shiftedGammaJump {f f' : ℝ → ℝ} {K B K' B' σ : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hK : ∀ x y : ℝ, |f x - f y| ≤ K * |x - y|) (hB : ∀ x, |f x| ≤ B)
    (hK' : ∀ x y : ℝ, |f' x - f' y| ≤ K' * |x - y|) (hB' : ∀ x, |f' x| ≤ B')
    (hf'c : Continuous f') (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (L : ℝ) :
    HasDerivAt (shiftedGammaJump σ f) (shiftedGammaJump σ f' L) L := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hcont : ∀ y : ℝ, Continuous fun s : ℝ => shiftedSecondDifference σ f y s := by
    intro y
    have : Continuous fun s : ℝ => 2 * f y - Real.exp (-(σ * s)) * f (y + s)
        - Real.exp (σ * s) * f (y - s) :=
      ((continuous_const.sub
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
          (hfc.comp (continuous_const.add continuous_id)))).sub
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
          (hfc.comp (continuous_const.sub continuous_id))))
    exact this
  have hcont' : Continuous fun s : ℝ => shiftedSecondDifference σ f' L s := by
    have : Continuous fun s : ℝ => 2 * f' L - Real.exp (-(σ * s)) * f' (L + s)
        - Real.exp (σ * s) * f' (L - s) :=
      ((continuous_const.sub
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).mul
          (hf'c.comp (continuous_const.add continuous_id)))).sub
        ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
          (hf'c.comp (continuous_const.sub continuous_id))))
    exact this
  have hkey := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun (y : ℝ) (s : ℝ) => shiftedSecondDifference σ f y s * gammaTransportKernel s)
    (F' := fun (y : ℝ) (s : ℝ) => shiftedSecondDifference σ f' y s * gammaTransportKernel s)
    (x₀ := L) (bound := gammaPairingMajorant K' B' σ)
    (s := Metric.ball L 1) (Metric.ball_mem_nhds L one_pos)
    (Filter.Eventually.of_forall fun y =>
      ((hcont y).aestronglyMeasurable.mul
        measurable_gammaTransportKernel.aestronglyMeasurable))
    (integrableOn_shiftedSecondDifference_mul_kernel hfc hK hB hσ0 hσ1 L)
    (hcont'.aestronglyMeasurable.mul measurable_gammaTransportKernel.aestronglyMeasurable)
    ?_ (integrableOn_gammaPairingMajorant hσ1) ?_
  · exact hkey.2
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs y _
    exact abs_shiftedSecondDifference_mul_kernel_le hK' hB' hσ0 hs y
  · filter_upwards with s y _
    have ha : HasDerivAt (fun y : ℝ => f (y + s)) (f' (y + s)) y :=
      HasDerivAt.comp_add_const y s (hf (y + s))
    have hb : HasDerivAt (fun y : ℝ => f (y - s)) (f' (y - s)) y :=
      HasDerivAt.comp_sub_const y s (hf (y - s))
    have h1 : HasDerivAt (fun y : ℝ => 2 * f y - Real.exp (-(σ * s)) * f (y + s)
        - Real.exp (σ * s) * f (y - s))
        (2 * f' y - Real.exp (-(σ * s)) * f' (y + s) - Real.exp (σ * s) * f' (y - s)) y :=
      (((hf y).const_mul 2).sub (ha.const_mul _)).sub (hb.const_mul _)
    exact h1.mul_const (gammaTransportKernel s)

/-- The derivative form. -/
theorem deriv_shiftedGammaJump {f f' : ℝ → ℝ} {K B K' B' σ : ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x)
    (hK : ∀ x y : ℝ, |f x - f y| ≤ K * |x - y|) (hB : ∀ x, |f x| ≤ B)
    (hK' : ∀ x y : ℝ, |f' x - f' y| ≤ K' * |x - y|) (hB' : ∀ x, |f' x| ≤ B')
    (hf'c : Continuous f') (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) (L : ℝ) :
    deriv (shiftedGammaJump σ f) L = shiftedGammaJump σ f' L :=
  (hasDerivAt_shiftedGammaJump hf hK hB hK' hB' hf'c hσ0 hσ1 L).deriv

end GaloisForLFunctions.RHTower
