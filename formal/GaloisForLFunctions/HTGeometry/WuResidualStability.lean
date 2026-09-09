import GaloisForLFunctions.HTGeometry.WuPropagatorEnergy
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Residual certification for a genuine unitary equation

The residual-control strategy in Section 2.3 of arXiv:2609.08421 can be
implemented without nonlinear geometric assumptions for the corpus's bounded
Schrödinger equation. Every Schwartz candidate trajectory has a constructed
Schwartz equation residual. Passing to the interaction frame turns its error
into a curve whose derivative is exactly the unitarily transported residual.
The mean-value estimate gives stability, and Wu's exponential integration
then gives an inverse-cubic-rate squared-energy bound for the damped error.
This is a linear evolution application of the strategy, not the nonlinear
Einstein residual theorem.
-/
namespace GaloisForLFunctions.HTGeometry.Wu
open MeasureTheory Set
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {𝓗 : Type*} [NormedAddCommGroup 𝓗] [InnerProductSpace ℂ 𝓗] [CompleteSpace 𝓗]

/-- The exact defect in `u' = -i(H+H*)u`. -/
def schrodingerResidual (H : 𝓗 →L[ℂ] 𝓗) (u : SchwartzMap ℝ 𝓗) : SchwartzMap ℝ 𝓗 :=
  SchwartzMap.derivCLM ℂ 𝓗 u - u.postcompCLM ((-Complex.I) • hermitianGenerator H)

theorem schrodingerResidual_apply (H : 𝓗 →L[ℂ] 𝓗) (u : SchwartzMap ℝ 𝓗) (t : ℝ) :
    schrodingerResidual H u t = deriv u t - (-Complex.I) • hermitianGenerator H (u t) := rfl

/-- Removing the exact free evolution from the candidate trajectory. -/
def interactionFrame (H : 𝓗 →L[ℂ] 𝓗) (u : SchwartzMap ℝ 𝓗) (t : ℝ) : 𝓗 :=
  propagator (hermitianGenerator H) (-t) (u t)

/-- The interaction derivative is precisely the transported equation defect. -/
theorem interactionFrame_hasDerivAt (H : 𝓗 →L[ℂ] 𝓗) (u : SchwartzMap ℝ 𝓗) (t : ℝ) :
    HasDerivAt (interactionFrame H u)
      (propagator (hermitianGenerator H) (-t) (schrodingerResidual H u t)) t := by
  let K := hermitianGenerator H
  let A : 𝓗 →L[ℂ] 𝓗 := (-Complex.I) • K
  have hd : HasDerivAt (fun s : ℝ => propagator K (-s))
      (-(A ∘L propagator K (-t))) t := by
    convert (hasDerivAt_propagator K (-t)).scomp t (hasDerivAt_neg t) using 1 <;>
      first | rfl | simp [A]
  have hc : Commute (propagator K (-t)) A :=
    ((Commute.refl A).smul_left (-t)).exp_left
  have he : A (propagator K (-t) (u t)) = propagator K (-t) (A (u t)) :=
    (congrArg (fun L : 𝓗 →L[ℂ] 𝓗 => L (u t)) hc.eq).symm
  have hdR := (ContinuousLinearMap.restrictScalarsL ℂ 𝓗 𝓗 ℝ ℝ).hasFDerivAt.comp_hasDerivAt t hd
  convert! hdR.clm_apply (u.hasDerivAt t) using 1
  change propagator K (-t) (deriv u t - A (u t)) =
    -(A (propagator K (-t) (u t))) + propagator K (-t) (deriv u t)
  rw [he, map_sub]
  abel

/-- The true solution error is exactly the error in the interaction frame. -/
theorem norm_schrodinger_error_eq (H : 𝓗 →L[ℂ] 𝓗) (u : SchwartzMap ℝ 𝓗) (t : ℝ) :
    ‖u t - propagator (hermitianGenerator H) t (u 0)‖ =
      ‖interactionFrame H u t - interactionFrame H u 0‖ := by
  have he : propagator (hermitianGenerator H) t
      (interactionFrame H u t - interactionFrame H u 0) =
      u t - propagator (hermitianGenerator H) t (u 0) := by
    simp only [interactionFrame, neg_zero, propagator_zero, one_apply_eq_self, map_sub]
    have hg := congrArg (fun L : 𝓗 →L[ℂ] 𝓗 => L (u t))
      (propagator_comp (hermitianGenerator H) t (-t))
    simpa using hg
  rw [← he, norm_propagator_apply (hermitianGenerator_selfAdjoint H)]

/-- A posteriori stability from the actual equation residual, with all regularity discharged. -/
theorem schrodinger_error_le_residual (H : 𝓗 →L[ℂ] 𝓗) (u : SchwartzMap ℝ 𝓗) (t : ℝ) :
    ‖u t - propagator (hermitianGenerator H) t (u 0)‖ ≤
      ‖(schrodingerResidual H u).toBoundedContinuousFunction‖ * |t| := by
  rw [norm_schrodinger_error_eq]
  have hd (s : ℝ) := interactionFrame_hasDerivAt H u s
  have hb (s : ℝ) : ‖deriv (interactionFrame H u) s‖ ≤
      ‖(schrodingerResidual H u).toBoundedContinuousFunction‖ := by
    rw [(hd s).deriv, norm_propagator_apply (hermitianGenerator_selfAdjoint H)]
    exact (schrodingerResidual H u).toBoundedContinuousFunction.norm_coe_le_norm s
  have hm := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun s (_ : s ∈ (univ : Set ℝ)) => (hd s).differentiableAt)
    (fun s _ => hb s) (convex_univ : Convex ℝ (univ : Set ℝ)) (mem_univ 0) (mem_univ t)
  simpa only [sub_zero, Real.norm_eq_abs] using hm

/-- Positive exponential damping uniformly controls linear-in-time accumulation. -/
theorem damped_time_le (d t : ℝ) :
    Real.exp (-(Real.exp d * |t|)) * |t| ≤ 1 / Real.exp d := by
  apply (le_div_iff₀ (Real.exp_pos d)).mpr
  calc Real.exp (-(Real.exp d * |t|)) * |t| * Real.exp d =
      Real.exp (-(Real.exp d * |t|)) * (Real.exp d * |t|) := by ring
    _ ≤ Real.exp (-(Real.exp d * |t|)) * Real.exp (Real.exp d * |t|) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      linarith [Real.add_one_le_exp (Real.exp d * |t|)]
    _ = 1 := by rw [← Real.exp_add]; simp

/-- The actual solution error, placed in the exponential frame used by the energy estimate. -/
def dampedSchrodingerError (H : 𝓗 →L[ℂ] 𝓗) (u : SchwartzMap ℝ 𝓗) (d : ℝ) :
    BoundedContinuousFunction ℝ 𝓗 :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => Real.exp (-(Real.exp d * |t|)) •
      (u t - propagator (hermitianGenerator H) t (u 0)))
    ((by fun_prop : Continuous (fun t : ℝ => Real.exp (-(Real.exp d * |t|)))).smul
      (u.continuous.sub ((continuous_propagator _).clm_apply continuous_const)))
    (‖(schrodingerResidual H u).toBoundedContinuousFunction‖ / Real.exp d)
    (fun t => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (-(Real.exp d * |t|)) * ‖u t - propagator (hermitianGenerator H) t (u 0)‖ ≤
          Real.exp (-(Real.exp d * |t|)) *
            (‖(schrodingerResidual H u).toBoundedContinuousFunction‖ * |t|) :=
          mul_le_mul_of_nonneg_left (schrodinger_error_le_residual H u t) (Real.exp_pos _).le
        _ = ‖(schrodingerResidual H u).toBoundedContinuousFunction‖ *
            (Real.exp (-(Real.exp d * |t|)) * |t|) := by ring
        _ ≤ ‖(schrodingerResidual H u).toBoundedContinuousFunction‖ * (1 / Real.exp d) :=
          mul_le_mul_of_nonneg_left (damped_time_le d t)
            (norm_nonneg (schrodingerResidual H u).toBoundedContinuousFunction)
        _ = _ := by ring)

/-- Combining residual certification with Wu integration yields inverse-cubic-rate squared energy. -/
theorem schrodinger_residual_energy_le (H : 𝓗 →L[ℂ] 𝓗) (u : SchwartzMap ℝ 𝓗) (d t : ℝ) :
    energy d t (fun s => Real.exp (-(Real.exp d * |s|)) •
      (u s - propagator (hermitianGenerator H) s (u 0))) ≤
      ‖(schrodingerResidual H u).toBoundedContinuousFunction‖ ^ 2 / (2 * Real.exp d ^ 3) := by
  have hb : ‖dampedSchrodingerError H u d‖ ≤
      ‖(schrodingerResidual H u).toBoundedContinuousFunction‖ / Real.exp d :=
    BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (by positivity) _
  calc energy d t (fun s => Real.exp (-(Real.exp d * |s|)) •
      (u s - propagator (hermitianGenerator H) s (u 0))) ≤
      ‖dampedSchrodingerError H u d‖ ^ 2 / (2 * Real.exp d) := energy_le d t (dampedSchrodingerError H u d)
    _ ≤ (‖(schrodingerResidual H u).toBoundedContinuousFunction‖ / Real.exp d) ^ 2 /
        (2 * Real.exp d) :=
      div_le_div_of_nonneg_right ((sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hb) (by positivity)
    _ = _ := by ring

end
end GaloisForLFunctions.HTGeometry.Wu
