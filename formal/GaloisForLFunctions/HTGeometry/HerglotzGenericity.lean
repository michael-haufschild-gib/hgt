import GaloisForLFunctions.HTGeometry.HerglotzJetMap
import GaloisForLFunctions.HTGeometry.LogGaugeLift
import GaloisForLFunctions.HTGeometry.AffineReachabilityGenericity

/-!
# Genericity of nondegenerate Herglotz parameters

Assembling the chart.  From a base parameter `u₀`, perturbing the density multiplicatively by
`1 + h` moves the parameter to `u₀ + log (1 + h)` — a change of size at most `2 ‖h‖` — and moves
the jets by exactly the weighted control map applied to `h`.  Both statements are equalities, not
estimates: no derivative of the chart is taken anywhere.

That is precisely the affine reachability hypothesis, whose linear part is surjective at every base
parameter.  Hence the parameters on which a fixed nonzero polynomial jet relation fails to
degenerate are dense.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The exponential density of a gauged parameter factors pointwise almost everywhere. -/
theorem exp_gauged_parameter_ae (μ : Measure ℝ) (u₀ h : Lp ℝ ⊤ μ)
    (hh : ‖h‖ ≤ 1 / 2) :
    ∀ᵐ t ∂μ, Real.exp ((u₀ + logOneAddLp μ h hh) t) =
      Real.exp (u₀ t) * (1 + h t) := by
  filter_upwards [Lp.coeFn_add u₀ (logOneAddLp μ h hh),
    logOneAddLp_coeFn μ h hh, ae_norm_le_norm_Lp_top μ h] with t hadd hlog hnorm
  have habs : |h t| ≤ 1 / 2 :=
    le_trans (by simpa [Real.norm_eq_abs] using hnorm) hh
  rw [hadd]
  simp only [Pi.add_apply]
  rw [hlog]
  exact exp_add_log_one_add habs

omit [DecidableEq ι] in
/-- **Reachability for the Herglotz chart.**  The jets of a multiplicatively gauged parameter are
exactly the base jets plus the weighted control applied to the gauge. -/
theorem herglotzJetMap_gauged (μ : Measure ℝ)
    (w : ℝ → ℝ) (hw : Integrable w μ) (x : ι → ℂ) (hne : ∀ i, (x i).im ≠ 0)
    (n : ι → ℕ) (u₀ h : Lp ℝ ⊤ μ) (hh : ‖h‖ ≤ 1 / 2) :
    herglotzJetMap μ w x n (u₀ + logOneAddLp μ h hh) =
      herglotzJetMap μ w x n u₀ +
        weightedJetControl μ (fun t => Real.exp (u₀ t) * w t)
          (integrable_exp_Lp_top_mul μ u₀ w hw) x hne n h := by
  funext s
  have hbase := integrable_weight_mul_cauchyJetKernel μ
    (fun t => Real.exp (u₀ t) * w t) (integrable_exp_Lp_top_mul μ u₀ w hw)
    x hne n s
  have hgauge := integrable_Lp_top_mul_weight μ h
    (fun t => Real.exp (u₀ t) * w t) (integrable_exp_Lp_top_mul μ u₀ w hw)
    _ (aestronglyMeasurable_cauchyJetKernel μ x n s)
    (norm_cauchyJetKernel_le x hne n s)
  have hsplit : ∀ᵐ t ∂μ,
      ((Real.exp ((u₀ + logOneAddLp μ h hh) t) * w t : ℝ) : ℂ) *
          cauchyJetKernel x n t s =
        ((Real.exp (u₀ t) * w t : ℝ) : ℂ) * cauchyJetKernel x n t s +
          ((h t : ℝ) : ℂ) *
            ((Real.exp (u₀ t) * w t : ℝ) : ℂ) * cauchyJetKernel x n t s := by
    filter_upwards [exp_gauged_parameter_ae μ u₀ h hh] with t ht
    rw [ht]
    push_cast
    ring
  show ∫ t, ((Real.exp ((u₀ + logOneAddLp μ h hh) t) * w t : ℝ) : ℂ) *
      cauchyJetKernel x n t s ∂μ = _
  rw [integral_congr_ae hsplit, integral_add hbase hgauge]
  rfl

/-- **Generic nondegeneracy of Herglotz parameters.**  For a base measure of infinite support with
a strictly positive integrable Nevanlinna density, the bounded parameters on which a fixed nonzero
polynomial jet relation fails to degenerate are dense. -/
theorem dense_nondegenerate_herglotzJetMap
    (μ : Measure ℝ) (hsupp : μ.support.Infinite)
    (w : ℝ → ℝ) (hw : Integrable w μ) (hwpos : ∀ t, 0 < w t)
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (P : MvPolynomial (jetIndex n) ℂ) (hP : P ≠ 0) :
    Dense {u : Lp ℝ ⊤ μ |
      MvPolynomial.eval (herglotzJetMap μ w x n u) P ≠ 0} := by
  classical
  set hne : ∀ i, (x i).im ≠ 0 := fun i => ne_of_gt (hupper i) with hnedef
  apply dense_nondegenerate_of_affine_reachability
    (herglotzJetMap μ w x n) P hP
  intro u₀ ε hε
  refine ⟨min (1 / 2) (ε / 2), by positivity, _,
    surjective_weightedJetControl_expDensity μ hsupp w hw hwpos x hx hupper n u₀,
    ?_⟩
  intro h hhδ
  have hhalf : ‖h‖ ≤ 1 / 2 :=
    le_of_lt (lt_of_lt_of_le hhδ (min_le_left _ _))
  have hheps : ‖h‖ < ε / 2 := lt_of_lt_of_le hhδ (min_le_right _ _)
  refine ⟨u₀ + logOneAddLp μ h hhalf, ?_, ?_⟩
  · rw [dist_eq_norm, add_sub_cancel_left]
    calc ‖logOneAddLp μ h hhalf‖ ≤ 2 * ‖h‖ := norm_logOneAddLp_le μ h hhalf
      _ < ε := by linarith
  · exact herglotzJetMap_gauged μ w hw x hne n u₀ h hhalf

end

end GaloisForLFunctions.HTGeometry
