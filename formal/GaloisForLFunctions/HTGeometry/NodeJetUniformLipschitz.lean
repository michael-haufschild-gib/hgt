import GaloisForLFunctions.HTGeometry.CompactNodePatchBounds
import GaloisForLFunctions.HTGeometry.HerglotzJetMapContinuity
import GaloisForLFunctions.HTGeometry.JointContinuityFromLipschitz

/-!
# The node-jet map and its uniform Lipschitz estimate

For the compact-patch Baire argument the jet is read at a single node, with the node allowed to move
inside a compact patch off the real axis.  The Lipschitz estimate in the parameter must then hold
with a constant that does not depend on the node.

That is exactly what the uniform kernel bound on the patch supplies: the same argument as for the
fixed-node estimate goes through with the patch bound in place of the pointwise one.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ENNReal

noncomputable section

/-- The jet of order `k` of the parameter's measure, read at a single node. -/
def nodeJet (μ : Measure ℝ) (w : ℝ → ℝ) (k : ℕ) (u : Lp ℝ ⊤ μ) (z : ℂ) : ℂ :=
  ∫ t, ((Real.exp (u t) * w t : ℝ) : ℂ) * (((t : ℝ) : ℂ) - z)⁻¹ ^ (k + 1) ∂μ

/-- Integrability of the node-jet integrand. -/
theorem integrable_nodeJet_integrand (μ : Measure ℝ)
    (w : ℝ → ℝ) (hw : Integrable w μ) (k : ℕ) (u : Lp ℝ ⊤ μ)
    {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (fun t => ((Real.exp (u t) * w t : ℝ) : ℂ) *
      (((t : ℝ) : ℂ) - z)⁻¹ ^ (k + 1)) μ := by
  have hdens := integrable_exp_Lp_top_mul μ u w hw
  refine Integrable.mono' ((hdens.abs).const_mul ((|z.im|⁻¹) ^ (k + 1))) ?_ ?_
  · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
      hdens.aestronglyMeasurable).mul
      (by apply Measurable.aestronglyMeasurable; fun_prop)
  · filter_upwards with t
    rw [norm_mul, Complex.norm_real]
    calc ‖Real.exp (u t) * w t‖ * ‖(((t : ℝ) : ℂ) - z)⁻¹ ^ (k + 1)‖
        ≤ ‖Real.exp (u t) * w t‖ * (|z.im|⁻¹) ^ (k + 1) :=
          mul_le_mul_of_nonneg_left (norm_kernelPow_le hz k t) (norm_nonneg _)
      _ = (|z.im|⁻¹) ^ (k + 1) * |Real.exp (u t) * w t| := by
          rw [Real.norm_eq_abs]; ring

/-- **Uniform Lipschitz estimate for the node jet.**  On a compact node patch off the real axis the
node jet is Lipschitz in the parameter with a constant independent of the node.  Only the uniform
kernel bound is used; compactness enters solely through producing that bound. -/
theorem norm_nodeJet_sub_le_uniform (μ : Measure ℝ)
    (w : ℝ → ℝ) (hw : Integrable w μ) (k : ℕ)
    {K : Set ℂ} (hKne : ∀ z ∈ K, z.im ≠ 0)
    {B : ℝ} (hB : ∀ z ∈ K, ∀ t : ℝ, ‖(((t : ℝ) : ℂ) - z)⁻¹ ^ (k + 1)‖ ≤ B)
    (u₀ u : Lp ℝ ⊤ μ) (hclose : ‖u - u₀‖ ≤ 1) {z : ℂ} (hz : z ∈ K) :
    ‖nodeJet μ w k u z - nodeJet μ w k u₀ z‖ ≤
      (2 * B * ∫ t, Real.exp (u₀ t) * |w t| ∂μ) * ‖u - u₀‖ := by
  have hIu := integrable_nodeJet_integrand μ w hw k u (hKne z hz)
  have hIu₀ := integrable_nodeJet_integrand μ w hw k u₀ (hKne z hz)
  have hdom : Integrable
      (fun t => 2 * B * ‖u - u₀‖ * (Real.exp (u₀ t) * |w t|)) μ :=
    (integrable_exp_Lp_top_mul μ u₀ _ hw.abs).const_mul _
  have hbound : ∀ᵐ t ∂μ,
      ‖((Real.exp (u t) * w t : ℝ) : ℂ) * (((t : ℝ) : ℂ) - z)⁻¹ ^ (k + 1) -
        ((Real.exp (u₀ t) * w t : ℝ) : ℂ) * (((t : ℝ) : ℂ) - z)⁻¹ ^ (k + 1)‖ ≤
        2 * B * ‖u - u₀‖ * (Real.exp (u₀ t) * |w t|) := by
    filter_upwards [ae_norm_le_norm_Lp_top μ (u - u₀), Lp.coeFn_sub u u₀]
      with t ht hsub
    have hdiff : |u t - u₀ t| ≤ ‖u - u₀‖ := by
      have heq : ((u - u₀) t) = u t - u₀ t := by rw [hsub]; simp
      rw [← heq]
      simpa [Real.norm_eq_abs] using ht
    have hone : |u t - u₀ t| ≤ 1 := le_trans hdiff hclose
    have hexp := abs_exp_sub_exp_le hone
    have hfac : ((Real.exp (u t) * w t : ℝ) : ℂ) *
          (((t : ℝ) : ℂ) - z)⁻¹ ^ (k + 1) -
        ((Real.exp (u₀ t) * w t : ℝ) : ℂ) * (((t : ℝ) : ℂ) - z)⁻¹ ^ (k + 1) =
        (((Real.exp (u t) - Real.exp (u₀ t)) * w t : ℝ) : ℂ) *
          (((t : ℝ) : ℂ) - z)⁻¹ ^ (k + 1) := by
      push_cast
      ring
    rw [hfac, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have hstep : |Real.exp (u t) - Real.exp (u₀ t)| * |w t| *
        ‖(((t : ℝ) : ℂ) - z)⁻¹ ^ (k + 1)‖ ≤
        (2 * Real.exp (u₀ t) * ‖u - u₀‖) * |w t| * B := by
      apply mul_le_mul _ (hB z hz t) (norm_nonneg _) (by positivity)
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      exact le_trans hexp (mul_le_mul_of_nonneg_left hdiff (by positivity))
    calc |Real.exp (u t) - Real.exp (u₀ t)| * |w t| *
          ‖(((t : ℝ) : ℂ) - z)⁻¹ ^ (k + 1)‖
        ≤ (2 * Real.exp (u₀ t) * ‖u - u₀‖) * |w t| * B := hstep
      _ = 2 * B * ‖u - u₀‖ * (Real.exp (u₀ t) * |w t|) := by ring
  show ‖(∫ t, ((Real.exp (u t) * w t : ℝ) : ℂ) *
      (((t : ℝ) : ℂ) - z)⁻¹ ^ (k + 1) ∂μ) -
      ∫ t, ((Real.exp (u₀ t) * w t : ℝ) : ℂ) *
        (((t : ℝ) : ℂ) - z)⁻¹ ^ (k + 1) ∂μ‖ ≤ _
  rw [← integral_sub hIu hIu₀]
  refine le_trans (norm_integral_le_integral_norm _) ?_
  refine le_trans (integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun t => norm_nonneg _) hdom hbound) ?_
  rw [integral_const_mul]
  ring_nf
  exact le_refl _

/-- The measure of a bounded parameter: the base measure reweighted by `exp u * w`. -/
def expWeightedMeasure (μ : Measure ℝ) (w : ℝ → ℝ) (u : Lp ℝ ⊤ μ) : Measure ℝ :=
  μ.withDensity (fun t => (Real.toNNReal (Real.exp (u t) * w t) : ℝ≥0∞))

/-- **The node jet is a kernel moment of the parameter's measure.**  This transfers every
node-variable regularity statement for kernel moments to the node jet. -/
theorem nodeJet_eq_cauchyKernelMoment (μ : Measure ℝ) (w : ℝ → ℝ)
    (hwnn : ∀ t, 0 ≤ w t) (hwmeas : AEMeasurable w μ)
    (k : ℕ) (u : Lp ℝ ⊤ μ) (z : ℂ) :
    nodeJet μ w k u z = cauchyKernelMoment (expWeightedMeasure μ w u) k z := by
  have hdens : AEMeasurable
      (fun t => Real.toNNReal (Real.exp (u t) * w t)) μ := by
    apply AEMeasurable.real_toNNReal
    exact ((Real.measurable_exp.comp_aemeasurable
      (Lp.aestronglyMeasurable u).aemeasurable)).mul hwmeas
  rw [cauchyKernelMoment, expWeightedMeasure,
    integral_withDensity_eq_integral_smul₀ hdens, nodeJet]
  apply integral_congr_ae
  filter_upwards with t
  have hnn : 0 ≤ Real.exp (u t) * w t :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) (hwnn t)
  rw [NNReal.smul_def, Complex.real_smul, Real.coe_toNNReal _ hnn]

/-- The parameter's measure is finite: its density is integrable by boundedness of the
parameter. -/
theorem isFiniteMeasure_expWeightedMeasure (μ : Measure ℝ) (w : ℝ → ℝ)
    (hw : Integrable w μ) (hwnn : ∀ t, 0 ≤ w t) (u : Lp ℝ ⊤ μ) :
    IsFiniteMeasure (expWeightedMeasure μ w u) := by
  have hint := integrable_exp_Lp_top_mul μ u w hw
  have hnn : 0 ≤ᵐ[μ] fun t => Real.exp (u t) * w t := by
    filter_upwards with t
    exact mul_nonneg (le_of_lt (Real.exp_pos _)) (hwnn t)
  have hlint : ∫⁻ t, (Real.toNNReal (Real.exp (u t) * w t) : ℝ≥0∞) ∂μ ≠ ⊤ := by
    have heq : ∫⁻ t, (Real.toNNReal (Real.exp (u t) * w t) : ℝ≥0∞) ∂μ =
        ENNReal.ofReal (∫ t, Real.exp (u t) * w t ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
    rw [heq]
    exact ENNReal.ofReal_ne_top
  rw [expWeightedMeasure]
  exact isFiniteMeasure_withDensity hlint

/-- **Joint continuity of the node jet.**  In the interior of a compact node patch off the real
axis, the node jet is continuous in parameter and node jointly.  The parameter side is Lipschitz
uniformly over the patch and the node side is continuous, which is exactly the joint-continuity
criterion. -/
theorem continuousAt_nodeJet_uncurry (μ : Measure ℝ)
    (w : ℝ → ℝ) (hw : Integrable w μ) (hwnn : ∀ t, 0 ≤ w t)
    (hwmeas : AEMeasurable w μ) (k : ℕ)
    {K : Set ℂ} (hK : IsCompact K) (hKne : ∀ z ∈ K, z.im ≠ 0)
    (u₀ : Lp ℝ ⊤ μ) {z₀ : ℂ} (hz₀ : z₀ ∈ interior K) :
    ContinuousAt (fun p : Lp ℝ ⊤ μ × ℂ => nodeJet μ w k p.1 p.2) (u₀, z₀) := by
  obtain ⟨B, hBpos, hB⟩ := exists_uniform_kernelPow_bound hK hKne k
  have hLnonneg : (0 : ℝ) ≤ 2 * B * ∫ t, Real.exp (u₀ t) * |w t| ∂μ := by
    apply mul_nonneg (by positivity)
    exact integral_nonneg fun t => by positivity
  apply continuousAt_uncurry_of_lipschitz_of_continuousAt
    (F := fun u z => nodeJet μ w k u z) hLnonneg
    (V := interior K) (isOpen_interior.mem_nhds hz₀) (r := 1) one_pos
  · intro z hz u hu
    have hzK : z ∈ K := interior_subset hz
    have hclose : ‖u - u₀‖ ≤ 1 := by
      have := Metric.mem_ball.mp hu
      rw [dist_eq_norm] at this
      exact le_of_lt this
    rw [dist_eq_norm]
    exact norm_nodeJet_sub_le_uniform μ w hw k hKne hB u₀ u hclose hzK
  · haveI := isFiniteMeasure_expWeightedMeasure μ w hw hwnn u₀
    have heq : (fun z => nodeJet μ w k u₀ z) =
        fun z => cauchyKernelMoment (expWeightedMeasure μ w u₀) k z := by
      funext z
      exact nodeJet_eq_cauchyKernelMoment μ w hwnn hwmeas k u₀ z
    rw [heq]
    exact (continuousOn_cauchyKernelMoment (expWeightedMeasure μ w u₀) k
      (U := interior K) (fun z hz => hKne z (interior_subset hz))).continuousAt
      (isOpen_interior.mem_nhds hz₀)

end

end GaloisForLFunctions.HTGeometry
