import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogarithmicStepProfiles
import GaloisForLFunctions.RHTower.EulerMaclaurinCountertermQuadratureAndOneSidedPBAP

/-!
# Mass and pole moments of complete logarithmic cells

The same step profiles recover continuous weighted moments on their common
compact window. In particular, both signed pole moments and square mass survive
the limit without moment constraints on the source.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells

theorem tendsto_logStep {f : ℝ → ℝ} {K : NNReal} (hf : LipschitzWith K f)
    (R : ℝ) (hs : ∀ u, u ≤ -R → f u = 0) (u : ℝ) :
    Tendsto (fun N : ℕ => logStep f R N u) atTop (𝓝 (f u)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => dist_nonneg)
    ?_ (tendsto_const_div_atTop_nhds_zero_nat (K : ℝ))
  filter_upwards [eventually_ge_atTop 1] with N hN
  simpa only [Real.dist_eq] using abs_logStep_sub_le hf R hN hs u

/-- Continuous weighted source moments converge on the unchanged support window. -/
theorem tendsto_integral_comp_logStep {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (R : ℝ) {B : ℕ} (hB : 1 ≤ B)
    (hs : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u = 0)
    (ψ w : ℝ → ℝ) (hψ : Continuous ψ) (hψ0 : ψ 0 = 0) (hw : Continuous w) :
    Tendsto (fun N : ℕ => ∫ u, w u * ψ (logStep f R (N + 1) u)) atTop
      (𝓝 (∫ u, w u * ψ (f u))) := by
  obtain ⟨K, hK⟩ := _root_.RHTower.CHMDDoobGraph.compact_source_lipschitz hf hc
  have hcompc : HasCompactSupport (fun u => ψ (f u)) := hc.comp_left hψ0
  obtain ⟨C, hC⟩ := hcompc.exists_bound_of_continuous (hψ.comp hf.continuous)
  let window := Icc (-R) (Real.log B - R)
  apply tendsto_integral_of_dominated_convergence
    (window.indicator (fun u => |w u| * C))
  · intro N
    exact (hw.measurable.mul (hψ.measurable.comp
      (measurable_logStep hf.continuous.measurable R (by omega)))).aestronglyMeasurable
  · exact (integrable_indicator_iff measurableSet_Icc).mpr
      (hw.abs.mul continuous_const).integrableOn_Icc
  · intro N
    apply Eventually.of_forall
    intro u
    by_cases hu : u ∈ window
    · rw [indicator_of_mem hu, norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hC (logCellPoint R (N + 1) u)) (abs_nonneg _)
    · have hout : u ≤ -R ∨ Real.log B - R ≤ u := by
        dsimp only [window] at hu
        simp only [mem_Icc, not_and_or, not_le] at hu
        exact hu.elim (fun h => Or.inl h.le) (fun h => Or.inr h.le)
      rw [logStep_eq_zero_outside R (by omega) hB hs hout, hψ0, mul_zero, norm_zero,
        indicator_of_notMem hu]
  · apply Eventually.of_forall
    intro u
    have ht := (tendsto_logStep hK R (fun x hx => hs x (Or.inl hx)) u).comp
      (tendsto_add_atTop_nat 1)
    exact tendsto_const_nhds.mul ((hψ.tendsto (f u)).comp ht)

theorem tendsto_logStep_mass {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (R : ℝ) {B : ℕ} (hB : 1 ≤ B)
    (hs : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => ∫ u, logStep f R (N + 1) u ^ 2) atTop
      (𝓝 (∫ u, f u ^ 2)) := by
  simpa only [one_mul] using tendsto_integral_comp_logStep hf hc R hB hs
    (fun x => x ^ 2) (fun _ => 1) (continuous_id.pow 2) (by norm_num) continuous_const

theorem tendsto_logStep_coshHalfMoment {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (R : ℝ) {B : ℕ} (hB : 1 ≤ B)
    (hs : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => coshHalfMoment (logStep f R (N + 1))) atTop
      (𝓝 (coshHalfMoment f)) := by
  simpa only [coshHalfMoment, mul_comm] using tendsto_integral_comp_logStep hf hc R hB hs
    (fun x => x) (fun u => Real.cosh (u / 2)) continuous_id rfl (by fun_prop)

theorem tendsto_logStep_sinhHalfMoment {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (R : ℝ) {B : ℕ} (hB : 1 ≤ B)
    (hs : ∀ u, u ≤ -R ∨ Real.log B - R ≤ u → f u = 0) :
    Tendsto (fun N : ℕ => sinhHalfMoment (logStep f R (N + 1))) atTop
      (𝓝 (sinhHalfMoment f)) := by
  simpa only [sinhHalfMoment, mul_comm] using tendsto_integral_comp_logStep hf hc R hB hs
    (fun x => x) (fun u => Real.sinh (u / 2)) continuous_id rfl (by fun_prop)

#print axioms tendsto_logStep_mass
#print axioms tendsto_logStep_coshHalfMoment
#print axioms tendsto_logStep_sinhHalfMoment

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
