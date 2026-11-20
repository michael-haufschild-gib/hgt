import GaloisForLFunctions.goldbach.LiLiu.Boundary.ArithmeticOperator

/-! # Strip Hardy traces and the columns of the residual operator

The squared trace norm is the sum of the two squared line norms. Vertical means
are uniformly bounded in the strip and approach the boundary values in L².
The Hilbert space uses the closure of these traces in the boundary norm.
-/

namespace GaloisForLFunctions.Goldbach.LiLiu
open _root_.Complex MeasureTheory Filter Set
open scoped Topology
noncomputable section

def IsHardyTrace (a b : ℝ) (u : Lp ℂ 2 (boundaryMeasure a b)) : Prop :=
  ∃ F g : ℂ → ℂ, DifferentiableOn ℂ F {s | s.re ∈ Ioo a b} ∧ Measurable g ∧
    (u : ℂ → ℂ) =ᵐ[boundaryMeasure a b] g ∧
    (∀ x ∈ Ioo a b, MemLp (fun t => F (mellinLine x t)) 2 volume) ∧
    (∃ C : ℝ, ∀ x ∈ Ioo a b, (∫ t : ℝ, ‖F (mellinLine x t)‖^2) ≤ C) ∧
    ∀ c ∈ ({a,b} : Set ℝ), Tendsto (fun x => ∫ t : ℝ, ‖F (mellinLine x t) - g (mellinLine c t)‖^2)
      (𝓝[Ioo a b] c) (𝓝 0)

def hardySpace (a b : ℝ) : Submodule ℂ (Lp ℂ 2 (boundaryMeasure a b)) :=
  (Submodule.span ℂ {u | IsHardyTrace a b u}).topologicalClosure

instance (a b : ℝ) : CompleteSpace (hardySpace a b) := by
  let K : Submodule ℂ (Lp ℂ 2 (boundaryMeasure a b)) := Submodule.span ℂ {u | IsHardyTrace a b u}
  exact @IsClosed.completeSpace_coe (Lp ℂ 2 (boundaryMeasure a b)) _ _
    (K.topologicalClosure : Set (Lp ℂ 2 (boundaryMeasure a b))) K.isClosed_topologicalClosure

theorem mem_hardySpace_of_trace {a b : ℝ} {u : Lp ℂ 2 (boundaryMeasure a b)}
    (hu : IsHardyTrace a b u) : u ∈ hardySpace a b :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span hu)

/-- A common L² majorant gives both the uniform vertical means and the
strong boundary traces by dominated convergence. -/
theorem exists_trace_of_majorant {a b : ℝ} {F : ℂ → ℂ} (hc : Continuous F)
    (hd : DifferentiableOn ℂ F {s | s.re ∈ Ioo a b}) {g : ℝ → ℝ}
    (hi : Integrable (fun t => g t ^ 2)) (hb : ∀ x t : ℝ, ‖F (mellinLine x t)‖ ≤ g t) :
    ∃ u : Lp ℂ 2 (boundaryMeasure a b), u ∈ hardySpace a b ∧ (u : ℂ → ℂ) =ᵐ[boundaryMeasure a b] F := by
  have hC (x : ℝ) := hc.comp (mellinLine_continuous x)
  have hline (x : ℝ) : Integrable (fun t : ℝ => ‖F (mellinLine x t)‖^2) := by
    apply hi.mono' ((hC x).norm.pow 2).aestronglyMeasurable
    exact Eventually.of_forall fun t => by
      change ‖‖F (mellinLine x t)‖^2‖ ≤ g t^2
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb x t) 2
  have hF : MemLp F 2 (boundaryMeasure a b) :=
    (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
      ((integrable_boundaryMeasure_iff (hc.norm.pow 2).measurable _ _).mpr ⟨hline _,hline _⟩)
  refine ⟨hF.toLp F,mem_hardySpace_of_trace ⟨F,F,hd,hc.measurable,hF.coeFn_toLp,?_,?_,?_⟩,hF.coeFn_toLp⟩
  · exact fun x _ => (memLp_two_iff_integrable_sq_norm (hC x).aestronglyMeasurable).mpr (hline x)
  · exact ⟨∫ t, g t ^ 2, fun x _ => integral_mono (hline x) hi
      (fun t => pow_le_pow_left₀ (norm_nonneg _) (hb x t) 2)⟩
  · intro c _
    have hdom (x t : ℝ) : ‖‖F (mellinLine x t)-F (mellinLine c t)‖^2‖ ≤ 4 * g t ^ 2 := by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have H := (norm_sub_le _ _).trans (add_le_add (hb x t) (hb c t))
      calc
        _ ≤ (g t+g t)^2 := pow_le_pow_left₀ (norm_nonneg _) H 2
        _ = _ := by ring
    have hcont : ContinuousAt (fun x => ∫ t : ℝ, ‖F (mellinLine x t)-F (mellinLine c t)‖^2) c := by
      apply continuousAt_of_dominated (bound := fun t => 4*g t^2)
      · exact Eventually.of_forall fun x => (((hC x).sub (hC c)).norm.pow 2).aestronglyMeasurable
      · exact Eventually.of_forall fun x => Eventually.of_forall fun t => hdom x t
      · exact hi.const_mul 4
      · have hv (t : ℝ) : Continuous (fun x : ℝ => F (mellinLine x t)) :=
          hc.comp (by unfold mellinLine; fun_prop)
        exact Eventually.of_forall fun t => (((hv t).sub continuous_const).norm.pow 2).continuousAt
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds

/-- Each arithmetic column gives an actual Hardy trace. -/
theorem arithmetic_column_trace {n : ℕ} (hN : 4 ≤ n+1) (h : modulusGRH (n+1))
    {a : ℝ} (ha : 0 < a) (hab : a ≤ 1/8) (z : ℂ) :
    ∃ u : Lp ℂ 2 (boundaryMeasure a (1/8)), u ∈ hardySpace a (1/8) ∧
      (u : ℂ → ℂ) =ᵐ[boundaryMeasure a (1/8)] fun s => extendedKernel (n+1) a s z := by
  obtain ⟨B,hB,hb⟩ := boundaryKernel_strip_decay hN h ha
  have hzc := clippedPoint_re hab z
  let C := B*edgeDecay z.im
  apply exists_trace_of_majorant (a := a) (b := 1/8) (F := fun s : ℂ => extendedKernel (n+1) a s z)
    (g := fun t => C*edgeDecay t)
  · have hv : Continuous (fun s : ℂ => (s,z)) := continuous_id.prodMk continuous_const
    exact (extendedKernel_continuous h ha hab).comp hv
  · intro s hs
    let S := {u : ℂ | u.re ∈ Ioo a (1/8)}
    have ho : IsOpen S := isOpen_Ioo.preimage continuous_re
    have he : (fun u => extendedKernel (n+1) a u z) =ᶠ[𝓝 s]
        fun u => boundaryKernel (n+1) u (clippedPoint a (1/8) z) := by
      filter_upwards [ho.mem_nhds hs] with u hu
      rw [extendedKernel,clippedPoint_eq ⟨hu.1.le,hu.2.le⟩]
    exact ((boundaryKernel_column_differentiableAt h
      ⟨ha.trans hs.1,hs.2.trans (by norm_num)⟩ ⟨ha.trans_le hzc.1,hzc.2.trans_lt (by norm_num)⟩
      ).congr_of_eventuallyEq he).differentiableWithinAt
  · simpa only [mul_pow] using edgeDecay_sq_line_integrable.const_mul (C^2)
  · intro x t
    have H := hb (clippedPoint a (1/8) (mellinLine x t)) (clippedPoint a (1/8) z)
      (clippedPoint_re hab _) hzc
    simpa only [extendedKernel,clippedPoint_im,mellinLine_im,C,edgeDecay,mul_right_comm] using H

#print axioms arithmetic_column_trace
end
end GaloisForLFunctions.Goldbach.LiLiu
