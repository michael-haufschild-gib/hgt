import GaloisForLFunctions.RHTower.Suzuki.SuzukiForcedStripGluing
import GaloisForLFunctions.RHTower.Suzuki.SuzukiForcedStripHolomorphy
import GaloisForLFunctions.HTGeometry.SegmentParameterPrimitive

/-!
# The segment and the horizontal-line representations of the forced solution agree

The particular solution is built from the contour integral of `H(w)^{-1}b(w)` along the segment from
the frequency origin, while the quantitative Hardy estimate is built from the same integral along a
horizontal line.  The two differ by the constant value at the base point of the line, because the
segment integral is a primitive:

`d/dz ∫_{[0,z]} H(w)^{-1}b(w) dw = H(z)^{-1}b(z)`.

The primitive property is the parameter fundamental theorem for the half-power weight: writing the
segment integral as `z^{3/2}Φ(z)` with `Φ(z) = ∫₀¹ s^{1/2}Q(zs)^{-1}b(zs)ds`, the product rule turns
its derivative into `z^{1/2}[(3/2)Φ(z) + zΦ'(z)]`, and the bracket is exactly `Q(z)^{-1}b(z)`.

Consequently the glued forced solution on an interior line is the variation-of-constants solution
rebased at the point `iσ`, so the Hardy estimate applies to it verbatim.
-/

open Complex Filter MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

variable {E : ℂ → ℂ} {b : ℂ → X} {T : X →L[ℂ] X}

/-- `(7)`: the contour integral of `H^{-1}b` along the segment from the frequency origin. -/
def forcedSegmentIntegral (E : ℂ → ℂ) (T : X →L[ℂ] X) (b : ℂ → X) (z : ℂ) : X :=
  z • ∫ s in (0 : ℝ)..1, stripPropagatorInv E T (z * (s : ℂ)) (b (z * (s : ℂ)))

omit [Nontrivial X] in
theorem forcedParticular_eq_propagator_apply (E : ℂ → ℂ) (T : X →L[ℂ] X) (b : ℂ → X) (z : ℂ) :
    forcedParticular E T b z = stripPropagator E T z (forcedSegmentIntegral E T b z) := rfl

omit [Nontrivial X] in
theorem forcedSegmentIntegral_eq_cpow_smul (E : ℂ → ℂ) (T : X →L[ℂ] X) (b : ℂ → X)
    {z : ℂ} (hz : z ≠ 0) :
    forcedSegmentIntegral E T b z = (z ^ ((3 : ℂ) / 2)) • forcedParticularKernel E T b z := by
  have hmul : z * z ^ ((1 : ℂ) / 2) = z ^ ((3 : ℂ) / 2) := by
    have h : z ^ ((1 : ℂ) + (1 : ℂ) / 2) = z ^ (1 : ℂ) * z ^ ((1 : ℂ) / 2) :=
      Complex.cpow_add _ _ hz
    rw [Complex.cpow_one] at h
    rw [← h]
    norm_num
  rw [forcedSegmentIntegral, integral_stripPropagatorInv_segment E T b hz, smul_smul, hmul]

section Primitive

/-- The strip is star-shaped about the frequency origin, as an interior-point statement. -/
private theorem strip_star_mem {w : ℂ} (hw : w ∈ imStrip (-1) 1) {s : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) : w * (s : ℂ) ∈ imStrip (-1) 1 := imStrip_star hw hs

omit [Nontrivial X] in
/-- **The segment integral is a primitive of `H^{-1}b` on the open strip.** -/
theorem hasDerivAt_forcedSegmentIntegral
    (hE : DifferentiableOn ℂ E (imStrip (-1) 1)) (hEne : ∀ w ∈ imStrip (-1) 1, E w ≠ 0)
    (hb : DifferentiableOn ℂ b (imStrip (-1) 1)) {z : ℂ} (hz : z ∈ imStrip 0 1) :
    HasDerivAt (forcedSegmentIntegral E T b) (stripPropagatorInv E T z (b z)) z := by
  have hzstrip : z ∈ imStrip (-1) 1 := ⟨by linarith [hz.1], hz.2⟩
  have hzim : 0 < z.im := hz.1
  have hzne : z ≠ 0 := by
    intro hcon
    rw [hcon] at hzim
    simp at hzim
  have hslit : z ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_gt hzim))
  -- the branch-free integrand
  set G : ℂ → X := fun w => stripTransportInv E T w (b w) with hGdef
  have hGdiff : DifferentiableOn ℂ G (imStrip (-1) 1) := by
    intro u hu
    exact (differentiableAt_stripTransportInv_apply T
      (hE.differentiableAt ((isOpen_imStrip (-1) 1).mem_nhds hu)) (hEne u hu)
      (hb.differentiableAt ((isOpen_imStrip (-1) 1).mem_nhds hu))).differentiableWithinAt
  -- the derivative of the branch-free kernel
  have hker := hasDerivAt_integral_unitSegment (isOpen_imStrip (-1) 1)
    (fun w hw s hs => strip_star_mem hw hs) hGdiff continuousOn_cpowHalf norm_cpowHalf_le_one
    hzstrip
  have hkerrw : (∫ s in (0 : ℝ)..1, (((s : ℂ) ^ ((1 : ℂ) / 2)) * (s : ℂ)) • deriv G (z * (s : ℂ)))
      = ∫ s in (0 : ℝ)..1, ((s : ℂ) ^ ((3 : ℂ) / 2)) • deriv G (z * (s : ℂ)) := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall ?_)
    intro s hs
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hs
    have hs0 : 0 < s := hs.1
    have hcast : ((s : ℂ) ^ ((1 : ℂ) / 2)) * (s : ℂ) = (s : ℂ) ^ ((3 : ℂ) / 2) := by
      have hsne : ((s : ℂ)) ≠ 0 := by simpa using hs0.ne'
      have h : (s : ℂ) ^ ((1 : ℂ) / 2 + (1 : ℂ))
          = (s : ℂ) ^ ((1 : ℂ) / 2) * (s : ℂ) ^ (1 : ℂ) := Complex.cpow_add _ _ hsne
      rw [Complex.cpow_one] at h
      rw [← h]
      norm_num
    rw [hcast]
  rw [hkerrw] at hker
  -- the derivative of the half power
  have hpow : HasDerivAt (fun w : ℂ => w ^ ((3 : ℂ) / 2))
      (((3 : ℂ) / 2) * z ^ ((1 : ℂ) / 2)) z := by
    have h := (hasDerivAt_id z).cpow_const (c := (3 : ℂ) / 2) hslit
    refine h.congr_deriv ?_
    norm_num
  -- the product rule
  have hprod := hpow.smul hker
  have hval : ((z ^ ((3 : ℂ) / 2)) •
        ∫ s in (0 : ℝ)..1, ((s : ℂ) ^ ((3 : ℂ) / 2)) • deriv G (z * (s : ℂ)))
      + (((3 : ℂ) / 2) * z ^ ((1 : ℂ) / 2)) • forcedParticularKernel E T b z
      = stripPropagatorInv E T z (b z) := by
    have hftc := segment_ftc_half (isOpen_imStrip (-1) 1)
      (fun w hw s hs => strip_star_mem hw hs) hGdiff hzstrip
    have hz32 : z ^ ((3 : ℂ) / 2) = z ^ ((1 : ℂ) / 2) * z := by
      have h : z ^ ((1 : ℂ) / 2 + (1 : ℂ)) = z ^ ((1 : ℂ) / 2) * z ^ (1 : ℂ) :=
        Complex.cpow_add _ _ hzne
      rw [Complex.cpow_one] at h
      rw [← h]
      norm_num
    have hGz : stripTransportInv E T z (b z) = G z := rfl
    rw [stripPropagatorInv_eq_cpow_smul E T z, smul_apply, hGz, ← hftc, hz32,
      forcedParticularKernel]
    rw [smul_add, smul_smul, smul_smul, add_comm,
      mul_comm ((3 : ℂ) / 2) (z ^ ((1 : ℂ) / 2))]
  -- transfer the derivative to the segment integral
  have heq : forcedSegmentIntegral E T b =ᶠ[nhds z]
      (fun w : ℂ => (w ^ ((3 : ℂ) / 2)) • forcedParticularKernel E T b w) := by
    have hopen : {w : ℂ | w ≠ 0} ∈ nhds z := by
      refine IsOpen.mem_nhds ?_ hzne
      exact isOpen_compl_singleton
    filter_upwards [hopen] with w hw
    exact forcedSegmentIntegral_eq_cpow_smul E T b hw
  exact ((hprod.congr_deriv hval).congr_of_eventuallyEq heq)

end Primitive

section Bridge

omit [Nontrivial X] in
/-- The inverse propagator applied to the forcing is holomorphic on the open strip. -/
theorem differentiableAt_stripPropagatorInv_apply
    (hE : DifferentiableOn ℂ E (imStrip (-1) 1)) (hEne : ∀ w ∈ imStrip (-1) 1, E w ≠ 0)
    (hb : DifferentiableOn ℂ b (imStrip (-1) 1)) {w : ℂ} (hw : w ∈ imStrip 0 1) :
    DifferentiableAt ℂ (fun u : ℂ => stripPropagatorInv E T u (b u)) w := by
  have hwstrip : w ∈ imStrip (-1) 1 := ⟨by linarith [hw.1], hw.2⟩
  have hslit : w ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_gt hw.1))
  have hpow : DifferentiableAt ℂ (fun u : ℂ => u ^ ((1 : ℂ) / 2)) w :=
    differentiableAt_id.cpow_const hslit
  have hvec : DifferentiableAt ℂ (fun u : ℂ => stripTransportInv E T u (b u)) w :=
    differentiableAt_stripTransportInv_apply T
      (hE.differentiableAt ((isOpen_imStrip (-1) 1).mem_nhds hwstrip)) (hEne w hwstrip)
      (hb.differentiableAt ((isOpen_imStrip (-1) 1).mem_nhds hwstrip))
  have hfun : (fun u : ℂ => stripPropagatorInv E T u (b u))
      = fun u : ℂ => (u ^ ((1 : ℂ) / 2)) • stripTransportInv E T u (b u) := by
    funext u
    rw [stripPropagatorInv_eq_cpow_smul E T u, smul_apply]
  rw [hfun]
  exact hpow.smul hvec

omit [Nontrivial X] in
/-- Along a horizontal interior line the segment integral is the line integral rebased at `iσ`. -/
theorem forcedSegmentIntegral_line
    (hE : DifferentiableOn ℂ E (imStrip (-1) 1)) (hEne : ∀ w ∈ imStrip (-1) 1, E w ≠ 0)
    (hb : DifferentiableOn ℂ b (imStrip (-1) 1)) {σ : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1) (x : ℝ) :
    forcedSegmentIntegral E T b ((x : ℂ) + (σ : ℂ) * Complex.I)
      = forcedSegmentIntegral E T b ((0 : ℂ) + (σ : ℂ) * Complex.I)
        + ∫ t in (0 : ℝ)..x,
            stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I)
              (b ((t : ℂ) + (σ : ℂ) * Complex.I)) := by
  set F : ℝ → X := fun t => forcedSegmentIntegral E T b ((t : ℂ) + (σ : ℂ) * Complex.I) with hFdef
  set F' : ℝ → X := fun t =>
    stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I)
      (b ((t : ℂ) + (σ : ℂ) * Complex.I)) with hF'def
  have hmem : ∀ t : ℝ, ((t : ℂ) + (σ : ℂ) * Complex.I) ∈ imStrip 0 1 := by
    intro t
    constructor <;> simp [hσ.1, hσ.2]
  have hline : ∀ t : ℝ, HasDerivAt (fun u : ℝ => ((u : ℂ) + (σ : ℂ) * Complex.I)) 1 t := by
    intro t
    simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).add_const ((σ : ℂ) * Complex.I)
  have hderiv : ∀ t : ℝ, HasDerivAt F (F' t) t := by
    intro t
    have hseg := hasDerivAt_forcedSegmentIntegral (T := T) hE hEne hb (hmem t)
    have hc := HasDerivAt.scomp t hseg (hline t)
    simp only [Function.comp_def, one_smul] at hc
    exact hc
  have hcont : Continuous F' := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hlinec : ContinuousAt (fun u : ℝ => ((u : ℂ) + (σ : ℂ) * Complex.I)) t := by fun_prop
    have hcomp : ContinuousAt ((fun u : ℂ => stripPropagatorInv E T u (b u))
        ∘ (fun u : ℝ => ((u : ℂ) + (σ : ℂ) * Complex.I))) t :=
      ContinuousAt.comp
        (differentiableAt_stripPropagatorInv_apply hE hEne hb (hmem t)).continuousAt hlinec
    exact hcomp
  have hint : IntervalIntegrable F' volume 0 x := hcont.intervalIntegrable _ _
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) hint
  have hgoal : F x = F 0 + ∫ t in (0 : ℝ)..x, F' t := by
    rw [hFTC]
    abel
  simpa [hFdef, hF'def] using hgoal

omit [Nontrivial X] in
/-- **The bridge.**  On an interior line the glued forced solution is the variation-of-constants
solution rebased at the base point of the line, so the quantitative Hardy estimate applies to it. -/
theorem stripSolution_add_forcedParticular_eq_forcedStripLine
    (hE : DifferentiableOn ℂ E (imStrip (-1) 1)) (hEne : ∀ w ∈ imStrip (-1) 1, E w ≠ 0)
    (hb : DifferentiableOn ℂ b (imStrip (-1) 1)) (cp : X) {σ : ℝ} (hσ : σ ∈ Ioo (0 : ℝ) 1)
    (x : ℝ) :
    stripSolution E T cp ((x : ℂ) + (σ : ℂ) * Complex.I)
        + forcedParticular E T b ((x : ℂ) + (σ : ℂ) * Complex.I)
      = forcedStripLine E T (cp + forcedSegmentIntegral E T b ((0 : ℂ) + (σ : ℂ) * Complex.I))
          (fun t : ℝ => b ((t : ℂ) + (σ : ℂ) * Complex.I)) σ x := by
  rw [forcedStripLine, forcedParticular_eq_propagator_apply,
    forcedSegmentIntegral_line hE hEne hb hσ x, ← stripPropagator_apply E T _ cp, ← map_add]
  congr 1
  rw [add_assoc]

end Bridge

end GaloisForLFunctions.RHTower
