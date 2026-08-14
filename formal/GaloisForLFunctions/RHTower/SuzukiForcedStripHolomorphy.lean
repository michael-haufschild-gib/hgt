import GaloisForLFunctions.RHTower.SuzukiForcedStripParticular
import GaloisForLFunctions.HTGeometry.SegmentParameterHolomorphy

/-!
# The forced Gamma particular solution is holomorphic through the frequency origin

After branch cancellation the particular solution is `p(z) = z·Q(z)Φ(z)` with

`Φ(z) = ∫₀¹ s^{1/2}Q(zs)^{-1}b(zs)ds`,

and both factors on the right are single-valued.  The transport `Q` and its inverse are holomorphic
wherever the branch `E` is holomorphic and nonvanishing, and `Φ` is holomorphic by differentiation
under the integral sign on any open set star-shaped about the origin.  Hence `p` extends
holomorphically through the frequency origin — the point at which the homogeneous solutions have
their regular singularity — and vanishes there.
-/

open Complex Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

section Weight

theorem continuousOn_cpowHalf :
    ContinuousOn (fun s : ℝ => ((s : ℂ) ^ ((1 : ℂ) / 2))) (Icc (0 : ℝ) 1) := by
  have heq : EqOn (fun s : ℝ => ((s : ℂ) ^ ((1 : ℂ) / 2)))
      (fun s : ℝ => ((s ^ ((1 : ℝ) / 2) : ℝ) : ℂ)) (Icc (0 : ℝ) 1) := by
    intro s hs
    show ((s : ℂ) ^ ((1 : ℂ) / 2)) = ((s ^ ((1 : ℝ) / 2) : ℝ) : ℂ)
    rw [show ((1 : ℂ) / 2) = (((1 : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow hs.1]
  refine ContinuousOn.congr ?_ heq
  exact Complex.continuous_ofReal.comp_continuousOn
    (Real.continuous_rpow_const (by norm_num)).continuousOn

theorem norm_cpowHalf_le_one : ∀ s ∈ Icc (0 : ℝ) 1, ‖((s : ℂ) ^ ((1 : ℂ) / 2))‖ ≤ 1 := by
  intro s hs
  rw [show ((1 : ℂ) / 2) = (((1 : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_cpow hs.1, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hs.1 _)]
  calc s ^ ((1 : ℝ) / 2) ≤ (1 : ℝ) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow hs.1 hs.2 (by norm_num)
    _ = 1 := Real.one_rpow _

end Weight

section Transport

variable {E : ℂ → ℂ} {b : ℂ → X}

/-- The inverse transport applied to a holomorphic vector field is holomorphic where the branch is
holomorphic and nonvanishing. -/
theorem differentiableAt_stripTransportInv_apply (T : X →L[ℂ] X) {z : ℂ}
    (hE : DifferentiableAt ℂ E z) (hEz : E z ≠ 0) (hb : DifferentiableAt ℂ b z) :
    DifferentiableAt ℂ (fun w : ℂ => stripTransportInv E T w (b w)) z := by
  have hscalar : DifferentiableAt ℂ
      (fun w : ℂ =>
        (Complex.exp (Complex.I * (Real.eulerMascheroniConstant : ℂ) * w) * E w)⁻¹) z := by
    refine DifferentiableAt.inv (((differentiableAt_id.const_mul _).cexp).mul hE) ?_
    exact mul_ne_zero (Complex.exp_ne_zero _) hEz
  have hopexp : DifferentiableAt ℂ
      (fun w : ℂ => NormedSpace.exp (((Complex.I / 2) * w) • T)) z := by
    have hbase := hasDerivAt_exp_smul_const (𝕂 := ℂ) T ((Complex.I / 2) * z)
    have hlin : HasDerivAt (fun w : ℂ => (Complex.I / 2) * w) (Complex.I / 2) z := by
      simpa using (hasDerivAt_id z).const_mul (Complex.I / 2)
    exact (HasDerivAt.scomp z hbase hlin).differentiableAt
  have hvec : DifferentiableAt ℂ
      (fun w : ℂ => NormedSpace.exp (((Complex.I / 2) * w) • T) (b w)) z :=
    hopexp.clm_apply hb
  have hfun : (fun w : ℂ => stripTransportInv E T w (b w))
      = fun w : ℂ =>
        (Complex.exp (Complex.I * (Real.eulerMascheroniConstant : ℂ) * w) * E w)⁻¹
          • (NormedSpace.exp (((Complex.I / 2) * w) • T) (b w)) := rfl
  rw [hfun]
  exact hscalar.smul hvec

/-- The transport applied to a holomorphic vector field is holomorphic where the branch is. -/
theorem differentiableAt_stripTransport_applyFun (T : X →L[ℂ] X) {z : ℂ}
    (hE : DifferentiableAt ℂ E z) (hb : DifferentiableAt ℂ b z) :
    DifferentiableAt ℂ (fun w : ℂ => stripTransport E T w (b w)) z := by
  have hscalar : DifferentiableAt ℂ
      (fun w : ℂ => Complex.exp (Complex.I * (Real.eulerMascheroniConstant : ℂ) * w) * E w) z :=
    ((differentiableAt_id.const_mul _).cexp).mul hE
  have hopexp : DifferentiableAt ℂ
      (fun w : ℂ => NormedSpace.exp ((-(Complex.I / 2) * w) • T)) z := by
    have hbase := hasDerivAt_exp_smul_const (𝕂 := ℂ) T (-(Complex.I / 2) * z)
    have hlin : HasDerivAt (fun w : ℂ => -(Complex.I / 2) * w) (-(Complex.I / 2)) z := by
      simpa using (hasDerivAt_id z).const_mul (-(Complex.I / 2))
    exact (HasDerivAt.scomp z hbase hlin).differentiableAt
  have hvec : DifferentiableAt ℂ
      (fun w : ℂ => NormedSpace.exp ((-(Complex.I / 2) * w) • T) (b w)) z :=
    hopexp.clm_apply hb
  have hfun : (fun w : ℂ => stripTransport E T w (b w))
      = fun w : ℂ => (Complex.exp (Complex.I * (Real.eulerMascheroniConstant : ℂ) * w) * E w)
        • (NormedSpace.exp ((-(Complex.I / 2) * w) • T) (b w)) :=
    funext fun w => stripTransport_apply E T w (b w)
  rw [hfun]
  exact hscalar.smul hvec

end Transport

section Holomorphy

variable {E : ℂ → ℂ} {b : ℂ → X} {T : X →L[ℂ] X}

/-- The branch cancellation identity holds at the frequency origin too: both sides vanish. -/
theorem forcedParticular_eq_total (E : ℂ → ℂ) (T : X →L[ℂ] X) (b : ℂ → X) (z : ℂ) :
    forcedParticular E T b z = z • stripTransport E T z (forcedParticularKernel E T b z) := by
  rcases eq_or_ne z 0 with rfl | hz
  · have hzero : ((0 : ℂ) ^ (-(1 : ℂ) / 2)) = 0 := Complex.zero_cpow (by norm_num)
    rw [forcedParticular, stripPropagator, hzero, zero_smul,
      zero_apply, zero_smul]
  · exact forcedParticular_eq E T b hz

/-- The branch-free kernel is holomorphic on every star-shaped open set of holomorphy. -/
theorem differentiableAt_forcedParticularKernel {U : Set ℂ} (hU : IsOpen U)
    (hstar : ∀ z ∈ U, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → z * (s : ℂ) ∈ U)
    (T : X →L[ℂ] X) (hE : DifferentiableOn ℂ E U) (hEne : ∀ z ∈ U, E z ≠ 0)
    (hb : DifferentiableOn ℂ b U) {z₀ : ℂ} (hz₀ : z₀ ∈ U) :
    DifferentiableAt ℂ (forcedParticularKernel E T b) z₀ := by
  have hG : DifferentiableOn ℂ (fun u : ℂ => stripTransportInv E T u (b u)) U := by
    intro u hu
    exact (differentiableAt_stripTransportInv_apply T
      (hE.differentiableAt (hU.mem_nhds hu)) (hEne u hu)
      (hb.differentiableAt (hU.mem_nhds hu))).differentiableWithinAt
  exact differentiableAt_integral_unitSegment hU hstar hG continuousOn_cpowHalf
    norm_cpowHalf_le_one hz₀

/-- **Theorem 1, holomorphy through the frequency origin.**  The particular solution extends
holomorphically across `z = 0`: after branch cancellation it is `z` times a transport of a
holomorphic kernel. -/
theorem differentiableOn_forcedParticular {U : Set ℂ} (hU : IsOpen U)
    (hstar : ∀ z ∈ U, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → z * (s : ℂ) ∈ U)
    (T : X →L[ℂ] X) (hE : DifferentiableOn ℂ E U) (hEne : ∀ z ∈ U, E z ≠ 0)
    (hb : DifferentiableOn ℂ b U) :
    DifferentiableOn ℂ (forcedParticular E T b) U := by
  have hfun : forcedParticular E T b
      = fun z : ℂ => z • stripTransport E T z (forcedParticularKernel E T b z) :=
    funext fun z => forcedParticular_eq_total E T b z
  rw [hfun]
  intro z hz
  have hker : DifferentiableAt ℂ (forcedParticularKernel E T b) z :=
    differentiableAt_forcedParticularKernel hU hstar T hE hEne hb hz
  have htr : DifferentiableAt ℂ
      (fun w : ℂ => stripTransport E T w (forcedParticularKernel E T b w)) z :=
    differentiableAt_stripTransport_applyFun T (hE.differentiableAt (hU.mem_nhds hz)) hker
  exact (differentiableAt_id.smul htr).differentiableWithinAt

/-- The unit strip is star-shaped about the frequency origin. -/
theorem imStrip_star {z : ℂ} (hz : z ∈ imStrip (-1) 1) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    z * (s : ℂ) ∈ imStrip (-1) 1 := by
  have him : (z * (s : ℂ)).im = z.im * s := by simp
  refine ⟨?_, ?_⟩
  · rw [him]
    nlinarith [hz.1, hz.2, hs.1, hs.2]
  · rw [him]
    nlinarith [hz.1, hz.2, hs.1, hs.2]

/-- **The particular solution is holomorphic on the whole unit strip, origin included.** -/
theorem differentiableOn_forcedParticular_imStrip (T : X →L[ℂ] X)
    (hE : DifferentiableOn ℂ E (imStrip (-1) 1)) (hEne : ∀ z ∈ imStrip (-1) 1, E z ≠ 0)
    (hb : DifferentiableOn ℂ b (imStrip (-1) 1)) :
    DifferentiableOn ℂ (forcedParticular E T b) (imStrip (-1) 1) :=
  differentiableOn_forcedParticular (isOpen_imStrip (-1) 1)
    (fun _ hz _ hs => imStrip_star hz hs) T hE hEne hb

end Holomorphy

end GaloisForLFunctions.RHTower
