import GaloisForLFunctions.HTGeometry.FokasLenellsZeroScattering
import GaloisForLFunctions.HTGeometry.FokasLenellsSquareIntegrableData

/-!
# The singular time phase has a continuous actual jump

Exact vanishing of both reflection coefficients at zero removes the apparent
pointwise singularity of the time phase. The jump is jointly continuous in time,
position, and spectral coordinate for every explicitly normalized Schwartz
potential. A single L² envelope controls every jump-perturbation entry uniformly
in time and position. These are the inputs for strong continuity of the actual
Cauchy inverse and its holomorphic realization.
-/

open MeasureTheory Complex Matrix Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

/-- Multiplying by the oscillatory phase preserves continuity at zero because the actual reflections vanish there. -/
theorem regularJumpReflection_continuousAt_zero (q : SchwartzMap ℝ ℂ) (t x : ℝ) :
    ContinuousAt (fun p : ℝ × ℝ × ℝ => regularJumpReflection q p.1 p.2.1 p.2.2) (t,x,0) ∧
    ContinuousAt (fun p : ℝ × ℝ × ℝ => regularJumpReverseReflection q p.1 p.2.1 p.2.2) (t,x,0) := by
  have hz : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.2.2) (t,x,0) := by fun_prop
  constructor
  · change Tendsto _ (𝓝 (t,x,0)) (𝓝 (regularJumpReflection q t x 0))
    rw [(regularJumpReflection_zero q t x).1]
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hc := ((continuousAt_regularReflectionCoefficients_zero q).1.comp (f := fun p : ℝ × ℝ × ℝ => p.2.2) hz).norm
    change Tendsto (fun p : ℝ × ℝ × ℝ => ‖regularReflectionCoefficient q p.2.2‖)
      (𝓝 (t,x,0)) (𝓝 ‖regularReflectionCoefficient q 0‖) at hc
    rw [(regularReflectionCoefficients_zero q).1,norm_zero] at hc
    exact hc.congr (fun p => by simpa only [sub_zero] using (regularJumpReflection_norms q p.1 p.2.1 p.2.2).1.symm)
  · change Tendsto _ (𝓝 (t,x,0)) (𝓝 (regularJumpReverseReflection q t x 0))
    rw [(regularJumpReflection_zero q t x).2]
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hc := ((continuousAt_regularReflectionCoefficients_zero q).2.comp (f := fun p : ℝ × ℝ × ℝ => p.2.2) hz).norm
    change Tendsto (fun p : ℝ × ℝ × ℝ => ‖regularReverseReflectionCoefficient q p.2.2‖)
      (𝓝 (t,x,0)) (𝓝 ‖regularReverseReflectionCoefficient q 0‖) at hc
    rw [(regularReflectionCoefficients_zero q).2,norm_zero] at hc
    exact hc.congr (fun p => by simpa only [sub_zero] using (regularJumpReflection_norms q p.1 p.2.1 p.2.2).2.symm)

/-- The normalized actual jump symbols are jointly continuous, including the singular spectral origin. -/
theorem continuous_globalSmall_regularJump_parameters (q : SchwartzMap ℝ ℂ) :
    Continuous (fun p : ℝ × ℝ × ℝ => regularJumpReflection (globalSmallScatteringPotential q) p.1 p.2.1 p.2.2) ∧
    Continuous (fun p : ℝ × ℝ × ℝ => regularJumpReverseReflection (globalSmallScatteringPotential q) p.1 p.2.1 p.2.2) := by
  have hp : ∀ p : ℝ × ℝ × ℝ,
      ContinuousAt (fun v : ℝ × ℝ × ℝ => regularJumpReflection (globalSmallScatteringPotential q) v.1 v.2.1 v.2.2) p ∧
      ContinuousAt (fun v : ℝ × ℝ × ℝ => regularJumpReverseReflection (globalSmallScatteringPotential q) v.1 v.2.1 v.2.2) p := by
    rintro ⟨t,x,z⟩
    by_cases he : z = 0
    · subst z
      exact regularJumpReflection_continuousAt_zero _ t x
    · have ht : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.1) (t,x,z) := by fun_prop
      have hx : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.2.1) (t,x,z) := by fun_prop
      have hz : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.2.2) (t,x,z) := by fun_prop
      have hden : ContinuousAt (fun p : ℝ × ℝ × ℝ => 4*p.2.2) (t,x,z) := continuousAt_const.mul hz
      have harg : ContinuousAt (fun p : ℝ × ℝ × ℝ => p.2.2*p.2.1-p.1/(4*p.2.2)) (t,x,z) :=
        (hz.mul hx).sub (ht.div hden (mul_ne_zero (by norm_num) he))
      have hs (c : ℝ) : Continuous (fun y : ℝ => FDNLS.staggerPhase c y) := by
        unfold FDNLS.staggerPhase
        fun_prop
      have hr := continuous_globalSmall_regularReflection q
      exact ⟨((hs 2).continuousAt.comp harg).mul (hr.1.continuousAt.comp hz),
        ((hs (-2)).continuousAt.comp harg).mul (hr.2.continuousAt.comp hz)⟩
  exact ⟨continuous_iff_continuousAt.mpr (fun p => (hp p).1),
    continuous_iff_continuousAt.mpr (fun p => (hp p).2)⟩

theorem continuous_globalSmall_regularJumpMatrix_entry (q : SchwartzMap ℝ ℂ) (i j : Fin 2) :
    Continuous (fun p : ℝ × ℝ × ℝ => regularJump (globalSmallScatteringPotential q) p.1 p.2.1 p.2.2 i j) := by
  have hc := continuous_globalSmall_regularJump_parameters q
  fin_cases i <;> fin_cases j
  · exact continuous_const
  · exact hc.2
  · exact hc.1.neg
  · exact continuous_const.sub (hc.1.mul hc.2)

/-- The full actual jump matrix varies continuously in all three real parameters. -/
theorem continuous_globalSmall_regularJumpMatrix (q : SchwartzMap ℝ ℂ) :
    Continuous (fun p : ℝ × ℝ × ℝ => regularJump (globalSmallScatteringPotential q) p.1 p.2.1 p.2.2) :=
  continuous_pi fun i => continuous_pi fun j => continuous_globalSmall_regularJumpMatrix_entry q i j

/-- A common integrable envelope for every matrix entry and every time and position. -/
def regularJumpL2Envelope (q : SchwartzMap ℝ ℂ) (z : ℝ) : ℝ :=
  ‖regularReflectionCoefficient (globalSmallScatteringPotential q) z‖+
    ‖regularReverseReflectionCoefficient (globalSmallScatteringPotential q) z‖

theorem regularJumpL2Envelope_memLp (q : SchwartzMap ℝ ℂ) : MemLp (regularJumpL2Envelope q) 2 volume :=
  (globalSmall_regularReflection_memLp q).1.norm.add (globalSmall_regularReflection_memLp q).2.norm

/-- The envelope controls every entry of the actual perturbation uniformly over the whole space-time plane. -/
theorem regularJump_sub_one_envelope (q : SchwartzMap ℝ ℂ) (t x z : ℝ) (i j : Fin 2) :
    ‖(regularJump (globalSmallScatteringPotential q) t x z-(1 : Matrix (Fin 2) (Fin 2) ℂ)) i j‖ ≤
      regularJumpL2Envelope q z := by
  have hn := regularJumpReflection_norms (globalSmallScatteringPotential q) t x z
  have hb := (globalSmall_regularReflection_bounds q z).2
  fin_cases i <;> fin_cases j
  · change ‖(1:ℂ)-1‖ ≤ _
    rw [sub_self,norm_zero]
    exact add_nonneg (norm_nonneg (regularReflectionCoefficient (globalSmallScatteringPotential q) z))
      (norm_nonneg (regularReverseReflectionCoefficient (globalSmallScatteringPotential q) z))
  · change ‖regularJumpReverseReflection (globalSmallScatteringPotential q) t x z-0‖ ≤ _
    rw [sub_zero,hn.2]
    exact le_add_of_nonneg_left (norm_nonneg (regularReflectionCoefficient (globalSmallScatteringPotential q) z))
  · change ‖-regularJumpReflection (globalSmallScatteringPotential q) t x z-0‖ ≤ _
    rw [sub_zero,norm_neg,hn.1]
    exact le_add_of_nonneg_right (norm_nonneg (regularReverseReflectionCoefficient (globalSmallScatteringPotential q) z))
  · change ‖(1-regularJumpReflection (globalSmallScatteringPotential q) t x z*
      regularJumpReverseReflection (globalSmallScatteringPotential q) t x z)-1‖ ≤ _
    rw [sub_sub_cancel_left,norm_neg,norm_mul,hn.1,hn.2]
    have hprod := mul_le_mul_of_nonneg_left (show ‖regularReverseReflectionCoefficient (globalSmallScatteringPotential q) z‖ ≤ 1 by linarith)
      (norm_nonneg (regularReflectionCoefficient (globalSmallScatteringPotential q) z))
    unfold regularJumpL2Envelope
    nlinarith [norm_nonneg (regularReverseReflectionCoefficient (globalSmallScatteringPotential q) z)]

end
end GaloisForLFunctions.HTGeometry.FokasLenells
