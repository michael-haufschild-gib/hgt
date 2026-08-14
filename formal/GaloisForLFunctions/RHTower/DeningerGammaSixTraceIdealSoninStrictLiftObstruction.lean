import GaloisForLFunctions.RHTower.DeningerGammaSixSingularGreenStokesCoface
import GaloisForLFunctions.RHTower.RouteRCrossPrimeStokesCalkinPolarHandoff

/-!
# Gamma-six trace-ideal/Sonin strict-lift obstruction

The complete corrected Gamma-six source has a literal Wold coface in rectangular Schatten class
one.  Route R's fixed aperture-one Sonin receiver has a nonzero Calkin class at every nonneutral
horizontal grade.  This file compares those two already constructed objects.

Any linear source-to-physical comparison preserving the trace-class subobject sends the source
coface to a compact operator.  Its strict-square defect therefore differs from the fixed physical
receiver only by a compact operator.  The defect has exactly the receiver's essential norm and
retains the explicit reflected Stokes-curvature lower bound.  Consequently an exact comparison
on this coface exists precisely at neutral grade.

This is a no-go for trace-class-invariant relative-cyclic or determinant-style repairs.  It does
not construct the remaining divisor-selective singular comparison and does not assert RH.
-/

open Complex

namespace RHTower

noncomputable section

/-- Rectangular operator space containing the complete Gamma-six shell source. -/
abbrev DeningerGammaSixRectangularSourceOperator :=
  EllTwo →L[ℂ] lp (fun _ : ℕ => DeningerGammaSixTensorSourceL2) 2

/-- Fixed physical operator space of the Sonin receiver. -/
abbrev DeningerGammaSixSoninPhysicalOperator :=
  ArchimedeanWeightedL2 →L[ℂ] ArchimedeanWeightedL2

/-- Literal complete-source Wold coface `W₆(T₆) - (1/6)T₆`. -/
def deningerGammaSixCompleteWoldCoface :
    DeningerGammaSixRectangularSourceOperator :=
  deningerGammaSixWoldCompression deningerGammaSixFullSourceTensorOperator -
    (1 / 6 : ℂ) • deningerGammaSixFullSourceTensorOperator

/-- The complete-source Wold coface belongs to the ordinary rectangular trace class. -/
theorem deningerGammaSixCompleteWoldCoface_traceClass :
    MemRectSchattenClass 1 deningerGammaSixCompleteWoldCoface := by
  exact deningerGammaSixFullSource_singularGreenStokesCoface

/-- Aperture-one fixed Sonin receiver carrying the ordered `(2,3)` Stokes curvature. -/
def deningerGammaSixFixedSoninPhysicalReceiver
    (a : ℝ) : DeningerGammaSixSoninPhysicalOperator :=
  routeRTwoThreeStokesSoninCommutator 1 a

/-- A linear comparison admissible for Route L's strict square must preserve the complete
trace-class source subobject at least up to compact physical operators.  No continuity,
positivity, cyclicity, or divisor premise is imposed. -/
structure DeningerGammaSixTraceIdealSoninComparison where
  toLinearMap :
    DeningerGammaSixRectangularSourceOperator →ₗ[ℂ]
      DeningerGammaSixSoninPhysicalOperator
  map_traceClass_isCompact :
    ∀ S : DeningerGammaSixRectangularSourceOperator,
      MemRectSchattenClass 1 S → IsCompactOperator (toLinearMap S)

/-- Failure of a trace-ideal comparison to intertwine the complete Wold coface with the fixed
physical receiver. -/
def deningerGammaSixTraceIdealSoninStrictDefect
    (F : DeningerGammaSixTraceIdealSoninComparison) (a : ℝ) :
    DeningerGammaSixSoninPhysicalOperator :=
  deningerGammaSixFixedSoninPhysicalReceiver a -
    F.toLinearMap deningerGammaSixCompleteWoldCoface

/-- Essential norm is invariant under compact perturbation, specialized to the fixed physical
operator space used by the Route-L comparison. -/
theorem essentialNorm_sub_eq_of_isCompactOperator_routeL
    (T K : DeningerGammaSixSoninPhysicalOperator)
    (hK : IsCompactOperator K) :
    essentialNorm (T - K) = essentialNorm T := by
  apply le_antisymm
  · calc
      essentialNorm (T - K) = essentialNorm (T + -K) := by rw [sub_eq_add_neg]
      _ ≤ essentialNorm T + essentialNorm (-K) := essentialNorm_add_le T (-K)
      _ = essentialNorm T := by
        rw [essentialNorm_neg,
          essentialNorm_eq_zero_of_isCompactOperator hK, add_zero]
  · calc
      essentialNorm T = essentialNorm ((T - K) + K) := by
        congr 1
        abel
      _ ≤ essentialNorm (T - K) + essentialNorm K :=
        essentialNorm_add_le (T - K) K
      _ = essentialNorm (T - K) := by
        rw [essentialNorm_eq_zero_of_isCompactOperator hK, add_zero]

/-- Every trace-ideal comparison leaves the complete physical Calkin class unchanged. -/
theorem deningerGammaSixTraceIdealSoninStrictDefect_essentialNorm_eq
    (F : DeningerGammaSixTraceIdealSoninComparison) (a : ℝ) :
    essentialNorm (deningerGammaSixTraceIdealSoninStrictDefect F a) =
      essentialNorm (deningerGammaSixFixedSoninPhysicalReceiver a) := by
  apply essentialNorm_sub_eq_of_isCompactOperator_routeL
  exact F.map_traceClass_isCompact deningerGammaSixCompleteWoldCoface
    deningerGammaSixCompleteWoldCoface_traceClass

/-- Quantitative obstruction: every admissible strict-square defect retains the exact normalized
reflection-odd Stokes-curvature lower bound. -/
theorem deningerGammaSixTraceIdealSoninStrictDefect_calkinLower
    (F : DeningerGammaSixTraceIdealSoninComparison) (a : ℝ) :
    |routeRCrossPrimeStokesOddCurvature 2 3 a| / Real.sqrt 6 ≤
      essentialNorm (deningerGammaSixTraceIdealSoninStrictDefect F a) := by
  rw [deningerGammaSixTraceIdealSoninStrictDefect_essentialNorm_eq]
  exact abs_routeRTwoThreeStokesOddCurvature_div_sqrt_six_le_essentialNorm
    (by norm_num) a

/-- At neutral grade the two physical curvature orientations coincide and the receiver is
literally zero. -/
@[simp] theorem deningerGammaSixFixedSoninPhysicalReceiver_zero :
    deningerGammaSixFixedSoninPhysicalReceiver 0 = 0 := by
  rw [deningerGammaSixFixedSoninPhysicalReceiver,
    routeRTwoThreeStokesSoninCommutator_eq_neg_orientationGram]
  have hconst : ∀ i j : Fin 2,
      routeRTwoThreeStokesCurvaturePacket 0 i =
        routeRTwoThreeStokesCurvaturePacket 0 j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [routeRTwoThreeStokesCurvaturePacket]
  have hmatrix :
      finiteEulerOrientationMatrix (routeRTwoThreeStokesCurvaturePacket 0) = 0 :=
    (finiteEulerOrientationMatrix_eq_zero_iff _).2 hconst
  rw [finiteArchimedeanEulerOrientationGram, hmatrix]
  simp [finiteArchimedeanPrimeEulerGramCombination]

/-- Existence of a trace-ideal-preserving comparison exact on the complete Gamma-six Wold
coface. -/
def DeningerGammaSixTraceIdealSoninStrictLiftExists (a : ℝ) : Prop :=
  ∃ F : DeningerGammaSixTraceIdealSoninComparison,
    deningerGammaSixTraceIdealSoninStrictDefect F a = 0

/-- **Exact strict-lift classification.**  A trace-ideal-preserving comparison can close the
complete Gamma-six/Sonin coface square exactly only at neutral horizontal grade; at neutral grade
the zero comparison supplies the converse. -/
theorem deningerGammaSixTraceIdealSoninStrictLiftExists_iff (a : ℝ) :
    DeningerGammaSixTraceIdealSoninStrictLiftExists a ↔ a = 0 := by
  constructor
  · rintro ⟨F, hF⟩
    have hcompactImage :
        IsCompactOperator
          (F.toLinearMap deningerGammaSixCompleteWoldCoface) :=
      F.map_traceClass_isCompact deningerGammaSixCompleteWoldCoface
        deningerGammaSixCompleteWoldCoface_traceClass
    have hreceiver :
        deningerGammaSixFixedSoninPhysicalReceiver a =
          F.toLinearMap deningerGammaSixCompleteWoldCoface :=
      sub_eq_zero.mp hF
    have hcompactReceiver :
        IsCompactOperator (deningerGammaSixFixedSoninPhysicalReceiver a) := by
      rw [hreceiver]
      exact hcompactImage
    exact (routeRTwoThreeStokesSoninCommutator_isCompactOperator_iff
      (A := 1) (by norm_num) a).1 hcompactReceiver
  · rintro rfl
    let Fzero : DeningerGammaSixTraceIdealSoninComparison :=
      { toLinearMap := 0
        map_traceClass_isCompact := by
          intro S hS
          change IsCompactOperator
            (0 : ArchimedeanWeightedL2 → ArchimedeanWeightedL2)
          exact isCompactOperator_zero }
    refine ⟨Fzero, ?_⟩
    change deningerGammaSixFixedSoninPhysicalReceiver 0 -
      (0 : DeningerGammaSixSoninPhysicalOperator) = 0
    rw [deningerGammaSixFixedSoninPhysicalReceiver_zero]
    simp

/-- **Route-L trace-ideal/Sonin obstruction.**  The Calkin defect is exactly invariant under every
trace-class-preserving source comparison and quantitatively retains the physical reflected
curvature. -/
theorem DAC_DENINGER_GAMMA_SIX_TRACE_IDEAL_SONIN_STRICT_LIFT_OBSTRUCTION
    (F : DeningerGammaSixTraceIdealSoninComparison) (a : ℝ) :
    essentialNorm (deningerGammaSixTraceIdealSoninStrictDefect F a) =
        essentialNorm (deningerGammaSixFixedSoninPhysicalReceiver a) ∧
      |routeRCrossPrimeStokesOddCurvature 2 3 a| / Real.sqrt 6 ≤
        essentialNorm (deningerGammaSixTraceIdealSoninStrictDefect F a) := by
  exact ⟨deningerGammaSixTraceIdealSoninStrictDefect_essentialNorm_eq F a,
    deningerGammaSixTraceIdealSoninStrictDefect_calkinLower F a⟩

end

end RHTower
