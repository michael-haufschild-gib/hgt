import GaloisForLFunctions.HTGeometry.PaperFourierCircleConvergence
import GaloisForLFunctions.RHTower.CCMArchimedeanCircleTraceCocycle

/-! # One Fourier exceptional set for the native circle operator orbit

All finite words in countably many actual multipliers, Hardy projections,
quantized differentials and crossblocks share one Fourier convergence set.
The set also works for every finite complex linear combination of their outputs.
-/

namespace RHTower
noncomputable section
open MeasureTheory Filter Topology
open GaloisForLFunctions.HTGeometry
open scoped BigOperators

/-- Five literal native operators at each supplied trace symbol. -/
def paperCircleTraceOperator (b : ℕ → CCMCircleTraceSymbol) (p : ℕ × Fin 5) :
    CCMCircleL2 →L[ℂ] CCMCircleL2 :=
  match p.2.val with
  | 0 => ccmCircleHardyProjection
  | 1 => ccmCircleMultiplier (b p.1).toCCMCircleBoundedSymbol
  | 2 => ccmCircleQuantizedDifferential (b p.1)
  | 3 => ccmCircleUpperCrossBlock (b p.1)
  | _ => ccmCircleLowerCrossBlock (b p.1)

/-- A finite ordered composition in the actual native operator algebra. -/
def paperCircleTraceWord (b : ℕ → CCMCircleTraceSymbol) :
    List (ℕ × Fin 5) → CCMCircleL2 →L[ℂ] CCMCircleL2
  | [] => 1
  | p::w => paperCircleTraceOperator b p * paperCircleTraceWord b w

/-- The exceptional set is chosen before the word, input, finite support, and coefficients. -/
theorem paperCircleTraceOrbit_common_span_convergence (b : ℕ → CCMCircleTraceSymbol)
    (f : ℕ → CCMCircleL2) :
    ∃ E : Set (AddCircle (1 : ℝ)), MeasurableSet E ∧ AddCircle.haarAddCircle E = 0 ∧
      ∀ x ∉ E, ∀ (S : Finset (List (ℕ × Fin 5) × ℕ))
        (c : (List (ℕ × Fin 5) × ℕ) → ℂ),
        Tendsto (fun N => paperCircleFourierPartialSum 1
          (fun y => ∑ p ∈ S, c p * (paperCircleTraceWord b p.1 (f p.2)) y) N x)
          atTop (𝓝 (∑ p ∈ S, c p * (paperCircleTraceWord b p.1 (f p.2)) x)) :=
  paperCircleLp_common_span_convergence 1
    (fun p : List (ℕ × Fin 5) × ℕ => paperCircleTraceWord b p.1 (f p.2))

end
end RHTower
