import GaloisForLFunctions.HTGeometry.SmallGrowthMeromorphicField
import GaloisForLFunctions.HTGeometry.EntireTranslation
import GaloisForLFunctions.HTGeometry.MeromorphicLaurentTranslation

/-!
# Translation of global meromorphic fraction presentations

This module transports an explicit entire numerator/denominator presentation through translation
of the complex variable.  Its literal quotient is exactly the translated meromorphic function, and
its divisor order is transported to the translated point.  No growth estimate is used here.
-/

open Filter Set Topology Metric ValueDistribution Asymptotics

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace EntireFractionPresentation

/-- Translate an entire-fraction presentation in its complex variable. -/
def translate {x : EntireField ℂ} (c : ℂ) (p : EntireFractionPresentation x) :
    EntireFractionPresentation (fieldTranslateEquiv c x) where
  numerator := entireTranslate c p.numerator
  denominator := entireTranslate c p.denominator
  denominator_ne_zero := by
    intro h
    apply p.denominator_ne_zero
    apply Subtype.ext
    funext z
    have hz := congrArg
      (fun a : entireSubring ℂ => (a : ℂ → ℂ) (z - c)) h
    change (p.denominator : ℂ → ℂ) (z - c + c) = (0 : ℂ) at hz
    simpa using hz
  eq_div := by
    calc
      fieldTranslateEquiv c x =
          fieldTranslateEquiv c
            (algebraMap (entireSubring ℂ) (EntireField ℂ) p.numerator /
              algebraMap (entireSubring ℂ) (EntireField ℂ) p.denominator) :=
        congrArg (fieldTranslateEquiv c) p.eq_div
      _ = algebraMap (entireSubring ℂ) (EntireField ℂ)
              (entireTranslate c p.numerator) /
            algebraMap (entireSubring ℂ) (EntireField ℂ)
              (entireTranslate c p.denominator) := by
        rw [map_div₀, fieldTranslateEquiv_algebraMap,
          fieldTranslateEquiv_algebraMap]

@[simp]
theorem function_translate {x : EntireField ℂ} (c : ℂ)
    (p : EntireFractionPresentation x) :
    (p.translate c).function = fun z => p.function (z + c) := by
  funext z
  rfl

/-- Translation transports the meromorphic divisor order to the translated point. -/
theorem meromorphicOrderAt_function_translate {x : EntireField ℂ} (c z : ℂ)
    (p : EntireFractionPresentation x) :
    meromorphicOrderAt (p.translate c).function z =
      meromorphicOrderAt p.function (z + c) := by
  rw [function_translate]
  exact meromorphicOrderAt_comp_add p.function z c

/-- The global divisor of a translated fraction is the translated global divisor. -/
theorem divisor_function_translate {x : EntireField ℂ} (c z : ℂ)
    (p : EntireFractionPresentation x) :
    MeromorphicOn.divisor (p.translate c).function Set.univ z =
      MeromorphicOn.divisor p.function Set.univ (z + c) := by
  rw [MeromorphicOn.divisor_apply (fun w _ => (p.translate c).meromorphic w)
      (Set.mem_univ z),
    MeromorphicOn.divisor_apply (fun w _ => p.meromorphic w)
      (Set.mem_univ (z + c)),
    meromorphicOrderAt_function_translate]

end EntireFractionPresentation

/-- Proximity of a translated function is the same boundary average around the translated
center. -/
theorem proximity_comp_add_top (f : ℂ → ℂ) (c : ℂ) (r : ℝ) :
    proximity (fun z => f (z + c)) ⊤ r =
      Real.circleAverage (fun z => Real.posLog ‖f z‖) c r := by
  simp [proximity, Real.circleAverage, circleMap, add_comm]

end

end GaloisForLFunctions.HTGeometry
