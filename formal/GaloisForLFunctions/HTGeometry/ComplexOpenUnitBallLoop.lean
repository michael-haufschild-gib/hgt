import GaloisForLFunctions.HTGeometry.TorusChartComplexPoints
import Mathlib.Analysis.Convex.Contractible

/-!
# Nullhomotopy of small subtractive loops in `ℂˣ`

The open complex unit ball is contractible.  Subtracting one of its loops from a unit-norm
center never meets zero, and therefore produces a nullhomotopic loop in `ℂˣ`.
-/

namespace GaloisForLFunctions.HTGeometry

open Path

noncomputable section

abbrev ComplexOpenUnitBall := {z : ℂ // z ∈ Metric.ball (0 : ℂ) 1}

def complexOpenUnitBallSubtractionMap (c : ℂ) (hc : ‖c‖ = 1) :
    C(ComplexOpenUnitBall, Units ℂ) := by
  let f : ComplexOpenUnitBall → {ζ : ℂ // ζ ≠ 0} := fun z ↦
    ⟨c - z.1, by
      intro hzero
      have heq : c = z.1 := sub_eq_zero.mp hzero
      have hzdist : dist z.1 0 < 1 := z.2
      have hz : ‖z.1‖ < 1 := by
        simpa [dist_zero_right] using hzdist
      rw [← heq, hc] at hz
      exact (lt_self_iff_false 1).mp hz⟩
  exact ⟨fun z ↦ (unitsHomeomorphNeZero (G₀ := ℂ)).symm (f z),
    (unitsHomeomorphNeZero (G₀ := ℂ)).symm.continuous.comp (by
      apply Continuous.subtype_mk
      fun_prop)⟩

theorem complexOpenUnitBallSubtractionLoop_mk_eq_refl
    (c : ℂ) (hc : ‖c‖ = 1) {z₀ : ComplexOpenUnitBall}
    (p : Path z₀ z₀) :
    Path.Homotopic.Quotient.mk
        (p.map (complexOpenUnitBallSubtractionMap c hc).continuous) =
      Path.Homotopic.Quotient.mk
        (Path.refl (complexOpenUnitBallSubtractionMap c hc z₀)) := by
  letI : ContractibleSpace ComplexOpenUnitBall :=
    (convex_ball (0 : ℂ) (1 : ℝ)).contractibleSpace
      ⟨0, by simp [Metric.mem_ball]⟩
  letI : SimplyConnectedSpace ComplexOpenUnitBall := inferInstance
  have hp : Path.Homotopic.Quotient.mk p =
      Path.Homotopic.Quotient.mk (Path.refl z₀) := Subsingleton.elim _ _
  have hm := congrArg
    (fun q : Path.Homotopic.Quotient z₀ z₀ ↦
      q.map (complexOpenUnitBallSubtractionMap c hc)) hp
  exact hm

end
end GaloisForLFunctions.HTGeometry
