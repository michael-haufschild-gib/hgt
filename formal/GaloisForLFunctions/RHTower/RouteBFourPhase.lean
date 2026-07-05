/-
The four-phase Fubini identity: the 4D sublevel measure of a four-phase
circle sum is the circle integral of the 3D sublevel measures at the
moving center `w + De^{iη}` (product-measure slice identity).
-/
import Mathlib
import GaloisForLFunctions.RHTower.RouteBBlockSplit

namespace RHTower
namespace Sublevel

open MeasureTheory

theorem four_phase_fubini (A B C D w : ℂ) (r : ℝ) :
    (volume.prod (volume.prod (volume.prod volume)))
      ((Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
          (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
            (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
              Set.Icc (0 : ℝ) (2 * Real.pi)))) ∩
        {q : ℝ × ℝ × ℝ × ℝ | ‖w + D * Complex.exp ((q.1 : ℂ) * Complex.I)
            + C * Complex.exp ((q.2.1 : ℂ) * Complex.I)
            + B * Complex.exp ((q.2.2.1 : ℂ) * Complex.I)
            + A * Complex.exp ((q.2.2.2 : ℂ) * Complex.I)‖ ≤ r})
      = ∫⁻ η in Set.Icc (0 : ℝ) (2 * Real.pi),
          (volume.prod (volume.prod volume))
            ((Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
                (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
                  Set.Icc (0 : ℝ) (2 * Real.pi))) ∩
              {p : ℝ × ℝ × ℝ | ‖w + D * Complex.exp ((η : ℂ) * Complex.I)
                  + C * Complex.exp ((p.1 : ℂ) * Complex.I)
                  + B * Complex.exp ((p.2.1 : ℂ) * Complex.I)
                  + A * Complex.exp ((p.2.2 : ℂ) * Complex.I)‖ ≤ r}) := by
  classical
  have hcont4 : Continuous fun q : ℝ × ℝ × ℝ × ℝ =>
      ‖w + D * Complex.exp ((q.1 : ℂ) * Complex.I)
        + C * Complex.exp ((q.2.1 : ℂ) * Complex.I)
        + B * Complex.exp ((q.2.2.1 : ℂ) * Complex.I)
        + A * Complex.exp ((q.2.2.2 : ℂ) * Complex.I)‖ := by
    refine Continuous.norm ?_
    refine Continuous.add (Continuous.add (Continuous.add
      (Continuous.add continuous_const ?_) ?_) ?_) ?_
    · exact continuous_const.mul (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_fst).mul
          continuous_const))
    · exact continuous_const.mul (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp
          (continuous_fst.comp continuous_snd)).mul continuous_const))
    · exact continuous_const.mul (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp (continuous_fst.comp
          (continuous_snd.comp continuous_snd))).mul continuous_const))
    · exact continuous_const.mul (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp (continuous_snd.comp
          (continuous_snd.comp continuous_snd))).mul continuous_const))
  have hSm : MeasurableSet
      ((Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
          (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
            (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
              Set.Icc (0 : ℝ) (2 * Real.pi)))) ∩
        {q : ℝ × ℝ × ℝ × ℝ | ‖w + D * Complex.exp ((q.1 : ℂ) * Complex.I)
            + C * Complex.exp ((q.2.1 : ℂ) * Complex.I)
            + B * Complex.exp ((q.2.2.1 : ℂ) * Complex.I)
            + A * Complex.exp ((q.2.2.2 : ℂ) * Complex.I)‖ ≤ r}) := by
    apply IsClosed.measurableSet
    exact (isClosed_Icc.prod (isClosed_Icc.prod
      (isClosed_Icc.prod isClosed_Icc))).inter
      (isClosed_le hcont4 continuous_const)
  rw [Measure.prod_apply hSm, ← lintegral_indicator measurableSet_Icc]
  congr 1
  funext η
  by_cases hη : η ∈ Set.Icc (0 : ℝ) (2 * Real.pi)
  · rw [Set.indicator_of_mem hη]
    congr 1
    ext p
    constructor
    · rintro ⟨⟨_, hp⟩, hnorm⟩
      exact ⟨hp, hnorm⟩
    · rintro ⟨hp, hnorm⟩
      exact ⟨⟨hη, hp⟩, hnorm⟩
  · rw [Set.indicator_of_notMem hη]
    have hempty : Prod.mk η ⁻¹'
        ((Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
            (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
              (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
                Set.Icc (0 : ℝ) (2 * Real.pi)))) ∩
          {q : ℝ × ℝ × ℝ × ℝ | ‖w + D * Complex.exp ((q.1 : ℂ)
              * Complex.I)
              + C * Complex.exp ((q.2.1 : ℂ) * Complex.I)
              + B * Complex.exp ((q.2.2.1 : ℂ) * Complex.I)
              + A * Complex.exp ((q.2.2.2 : ℂ) * Complex.I)‖ ≤ r}) = ∅ := by
      ext p
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨hη', _⟩, _⟩
      exact hη hη'
    rw [hempty, measure_empty]

end Sublevel
end RHTower
