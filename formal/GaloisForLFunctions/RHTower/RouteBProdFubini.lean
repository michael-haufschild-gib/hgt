/-
Lower-arity companions of the four-phase Fubini identity: peeling one
circle coordinate off a product-measure sublevel set at a fixed center,
down to the one-phase base.  Chaining these expresses the 4D product
sublevel measure as a four-fold iterated integral over the angle interval.
-/
import Mathlib
import GaloisForLFunctions.RHTower.RouteBFourPhase

namespace RHTower
namespace Sublevel

open MeasureTheory

/-- Peel the outer coordinate of a three-phase product sublevel set:
the 3D measure equals the circle integral of the 2D measures at the
moving center `c + C e^{iη}`. -/
theorem three_phase_fubini (A B C c : ℂ) (r : ℝ) :
    (volume.prod (volume.prod volume))
      ((Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
          (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
            Set.Icc (0 : ℝ) (2 * Real.pi))) ∩
        {p : ℝ × ℝ × ℝ | ‖c + C * Complex.exp ((p.1 : ℂ) * Complex.I)
            + B * Complex.exp ((p.2.1 : ℂ) * Complex.I)
            + A * Complex.exp ((p.2.2 : ℂ) * Complex.I)‖ ≤ r})
      = ∫⁻ η in Set.Icc (0 : ℝ) (2 * Real.pi),
          (volume.prod volume)
            ((Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
                Set.Icc (0 : ℝ) (2 * Real.pi)) ∩
              {p : ℝ × ℝ | ‖(c + C * Complex.exp ((η : ℂ) * Complex.I))
                  + B * Complex.exp ((p.1 : ℂ) * Complex.I)
                  + A * Complex.exp ((p.2 : ℂ) * Complex.I)‖ ≤ r}) := by
  classical
  have hcont3 : Continuous fun p : ℝ × ℝ × ℝ =>
      ‖c + C * Complex.exp ((p.1 : ℂ) * Complex.I)
        + B * Complex.exp ((p.2.1 : ℂ) * Complex.I)
        + A * Complex.exp ((p.2.2 : ℂ) * Complex.I)‖ := by
    refine Continuous.norm ?_
    refine Continuous.add (Continuous.add (Continuous.add
      continuous_const ?_) ?_) ?_
    · exact continuous_const.mul (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_fst).mul
          continuous_const))
    · exact continuous_const.mul (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp
          (continuous_fst.comp continuous_snd)).mul continuous_const))
    · exact continuous_const.mul (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp (continuous_snd.comp
          continuous_snd)).mul continuous_const))
  have hSm : MeasurableSet
      ((Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
          (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
            Set.Icc (0 : ℝ) (2 * Real.pi))) ∩
        {p : ℝ × ℝ × ℝ | ‖c + C * Complex.exp ((p.1 : ℂ) * Complex.I)
            + B * Complex.exp ((p.2.1 : ℂ) * Complex.I)
            + A * Complex.exp ((p.2.2 : ℂ) * Complex.I)‖ ≤ r}) := by
    apply IsClosed.measurableSet
    exact (isClosed_Icc.prod (isClosed_Icc.prod isClosed_Icc)).inter
      (isClosed_le hcont3 continuous_const)
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
              Set.Icc (0 : ℝ) (2 * Real.pi))) ∩
          {p : ℝ × ℝ × ℝ | ‖c + C * Complex.exp ((p.1 : ℂ) * Complex.I)
              + B * Complex.exp ((p.2.1 : ℂ) * Complex.I)
              + A * Complex.exp ((p.2.2 : ℂ) * Complex.I)‖ ≤ r}) = ∅ := by
      ext p
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨hη', _⟩, _⟩
      exact hη hη'
    rw [hempty, measure_empty]

/-- Peel the outer coordinate of a two-phase product sublevel set. -/
theorem two_phase_fubini (A B c : ℂ) (r : ℝ) :
    (volume.prod volume)
      ((Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) ∩
        {p : ℝ × ℝ | ‖c + B * Complex.exp ((p.1 : ℂ) * Complex.I)
            + A * Complex.exp ((p.2 : ℂ) * Complex.I)‖ ≤ r})
      = ∫⁻ η in Set.Icc (0 : ℝ) (2 * Real.pi),
          volume
            {θ : ℝ | θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ∧
              ‖(c + B * Complex.exp ((η : ℂ) * Complex.I))
                + A * Complex.exp ((θ : ℂ) * Complex.I)‖ ≤ r} := by
  classical
  have hcont2 : Continuous fun p : ℝ × ℝ =>
      ‖c + B * Complex.exp ((p.1 : ℂ) * Complex.I)
        + A * Complex.exp ((p.2 : ℂ) * Complex.I)‖ := by
    refine Continuous.norm ?_
    refine Continuous.add (Continuous.add continuous_const ?_) ?_
    · exact continuous_const.mul (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_fst).mul
          continuous_const))
    · exact continuous_const.mul (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_snd).mul
          continuous_const))
  have hSm : MeasurableSet
      ((Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) ∩
        {p : ℝ × ℝ | ‖c + B * Complex.exp ((p.1 : ℂ) * Complex.I)
            + A * Complex.exp ((p.2 : ℂ) * Complex.I)‖ ≤ r}) := by
    apply IsClosed.measurableSet
    exact (isClosed_Icc.prod isClosed_Icc).inter
      (isClosed_le hcont2 continuous_const)
  rw [Measure.prod_apply hSm, ← lintegral_indicator measurableSet_Icc]
  congr 1
  funext η
  by_cases hη : η ∈ Set.Icc (0 : ℝ) (2 * Real.pi)
  · rw [Set.indicator_of_mem hη]
    congr 1
    ext θ
    constructor
    · rintro ⟨⟨_, hθ⟩, hnorm⟩
      exact ⟨hθ, hnorm⟩
    · rintro ⟨hθ, hnorm⟩
      exact ⟨⟨hη, hθ⟩, hnorm⟩
  · rw [Set.indicator_of_notMem hη]
    have hempty : Prod.mk η ⁻¹'
        ((Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) ∩
          {p : ℝ × ℝ | ‖c + B * Complex.exp ((p.1 : ℂ) * Complex.I)
              + A * Complex.exp ((p.2 : ℂ) * Complex.I)‖ ≤ r}) = ∅ := by
      ext θ
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨hη', _⟩, _⟩
      exact hη hη'
    rw [hempty, measure_empty]

/-- The one-phase base: the arc measure is the integral of the sublevel
indicator over the angle interval. -/
theorem one_phase_fubini (A c : ℂ) (r : ℝ) :
    volume
      {θ : ℝ | θ ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ∧
        ‖c + A * Complex.exp ((θ : ℂ) * Complex.I)‖ ≤ r}
      = ∫⁻ θ in Set.Icc (0 : ℝ) (2 * Real.pi),
          {θ' : ℝ | ‖c + A * Complex.exp ((θ' : ℂ) * Complex.I)‖ ≤ r}.indicator
            (fun _ => (1 : ENNReal)) θ := by
  classical
  have hcont : Continuous fun θ : ℝ =>
      ‖c + A * Complex.exp ((θ : ℂ) * Complex.I)‖ :=
    (continuous_const.add (continuous_const.mul (Complex.continuous_exp.comp
      (Complex.continuous_ofReal.mul continuous_const)))).norm
  have hTm : MeasurableSet
      {θ' : ℝ | ‖c + A * Complex.exp ((θ' : ℂ) * Complex.I)‖ ≤ r} :=
    (isClosed_le hcont continuous_const).measurableSet
  rw [lintegral_indicator hTm, setLIntegral_one, Measure.restrict_apply hTm]
  congr 1
  ext θ
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  tauto

/-- The 4D product sublevel measure expands to a four-fold iterated
integral of the sublevel indicator over the angle interval. -/
theorem four_phase_prod_eq_nested (A B C D w : ℂ) (r : ℝ) :
    (volume.prod (volume.prod (volume.prod volume)))
      ((Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
          (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
            (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
              Set.Icc (0 : ℝ) (2 * Real.pi)))) ∩
        {q : ℝ × ℝ × ℝ × ℝ | ‖w + D * Complex.exp ((q.1 : ℂ) * Complex.I)
            + C * Complex.exp ((q.2.1 : ℂ) * Complex.I)
            + B * Complex.exp ((q.2.2.1 : ℂ) * Complex.I)
            + A * Complex.exp ((q.2.2.2 : ℂ) * Complex.I)‖ ≤ r})
      = ∫⁻ θD in Set.Icc (0 : ℝ) (2 * Real.pi),
          ∫⁻ θC in Set.Icc (0 : ℝ) (2 * Real.pi),
            ∫⁻ θB in Set.Icc (0 : ℝ) (2 * Real.pi),
              ∫⁻ θA in Set.Icc (0 : ℝ) (2 * Real.pi),
                {θ' : ℝ | ‖w + D * Complex.exp ((θD : ℂ) * Complex.I)
                    + C * Complex.exp ((θC : ℂ) * Complex.I)
                    + B * Complex.exp ((θB : ℂ) * Complex.I)
                    + A * Complex.exp ((θ' : ℂ) * Complex.I)‖ ≤ r}.indicator
                  (fun _ => (1 : ENNReal)) θA := by
  rw [four_phase_fubini]
  simp_rw [three_phase_fubini, two_phase_fubini, one_phase_fubini]

end Sublevel
end RHTower
