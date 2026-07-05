/-
The three-phase small-ball law with dyadic-logarithmic constant: the
composition of the three-phase Fubini reduction with the caustic-averaged
annulus bound.  `annulus_fubini` is the product-measure slice identity;
`three_phase_sublevel_r2log` is the endpoint: the 3D sublevel measure of a
three-phase circle sum is at most `(2πr/‖A‖) · (J·C₁ + C₂ + C₂ + C₃)` with
explicit constants, `J` any dyadic depth covering the caustic gap.
-/
import Mathlib
import GaloisForLFunctions.RHTower.RouteBCausticCapstone

namespace RHTower
namespace Sublevel

open MeasureTheory

/-- The annulus measure as a third-phase integral of radial-band
measures (product-measure slice identity). -/
theorem annulus_fubini (B C c : ℂ) (ρ r : ℝ) :
    (volume.prod volume)
      ((Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) ∩
        {p : ℝ × ℝ | |‖c + C * Complex.exp ((p.1 : ℂ) * Complex.I)
            + B * Complex.exp ((p.2 : ℂ) * Complex.I)‖ - ρ| ≤ r})
      = ∫⁻ η in Set.Icc (0 : ℝ) (2 * Real.pi),
          volume {φ : ℝ | φ ∈ Set.Icc 0 (2 * Real.pi) ∧
            |‖c + C * Complex.exp ((η : ℂ) * Complex.I)
              + B * Complex.exp ((φ : ℂ) * Complex.I)‖ - ρ| ≤ r} := by
  classical
  have hcontA : Continuous fun p : ℝ × ℝ =>
      |‖c + C * Complex.exp ((p.1 : ℂ) * Complex.I)
        + B * Complex.exp ((p.2 : ℂ) * Complex.I)‖ - ρ| := by
    apply Continuous.abs
    apply Continuous.sub _ continuous_const
    apply Continuous.norm
    refine Continuous.add (Continuous.add continuous_const ?_) ?_
    · exact continuous_const.mul (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_fst).mul
          continuous_const))
    · exact continuous_const.mul (Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp continuous_snd).mul
          continuous_const))
  have hAnnm : MeasurableSet
      ((Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) ∩
        {p : ℝ × ℝ | |‖c + C * Complex.exp ((p.1 : ℂ) * Complex.I)
            + B * Complex.exp ((p.2 : ℂ) * Complex.I)‖ - ρ| ≤ r}) := by
    apply IsClosed.measurableSet
    exact (isClosed_Icc.prod isClosed_Icc).inter
      (isClosed_le hcontA continuous_const)
  rw [Measure.prod_apply hAnnm, ← lintegral_indicator measurableSet_Icc]
  congr 1
  funext η
  by_cases hη : η ∈ Set.Icc (0 : ℝ) (2 * Real.pi)
  · rw [Set.indicator_of_mem hη]
    congr 1
    ext φ
    constructor
    · rintro ⟨⟨_, hφI⟩, hband⟩
      exact ⟨hφI, hband⟩
    · rintro ⟨hφI, hband⟩
      exact ⟨⟨hη, hφI⟩, hband⟩
  · rw [Set.indicator_of_notMem hη]
    have hempty : Prod.mk η ⁻¹'
        ((Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) ∩
          {p : ℝ × ℝ | |‖c + C * Complex.exp ((p.1 : ℂ) * Complex.I)
              + B * Complex.exp ((p.2 : ℂ) * Complex.I)‖ - ρ| ≤ r}) = ∅ := by
      ext φ
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨⟨hη', _⟩, _⟩
      exact hη hη'
    rw [hempty, measure_empty]

/-- **The three-phase small-ball law with dyadic depth `J`** (the caustic
ladder's top rung): the 3D sublevel measure of a three-phase circle sum is
at most the per-phase arc bound times `J·(shell) + 2·(core) + (mid)` with
explicit constants.  Taking `J` logarithmic in `1/r` (the least depth
satisfying the cover hypothesis at the minimal admissible `σ0 ~ r`) gives
the `r²·log(1/r)` law. -/
theorem three_phase_sublevel_r2log {A B C c : ℂ} {r σ0 : ℝ} {J : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) (hc : c ≠ 0)
    (hρB : ‖B‖ < ‖A‖) (hr0 : 0 < r) (hr2 : 2 * r ≤ ‖A‖ - ‖B‖)
    (hσ0 : 0 < σ0)
    (hσ0G : σ0 ≤ ((‖A‖ + ‖B‖) ^ 2 - (‖A‖ - ‖B‖) ^ 2) / 3)
    (hJ : ((‖A‖ + ‖B‖) ^ 2 - (‖A‖ - ‖B‖) ^ 2) / 3 < 2 ^ J * σ0)
    (hHσ0 : 2 * (r * (2 * ‖A‖ + r) / ((‖A‖ - ‖B‖) * ‖B‖))
        ≤ σ0 * causticKappa ‖A‖ ‖B‖) :
    (volume.prod (volume.prod volume))
      ((Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ
          (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi))) ∩
        {q : ℝ × ℝ × ℝ | ‖c + C * Complex.exp ((q.1 : ℂ) * Complex.I)
            + B * Complex.exp ((q.2.1 : ℂ) * Complex.I)
            + A * Complex.exp ((q.2.2 : ℂ) * Complex.I)‖ ≤ r})
      ≤ ENNReal.ofReal (2 * (Real.pi * r / ‖A‖))
        * (J • ENNReal.ofReal (8 * Real.pi ^ 2
              * (r * (2 * ‖A‖ + r) / ((‖A‖ - ‖B‖) / 2 * ‖B‖))
              * (Real.sqrt (2 / (causticKappa ‖A‖ ‖B‖ * (‖c‖ * ‖C‖)))
                + Real.sqrt 2))
          + ENNReal.ofReal ((2 * Real.pi
              * Real.sqrt (2 * (r * (2 * ‖A‖ + r)
                / ((‖A‖ - ‖B‖) / 2 * ‖B‖))))
              * (2 * Real.pi * Real.sqrt (2
                * ((σ0 + r * (2 * (‖A‖ + ‖B‖) + r))
                  / (2 * (‖c‖ * ‖C‖))))))
          + ENNReal.ofReal ((2 * Real.pi
              * Real.sqrt (2 * (r * (2 * ‖A‖ + r)
                / ((‖A‖ - ‖B‖) / 2 * ‖B‖))))
              * (2 * Real.pi * Real.sqrt (2
                * ((σ0 + r * (2 * (‖A‖ + ‖B‖) + r))
                  / (2 * (‖c‖ * ‖C‖))))))
          + ENNReal.ofReal (2 * Real.pi * (2 * Real.pi
              * (r * (2 * ‖A‖ + r) / ((‖A‖ - ‖B‖) / 2 * ‖B‖))
              / Real.sqrt (min (((‖A‖ + ‖B‖) ^ 2 - (‖A‖ - ‖B‖) ^ 2) / 3
                  * causticKappa ‖A‖ ‖B‖ / 2) (1 / 2))))) := by
  refine le_trans (three_phase_sublevel hA hr0.le) ?_
  refine mul_le_mul_right ?_ _
  refine le_trans (le_of_eq (annulus_fubini B C c ‖A‖ r)) ?_
  exact annulus_lintegral_le hB hC hc hρB hr0 hr2 hσ0 hσ0G hJ hHσ0

end Sublevel
end RHTower
