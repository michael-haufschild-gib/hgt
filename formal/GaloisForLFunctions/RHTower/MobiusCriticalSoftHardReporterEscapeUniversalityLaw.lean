import GaloisForLFunctions.RHTower.MobiusCriticalFisherTangentCoefficients
import GaloisForLFunctions.RHTower.MobiusCriticalFisherCutoffLimits
import GaloisForLFunctions.RHTower.MobiusChannelCriticalMassEscape

/-!
# Möbius critical soft--hard reporter escape

The moving damped Fisher tangent has a positive soft critical profile, while the hard cutoff Ward
profile is asymptotically four times that soft profile at small positive aperture.  Fixed bounded
reporters of the critical shift channel vanish weakly.  Thus neither calibrated boundary statistic
can be tracked by a fixed reporter on the same punctured aperture neighborhood.
-/

open Complex Filter MeasureTheory
open scoped Topology

namespace RHTower

noncomputable section

/-- **Möbius soft--hard reporter-escape universality law.**  The hard/soft boundary ratio tends
`4`.  On a punctured neighborhood of zero aperture, every fixed continuous linear reporter fails
to track both the co-moving soft Fisher coefficient and one quarter of the positive hard cutoff
profile. -/
theorem mobiusCriticalSoftHardReporterEscapeUniversality :
    Tendsto
      (fun u : ℝ => squarefreeMobiusCriticalFisherCutoffWardLimit u /
        (2 * u / (1 + u) ^ 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 4) ∧
    ∀ (f : Lp ℂ 2 (volume : Measure ℝ))
        (ell : InfiniteMobiusShiftChannel →L[ℂ] ℂ),
      ∀ᶠ u : ℝ in nhdsWithin 0 (Set.Ioi 0),
        (¬ Tendsto
          (fun sigma : ℝ =>
            ell (mobiusCriticalShiftChannel sigma f) -
              infiniteMobiusCriticalFisherTangentDampedCoefficient sigma u)
          (nhdsWithin 1 (Set.Ioi 1)) (nhds 0)) ∧
        (¬ Tendsto
          (fun sigma : ℝ =>
            ell (mobiusCriticalShiftChannel sigma f) -
              ((squarefreeMobiusCriticalFisherCutoffWardLimit u / 4 : ℝ) : ℂ))
          (nhdsWithin 1 (Set.Ioi 1)) (nhds 0)) := by
  have hscale : Tendsto (fun u : ℝ => (1 + u) ^ 2)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
    have hu : Tendsto (fun u : ℝ => u)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      tendsto_id.mono_left inf_le_left
    have hone : Tendsto (fun _ : ℝ => (1 : ℝ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := tendsto_const_nhds
    simpa using ((hone.add hu).pow 2)
  have hratio :=
    tendsto_squarefreeMobiusCriticalFisherCutoffWardLimit_div_two_mul.mul hscale
  norm_num at hratio
  have hratio' : Tendsto
      (fun u : ℝ => squarefreeMobiusCriticalFisherCutoffWardLimit u /
        (2 * u / (1 + u) ^ 2))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 4) := by
    refine hratio.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu0 : u ≠ 0 := hu.ne'
    field_simp [hu0]
  refine ⟨hratio', ?_⟩
  intro f ell
  have hratioPos : ∀ᶠ u : ℝ in nhdsWithin 0 (Set.Ioi 0),
      0 < squarefreeMobiusCriticalFisherCutoffWardLimit u /
        (2 * u / (1 + u) ^ 2) :=
    hratio'.eventually (isOpen_Ioi.mem_nhds (by norm_num))
  filter_upwards [self_mem_nhdsWithin, hratioPos] with u hu hpositive
  have hu0 : 0 < u := hu
  have hsoftPos : 0 < 2 * u / (1 + u) ^ 2 := by
    exact div_pos (mul_pos (by norm_num) hu0)
      (sq_pos_of_pos (add_pos zero_lt_one hu0))
  have hhardPos : 0 < squarefreeMobiusCriticalFisherCutoffWardLimit u := by
    rcases (div_pos_iff.mp hpositive) with h | h
    · exact h.1
    · exact (not_lt_of_ge hsoftPos.le h.2).elim
  have hweak := mobiusCriticalShiftChannel_weakly_tendsto_zero f ell
  constructor
  · intro htrack
    have hmoving :=
      tendsto_infiniteMobiusCriticalFisherTangentDampedCoefficient hu.le
    have hlimit := hweak.sub hmoving
    have heq := tendsto_nhds_unique hlimit htrack
    have hne : ((2 * u / (1 + u) ^ 2 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr hsoftPos.ne'
    have heq' : -((2 * u / (1 + u) ^ 2 : ℝ) : ℂ) = 0 := by
      simpa using heq
    exact hne (neg_eq_zero.mp heq')
  · intro htrack
    have htarget :
        ((squarefreeMobiusCriticalFisherCutoffWardLimit u / 4 : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (div_ne_zero hhardPos.ne' (by norm_num))
    have hlimit := hweak.sub (tendsto_const_nhds : Tendsto
      (fun _ : ℝ =>
        ((squarefreeMobiusCriticalFisherCutoffWardLimit u / 4 : ℝ) : ℂ))
      (nhdsWithin 1 (Set.Ioi 1))
      (nhds ((squarefreeMobiusCriticalFisherCutoffWardLimit u / 4 : ℝ) : ℂ)))
    have heq := tendsto_nhds_unique hlimit htrack
    have heq' :
        -((squarefreeMobiusCriticalFisherCutoffWardLimit u / 4 : ℝ) : ℂ) = 0 := by
      simpa using heq
    exact htarget (neg_eq_zero.mp heq')

end

end RHTower
