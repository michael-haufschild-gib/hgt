import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistenceAIntervalGibbsRange

/-!
# Unique intermediate energy maximum on the phase interval

The two strict monotonicity intervals identify the unique maximizer,
including endpoint exclusion. The interval membership is part of the
unconditional characterization, not an additional hypothesis.
-/
noncomputable section
open Real Set
namespace GaloisForLFunctions.HTGeometry
open CPV

theorem egbCoexistenceAReducedLogGibbs_interval_maximizer_iff (τ θ u : ℝ) :
    (u ∈ Icc (log (thermalRatio τ)) 0 ∧ egbCoexistenceAReducedLogGibbs τ θ u =
      egbCoexistenceAReducedLogGibbs τ θ (log (egbCoexistenceAMiddleRadius τ θ))) ↔
      u = log (egbCoexistenceAMiddleRadius τ θ) := by
  have hb := egbCoexistenceAMiddleRadius_log_bounds τ θ
  constructor
  · rintro ⟨hu, he⟩
    by_contra hn
    rcases lt_or_gt_of_ne hn with hlo | hhi
    · have h := egbCoexistenceAReducedLogGibbs_lower_middle_strictMono τ θ
        ⟨hu.1, hlo.le⟩ ⟨hb.1.le, le_rfl⟩ hlo
      rw [he] at h
      exact lt_irrefl _ h
    · have h := egbCoexistenceAReducedLogGibbs_upper_middle_strictAnti τ θ
        ⟨le_rfl, hb.2.le⟩ ⟨hhi.le, hu.2⟩ hhi
      rw [he] at h
      exact lt_irrefl _ h
  · intro he
    rw [he]
    exact ⟨⟨hb.1.le, hb.2.le⟩, rfl⟩

end GaloisForLFunctions.HTGeometry
