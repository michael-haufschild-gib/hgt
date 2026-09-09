import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistenceAGlobalMinima

/-!
# The full energy range between the two coexistence phases

The established monotonicity on either side of the intermediate root
places every interior energy between the common phase minimum and the
intermediate energy maximum.
-/
noncomputable section
open Real Set
namespace GaloisForLFunctions.HTGeometry
open CPV

theorem egbCoexistenceAReducedLogGibbs_interval_mapsTo (τ θ : ℝ) :
    MapsTo (egbCoexistenceAReducedLogGibbs τ θ) (Icc (log (thermalRatio τ)) 0)
      (Icc (egbCoexistenceAReducedLogGibbs τ θ 0)
        (egbCoexistenceAReducedLogGibbs τ θ (log (egbCoexistenceAMiddleRadius τ θ)))) := by
  intro u hu
  have hb := egbCoexistenceAMiddleRadius_log_bounds τ θ
  constructor
  · exact egbCoexistenceAReducedLogGibbs_global_minimum τ θ u
  · by_cases hm : u ≤ log (egbCoexistenceAMiddleRadius τ θ)
    · exact (egbCoexistenceAReducedLogGibbs_lower_middle_strictMono τ θ).monotoneOn
        ⟨hu.1, hm⟩ ⟨hb.1.le, le_rfl⟩ hm
    · have hm' : log (egbCoexistenceAMiddleRadius τ θ) ≤ u := (lt_of_not_ge hm).le
      exact (egbCoexistenceAReducedLogGibbs_upper_middle_strictAnti τ θ).antitoneOn
        ⟨le_rfl, hb.2.le⟩ ⟨hm', hu.2⟩ hm'

end GaloisForLFunctions.HTGeometry
