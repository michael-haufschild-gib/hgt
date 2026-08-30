import GaloisForLFunctions.HTGeometry.MaximumTermCentralIndex
import GaloisForLFunctions.HTGeometry.FactorialModulusProfile

/-!
# Coefficient magnitudes determine the whole Newton geometry

The maximum term, the set of indices attaining it, the central (active) index, and therefore the
logarithmic Newton envelope, the transition radii and the plateau widths, are defined from the
coefficient magnitudes alone.  Two entire functions with the same Taylor moduli have identical
Newton data — even when one is differentially algebraic and the other hypertranscendental.
-/

open PowerSeries

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {a b : ℕ → ℂ}

theorem maxTerm_congr (h : ∀ n, ‖a n‖ = ‖b n‖) (r : ℝ) : maxTerm a r = maxTerm b r := by
  rw [maxTerm, maxTerm]
  congr 1
  funext n
  rw [h n]

theorem maxTermAttained_congr (h : ∀ n, ‖a n‖ = ‖b n‖) (r : ℝ) :
    maxTermAttained a r = maxTermAttained b r := by
  ext n
  rw [maxTermAttained, maxTermAttained]
  simp only [Set.mem_setOf_eq, h n, maxTerm_congr h r]

theorem centralIndex_congr (h : ∀ n, ‖a n‖ = ‖b n‖) (r : ℝ) :
    centralIndex a r = centralIndex b r := by
  rw [centralIndex, centralIndex, maxTermAttained_congr h r]

/-- The logarithmic Newton envelope: the logarithm of the maximum term in logarithmic radius. -/
def logNewtonEnvelope (a : ℕ → ℂ) (t : ℝ) : ℝ := Real.log (maxTerm a (Real.exp t))

theorem logNewtonEnvelope_congr (h : ∀ n, ‖a n‖ = ‖b n‖) (t : ℝ) :
    logNewtonEnvelope a t = logNewtonEnvelope b t := by
  rw [logNewtonEnvelope, logNewtonEnvelope, maxTerm_congr h]

/-- **Equal moduli give identical Newton data.** -/
theorem newton_data_congr (h : ∀ n, ‖a n‖ = ‖b n‖) :
    (∀ r, maxTerm a r = maxTerm b r) ∧ (∀ r, maxTermAttained a r = maxTermAttained b r)
      ∧ (∀ r, centralIndex a r = centralIndex b r)
      ∧ (∀ t, logNewtonEnvelope a t = logNewtonEnvelope b t) :=
  ⟨maxTerm_congr h, maxTermAttained_congr h, centralIndex_congr h, logNewtonEnvelope_congr h⟩

/-- **The factorial profile: identical Newton geometry, opposite differential nature.** -/
theorem factorialProfile_newton_data_agree :
    (∀ r, maxTerm (fun n => PowerSeries.coeff n (GaloisForLFunctions.taylorPS Complex.exp)) r
        = maxTerm (fun n => PowerSeries.coeff n
          (GaloisForLFunctions.taylorPS factorialProfileHT)) r)
      ∧ (∀ r, maxTermAttained
          (fun n => PowerSeries.coeff n (GaloisForLFunctions.taylorPS Complex.exp)) r
        = maxTermAttained (fun n => PowerSeries.coeff n
          (GaloisForLFunctions.taylorPS factorialProfileHT)) r)
      ∧ (∀ r, centralIndex
          (fun n => PowerSeries.coeff n (GaloisForLFunctions.taylorPS Complex.exp)) r
        = centralIndex (fun n => PowerSeries.coeff n
          (GaloisForLFunctions.taylorPS factorialProfileHT)) r)
      ∧ (∀ t, logNewtonEnvelope
          (fun n => PowerSeries.coeff n (GaloisForLFunctions.taylorPS Complex.exp)) t
        = logNewtonEnvelope (fun n => PowerSeries.coeff n
          (GaloisForLFunctions.taylorPS factorialProfileHT)) t) := by
  refine newton_data_congr fun n => ?_
  rw [norm_taylorPS_cexp, norm_taylorPS_factorialProfileHT]

end

end GaloisForLFunctions.HTGeometry
