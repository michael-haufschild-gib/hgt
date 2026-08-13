import GaloisForLFunctions.HTGeometry.TripticMultiplicativeSourceClass

/-!
# Reciprocity of the two orbital charges of a triptic source

The `σ`-side and `τ`-side orbital charges of a member of the multiplicative triptic class agree at
every base point: the divisor read off the two noncommensurable elliptic boundary quotients is one
integer-valued function, which is what makes the integral orbit divisor of the class canonical.

* `tripticOrbitCharge_reciprocity_source`.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The two orbital charges of a class member agree.**  The `σ`-orbital charge at any base point
equals the `τ`-orbital charge there, by triptic orbit-residue reciprocity applied to the
logarithmic derivative. -/
theorem tripticOrbitCharge_reciprocity_source {τ σ : ℂ} {Y : ℂ → ℂ} {Cst : ℂ}
    (hY : TripticMultiplicativeSource τ σ Y Cst)
    (hτ : 0 < τ.im) (hσ : 0 < σ.im)
    (hindep : ∀ n m j : ℤ, (n : ℂ) * τ + (m : ℂ) * σ + (j : ℂ) = 0 → n = 0 ∧ m = 0 ∧ j = 0)
    (p : ℂ) :
    tripticOrbitCharge Y σ p = tripticOrbitCharge Y τ p := by
  have hlogmero : MeromorphicOn (logDeriv Y) Set.univ := fun z _ =>
    ((hY.mero z (Set.mem_univ z)).deriv).div (hY.mero z (Set.mem_univ z))
  have hper : ∀ z : ℂ, logDeriv Y (z + 1) = logDeriv Y z := fun z ↦
    logDeriv_of_periodic hY.periodic z
  have hrec := triptic_orbit_residue_reciprocity hlogmero (periodicOneGerm_of_forall hper)
    hY.mixed hτ hσ hindep p (ℓ := (-1 : ℤ)) (by norm_num)
  have hσterm : ∀ m : ℤ,
      laurentCoeff (fun z => logDeriv Y (z + σ) - logDeriv Y z) (p + (m : ℂ) * σ) (-1)
        = ((shiftOrder Y σ (p + (m : ℂ) * σ) : ℤ) : ℂ) := fun m ↦
    laurentCoeff_shiftDiff_logDeriv hY.mero hY.finOrd σ _
  have hτterm : ∀ n : ℤ,
      laurentCoeff (fun z => logDeriv Y (z + τ) - logDeriv Y z) (p + (n : ℂ) * τ) (-1)
        = ((shiftOrder Y τ (p + (n : ℂ) * τ) : ℤ) : ℂ) := fun n ↦
    laurentCoeff_shiftDiff_logDeriv hY.mero hY.finOrd τ _
  rw [finsum_congr hσterm, finsum_congr hτterm, ← intCast_finsum, ← intCast_finsum] at hrec
  have hcast : ((tripticOrbitCharge Y σ p : ℤ) : ℂ) = ((tripticOrbitCharge Y τ p : ℤ) : ℂ) := hrec
  exact_mod_cast hcast

end

end GaloisForLFunctions.HTGeometry
