import GaloisForLFunctions.RHTower.LandauAbscissaRigidity

/-!
# A Laplace abscissa exists

Lebesgue measure on the positive half line has Laplace abscissa zero: to the right of zero the
exponential kernel is integrable, and to the left it is bounded below by one, whose mass on the half
line is infinite.  This realizes the abscissa interface, so the Taylor-radius rigidity statements are
not vacuous.
-/

open MeasureTheory Set
open scoped ENNReal

namespace GaloisForLFunctions

namespace RHTower

theorem laplaceMass_volume_ne_top {σ : ℝ} (hσ : 0 < σ) :
    laplaceMass volume σ ≠ ⊤ := by
  have hint : IntegrableOn (fun u : ℝ => Real.exp (-σ * u)) (Ioi 0) volume :=
    exp_neg_integrableOn_Ioi 0 hσ
  have hnonneg : 0 ≤ᶠ[ae (volume.restrict (Ioi (0 : ℝ)))]
      fun u : ℝ => Real.exp (-σ * u) :=
    Filter.Eventually.of_forall fun u => (Real.exp_pos _).le
  have hfin : ∫⁻ u, ENNReal.ofReal (Real.exp (-σ * u))
      ∂(volume.restrict (Ioi (0 : ℝ))) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal hnonneg).mp hint.2
  exact ne_of_lt hfin

theorem laplaceMass_volume_eq_top {σ : ℝ} (hσ : σ < 0) :
    laplaceMass volume σ = ⊤ := by
  rw [eq_top_iff]
  calc (⊤ : ℝ≥0∞) = volume (Ioi (0 : ℝ)) := Real.volume_Ioi.symm
    _ = ∫⁻ _ in Ioi (0 : ℝ), (1 : ℝ≥0∞) := (setLIntegral_one _).symm
    _ ≤ laplaceMass volume σ := by
        unfold laplaceMass
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        rw [ENNReal.one_le_ofReal]
        have hu' : 0 < u := hu
        have hpos : 0 ≤ -σ * u := by nlinarith
        calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
          _ ≤ Real.exp (-σ * u) := Real.exp_le_exp.mpr hpos

/-- **Lebesgue measure has Laplace abscissa zero.** -/
theorem isAbscissa_volume_zero : IsAbscissa volume 0 :=
  ⟨fun _ hσ => laplaceMass_volume_ne_top hσ, fun _ hσ => laplaceMass_volume_eq_top hσ⟩

end RHTower

end GaloisForLFunctions
