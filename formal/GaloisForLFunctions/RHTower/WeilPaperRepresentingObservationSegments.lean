import GaloisForLFunctions.RHTower.WeilPaperComplexNullObservations
import GaloisForLFunctions.RHTower.WeilPaperSpectralObservationSegments

/-!
# Intervals of representing spectral probabilities with fixed observations

Positive conjugation averaging upgrades the prime-mask kernel construction to
full complex integer cancellation. Convex interpolation then gives an injective
interval of actual origin-representing spectral probabilities with any finite
linear observation vector fixed, including full energy and selected correlations.
-/

noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- Normalized convex interpolation retains every full complex integer-null condition. -/
def paperComplexNullSegment (a b : ComplexNullMixture) (t : Set.Icc (0 : ℝ) 1) :
    ComplexNullMixture :=
  ⟨paperNormalizedSegment a.1 b.1 t, by
    intro n hn
    rw [mixtureSample_paperNormalizedSegment, a.2 n hn, b.2 n hn,
      smul_zero, smul_zero, zero_add]⟩

/-- Every finite real linear observation vector is constant on some injective interval
of actual origin-representing spectral probabilities. -/
theorem exists_injective_spectralRepresentingMeasures_same_finite_observations (k : ℕ)
    (T : (WeilTestFn →₀ ℝ) →ₗ[ℝ] (Fin k → ℝ)) :
    ∃ c : Set.Icc (0 : ℝ) 1 → ComplexNullMixture,
      (∀ s t, T (c s).1.1 = T (c t).1.1) ∧
      Function.Injective (fun t => spectralRepresentingMeasure (c t)) := by
  obtain ⟨a, b, hT, r, hr⟩ := exists_complexNullMixtures_same_finite_observations k T
  have hconst (t : Set.Icc (0 : ℝ) 1) :
      T (paperComplexNullSegment a b t).1.1 = T a.1.1 := by
    change T (paperNormalizedSegment a.1 b.1 t).1 = _
    rw [paperNormalizedSegment_observe, ← hT, ← add_smul, sub_add_cancel, one_smul]
  refine ⟨paperComplexNullSegment a b, fun s t => (hconst s).trans (hconst t).symm, ?_⟩
  intro s t hst
  have hleft : (r.1.1 : ℕ) ≠ 0 := by
    have := (Finset.mem_Icc.mp r.1.1.property).1
    omega
  have hright : (r.1.2 : ℕ) ≠ 0 := by
    have := (Finset.mem_Icc.mp r.1.2.property).1
    omega
  have h := congrArg (fun μ : RepresentingPhaseMeasure =>
    phaseMoment μ.1 (r.1.1 : ℕ) (r.1.2 : ℕ)) hst
  change phaseMoment (spectralTorusProbability (paperNormalizedSegment a.1 b.1 s)) _ _ =
    phaseMoment (spectralTorusProbability (paperNormalizedSegment a.1 b.1 t)) _ _ at h
  rw [phaseMoment_spectralTorusProbability _ hleft hright,
    phaseMoment_spectralTorusProbability _ hleft hright,
    mixtureSample_paperNormalizedSegment, mixtureSample_paperNormalizedSegment,
    Complex.real_smul, Complex.real_smul, Complex.real_smul, Complex.real_smul] at h
  let A := mixtureSample a.1.1 (Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ))
  let B := mixtureSample b.1.1 (Real.log (r.1.1 : ℕ) - Real.log (r.1.2 : ℕ))
  have hz : ((s.1 : ℂ) - (t.1 : ℂ)) * (B - A) = 0 := by
    dsimp [A, B]
    push_cast at h
    linear_combination h
  have hd : (s.1 : ℂ) - (t.1 : ℂ) = 0 :=
    (mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hr.symm)
  exact Subtype.ext (Complex.ofReal_injective (sub_eq_zero.mp hd))

/-- An entire injective interval of representing spectral probabilities can share full
energy and any chosen finite list of complex autocorrelation samples. -/
theorem exists_injective_spectralRepresentingMeasures_same_energy_samples {k : ℕ}
    (y : Fin k → ℝ) :
    ∃ c : Set.Icc (0 : ℝ) 1 → ComplexNullMixture,
      (∀ s t, energy (c s).1.1 = energy (c t).1.1) ∧
      (∀ i s t, mixtureSample (c s).1.1 (y i) = mixtureSample (c t).1.1 (y i)) ∧
      Function.Injective (fun t => spectralRepresentingMeasure (c t)) := by
  let E := ℝ × (Fin k → ℂ)
  let e : E ≃ₗ[ℝ] (Fin (Module.finrank ℝ E) → ℝ) := (Module.finBasis ℝ E).equivFun
  obtain ⟨c, hc, hinj⟩ := exists_injective_spectralRepresentingMeasures_same_finite_observations
    (Module.finrank ℝ E) (e.toLinearMap.comp (paperEnergySampleObserver y))
  have hobs s t : paperEnergySampleObserver y (c s).1.1 =
      paperEnergySampleObserver y (c t).1.1 := e.injective (hc s t)
  exact ⟨c, fun s t => congrArg Prod.fst (hobs s t),
    fun i s t => congrFun (congrArg Prod.snd (hobs s t)) i, hinj⟩

end RHTower.WeilWorkPBAP
