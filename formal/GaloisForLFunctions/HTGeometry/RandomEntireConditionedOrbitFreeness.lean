import GaloisForLFunctions.HTGeometry.AvoidingRandomAffineJetFreeness
import GaloisForLFunctions.HTGeometry.FiniteJetLawDeterministicGauge

/-!
# Finite Taylor conditioning leaves the translation orbit free

Conditioning the clamped random entire series on any finite prefix of its coefficients replaces it
by a deterministic polynomial plus the tail series in the remaining coordinates, whose law is again
the same countable product.  The tail has degenerate jet packets only at the origin, and escaping
witnesses can be chosen away from it, so the conditioned source still has an almost surely free
translation orbit.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem HasAvoidingAbsolutelyContinuousFiniteAffineJetLaws.add_const
    {Ω Λ : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {d : ℕ}
    (frame : Λ → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))) (Cav : Finset (Fin d → ℂ))
    (F : Ω → MultivariateEntire d)
    (hND : HasAvoidingAbsolutelyContinuousFiniteAffineJetLaws μ frame Cav F)
    (g : MultivariateEntire d) :
    HasAvoidingAbsolutelyContinuousFiniteAffineJetLaws μ frame Cav (fun ω => F ω + g) := by
  intro p base hpacket havoid
  obtain ⟨hmeas, hAC⟩ := hND p base hpacket havoid
  let X : Ω → Fin (affineJetPacketFiniteCoordinateCount p) → ℂ :=
    fun ω => finiteAffineJetPacketObservation frame p base (F ω)
  let c : Fin (affineJetPacketFiniteCoordinateCount p) → ℂ :=
    finiteAffineJetPacketObservation frame p base g
  have hsource : (fun ω => finiteAffineJetPacketObservation frame p base (F ω + g)) =
      fun ω => X ω + c := by
    funext ω
    exact finiteAffineJetPacketObservation_add frame p base (F ω) g
  rw [hsource]
  refine ⟨hmeas.add measurable_const, ?_⟩
  have htranslate : Measurable
      (fun x : Fin (affineJetPacketFiniteCoordinateCount p) → ℂ => x + c) := by
    fun_prop
  change Measure.map ((fun x => x + c) ∘ X) μ ≪ _
  rw [← Measure.map_map htranslate hmeas]
  exact map_add_const_absolutelyContinuous
    (affineJetPacketFiniteCoordinateCount p) _ hAC c

/-- **Almost-sure maximal translation-orbit freeness from node-avoiding jet laws.** -/
theorem ae_translationOrbit_free_of_avoidingJetLaws
    {Ω H : Type*} [MeasurableSpace Ω] [Countable H] (μ : Measure Ω)
    (shift : H → ℂ) (hshift : Function.Injective shift)
    (Cav : Finset (Fin 1 → ℂ)) (F : Ω → MultivariateEntire 1)
    (hND : HasAvoidingAbsolutelyContinuousFiniteAffineJetLaws μ
      (fun h => oneDimTranslationFrame (shift h)) Cav F) :
    ∀ᵐ ω ∂μ, ∀ (n : ℕ) (lab : Fin n → H), Function.Injective lab →
      ∀ P : MvPolynomial (RelationJetVar 1 n) (MvPolynomial (Fin 1) ℂ), P ≠ 0 →
        ∃ z : Fin 1 → ℂ,
          jetRelationValue
            (fun i => oneDimEntireTranslate (shift (lab i)) (F ω)) P z ≠ 0 := by
  have hframe : Function.Injective (fun h : H => oneDimTranslationFrame (shift h)) :=
    oneDimTranslationFrame_injective.comp hshift
  filter_upwards [ae_affineOrbit_free_of_avoidingJetLaws μ (d := 1) (by omega)
      (fun h => oneDimTranslationFrame (shift h)) hframe Cav F hND] with ω hω
  intro n lab hlab P hP
  obtain ⟨z, hz⟩ := hω n lab hlab P hP
  refine ⟨z, ?_⟩
  simpa only [affineJetRelationValue_eq_jetRelationValue, oneDimEntireTranslate] using hz

/-- **Finite Taylor conditioning.**  Fixing any finite prefix of the coefficients and any
deterministic entire passport leaves the translation orbit of the residual random source almost
surely differentially free. -/
theorem ae_translationOrbit_free_randomEntireTail_add_const
    {H : Type*} [Countable H] (shift : H → ℂ) (hshift : Function.Injective shift)
    (L : ℕ) (g : MultivariateEntire 1) :
    ∀ᵐ y ∂(Measure.infinitePi (fun _ : ℕ => complexSquareProbability)),
      ∀ (n : ℕ) (lab : Fin n → H), Function.Injective lab →
        ∀ P : MvPolynomial (RelationJetVar 1 n) (MvPolynomial (Fin 1) ℂ), P ≠ 0 →
          ∃ z : Fin 1 → ℂ,
            jetRelationValue
              (fun i => oneDimEntireTranslate (shift (lab i))
                (randomEntireTailSource L y + g)) P z ≠ 0 :=
  ae_translationOrbit_free_of_avoidingJetLaws _ shift hshift ({0} : Finset (Fin 1 → ℂ)) _
    ((hasAvoidingAbsolutelyContinuousFiniteAffineJetLaws_randomEntireTail shift L).add_const _ _ _
      _ g)

end

end GaloisForLFunctions.HTGeometry
