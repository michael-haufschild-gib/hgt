import GaloisForLFunctions.HTGeometry.AdditiveNoiseAbsoluteContinuity
import GaloisForLFunctions.HTGeometry.RandomAffineJetPacketFreeness

/-!
# Deterministic gauges preserve finite-jet nondegeneracy

Adding a deterministic entire source translates every finite affine jet packet by one fixed
vector.  Lebesgue absolute continuity, hence almost-sure maximal differential freeness, is
unchanged.  This is the measure-theoretic core of finite deterministic passport stability.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem finiteAffineJetPacketObservation_add
    {d : ℕ} {Λ : Type*}
    (frame : Λ → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ)))
    (p : FiniteMultivariateAffineJetPattern Λ d)
    (base : MultivariateAffinePatternRow p → Fin d → ℂ)
    (f g : MultivariateEntire d) :
    finiteAffineJetPacketObservation frame p base (f + g) =
      finiteAffineJetPacketObservation frame p base f +
        finiteAffineJetPacketObservation frame p base g := by
  funext k
  simp [finiteAffineJetPacketObservation]

/-- Finite-jet absolute continuity is invariant under addition of a deterministic entire source. -/
theorem HasAbsolutelyContinuousFiniteAffineJetLaws.add_const
    {Ω Λ : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {d : ℕ}
    (frame : Λ → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ)))
    (F : Ω → MultivariateEntire d)
    (hND : HasAbsolutelyContinuousFiniteAffineJetLaws μ frame F)
    (g : MultivariateEntire d) :
    HasAbsolutelyContinuousFiniteAffineJetLaws μ frame (fun ω => F ω + g) := by
  intro p base hpacket
  obtain ⟨hmeas, hAC⟩ := hND p base hpacket
  let X : Ω → Fin (affineJetPacketFiniteCoordinateCount p) → ℂ :=
    fun ω => finiteAffineJetPacketObservation frame p base (F ω)
  let c : Fin (affineJetPacketFiniteCoordinateCount p) → ℂ :=
    finiteAffineJetPacketObservation frame p base g
  have hsource : (fun ω => finiteAffineJetPacketObservation frame p base (F ω + g)) =
      fun ω => X ω + c := by
    funext ω
    exact finiteAffineJetPacketObservation_add frame p base (F ω) g
  rw [hsource]
  constructor
  · exact hmeas.add measurable_const
  · have htranslate : Measurable
        (fun x : Fin (affineJetPacketFiniteCoordinateCount p) → ℂ => x + c) := by
      fun_prop
    change Measure.map ((fun x => x + c) ∘ X) μ ≪ _
    rw [← Measure.map_map htranslate hmeas]
    exact map_add_const_absolutelyContinuous
      (affineJetPacketFiniteCoordinateCount p) _ hAC c

/-- Deterministic finite passports do not change the almost-sure free translation-orbit law once
the residual random source has nondegenerate finite jets. -/
theorem ae_translationOrbit_no_polynomialDifferentialRelation_add_const
    {Ω H : Type*} [MeasurableSpace Ω] [Countable H] (μ : Measure Ω)
    (shift : H → ℂ) (hshift : Function.Injective shift)
    (F : Ω → MultivariateEntire 1)
    (hND : HasAbsolutelyContinuousFiniteAffineJetLaws μ
      (fun h => oneDimTranslationFrame (shift h)) F)
    (g : MultivariateEntire 1) :
    ∀ᵐ ω ∂μ, ∀ (n : ℕ) (lab : Fin n → H), Function.Injective lab →
      ∀ P : MvPolynomial (RelationJetVar 1 n) (MvPolynomial (Fin 1) ℂ), P ≠ 0 →
        ∃ z : Fin 1 → ℂ,
          jetRelationValue
            (fun i => oneDimEntireTranslate (shift (lab i)) (F ω + g)) P z ≠ 0 := by
  exact ae_translationOrbit_no_polynomialDifferentialRelation
    μ shift hshift (fun ω => F ω + g) (hND.add_const μ _ F g)

end

end GaloisForLFunctions.HTGeometry
