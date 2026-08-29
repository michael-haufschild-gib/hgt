import GaloisForLFunctions.HTGeometry.AdditiveNoiseAbsoluteContinuity
import GaloisForLFunctions.HTGeometry.InfinitePiSumSplit
import GaloisForLFunctions.HTGeometry.RandomEntirePacketSplit
import GaloisForLFunctions.HTGeometry.RandomEntireTailSource
import GaloisForLFunctions.HTGeometry.SurjectiveLinearMapAbsoluteContinuity

/-!
# The bounded random entire series has nondegenerate finite jet laws

Every finite jet packet of the clamped random series splits into the Hermite evaluation of its
first `N` coordinates — a surjective linear image of an absolutely continuous product law — plus a
term depending only on the independent remaining coordinates.  Absolute continuity therefore
survives, so the random source realizes the finite-jet nondegeneracy hypothesis of the almost-sure
translation-orbit freeness theorem.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem continuous_finiteAffineJetPacketObservation {d : ℕ} {Λ : Type*}
    (frame : Λ → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))) (p : FiniteMultivariateAffineJetPattern Λ d)
    (base : MultivariateAffinePatternRow p → Fin d → ℂ) :
    Continuous
      (fun f : MultivariateEntire d => finiteAffineJetPacketObservation frame p base f) := by
  refine continuous_pi fun k => ?_
  exact (continuous_apply _).comp
    (multivariateAffinePatternObservationCLM frame p base).continuous

variable {H : Type*}

theorem packetTailObservation_eq (shift : H → ℂ) (p : FiniteMultivariateAffineJetPattern H 1)
    (base : MultivariateAffinePatternRow p → Fin 1 → ℂ) (y : ℕ → ℂ) :
    packetTailObservation shift p base y
      = finiteAffineJetPacketObservation (fun h => oneDimTranslationFrame (shift h)) p base
        (randomEntireTailSource (affineJetPacketFiniteCoordinateCount p) y) := by
  funext k
  exact (multivariateAffinePatternObservationCLM_oneDim shift p base _ _ _).symm

theorem measurable_packetTailObservation (shift : H → ℂ)
    (p : FiniteMultivariateAffineJetPattern H 1)
    (base : MultivariateAffinePatternRow p → Fin 1 → ℂ) :
    Measurable (packetTailObservation shift p base) := by
  rw [funext (packetTailObservation_eq shift p base)]
  exact ((continuous_finiteAffineJetPacketObservation _ p base).comp
    (continuous_randomEntireTailSource _)).measurable

/-- The joint law of the shifted coordinates and the clamped head is the product law. -/
theorem map_tailHead_infinitePi (N : ℕ) :
    Measure.map (fun x : ℕ → ℂ => ((fun k => x (k + N)), clampedComplexCoefficientHead N x))
        (Measure.infinitePi (fun _ : ℕ => complexSquareProbability))
      = (Measure.infinitePi (fun _ : ℕ => complexSquareProbability)).prod
        (Measure.pi (fun _ : Fin N => complexSquareProbability)) := by
  classical
  set clampFin : (Fin N → ℂ) → (Fin N → ℂ) := fun c i => clampComplexSquare (c i) with hclampFin
  have hclampMeas : Measurable clampFin := by
    apply measurable_pi_lambda
    intro i
    exact measurable_clampComplexSquare.comp (measurable_pi_apply (X := fun _ : Fin N => ℂ) i)
  have hheadtail : Measurable
      (fun x : ℕ → ℂ => ((fun i : Fin N => x (i : ℕ)), fun k : ℕ => x (k + N))) := by
    refine Measurable.prodMk ?_ ?_
    · exact measurable_pi_lambda _ fun i => measurable_pi_apply (X := fun _ : ℕ => ℂ) (i : ℕ)
    · exact measurable_pi_lambda _ fun k => measurable_pi_apply (X := fun _ : ℕ => ℂ) (k + N)
  have hswapmap : Measurable
      (fun q : (Fin N → ℂ) × (ℕ → ℂ) => (q.2, clampFin q.1)) :=
    (measurable_snd).prodMk (hclampMeas.comp measurable_fst)
  have hcomp : (fun x : ℕ → ℂ => ((fun k => x (k + N)), clampedComplexCoefficientHead N x))
      = (fun q : (Fin N → ℂ) × (ℕ → ℂ) => (q.2, clampFin q.1))
        ∘ (fun x : ℕ → ℂ => ((fun i : Fin N => x (i : ℕ)), fun k : ℕ => x (k + N))) := rfl
  rw [hcomp, ← Measure.map_map hswapmap hheadtail, map_headTail_infinitePi]
  have hsplit : (fun q : (Fin N → ℂ) × (ℕ → ℂ) => (q.2, clampFin q.1))
      = Prod.swap ∘ (Prod.map clampFin (id : (ℕ → ℂ) → (ℕ → ℂ))) := rfl
  rw [hsplit, ← Measure.map_map measurable_swap (hclampMeas.prodMap measurable_id),
    ← Measure.map_prod_map _ _ hclampMeas measurable_id]
  have hclampLaw : Measure.map clampFin (Measure.pi (fun _ : Fin N => complexSquareProbability))
      = Measure.pi (fun _ : Fin N => complexSquareProbability) := by
    rw [hclampFin, Measure.pi_map_pi (fun _ : Fin N => measurable_clampComplexSquare.aemeasurable)]
    simp only [map_clampComplexSquare_complexSquareProbability]
  rw [hclampLaw, Measure.map_id, Measure.prod_swap]

/-- **Finite-jet nondegeneracy of the bounded random entire series.** -/
theorem hasAbsolutelyContinuousFiniteAffineJetLaws_boundedRandomEntire (shift : H → ℂ) :
    HasAbsolutelyContinuousFiniteAffineJetLaws
      (Measure.infinitePi (fun _ : ℕ => complexSquareProbability))
      (fun h => oneDimTranslationFrame (shift h))
      (fun x : ℕ → ℂ => boundedRandomEntireSource x) := by
  classical
  intro p base hpacket
  set N : ℕ := affineJetPacketFiniteCoordinateCount p with hN
  set L := packetHermiteMap shift p base with hL
  set G := packetTailObservation shift p base with hG
  have hLmeas : Measurable L := L.continuous_of_finiteDimensional.measurable
  have hGmeas : Measurable G := measurable_packetTailObservation shift p base
  have hheadMeas : Measurable (clampedComplexCoefficientHead N) :=
    measurable_clampedComplexCoefficientHead N
  have htailMeas : Measurable (fun x : ℕ → ℂ => fun k => x (k + N)) :=
    measurable_pi_lambda _ fun k => measurable_pi_apply (X := fun _ : ℕ => ℂ) (k + N)
  have hobs : (fun x : ℕ → ℂ => finiteAffineJetPacketObservation
      (fun h => oneDimTranslationFrame (shift h)) p base (boundedRandomEntireSource x))
      = (fun q : (ℕ → ℂ) × (Fin N → ℂ) => q.2 + G q.1)
        ∘ (fun x : ℕ → ℂ => ((fun k => x (k + N)), L (clampedComplexCoefficientHead N x))) := by
    funext x
    rw [Function.comp_apply, finiteAffineJetPacketObservation_split shift p base x]
  have hmapg : Measurable (fun q : (ℕ → ℂ) × (Fin N → ℂ) => q.2 + G q.1) :=
    measurable_snd.add (hGmeas.comp measurable_fst)
  have hmapf : Measurable (fun x : ℕ → ℂ =>
      ((fun k => x (k + N)), L (clampedComplexCoefficientHead N x))) :=
    htailMeas.prodMk (hLmeas.comp hheadMeas)
  have hmapf0 : Measurable (fun x : ℕ → ℂ =>
      ((fun k => x (k + N)), clampedComplexCoefficientHead N x)) :=
    htailMeas.prodMk hheadMeas
  have hprodmap : Measurable (Prod.map (id : (ℕ → ℂ) → (ℕ → ℂ)) (L : _ → _)) :=
    measurable_id.prodMap hLmeas
  have hpair : Measure.map
      (fun x : ℕ → ℂ => ((fun k => x (k + N)), L (clampedComplexCoefficientHead N x)))
      (Measure.infinitePi (fun _ : ℕ => complexSquareProbability))
      = (Measure.infinitePi (fun _ : ℕ => complexSquareProbability)).prod
        (Measure.map L (Measure.pi (fun _ : Fin N => complexSquareProbability))) := by
    have hfac : (fun x : ℕ → ℂ => ((fun k => x (k + N)), L (clampedComplexCoefficientHead N x)))
        = (Prod.map (id : (ℕ → ℂ) → (ℕ → ℂ)) L)
          ∘ (fun x : ℕ → ℂ => ((fun k => x (k + N)), clampedComplexCoefficientHead N x)) := rfl
    rw [hfac, ← Measure.map_map hprodmap hmapf0, map_tailHead_infinitePi,
      ← Measure.map_prod_map _ _ measurable_id hLmeas, Measure.map_id]
  refine ⟨?_, ?_⟩
  · exact ((continuous_finiteAffineJetPacketObservation _ p base).comp
      continuous_boundedRandomEntireSource).measurable
  · rw [hobs, ← Measure.map_map hmapg hmapf, hpair]
    haveI : IsProbabilityMeasure
        (Measure.map L (Measure.pi (fun _ : Fin N => complexSquareProbability))) :=
      Measure.isProbabilityMeasure_map hLmeas.aemeasurable
    refine map_snd_add_noise_prod_absolutelyContinuous N _ _ ?_ G hGmeas
    exact map_surjectiveLinearMap_absolutelyContinuous L
      (surjective_packetHermiteMap hpacket) _
      (pi_complexSquareProbability_absolutelyContinuous N)

end

end GaloisForLFunctions.HTGeometry
