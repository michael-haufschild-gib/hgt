import GaloisForLFunctions.HTGeometry.AvoidingAffineJetPacketWitness
import GaloisForLFunctions.HTGeometry.RandomEntireTailPacketSplit

/-!
# Almost-sure freeness from jet laws that are nondegenerate away from prescribed nodes

A source that vanishes to a fixed order at a distinguished point has degenerate jet packets there,
but nowhere else.  Since the escaping witness of a finite pattern can be chosen with all its nodes
outside any prescribed finite set, absolute continuity away from that set already gives almost-sure
maximal differential freeness.  This is what a random series conditioned on a finite Taylor
passport needs.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Finite-jet nondegeneracy required only at packets whose nodes avoid a prescribed finite set. -/
def HasAvoidingAbsolutelyContinuousFiniteAffineJetLaws
    {Ω Λ : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {d : ℕ}
    (frame : Λ → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))) (Cav : Finset (Fin d → ℂ))
    (F : Ω → MultivariateEntire d) : Prop :=
  ∀ (p : FiniteMultivariateAffineJetPattern Λ d)
      (base : MultivariateAffinePatternRow p → Fin d → ℂ),
    Function.Injective
        (fun q : MultivariateAffinePatternRow p × Fin p.frameCount =>
          frame (p.frameCode q.2) (base q.1)) →
      (∀ q : MultivariateAffinePatternRow p × Fin p.frameCount,
        frame (p.frameCode q.2) (base q.1) ∉ Cav) →
      Measurable (fun ω => finiteAffineJetPacketObservation frame p base (F ω)) ∧
      (Measure.map (fun ω => finiteAffineJetPacketObservation frame p base (F ω))
          μ).AbsolutelyContinuous
        (volume : Measure (Fin (affineJetPacketFiniteCoordinateCount p) → ℂ))

/-- **Almost-sure maximal affine-orbit freeness from node-avoiding jet laws.** -/
theorem ae_affineOrbit_free_of_avoidingJetLaws
    {Ω Λ : Type*} [MeasurableSpace Ω] [Countable Λ] (μ : Measure Ω)
    {d : ℕ} (hd : 0 < d)
    (frame : Λ → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))) (hframe : Function.Injective frame)
    (Cav : Finset (Fin d → ℂ)) (F : Ω → MultivariateEntire d)
    (hND : HasAvoidingAbsolutelyContinuousFiniteAffineJetLaws μ frame Cav F) :
    ∀ᵐ ω ∂μ, ∀ (n : ℕ) (lab : Fin n → Λ), Function.Injective lab →
      ∀ P : MvPolynomial (RelationJetVar d n) (MvPolynomial (Fin d) ℂ), P ≠ 0 →
        ∃ z : Fin d → ℂ,
          affineJetRelationValue (fun i => frame (lab i)) (F ω) P z ≠ 0 := by
  set witness := avoidingAffineJetPacketWitness hd frame hframe Cav with hwit
  have hdata : ∀ p : FiniteMultivariateAffineJetPattern Λ d,
      Measurable (fun ω => finiteAffineJetPacketObservation frame p (witness p).base (F ω)) ∧
      (Measure.map (fun ω => finiteAffineJetPacketObservation frame p
          (witness p).base (F ω)) μ).AbsolutelyContinuous
        (volume : Measure (Fin (affineJetPacketFiniteCoordinateCount p) → ℂ)) := by
    intro p
    exact hND p (witness p).base
      (avoidingAffineJetPacketWitness_packet_injective hd frame hframe Cav p)
      (fun q => avoidingAffineJetPacketWitness_avoids hd frame hframe Cav p q)
  have hzero := measure_compl_preimage_residualSet_eq_zero μ frame witness F
    (fun p => (hdata p).1) (fun p => (hdata p).2)
  have hae : ∀ᵐ ω ∂μ, F ω ∈ multivariateAffinePatternResidualSet frame witness := by
    rw [ae_iff]
    exact hzero
  filter_upwards [hae] with ω hω
  intro n lab hlab P hP
  exact exists_affineJetRelationValue_ne_zero_of_witness frame witness hω lab hlab hP

variable {H : Type*}

theorem packetNode_ne_zero_of_avoids {shift : H → ℂ}
    {p : FiniteMultivariateAffineJetPattern H 1}
    {base : MultivariateAffinePatternRow p → Fin 1 → ℂ}
    (havoid : ∀ q : MultivariateAffinePatternRow p × Fin p.frameCount,
      (fun h => oneDimTranslationFrame (shift h)) (p.frameCode q.2) (base q.1)
        ∉ ({0} : Finset (Fin 1 → ℂ)))
    (q : MultivariateAffinePatternRow p × Fin p.frameCount) :
    packetNode shift p base q ≠ 0 := by
  intro hzero
  rw [packetNode] at hzero
  refine havoid q ?_
  rw [Finset.mem_singleton]
  funext i
  fin_cases i
  simpa [oneDimTranslationFrame_apply] using hzero

/-- **Node-avoiding finite-jet nondegeneracy of the tail of the random entire series.** -/
theorem hasAvoidingAbsolutelyContinuousFiniteAffineJetLaws_randomEntireTail
    (shift : H → ℂ) (L : ℕ) :
    HasAvoidingAbsolutelyContinuousFiniteAffineJetLaws
      (Measure.infinitePi (fun _ : ℕ => complexSquareProbability))
      (fun h => oneDimTranslationFrame (shift h)) ({0} : Finset (Fin 1 → ℂ))
      (fun y : ℕ → ℂ => randomEntireTailSource L y) := by
  classical
  intro p base hpacket havoid
  set N : ℕ := affineJetPacketFiniteCoordinateCount p with hN
  set wt : ℕ → ℂ := fun n => ((4 : ℂ) * ((Nat.factorial (n + L)) : ℂ))⁻¹ with hwtdef
  set A := packetShiftedHermiteMap shift p base wt L with hA
  set G := packetTailObservationAt shift p base (N + L) with hG
  have hAmeas : Measurable A := A.continuous_of_finiteDimensional.measurable
  have hGmeas : Measurable G := measurable_packetTailObservationAt shift p base (N + L)
  have hheadMeas : Measurable (clampedComplexCoefficientHead N) :=
    measurable_clampedComplexCoefficientHead N
  have htailMeas : Measurable (fun y : ℕ → ℂ => fun k => y (k + N)) :=
    measurable_pi_lambda _ fun k => measurable_pi_apply (X := fun _ : ℕ => ℂ) (k + N)
  have hobs : (fun y : ℕ → ℂ => finiteAffineJetPacketObservation
      (fun h => oneDimTranslationFrame (shift h)) p base (randomEntireTailSource L y))
      = (fun q : (ℕ → ℂ) × (Fin N → ℂ) => q.2 + G q.1)
        ∘ (fun y : ℕ → ℂ => ((fun k => y (k + N)), A (clampedComplexCoefficientHead N y))) := by
    funext y
    rw [Function.comp_apply, finiteAffineJetPacketObservation_tail_split shift p base L y]
  have hmapg : Measurable (fun q : (ℕ → ℂ) × (Fin N → ℂ) => q.2 + G q.1) :=
    measurable_snd.add (hGmeas.comp measurable_fst)
  have hmapf : Measurable (fun y : ℕ → ℂ =>
      ((fun k => y (k + N)), A (clampedComplexCoefficientHead N y))) :=
    htailMeas.prodMk (hAmeas.comp hheadMeas)
  have hmapf0 : Measurable (fun y : ℕ → ℂ =>
      ((fun k => y (k + N)), clampedComplexCoefficientHead N y)) :=
    htailMeas.prodMk hheadMeas
  have hprodmap : Measurable (Prod.map (id : (ℕ → ℂ) → (ℕ → ℂ)) (A : _ → _)) :=
    measurable_id.prodMap hAmeas
  have hpair : Measure.map
      (fun y : ℕ → ℂ => ((fun k => y (k + N)), A (clampedComplexCoefficientHead N y)))
      (Measure.infinitePi (fun _ : ℕ => complexSquareProbability))
      = (Measure.infinitePi (fun _ : ℕ => complexSquareProbability)).prod
        (Measure.map A (Measure.pi (fun _ : Fin N => complexSquareProbability))) := by
    have hfac : (fun y : ℕ → ℂ => ((fun k => y (k + N)), A (clampedComplexCoefficientHead N y)))
        = (Prod.map (id : (ℕ → ℂ) → (ℕ → ℂ)) A)
          ∘ (fun y : ℕ → ℂ => ((fun k => y (k + N)), clampedComplexCoefficientHead N y)) := rfl
    rw [hfac, ← Measure.map_map hprodmap hmapf0, map_tailHead_infinitePi,
      ← Measure.map_prod_map _ _ measurable_id hAmeas, Measure.map_id]
  refine ⟨?_, ?_⟩
  · exact ((continuous_finiteAffineJetPacketObservation _ p base).comp
      (continuous_randomEntireTailSource L)).measurable
  · rw [hobs, ← Measure.map_map hmapg hmapf, hpair]
    haveI : IsProbabilityMeasure
        (Measure.map A (Measure.pi (fun _ : Fin N => complexSquareProbability))) :=
      Measure.isProbabilityMeasure_map hAmeas.aemeasurable
    refine map_snd_add_noise_prod_absolutelyContinuous N _ _ ?_ G hGmeas
    exact map_surjectiveLinearMap_absolutelyContinuous A
      (surjective_packetShiftedHermiteMap wt L
        (fun n => inv_ne_zero (mul_ne_zero (by norm_num)
          (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _))))
        hpacket (packetNode_ne_zero_of_avoids havoid)) _
      (pi_complexSquareProbability_absolutelyContinuous N)

end

end GaloisForLFunctions.HTGeometry
