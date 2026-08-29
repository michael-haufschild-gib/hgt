import GaloisForLFunctions.HTGeometry.AffineJetDifferentialIndependence
import GaloisForLFunctions.HTGeometry.AffineOperatorRankLaw
import GaloisForLFunctions.HTGeometry.FiniteJetPolynomialAvoidance

/-!
# Almost-sure affine-orbit differential freeness from finite-jet laws

The deterministic affine jet-packet construction chooses, for each countable relation shape, a
finite packet of distinct affine-image points and a nonzero determinant polynomial in the jets at
those points.  Absolute continuity of every such finite-coordinate law makes each determinant
defect null.  Countability of relation shapes then gives simultaneous avoidance, and the existing
deterministic relation detector upgrades it to full finite-family differential freeness.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Finite coordinate count of the row-by-frame mixed-jet packet attached to a relation pattern. -/
abbrev affineJetPacketFiniteCoordinateCount {d : ℕ} {Λ : Type*}
    (p : FiniteMultivariateAffineJetPattern Λ d) : ℕ :=
  Fintype.card (MultivariateAffinePatternRow p × MultivariateAffinePatternJet p)

/-- Reindex one chosen affine jet observation packet by a canonical finite type. -/
def finiteAffineJetPacketObservation {d : ℕ} {Λ : Type*}
    (frame : Λ → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ)))
    (p : FiniteMultivariateAffineJetPattern Λ d)
    (base : MultivariateAffinePatternRow p → Fin d → ℂ)
    (f : MultivariateEntire d) :
    Fin (affineJetPacketFiniteCoordinateCount p) → ℂ :=
  fun k => multivariateAffinePatternObservationCLM frame p base f
    ((Fintype.equivFin
      (MultivariateAffinePatternRow p × MultivariateAffinePatternJet p)).symm k)

/-- Chosen determinant polynomial, reindexed by the same canonical finite coordinate type. -/
def finiteAffineJetPacketDeterminant {d : ℕ} {Λ : Type*}
    (p : FiniteMultivariateAffineJetPattern Λ d)
    (base : MultivariateAffinePatternRow p → Fin d → ℂ) :
    MvPolynomial (Fin (affineJetPacketFiniteCoordinateCount p)) ℂ :=
  MvPolynomial.rename
    (Fintype.equivFin
      (MultivariateAffinePatternRow p × MultivariateAffinePatternJet p))
    (multivariateCoefficientPatternDeterminant
      base p.coordinateExponent p.jetExponent)

/-- Reindexing does not change evaluation of the chosen determinant. -/
theorem eval_finiteAffineJetPacketDeterminant {d : ℕ} {Λ : Type*}
    (frame : Λ → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ)))
    (p : FiniteMultivariateAffineJetPattern Λ d)
    (base : MultivariateAffinePatternRow p → Fin d → ℂ)
    (f : MultivariateEntire d) :
    MvPolynomial.eval (finiteAffineJetPacketObservation frame p base f)
        (finiteAffineJetPacketDeterminant p base) =
      MvPolynomial.eval (multivariateAffinePatternObservationCLM frame p base f)
        (multivariateCoefficientPatternDeterminant
          base p.coordinateExponent p.jetExponent) := by
  rw [finiteAffineJetPacketDeterminant, MvPolynomial.eval_rename]
  have hcoords :
      finiteAffineJetPacketObservation frame p base f ∘
          (Fintype.equivFin
            (MultivariateAffinePatternRow p × MultivariateAffinePatternJet p)) =
        multivariateAffinePatternObservationCLM frame p base f := by
    funext x
    simp [finiteAffineJetPacketObservation]
  rw [hcoords]

/-- Every chosen finite determinant is genuinely nonzero; the escaping source in the witness
certifies this before the coordinate reindexing. -/
theorem finiteAffineJetPacketDeterminant_ne_zero_of_witness {d : ℕ} {Λ : Type*}
    (frame : Λ → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ)))
    (p : FiniteMultivariateAffineJetPattern Λ d)
    (wit : MultivariateAffinePatternWitness frame p) :
    finiteAffineJetPacketDeterminant p wit.base ≠ 0 := by
  have hD : multivariateCoefficientPatternDeterminant wit.base
      p.coordinateExponent p.jetExponent ≠ 0 := by
    intro hzero
    have hescape := wit.escapes
    rw [hzero] at hescape
    simp at hescape
  exact (MvPolynomial.rename_injective
    (Fintype.equivFin
      (MultivariateAffinePatternRow p × MultivariateAffinePatternJet p))
    (Fintype.equivFin
      (MultivariateAffinePatternRow p × MultivariateAffinePatternJet p)).injective).ne hD

theorem finiteAffineJetPacketDeterminant_ne_zero {d : ℕ} (hd : 0 < d) {Λ : Type*}
    (frame : Λ → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))) (hframe : Function.Injective frame)
    (p : FiniteMultivariateAffineJetPattern Λ d) :
    finiteAffineJetPacketDeterminant p
      (affineJetPacketWitness hd frame hframe p).base ≠ 0 :=
  finiteAffineJetPacketDeterminant_ne_zero_of_witness frame p _

/-- Membership in a chosen residual set is nonvanishing of every chosen pattern determinant. -/
theorem mem_multivariateAffinePatternResidualSet_iff {d : ℕ} {Λ : Type*}
    (frame : Λ → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ)))
    (witness : ∀ p : FiniteMultivariateAffineJetPattern Λ d,
      MultivariateAffinePatternWitness frame p)
    (f : MultivariateEntire d) :
    f ∈ multivariateAffinePatternResidualSet frame witness ↔
      ∀ p : FiniteMultivariateAffineJetPattern Λ d,
        MvPolynomial.eval
            (multivariateAffinePatternObservationCLM frame p (witness p).base f)
            (multivariateCoefficientPatternDeterminant
              (witness p).base p.coordinateExponent p.jetExponent) ≠ 0 :=
  Iff.rfl

/-- Finite-jet nondegeneracy for a random entire source along an affine palette.  Every finite
rectangular mixed-jet packet read at pairwise distinct affine-image points is measurable and has
law absolutely continuous with respect to complex Lebesgue measure. -/
def HasAbsolutelyContinuousFiniteAffineJetLaws
    {Ω Λ : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {d : ℕ}
    (frame : Λ → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ)))
    (F : Ω → MultivariateEntire d) : Prop :=
  ∀ (p : FiniteMultivariateAffineJetPattern Λ d)
      (base : MultivariateAffinePatternRow p → Fin d → ℂ),
    Function.Injective
        (fun q : MultivariateAffinePatternRow p × Fin p.frameCount =>
          frame (p.frameCode q.2) (base q.1)) →
      Measurable (fun ω => finiteAffineJetPacketObservation frame p base (F ω)) ∧
      (Measure.map (fun ω => finiteAffineJetPacketObservation frame p base (F ω)) μ).AbsolutelyContinuous
        (volume : Measure (Fin (affineJetPacketFiniteCoordinateCount p) → ℂ))

/-- **Probability-one affine jet-packet genericity.**  If every chosen finite jet packet is
measurable and has law absolutely continuous with respect to complex Lebesgue measure, a random
source avoids all relation determinants almost surely. -/
theorem measure_compl_preimage_residualSet_eq_zero
    {Ω Λ : Type*} [MeasurableSpace Ω] [Countable Λ] (μ : Measure Ω)
    {d : ℕ}
    (frame : Λ → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ)))
    (witness : ∀ p : FiniteMultivariateAffineJetPattern Λ d,
      MultivariateAffinePatternWitness frame p)
    (F : Ω → MultivariateEntire d)
    (hmeas : ∀ p : FiniteMultivariateAffineJetPattern Λ d,
      Measurable (fun ω => finiteAffineJetPacketObservation frame p
        (witness p).base (F ω)))
    (hAC : ∀ p : FiniteMultivariateAffineJetPattern Λ d,
      (Measure.map (fun ω => finiteAffineJetPacketObservation frame p
        (witness p).base (F ω)) μ).AbsolutelyContinuous
        (volume : Measure (Fin (affineJetPacketFiniteCoordinateCount p) → ℂ))) :
    μ (F ⁻¹' multivariateAffinePatternResidualSet frame witness)ᶜ = 0 := by
  let n : FiniteMultivariateAffineJetPattern Λ d → ℕ :=
    fun p => affineJetPacketFiniteCoordinateCount p
  let X : ∀ p : FiniteMultivariateAffineJetPattern Λ d,
      Ω → (Fin (n p) → ℂ) :=
    fun p ω => finiteAffineJetPacketObservation frame p (witness p).base (F ω)
  let P : ∀ p : FiniteMultivariateAffineJetPattern Λ d,
      MvPolynomial (Fin (n p)) ℂ :=
    fun p => finiteAffineJetPacketDeterminant p (witness p).base
  have hnull : μ {ω | ∃ p, MvPolynomial.eval (X p ω) (P p) = 0} = 0 :=
    measure_exists_mvPolynomial_eval_eq_zero_of_countable μ n X
      (fun p => hmeas p) (fun p => hAC p) P
      (fun p => finiteAffineJetPacketDeterminant_ne_zero_of_witness frame p (witness p))
  have hbad : (F ⁻¹' multivariateAffinePatternResidualSet frame witness)ᶜ =
      {ω | ∃ p, MvPolynomial.eval (X p ω) (P p) = 0} := by
    ext ω
    simp only [Set.mem_compl_iff, Set.mem_preimage, Set.mem_setOf_eq]
    rw [mem_multivariateAffinePatternResidualSet_iff]
    simp only [not_forall, Classical.not_not]
    apply exists_congr
    intro p
    rw [eval_finiteAffineJetPacketDeterminant frame p (witness p).base (F ω)]
  rw [hbad]
  exact hnull

/-- **Probability-one affine jet-packet genericity.**  If every chosen finite jet packet is
measurable and has law absolutely continuous with respect to complex Lebesgue measure, a random
source avoids all relation determinants almost surely. -/
theorem measure_compl_preimage_affineJetPacketGenericSet_eq_zero
    {Ω Λ : Type*} [MeasurableSpace Ω] [Countable Λ] (μ : Measure Ω)
    {d : ℕ} (hd : 0 < d)
    (frame : Λ → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))) (hframe : Function.Injective frame)
    (F : Ω → MultivariateEntire d)
    (hmeas : ∀ p : FiniteMultivariateAffineJetPattern Λ d,
      Measurable (fun ω => finiteAffineJetPacketObservation frame p
        (affineJetPacketWitness hd frame hframe p).base (F ω)))
    (hAC : ∀ p : FiniteMultivariateAffineJetPattern Λ d,
      (Measure.map (fun ω => finiteAffineJetPacketObservation frame p
        (affineJetPacketWitness hd frame hframe p).base (F ω)) μ).AbsolutelyContinuous
        (volume : Measure (Fin (affineJetPacketFiniteCoordinateCount p) → ℂ))) :
    μ (F ⁻¹' affineJetPacketGenericSet hd frame hframe)ᶜ = 0 :=
  measure_compl_preimage_residualSet_eq_zero μ frame
    (affineJetPacketWitness hd frame hframe) F hmeas hAC

/-- Finite-jet-law form of probability-one affine jet-packet genericity. -/
theorem measure_compl_preimage_affineJetPacketGenericSet_eq_zero_of_finiteJetLaws
    {Ω Λ : Type*} [MeasurableSpace Ω] [Countable Λ] (μ : Measure Ω)
    {d : ℕ} (hd : 0 < d)
    (frame : Λ → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))) (hframe : Function.Injective frame)
    (F : Ω → MultivariateEntire d)
    (hND : HasAbsolutelyContinuousFiniteAffineJetLaws μ frame F) :
    μ (F ⁻¹' affineJetPacketGenericSet hd frame hframe)ᶜ = 0 := by
  apply measure_compl_preimage_affineJetPacketGenericSet_eq_zero μ hd frame hframe F
  · intro p
    exact (hND p (affineJetPacketWitness hd frame hframe p).base
      (affineJetPacketWitness_packet_injective hd frame hframe p)).1
  · intro p
    exact (hND p (affineJetPacketWitness hd frame hframe p).base
      (affineJetPacketWitness_packet_injective hd frame hframe p)).2

/-- Almost-everywhere membership form of the probability-one genericity theorem. -/
theorem ae_mem_affineJetPacketGenericSet
    {Ω Λ : Type*} [MeasurableSpace Ω] [Countable Λ] (μ : Measure Ω)
    {d : ℕ} (hd : 0 < d)
    (frame : Λ → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))) (hframe : Function.Injective frame)
    (F : Ω → MultivariateEntire d)
    (hmeas : ∀ p : FiniteMultivariateAffineJetPattern Λ d,
      Measurable (fun ω => finiteAffineJetPacketObservation frame p
        (affineJetPacketWitness hd frame hframe p).base (F ω)))
    (hAC : ∀ p : FiniteMultivariateAffineJetPattern Λ d,
      (Measure.map (fun ω => finiteAffineJetPacketObservation frame p
        (affineJetPacketWitness hd frame hframe p).base (F ω)) μ).AbsolutelyContinuous
        (volume : Measure (Fin (affineJetPacketFiniteCoordinateCount p) → ℂ))) :
    ∀ᵐ ω ∂μ, F ω ∈ affineJetPacketGenericSet hd frame hframe := by
  rw [ae_iff]
  change μ (F ⁻¹' affineJetPacketGenericSet hd frame hframe)ᶜ = 0
  exact measure_compl_preimage_affineJetPacketGenericSet_eq_zero
    μ hd frame hframe F hmeas hAC

/-- **Almost-sure maximal affine-orbit differential freeness.**  Under the finite-jet law, every
finite injectively labelled affine suborbit avoids every nonzero polynomial-coefficient
differential relation. -/
theorem ae_affineOrbit_no_polynomialDifferentialRelation
    {Ω Λ : Type*} [MeasurableSpace Ω] [Countable Λ] (μ : Measure Ω)
    {d : ℕ} (hd : 0 < d)
    (frame : Λ → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))) (hframe : Function.Injective frame)
    (F : Ω → MultivariateEntire d)
    (hmeas : ∀ p : FiniteMultivariateAffineJetPattern Λ d,
      Measurable (fun ω => finiteAffineJetPacketObservation frame p
        (affineJetPacketWitness hd frame hframe p).base (F ω)))
    (hAC : ∀ p : FiniteMultivariateAffineJetPattern Λ d,
      (Measure.map (fun ω => finiteAffineJetPacketObservation frame p
        (affineJetPacketWitness hd frame hframe p).base (F ω)) μ).AbsolutelyContinuous
        (volume : Measure (Fin (affineJetPacketFiniteCoordinateCount p) → ℂ))) :
    ∀ᵐ ω ∂μ, ∀ (n : ℕ) (lab : Fin n → Λ), Function.Injective lab →
      ∀ P : MvPolynomial (RelationJetVar d n) (MvPolynomial (Fin d) ℂ), P ≠ 0 →
        ∃ z : Fin d → ℂ,
          affineJetRelationValue (fun i => frame (lab i)) (F ω) P z ≠ 0 := by
  filter_upwards [ae_mem_affineJetPacketGenericSet μ hd frame hframe F hmeas hAC]
    with ω hω
  intro n lab hlab P hP
  exact exists_affineJetRelationValue_ne_zero hd frame hframe hω lab hlab hP

/-- Finite-jet-law form of almost-sure maximal affine-orbit differential freeness. -/
theorem ae_affineOrbit_no_polynomialDifferentialRelation_of_finiteJetLaws
    {Ω Λ : Type*} [MeasurableSpace Ω] [Countable Λ] (μ : Measure Ω)
    {d : ℕ} (hd : 0 < d)
    (frame : Λ → ((Fin d → ℂ) ≃ᴬ[ℂ] (Fin d → ℂ))) (hframe : Function.Injective frame)
    (F : Ω → MultivariateEntire d)
    (hND : HasAbsolutelyContinuousFiniteAffineJetLaws μ frame F) :
    ∀ᵐ ω ∂μ, ∀ (n : ℕ) (lab : Fin n → Λ), Function.Injective lab →
      ∀ P : MvPolynomial (RelationJetVar d n) (MvPolynomial (Fin d) ℂ), P ≠ 0 →
        ∃ z : Fin d → ℂ,
          affineJetRelationValue (fun i => frame (lab i)) (F ω) P z ≠ 0 := by
  apply ae_affineOrbit_no_polynomialDifferentialRelation μ hd frame hframe F
  · intro p
    exact (hND p (affineJetPacketWitness hd frame hframe p).base
      (affineJetPacketWitness_packet_injective hd frame hframe p)).1
  · intro p
    exact (hND p (affineJetPacketWitness hd frame hframe p).base
      (affineJetPacketWitness_packet_injective hd frame hframe p)).2

/-! ### One-dimensional translation-orbit specialization -/

/-- Translation by `h` as a complex affine automorphism of the one-coordinate model. -/
def oneDimTranslationFrame (h : ℂ) :
    ((Fin 1 → ℂ) ≃ᴬ[ℂ] (Fin 1 → ℂ)) :=
  ContinuousAffineEquiv.constVAdd ℂ (Fin 1 → ℂ) (fun _ => h)

@[simp]
theorem oneDimTranslationFrame_apply (h : ℂ) (z : Fin 1 → ℂ) (i : Fin 1) :
    oneDimTranslationFrame h z i = z i + h := by
  change h + z i = z i + h
  exact add_comm h (z i)

/-- Distinct complex shifts give distinct affine translation frames. -/
theorem oneDimTranslationFrame_injective : Function.Injective oneDimTranslationFrame := by
  intro h k heq
  have hval := congrArg
    (fun e : (Fin 1 → ℂ) ≃ᴬ[ℂ] (Fin 1 → ℂ) => e 0 0) heq
  simpa using hval

/-- Translate a one-dimensional multivariate entire source. -/
def oneDimEntireTranslate (h : ℂ) (f : MultivariateEntire 1) : MultivariateEntire 1 :=
  multivariateEntireAffinePullback (oneDimTranslationFrame h) f

@[simp]
theorem oneDimEntireTranslate_apply (h : ℂ) (f : MultivariateEntire 1)
    (z : Fin 1 → ℂ) :
    (oneDimEntireTranslate h f).1 z = f.1 (fun i => z i + h) := by
  rw [oneDimEntireTranslate, multivariateEntireAffinePullback_apply]
  congr 1
  funext i
  exact oneDimTranslationFrame_apply h z i

/-- **Almost-sure maximal translation-orbit differential freeness.**  For every countable
injectively coded set of complex shifts, finite-jet absolute continuity implies that every finite
family of distinct translates avoids every nonzero polynomial-coefficient differential relation. -/
theorem ae_translationOrbit_no_polynomialDifferentialRelation
    {Ω H : Type*} [MeasurableSpace Ω] [Countable H] (μ : Measure Ω)
    (shift : H → ℂ) (hshift : Function.Injective shift)
    (F : Ω → MultivariateEntire 1)
    (hND : HasAbsolutelyContinuousFiniteAffineJetLaws μ
      (fun h => oneDimTranslationFrame (shift h)) F) :
    ∀ᵐ ω ∂μ, ∀ (n : ℕ) (lab : Fin n → H), Function.Injective lab →
      ∀ P : MvPolynomial (RelationJetVar 1 n) (MvPolynomial (Fin 1) ℂ), P ≠ 0 →
        ∃ z : Fin 1 → ℂ,
          jetRelationValue
            (fun i => oneDimEntireTranslate (shift (lab i)) (F ω)) P z ≠ 0 := by
  have hframe : Function.Injective (fun h : H => oneDimTranslationFrame (shift h)) :=
    oneDimTranslationFrame_injective.comp hshift
  filter_upwards [ae_affineOrbit_no_polynomialDifferentialRelation_of_finiteJetLaws
      μ (d := 1) (by omega) (fun h => oneDimTranslationFrame (shift h)) hframe F hND]
    with ω hω
  intro n lab hlab P hP
  obtain ⟨z, hz⟩ := hω n lab hlab P hP
  refine ⟨z, ?_⟩
  simpa only [affineJetRelationValue_eq_jetRelationValue, oneDimEntireTranslate] using hz

end

end GaloisForLFunctions.HTGeometry
