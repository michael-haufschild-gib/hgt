import GaloisForLFunctions.HTGeometry.NevanlinnaBauerRetract

/-!
# Faces and the extremal stationary boundary of the Nevanlinna projector

The closed carrier subsets constructed from projective support are genuine faces for probability
mixtures.  The stationary simplex of the constraint kernel is the full boundary carrier, so its
extremal stationary laws are exactly the `N`-extremal leaves.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory OnePoint ProbabilityTheory Set
open scoped OnePoint ENNReal

noncomputable section

/-- `D` is a face of `C` for genuine probability mixtures. -/
def IsProbabilityLawFace {X : Type*} [MeasurableSpace X]
    (D C : Set (ProbabilityMeasure X)) : Prop :=
  D ⊆ C ∧
    ∀ (t : ℝ≥0∞) (ht : t ≤ 1), 0 < t → t < 1 →
      ∀ mu nu, mu ∈ C → nu ∈ C →
        probabilityMixture t ht mu nu ∈ D → mu ∈ D ∧ nu ∈ D

/-- Probability laws carried by any subset form a face of the full probability simplex. -/
theorem probabilityLawsCarriedBy_isProbabilityLawFace
    {X : Type*} [MeasurableSpace X] (K : Set X) :
    IsProbabilityLawFace (probabilityLawsCarriedBy K) Set.univ := by
  refine ⟨subset_univ _, ?_⟩
  intro t ht ht0 ht1 mu nu _ _ hmix
  change (probabilityMixture t ht mu nu : Measure X) Kᶜ = 0 at hmix
  rw [probabilityMixture_toMeasure, Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply] at hmix
  simp only [smul_eq_mul] at hmix
  have hparts : t * (mu : Measure X) Kᶜ = 0 ∧
      (1 - t) * (nu : Measure X) Kᶜ = 0 :=
    add_eq_zero.mp hmix
  have htne : t ≠ 0 := ne_of_gt ht0
  have hctne : 1 - t ≠ 0 := ne_of_gt (tsub_pos_iff_lt.mpr ht1)
  exact ⟨(mul_eq_zero.mp hparts.1).resolve_left htne,
    (mul_eq_zero.mp hparts.2).resolve_left hctne⟩

namespace NevanlinnaBoundaryFamily

variable {s : ℕ → ℝ} (F : NevanlinnaBoundaryFamily s)

/-- Every projective carrier subset gives a genuine face of the Nevanlinna boundary simplex. -/
theorem boundaryCarrierFace_isProbabilityLawFace (K : Set (OnePoint ℝ)) :
    IsProbabilityLawFace (F.boundaryCarrierFace K) (range F.barycenter) := by
  refine ⟨fun _ hnu => ⟨hnu.choose, hnu.choose_spec.2⟩, ?_⟩
  intro t ht ht0 ht1 mu nu hmu hnu hmix
  rcases hmu with ⟨eta, rfl⟩
  rcases hnu with ⟨theta, rfl⟩
  rcases hmix with ⟨rho, hrho, hmix⟩
  have hparameters : probabilityMixture t ht eta theta = rho := by
    apply F.barycenter_isClosedEmbedding.injective
    rw [F.barycenter_probabilityMixture]
    exact hmix.symm
  have hface := (probabilityLawsCarriedBy_isProbabilityLawFace K).2
    t ht ht0 ht1 eta theta (Set.mem_univ _) (Set.mem_univ _)
  have hparts : eta ∈ probabilityLawsCarriedBy K ∧
      theta ∈ probabilityLawsCarriedBy K := by
    apply hface
    rw [hparameters]
    exact hrho
  exact ⟨⟨eta, hparts.1, rfl⟩, ⟨theta, hparts.2, rfl⟩⟩

/-- Stationary probability laws of the constraint kernel, as a subset of the probability
simplex. -/
def stationaryProbabilityLaws : Set (ProbabilityMeasure ℝ) :=
  {nu | F.constraintKernel ∘ₘ (nu : Measure ℝ) = (nu : Measure ℝ)}

theorem stationaryProbabilityLaws_eq_carrierRange :
    F.stationaryProbabilityLaws = range F.barycenter := by
  ext nu
  exact F.constraintKernel_stationary_iff nu

/-- An extremal stationary law.  For Markov kernels this is the convex form of ergodicity. -/
def IsExtremalStationaryLaw (nu : ProbabilityMeasure ℝ) : Prop :=
  IsExtremeProbabilityLaw F.stationaryProbabilityLaws nu

/-- The extremal stationary laws are exactly the `N`-extremal boundary leaves. -/
theorem extremalStationaryBoundary :
    {nu : ProbabilityMeasure ℝ | F.IsExtremalStationaryLaw nu} = range F.leaf := by
  rw [show {nu : ProbabilityMeasure ℝ | F.IsExtremalStationaryLaw nu} =
      {nu : ProbabilityMeasure ℝ |
        IsExtremeProbabilityLaw (range F.barycenter) nu} by
    ext nu
    simp only [IsExtremalStationaryLaw, F.stationaryProbabilityLaws_eq_carrierRange]]
  exact F.extremeBoundary_carrierRange

/-- The extremal stationary boundary is closed. -/
theorem isClosed_extremalStationaryBoundary :
    IsClosed {nu : ProbabilityMeasure ℝ | F.IsExtremalStationaryLaw nu} := by
  rw [F.extremalStationaryBoundary]
  exact F.isClosed_range_leaf

end NevanlinnaBoundaryFamily

end

end GaloisForLFunctions.HTGeometry
