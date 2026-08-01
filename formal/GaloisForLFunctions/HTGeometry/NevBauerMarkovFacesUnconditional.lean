import GaloisForLFunctions.HTGeometry.NevBauerUnconditional
import GaloisForLFunctions.HTGeometry.NevanlinnaAffineGeometry
import GaloisForLFunctions.HTGeometry.NevanlinnaBoundaryFaceLattice
import GaloisForLFunctions.HTGeometry.NevanlinnaKernelErgodicity

/-!
# The Nevanlinna Markov projector and face lattice, unconditionally

The constructed `nevExtremalFamily` removes the abstract-family input from the constraint-kernel,
stationary-boundary, ergodicity, and closed-face results.  Every theorem below therefore assumes
only positivity, indeterminacy through boundedness of the moment kernel, and normalization of the
zeroth moment.
-/

open scoped BoundedContinuousFunction ENNReal OnePoint
open MeasureTheory OnePoint ProbabilityTheory Set

namespace HTGeometry

noncomputable section

variable {s : ℕ → ℝ}

/-- Reading the projective label after barycentring the constructed boundary recovers the complete
parameter law. -/
theorem nevProjectiveLaw_barycenter (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) (eta : ProbabilityMeasure (OnePoint ℝ)) :
    (nevBoundaryFamily h h0b h0).projectiveLaw
        ((nevBoundaryFamily h h0b h0).barycenter eta) = eta :=
  (nevBoundaryFamily h h0b h0).projectiveLaw_barycenter eta

/-- The measure-side constraint projector of the constructed boundary is continuous. -/
theorem nevCarrierProjector_continuous (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) :
    Continuous (nevBoundaryFamily h h0b h0).carrierProjector :=
  (nevBoundaryFamily h h0b h0).continuous_carrierProjector

/-- The constructed carrier projector is affine on genuine probability mixtures. -/
theorem nevCarrierProjector_probabilityMixture (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1)
    (t : ℝ≥0∞) (ht : t ≤ 1) (mu nu : ProbabilityMeasure ℝ) :
    (nevBoundaryFamily h h0b h0).carrierProjector
        (GaloisForLFunctions.HTGeometry.probabilityMixture t ht mu nu) =
      GaloisForLFunctions.HTGeometry.probabilityMixture t ht
        ((nevBoundaryFamily h h0b h0).carrierProjector mu)
        ((nevBoundaryFamily h h0b h0).carrierProjector nu) :=
  (nevBoundaryFamily h h0b h0).carrierProjector_probabilityMixture t ht mu nu

/-- The constructed carrier projector is idempotent on all real probability laws. -/
theorem nevCarrierProjector_idempotent (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) (nu : ProbabilityMeasure ℝ) :
    (nevBoundaryFamily h h0b h0).carrierProjector
        ((nevBoundaryFamily h h0b h0).carrierProjector nu) =
      (nevBoundaryFamily h h0b h0).carrierProjector nu :=
  (nevBoundaryFamily h h0b h0).carrierProjector_idempotent nu

/-- The projector range is exactly the constructed boundary simplex. -/
theorem nevCarrierProjector_range (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) :
    Set.range (nevBoundaryFamily h h0b h0).carrierProjector =
      Set.range (nevBoundaryFamily h h0b h0).barycenter :=
  (nevBoundaryFamily h h0b h0).range_carrierProjector

/-- A real probability law is fixed exactly when it belongs to the constructed boundary simplex. -/
theorem nevCarrierProjector_fixed_iff (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) (nu : ProbabilityMeasure ℝ) :
    (nevBoundaryFamily h h0b h0).carrierProjector nu = nu ↔
      nu ∈ Set.range (nevBoundaryFamily h h0b h0).barycenter :=
  (nevBoundaryFamily h h0b h0).carrierProjector_eq_self_iff nu

/-- One projection of any real probability law lands in the exact complete moment fiber. -/
theorem nevCarrierProjector_hasHamburgerMoments (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) (nu : ProbabilityMeasure ℝ) :
    GaloisForLFunctions.HTGeometry.HasHamburgerMoments s
      ((nevBoundaryFamily h h0b h0).carrierProjector nu : Measure ℝ) :=
  (nevBoundaryFamily h h0b h0).carrierProjector_hasHamburgerMoments nu

/-- Kernel action and the measure-side projector agree exactly. -/
theorem nevConstraintKernel_comp_probability (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) (nu : ProbabilityMeasure ℝ) :
    (nevBoundaryFamily h h0b h0).constraintKernel ∘ₘ (nu : Measure ℝ) =
      ((nevBoundaryFamily h h0b h0).carrierProjector nu : Measure ℝ) :=
  (nevBoundaryFamily h h0b h0).constraintKernel_comp_probability nu

/-- The constructed pointwise Markov kernel is idempotent under kernel composition. -/
theorem nevConstraintKernel_idempotent (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) :
    (nevBoundaryFamily h h0b h0).constraintKernel ∘ₖ
        (nevBoundaryFamily h h0b h0).constraintKernel =
      (nevBoundaryFamily h h0b h0).constraintKernel :=
  (nevBoundaryFamily h h0b h0).constraintKernel_comp_self

/-- Stationary laws of the constructed kernel are exactly its boundary barycentres. -/
theorem nevConstraintKernel_stationary_iff (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) (nu : ProbabilityMeasure ℝ) :
    (nevBoundaryFamily h h0b h0).constraintKernel ∘ₘ (nu : Measure ℝ) =
        (nu : Measure ℝ) ↔
      nu ∈ Set.range (nevBoundaryFamily h h0b h0).barycenter :=
  (nevBoundaryFamily h h0b h0).constraintKernel_stationary_iff nu

/-- Every monomial is sent in one step to its prescribed moment. -/
theorem nevConstraintKernel_integral_pow (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) (n : ℕ) (x : ℝ) :
    ∫ y, y ^ n ∂((nevBoundaryFamily h h0b h0).constraintKernel x) = s n :=
  (nevBoundaryFamily h h0b h0).integral_pow_constraintKernel n x

/-- The constructed constraint kernel is weak Feller. -/
theorem nevConstraintKernel_isWeakFeller (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) :
    GaloisForLFunctions.HTGeometry.IsWeakFellerKernel
      (nevBoundaryFamily h h0b h0).constraintKernel :=
  (nevBoundaryFamily h h0b h0).constraintKernel_isWeakFeller

/-- The dual Markov operator preserves one. -/
theorem nevConstraintMarkovOperator_one (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) :
    (nevBoundaryFamily h h0b h0).constraintMarkovOperator (1 : ℝ →ᵇ ℝ) = 1 :=
  (nevBoundaryFamily h h0b h0).constraintMarkovOperator_one

/-- The dual Markov operator preserves nonnegativity. -/
theorem nevConstraintMarkovOperator_nonneg (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) {f : ℝ →ᵇ ℝ}
    (hf : ∀ x, 0 ≤ f x) :
    ∀ x, 0 ≤ (nevBoundaryFamily h h0b h0).constraintMarkovOperator f x :=
  (nevBoundaryFamily h h0b h0).constraintMarkovOperator_nonneg hf

/-- The dual Markov operator contracts the supremum norm. -/
theorem nevConstraintMarkovOperator_norm_le (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) (f : ℝ →ᵇ ℝ) :
    ‖(nevBoundaryFamily h h0b h0).constraintMarkovOperator f‖ ≤ ‖f‖ :=
  (nevBoundaryFamily h h0b h0).norm_constraintMarkovOperator_le f

/-- The dual Markov operator is idempotent. -/
theorem nevConstraintMarkovOperator_idempotent (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) (f : ℝ →ᵇ ℝ) :
    (nevBoundaryFamily h h0b h0).constraintMarkovOperator
        ((nevBoundaryFamily h h0b h0).constraintMarkovOperator f) =
      (nevBoundaryFamily h h0b h0).constraintMarkovOperator f :=
  (nevBoundaryFamily h h0b h0).constraintMarkovOperator_idempotent f

/-- Every closed projective carrier gives a weakly closed boundary face. -/
theorem nevBoundaryCarrierFace_isClosed (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1)
    (K : Set (OnePoint ℝ)) (hK : IsClosed K) :
    IsClosed ((nevBoundaryFamily h h0b h0).boundaryCarrierFace K) :=
  (nevBoundaryFamily h h0b h0).boundaryCarrierFace_isClosed K hK

/-- Every projective carrier subset gives a genuine face of the constructed boundary simplex. -/
theorem nevBoundaryCarrierFace_isProbabilityLawFace (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) (K : Set (OnePoint ℝ)) :
    GaloisForLFunctions.HTGeometry.IsProbabilityLawFace
      ((nevBoundaryFamily h h0b h0).boundaryCarrierFace K)
      (Set.range (nevBoundaryFamily h h0b h0).barycenter) :=
  (nevBoundaryFamily h h0b h0).boundaryCarrierFace_isProbabilityLawFace K

/-- The constructed closed-face map is monotone. -/
theorem nevBoundaryCarrierFace_mono (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) {K L : Set (OnePoint ℝ)}
    (hKL : K ⊆ L) :
    (nevBoundaryFamily h h0b h0).boundaryCarrierFace K ⊆
      (nevBoundaryFamily h h0b h0).boundaryCarrierFace L :=
  (nevBoundaryFamily h h0b h0).boundaryCarrierFace_mono hKL

/-- The constructed closed-face map preserves binary intersections exactly. -/
theorem nevBoundaryCarrierFace_inter (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) (K L : Set (OnePoint ℝ)) :
    (nevBoundaryFamily h h0b h0).boundaryCarrierFace (K ∩ L) =
      (nevBoundaryFamily h h0b h0).boundaryCarrierFace K ∩
        (nevBoundaryFamily h h0b h0).boundaryCarrierFace L :=
  (nevBoundaryFamily h h0b h0).boundaryCarrierFace_inter K L

/-- On closed carriers, face inclusion reflects and preserves carrier inclusion. -/
theorem nevBoundaryCarrierFace_subset_iff (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1)
    {K L : Set (OnePoint ℝ)} (hK : IsClosed K) (hL : IsClosed L) :
    (nevBoundaryFamily h h0b h0).boundaryCarrierFace K ⊆
        (nevBoundaryFamily h h0b h0).boundaryCarrierFace L ↔
      K ⊆ L :=
  (nevBoundaryFamily h h0b h0).boundaryCarrierFace_subset_iff hK hL

/-- Every carrier in every constructed boundary face has the complete prescribed moments. -/
theorem nevBoundaryCarrierFace_hasHamburgerMoments (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1)
    {K : Set (OnePoint ℝ)} {nu : ProbabilityMeasure ℝ}
    (hnu : nu ∈ (nevBoundaryFamily h h0b h0).boundaryCarrierFace K) :
    GaloisForLFunctions.HTGeometry.HasHamburgerMoments s (nu : Measure ℝ) :=
  (nevBoundaryFamily h h0b h0).boundaryCarrierFace_hasHamburgerMoments hnu

/-- Stationary laws are exactly the constructed boundary simplex. -/
theorem nevStationaryProbabilityLaws_eq_carrierRange (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) :
    (nevBoundaryFamily h h0b h0).stationaryProbabilityLaws =
      Set.range (nevBoundaryFamily h h0b h0).barycenter :=
  (nevBoundaryFamily h h0b h0).stationaryProbabilityLaws_eq_carrierRange

/-- Invariant-set ergodic stationary laws are exactly the constructed N-extremal leaves. -/
theorem nevErgodicConstraintStationaryBoundary (h : PositiveMomentForm s)
    (h0b : BoundedKernel s 0) (h0 : s 0 = 1) :
    {nu : ProbabilityMeasure ℝ |
        (nevBoundaryFamily h h0b h0).IsErgodicConstraintStationaryLaw nu} =
      Set.range (nevBoundaryFamily h h0b h0).leaf :=
  (nevBoundaryFamily h h0b h0).ergodicConstraintStationaryBoundary

/-- For the constructed kernel, invariant-set ergodicity equals convex extremality among
stationary laws. -/
theorem nevErgodicConstraintStationaryLaw_iff_extremalStationaryLaw
    (h : PositiveMomentForm s) (h0b : BoundedKernel s 0) (h0 : s 0 = 1)
    (nu : ProbabilityMeasure ℝ) :
    (nevBoundaryFamily h h0b h0).IsErgodicConstraintStationaryLaw nu ↔
      (nevBoundaryFamily h h0b h0).IsExtremalStationaryLaw nu :=
  (nevBoundaryFamily h h0b h0).ergodicConstraintStationaryLaw_iff_extremalStationaryLaw nu

end

end HTGeometry
