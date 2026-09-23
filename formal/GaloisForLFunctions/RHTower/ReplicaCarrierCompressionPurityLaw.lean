import GaloisForLFunctions.RHTower.TotalDegreePolynomialCircuitCarrierFirstEntryLaw

/-!
# Replica-carrier compression is dominated by full replica purity

Pointwise projection can increase pair overlap, so pointwise comparison is
false.  After source averaging, however, carrier action is Hilbert--Schmidt
energy of a positive covariance compression.  Extending carrier coordinates
to a full orthonormal basis shows that its covariance matrix is a principal
block.  Sum-of-squares energy therefore cannot increase.

Consequently every return-excised carrier action is bounded by full replica
purity on surviving source sheets:

`∬ finitePureStateFidelity (state x) (state y) ^ r`.

This removes target cardinality, carrier orientation, and circuit geometry
from quenched action estimation.  Complete circuit class remains only through
explicit carrier rank in coarea law.
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem finiteCoordinateCovarianceCollision_le_of_injective
    {X ι κ : Type*} [MeasurableSpace X] [Fintype ι] [Fintype κ]
    (μ : Measure X) (a : X → κ → ℂ) (J : ι → κ)
    (hJ : Function.Injective J) :
    (∑ i, ∑ j,
        ‖finiteCoordinateCovariance μ (fun x i => a x (J i)) i j‖ ^ (2 : ℕ)) ≤
      ∑ p, ∑ q, ‖finiteCoordinateCovariance μ a p q‖ ^ (2 : ℕ) := by
  classical
  have himage (g : κ → ℝ) (hg : ∀ q, 0 ≤ g q) :
      (∑ i, g (J i)) ≤ ∑ q, g q := by
    rw [← Finset.sum_image]
    · exact Finset.sum_le_univ_sum_of_nonneg hg
    · intro i _ j _ hij
      exact hJ hij
  have hcov : ∀ i j,
      finiteCoordinateCovariance μ (fun x i => a x (J i)) i j =
        finiteCoordinateCovariance μ a (J i) (J j) := by
    intro i j
    rfl
  simp_rw [hcov]
  calc
    (∑ i, ∑ j, ‖finiteCoordinateCovariance μ a (J i) (J j)‖ ^ (2 : ℕ)) ≤
        ∑ i, ∑ q, ‖finiteCoordinateCovariance μ a (J i) q‖ ^ (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro i _
      exact himage
        (fun q => ‖finiteCoordinateCovariance μ a (J i) q‖ ^ (2 : ℕ))
        (fun q => sq_nonneg _)
    _ ≤ ∑ p, ∑ q, ‖finiteCoordinateCovariance μ a p q‖ ^ (2 : ℕ) := by
      exact himage
        (fun p => ∑ q, ‖finiteCoordinateCovariance μ a p q‖ ^ (2 : ℕ))
        (fun p => Finset.sum_nonneg fun q _ => sq_nonneg _)

theorem finiteCoordinatePairKernel_orthonormalBasis
    {X κ E : Type*} [Fintype κ]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (b : OrthonormalBasis κ ℂ E) (v : X → E) (p : X × X) :
    finiteCoordinatePairKernel (fun x i => inner ℂ (b i) (v x)) p =
      ‖inner ℂ (v p.1) (v p.2)‖ ^ (2 : ℕ) := by
  unfold finiteCoordinatePairKernel
  have hsum :
    (∑ i, star (inner ℂ (b i) (v p.1)) *
        inner ℂ (b i) (v p.2)) =
        inner ℂ (v p.1) (v p.2) := by
    calc
      (∑ i, star (inner ℂ (b i) (v p.1)) *
          inner ℂ (b i) (v p.2)) =
          ∑ i, inner ℂ (v p.1) (b i) * inner ℂ (b i) (v p.2) := by
        apply Finset.sum_congr rfl
        intro i _
        change (starRingEnd ℂ) (inner ℂ (b i) (v p.1)) *
          inner ℂ (b i) (v p.2) = _
        rw [inner_conj_symm]
      _ = inner ℂ (v p.1) (v p.2) :=
        b.sum_inner_mul_inner (v p.1) (v p.2)
  exact congrArg (fun z : ℂ => ‖z‖ ^ (2 : ℕ)) hsum

/-- Orthogonal compression cannot increase integrated covariance collision.
This is the carrier-independent reduction from circuit coarea to full replica
purity. -/
theorem replicaSubspaceIncidenceCollision_le_fullReplicaPairAction
    {X α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) [SFinite μ] (r : ℕ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin r → α)))
    (state : X → α → ℂ)
    (hmeas : ∀ u : EuclideanSpace ℂ (Fin r → α),
      AEStronglyMeasurable
        (fun x => inner ℂ u (finitePureTensorPowerEuclidean r (state x))) μ)
    (hsq : ∀ u : EuclideanSpace ℂ (Fin r → α),
      Integrable
        (fun x => ‖inner ℂ u
          (finitePureTensorPowerEuclidean r (state x))‖ ^ (2 : ℕ)) μ) :
    replicaSubspaceIncidenceCollision μ r S state ≤
      ∫ p : X × X,
        ‖inner ℂ
          (finitePureTensorPowerEuclidean r (state p.1))
          (finitePureTensorPowerEuclidean r (state p.2))‖ ^ (2 : ℕ) ∂(μ.prod μ) := by
  classical
  let bS := replicaSubspaceOrthonormalBasis r S
  let vS : Fin (Module.finrank ℂ S) →
      EuclideanSpace ℂ (Fin r → α) :=
    fun i => ((bS i : S) : EuclideanSpace ℂ (Fin r → α))
  have hvS : Orthonormal ℂ vS := by
    simpa [vS, Function.comp_def] using
      bS.orthonormal.comp_linearIsometry S.subtypeₗᵢ
  have hvRange : Orthonormal ℂ
      ((↑) : Set.range vS → EuclideanSpace ℂ (Fin r → α)) := by
    rw [orthonormal_subtype_range hvS.linearIndependent.injective]
    exact hvS
  obtain ⟨u, b, hsub, hb⟩ := hvRange.exists_orthonormalBasis_extension
  let J : Fin (Module.finrank ℂ S) → u := fun i =>
    ⟨vS i, hsub ⟨i, rfl⟩⟩
  have hJ : Function.Injective J := by
    intro i j hij
    apply hvS.linearIndependent.injective
    exact congrArg
      (fun z : u => (z : EuclideanSpace ℂ (Fin r → α))) hij
  let v : X → EuclideanSpace ℂ (Fin r → α) :=
    fun x => finitePureTensorPowerEuclidean r (state x)
  let a : X → u → ℂ := fun x z => inner ℂ (b z) (v x)
  have hbJ : ∀ i, b (J i) = vS i := by
    intro i
    exact congrFun hb (J i)
  have haJ : ∀ x i,
      a x (J i) = replicaSubspaceCoordinate r S (state x) i := by
    intro x i
    rw [show a x (J i) = inner ℂ (b (J i)) (v x) by rfl, hbJ]
    rfl
  have hcov : ∀ i j,
      replicaSubspaceIncidenceCovariance μ r S state i j =
        finiteCoordinateCovariance μ (fun x i => a x (J i)) i j := by
    intro i j
    unfold replicaSubspaceIncidenceCovariance finiteCoordinateCovariance
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by
      change star (replicaSubspaceCoordinate r S (state x) i) *
          replicaSubspaceCoordinate r S (state x) j =
        star (a x (J i)) * a x (J j)
      rw [haJ x i, haJ x j]
  calc
    replicaSubspaceIncidenceCollision μ r S state =
        ∑ i, ∑ j,
          ‖finiteCoordinateCovariance μ (fun x i => a x (J i)) i j‖ ^ (2 : ℕ) := by
      unfold replicaSubspaceIncidenceCollision
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hcov]
    _ ≤ ∑ p, ∑ q, ‖finiteCoordinateCovariance μ a p q‖ ^ (2 : ℕ) :=
      finiteCoordinateCovarianceCollision_le_of_injective μ a J hJ
    _ = ∫ p, finiteCoordinatePairKernel a p ∂(μ.prod μ) :=
      finiteCoordinate_covarianceCollision_eq_pairKernel μ a
        (fun z => hmeas (b z)) (fun z => hsq (b z))
    _ = ∫ p : X × X,
        ‖inner ℂ
          (finitePureTensorPowerEuclidean r (state p.1))
          (finitePureTensorPowerEuclidean r (state p.2))‖ ^ (2 : ℕ) ∂(μ.prod μ) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun p => by
        exact finiteCoordinatePairKernel_orthonormalBasis b v p

/-- Return removal and carrier compression both decrease covariance collision.
The surviving action is controlled by full-state replica purity, independently
of carrier orientation or target cardinality. -/
theorem returnExcisedReplicaCarrierIncidenceAction_le_fullReplicaPurity
    {X α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) [SFinite μ] (r : ℕ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin r → α)))
    (state : X → α → ℂ) (returnSet : Set X)
    (hmeas : ∀ u : EuclideanSpace ℂ (Fin r → α),
      AEStronglyMeasurable
        (fun x => inner ℂ u (finitePureTensorPowerEuclidean r (state x)))
        (μ.restrict returnSetᶜ))
    (hsq : ∀ u : EuclideanSpace ℂ (Fin r → α),
      Integrable
        (fun x => ‖inner ℂ u
          (finitePureTensorPowerEuclidean r (state x))‖ ^ (2 : ℕ))
        (μ.restrict returnSetᶜ)) :
    returnExcisedReplicaCarrierIncidenceAction μ r S state returnSet ≤
      ∫ p : X × X,
        finitePureStateFidelity (state p.1) (state p.2) ^ r
        ∂((μ.restrict returnSetᶜ).prod (μ.restrict returnSetᶜ)) := by
  let ν := μ.restrict returnSetᶜ
  have hcollision :
      returnExcisedReplicaCarrierIncidenceAction μ r S state returnSet =
        replicaSubspaceIncidenceCollision ν r S state := by
    rw [returnExcisedReplicaCarrierIncidenceAction,
      returnExcisedFiniteCoordinateIncidenceAction_eq_restrictProduct]
    symm
    exact replicaSubspaceIncidenceCollision_eq_integral_pairKernel
      ν r S state
        (fun i => (hmeas
          ((replicaSubspaceOrthonormalBasis r S i : S) :
            EuclideanSpace ℂ (Fin r → α))))
        (fun i => (hsq
          ((replicaSubspaceOrthonormalBasis r S i : S) :
            EuclideanSpace ℂ (Fin r → α))))
  rw [hcollision]
  refine (replicaSubspaceIncidenceCollision_le_fullReplicaPairAction
    ν r S state hmeas hsq).trans_eq ?_
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun p =>
    (finitePureStateFidelity_pow_eq_replica_inner_norm_sq
      r (state p.1) (state p.2)).symm

end

end GaloisForLFunctions.HTGeometry
