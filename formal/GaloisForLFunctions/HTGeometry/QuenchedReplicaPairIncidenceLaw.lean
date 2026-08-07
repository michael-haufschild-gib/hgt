import GaloisForLFunctions.HTGeometry.QuenchedReplicaIncidenceCovarianceLaw

/-!
# Quenched replica pair-incidence cut law

The covariance collision controlling complete circuit capture is exactly a
double-source pair action after compression to the occupied replica target
image.  Every measurable return relation therefore splits this action once
into return-near and return-far mass.  Source points are never quotiented,
duplicate target labels are invisible, and adjoining an exact-return zero
residual at positive replica order changes neither kernel nor bound.
-/

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

noncomputable def finiteCoordinateCovariance
    {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) (a : X → ι → ℂ) : Matrix ι ι ℂ :=
  fun i j => ∫ x, star (a x i) * a x j ∂μ

noncomputable def finiteCoordinatePairKernel
    {X ι : Type*} [Fintype ι]
    (a : X → ι → ℂ) (p : X × X) : ℝ :=
  ‖∑ i, star (a p.1 i) * a p.2 i‖ ^ 2

theorem finiteCoordinatePairKernel_integrable
    {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) [SFinite μ] (a : X → ι → ℂ)
    (hmeas : ∀ i, AEStronglyMeasurable (fun x => a x i) μ)
    (hsq : ∀ i, Integrable (fun x => ‖a x i‖ ^ 2) μ) :
    Integrable (finiteCoordinatePairKernel a) (μ.prod μ) := by
  have hL2 (i : ι) : MemLp (fun x => a x i) 2 μ :=
    (memLp_two_iff_integrable_sq_norm (hmeas i)).2 (hsq i)
  have hcov (i j : ι) :
      Integrable (fun x => star (a x i) * a x j) μ := by
    change Integrable ((star (fun x => a x i)) * (fun x => a x j)) μ
    exact (hL2 i).star.integrable_mul (hL2 j)
  have hcovStar (i j : ι) :
      Integrable (fun x => a x i * star (a x j)) μ := by
    change Integrable ((fun x => a x i) * star (fun x => a x j)) μ
    exact (hL2 i).integrable_mul (hL2 j).star
  have hpair (i j : ι) :
      Integrable (fun p : X × X =>
        (a p.1 i * star (a p.1 j)) *
          (star (a p.2 i) * a p.2 j)) (μ.prod μ) :=
    (hcovStar i j).mul_prod (hcov i j)
  have hsum : Integrable (fun p : X × X => ∑ i, ∑ j,
      (a p.1 i * star (a p.1 j)) *
        (star (a p.2 i) * a p.2 j)) (μ.prod μ) :=
    integrable_finsetSum Finset.univ fun i _ =>
      integrable_finsetSum Finset.univ fun j _ => hpair i j
  have hkernel (p : X × X) :
      star (∑ i, star (a p.1 i) * a p.2 i) *
          (∑ i, star (a p.1 i) * a p.2 i) =
        ∑ i, ∑ j,
          (a p.1 i * star (a p.1 j)) *
            (star (a p.2 i) * a p.2 j) := by
    rw [star_sum]
    simp only [star_mul, star_star]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hcplx : Integrable (fun p : X × X =>
      star (∑ i, star (a p.1 i) * a p.2 i) *
        (∑ i, star (a p.1 i) * a p.2 i)) (μ.prod μ) :=
    hsum.congr (Filter.Eventually.of_forall fun p => (hkernel p).symm)
  apply hcplx.re.congr
  exact Filter.Eventually.of_forall fun p => by
    let z : ℂ := ∑ i, star (a p.1 i) * a p.2 i
    change (star z * z).re = ‖z‖ ^ 2
    rw [show star z = conj z from rfl,
      ← Complex.normSq_eq_conj_mul_self]
    norm_cast
    exact Complex.normSq_eq_norm_sq z

theorem finiteCoordinate_covarianceCollision_eq_pairKernel
    {X ι : Type*} [MeasurableSpace X] [Fintype ι]
    (μ : Measure X) [SFinite μ] (a : X → ι → ℂ)
    (hmeas : ∀ i, AEStronglyMeasurable (fun x => a x i) μ)
    (hsq : ∀ i, Integrable (fun x => ‖a x i‖ ^ 2) μ) :
    (∑ i, ∑ j, ‖(finiteCoordinateCovariance μ a) i j‖ ^ 2) =
      ∫ p, finiteCoordinatePairKernel a p ∂(μ.prod μ) := by
  unfold finiteCoordinateCovariance finiteCoordinatePairKernel
  have hc :
      ((∑ i, ∑ j, ‖∫ x, star (a x i) * a x j ∂μ‖ ^ 2 : ℝ) : ℂ) =
        ∫ p, ((‖∑ i, star (a p.1 i) * a p.2 i‖ ^ 2 : ℝ) : ℂ)
          ∂(μ.prod μ) := by
    have hnorm (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = star z * z := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
      rfl
    have hL2 (i : ι) : MemLp (fun x => a x i) 2 μ :=
      (memLp_two_iff_integrable_sq_norm (hmeas i)).2 (hsq i)
    have hcov (i j : ι) :
        Integrable (fun x => star (a x i) * a x j) μ := by
      change Integrable
        ((star (fun x => a x i)) * (fun x => a x j)) μ
      exact (hL2 i).star.integrable_mul (hL2 j)
    have hcovStar (i j : ι) :
        Integrable (fun x => a x i * star (a x j)) μ := by
      change Integrable
        ((fun x => a x i) * star (fun x => a x j)) μ
      exact (hL2 i).integrable_mul (hL2 j).star
    have hpair (i j : ι) :
        Integrable (fun p : X × X =>
          (a p.1 i * star (a p.1 j)) *
            (star (a p.2 i) * a p.2 j)) (μ.prod μ) :=
      (hcovStar i j).mul_prod (hcov i j)
    have hterm (i j : ι) :
        star (∫ x, star (a x i) * a x j ∂μ) *
            (∫ x, star (a x i) * a x j ∂μ) =
          ∫ p : X × X,
            (a p.1 i * star (a p.1 j)) *
              (star (a p.2 i) * a p.2 j) ∂(μ.prod μ) := by
      change
        conj (∫ x, conj (a x i) * a x j ∂μ) *
            (∫ x, conj (a x i) * a x j ∂μ) = _
      calc
        conj (∫ x, conj (a x i) * a x j ∂μ) *
              (∫ x, conj (a x i) * a x j ∂μ) =
            (∫ x, conj (conj (a x i) * a x j) ∂μ) *
              (∫ x, conj (a x i) * a x j ∂μ) := by
                rw [integral_conj]
        _ = ∫ p : X × X,
            conj (conj (a p.1 i) * a p.1 j) *
              (conj (a p.2 i) * a p.2 j) ∂(μ.prod μ) := by
                exact (integral_prod_mul
                  (μ := μ) (ν := μ)
                  (fun x => conj (conj (a x i) * a x j))
                  (fun x => conj (a x i) * a x j)).symm
        _ = _ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun p => by
            simp only [map_mul, star_star, starRingEnd_apply]
    have hkernel (p : X × X) :
        star (∑ i, star (a p.1 i) * a p.2 i) *
            (∑ i, star (a p.1 i) * a p.2 i) =
          ∑ i, ∑ j,
            (a p.1 i * star (a p.1 j)) *
              (star (a p.2 i) * a p.2 j) := by
      rw [star_sum]
      simp only [star_mul, star_star]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp_rw [Complex.ofReal_sum, hnorm]
    calc
      ∑ i, ∑ j,
          star (∫ x, star (a x i) * a x j ∂μ) *
            (∫ x, star (a x i) * a x j ∂μ) =
          ∑ i, ∑ j, ∫ p : X × X,
            (a p.1 i * star (a p.1 j)) *
              (star (a p.2 i) * a p.2 j) ∂(μ.prod μ) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact hterm i j
      _ = ∫ p : X × X, ∑ i, ∑ j,
            (a p.1 i * star (a p.1 j)) *
              (star (a p.2 i) * a p.2 j) ∂(μ.prod μ) := by
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro i _
          rw [integral_finsetSum]
          exact fun j _ => hpair i j
        · intro i _
          exact integrable_finsetSum Finset.univ fun j _ => hpair i j
      _ = ∫ p : X × X,
          star (∑ i, star (a p.1 i) * a p.2 i) *
            (∑ i, star (a p.1 i) * a p.2 i) ∂(μ.prod μ) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun p => (hkernel p).symm
  have ho :
      (∫ p, ((‖∑ i, star (a p.1 i) * a p.2 i‖ ^ 2 : ℝ) : ℂ)
          ∂(μ.prod μ)) =
        ((∫ p, ‖∑ i, star (a p.1 i) * a p.2 i‖ ^ 2
          ∂(μ.prod μ) : ℝ) : ℂ) :=
    @integral_ofReal (X × X) _ (μ.prod μ) ℂ _
      (fun p => ‖∑ i, star (a p.1 i) * a p.2 i‖ ^ 2)
  exact Complex.ofReal_injective (hc.trans ho)

/-- Pair-overlap kernel after compressing both replica endpoints to one subspace. -/
noncomputable def replicaSubspacePairIncidenceKernel
    {X α : Type*} [Fintype α] (r : ℕ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin r → α)))
    (state : X → α → ℂ) (p : X × X) : ℝ :=
  finiteCoordinatePairKernel
    (fun x i => replicaSubspaceCoordinate r S (state x) i) p

/-- Pair-overlap kernel compressed to the occupied replica target image. -/
noncomputable def replicaTargetPairIncidenceKernel
    {X C α : Type*} [Fintype α] (r : ℕ)
    (target : C → α → ℂ) (state : X → α → ℂ) (p : X × X) : ℝ :=
  replicaSubspacePairIncidenceKernel r (replicaTargetSpan r target) state p

theorem replicaTargetPairIncidenceKernel_eq_of_span_eq
    {X C D α : Type*} [Fintype α] (r : ℕ)
    (target : C → α → ℂ) (target' : D → α → ℂ)
    (state : X → α → ℂ)
    (hspan : replicaTargetSpan r target = replicaTargetSpan r target') :
    replicaTargetPairIncidenceKernel r target state =
      replicaTargetPairIncidenceKernel r target' state := by
  unfold replicaTargetPairIncidenceKernel
  rw [hspan]

theorem replicaTargetPairIncidenceKernel_duplicated
    {X C α : Type*} [Fintype α] (r : ℕ)
    (target : C → α → ℂ) (state : X → α → ℂ) :
    replicaTargetPairIncidenceKernel r (duplicatedReplicaTarget target) state =
      replicaTargetPairIncidenceKernel r target state :=
  replicaTargetPairIncidenceKernel_eq_of_span_eq r
    (duplicatedReplicaTarget target) target state
      (replicaTargetSpan_duplicated r target)

theorem replicaTargetPairIncidenceKernel_withZero
    {X C α : Type*} [Fintype α] {r : ℕ} (hr : 0 < r)
    (target : C → α → ℂ) (state : X → α → ℂ) :
    replicaTargetPairIncidenceKernel r (replicaTargetWithZero target) state =
      replicaTargetPairIncidenceKernel r target state :=
  replicaTargetPairIncidenceKernel_eq_of_span_eq r
    (replicaTargetWithZero target) target state
      (replicaTargetSpan_withZero hr target)

theorem integrable_replicaSubspacePairIncidenceKernel
    {X α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) [SFinite μ] (r : ℕ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin r → α)))
    (state : X → α → ℂ)
    (hmeas : ∀ i, AEStronglyMeasurable
      (fun x => replicaSubspaceCoordinate r S (state x) i) μ)
    (hsq : ∀ i, Integrable
      (fun x => ‖replicaSubspaceCoordinate r S (state x) i‖ ^ 2) μ) :
    Integrable (replicaSubspacePairIncidenceKernel r S state) (μ.prod μ) := by
  exact finiteCoordinatePairKernel_integrable μ
    (fun x i => replicaSubspaceCoordinate r S (state x) i) hmeas hsq

theorem replicaSubspaceIncidenceCollision_eq_integral_pairKernel
    {X α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) [SFinite μ] (r : ℕ)
    (S : Submodule ℂ (EuclideanSpace ℂ (Fin r → α)))
    (state : X → α → ℂ)
    (hmeas : ∀ i, AEStronglyMeasurable
      (fun x => replicaSubspaceCoordinate r S (state x) i) μ)
    (hsq : ∀ i, Integrable
      (fun x => ‖replicaSubspaceCoordinate r S (state x) i‖ ^ 2) μ) :
    replicaSubspaceIncidenceCollision μ r S state =
      ∫ p, replicaSubspacePairIncidenceKernel r S state p ∂(μ.prod μ) := by
  simpa [replicaSubspaceIncidenceCollision,
    replicaSubspaceIncidenceCovariance, replicaSubspacePairIncidenceKernel,
    finiteCoordinateCovariance] using
    finiteCoordinate_covarianceCollision_eq_pairKernel μ
      (fun x i => replicaSubspaceCoordinate r S (state x) i) hmeas hsq

theorem replicaTargetIncidenceCollision_eq_integral_pairKernel
    {X C α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) [SFinite μ] (r : ℕ)
    (target : C → α → ℂ) (state : X → α → ℂ)
    (hmeas : ∀ i, AEStronglyMeasurable
      (fun x => replicaTargetCoordinate r target (state x) i) μ)
    (hsq : ∀ i, Integrable
      (fun x => ‖replicaTargetCoordinate r target (state x) i‖ ^ 2) μ) :
    replicaTargetIncidenceCollision μ r target state =
      ∫ p, replicaTargetPairIncidenceKernel r target state p ∂(μ.prod μ) := by
  exact replicaSubspaceIncidenceCollision_eq_integral_pairKernel μ r
    (replicaTargetSpan r target) state hmeas hsq

theorem integral_replicaTargetPairIncidenceKernel_add_compl
    {X C α : Type*} [MeasurableSpace X] [Fintype α]
    (μ : Measure X) [SFinite μ] (r : ℕ)
    (target : C → α → ℂ) (state : X → α → ℂ)
    (hmeas : ∀ i, AEStronglyMeasurable
      (fun x => replicaTargetCoordinate r target (state x) i) μ)
    (hsq : ∀ i, Integrable
      (fun x => ‖replicaTargetCoordinate r target (state x) i‖ ^ 2) μ)
    (R : Set (X × X)) (hR : MeasurableSet R) :
    (∫ p in R, replicaTargetPairIncidenceKernel r target state p ∂(μ.prod μ)) +
        (∫ p in Rᶜ, replicaTargetPairIncidenceKernel r target state p ∂(μ.prod μ)) =
      ∫ p, replicaTargetPairIncidenceKernel r target state p ∂(μ.prod μ) := by
  apply integral_add_compl hR
  exact integrable_replicaSubspacePairIncidenceKernel μ r
    (replicaTargetSpan r target) state hmeas hsq

/-- Complete shortcut mass is bounded by one return-near/far decomposition of
the occupied-image compressed pair action. -/
theorem quenchedReplica_pairIncidenceCut_bound
    {X C α : Type*} [MeasurableSpace X] [Fintype C] [Fintype α]
    (μ : Measure X) [IsFiniteMeasure μ]
    {r : ℕ} (hr : 0 < r)
    (target : C → α → ℂ) (state : X → α → ℂ)
    (htarget : ∀ c, finiteComplexInner (target c) (target c) = 1)
    (threshold : ℝ) (hthreshold : 0 < threshold)
    (hmeas : ∀ i, AEStronglyMeasurable
      (fun x => replicaTargetCoordinate r target (state x) i) μ)
    (hcoord : ∀ i, Integrable
      (fun x => ‖replicaTargetCoordinate r target (state x) i‖ ^ 2) μ)
    (R : Set (X × X)) (hR : MeasurableSet R) :
    (μ.real {x | ∃ c,
        threshold ≤ finitePureStateFidelity (state x) (target c)} *
      threshold ^ r) ^ 2 ≤
      (replicaTargetHilbertNumber r target : ℝ) *
        ((∫ p in R,
            replicaTargetPairIncidenceKernel r target state p ∂(μ.prod μ)) +
          ∫ p in Rᶜ,
            replicaTargetPairIncidenceKernel r target state p ∂(μ.prod μ)) := by
  calc
    _ ≤ (replicaTargetHilbertNumber r target : ℝ) *
        replicaTargetIncidenceCollision μ r target state :=
      quenchedReplica_incidenceCovariance_bound μ hr target state
        htarget threshold hthreshold hcoord
    _ = _ := by
      rw [replicaTargetIncidenceCollision_eq_integral_pairKernel
        μ r target state hmeas hcoord]
      rw [← integral_replicaTargetPairIncidenceKernel_add_compl
        μ r target state hmeas hcoord R hR]

end

end GaloisForLFunctions.HTGeometry
