import GaloisForLFunctions.HTGeometry.TemporalDimensionInteractionMultiplicationLaw
import GaloisForLFunctions.HTGeometry.RealFiniteAnalyticEscape

/-!
# Separable interaction multiplication of temporal dimension

The arbitrary joint perturbation in the temporal-dimension multiplication
law can be restricted to a single separable diagonal interaction. For every
pair of nonempty finite spectra and every positive budget, there are two
real diagonal factor observables whose product interaction:

* lies inside the requested operator-norm budget;
* destroys every nonzero balanced integer spectral relation;
* raises projective temporal dimension from at most the additive one-body
  bound to the full product dimension;
* preserves the dimension-free finite-time perturbation bound;
* forces every positive full-support replica collision mass to its
  permutation floor.

The proof treats every integer relation as a nonzero real multivariate
polynomial in the two factor observables. Countable real-analytic avoidance
finds one arbitrarily small factor pair escaping all relations at once.
-/

open Set Filter NormedSpace Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Tensor-sum energy plus one separable diagonal interaction. The two
factor observables are the restrictions of `p` to the two summands. -/
def separableInteractionEnergy
    {A B : Type*}
    (left : A → ℝ) (right : B → ℝ)
    (p : A ⊕ B → ℝ) :
    A × B → ℝ :=
  fun x =>
    left x.1 + right x.2 +
      p (Sum.inl x.1) * p (Sum.inr x.2)

/-- Evaluation of one nonzero balanced spectral character on a separably
coupled spectrum. -/
def separableSpectralRelation
    {A B : Type*} [Fintype A] [Fintype B]
    (left : A → ℝ) (right : B → ℝ)
    (j : {k : A × B → ℤ //
      SpectralCharacterBalanced k ∧ k ≠ 0})
    (p : A ⊕ B → ℝ) : ℝ :=
  ∑ x, (j.1 x : ℝ) *
    separableInteractionEnergy left right p x

/-- Polynomial representing one separable spectral relation. -/
def separableSpectralRelationPolynomial
    {A B : Type*} [Fintype A] [Fintype B]
    (left : A → ℝ) (right : B → ℝ)
    (j : {k : A × B → ℤ //
      SpectralCharacterBalanced k ∧ k ≠ 0}) :
    MvPolynomial (A ⊕ B) ℝ :=
  ∑ x, MvPolynomial.C (j.1 x : ℝ) *
    (MvPolynomial.C (left x.1 + right x.2) +
      MvPolynomial.X (Sum.inl x.1) *
        MvPolynomial.X (Sum.inr x.2))

/-- Polynomial evaluation is exactly the corresponding spectral
relation. -/
theorem eval_separableSpectralRelationPolynomial
    {A B : Type*} [Fintype A] [Fintype B]
    (left : A → ℝ) (right : B → ℝ)
    (j : {k : A × B → ℤ //
      SpectralCharacterBalanced k ∧ k ≠ 0})
    (p : A ⊕ B → ℝ) :
    MvPolynomial.eval p
        (separableSpectralRelationPolynomial left right j) =
      separableSpectralRelation left right j p := by
  simp [separableSpectralRelationPolynomial,
    separableSpectralRelation,
    separableInteractionEnergy]

/-- Two-coordinate witness used to show that every nonzero relation
polynomial is nontrivial in every neighborhood of zero. -/
def selectedSeparableParameter
    {A B : Type*} [DecidableEq A] [DecidableEq B]
    (x : A × B) (s : ℝ) : A ⊕ B → ℝ :=
  Pi.single (Sum.inl x.1) s +
    Pi.single (Sum.inr x.2) s

/-- A selected two-coordinate perturbation changes a relation by exactly
one nonzero bilinear coefficient. -/
theorem separableSpectralRelation_selected
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (left : A → ℝ) (right : B → ℝ)
    (j : {k : A × B → ℤ //
      SpectralCharacterBalanced k ∧ k ≠ 0})
    (x : A × B) (s : ℝ) :
    separableSpectralRelation left right j
        (selectedSeparableParameter x s) =
      separableSpectralRelation left right j 0 +
        (j.1 x : ℝ) * s ^ (2 : ℕ) := by
  classical
  unfold separableSpectralRelation
  unfold separableInteractionEnergy
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  · simp
  · rw [Fintype.sum_prod_type]
    simp [selectedSeparableParameter, Pi.single_apply]
    ring_nf
    simp

/-- Elementary norm control for the selected relation witness. -/
theorem norm_selectedSeparableParameter_le
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    (x : A × B) (s : ℝ) :
    ‖selectedSeparableParameter x s‖ ≤
      |s| + |s| := by
  classical
  unfold selectedSeparableParameter
  calc
    _ ≤ ‖(Pi.single (Sum.inl x.1) s :
            A ⊕ B → ℝ)‖ +
          ‖(Pi.single (Sum.inr x.2) s :
            A ⊕ B → ℝ)‖ :=
      norm_add_le _ _
    _ = |s| + |s| := by
      rw [Pi.norm_single, Pi.norm_single]
      simp

/-- Every separable spectral relation is globally real analytic in the two
factor observables. -/
theorem analyticOnNhd_separableSpectralRelation
    {A B : Type*} [Fintype A] [Fintype B]
    (left : A → ℝ) (right : B → ℝ)
    (j : {k : A × B → ℤ //
      SpectralCharacterBalanced k ∧ k ≠ 0}) :
    AnalyticOnNhd ℝ
      (separableSpectralRelation left right j)
      Set.univ := by
  intro p hp
  have hfun :
      separableSpectralRelation left right j =
        fun q => MvPolynomial.eval q
          (separableSpectralRelationPolynomial
            left right j) := by
    funext q
    exact
      (eval_separableSpectralRelationPolynomial
        left right j q).symm
  rw [hfun]
  exact
    (AnalyticOnNhd.eval_mvPolynomial
      (separableSpectralRelationPolynomial
        left right j)) p (Set.mem_univ p)

/-- **Separable interaction relation erasure.** Every pair of nonempty
finite spectra admits arbitrarily weak diagonal factor observables whose
single product interaction erases all nonzero projective spectral
relations. -/
theorem exists_smallSeparableInteraction_maximallyProjective
    {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B]
    [Nonempty A] [Nonempty B]
    (left : A → ℝ) (right : B → ℝ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ p : A ⊕ B → ℝ,
      MaximallyProjectiveEnergy
        (separableInteractionEnergy left right p) ∧
      (∀ x : A × B,
        |p (Sum.inl x.1) * p (Sum.inr x.2)| < δ) := by
  classical
  let ε : ℝ := min 1 δ
  have hε : 0 < ε := by
    exact lt_min zero_lt_one hδ
  let I :=
    {k : A × B → ℤ //
      SpectralCharacterBalanced k ∧ k ≠ 0}
  let U : Set (A ⊕ B → ℝ) :=
    Metric.ball 0 ε
  have hUopen : IsOpen U :=
    Metric.isOpen_ball
  have hUconnected : IsPreconnected U :=
    (convex_ball (0 : A ⊕ B → ℝ) ε).isPreconnected
  have hUnonempty : U.Nonempty := by
    refine ⟨0, ?_⟩
    simpa [U] using hε
  have hf :
      ∀ j : I,
        AnalyticOnNhd ℝ
          (separableSpectralRelation left right j) U := by
    intro j
    exact
      (analyticOnNhd_separableSpectralRelation
        left right j).mono (Set.subset_univ U)
  have hne :
      ∀ j : I,
        ∃ p ∈ U,
          separableSpectralRelation left right j p ≠ 0 := by
    intro j
    by_cases hzero :
        separableSpectralRelation left right j 0 = 0
    · have hex : ∃ x, j.1 x ≠ 0 := by
        by_contra h
        push Not at h
        exact j.property.2 (funext h)
      obtain ⟨x, hx⟩ := hex
      let s : ℝ := ε / 4
      let p : A ⊕ B → ℝ :=
        selectedSeparableParameter x s
      have hpNorm :
          ‖p‖ < ε := by
        calc
          ‖p‖ ≤ |s| + |s| :=
            norm_selectedSeparableParameter_le x s
          _ = ε / 2 := by
            rw [abs_of_pos (by dsimp [s]; positivity)]
            ring
          _ < ε := by linarith
      refine ⟨p, ?_, ?_⟩
      · simpa [U, Metric.mem_ball, dist_zero_right] using hpNorm
      · rw [separableSpectralRelation_selected,
          hzero, zero_add]
        exact mul_ne_zero (by exact_mod_cast hx)
          (pow_ne_zero 2 (by dsimp [s]; positivity))
    · refine ⟨0, ?_, hzero⟩
      simpa [U] using hε
  obtain ⟨p, hpU, hpAll⟩ :=
    exists_forall_neZero_of_countable_analyticOnNhd_real_local
      (fun j : I =>
        separableSpectralRelation left right j)
      U hUopen hUconnected hUnonempty hf hne
  have hpNorm : ‖p‖ < ε := by
    simpa [U, Metric.mem_ball, dist_zero_right] using hpU
  have hpCoordinate :
      ∀ z, |p z| < ε := by
    intro z
    have h :=
      (pi_norm_lt_iff hε).mp hpNorm z
    simpa [Real.norm_eq_abs] using h
  refine ⟨p, ?_, ?_⟩
  · intro k hbalanced hsum
    by_contra hk
    let j : I := ⟨k, hbalanced, hk⟩
    apply hpAll j
    simpa [separableSpectralRelation,
      separableInteractionEnergy] using hsum
  · intro x
    rw [abs_mul]
    have ha := hpCoordinate (Sum.inl x.1)
    have hb := hpCoordinate (Sum.inr x.2)
    have hεone : ε ≤ 1 := min_le_left _ _
    have hεδ : ε ≤ δ := min_le_right _ _
    have ha0 := abs_nonneg (p (Sum.inl x.1))
    have hb0 := abs_nonneg (p (Sum.inr x.2))
    nlinarith

/-- Maximal projective independence is invariant under reindexing by an
equivalence between finite types. -/
theorem maximallyProjectiveEnergy_equiv
    {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J) {energy : J → ℝ}
    (hmax : MaximallyProjectiveEnergy energy) :
    MaximallyProjectiveEnergy (fun i => energy (e i)) := by
  intro k hbalanced hzero
  let k' : J → ℤ :=
    fun j => k (e.symm j)
  have hbalanced' : SpectralCharacterBalanced k' := by
    unfold SpectralCharacterBalanced at hbalanced ⊢
    have hsum :=
      e.bijective.sum_comp (fun j => k' j)
    have hleft :
        (∑ i, k' (e i)) = 0 := by
      simpa [k'] using hbalanced
    exact hsum.symm.trans hleft
  have hzero' :
      (∑ j, (k' j : ℝ) * energy j) = 0 := by
    have hsum :=
      e.bijective.sum_comp
        (fun j => (k' j : ℝ) * energy j)
    have hleft :
        (∑ i, (k' (e i) : ℝ) * energy (e i)) = 0 := by
      simpa [k'] using hzero
    exact hsum.symm.trans hleft
  have hk' : k' = 0 :=
    hmax k' hbalanced' hzero'
  funext i
  have hi := congrFun hk' (e i)
  simpa [k'] using hi

/-- Flattened separably coupled spectrum in product-minus-one cardinal
coordinates. -/
def reindexedSeparableInteractionEnergy
    {m n : ℕ}
    (left : Fin (m + 1) → ℝ)
    (right : Fin (n + 1) → ℝ)
    (p : Fin (m + 1) ⊕ Fin (n + 1) → ℝ) :
    Fin (m * n + m + n + 1) → ℝ :=
  fun i =>
    separableInteractionEnergy left right p
      ((@finProdFinEquiv (m + 1) (n + 1)).symm
        (finCongr (by ring) i))

/-- The flattened interaction difference is the product of one left and
one right factor coordinate. -/
theorem reindexedSeparableInteractionEnergy_sub_product
    {m n : ℕ}
    (left : Fin (m + 1) → ℝ)
    (right : Fin (n + 1) → ℝ)
    (p : Fin (m + 1) ⊕ Fin (n + 1) → ℝ)
    (i : Fin (m * n + m + n + 1)) :
    reindexedSeparableInteractionEnergy left right p i -
        reindexedBipartiteProductEnergy left right i =
      let x :=
        (@finProdFinEquiv (m + 1) (n + 1)).symm
          (finCongr (by ring) i)
      p (Sum.inl x.1) * p (Sum.inr x.2) := by
  unfold reindexedSeparableInteractionEnergy
  unfold reindexedBipartiteProductEnergy
  unfold bipartiteProductEnergy
  unfold separableInteractionEnergy
  ring

/-- **Separable temporal-dimension multiplication law.** A single
operator-Schmidt-rank-one diagonal interaction suffices for the exact
additive-to-multiplicative temporal-dimension jump for every finite pair.
The same witness remains uniformly close for every fixed-time Heisenberg
probe and attains the all-order collision floor. -/
theorem exists_smallSeparableInteraction_temporalDimensionMultiplication
    {m n : ℕ}
    (left : Fin (m + 1) → ℝ)
    (right : Fin (n + 1) → ℝ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ p : Fin (m + 1) ⊕ Fin (n + 1) → ℝ,
      MaximallyProjectiveEnergy
        (reindexedSeparableInteractionEnergy left right p) ∧
      ‖RHTower.finiteIndexDiagonalHamiltonian
            (reindexedSeparableInteractionEnergy left right p) -
          RHTower.finiteIndexDiagonalHamiltonian
            (reindexedBipartiteProductEnergy left right)‖ ≤ δ ∧
      projectiveTemporalRank
          (reindexedBipartiteProductEnergy left right) ≤ m + n ∧
      projectiveTemporalRank
          (reindexedSeparableInteractionEnergy left right p) =
        m * n + m + n ∧
      m * n ≤
        projectiveTemporalRank
            (reindexedSeparableInteractionEnergy left right p) -
          projectiveTemporalRank
            (reindexedBipartiteProductEnergy left right) ∧
      (∀ (O :
          RHTower.FiniteIndexClockSpace
                (Fin (m * n + m + n + 1)) →L[ℂ]
            RHTower.FiniteIndexClockSpace
                (Fin (m * n + m + n + 1)))
          (t : ℝ),
        ‖exp (t • ((-Complex.I) •
              RHTower.finiteIndexDiagonalHamiltonian
                (reindexedSeparableInteractionEnergy
                  left right p))) * O *
              star (exp (t • ((-Complex.I) •
                RHTower.finiteIndexDiagonalHamiltonian
                  (reindexedSeparableInteractionEnergy
                    left right p)))) -
            exp (t • ((-Complex.I) •
              RHTower.finiteIndexDiagonalHamiltonian
                (reindexedBipartiteProductEnergy left right))) * O *
              star (exp (t • ((-Complex.I) •
                RHTower.finiteIndexDiagonalHamiltonian
                  (reindexedBipartiteProductEnergy left right))))‖
          ≤ 2 * |t| * δ * ‖O‖) ∧
      (∀ (weight : Fin (m * n + m + n + 1) → ℝ),
        (∀ i, 0 < weight i) →
        ∀ r : ℕ,
          fidelityReplicaCollisionMass weight
              (reindexedSeparableInteractionEnergy left right p) r =
            fidelityReplicaPermutationFloor weight r) := by
  obtain ⟨p, hmax, hp⟩ :=
    exists_smallSeparableInteraction_maximallyProjective
      left right δ hδ
  let e :
      Fin (m * n + m + n + 1) ≃
        Fin (m + 1) × Fin (n + 1) :=
    (finCongr (by ring)).trans
      (@finProdFinEquiv (m + 1) (n + 1)).symm
  have hmaxFlat :
      MaximallyProjectiveEnergy
        (reindexedSeparableInteractionEnergy left right p) := by
    exact maximallyProjectiveEnergy_equiv e hmax
  have hpoint :
      ∀ i,
        |reindexedSeparableInteractionEnergy left right p i -
          reindexedBipartiteProductEnergy left right i| ≤ δ := by
    intro i
    rw [reindexedSeparableInteractionEnergy_sub_product]
    exact (hp _).le
  have hnorm :
      ‖RHTower.finiteIndexDiagonalHamiltonian
            (reindexedSeparableInteractionEnergy left right p) -
          RHTower.finiteIndexDiagonalHamiltonian
            (reindexedBipartiteProductEnergy left right)‖ ≤ δ :=
    finiteIndexDiagonalHamiltonian_norm_sub_le
      _ _ δ hδ.le hpoint
  have hbase :=
    bipartiteProduct_projectiveTemporalRank_le left right
  have hcoupled :
      projectiveTemporalRank
          (reindexedSeparableInteractionEnergy left right p) =
        m * n + m + n :=
    projectiveTemporalRank_eq hmaxFlat
  have hfinite :
      ∀ (O :
          RHTower.FiniteIndexClockSpace
                (Fin (m * n + m + n + 1)) →L[ℂ]
            RHTower.FiniteIndexClockSpace
                (Fin (m * n + m + n + 1)))
          (t : ℝ),
        ‖exp (t • ((-Complex.I) •
              RHTower.finiteIndexDiagonalHamiltonian
                (reindexedSeparableInteractionEnergy
                  left right p))) * O *
              star (exp (t • ((-Complex.I) •
                RHTower.finiteIndexDiagonalHamiltonian
                  (reindexedSeparableInteractionEnergy
                    left right p)))) -
            exp (t • ((-Complex.I) •
              RHTower.finiteIndexDiagonalHamiltonian
                (reindexedBipartiteProductEnergy left right))) * O *
              star (exp (t • ((-Complex.I) •
                RHTower.finiteIndexDiagonalHamiltonian
                  (reindexedBipartiteProductEnergy left right))))‖
          ≤ 2 * |t| * δ * ‖O‖ := by
    intro O t
    have hcoupledSelf :=
      finiteIndexDiagonalHamiltonian_isSelfAdjoint
        (reindexedSeparableInteractionEnergy left right p)
    have hbaseSelf :=
      finiteIndexDiagonalHamiltonian_isSelfAdjoint
        (reindexedBipartiteProductEnergy left right)
    calc
      _ ≤ 2 * |t| *
            ‖RHTower.finiteIndexDiagonalHamiltonian
                  (reindexedSeparableInteractionEnergy left right p) -
                RHTower.finiteIndexDiagonalHamiltonian
                  (reindexedBipartiteProductEnergy left right)‖ *
              ‖O‖ :=
        selfAdjoint_heisenbergEvolution_norm_sub_le
          (RHTower.finiteIndexDiagonalHamiltonian
            (reindexedSeparableInteractionEnergy left right p))
          (RHTower.finiteIndexDiagonalHamiltonian
            (reindexedBipartiteProductEnergy left right))
          O hcoupledSelf hbaseSelf t
      _ ≤ 2 * |t| * δ * ‖O‖ := by gcongr
  have hcollision :
      ∀ (weight : Fin (m * n + m + n + 1) → ℝ),
        (∀ i, 0 < weight i) →
        ∀ r : ℕ,
          fidelityReplicaCollisionMass weight
              (reindexedSeparableInteractionEnergy left right p) r =
            fidelityReplicaPermutationFloor weight r := by
    intro weight hweight r
    exact
      (all_fidelityReplicaCollisionMass_eq_floor_iff
        hweight
        (reindexedSeparableInteractionEnergy left right p)).2
          hmaxFlat r
  refine ⟨p, hmaxFlat, hnorm, hbase, hcoupled, ?_,
    hfinite, hcollision⟩
  omega

end

end GaloisForLFunctions.HTGeometry
