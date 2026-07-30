import GaloisForLFunctions.HTGeometry.WeakInteractionRecurrenceSingularityLaw

/-!
# Interaction multiplication of finite temporal dimension

For a finite energy packet, projective temporal dimension is the rational
rank of its energy gaps relative to one reference level. This file proves:

* every `d + 1` level packet has temporal dimension at most `d`;
* maximal projective independence attains that bound exactly;
* the tensor-sum of systems with `m + 1` and `n + 1` levels has temporal
  dimension at most `m + n`;
* an arbitrarily weak joint perturbation can attain the full product
  dimension `m * n + m + n`, creating at least `m * n` independent
  temporal directions;
* the exact dimension jump coexists with a dimension-free finite-time
  operator-norm bound and minimum collision mass at every replica order.

Thus the uncoupled additive bound and coupled multiplicative bound hold for
every pair of nonempty finite systems, with no genericity assumption on the
uncoupled spectra.
-/

open Set Filter NormedSpace
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Energy gaps relative to the distinguished zeroth level. -/
def projectiveGapPacket
    {d : ℕ} (energy : Fin (d + 1) → ℝ) : Fin d → ℝ :=
  fun i => energy i.succ - energy 0

/-- Rational dimension of the projective energy-gap space. -/
def projectiveTemporalRank
    {d : ℕ} (energy : Fin (d + 1) → ℝ) : ℕ :=
  rationalCoordinateRank (projectiveGapPacket energy)

/-- A packet of `d + 1` levels has projective temporal rank at most `d`. -/
theorem projectiveTemporalRank_le
    {d : ℕ} (energy : Fin (d + 1) → ℝ) :
    projectiveTemporalRank energy ≤ d := by
  unfold projectiveTemporalRank rationalCoordinateRank
  let s : Set ℝ := Set.range (projectiveGapPacket energy)
  letI : Fintype s := s.toFinite.fintype
  calc
    Module.finrank ℚ ↥(Submodule.span ℚ s) ≤ s.toFinset.card :=
      finrank_span_le_card s
    _ ≤ Fintype.card (Fin d) := by
      convert Fintype.card_range_le
        (projectiveGapPacket energy) using 1
      rw [Set.toFinset_card]
    _ = d := Fintype.card_fin d

/-- Maximal projective independence forces integer independence of all
gaps relative to one level. -/
theorem projectiveGapPacket_linearIndependent_int
    {d : ℕ} {energy : Fin (d + 1) → ℝ}
    (hmax : MaximallyProjectiveEnergy energy) :
    LinearIndependent ℤ (projectiveGapPacket energy) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  let k : Fin (d + 1) → ℤ :=
    Fin.cases (-∑ i, g i) g
  have hbalanced : SpectralCharacterBalanced k := by
    unfold SpectralCharacterBalanced
    rw [Fin.sum_univ_succ]
    simp [k]
  have henergy :
      (∑ i, (k i : ℝ) * energy i) = 0 := by
    rw [Fin.sum_univ_succ]
    simp only [k, Fin.cases_zero, Fin.cases_succ]
    push_cast
    calc
      -(∑ i, (g i : ℝ)) * energy 0 +
          ∑ i, (g i : ℝ) * energy i.succ =
          ∑ i, (g i : ℝ) *
            (energy i.succ - energy 0) := by
              simp_rw [mul_sub]
              rw [Finset.sum_sub_distrib]
              have hsum0 :
                  (∑ i, (g i : ℝ) * energy 0) =
                    (∑ i, (g i : ℝ)) * energy 0 := by
                rw [Finset.sum_mul]
              rw [hsum0]
              ring
      _ = 0 := by
        simpa [projectiveGapPacket, zsmul_eq_mul] using hg
  have hk := hmax k hbalanced henergy
  intro i
  have hi := congrFun hk i.succ
  simpa [k] using hi

/-- Maximal projective independence forces rational independence of all
gaps relative to one level. -/
theorem projectiveGapPacket_linearIndependent
    {d : ℕ} {energy : Fin (d + 1) → ℝ}
    (hmax : MaximallyProjectiveEnergy energy) :
    LinearIndependent ℚ (projectiveGapPacket energy) := by
  rw [← LinearIndependent.iff_fractionRing ℤ ℚ]
  exact projectiveGapPacket_linearIndependent_int hmax

/-- A maximally projective packet of `d + 1` levels has exactly `d`
independent temporal directions. -/
theorem projectiveTemporalRank_eq
    {d : ℕ} {energy : Fin (d + 1) → ℝ}
    (hmax : MaximallyProjectiveEnergy energy) :
    projectiveTemporalRank energy = d := by
  unfold projectiveTemporalRank rationalCoordinateRank
  simpa using
    finrank_span_eq_card
      (projectiveGapPacket_linearIndependent hmax)

/-- Every anchored energy gap belongs to the projective gap space. -/
theorem anchoredGap_mem_projectiveGapSubspace
    {d : ℕ} (energy : Fin (d + 1) → ℝ)
    (i : Fin (d + 1)) :
    energy i - energy 0 ∈
      visibleGapSubspace (projectiveGapPacket energy) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [visibleGapSubspace]
  · exact Submodule.subset_span ⟨j, rfl⟩

/-- Tensor-sum spectrum reindexed so its product cardinality is written as
`m * n + m + n + 1`. -/
def reindexedBipartiteProductEnergy
    {m n : ℕ}
    (left : Fin (m + 1) → ℝ)
    (right : Fin (n + 1) → ℝ) :
    Fin (m * n + m + n + 1) → ℝ :=
  fun i =>
    bipartiteProductEnergy left right
      (finCongr (by ring) i)

/-- The distinguished product level is the sum of the distinguished
one-body levels. -/
theorem reindexedBipartiteProductEnergy_zero
    {m n : ℕ}
    (left : Fin (m + 1) → ℝ)
    (right : Fin (n + 1) → ℝ) :
    reindexedBipartiteProductEnergy left right 0 =
      left 0 + right 0 := by
  have hzero :
      (@finProdFinEquiv (m + 1) (n + 1)).symm
          (0 : Fin ((m + 1) * (n + 1))) =
        (0, 0) := by
    ext <;> simp [finProdFinEquiv]
  change
    left
          ((@finProdFinEquiv (m + 1) (n + 1)).symm
            (finCongr (by ring) 0)).1 +
        right
          ((@finProdFinEquiv (m + 1) (n + 1)).symm
            (finCongr (by ring) 0)).2 =
      left 0 + right 0
  rw [show finCongr (by ring) (0 :
      Fin (m * n + m + n + 1)) = 0 by rfl, hzero]

/-- Temporal dimension of an uncoupled tensor-sum is at most the sum of
the one-body maximum dimensions. -/
theorem bipartiteProduct_projectiveTemporalRank_le
    {m n : ℕ}
    (left : Fin (m + 1) → ℝ)
    (right : Fin (n + 1) → ℝ) :
    projectiveTemporalRank
        (reindexedBipartiteProductEnergy left right) ≤
      m + n := by
  let leftSpace : Submodule ℚ ℝ :=
    visibleGapSubspace (projectiveGapPacket left)
  let rightSpace : Submodule ℚ ℝ :=
    visibleGapSubspace (projectiveGapPacket right)
  letI : FiniteDimensional ℚ leftSpace :=
    FiniteDimensional.span_of_finite ℚ
      (Set.finite_range (projectiveGapPacket left))
  letI : FiniteDimensional ℚ rightSpace :=
    FiniteDimensional.span_of_finite ℚ
      (Set.finite_range (projectiveGapPacket right))
  have hspan :
      visibleGapSubspace
          (projectiveGapPacket
            (reindexedBipartiteProductEnergy left right)) ≤
        leftSpace ⊔ rightSpace := by
    apply Submodule.span_le.2
    rintro x ⟨i, rfl⟩
    let p : Fin (m + 1) × Fin (n + 1) :=
      (@finProdFinEquiv (m + 1) (n + 1)).symm
        (finCongr (by ring) i.succ)
    have hleft :
        left p.1 - left 0 ∈ leftSpace :=
      anchoredGap_mem_projectiveGapSubspace left p.1
    have hright :
        right p.2 - right 0 ∈ rightSpace :=
      anchoredGap_mem_projectiveGapSubspace right p.2
    have hadd :
        (left p.1 - left 0) + (right p.2 - right 0) ∈
          leftSpace ⊔ rightSpace :=
      Submodule.add_mem _ (show left p.1 - left 0 ∈
        leftSpace ⊔ rightSpace from
          (show leftSpace ≤ leftSpace ⊔ rightSpace from
            le_sup_left) hleft)
        (show right p.2 - right 0 ∈
          leftSpace ⊔ rightSpace from
            (show rightSpace ≤ leftSpace ⊔ rightSpace from
              le_sup_right) hright)
    have heval :
        reindexedBipartiteProductEnergy left right i.succ =
          left p.1 + right p.2 := by
      rfl
    change
      reindexedBipartiteProductEnergy left right i.succ -
          reindexedBipartiteProductEnergy left right 0 ∈
        leftSpace ⊔ rightSpace
    rw [heval,
      reindexedBipartiteProductEnergy_zero]
    convert hadd using 1
    ring
  have hmono :
      Module.finrank ℚ
          (visibleGapSubspace
            (projectiveGapPacket
              (reindexedBipartiteProductEnergy left right))) ≤
        Module.finrank ℚ ↥(leftSpace ⊔ rightSpace) :=
    Submodule.finrank_mono hspan
  have hconservation :=
    observerTemporalDimension_conservation
      (projectiveGapPacket left)
      (projectiveGapPacket right)
  have hleftRank :
      rationalCoordinateRank
          (projectiveGapPacket left) ≤ m :=
    projectiveTemporalRank_le left
  have hrightRank :
      rationalCoordinateRank
          (projectiveGapPacket right) ≤ n :=
    projectiveTemporalRank_le right
  change
    Module.finrank ℚ
        (visibleGapSubspace
          (projectiveGapPacket
            (reindexedBipartiteProductEnergy left right))) ≤
      m + n
  change
    Module.finrank ℚ ↥(leftSpace ⊔ rightSpace) +
        Module.finrank ℚ ↥(leftSpace ⊓ rightSpace) =
      rationalCoordinateRank (projectiveGapPacket left) +
        rationalCoordinateRank (projectiveGapPacket right)
      at hconservation
  omega

/-- **Temporal-dimension multiplication law.** For every pair of nonempty
finite spectra and every positive norm budget, there is a joint perturbation
inside that budget whose temporal dimension is the maximum product
dimension. It creates at least `m * n` independent directions beyond the
uncoupled tensor-sum, while all finite-time Heisenberg probes obey the
dimension-free perturbation bound and all positive full-support replica
collision masses attain their universal floor. -/
theorem exists_arbitrarilyWeak_temporalDimensionMultiplication
    {m n : ℕ}
    (left : Fin (m + 1) → ℝ)
    (right : Fin (n + 1) → ℝ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ coupled : Fin (m * n + m + n + 1) → ℝ,
      MaximallyProjectiveEnergy coupled ∧
      ‖RHTower.finiteIndexDiagonalHamiltonian coupled -
          RHTower.finiteIndexDiagonalHamiltonian
            (reindexedBipartiteProductEnergy left right)‖ ≤ δ ∧
      projectiveTemporalRank
          (reindexedBipartiteProductEnergy left right) ≤
        m + n ∧
      projectiveTemporalRank coupled =
        m * n + m + n ∧
      m * n ≤
        projectiveTemporalRank coupled -
          projectiveTemporalRank
            (reindexedBipartiteProductEnergy left right) ∧
      (∀ (O :
          RHTower.FiniteIndexClockSpace
                (Fin (m * n + m + n + 1)) →L[ℂ]
            RHTower.FiniteIndexClockSpace
                (Fin (m * n + m + n + 1)))
          (t : ℝ),
        ‖exp (t • ((-Complex.I) •
              RHTower.finiteIndexDiagonalHamiltonian coupled)) * O *
              star (exp (t • ((-Complex.I) •
                RHTower.finiteIndexDiagonalHamiltonian coupled))) -
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
          fidelityReplicaCollisionMass weight coupled r =
            fidelityReplicaPermutationFloor weight r) := by
  obtain ⟨coupled, hmax, hnorm, hfinite, hcollision⟩ :=
    exists_arbitrarilyWeak_fullRecurrenceCompletion
      (m * n + m + n + 1)
      (reindexedBipartiteProductEnergy left right)
      δ hδ
  have hbase :=
    bipartiteProduct_projectiveTemporalRank_le left right
  have hcoupled :
      projectiveTemporalRank coupled =
        m * n + m + n :=
    projectiveTemporalRank_eq hmax
  refine ⟨coupled, hmax, hnorm, hbase, hcoupled, ?_,
    hfinite, hcollision⟩
  omega

end

end GaloisForLFunctions.HTGeometry
