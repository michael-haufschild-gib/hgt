import GaloisForLFunctions.HTGeometry.FiniteWindowReplicaCollisionResolution
import GaloisForLFunctions.HTGeometry.NevanlinnaNoncriticalProjectiveCompactPatch

/-!
# Fixed-order one-knob uniformity of the finite-window certificate

For a spectrum depending on one real knob, each replica detuning through a fixed order is detected
by a relation polynomial in the knob: the polynomial vanishes wherever the detuning does, and is
dominated by it.  Removing the finitely many roots of the nonzero relation polynomials leaves a set
on whose compact subsets all retained detunings are bounded away from zero, uniformly in the knob
and in the replica order.

Feeding that uniform gap to the finite-window collision certificate gives one error bound
`min 1 (T δ)⁻¹` valid simultaneously for every knob value in the compact set and every replica order
through the fixed one.  The affine (simultaneously diagonalized) family satisfies the detection
hypotheses outright, so there the whole statement is unconditional.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The replica detuning of a knob-dependent spectrum at multiplicity vectors `p`, `q`. -/
def oneKnobDetuning (E : ℝ → I → ℝ) (g : ℝ) (p q : I → ℕ) : ℝ :=
  replicaMultiplicityEnergy (E g) p - replicaMultiplicityEnergy (E g) q

/-- The finite index of replica multiplicity pairs through order `M`. -/
def replicaPairIndex (I : Type*) [Fintype I] [DecidableEq I] (M : ℕ) :
    Finset (ℕ × (I → ℕ) × (I → ℕ)) :=
  (Finset.range (M + 1)).biUnion fun n =>
    ((Finset.univ.piAntidiag n) ×ˢ (Finset.univ.piAntidiag n)).image fun pq => (n, pq.1, pq.2)

theorem mem_replicaPairIndex {M : ℕ} {n : ℕ} {p q : I → ℕ}
    (hn : n ≤ M) (hp : p ∈ Finset.univ.piAntidiag n) (hq : q ∈ Finset.univ.piAntidiag n) :
    (n, p, q) ∈ replicaPairIndex I M := by
  rw [replicaPairIndex, Finset.mem_biUnion]
  refine ⟨n, Finset.mem_range.mpr (Nat.lt_succ_of_le hn), ?_⟩
  rw [Finset.mem_image]
  exact ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, rfl⟩

/-- Relation-probe data for a knob-dependent spectrum: a continuous nonnegative probe dominated by
each replica detuning, with finite zero set unless the detuning vanishes identically.  The probe is
the modulus of the relation polynomial in the knob. -/
structure ReplicaRelationDetection (E : ℝ → I → ℝ) (J : Set ℝ) (M : ℕ) where
  /-- The relation probe of a replica multiplicity pair. -/
  probe : ℕ × (I → ℕ) × (I → ℕ) → ℝ → ℝ
  probe_continuous : ∀ x, Continuous (probe x)
  probe_nonneg : ∀ x g, 0 ≤ probe x g
  /-- The domination constant of a replica multiplicity pair. -/
  const : ℕ × (I → ℕ) × (I → ℕ) → ℝ
  const_pos : ∀ x, 0 < const x
  dominate : ∀ x, ∀ g ∈ J, probe x g ≤ const x * |oneKnobDetuning E g x.2.1 x.2.2|
  degenerate_or_finiteZeros : ∀ x ∈ replicaPairIndex I M,
    (∀ g ∈ J, oneKnobDetuning E g x.2.1 x.2.2 = 0) ∨ {g : ℝ | probe x g = 0}.Finite

variable {E : ℝ → I → ℝ} {J : Set ℝ} {M : ℕ}

/-- The exceptional knob values: the zeros of the nondegenerate relation probes. -/
def exceptionalKnobSet (d : ReplicaRelationDetection E J M) : Set ℝ :=
  ⋃ x ∈ (replicaPairIndex I M : Set (ℕ × (I → ℕ) × (I → ℕ))),
    {g : ℝ | d.probe x g = 0 ∧ ¬ (∀ g' ∈ J, oneKnobDetuning E g' x.2.1 x.2.2 = 0)}

/-- **The exceptional knob set is finite.** -/
theorem finite_exceptionalKnobSet (d : ReplicaRelationDetection E J M) :
    (exceptionalKnobSet d).Finite := by
  classical
  refine Set.Finite.biUnion (Finset.finite_toSet _) fun x hx => ?_
  rcases d.degenerate_or_finiteZeros x hx with hdeg | hfin
  · refine Set.Finite.subset Set.finite_empty fun g hg => ?_
    exact absurd hdeg hg.2
  · exact hfin.subset fun g hg => hg.1

/-- **Uniform replica-detuning gap.**  On a compact set of knob values avoiding the exceptional
set, every retained detuning through order `M` is bounded away from zero. -/
theorem exists_uniform_replicaDetuning_gap (d : ReplicaRelationDetection E J M)
    {K : Set ℝ} (hK : IsCompact K) (hKJ : K ⊆ J)
    (hKR : ∀ g ∈ K, g ∉ exceptionalKnobSet d) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g ∈ K, ∀ n ≤ M,
      ∀ p ∈ Finset.univ.piAntidiag n, ∀ q ∈ Finset.univ.piAntidiag n,
        replicaMultiplicityEnergy (E g) p ≠ replicaMultiplicityEnergy (E g) q →
          δ ≤ |replicaMultiplicityEnergy (E g) p - replicaMultiplicityEnergy (E g) q| := by
  classical
  set ρ : Type _ := {x : ℕ × (I → ℕ) × (I → ℕ) // x ∈ replicaPairIndex I M} with hρ
  set f : ℝ → ρ → ℝ := fun g x =>
    if (∀ g' ∈ J, oneKnobDetuning E g' (x : ℕ × (I → ℕ) × (I → ℕ)).2.1
        (x : ℕ × (I → ℕ) × (I → ℕ)).2.2 = 0)
      then 1
      else d.probe (x : ℕ × (I → ℕ) × (I → ℕ)) g / d.const (x : ℕ × (I → ℕ) × (I → ℕ))
    with hf
  have hcont : ∀ x : ρ, ContinuousOn (fun g => f g x) K := by
    intro x
    by_cases hdeg : (∀ g' ∈ J, oneKnobDetuning E g' (x : ℕ × (I → ℕ) × (I → ℕ)).2.1
        (x : ℕ × (I → ℕ) × (I → ℕ)).2.2 = 0)
    · simp only [hf, if_pos hdeg]
      exact continuousOn_const
    · simp only [hf, if_neg hdeg]
      exact ((d.probe_continuous _).div_const _).continuousOn
  have hpos : ∀ g ∈ K, ∀ x : ρ, 0 < f g x := by
    intro g hg x
    by_cases hdeg : (∀ g' ∈ J, oneKnobDetuning E g' (x : ℕ × (I → ℕ) × (I → ℕ)).2.1
        (x : ℕ × (I → ℕ) × (I → ℕ)).2.2 = 0)
    · simp only [hf, if_pos hdeg]
      norm_num
    · simp only [hf, if_neg hdeg]
      have hroot : d.probe (x : ℕ × (I → ℕ) × (I → ℕ)) g ≠ 0 := by
        intro hcon
        refine hKR g hg ?_
        rw [exceptionalKnobSet, Set.mem_iUnion₂]
        exact ⟨(x : ℕ × (I → ℕ) × (I → ℕ)), x.2, hcon, hdeg⟩
      exact div_pos (lt_of_le_of_ne (d.probe_nonneg _ g) (Ne.symm hroot)) (d.const_pos _)
  obtain ⟨η, hη, hbound⟩ := compact_finite_strictPositive_uniformLowerBound K hK f hcont hpos
  refine ⟨η, hη, ?_⟩
  intro g hg n hn p hp q hq hne
  have hx : (n, p, q) ∈ replicaPairIndex I M := mem_replicaPairIndex hn hp hq
  have hdetuning : oneKnobDetuning E g p q ≠ 0 := by
    rw [oneKnobDetuning, sub_ne_zero]
    exact hne
  have hdeg : ¬ (∀ g' ∈ J, oneKnobDetuning E g' p q = 0) := by
    intro hcon
    exact hdetuning (hcon g (hKJ hg))
  have hval := hbound g hg ⟨(n, p, q), hx⟩
  simp only [hf, if_neg hdeg] at hval
  have hdom := d.dominate (n, p, q) g (hKJ hg)
  have hCpos := d.const_pos (n, p, q)
  have hchain : η ≤ |oneKnobDetuning E g p q| := by
    have hdiv : d.probe (n, p, q) g / d.const (n, p, q)
        ≤ |oneKnobDetuning E g p q| := by
      rw [div_le_iff₀ hCpos]
      calc d.probe (n, p, q) g ≤ d.const (n, p, q) * |oneKnobDetuning E g p q| := hdom
        _ = |oneKnobDetuning E g p q| * d.const (n, p, q) := by ring
    exact le_trans hval hdiv
  rwa [oneKnobDetuning] at hchain

/-- **Fixed-order one-knob finite-window certificate.**  One error bound holds simultaneously for
every knob value in the compact set, every replica order through `M`, and every window length. -/
theorem exists_uniform_finiteWindow_certificate (d : ReplicaRelationDetection E J M)
    {K : Set ℝ} (hK : IsCompact K) (hKJ : K ⊆ J) (hKR : ∀ g ∈ K, g ∉ exceptionalKnobSet d)
    {weight : I → ℝ} (hweight : ∀ i, 0 ≤ weight i) (hweightSum : ∑ i, weight i = 1) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ g ∈ K, ∀ n ≤ M, ∀ T : ℝ, 0 < T →
      ‖finiteSpectralSurvivalFidelityMean weight (E g) n T -
          (fidelityReplicaCollisionMass weight (E g) n : ℂ)‖ ≤ min 1 (T * δ)⁻¹ := by
  obtain ⟨δ, hδ, hgap⟩ := exists_uniform_replicaDetuning_gap d hK hKJ hKR
  refine ⟨δ, hδ, fun g hg n hn T hT => ?_⟩
  exact norm_finiteSpectralSurvivalFidelityMean_sub_collisionMass_le hweight hweightSum n hT hδ
    (fun p hp q hq hne => hgap g hg n hn p hp q hq hne)

/-! ## The affine one-knob family -/

/-- The spectrum of a simultaneously diagonalized affine family `A + g V`. -/
def affineSpectrum (a v : I → ℝ) (g : ℝ) (i : I) : ℝ := a i + g * v i

omit [DecidableEq I] in
theorem oneKnobDetuning_affineSpectrum (a v : I → ℝ) (g : ℝ) (p q : I → ℕ) :
    oneKnobDetuning (affineSpectrum a v) g p q
      = (∑ i, ((p i : ℝ) - (q i : ℝ)) * a i)
        + g * ∑ i, ((p i : ℝ) - (q i : ℝ)) * v i := by
  rw [oneKnobDetuning, replicaMultiplicityEnergy, replicaMultiplicityEnergy, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [affineSpectrum]
  ring

/-- The relation polynomial of an affine family is the detuning itself. -/
def affineRelationPolynomial (a v : I → ℝ) (x : ℕ × (I → ℕ) × (I → ℕ)) : Polynomial ℝ :=
  Polynomial.C (∑ i, ((x.2.1 i : ℝ) - (x.2.2 i : ℝ)) * a i) +
    Polynomial.C (∑ i, ((x.2.1 i : ℝ) - (x.2.2 i : ℝ)) * v i) * Polynomial.X

omit [DecidableEq I] in
theorem eval_affineRelationPolynomial (a v : I → ℝ) (x : ℕ × (I → ℕ) × (I → ℕ)) (g : ℝ) :
    (affineRelationPolynomial a v x).eval g
      = oneKnobDetuning (affineSpectrum a v) g x.2.1 x.2.2 := by
  rw [affineRelationPolynomial, oneKnobDetuning_affineSpectrum]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  ring

/-- **The affine family carries relation-probe data.**  Its detunings are polynomials of degree at
most one in the knob, so the probe is the detuning itself and the domination constant is one. -/
def affineReplicaRelationDetection (a v : I → ℝ) (J : Set ℝ) (M : ℕ) :
    ReplicaRelationDetection (affineSpectrum a v) J M where
  probe := fun x g => |(affineRelationPolynomial a v x).eval g|
  probe_continuous := fun x => ((affineRelationPolynomial a v x).continuous).abs
  probe_nonneg := fun _ _ => abs_nonneg _
  const := fun _ => 1
  const_pos := fun _ => one_pos
  dominate := by
    intro x g _
    rw [eval_affineRelationPolynomial, one_mul]
  degenerate_or_finiteZeros := by
    intro x _
    by_cases hx : affineRelationPolynomial a v x = 0
    · left
      intro g _
      rw [← eval_affineRelationPolynomial, hx, Polynomial.eval_zero]
    · right
      refine (Polynomial.finite_setOf_isRoot hx).subset fun g hg => ?_
      exact abs_eq_zero.mp hg

/-- **Fixed-order one-knob robustness for an affine spectral family.**  Outside a finite set of knob
values, every compact knob set carries one finite-window error bound valid for all replica orders
through `M` and all window lengths. -/
theorem affine_exists_uniform_finiteWindow_certificate (a v : I → ℝ) (J : Set ℝ) (M : ℕ)
    {weight : I → ℝ} (hweight : ∀ i, 0 ≤ weight i) (hweightSum : ∑ i, weight i = 1) :
    ∃ R : Set ℝ, R.Finite ∧ ∀ K : Set ℝ, IsCompact K → K ⊆ J → (∀ g ∈ K, g ∉ R) →
      ∃ δ : ℝ, 0 < δ ∧ ∀ g ∈ K, ∀ n ≤ M, ∀ T : ℝ, 0 < T →
        ‖finiteSpectralSurvivalFidelityMean weight (affineSpectrum a v g) n T -
            (fidelityReplicaCollisionMass weight (affineSpectrum a v g) n : ℂ)‖
          ≤ min 1 (T * δ)⁻¹ := by
  refine ⟨exceptionalKnobSet (affineReplicaRelationDetection a v J M) ∩ J,
    (finite_exceptionalKnobSet _).subset Set.inter_subset_left, fun K hK hKJ hKR => ?_⟩
  refine exists_uniform_finiteWindow_certificate (affineReplicaRelationDetection a v J M) hK hKJ
    ?_ hweight hweightSum
  intro g hg hcon
  exact hKR g hg ⟨hcon, hKJ hg⟩


/-! ## The knob family as a Hermitian affine matrix family -/

omit [Fintype I] in
/-- For simultaneously diagonalized data the one-knob Hermitian family `A + g V` is the diagonal
matrix of the affine spectrum. -/
theorem diagonal_add_smul_diagonal (a v : I → ℝ) (g : ℝ) :
    Matrix.diagonal a + g • Matrix.diagonal v = Matrix.diagonal (affineSpectrum a v g) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.diagonal_apply_eq, affineSpectrum]
  · simp [hij]

omit [Fintype I] in
theorem isHermitian_diagonal_affine (a v : I → ℝ) (g : ℝ) :
    (Matrix.diagonal a + g • Matrix.diagonal v : Matrix I I ℝ).IsHermitian := by
  rw [diagonal_add_smul_diagonal]
  exact Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)

end

end GaloisForLFunctions.HTGeometry
