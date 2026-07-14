import GaloisForLFunctions.HTGeometry.FiniteRangeProjectiveTail
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Cofinite Gram polarization of coefficient tails

A finite family of complex coefficient functions is independent modulo finite support exactly when
every finite deletion leaves a finite square evaluation packet with strictly positive Gram matrix.
This converts the tail matroid into a deletion-robust positive geometry.

In a prime-Dirichlet application, positive weights may be inserted into the selected rows.  For
unit-phase coefficients the diagonal then consists of partial sums of the all-positive prime
carrier, while the off-diagonal entries are cross-Hadamard carriers.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped ComplexOrder

noncomputable section

/-- The column vector obtained by evaluating one coefficient function on a square packet outside
a deleted coordinate set. -/
def cofiniteEvaluationColumn
    {J P : Type*} [Fintype J]
    (c : J → P → ℂ) (F : Set P) (points : J → {p : P // p ∉ F})
    (j : J) : EuclideanSpace ℂ J :=
  WithLp.toLp 2 fun row => c j (points row)

/-- The Hermitian Gram matrix of a square cofinite evaluation packet. -/
def cofiniteEvaluationGram
    {J P : Type*} [Fintype J]
    (c : J → P → ℂ) (F : Set P) (points : J → {p : P // p ∉ F}) :
    Matrix J J ℂ :=
  Matrix.gram ℂ (cofiniteEvaluationColumn c F points)

/-- Tail independence makes the coefficient family linearly independent after deleting any
finite coordinate set. -/
theorem TailCoefficientIndependent.linearIndependent_on_compl
    {J P : Type*} [Fintype J]
    (c : J → P → ℂ) (htail : TailCoefficientIndependent c)
    (F : Set P) (hF : F.Finite) :
    LinearIndependent ℂ
      (fun j => fun p : {p : P // p ∉ F} => c j p) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro q hq
  have hqzero : q = 0 := by
    apply htail q
    apply hF.subset
    intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    by_contra hpF
    have hpoint := congrFun hq ⟨p, hpF⟩
    apply hp
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hpoint
  exact fun i => congrFun hqzero i

/-- After every finite deletion, a tail-independent family admits a square strictly positive Gram
packet. -/
theorem TailCoefficientIndependent.exists_cofinite_posDef_evaluationGram
    {J P : Type*} [Fintype J] [DecidableEq J]
    (c : J → P → ℂ) (htail : TailCoefficientIndependent c)
    (F : Set P) (hF : F.Finite) :
    ∃ points : J → {p : P // p ∉ F},
      (cofiniteEvaluationGram c F points).PosDef := by
  have hlin := htail.linearIndependent_on_compl c F hF
  obtain ⟨points, hfull⟩ :=
    GaloisForLFunctions.HTGeometry.exists_fullRank_evaluation_packet
    (fun j => fun p : {p : P // p ∉ F} => c j p) hlin
  refine ⟨points, ?_⟩
  apply Matrix.posDef_gram_of_linearIndependent
  have hcols : LinearIndependent ℂ
      (Matrix.of fun row j => c j (points row) : Matrix J J ℂ).col :=
    Matrix.linearIndependent_cols_iff_isUnit.mpr hfull
  rw [Fintype.linearIndependent_iff] at hcols ⊢
  intro q hq
  apply hcols q
  funext row
  have hrow := congrArg (fun v : EuclideanSpace ℂ J => v row) hq
  simpa [cofiniteEvaluationColumn, Matrix.col_apply, Finset.sum_apply,
    Pi.smul_apply] using hrow

/-- **Cofinite Gram polarization law.**  Independence modulo finite support is equivalent to
strict positive Gram realizability after every finite deletion. -/
theorem tailCoefficientIndependent_iff_cofinite_posDef_evaluationGram
    {J P : Type*} [Fintype J] [DecidableEq J]
    (c : J → P → ℂ) :
    TailCoefficientIndependent c ↔
      ∀ F : Set P, F.Finite →
        ∃ points : J → {p : P // p ∉ F},
          (cofiniteEvaluationGram c F points).PosDef := by
  constructor
  · intro htail F hF
    exact htail.exists_cofinite_posDef_evaluationGram c F hF
  · intro hgram q hsupp
    let F : Set P := {p | ∑ j, q j * c j p ≠ 0}
    obtain ⟨points, hpos⟩ := hgram F hsupp
    have hlin : LinearIndependent ℂ (cofiniteEvaluationColumn c F points) :=
      Matrix.posDef_gram_iff_linearIndependent.mp hpos
    rw [Fintype.linearIndependent_iff] at hlin
    have hqpoint : ∀ i, q i = 0 := hlin q (by
      ext row
      have hzero : ∑ j, q j * c j (points row) = 0 := by
        apply not_ne_iff.mp
        exact (points row).property
      simpa [cofiniteEvaluationColumn, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        using hzero)
    exact funext hqpoint

/-- The cofinite weighted Gram energy of one coefficient vector. -/
def cofiniteWeightedGramEnergy
    {J P : Type*} [Fintype J] [DecidableEq P]
    (c : J → P → ℂ) (weight : P → ℝ) (F : Finset P) (q : J → ℂ) : ℝ :=
  ∑' p, if p ∈ F then 0
    else weight p * ‖∑ j, q j * c j p‖ ^ 2

/-- **Support-stratified metric radical law.**  For a nonnegative summable Gram metric, zero
energy means precisely that the coefficient combination vanishes at every undeleted coordinate
carrying positive weight.  Hence the radical depends on the support stratum of the metric, not on
the values of its positive weights. -/
theorem cofiniteWeightedGramEnergy_eq_zero_iff_on_positiveSupport
    {J P : Type*} [Fintype J] [DecidableEq P]
    (c : J → P → ℂ) (weight : P → ℝ) (F : Finset P) (q : J → ℂ)
    (hweight : ∀ p, 0 ≤ weight p)
    (hsummable : Summable fun p => if p ∈ F then 0
      else weight p * ‖∑ j, q j * c j p‖ ^ 2) :
    cofiniteWeightedGramEnergy c weight F q = 0 ↔
      ∀ p, p ∉ F → 0 < weight p → ∑ j, q j * c j p = 0 := by
  classical
  let g : P → ℝ := fun p => if p ∈ F then 0
    else weight p * ‖∑ j, q j * c j p‖ ^ 2
  change (∑' p, g p) = 0 ↔ _
  constructor
  · intro hzero p hpF hpweight
    have hnonneg : ∀ r, 0 ≤ g r := by
      intro r
      by_cases hrF : r ∈ F
      · simp [g, hrF]
      · simpa only [g, hrF, ↓reduceIte] using
          mul_nonneg (hweight r) (sq_nonneg ‖∑ j, q j * c j r‖)
    have hle : g p ≤ ∑' r, g r := hsummable.le_tsum p fun r _ => hnonneg r
    have hgp : g p = 0 := le_antisymm (by simpa only [hzero] using hle) (hnonneg p)
    simp only [g, hpF, ↓reduceIte] at hgp
    have hnormsq : ‖∑ j, q j * c j p‖ ^ 2 = 0 :=
      (mul_eq_zero.mp hgp).resolve_left (ne_of_gt hpweight)
    exact norm_eq_zero.mp (sq_eq_zero_iff.mp hnormsq)
  · intro hvanish
    have hg : g = 0 := by
      funext p
      by_cases hpF : p ∈ F
      · simp [g, hpF]
      · by_cases hpweight : weight p = 0
        · simp [g, hpF, hpweight]
        · have hpweightPos : 0 < weight p :=
            lt_of_le_of_ne (hweight p) (Ne.symm hpweight)
          simp [g, hpF, hvanish p hpF hpweightPos]
    simp [hg]

/-- **Full-support metric radical law.**  For any strictly positive summable Gram metric, the
zero-energy vectors are exactly the coefficient combinations vanishing outside the deleted
finite set.  In particular, changing the positive weights changes the metric but not its
radical. -/
theorem cofiniteWeightedGramEnergy_eq_zero_iff
    {J P : Type*} [Fintype J] [DecidableEq P]
    (c : J → P → ℂ) (weight : P → ℝ) (F : Finset P) (q : J → ℂ)
    (hweight : ∀ p, 0 < weight p)
    (hsummable : Summable fun p => if p ∈ F then 0
      else weight p * ‖∑ j, q j * c j p‖ ^ 2) :
    cofiniteWeightedGramEnergy c weight F q = 0 ↔
      ∀ p, p ∉ F → ∑ j, q j * c j p = 0 := by
  simpa only [show (∀ p, p ∉ F → 0 < weight p →
      ∑ j, q j * c j p = 0) ↔
      (∀ p, p ∉ F → ∑ j, q j * c j p = 0) by
        constructor
        · intro h p hpF
          exact h p hpF (hweight p)
        · exact fun h p hpF _ => h p hpF] using
    cofiniteWeightedGramEnergy_eq_zero_iff_on_positiveSupport
      c weight F q (fun p => (hweight p).le) hsummable

/-- Two nonnegative summable weights with the same positive support induce exactly the same Gram
radical after every fixed finite deletion. -/
theorem cofiniteWeightedGramEnergy_zero_iff_same_positiveSupport
    {J P : Type*} [Fintype J] [DecidableEq P]
    (c : J → P → ℂ) (weight₁ weight₂ : P → ℝ) (F : Finset P) (q : J → ℂ)
    (hweight₁ : ∀ p, 0 ≤ weight₁ p) (hweight₂ : ∀ p, 0 ≤ weight₂ p)
    (hsupport : ∀ p, 0 < weight₁ p ↔ 0 < weight₂ p)
    (hsummable₁ : Summable fun p => if p ∈ F then 0
      else weight₁ p * ‖∑ j, q j * c j p‖ ^ 2)
    (hsummable₂ : Summable fun p => if p ∈ F then 0
      else weight₂ p * ‖∑ j, q j * c j p‖ ^ 2) :
    cofiniteWeightedGramEnergy c weight₁ F q = 0 ↔
      cofiniteWeightedGramEnergy c weight₂ F q = 0 := by
  rw [cofiniteWeightedGramEnergy_eq_zero_iff_on_positiveSupport
      c weight₁ F q hweight₁ hsummable₁,
    cofiniteWeightedGramEnergy_eq_zero_iff_on_positiveSupport
      c weight₂ F q hweight₂ hsummable₂]
  constructor
  · exact fun h p hpF hp => h p hpF ((hsupport p).mpr hp)
  · exact fun h p hpF hp => h p hpF ((hsupport p).mp hp)

/-- Any two strictly positive summable weights induce Gram forms with the same radical after the
same finite deletion. -/
theorem cofiniteWeightedGramEnergy_zero_iff_change_weight
    {J P : Type*} [Fintype J] [DecidableEq P]
    (c : J → P → ℂ) (weight₁ weight₂ : P → ℝ) (F : Finset P) (q : J → ℂ)
    (hweight₁ : ∀ p, 0 < weight₁ p) (hweight₂ : ∀ p, 0 < weight₂ p)
    (hsummable₁ : Summable fun p => if p ∈ F then 0
      else weight₁ p * ‖∑ j, q j * c j p‖ ^ 2)
    (hsummable₂ : Summable fun p => if p ∈ F then 0
      else weight₂ p * ‖∑ j, q j * c j p‖ ^ 2) :
    cofiniteWeightedGramEnergy c weight₁ F q = 0 ↔
      cofiniteWeightedGramEnergy c weight₂ F q = 0 := by
  rw [cofiniteWeightedGramEnergy_eq_zero_iff c weight₁ F q hweight₁ hsummable₁,
    cofiniteWeightedGramEnergy_eq_zero_iff c weight₂ F q hweight₂ hsummable₂]

/-- Every cofinite weighted Gram form is strictly positive away from the zero coefficient vector. -/
def CofiniteWeightedGramStrict
    {J P : Type*} [Fintype J] [DecidableEq P]
    (c : J → P → ℂ) (weight : P → ℝ) : Prop :=
  ∀ F : Finset P, ∀ q : J → ℂ, q ≠ 0 →
    0 < cofiniteWeightedGramEnergy c weight F q

/-- **Infinite weighted cofinite Gram law.**  Under absolute convergence and strictly positive
coordinate weights, tail independence is exactly strict positivity of every cofinite weighted
Gram form. -/
theorem tailCoefficientIndependent_iff_cofiniteWeightedGramStrict
    {J P : Type*} [Fintype J] [DecidableEq P]
    (c : J → P → ℂ) (weight : P → ℝ)
    (hweight : ∀ p, 0 < weight p)
    (hsummable : ∀ F : Finset P, ∀ q : J → ℂ,
      Summable fun p => if p ∈ F then 0
        else weight p * ‖∑ j, q j * c j p‖ ^ 2) :
    TailCoefficientIndependent c ↔ CofiniteWeightedGramStrict c weight := by
  classical
  constructor
  · intro htail F q hq
    have hinf : {p | ∑ j, q j * c j p ≠ 0}.Infinite := by
      intro hfinite
      exact hq (htail q hfinite)
    obtain ⟨p, hp, hpF⟩ := (hinf.diff F.finite_toSet).nonempty
    refine (hsummable F q).tsum_pos (fun r => ?_) p ?_
    · by_cases hrF : r ∈ F
      · simp [hrF]
      · simpa only [hrF, ↓reduceIte] using
          mul_nonneg (le_of_lt (hweight r)) (sq_nonneg ‖∑ j, q j * c j r‖)
    · simp only [Set.mem_setOf_eq] at hp
      have hpF' : p ∉ F := by simpa using hpF
      simpa only [hpF', ↓reduceIte] using
        mul_pos (hweight p) (sq_pos_of_pos (norm_pos_iff.mpr hp))
  · intro hstrict q hsupp
    by_contra hq
    let F : Finset P := hsupp.toFinset
    have hpos := hstrict F q hq
    have hzero : cofiniteWeightedGramEnergy c weight F q = 0 := by
      unfold cofiniteWeightedGramEnergy
      have hfun : (fun p => if p ∈ F then 0
          else weight p * ‖∑ j, q j * c j p‖ ^ 2) = (fun _ => 0) := by
        funext p
        by_cases hpF : p ∈ F
        · simp [hpF]
        · have hpzero : ∑ j, q j * c j p = 0 := by
            apply not_ne_iff.mp
            intro hpne
            apply hpF
            simpa only [F, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hpne
          simp [hpF, hpzero]
      rw [hfun, tsum_zero]
    rw [hzero] at hpos
    exact (lt_irrefl 0) hpos

/-- Unit-phase coefficient families automatically satisfy the absolute-convergence hypothesis of
the weighted cofinite Gram law for every summable positive weight. -/
theorem tailCoefficientIndependent_iff_cofiniteWeightedGramStrict_of_phase
    {J P : Type*} [Fintype J] [DecidableEq P]
    (c : J → P → ℂ) (weight : P → ℝ)
    (hphase : ∀ j p, ‖c j p‖ = 1)
    (hweight : ∀ p, 0 < weight p)
    (hwsum : Summable weight) :
    TailCoefficientIndependent c ↔ CofiniteWeightedGramStrict c weight := by
  apply tailCoefficientIndependent_iff_cofiniteWeightedGramStrict c weight hweight
  intro F q
  let Q : ℝ := ∑ j, ‖q j‖
  let g : P → ℝ := fun p => if p ∈ F then 0
    else weight p * ‖∑ j, q j * c j p‖ ^ 2
  have hdom : Summable fun p => weight p * Q ^ 2 :=
    hwsum.mul_right (Q ^ 2)
  change Summable g
  refine Summable.of_nonneg_of_le (f := fun p => weight p * Q ^ 2) (g := g) ?_ ?_ hdom
  · intro p
    by_cases hpF : p ∈ F
    · simp [g, hpF]
    · simpa only [g, hpF, ↓reduceIte] using
        mul_nonneg (le_of_lt (hweight p)) (sq_nonneg ‖∑ j, q j * c j p‖)
  · intro p
    by_cases hpF : p ∈ F
    · simp only [g, hpF, ↓reduceIte]
      exact mul_nonneg (le_of_lt (hweight p)) (sq_nonneg Q)
    · simp only [g, hpF, ↓reduceIte]
      apply mul_le_mul_of_nonneg_left _ (le_of_lt (hweight p))
      have hnorm : ‖∑ j, q j * c j p‖ ≤ Q := by
        calc
          ‖∑ j, q j * c j p‖ ≤ ∑ j, ‖q j * c j p‖ := norm_sum_le _ _
          _ = ∑ j, ‖q j‖ := by
            apply Finset.sum_congr rfl
            intro j _
            rw [norm_mul, hphase, mul_one]
          _ = Q := rfl
      have hQ : 0 ≤ Q := Finset.sum_nonneg fun _ _ => norm_nonneg _
      nlinarith [norm_nonneg (∑ j, q j * c j p)]

/-- One entry of the cofinite weighted cross-Hadamard carrier matrix. -/
def cofiniteWeightedHadamardEntry
    {J P : Type*} [DecidableEq P]
    (c : J → P → ℂ) (weight : P → ℝ) (F : Finset P) (i j : J) : ℂ :=
  ∑' p, if p ∈ F then 0
    else (weight p : ℂ) * star (c i p) * c j p

/-- **Common Hadamard-norm diagonal.**  A unit-phase family has one common weighted diagonal,
independent of the source label. -/
theorem cofiniteWeightedHadamardEntry_phase_diagonal
    {J P : Type*} [DecidableEq P]
    (c : J → P → ℂ) (weight : P → ℝ) (F : Finset P)
    (hphase : ∀ j p, ‖c j p‖ = 1) (j : J) :
    cofiniteWeightedHadamardEntry c weight F j j =
      ∑' p, if p ∈ F then 0 else (weight p : ℂ) := by
  apply tsum_congr
  intro p
  by_cases hpF : p ∈ F
  · simp [hpF]
  · simp only [hpF, ↓reduceIte]
    rw [mul_assoc, RCLike.star_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq, hphase]
    norm_num

/-- A unit-phase packet has constant diagonal Gram entries: each diagonal is the packet size. -/
theorem cofiniteEvaluationGram_phase_diagonal
    {J P : Type*} [Fintype J]
    (c : J → P → ℂ) (F : Set P) (points : J → {p : P // p ∉ F})
    (hphase : ∀ j p, ‖c j p‖ = 1) (j : J) :
    cofiniteEvaluationGram c F points j j = Fintype.card J := by
  rw [cofiniteEvaluationGram, Matrix.gram_apply]
  rw [PiLp.inner_apply]
  simp only [cofiniteEvaluationColumn, WithLp.ofLp_toLp, RCLike.inner_apply]
  calc
    ∑ row, c j (points row) * star (c j (points row)) =
        ∑ _row : J, (1 : ℂ) := by
          apply Finset.sum_congr rfl
          intro row _
          rw [mul_comm, RCLike.star_def, RCLike.conj_mul, hphase]
          norm_num
    _ = Fintype.card J := by simp

end

end GaloisForLFunctions.HTGeometry
