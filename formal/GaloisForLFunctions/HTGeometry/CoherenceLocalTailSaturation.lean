import GaloisForLFunctions.HTGeometry.PrefixFunctionTailIndependentFamily
import GaloisForLFunctions.HTGeometry.AlmostDisjointIsodivisorialFrame
import GaloisForLFunctions.HTGeometry.PrimeDirichletDifferentialField

/-!
# Coherence-local tail saturation

This module transports the explicit prefix-function family into an arbitrary
sparse coordinate range.  It proves three load-bearing parts of the local
saturation law:

* every finite injective subfamily is independent modulo finite support;
* multiplication by an arbitrary common base orientation preserves that rank;
* if the embedded range has small weighted square budget, every member and
  every pair of members have correspondingly small weighted distance.

For prime coordinates, the existing exact tail/differential matroid theorem
then gives differential independence of every finite translated palette.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

instance : Nonempty PrefixFunctionCoordinate :=
  ⟨⟨0, fun _ => false⟩⟩

/-- Transport the prefix family into the range of a sparse coordinate embedding,
using the positive orientation off that range. -/
noncomputable def sparsePrefixOrientation {P : Type*}
    (e : PrefixFunctionCoordinate ↪ P) (x : ℕ → Bool) (p : P) : Bool := by
  classical
  exact if hp : p ∈ Set.range e then
    prefixFunctionOrientation x (Function.invFun e p)
  else false

@[simp] theorem sparsePrefixOrientation_apply_embedding {P : Type*}
    (e : PrefixFunctionCoordinate ↪ P) (x : ℕ → Bool)
    (q : PrefixFunctionCoordinate) :
    sparsePrefixOrientation e x (e q) = prefixFunctionOrientation x q := by
  classical
  rw [sparsePrefixOrientation, dif_pos ⟨q, rfl⟩]
  rw [Function.leftInverse_invFun e.injective q]

theorem sparsePrefixOrientation_pattern_fiber_infinite
    {I P : Type*} [Fintype I] (e : PrefixFunctionCoordinate ↪ P)
    (x : I → ℕ → Bool) (hx : Function.Injective x) (b : I → Bool) :
    {p : P | primeOrientationPattern (fun i => sparsePrefixOrientation e (x i)) p = b}.Infinite := by
  let A : Set PrefixFunctionCoordinate :=
    {q | primeOrientationPattern (fun i => prefixFunctionOrientation (x i)) q = b}
  have hA : A.Infinite :=
    prefixFunctionOrientation_pattern_fiber_infinite x hx b
  apply (Set.Infinite.image e.injective.injOn hA).mono
  intro p hp
  obtain ⟨q, hqA, rfl⟩ := hp
  change (fun i => prefixFunctionOrientation (x i) q) = b at hqA
  change (fun i => sparsePrefixOrientation e (x i) (e q)) = b
  simpa only [sparsePrefixOrientation_apply_embedding] using hqA

/-- Sparse transport preserves the recurring-pattern tail rank of every finite
injective sequence family. -/
theorem sparsePrefixOrientation_tailIndependent
    {I P : Type*} [Fintype I] (e : PrefixFunctionCoordinate ↪ P)
    (x : I → ℕ → Bool) (hx : Function.Injective x) :
    PrimeOrientationTailIndependent (fun i => sparsePrefixOrientation e (x i)) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl _ =>
      intro c _
      exact Subsingleton.elim c 0
  | inr hI =>
      let anchor : I := Classical.choice hI
      apply primeOrientationTailIndependent_of_anchoredSkeleton
        (fun i => sparsePrefixOrientation e (x i)) anchor
      · exact sparsePrefixOrientation_pattern_fiber_infinite e x hx
          allPositiveOrientationPattern
      · intro j _
        exact sparsePrefixOrientation_pattern_fiber_infinite e x hx
          (singleNegativeOrientationPattern j)

/-- Translate a sparse prefix orientation by an arbitrary common base orientation. -/
def basedSparsePrefixOrientation {P : Type*}
    (base : P → Bool) (e : PrefixFunctionCoordinate ↪ P)
    (x : ℕ → Bool) (p : P) : Bool :=
  Bool.xor (base p) (sparsePrefixOrientation e x p)

theorem primeDirichletSign_xor (a b : Bool) :
    primeDirichletSign (Bool.xor a b) = primeDirichletSign a * primeDirichletSign b := by
  cases a <;> cases b <;> norm_num [primeDirichletSign]

/-- A common base orientation is a nowhere-zero diagonal multiplier and hence
preserves every finite tail-independent subfamily. -/
theorem basedSparsePrefixOrientation_tailIndependent
    {I P : Type*} [Fintype I] (base : P → Bool)
    (e : PrefixFunctionCoordinate ↪ P) (x : I → ℕ → Bool)
    (hx : Function.Injective x) :
    PrimeOrientationTailIndependent (fun i => basedSparsePrefixOrientation base e (x i)) := by
  have htail := sparsePrefixOrientation_tailIndependent e x hx
  have hweighted := (tailCoefficientIndependent_commonWeight_iff
    (fun i p => primeDirichletSign (sparsePrefixOrientation e (x i) p))
    (fun p => primeDirichletSign (base p))
    (fun p => primeDirichletSign_ne_zero (base p))).2 htail
  simpa only [PrimeOrientationTailIndependent, basedSparsePrefixOrientation,
    primeDirichletSign_xor] using hweighted

/-- Squared weighted distance between two Boolean orientations. -/
def weightedOrientationDistanceSq {P : Type*}
    (r : P → ℝ) (a b : P → Bool) : ℝ :=
  ∑' p, if a p = b p then 0 else 4 * r p ^ (2 : ℕ)

/-- Total coherence budget carried by the sparse embedding range. -/
def sparseCoherenceBudget {P : Type*}
    (r : P → ℝ) (e : PrefixFunctionCoordinate ↪ P) : ℝ :=
  ∑' p, (Set.range e).indicator (fun p => 4 * r p ^ (2 : ℕ)) p

/-- A mismatch supported in a set of total budget below `B` has weighted
squared distance below `B`. -/
theorem weightedOrientationDistanceSq_lt_of_mismatch_subset
    {P : Type*} (r : P → ℝ) (a b : P → Bool) (S : Set P) (B : ℝ)
    (hsum : Summable fun p => S.indicator (fun p => 4 * r p ^ (2 : ℕ)) p)
    (hsupport : ∀ p, a p ≠ b p → p ∈ S)
    (hbudget : (∑' p, S.indicator (fun p => 4 * r p ^ (2 : ℕ)) p) < B) :
    weightedOrientationDistanceSq r a b < B := by
  classical
  let f : P → ℝ := fun p => if a p = b p then 0 else 4 * r p ^ (2 : ℕ)
  let g : P → ℝ := fun p => S.indicator (fun p => 4 * r p ^ (2 : ℕ)) p
  have hfnonneg : ∀ p, 0 ≤ f p := by
    intro p
    simp only [f]
    split <;> positivity
  have hle : ∀ p, f p ≤ g p := by
    intro p
    simp only [f, g]
    by_cases hab : a p = b p
    · rw [if_pos hab]
      by_cases hp : p ∈ S
      · rw [Set.indicator_of_mem hp]
        positivity
      · simp [hp]
    · rw [if_neg hab]
      simp only [Set.indicator_of_mem (hsupport p hab)]
      exact le_rfl
  have hfsum : Summable f := Summable.of_nonneg_of_le hfnonneg hle hsum
  exact lt_of_le_of_lt (hfsum.tsum_le_tsum hle hsum) hbudget

theorem basedSparsePrefixOrientation_mismatch_mem_range
    {P : Type*} (base : P → Bool) (e : PrefixFunctionCoordinate ↪ P)
    (x : ℕ → Bool) (p : P)
    (hneq : basedSparsePrefixOrientation base e x p ≠ base p) :
    p ∈ Set.range e := by
  classical
  by_contra hp
  have hsparse : sparsePrefixOrientation e x p = false := by
    simp [sparsePrefixOrientation, hp]
  apply hneq
  simp [basedSparsePrefixOrientation, hsparse]

theorem basedSparsePrefixOrientation_pair_mismatch_mem_range
    {P : Type*} (base : P → Bool) (e : PrefixFunctionCoordinate ↪ P)
    (x y : ℕ → Bool) (p : P)
    (hneq : basedSparsePrefixOrientation base e x p ≠
      basedSparsePrefixOrientation base e y p) :
    p ∈ Set.range e := by
  classical
  by_contra hp
  have hx : sparsePrefixOrientation e x p = false := by
    simp [sparsePrefixOrientation, hp]
  have hy : sparsePrefixOrientation e y p = false := by
    simp [sparsePrefixOrientation, hp]
  apply hneq
  simp [basedSparsePrefixOrientation, hx, hy]

/-- Every transported family member lies in the sparse coherence ball about
the chosen base. -/
theorem basedSparsePrefixOrientation_distance_base_lt
    {P : Type*} (base : P → Bool) (e : PrefixFunctionCoordinate ↪ P)
    (r : P → ℝ) (x : ℕ → Bool) (B : ℝ)
    (hsum : Summable fun p => (Set.range e).indicator (fun p => 4 * r p ^ (2 : ℕ)) p)
    (hbudget : sparseCoherenceBudget r e < B) :
    weightedOrientationDistanceSq r (basedSparsePrefixOrientation base e x) base < B := by
  apply weightedOrientationDistanceSq_lt_of_mismatch_subset r _ _ (Set.range e) B
    hsum (basedSparsePrefixOrientation_mismatch_mem_range base e x)
  exact hbudget

/-- Every two transported family members are mutually close under the same
sparse coherence budget. -/
theorem basedSparsePrefixOrientation_pair_distance_lt
    {P : Type*} (base : P → Bool) (e : PrefixFunctionCoordinate ↪ P)
    (r : P → ℝ) (x y : ℕ → Bool) (B : ℝ)
    (hsum : Summable fun p => (Set.range e).indicator (fun p => 4 * r p ^ (2 : ℕ)) p)
    (hbudget : sparseCoherenceBudget r e < B) :
    weightedOrientationDistanceSq r (basedSparsePrefixOrientation base e x)
      (basedSparsePrefixOrientation base e y) < B := by
  apply weightedOrientationDistanceSq_lt_of_mismatch_subset r _ _ (Set.range e) B
    hsum (basedSparsePrefixOrientation_pair_mismatch_mem_range base e x y)
  exact hbudget

/-- On prime coordinates, every finite injective prefix subfamily and every
finite shift palette with distinct real parts is differentially independent over
the finite-prime rational coefficient field. -/
theorem basedSparsePrefix_signedPrimeShiftPalette_differentialIndependent
    {I A : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (base : Nat.Primes → Bool) (e : PrefixFunctionCoordinate ↪ Nat.Primes)
    (x : I → ℕ → Bool) (hx : Function.Injective x)
    (alpha : A → ℂ) (hdistinct : Function.Injective (fun a => (alpha a).re)) :
    GaloisForLFunctions.DifferentialIndependent finitePrimeRationalCoefficientField
      (fun ia : I × A => signedPrimeShiftCarrier
        (basedSparsePrefixOrientation base e (x ia.1)) (alpha ia.2)) := by
  apply (signedPrimeShiftPalette_differentialIndependent_iff
    (fun i => basedSparsePrefixOrientation base e (x i)) alpha hdistinct).2
  exact basedSparsePrefixOrientation_tailIndependent base e x hx

/-- Summability of the squared weighted Boolean mismatch distance. -/
def WeightedOrientationDistanceSummable {P : Type*}
    (r : P → ℝ) (a b : P → Bool) : Prop :=
  Summable fun p => if a p = b p then 0 else 4 * r p ^ (2 : ℕ)

/-- **Positive-floor branch of the coherence dichotomy.**  If every coordinate
weight is bounded below in absolute value by one positive constant, weighted
square distance is summable exactly when the two orientations differ at only
finitely many coordinates. -/
theorem weightedOrientationDistanceSummable_iff_mismatch_finite_of_floor
    {P : Type*} (r : P → ℝ) (a b : P → Bool) (c : ℝ)
    (hc : 0 < c) (hfloor : ∀ p, c ≤ |r p|) :
    WeightedOrientationDistanceSummable r a b ↔ {p | a p ≠ b p}.Finite := by
  let f : P → ℝ := fun p => if a p = b p then 0 else 4 * r p ^ (2 : ℕ)
  constructor
  · intro hsum
    have heps : 0 < 4 * c ^ (2 : ℕ) := by positivity
    have hev : ∀ᶠ p in Filter.cofinite, f p ∈ Metric.ball 0 (4 * c ^ (2 : ℕ)) :=
      hsum.tendsto_cofinite_zero.eventually (Metric.ball_mem_nhds 0 heps)
    have hbad : {p | ¬f p ∈ Metric.ball 0 (4 * c ^ (2 : ℕ))}.Finite :=
      Filter.eventually_cofinite.mp hev
    apply hbad.subset
    intro p hp
    simp only [Set.mem_setOf_eq] at hp ⊢
    have hsq : c ^ (2 : ℕ) ≤ r p ^ (2 : ℕ) := by
      have := (sq_le_sq₀ hc.le (abs_nonneg (r p))).2 (hfloor p)
      simpa [sq_abs] using this
    simp only [f, if_neg hp, Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
    have hnonneg : 0 ≤ 4 * r p ^ (2 : ℕ) := by positivity
    rw [abs_of_nonneg hnonneg]
    nlinarith
  · intro hfinite
    apply summable_of_hasFiniteSupport
    apply hfinite.subset
    intro p hp
    change f p ≠ 0 at hp
    simp only [Set.mem_setOf_eq]
    intro hab
    apply hp
    simp [f, hab]

end

end GaloisForLFunctions.HTGeometry
