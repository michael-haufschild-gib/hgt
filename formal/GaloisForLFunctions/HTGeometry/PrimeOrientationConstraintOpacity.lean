import GaloisForLFunctions.HTGeometry.PrimeDirichletTailPattern

/-!
# Prime-orientation constraint opacity

The tail differential matroid of a finite family of signed prime orientations depends only on the
linear span of its recurring Boolean patterns.  This file isolates a minimal anchored pattern
skeleton which already forces maximal tail rank.  Arbitrarily many additional recurring patterns
may be imposed without changing that rank.

The final construction realizes any prescribed set of finite Boolean patterns exactly: take the
coordinate set to be the prescribed patterns times `ℕ`, and repeat each pattern infinitely often.
Thus the whole interval of pattern constraints containing the anchored skeleton has one maximal
tail matroid, even though its nonlinear constraint geometry may vary.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The all-positive pattern on an orientation family. -/
def allPositiveOrientationPattern {J : Type*} : J → Bool := fun _ => false

/-- The pattern with exactly one negative coordinate. -/
def singleNegativeOrientationPattern {J : Type*} [DecidableEq J] (j : J) : J → Bool :=
  fun k => decide (k = j)

@[simp]
theorem primeDirichletSign_singleNegativeOrientationPattern_same
    {J : Type*} [DecidableEq J] (j : J) :
    primeDirichletSign (singleNegativeOrientationPattern j j) = -1 := by
  simp [singleNegativeOrientationPattern]

theorem primeDirichletSign_singleNegativeOrientationPattern_ne
    {J : Type*} [DecidableEq J] {j k : J} (h : k ≠ j) :
    primeDirichletSign (singleNegativeOrientationPattern j k) = 1 := by
  simp [singleNegativeOrientationPattern, h]

/-- **Anchored pattern skeleton span law.**  Recurrence of the all-positive pattern and of every
single-negative pattern away from one distinguished coordinate forces the recurring patterns to
span the entire finite coefficient space.  The distinguished coordinate itself is recovered from
the all-positive equation. -/
theorem recurringPatternsSpan_of_anchoredSkeleton
    {J P : Type*} [Fintype J] [DecidableEq J]
    (ε : J → P → Bool) (anchor : J)
    (hall : {p | primeOrientationPattern ε p = allPositiveOrientationPattern}.Infinite)
    (hsingle : ∀ j, j ≠ anchor →
      {p | primeOrientationPattern ε p = singleNegativeOrientationPattern j}.Infinite) :
    RecurringPrimeOrientationPatternsSpan ε := by
  classical
  intro c hrec
  have hsum : ∑ j, c j = 0 := by
    have h := hrec allPositiveOrientationPattern hall
    simpa [allPositiveOrientationPattern, primeDirichletSign] using h
  have hoff : ∀ j, j ≠ anchor → c j = 0 := by
    intro j hj
    have h := hrec (singleNegativeOrientationPattern j) (hsingle j hj)
    have hformula :
        (∑ k, c k * primeDirichletSign (singleNegativeOrientationPattern j k)) =
          (∑ k, c k) - 2 * c j := by
      rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ j)]
      rw [primeDirichletSign_singleNegativeOrientationPattern_same]
      have hrest :
          (∑ k ∈ (Finset.univ : Finset J) \ {j},
              c k * primeDirichletSign (singleNegativeOrientationPattern j k)) =
            ∑ k ∈ (Finset.univ : Finset J) \ {j}, c k := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkj : k ≠ j := by simpa using (Finset.mem_sdiff.mp hk).2
        rw [primeDirichletSign_singleNegativeOrientationPattern_ne hkj]
        ring
      rw [hrest]
      rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem (Finset.mem_univ j)]
      ring
    rw [hformula, hsum] at h
    simpa using h
  funext j
  by_cases hj : j = anchor
  · subst j
    have hsumAnchor : (∑ k, c k) = c anchor := by
      rw [Finset.sum_eq_single anchor]
      · intro k _ hk
        exact hoff k hk
      · simp
    exact hsumAnchor ▸ hsum
  · exact hoff j hj

/-- The anchored recurring-pattern skeleton forces maximal tail coefficient independence. -/
theorem primeOrientationTailIndependent_of_anchoredSkeleton
    {J P : Type*} [Fintype J] [DecidableEq J]
    (ε : J → P → Bool) (anchor : J)
    (hall : {p | primeOrientationPattern ε p = allPositiveOrientationPattern}.Infinite)
    (hsingle : ∀ j, j ≠ anchor →
      {p | primeOrientationPattern ε p = singleNegativeOrientationPattern j}.Infinite) :
    PrimeOrientationTailIndependent ε := by
  rw [primeOrientationTailIndependent_iff_recurringPatternsSpan]
  exact recurringPatternsSpan_of_anchoredSkeleton ε anchor hall hsingle

/-- Repeat every member of a prescribed Boolean-pattern constraint countably often. -/
def constraintOrientation {J : Type*} (R : Set (J → Bool))
    (j : J) (p : R × ℕ) : Bool := p.1.1 j

@[simp]
theorem primeOrientationPattern_constraintOrientation
    {J : Type*} [Fintype J] (R : Set (J → Bool)) (p : R × ℕ) :
    primeOrientationPattern (constraintOrientation R) p = p.1.1 := by
  rfl

/-- The recurring patterns of the exact constraint realization are precisely the prescribed
patterns. -/
theorem constraintOrientation_pattern_fiber_infinite_iff
    {J : Type*} [Fintype J] (R : Set (J → Bool)) (b : J → Bool) :
    {p : R × ℕ | primeOrientationPattern (constraintOrientation R) p = b}.Infinite ↔
      b ∈ R := by
  constructor
  · intro hinf
    obtain ⟨p, hp⟩ := hinf.nonempty
    have hpb : p.1.1 = b := by
      change primeOrientationPattern (constraintOrientation R) p = b at hp
      simpa only [primeOrientationPattern_constraintOrientation] using hp
    rw [← hpb]
    exact p.1.2
  · intro hb
    let f : ℕ → R × ℕ := fun n => (⟨b, hb⟩, n)
    have hf : Function.Injective f := by
      intro m n hmn
      exact congrArg Prod.snd hmn
    apply (Set.infinite_range_of_injective hf).mono
    intro p hp
    obtain ⟨n, rfl⟩ := hp
    simp [f]

/-- Every finite nonlinear pattern constraint containing the anchored skeleton has the same
maximal tail matroid. -/
theorem constraintOrientation_tailIndependent_of_anchoredSkeleton
    {J : Type*} [Fintype J] [DecidableEq J]
    (R : Set (J → Bool)) (anchor : J)
    (hall : allPositiveOrientationPattern ∈ R)
    (hsingle : ∀ j, j ≠ anchor → singleNegativeOrientationPattern j ∈ R) :
    PrimeOrientationTailIndependent (constraintOrientation R) := by
  apply primeOrientationTailIndependent_of_anchoredSkeleton _ anchor
  · exact (constraintOrientation_pattern_fiber_infinite_iff R _).2 hall
  · intro j hj
    exact (constraintOrientation_pattern_fiber_infinite_iff R _).2 (hsingle j hj)

/-- If every allowed pattern is positive at the anchor, the anchor orientation in the exact
constraint realization is identically positive. -/
theorem constraintOrientation_anchor_eq_false
    {J : Type*} (R : Set (J → Bool)) (anchor : J)
    (hanchor : ∀ b ∈ R, b anchor = false) :
    ∀ p : R × ℕ, constraintOrientation R anchor p = false := by
  intro p
  exact hanchor p.1.1 p.1.2

/-- Realize a prescribed pattern constraint on one infinite reservoir while keeping an independent
infinite background identically all-positive. -/
def backgroundConstraintOrientation {J : Type*} (R : Set (J → Bool))
    (j : J) (p : ℕ ⊕ (R × ℕ)) : Bool :=
  match p with
  | Sum.inl _ => false
  | Sum.inr q => q.1.1 j

@[simp]
theorem primeOrientationPattern_backgroundConstraintOrientation_inl
    {J : Type*} [Fintype J] (R : Set (J → Bool)) (n : ℕ) :
    primeOrientationPattern (backgroundConstraintOrientation R) (Sum.inl n) =
      allPositiveOrientationPattern := by
  rfl

@[simp]
theorem primeOrientationPattern_backgroundConstraintOrientation_inr
    {J : Type*} [Fintype J] (R : Set (J → Bool)) (q : R × ℕ) :
    primeOrientationPattern (backgroundConstraintOrientation R) (Sum.inr q) = q.1.1 := by
  rfl

/-- If the all-positive pattern is allowed, adding an infinite all-positive background does not
change the exact set of recurring patterns. -/
theorem backgroundConstraintOrientation_pattern_fiber_infinite_iff
    {J : Type*} [Fintype J] (R : Set (J → Bool))
    (hall : allPositiveOrientationPattern ∈ R) (b : J → Bool) :
    {p : ℕ ⊕ (R × ℕ) |
      primeOrientationPattern (backgroundConstraintOrientation R) p = b}.Infinite ↔
      b ∈ R := by
  constructor
  · intro hinf
    obtain ⟨p, hp⟩ := hinf.nonempty
    cases p with
    | inl n =>
        have hb : allPositiveOrientationPattern = b := by simpa using hp
        exact hb ▸ hall
    | inr q =>
        have hqb : q.1.1 = b := by simpa using hp
        exact hqb ▸ q.1.2
  · intro hb
    let f : ℕ → ℕ ⊕ (R × ℕ) := fun n => Sum.inr (⟨b, hb⟩, n)
    have hf : Function.Injective f := by
      intro m n hmn
      exact congrArg (fun p => p.elim (fun _ => 0) fun q => q.2) hmn
    apply (Set.infinite_range_of_injective hf).mono
    intro p hp
    obtain ⟨n, rfl⟩ := hp
    simp [f]

/-- The sparse-background realization retains maximal tail independence whenever its prescribed
constraint contains the anchored skeleton. -/
theorem backgroundConstraintOrientation_tailIndependent_of_anchoredSkeleton
    {J : Type*} [Fintype J] [DecidableEq J]
    (R : Set (J → Bool)) (anchor : J)
    (hall : allPositiveOrientationPattern ∈ R)
    (hsingle : ∀ j, j ≠ anchor → singleNegativeOrientationPattern j ∈ R) :
    PrimeOrientationTailIndependent (backgroundConstraintOrientation R) := by
  apply primeOrientationTailIndependent_of_anchoredSkeleton _ anchor
  · exact (backgroundConstraintOrientation_pattern_fiber_infinite_iff R hall _).2 hall
  · intro j hj
    exact (backgroundConstraintOrientation_pattern_fiber_infinite_iff R hall _).2 (hsingle j hj)

/-- If every allowed pattern is positive at the anchor, the sparse-background anchor is exactly
the all-positive orientation. -/
theorem backgroundConstraintOrientation_anchor_eq_false
    {J : Type*} (R : Set (J → Bool)) (anchor : J)
    (hanchor : ∀ b ∈ R, b anchor = false) :
    ∀ p : ℕ ⊕ (R × ℕ), backgroundConstraintOrientation R anchor p = false := by
  intro p
  cases p with
  | inl n => rfl
  | inr q => exact hanchor q.1.1 q.1.2

end

end GaloisForLFunctions.HTGeometry
