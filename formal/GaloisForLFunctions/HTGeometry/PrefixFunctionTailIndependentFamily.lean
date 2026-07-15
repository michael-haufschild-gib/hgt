import GaloisForLFunctions.HTGeometry.PrimeOrientationConstraintOpacity

/-!
# Prefix-function tail-independent family

This module formalizes the explicit continuum-indexed family used in the
coherence-local saturation argument.  A coordinate consists of a finite binary
prefix length `n` and a Boolean function on all length-`n` prefixes.  Evaluating
that function on the prefix of an infinite Boolean sequence gives one
orientation.

For every finite family of distinct infinite sequences, sufficiently long
prefixes separate the family.  Consequently every Boolean pattern on the
family occurs at infinitely many coordinates.  The recurring-pattern criterion
then gives linear independence modulo finite support.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A finite binary-prefix length together with a Boolean function on all
prefixes of that length. -/
def PrefixFunctionCoordinate := Σ n : ℕ, (Fin n → Bool) → Bool

/-- Restriction of an infinite Boolean sequence to its first `n` entries. -/
def binaryPrefix (x : ℕ → Bool) (n : ℕ) : Fin n → Bool := fun i => x i

/-- The prefix-function orientation indexed by one infinite Boolean sequence. -/
def prefixFunctionOrientation (x : ℕ → Bool) (p : PrefixFunctionCoordinate) : Bool :=
  p.2 (binaryPrefix x p.1)

/-- A coordinate at which two distinct members of an injectively indexed
sequence family differ. -/
noncomputable def prefixDifferenceIndex {I : Type*} (x : I → ℕ → Bool)
    (hx : Function.Injective x) (i j : I) (hij : i ≠ j) : ℕ :=
  Classical.choose ((Function.ne_iff.mp (hx.ne hij)))

theorem prefixDifferenceIndex_spec {I : Type*} (x : I → ℕ → Bool)
    (hx : Function.Injective x) (i j : I) (hij : i ≠ j) :
    x i (prefixDifferenceIndex x hx i j hij) ≠
      x j (prefixDifferenceIndex x hx i j hij) :=
  Classical.choose_spec ((Function.ne_iff.mp (hx.ne hij)))

/-- One length beyond every first coordinate selected to separate a finite
sequence family. -/
noncomputable def prefixSeparationBound {I : Type*} [Fintype I]
    (x : I → ℕ → Bool) (hx : Function.Injective x) : ℕ := by
  classical
  exact Finset.univ.sup fun i => Finset.univ.sup fun j =>
    if hij : i ≠ j then prefixDifferenceIndex x hx i j hij + 1 else 0

theorem prefixDifferenceIndex_lt_separationBound
    {I : Type*} [Fintype I] (x : I → ℕ → Bool) (hx : Function.Injective x)
    {i j : I} (hij : i ≠ j) :
    prefixDifferenceIndex x hx i j hij < prefixSeparationBound x hx := by
  classical
  let k := prefixDifferenceIndex x hx i j hij
  calc
    k < k + 1 := Nat.lt_succ_self k
    _ ≤ Finset.univ.sup (fun j' =>
        if hij' : i ≠ j' then prefixDifferenceIndex x hx i j' hij' + 1 else 0) := by
      have h := Finset.le_sup (f := fun j' =>
        if hij' : i ≠ j' then prefixDifferenceIndex x hx i j' hij' + 1 else 0)
        (Finset.mem_univ j)
      simpa [hij, k] using h
    _ ≤ prefixSeparationBound x hx := by
      exact Finset.le_sup (f := fun i' => Finset.univ.sup fun j' =>
        if hij' : i' ≠ j' then prefixDifferenceIndex x hx i' j' hij' + 1 else 0)
        (Finset.mem_univ i)

/-- At every sufficiently long prefix length, an injective finite sequence
family remains injective after prefix restriction. -/
theorem binaryPrefix_injective_of_separationBound_le
    {I : Type*} [Fintype I] (x : I → ℕ → Bool) (hx : Function.Injective x)
    {n : ℕ} (hn : prefixSeparationBound x hx ≤ n) :
    Function.Injective (fun i => binaryPrefix (x i) n) := by
  intro i j hpref
  by_contra hij
  let k := prefixDifferenceIndex x hx i j hij
  have hk : k < n :=
    lt_of_lt_of_le (prefixDifferenceIndex_lt_separationBound x hx hij) hn
  have hvalue := congrFun hpref (⟨k, hk⟩ : Fin n)
  exact prefixDifferenceIndex_spec x hx i j hij hvalue

/-- A Boolean function on length-`n` prefixes realizing a prescribed pattern
on a finite family. -/
noncomputable def prefixPatternFunction {I : Type*} (x : I → ℕ → Bool)
    (b : I → Bool) (n : ℕ) : (Fin n → Bool) → Bool := by
  classical
  exact fun y => if h : ∃ i, binaryPrefix (x i) n = y then b h.choose else false

theorem prefixPatternFunction_apply {I : Type*} (x : I → ℕ → Bool)
    (b : I → Bool) (n : ℕ)
    (hinj : Function.Injective (fun i => binaryPrefix (x i) n)) (i : I) :
    prefixPatternFunction x b n (binaryPrefix (x i) n) = b i := by
  classical
  let h : ∃ j, binaryPrefix (x j) n = binaryPrefix (x i) n := ⟨i, rfl⟩
  rw [prefixPatternFunction, dif_pos h]
  congr 1
  exact hinj (Classical.choose_spec h)

/-- Every Boolean pattern on a finite injective sequence family occurs at
infinitely many prefix-function coordinates. -/
theorem prefixFunctionOrientation_pattern_fiber_infinite
    {I : Type*} [Fintype I] (x : I → ℕ → Bool) (hx : Function.Injective x)
    (b : I → Bool) :
    {p : PrefixFunctionCoordinate |
      primeOrientationPattern (fun i => prefixFunctionOrientation (x i)) p = b}.Infinite := by
  let N := prefixSeparationBound x hx
  let f : ℕ → PrefixFunctionCoordinate := fun k =>
    ⟨N + k, prefixPatternFunction x b (N + k)⟩
  have hf : Function.Injective f := by
    intro k l hkl
    have hfst := congrArg Sigma.fst hkl
    dsimp [f] at hfst
    omega
  apply Set.infinite_of_injective_forall_mem hf
  intro k
  change (fun i => prefixFunctionOrientation (x i) (f k)) = b
  funext i
  apply prefixPatternFunction_apply
  apply binaryPrefix_injective_of_separationBound_le x hx
  exact Nat.le_add_right N k

/-- Every finite injective subfamily of the prefix-function construction is
linearly independent modulo finite support. -/
theorem prefixFunctionOrientation_tailIndependent
    {I : Type*} [Fintype I] (x : I → ℕ → Bool) (hx : Function.Injective x) :
    PrimeOrientationTailIndependent (fun i => prefixFunctionOrientation (x i)) := by
  classical
  cases isEmpty_or_nonempty I with
  | inl _ =>
      intro c _
      exact Subsingleton.elim c 0
  | inr hI =>
      let anchor : I := Classical.choice hI
      apply primeOrientationTailIndependent_of_anchoredSkeleton
        (fun i => prefixFunctionOrientation (x i)) anchor
      · exact prefixFunctionOrientation_pattern_fiber_infinite x hx
          allPositiveOrientationPattern
      · intro j _
        exact prefixFunctionOrientation_pattern_fiber_infinite x hx
          (singleNegativeOrientationPattern j)

end

end GaloisForLFunctions.HTGeometry
