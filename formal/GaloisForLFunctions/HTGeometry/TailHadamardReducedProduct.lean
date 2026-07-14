import GaloisForLFunctions.HTGeometry.TailEventualOrder

/-!
# The Hadamard reduced product of coefficient tails

Coefficient functions modulo finite support retain more than their linear tail matroid.  Pointwise
addition and multiplication descend, producing a commutative reduced-product algebra.  Its unit
is the all-positive coefficient tail.  Boolean orientations are involutions, and the eventual
positive cone contains exactly one Boolean involution: the unit.

For prime-supported Dirichlet series, this pointwise multiplication is the coefficientwise
Hadamard product, not ordinary multiplication of functions.  It is therefore transverse to the
ordinary differential-field operations.
-/

namespace HTGeometry

noncomputable section

/-- The ideal of finitely supported real coefficient functions. -/
def finiteSupportIdeal (ι : Type*) : Ideal (ι → ℝ) where
  carrier := {a | (Function.support a).Finite}
  zero_mem' := by
    simp [Function.support]
  add_mem' := by
    intro a b ha hb
    apply (ha.union hb).subset
    intro i hi
    simp only [Function.support, Set.mem_union, Set.mem_setOf_eq] at hi ⊢
    by_cases hai : a i = 0
    · exact Or.inr fun hbi => hi (by rw [hai, hbi, add_zero])
    · exact Or.inl hai
  smul_mem' := by
    intro c a ha
    apply ha.subset
    intro i hi
    simp only [Function.support, Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul] at hi ⊢
    intro hai
    exact hi (by rw [hai, mul_zero])

/-- The real coefficient algebra modulo finite-support changes. -/
abbrev TailHadamardReducedProduct (ι : Type*) :=
  (ι → ℝ) ⧸ finiteSupportIdeal ι

/-- The reduced-product class of a coefficient function. -/
def tailHadamardClass {ι : Type*} (a : ι → ℝ) : TailHadamardReducedProduct ι :=
  Ideal.Quotient.mk (finiteSupportIdeal ι) a

theorem support_sub_eq_neSet {ι : Type*} (a b : ι → ℝ) :
    Function.support (a - b) = {i | a i ≠ b i} := by
  ext i
  simp [Function.support, sub_ne_zero]

/-- Equality in the Hadamard reduced product is exactly finite-support tail equivalence. -/
@[simp]
theorem tailHadamardClass_eq_iff
    {ι : Type*} (a b : ι → ℝ) :
    tailHadamardClass a = tailHadamardClass b ↔ FiniteTailEquivalent a b := by
  constructor
  · intro h
    have hzero : tailHadamardClass (a - b) = 0 := by
      rw [tailHadamardClass, map_sub, h, sub_self]
    have hmem : a - b ∈ finiteSupportIdeal ι :=
      Ideal.Quotient.eq_zero_iff_mem.mp hzero
    simpa only [finiteSupportIdeal, support_sub_eq_neSet] using hmem
  · intro h
    apply sub_eq_zero.mp
    rw [← map_sub]
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    simpa only [finiteSupportIdeal, support_sub_eq_neSet] using h

@[simp]
theorem tailHadamardClass_zero {ι : Type*} :
    tailHadamardClass (fun _ : ι => 0) = 0 := by
  rfl

@[simp]
theorem tailHadamardClass_one {ι : Type*} :
    tailHadamardClass (fun _ : ι => 1) = 1 := by
  rfl

@[simp]
theorem tailHadamardClass_add
    {ι : Type*} (a b : ι → ℝ) :
    tailHadamardClass (fun i => a i + b i) =
      tailHadamardClass a + tailHadamardClass b := by
  rfl

@[simp]
theorem tailHadamardClass_mul
    {ι : Type*} (a b : ι → ℝ) :
    tailHadamardClass (fun i => a i * b i) =
      tailHadamardClass a * tailHadamardClass b := by
  rfl

/-- Positivity in the reduced product means that the class has a coordinatewise nonnegative
representative. -/
def TailHadamardPositive {ι : Type*} (q : TailHadamardReducedProduct ι) : Prop :=
  ∃ a : ι → ℝ, tailHadamardClass a = q ∧ InPositiveCone a

/-- Reduced-product positivity is exactly eventual nonnegativity of any representative. -/
theorem tailHadamardPositive_class_iff
    {ι : Type*} (a : ι → ℝ) :
    TailHadamardPositive (tailHadamardClass a) ↔ EventuallyNonnegative a := by
  constructor
  · rintro ⟨b, hb, hpos⟩
    have htail : FiniteTailEquivalent a b :=
      (tailHadamardClass_eq_iff a b).mp hb.symm
    exact (eventuallyNonnegative_iff_exists_positiveRepresentative a).mpr
      ⟨b, hpos, htail⟩
  · intro ha
    obtain ⟨b, hpos, htail⟩ :=
      (eventuallyNonnegative_iff_exists_positiveRepresentative a).mp ha
    exact ⟨b, (tailHadamardClass_eq_iff b a).mpr
      (finiteTailEquivalent_symm htail), hpos⟩

/-- The all-positive tail is the multiplicative unit for coefficientwise multiplication. -/
theorem allPositiveTail_hadamard_unit
    {ι : Type*} (a : ι → ℝ) :
    tailHadamardClass (fun i => a i * 1) = tailHadamardClass a := by
  simp

/-- The reduced-product element represented by one Boolean prime orientation. -/
def primeOrientationHadamardTail
    {P : Type*} (ε : P → Bool) : TailHadamardReducedProduct P :=
  tailHadamardClass
    (fun p => GaloisForLFunctions.HTGeometry.primeDirichletRealSign (ε p))

/-- Every Boolean orientation tail is an involution of the Hadamard reduced product. -/
theorem primeOrientationHadamardTail_sq
    {P : Type*} (ε : P → Bool) :
    primeOrientationHadamardTail ε ^ 2 = 1 := by
  rw [pow_two]
  change tailHadamardClass
      (fun p => GaloisForLFunctions.HTGeometry.primeDirichletRealSign (ε p)) *
      tailHadamardClass
      (fun p => GaloisForLFunctions.HTGeometry.primeDirichletRealSign (ε p)) = 1
  rw [← tailHadamardClass_mul]
  change tailHadamardClass
      (fun p => GaloisForLFunctions.HTGeometry.primeDirichletRealSign (ε p) *
        GaloisForLFunctions.HTGeometry.primeDirichletRealSign (ε p)) = 1
  apply (tailHadamardClass_eq_iff _ _).mpr
  simp only [FiniteTailEquivalent]
  convert Set.finite_empty
  ext p
  cases h : ε p <;>
    norm_num [GaloisForLFunctions.HTGeometry.primeDirichletRealSign, h]

/-- **Canonical positive-unit law.**  A Boolean orientation is positive in the Hadamard tail
algebra exactly when it is the multiplicative unit. -/
theorem primeOrientationHadamardTail_positive_iff_eq_one
    {P : Type*} (ε : P → Bool) :
    TailHadamardPositive (primeOrientationHadamardTail ε) ↔
      primeOrientationHadamardTail ε = 1 := by
  rw [primeOrientationHadamardTail, tailHadamardPositive_class_iff]
  constructor
  · intro hpos
    rw [← tailHadamardClass_one]
    exact (tailHadamardClass_eq_iff _ _).mpr
      ((primeOrientation_eventuallyNonnegative_iff_allPositiveTail ε).mp hpos)
  · intro hone
    have htail : FiniteTailEquivalent
        (fun p => GaloisForLFunctions.HTGeometry.primeDirichletRealSign (ε p))
        (fun _ => 1) := by
      apply (tailHadamardClass_eq_iff _ _).mp
      simpa only [tailHadamardClass_one] using hone
    exact (primeOrientation_eventuallyNonnegative_iff_allPositiveTail ε).mpr htail

/-- Bounded real coefficient tails are order-bounded by a scalar multiple of the Hadamard unit.
This is the representative form of the unit being an order unit on the bounded reduced product. -/
theorem bounded_tail_between_unit_multiples
    {ι : Type*} (a : ι → ℝ) {M : ℝ}
    (hM : ∀ i, |a i| ≤ M) :
    TailEventuallyLE (fun _ => -M) a ∧
      TailEventuallyLE a (fun _ => M) := by
  constructor
  · unfold TailEventuallyLE EventuallyNonnegative negativeSupport
    convert Set.finite_empty
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
    have hi := hM i
    constructor
    · intro h
      rw [abs_le] at hi
      linarith
    · intro h
      contradiction
  · unfold TailEventuallyLE EventuallyNonnegative negativeSupport
    convert Set.finite_empty
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
    have hi := hM i
    constructor
    · intro h
      rw [abs_le] at hi
      linarith
    · intro h
      contradiction

end

end HTGeometry
