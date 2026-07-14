import GaloisForLFunctions.HTGeometry.TailConeFiber
import GaloisForLFunctions.HTGeometry.PrimeDirichletTailPattern

/-!
# The canonical eventual order on finite-support tail classes

Exact coordinatewise positivity is not invariant under finite-support changes, but existence of a
positive representative is invariant.  Equivalently, a real coefficient tail is positive when
the chosen representative is nonnegative outside a finite set.  This relation is a genuine
partial order on the quotient by finite support.

For Boolean prime orientations the positive part of the quotient contains exactly the tail class
of the all-positive orientation.  Pointwise atomic positivity then selects the unique all-positive
representative inside that class.  This separates coarse tail pointing from fine spectral
pointing without using a flow or a choice of representative.
-/

namespace HTGeometry

noncomputable section

/-- A coefficient function is eventually nonnegative when it has only finitely many negative
coordinates. -/
def EventuallyNonnegative {ι : Type*} (a : ι → ℝ) : Prop :=
  (negativeSupport a).Finite

/-- Eventual order before quotienting: `a ≤ b` when `b - a` is nonnegative away from finitely many
coordinates. -/
def TailEventuallyLE {ι : Type*} (a b : ι → ℝ) : Prop :=
  EventuallyNonnegative (fun i => b i - a i)

/-- Eventual nonnegativity is exactly the condition that the tail fibre meet the pointwise
positive cone. -/
theorem eventuallyNonnegative_iff_exists_positiveRepresentative
    {ι : Type*} (a : ι → ℝ) :
    EventuallyNonnegative a ↔
      ∃ b : ι → ℝ, InPositiveCone b ∧ FiniteTailEquivalent a b := by
  simpa only [EventuallyNonnegative] using
    (exists_positiveCone_finiteTailEquivalent_iff a).symm

/-- Eventual nonnegativity is invariant under finite-support tail equivalence. -/
theorem eventuallyNonnegative_congr
    {ι : Type*} {a b : ι → ℝ} (hab : FiniteTailEquivalent a b) :
    EventuallyNonnegative a ↔ EventuallyNonnegative b := by
  constructor
  · intro ha
    apply (ha.union hab).subset
    intro i hi
    simp only [negativeSupport, Set.mem_union, Set.mem_setOf_eq] at hi ⊢
    by_cases hdiff : a i ≠ b i
    · exact Or.inr hdiff
    · have heq : a i = b i := not_ne_iff.mp hdiff
      exact Or.inl (by rw [heq]; exact hi)
  · intro hb
    apply (hb.union (finiteTailEquivalent_symm hab)).subset
    intro i hi
    simp only [negativeSupport, Set.mem_union, Set.mem_setOf_eq] at hi ⊢
    by_cases hdiff : b i ≠ a i
    · exact Or.inr hdiff
    · have heq : b i = a i := not_ne_iff.mp hdiff
      exact Or.inl (by rw [heq]; exact hi)

theorem eventuallyNonnegative_zero {ι : Type*} :
    EventuallyNonnegative (fun _ : ι => 0) := by
  simp [EventuallyNonnegative, negativeSupport]

/-- The eventual positive cone is closed under addition. -/
theorem EventuallyNonnegative.add
    {ι : Type*} {a b : ι → ℝ}
    (ha : EventuallyNonnegative a) (hb : EventuallyNonnegative b) :
    EventuallyNonnegative (fun i => a i + b i) := by
  apply (ha.union hb).subset
  intro i hi
  simp only [negativeSupport, Set.mem_union, Set.mem_setOf_eq] at hi ⊢
  by_cases hai : a i < 0
  · exact Or.inl hai
  · exact Or.inr (by linarith [le_of_not_gt hai])

/-- The eventual positive cone is closed under multiplication by a nonnegative real scalar. -/
theorem EventuallyNonnegative.smul_nonneg
    {ι : Type*} {a : ι → ℝ} (ha : EventuallyNonnegative a)
    {c : ℝ} (hc : 0 ≤ c) :
    EventuallyNonnegative (fun i => c * a i) := by
  apply ha.subset
  intro i hi
  simp only [negativeSupport, Set.mem_setOf_eq] at hi ⊢
  nlinarith

/-- The eventual cone is pointed modulo finite support.  If both `a` and `-a` are eventually
nonnegative, then `a` is finitely supported and hence represents the zero tail. -/
theorem finiteTailEquivalent_zero_of_eventuallyNonnegative_neg
    {ι : Type*} {a : ι → ℝ}
    (ha : EventuallyNonnegative a)
    (hna : EventuallyNonnegative (fun i => -a i)) :
    FiniteTailEquivalent a (fun _ => 0) := by
  apply (ha.union hna).subset
  intro i hi
  simp only [negativeSupport, Set.mem_union, Set.mem_setOf_eq] at hi ⊢
  by_cases hai : a i < 0
  · exact Or.inl hai
  · have ha0 : 0 ≤ a i := le_of_not_gt hai
    have hapos : 0 < a i := lt_of_le_of_ne ha0 (Ne.symm hi)
    exact Or.inr (by linarith)

theorem tailEventuallyLE_refl {ι : Type*} (a : ι → ℝ) :
    TailEventuallyLE a a := by
  simpa [TailEventuallyLE] using (eventuallyNonnegative_zero (ι := ι))

theorem tailEventuallyLE_trans
    {ι : Type*} {a b c : ι → ℝ}
    (hab : TailEventuallyLE a b) (hbc : TailEventuallyLE b c) :
    TailEventuallyLE a c := by
  have hsum := hab.add hbc
  apply (eventuallyNonnegative_congr (a := fun i => (b i - a i) + (c i - b i))
    (b := fun i => c i - a i) ?_).mp hsum
  simp only [FiniteTailEquivalent]
  convert Set.finite_empty
  ext i
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
  ring_nf
  simp

/-- Antisymmetry holds exactly modulo finite support. -/
theorem tailEventuallyLE_antisymm
    {ι : Type*} {a b : ι → ℝ}
    (hab : TailEventuallyLE a b) (hba : TailEventuallyLE b a) :
    FiniteTailEquivalent a b := by
  apply (hab.union hba).subset
  intro i hi
  simp only [negativeSupport, Set.mem_union, Set.mem_setOf_eq] at hi ⊢
  by_cases hlt : a i < b i
  · exact Or.inr (sub_neg.mpr hlt)
  · have hle : b i ≤ a i := le_of_not_gt hlt
    exact Or.inl (sub_neg.mpr (lt_of_le_of_ne hle (Ne.symm hi)))

/-- Subtraction respects finite-support tail equivalence in both variables. -/
theorem finiteTailEquivalent_sub
    {ι : Type*} {a a' b b' : ι → ℝ}
    (ha : FiniteTailEquivalent a a') (hb : FiniteTailEquivalent b b') :
    FiniteTailEquivalent (fun i => b i - a i) (fun i => b' i - a' i) := by
  apply (ha.union hb).subset
  intro i hi
  simp only [Set.mem_union, Set.mem_setOf_eq] at hi ⊢
  by_contra hnot
  push Not at hnot
  exact hi (by rw [hnot.1, hnot.2])

/-- Eventual order is independent of both chosen representatives. -/
theorem tailEventuallyLE_congr
    {ι : Type*} {a a' b b' : ι → ℝ}
    (ha : FiniteTailEquivalent a a') (hb : FiniteTailEquivalent b b') :
    TailEventuallyLE a b ↔ TailEventuallyLE a' b' := by
  exact eventuallyNonnegative_congr (finiteTailEquivalent_sub ha hb)

/-- The setoid of real coefficient functions modulo finite-support changes. -/
def finiteTailSetoid (ι : Type*) : Setoid (ι → ℝ) where
  r := FiniteTailEquivalent
  iseqv := ⟨finiteTailEquivalent_refl, finiteTailEquivalent_symm,
    finiteTailEquivalent_trans⟩

/-- Real coefficient tails modulo finite support. -/
def RealTailQuotient (ι : Type*) := Quotient (finiteTailSetoid ι)

/-- The tail class of a representative. -/
def realTailClass {ι : Type*} (a : ι → ℝ) : RealTailQuotient ι :=
  Quotient.mk (finiteTailSetoid ι) a

@[simp]
theorem realTailClass_eq_iff {ι : Type*} (a b : ι → ℝ) :
    realTailClass a = realTailClass b ↔ FiniteTailEquivalent a b :=
  Quotient.eq_iff_equiv

/-- Eventual order descends to the tail quotient. -/
def realTailLE {ι : Type*} : RealTailQuotient ι → RealTailQuotient ι → Prop :=
  fun q r => Quotient.liftOn₂ q r TailEventuallyLE (by
    intro a b a' b' ha hb
    exact propext (tailEventuallyLE_congr ha hb))

instance {ι : Type*} : LE (RealTailQuotient ι) := ⟨realTailLE⟩

@[simp]
theorem realTailClass_le_iff {ι : Type*} (a b : ι → ℝ) :
    realTailClass a ≤ realTailClass b ↔ TailEventuallyLE a b := by
  rfl

/-- **Canonical tail-order law.**  Eventual coordinatewise order is a genuine partial order on
real coefficient tails modulo finite support. -/
instance {ι : Type*} : PartialOrder (RealTailQuotient ι) where
  le_refl q := Quotient.inductionOn q fun a => tailEventuallyLE_refl a
  le_trans q r t := Quotient.inductionOn₃ q r t fun _ _ _ => tailEventuallyLE_trans
  le_antisymm q r := Quotient.inductionOn₂ q r fun _ _ hab hba =>
    Quotient.sound (tailEventuallyLE_antisymm hab hba)

/-- Translation does not alter eventual comparisons. -/
theorem tailEventuallyLE_add_iff
    {ι : Type*} (a b c : ι → ℝ) :
    TailEventuallyLE (fun i => a i + c i) (fun i => b i + c i) ↔
      TailEventuallyLE a b := by
  apply eventuallyNonnegative_congr
  simp only [FiniteTailEquivalent]
  convert Set.finite_empty
  ext i
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
  ring_nf
  simp

/-- Multiplication by a strictly positive scalar preserves and reflects eventual comparisons. -/
theorem tailEventuallyLE_smul_iff
    {ι : Type*} (a b : ι → ℝ) {c : ℝ} (hc : 0 < c) :
    TailEventuallyLE (fun i => c * a i) (fun i => c * b i) ↔
      TailEventuallyLE a b := by
  unfold TailEventuallyLE EventuallyNonnegative negativeSupport
  have hset : {i | c * b i - c * a i < 0} = {i | b i - a i < 0} := by
    ext i
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h <;> nlinarith
  rw [hset]

/-- Eventual positivity of a Boolean prime orientation is exactly membership in the all-positive
tail class. -/
theorem primeOrientation_eventuallyNonnegative_iff_allPositiveTail
    {P : Type*} (ε : P → Bool) :
    EventuallyNonnegative
        (fun p => GaloisForLFunctions.HTGeometry.primeDirichletRealSign (ε p)) ↔
      FiniteTailEquivalent
        (fun p => GaloisForLFunctions.HTGeometry.primeDirichletRealSign (ε p))
        (fun _ => 1) := by
  unfold EventuallyNonnegative negativeSupport FiniteTailEquivalent
  have hset :
      {p | GaloisForLFunctions.HTGeometry.primeDirichletRealSign (ε p) < 0} =
      {p | GaloisForLFunctions.HTGeometry.primeDirichletRealSign (ε p) ≠ 1} := by
    ext p
    cases h : ε p <;>
      norm_num [GaloisForLFunctions.HTGeometry.primeDirichletRealSign, h]
  rw [hset]

/-- **Two-stage prime pointing law.**  The eventual cone first selects the all-positive Boolean
tail class.  For any strictly positive atomic weights, exact atomic positivity then selects the
unique all-positive representative inside that class. -/
theorem primeOrientation_twoStagePointing
    {P : Type*} (ε : P → Bool) (weight : P → ℝ)
    (hweight : ∀ p, 0 < weight p) :
    (EventuallyNonnegative
        (fun p => GaloisForLFunctions.HTGeometry.primeDirichletRealSign (ε p)) ↔
      FiniteTailEquivalent
        (fun p => GaloisForLFunctions.HTGeometry.primeDirichletRealSign (ε p))
        (fun _ => 1)) ∧
    (GaloisForLFunctions.HTGeometry.PrimeOrientationAtomicMassPositive ε weight ↔
      GaloisForLFunctions.HTGeometry.PrimeOrientationAllPositive ε) :=
  ⟨primeOrientation_eventuallyNonnegative_iff_allPositiveTail ε,
    GaloisForLFunctions.HTGeometry.primeOrientationAtomicMassPositive_iff_allPositive
      ε weight hweight⟩

end

end HTGeometry
