import GaloisForLFunctions.HTGeometry.NonautonomousProjectiveTailCollapse

/-!
# Functional--relational phase separation for projective constraints

The arithmetic capacity and one-sided collapse theorems are unconditional.  The positive
triangle and modular phases use classical existence, common-pullback, and projective-minimality
inputs.  Those named inputs are represented here by explicit witness structures: no existence
theorem is postulated as an axiom.  From any such witnesses, the exact storage laws force
unbounded relational degree to be accompanied by unbounded topology while irreducibility and
the common projective pullback persist.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Integer-valued data are unbounded above. -/
def IntUnboundedAbove {ι : Type*} (f : ι → ℤ) : Prop :=
  ∀ bound, ∃ i, bound < f i

/-- The named classical inputs for an unbounded family of torsion-free `(2,3,7)`
correspondence surfaces.  `commonPullback` records equality of the two pulled-back projective
connections and `irreducible` records Kummer minimality (hence no tensor or affine reduction). -/
structure HurwitzProjectiveSurvivalWitness (ι : Type*) where
  degree : ι → ℤ
  genus : ι → ℤ
  commonPullback : ι → Prop
  irreducible : ι → Prop
  exactStorage : ∀ i, degree i = 42 * (2 * genus i - 2)
  survives : ∀ i, commonPullback i ∧ irreducible i
  degree_unbounded : IntUnboundedAbove degree

/-- The named classical inputs for an unbounded family of torsion-free modular correspondence
surfaces.  The cusp number is retained because modular storage uses the noncompact Euler
capacity `2g+s-2`. -/
structure ModularProjectiveSurvivalWitness (ι : Type*) where
  degree : ι → ℤ
  genus : ι → ℤ
  cuspCard : ι → ℤ
  commonPullback : ι → Prop
  irreducible : ι → Prop
  exactStorage : ∀ i, degree i = 6 * (2 * genus i + cuspCard i - 2)
  survives : ∀ i, commonPullback i ∧ irreducible i
  degree_unbounded : IntUnboundedAbove degree

/-- Exact compact Hurwitz storage in the affine form used to compare two correspondence
surfaces. -/
theorem HurwitzProjectiveSurvivalWitness.degree_add_eightyFour
    {ι : Type*} (phase : HurwitzProjectiveSurvivalWitness ι) (i : ι) :
    phase.degree i + 84 = 84 * phase.genus i :=
  hurwitzTriangle_projectiveCapacity_saturates
    (phase.degree i) (phase.genus i) (phase.exactStorage i)

/-- Exact noncompact modular storage in the affine form used to compare two correspondence
surfaces. -/
theorem ModularProjectiveSurvivalWitness.degree_add_twelve
    {ι : Type*} (phase : ModularProjectiveSurvivalWitness ι) (i : ι) :
    phase.degree i + 12 = 6 * (phase.cuspCard i + 2 * phase.genus i) := by
  apply modularTriangle_projectiveCapacity_saturates
  simpa [add_comm, add_left_comm, add_assoc] using phase.exactStorage i

/-- At the sharp compact phase, correspondence degree and genus have exactly the same strict
order. -/
theorem HurwitzProjectiveSurvivalWitness.degree_lt_iff_genus_lt
    {ι : Type*} (phase : HurwitzProjectiveSurvivalWitness ι) (i j : ι) :
    phase.degree i < phase.degree j ↔ phase.genus i < phase.genus j :=
  hurwitzProjectiveStorage_order_iff
    (phase.degree i) (phase.degree j) (phase.genus i) (phase.genus j)
    (phase.degree_add_eightyFour i) (phase.degree_add_eightyFour j)

/-- At the sharp modular phase, correspondence degree and Euler storage have exactly the same
strict order. -/
theorem ModularProjectiveSurvivalWitness.degree_lt_iff_capacity_lt
    {ι : Type*} (phase : ModularProjectiveSurvivalWitness ι) (i j : ι) :
    phase.degree i < phase.degree j ↔
      phase.cuspCard i + 2 * phase.genus i <
        phase.cuspCard j + 2 * phase.genus j :=
  modularProjectiveStorage_order_iff
    (phase.degree i) (phase.degree j)
    (phase.cuspCard i + 2 * phase.genus i)
    (phase.cuspCard j + 2 * phase.genus j)
    (phase.degree_add_twelve i) (phase.degree_add_twelve j)

/-- Unbounded `(2,3,7)` relational degree forces unbounded genus. -/
theorem HurwitzProjectiveSurvivalWitness.genus_unbounded
    {ι : Type*} (phase : HurwitzProjectiveSurvivalWitness ι) :
    IntUnboundedAbove phase.genus := by
  intro bound
  obtain ⟨i, hi⟩ := phase.degree_unbounded (84 * bound - 84)
  refine ⟨i, ?_⟩
  have hexact := phase.degree_add_eightyFour i
  linarith

/-- Unbounded modular relational degree forces unbounded punctured Euler capacity. -/
theorem ModularProjectiveSurvivalWitness.capacity_unbounded
    {ι : Type*} (phase : ModularProjectiveSurvivalWitness ι) :
    IntUnboundedAbove (fun i => phase.cuspCard i + 2 * phase.genus i) := by
  intro bound
  obtain ⟨i, hi⟩ := phase.degree_unbounded (6 * bound - 12)
  refine ⟨i, ?_⟩
  have hexact := phase.degree_add_twelve i
  linarith

/-- Full functional--relational separation.  A one-sided fixed-skeleton tail is eventually
nonhyperbolic and has at most two non-orbifold fibres.  In contrast, any supplied classical
Hurwitz and modular correspondence witnesses retain common pullback and irreducibility at every
stage, with unbounded degree paid for by unbounded topological capacity. -/
theorem projectiveConstraint_functionalRelational_phaseSeparation
    {ι κ : Type*}
    (prefixDegree badFiberCard : ℕ → ℕ)
    (sourceExceptionalCard exceptionalBudget : ℕ)
    (hyperbolic : ℕ → Prop)
    (hdegree : ∀ n, 2 ^ n ≤ prefixDegree n)
    (hthreeBudget : ∀ n, 3 ≤ badFiberCard n →
      prefixDegree n + 2 ≤ sourceExceptionalCard)
    (hhyperbolicDegree : ∀ n, hyperbolic n →
      prefixDegree n ≤ 42 * exceptionalBudget)
    (hurwitz : HurwitzProjectiveSurvivalWitness ι)
    (modular : ModularProjectiveSurvivalWitness κ) :
    (∀ᶠ n in Filter.atTop, badFiberCard n ≤ 2 ∧ ¬ hyperbolic n) ∧
      IntUnboundedAbove hurwitz.genus ∧
      IntUnboundedAbove (fun i => modular.cuspCard i + 2 * modular.genus i) ∧
      (∀ i, hurwitz.commonPullback i ∧ hurwitz.irreducible i) ∧
      (∀ i, modular.commonPullback i ∧ modular.irreducible i) := by
  exact ⟨projectiveTail_eventually_nonhyperbolic_with_twoPointSkeleton
      prefixDegree badFiberCard sourceExceptionalCard exceptionalBudget hyperbolic
      hdegree hthreeBudget hhyperbolicDegree,
    hurwitz.genus_unbounded, modular.capacity_unbounded,
    hurwitz.survives, modular.survives⟩

end GaloisForLFunctions.HTGeometry
