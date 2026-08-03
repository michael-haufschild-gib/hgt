import GaloisForLFunctions.RHTower.SelfDualAnalyticRealZeros
import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
import Mathlib.Data.Nat.Cast.Basic

noncomputable section

namespace GaloisForLFunctions.RHTower

section SupportMultiplicityFracture

variable {ι : Type*}

/-- Coordinate-rank vector of the fixed Real-corona idempotent: one at every occupied real
zero coordinate, independently of its analytic multiplicity. -/
def realCoronaKZeroSupportVector (q : ι →₀ ℕ) : ι →₀ ℕ :=
  Finsupp.mapRange (fun n : ℕ => if n = 0 then 0 else 1) (by simp) q

@[simp] theorem realCoronaKZeroSupportVector_apply (q : ι →₀ ℕ) (i : ι) :
    realCoronaKZeroSupportVector q i = if q i = 0 then 0 else 1 := by
  simp [realCoronaKZeroSupportVector, Finsupp.mapRange_apply]

theorem realCoronaKZeroSupportVector_support (q : ι →₀ ℕ) :
    (realCoronaKZeroSupportVector q).support = q.support := by
  ext i
  simp [Finsupp.mem_support_iff]

/-- Reduced finite-coordinate realization of the fixed Real-corona idempotent. -/
def realCoronaFixedCoordinateIdempotent (q : ι →₀ ℕ) : ι → ℂ :=
  fun i => if q i = 0 then 0 else 1

theorem realCoronaFixedCoordinateIdempotent_isIdempotent (q : ι →₀ ℕ) :
    IsIdempotentElem (realCoronaFixedCoordinateIdempotent q) := by
  rw [IsIdempotentElem]
  funext i
  by_cases hi : q i = 0 <;> simp [realCoronaFixedCoordinateIdempotent, hi]

/-- Scalar evaluation ranks of the concrete coordinate idempotent are exactly its support vector. -/
theorem realCoronaKZeroSupportVector_eq_coordinate_rank
    (q : ι →₀ ℕ) (i : ι) :
    realCoronaKZeroSupportVector q i =
      if realCoronaFixedCoordinateIdempotent q i = 0 then 0 else 1 := by
  by_cases hi : q i = 0 <;>
    simp [realCoronaKZeroSupportVector_apply, realCoronaFixedCoordinateIdempotent, hi]

def fixedSectorKZeroRank (q : ι →₀ ℕ) : ℕ :=
  fixedSectorDefectRank (realCoronaKZeroSupportVector q)

theorem fixedSectorKZeroRank_eq_support_card (q : ι →₀ ℕ) :
    fixedSectorKZeroRank q = q.support.card := by
  rw [fixedSectorKZeroRank, fixedSectorDefectRank, Finsupp.sum,
    realCoronaKZeroSupportVector_support, Finset.card_eq_sum_ones]
  apply Finset.sum_congr rfl
  intro i hi
  simp [realCoronaKZeroSupportVector_apply, Finsupp.mem_support_iff.mp hi]

/-- Multiplicity retained by cyclic pairing but discarded by ordinary coordinate K-zero. -/
def fixedSectorMultiplicityExcess (q : ι →₀ ℕ) : ℕ :=
  ∑ i ∈ q.support, (q i - 1)

/-- Support--multiplicity fracture: cyclic defect equals ordinary K-zero support rank plus the
exact multiplicity excess. -/
theorem fixedSectorDefectRank_eq_kZeroRank_add_multiplicityExcess (q : ι →₀ ℕ) :
    fixedSectorDefectRank q = fixedSectorKZeroRank q + fixedSectorMultiplicityExcess q := by
  rw [fixedSectorDefectRank, Finsupp.sum, fixedSectorKZeroRank_eq_support_card,
    fixedSectorMultiplicityExcess, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hpos : 1 ≤ q i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
  omega

theorem fixedSectorMultiplicityExcess_eq_zero_iff (q : ι →₀ ℕ) :
    fixedSectorMultiplicityExcess q = 0 ↔ ∀ i, q i ≤ 1 := by
  rw [fixedSectorMultiplicityExcess, Finset.sum_eq_zero_iff]
  constructor
  · intro h i
    by_cases hi : i ∈ q.support
    · have hz := h i hi
      omega
    · rw [Finsupp.notMem_support_iff.mp hi]
      omega
  · intro h i _
    exact Nat.sub_eq_zero_of_le (h i)

theorem fixedSectorDefectRank_eq_kZeroRank_iff (q : ι →₀ ℕ) :
    fixedSectorDefectRank q = fixedSectorKZeroRank q ↔ ∀ i, q i ≤ 1 := by
  rw [fixedSectorDefectRank_eq_kZeroRank_add_multiplicityExcess]
  constructor
  · intro h
    apply (fixedSectorMultiplicityExcess_eq_zero_iff q).mp
    omega
  · intro h
    rw [(fixedSectorMultiplicityExcess_eq_zero_iff q).mpr h, add_zero]

/-- At the functional-equation center, the evaluation K-zero rank equals analytic rank precisely
for central multiplicity zero or one. -/
theorem realCoronaKZeroSupportVector_eq_analyticRankAt_iff
    [DecidableEq ι] (center : ι) (q : ι →₀ ℕ) :
    realCoronaKZeroSupportVector q center = analyticRankAt center q ↔ q center ≤ 1 := by
  rw [analyticRankAt, realCoronaKZeroSupportVector_apply]
  by_cases hzero : q center = 0
  · simp [hzero]
  · simp only [hzero, if_false]
    omega

/-! ### Genuine Grothendieck group of finite coordinate projective ranks -/

/-- K-zero of the finite-coordinate projective-rank monoid.  For a finite product of complex
coordinate algebras, a projective module is classified by this finite-support dimension vector. -/
abbrev FiniteCoordinateKZero (ι : Type*) :=
  Algebra.GrothendieckAddGroup (ι →₀ ℕ)

def realCoronaFixedKZeroClass (q : ι →₀ ℕ) : FiniteCoordinateKZero ι :=
  Algebra.GrothendieckAddGroup.of (realCoronaKZeroSupportVector q)

def finiteCoordinateRankMonoidHom : (ι →₀ ℕ) →+ ℤ where
  toFun q := q.sum fun _ n => (n : ℤ)
  map_zero' := by simp
  map_add' q r := by
    exact Finsupp.sum_add_index' (by simp) (by simp)

def finiteCoordinateKZeroRank : FiniteCoordinateKZero ι →+ ℤ :=
  Algebra.GrothendieckAddGroup.lift finiteCoordinateRankMonoidHom

def finiteCoordinateEvaluationMonoidHom (i : ι) : (ι →₀ ℕ) →+ ℤ where
  toFun q := q i
  map_zero' := by simp
  map_add' q r := by simp

def finiteCoordinateKZeroEvaluationRank (i : ι) : FiniteCoordinateKZero ι →+ ℤ :=
  Algebra.GrothendieckAddGroup.lift (finiteCoordinateEvaluationMonoidHom i)

theorem finiteCoordinateKZeroEvaluationRank_realCoronaFixedKZeroClass
    (q : ι →₀ ℕ) (i : ι) :
    finiteCoordinateKZeroEvaluationRank i (realCoronaFixedKZeroClass q) =
      realCoronaKZeroSupportVector q i := by
  let E := (Algebra.GrothendieckAddGroup.lift :
    ((ι →₀ ℕ) →+ ℤ) ≃ (FiniteCoordinateKZero ι →+ ℤ))
  have hlift := congrArg
    (fun f : (ι →₀ ℕ) →+ ℤ => f (realCoronaKZeroSupportVector q))
    (E.symm_apply_apply (finiteCoordinateEvaluationMonoidHom i))
  change (E (finiteCoordinateEvaluationMonoidHom i))
      (Algebra.GrothendieckAddGroup.of (realCoronaKZeroSupportVector q)) =
        finiteCoordinateEvaluationMonoidHom i (realCoronaKZeroSupportVector q) at hlift
  exact hlift

theorem finiteCoordinateKZeroRank_realCoronaFixedKZeroClass (q : ι →₀ ℕ) :
    finiteCoordinateKZeroRank (realCoronaFixedKZeroClass q) = q.support.card := by
  let E := (Algebra.GrothendieckAddGroup.lift :
    ((ι →₀ ℕ) →+ ℤ) ≃ (FiniteCoordinateKZero ι →+ ℤ))
  have hlift := congrArg
    (fun f : (ι →₀ ℕ) →+ ℤ => f (realCoronaKZeroSupportVector q))
    (E.symm_apply_apply finiteCoordinateRankMonoidHom)
  change (E finiteCoordinateRankMonoidHom)
      (Algebra.GrothendieckAddGroup.of (realCoronaKZeroSupportVector q)) =
        finiteCoordinateRankMonoidHom (realCoronaKZeroSupportVector q) at hlift
  change (E finiteCoordinateRankMonoidHom)
      (Algebra.GrothendieckAddGroup.of (realCoronaKZeroSupportVector q)) = _
  rw [hlift]
  change (realCoronaKZeroSupportVector q).sum (fun _ n => (n : ℤ)) = _
  rw [Finsupp.sum, realCoronaKZeroSupportVector_support, Finset.card_eq_sum_ones,
    Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [realCoronaKZeroSupportVector_apply, Finsupp.mem_support_iff.mp hi]

end SupportMultiplicityFracture

section SelfDualSupportMultiplicity

def centralKZeroSupportRank (center : ℝ) (q : ℝ →₀ ℕ) : ℕ :=
  realCoronaKZeroSupportVector q center

def upperDistinctRealZeroRank (center : ℝ) (q : ℝ →₀ ℕ) : ℕ :=
  upperRealMultiplicity center (realCoronaKZeroSupportVector q)

theorem realCoronaKZeroSupportVector_reflection
    (center : ℝ) (q : ℝ →₀ ℕ)
    (hsymm : ∀ x, q (2 * center - x) = q x) :
    ∀ x, realCoronaKZeroSupportVector q (2 * center - x) =
      realCoronaKZeroSupportVector q x := by
  intro x
  simp [realCoronaKZeroSupportVector_apply, hsymm]

/-- Ordinary K-zero has the same orbit decomposition as cyclic multiplicity, but with every
occupied orbit counted once. -/
theorem fixedSectorKZeroRank_eq_centralSupport_add_twice_upperDistinct
    (center : ℝ) (q : ℝ →₀ ℕ)
    (hsymm : ∀ x, q (2 * center - x) = q x) :
    fixedSectorKZeroRank q =
      centralKZeroSupportRank center q + 2 * upperDistinctRealZeroRank center q := by
  exact fixedSectorDefectRank_eq_analyticRank_add_twice_upper
    center (realCoronaKZeroSupportVector q)
      (realCoronaKZeroSupportVector_reflection center q hsymm)

end SelfDualSupportMultiplicity

section AnalyticKZeroComparison

variable {T : Type*}

def CompletedSelfDualAnalyticFamily.fixedKZeroClass
    (F : CompletedSelfDualAnalyticFamily T) (t : T) : FiniteCoordinateKZero ℝ :=
  realCoronaFixedKZeroClass (F.realWindowMultiplicity t)

/-- Exact comparison requested by P4: central evaluation of the fixed Real-corona K-zero class
equals analytic rank exactly in ranks zero and one.  Higher central multiplicity is invisible to
the idempotent class and survives only in the cyclic multiplicity pairing. -/
theorem CompletedSelfDualAnalyticFamily.centralKZeroEvaluation_eq_analyticRank_iff
    (F : CompletedSelfDualAnalyticFamily T) (t : T) :
    finiteCoordinateKZeroEvaluationRank F.center (F.fixedKZeroClass t) =
        (F.toSelfDualRealZeroFamily.analyticRank t : ℤ) ↔
      F.toSelfDualRealZeroFamily.analyticRank t ≤ 1 := by
  rw [CompletedSelfDualAnalyticFamily.fixedKZeroClass,
    finiteCoordinateKZeroEvaluationRank_realCoronaFixedKZeroClass]
  norm_cast
  exact realCoronaKZeroSupportVector_eq_analyticRankAt_iff
    F.center (F.realWindowMultiplicity t)

/-- On an analytic self-dual family, the cyclic fixed defect differs from ordinary coordinate
K-zero rank by exactly the sum of multiplicity excesses. -/
theorem CompletedSelfDualAnalyticFamily.defectRank_eq_kZeroRank_add_multiplicityExcess
    (F : CompletedSelfDualAnalyticFamily T) (t : T) :
    F.toSelfDualRealZeroFamily.defectRank t =
      fixedSectorKZeroRank (F.realWindowMultiplicity t) +
        fixedSectorMultiplicityExcess (F.realWindowMultiplicity t) := by
  exact fixedSectorDefectRank_eq_kZeroRank_add_multiplicityExcess
    (F.realWindowMultiplicity t)

end AnalyticKZeroComparison

end GaloisForLFunctions.RHTower

