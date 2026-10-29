import GaloisForLFunctions.HTGeometry.NumberFieldTraceCoordinates
import GaloisForLFunctions.HTGeometry.DualZLatticeCovolume
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Trace duals of weighted ideal lattices

The integer dual of a fractional ideal's trace-normalized real lattice is precisely the
conjugated weighted embedding of its arithmetic trace dual. Integral pairings against an
ideal basis determine a field element through the rational trace-dual basis; real basis
extensionality then identifies the original dual vector with that element's embedding.
-/

noncomputable section

open NumberField NumberField.InfinitePlace Module
open scoped Classical NumberField ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

variable {K : Type*} [Field K] [NumberField K]

local notation "X" => numberFieldMixedRealCoordinateIndex K → ℝ
local notation "E" => EuclideanSpace ℝ (numberFieldMixedRealCoordinateIndex K)
local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K

/-- Trace-normalized mixed coordinates, represented as a real coordinate function. -/
def numberFieldTraceRealCoordinates : mixedEmbedding.mixedSpace K ≃ₗ[ℝ] X :=
  numberFieldTraceCoordinates.toLinearEquiv.trans (WithLp.linearEquiv 2 ℝ X)

/-- The image of a nonzero fractional ideal in trace-normalized real coordinates. -/
def numberFieldTraceLattice (I : FIˣ) : Submodule ℤ X :=
  (mixedEmbedding.idealLattice K I).map
    ((numberFieldTraceRealCoordinates (K := K)).toLinearMap.restrictScalars ℤ)

theorem mem_numberFieldTraceLattice (I : FIˣ) {x : X} :
    x ∈ numberFieldTraceLattice I ↔ ∃ a : K, a ∈ (I : Set K) ∧
      numberFieldTraceRealCoordinates (mixedEmbedding K a) = x := by
  change (∃ z, z ∈ mixedEmbedding.idealLattice K I ∧ numberFieldTraceRealCoordinates z = x) ↔ _
  constructor
  · rintro ⟨z, hz, hzx⟩
    rcases (mixedEmbedding.mem_idealLattice K I).mp hz with ⟨a, ha, rfl⟩
    exact ⟨a, ha, hzx⟩
  · rintro ⟨a, ha, hax⟩
    exact ⟨mixedEmbedding K a, (mixedEmbedding.mem_idealLattice K I).mpr ⟨a, ha, rfl⟩, hax⟩

/-- The ideal's real basis in trace-normalized coordinates. -/
def numberFieldTraceLatticeBasis (I : FIˣ) :
    Basis (Free.ChooseBasisIndex ℤ I) ℝ X :=
  (mixedEmbedding.fractionalIdealLatticeBasis K I).map numberFieldTraceRealCoordinates

theorem span_numberFieldTraceLatticeBasis (I : FIˣ) :
    Submodule.span ℤ (Set.range (numberFieldTraceLatticeBasis I)) =
      numberFieldTraceLattice I := by
  rw [numberFieldTraceLattice, ← mixedEmbedding.span_idealLatticeBasis,
    Submodule.map_span, ← Set.range_comp]
  rfl

instance (I : FIˣ) : DiscreteTopology (numberFieldTraceLattice I) := by
  rw [← span_numberFieldTraceLatticeBasis]
  infer_instance

instance (I : FIˣ) : IsZLattice ℝ (numberFieldTraceLattice I) := by
  simp_rw [← span_numberFieldTraceLatticeBasis]
  infer_instance

theorem numberFieldCoordinatePair_eq_inner (x y : X) :
    DualZLattice.pair x y = inner ℝ (WithLp.toLp 2 x) (WithLp.toLp 2 y) := by
  simp only [DualZLattice.pair, PiLp.inner_apply, Real.inner_apply]

theorem numberFieldTraceRealCoordinates_pair (a b : K) :
    DualZLattice.pair
      (numberFieldTraceRealCoordinates (mixedEmbedding K a))
      (numberFieldTraceRealCoordinates (numberFieldMixedConjugation (mixedEmbedding K b))) =
        (Algebra.trace ℚ K (a * b) : ℝ) := by
  rw [numberFieldCoordinatePair_eq_inner]
  change inner ℝ (numberFieldTraceCoordinates (mixedEmbedding K a))
    (numberFieldTraceCoordinates (numberFieldMixedConjugation (mixedEmbedding K b))) = _
  exact numberField_trace_eq_weighted_inner a b

/-- The integer dual of an ideal lattice is the conjugated embedding of its trace dual. -/
theorem mem_dual_numberFieldTraceLattice (I : FIˣ) {y : X} :
    y ∈ DualZLattice.dual (numberFieldTraceLattice I) ↔
      ∃ c : K, c ∈ FractionalIdeal.dual ℤ ℚ (I : FI) ∧
        numberFieldTraceRealCoordinates
          (numberFieldMixedConjugation (mixedEmbedding K c)) = y := by
  classical
  constructor
  · intro hy
    let b := NumberField.basisOfFractionalIdeal K I
    let β := (mixedEmbedding.fractionalIdealLatticeBasis K I).map
      (numberFieldTraceCoordinates (K := K)).toLinearEquiv
    have hvals : ∀ i, ∃ m : ℤ, inner ℝ (β i) (WithLp.toLp 2 y) = m := by
      intro i
      have hi : b i ∈ (I : Set K) := by
        change NumberField.basisOfFractionalIdeal K I i ∈ (I : Set K)
        rw [NumberField.basisOfFractionalIdeal_apply]
        exact (NumberField.fractionalIdealBasis K (I : FI) i).property
      obtain ⟨m, hm⟩ := hy _ ((mem_numberFieldTraceLattice I).mpr ⟨b i, hi, rfl⟩)
      refine ⟨m, ?_⟩
      rw [numberFieldCoordinatePair_eq_inner] at hm
      change inner ℝ (numberFieldTraceCoordinates (mixedEmbedding K (b i)))
        (WithLp.toLp 2 y) = (m : ℝ) at hm
      simp only [β, Basis.map_apply, mixedEmbedding.fractionalIdealLatticeBasis_apply]
      change inner ℝ (numberFieldTraceCoordinates (mixedEmbedding K (b i)))
        (WithLp.toLp 2 y) = (m : ℝ)
      exact hm
    -- Integral pairings are rational coordinates in the trace-dual basis.
    choose m hm using hvals
    let c := b.traceDual.equivFun.symm (fun i => (m i : ℚ))
    have hc : ∀ i, Algebra.trace ℚ K (b i * c) = (m i : ℚ) := by
      intro i
      have h := congrFun (b.traceDual.equivFun.apply_symm_apply (fun i => (m i : ℚ))) i
      change b.traceDual.repr c i = (m i : ℚ) at h
      rw [b.traceDual_repr_apply] at h
      change Algebra.trace ℚ K (c * b i) = (m i : ℚ) at h
      simpa only [mul_comm] using h
    -- Equality against a full real basis recovers the original dual vector.
    have hyc : WithLp.toLp 2 y =
        numberFieldTraceCoordinates (numberFieldMixedConjugation (mixedEmbedding K c)) := by
      apply InnerProductSpace.ext_inner_left_basis β
      intro i
      rw [hm i]
      simp only [β, Basis.map_apply, mixedEmbedding.fractionalIdealLatticeBasis_apply]
      change (m i : ℝ) = inner ℝ (numberFieldTraceCoordinates (mixedEmbedding K (b i))) _
      rw [numberField_trace_eq_weighted_inner, hc i]
      exact_mod_cast rfl
    have hcy : numberFieldTraceRealCoordinates
        (numberFieldMixedConjugation (mixedEmbedding K c)) = y := by
      exact (congrArg (fun z : E => z.ofLp) hyc).symm
    refine ⟨c, (FractionalIdeal.mem_dual (Units.ne_zero I)).mpr ?_, hcy⟩
    intro a ha
    obtain ⟨m, hm⟩ := hy _ ((mem_numberFieldTraceLattice I).mpr ⟨a, ha, rfl⟩)
    rw [← hcy, numberFieldTraceRealCoordinates_pair] at hm
    refine ⟨m, ?_⟩
    change (m : ℚ) = Algebra.trace ℚ K (c * a)
    have h : Algebra.trace ℚ K (a * c) = (m : ℚ) := by exact_mod_cast hm
    simpa only [mul_comm] using h.symm
  · rintro ⟨c, hc, rfl⟩ x hx
    rcases (mem_numberFieldTraceLattice I).mp hx with ⟨a, ha, rfl⟩
    obtain ⟨m, hm⟩ := (FractionalIdeal.mem_dual (Units.ne_zero I)).mp hc a ha
    refine ⟨m, ?_⟩
    rw [numberFieldTraceRealCoordinates_pair]
    change (m : ℚ) = Algebra.trace ℚ K (c * a) at hm
    have h : Algebra.trace ℚ K (a * c) = (m : ℚ) := by
      simpa only [mul_comm] using hm.symm
    exact_mod_cast h

end GaloisForLFunctions.HTGeometry
