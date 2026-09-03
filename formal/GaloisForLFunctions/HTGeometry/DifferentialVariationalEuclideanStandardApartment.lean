import GaloisForLFunctions.HTGeometry.DifferentialVariationalStandardApartment
import GaloisForLFunctions.HTGeometry.BorelWeil.BottCombinatorics
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Euclidean realization of the differential variational standard apartment

Integral coweights modulo their common translation have a canonical representative in the
zero-sum real coweight hyperplane.  This file constructs that representative, proves it is faithful,
and embeds the integral apartment vertices in the literal Euclidean type-A apartment.  It also
supplies a dominant permutation without changing the determinant-balance sum.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

namespace DiffOp

variable {ι : Type*} [Fintype ι]

/-- Zero-sum real representative of an integral coweight modulo common translation. -/
def centeredCoweight (m : ι → ℤ) : ι → ℝ :=
  fun i => (m i : ℝ) - (∑ j, (m j : ℝ)) / Fintype.card ι

theorem centeredCoweight_sum_eq_zero (m : ι → ℤ) :
    ∑ i, centeredCoweight m i = 0 := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      letI := hι
      simp
  | inr hι =>
      letI := hι
      simp only [centeredCoweight, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
        exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
      field_simp
      ring

theorem centeredCoweight_add_const (m : ι → ℤ) (c : ℤ) :
    centeredCoweight (m + fun _ => c) = centeredCoweight m := by
  classical
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      letI := hι
      exact Subsingleton.elim _ _
  | inr hι =>
      letI := hι
      funext i
      simp only [centeredCoweight, Pi.add_apply, Int.cast_add, Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
        exact_mod_cast (Fintype.card_ne_zero : Fintype.card ι ≠ 0)
      field_simp
      ring

/-- Canonical realization of the integral standard apartment in the zero-sum real hyperplane. -/
def standardApartmentEuclideanRealization :
    DifferentialVariationalStandardApartmentCarrier ι → (ι → ℝ) :=
  Quotient.lift centeredCoweight (by
    intro m n h
    obtain ⟨c, rfl⟩ := h
    exact (centeredCoweight_add_const m c).symm)

@[simp] theorem standardApartmentEuclideanRealization_mk (m : ι → ℤ) :
    standardApartmentEuclideanRealization
        (Quotient.mk (coweightTranslationSetoid (ι := ι)) m) = centeredCoweight m :=
  rfl

theorem standardApartmentEuclideanRealization_sum_eq_zero
    (x : DifferentialVariationalStandardApartmentCarrier ι) :
    ∑ i, standardApartmentEuclideanRealization x i = 0 := by
  induction x using Quotient.inductionOn with
  | _ m => exact centeredCoweight_sum_eq_zero m

theorem standardApartmentEuclideanRealization_injective :
    Function.Injective (standardApartmentEuclideanRealization (ι := ι)) := by
  classical
  intro x y hxy
  cases isEmpty_or_nonempty ι with
  | inl hι =>
      letI := hι
      exact Subsingleton.elim _ _
  | inr hι =>
      letI := hι
      induction x using Quotient.inductionOn with
      | _ m =>
          induction y using Quotient.inductionOn with
          | _ n =>
              apply Quotient.sound
              let i0 : ι := Classical.choice inferInstance
              refine ⟨n i0 - m i0, ?_⟩
              funext i
              have hi := congrFun hxy i
              have hi0 := congrFun hxy i0
              simp only [standardApartmentEuclideanRealization_mk, centeredCoweight] at hi hi0
              have hreal : (n i : ℝ) = (m i : ℝ) + ((n i0 - m i0 : ℤ) : ℝ) := by
                push_cast
                linarith [hi, hi0]
              exact_mod_cast hreal

/-- Real type-A coweight space: the Euclidean apartment containing integral lattice vertices. -/
abbrev DifferentialVariationalEuclideanApartment (ι : Type*) [Fintype ι] :=
  {x : EuclideanSpace ℝ ι // ∑ i, x i = 0}

theorem isClosed_differentialVariationalEuclideanApartment :
    IsClosed {x : EuclideanSpace ℝ ι | ∑ i, x i = 0} := by
  apply isClosed_eq
  · fun_prop
  · exact continuous_const

noncomputable instance differentialVariationalEuclideanApartment_completeSpace :
    CompleteSpace (DifferentialVariationalEuclideanApartment ι) := by
  exact @IsClosed.completeSpace_coe (EuclideanSpace ℝ ι) inferInstance inferInstance
    {x | ∑ i, x i = 0} isClosed_differentialVariationalEuclideanApartment

/-- Integral standard-apartment vertex embedded in the full real type-A apartment. -/
def standardApartmentEuclideanEmbedding
    (x : DifferentialVariationalStandardApartmentCarrier ι) :
    DifferentialVariationalEuclideanApartment ι :=
  ⟨WithLp.toLp 2 (standardApartmentEuclideanRealization x),
    standardApartmentEuclideanRealization_sum_eq_zero x⟩

@[simp] theorem standardApartmentEuclideanEmbedding_apply
    (x : DifferentialVariationalStandardApartmentCarrier ι) (i : ι) :
    (standardApartmentEuclideanEmbedding x).1 i =
      standardApartmentEuclideanRealization x i := rfl

theorem standardApartmentEuclideanEmbedding_injective :
    Function.Injective (standardApartmentEuclideanEmbedding (ι := ι)) := by
  intro x y hxy
  apply standardApartmentEuclideanRealization_injective
  apply WithLp.toLp_injective 2
  exact congrArg Subtype.val hxy

/-- Straight Euclidean segment inside the zero-sum apartment. -/
def euclideanApartmentSegment
    (x y : DifferentialVariationalEuclideanApartment ι) (t : ℝ) :
    DifferentialVariationalEuclideanApartment ι :=
  ⟨(1 - t) • x.1 + t • y.1, by
    change ∑ i, ((1 - t) * x.1 i + t * y.1 i) = 0
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, x.2, y.2]
    ring⟩

@[simp] theorem euclideanApartmentSegment_zero
    (x y : DifferentialVariationalEuclideanApartment ι) :
    euclideanApartmentSegment x y 0 = x := by
  apply Subtype.ext
  simp [euclideanApartmentSegment]

@[simp] theorem euclideanApartmentSegment_one
    (x y : DifferentialVariationalEuclideanApartment ι) :
    euclideanApartmentSegment x y 1 = y := by
  apply Subtype.ext
  simp [euclideanApartmentSegment]

/-- Straight segments are constant-speed Euclidean geodesics in the type-A apartment. -/
theorem dist_euclideanApartmentSegment
    (x y : DifferentialVariationalEuclideanApartment ι) (s t : ℝ) :
    dist (euclideanApartmentSegment x y s) (euclideanApartmentSegment x y t) =
      |s - t| * dist x y := by
  change dist ((1 - s) • x.1 + s • y.1) ((1 - t) • x.1 + t • y.1) =
    |s - t| * dist x.1 y.1
  rw [dist_eq_norm, dist_eq_norm]
  have hvec :
      ((1 - s) • x.1 + s • y.1) - ((1 - t) • x.1 + t • y.1) =
        (s - t) • (y.1 - x.1) := by module
  rw [hvec, norm_smul, Real.norm_eq_abs]
  congr 1
  exact norm_sub_rev y.1 x.1

/-- Every integral coweight has a dominant permutation preserving its total weight. -/
theorem exists_dominant_permutation {N : ℕ} (m : Fin N → ℤ) :
    ∃ w : Equiv.Perm (Fin N), Antitone (m ∘ w) ∧
      ∑ i, m (w i) = ∑ i, m i := by
  classical
  refine ⟨BorelWeil.sortDescPerm m,
    BorelWeil.antitone_comp_sortDescPerm m, ?_⟩
  exact Equiv.sum_comp (BorelWeil.sortDescPerm m) m

end DiffOp

end

end GaloisForLFunctions.HTGeometry
