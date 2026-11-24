import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveChartDiagonal
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.TensorLatticeCoordinates
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic

/-! The common-chart diagonal generators form a regular sequence in
the chart tensor ring realized inside the rational tensor algebra. -/

noncomputable section

open RingTheory.Sequence
open scoped TensorProduct

namespace GlobalTheory.PD

variable {k F : Type} [Field k] [Field F] [Algebra k F]

/-- The chart tensor algebra injects into the tensor of the function
fields, since the base of the tensor product is a field. -/
def tensorChartRingEquiv (B C : Subalgebra k F) : B ⊗[k] C ≃ₐ[k] tensorChartRing B C := by
  letI : Module.Free k F := Module.Free.of_divisionRing k F
  letI : Module.Free k C := Module.Free.of_divisionRing k C
  letI : Module.Flat k F := Module.Flat.of_free (R := k) (M := F)
  letI : Module.Flat k C := Module.Flat.of_free (R := k) (M := C)
  exact AlgEquiv.ofInjective (Algebra.TensorProduct.map B.val C.val)
    (TensorProduct.map_injective_of_flat_flat B.val.toLinearMap C.val.toLinearMap
      Subtype.val_injective Subtype.val_injective)

/-- Restrict the chart tensor ring to the diagonal. -/
def tensorChartRingDiagonal (B C : Subalgebra k F) : tensorChartRing B C →ₐ[k] F :=
  (Algebra.TensorProduct.lmul' k (S := F)).comp (tensorChartRing B C).val

private theorem tensorChartRingDiagonal_comp (B C : Subalgebra k F) :
    (tensorChartRingDiagonal B C).comp (tensorChartRingEquiv B C).toAlgHom =
      tensorChartRestriction (k := k) (L := F) B C := by
  apply Algebra.TensorProduct.ext'
  intro b c
  change Algebra.TensorProduct.lmul' k (Algebra.TensorProduct.map B.val C.val (b ⊗ₜ[k] c)) =
    tensorChartRestriction (k := k) (L := F) B C (b ⊗ₜ[k] c)
  rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lmul'_apply_tmul,
    tensorChartRestriction_tmul]
  rfl

variable {d : ℕ} {x : Fin (d + 1) → F} {I J : Finset (Fin (d + 1))} {i : Fin (d + 1)}

/-- The difference of the two affine coordinate ratios in the chart
tensor ring. -/
def IsPd.chartDiagonalGenerators (h : IsPd k x) (hi : i ∈ I) (hj : i ∈ J) :
    Fin d → tensorChartRing (rA k x I) (rA k x J) := by
  letI := chartIntersectionAlgebra (k := k) (x := x) hi
  letI := chartIntersectionAlgebra (k := k) (x := x) hj
  exact fun j => tensorChartRingEquiv (rA k x I) (rA k x J)
    (diagonalDifference (k := k) (rA k x I) (rA k x J) (h.chartPolynomialEquiv i (MvPolynomial.X j)))

theorem IsPd.chartDiagonalGenerators_coe (h : IsPd k x) (hi : i ∈ I) (hj : i ∈ J)
    (l : Fin d) :
    (h.chartDiagonalGenerators hi hj l : F ⊗[k] F) =
      chartCoordinates x i l ⊗ₜ[k] (1 : F) - (1 : F) ⊗ₜ[k] chartCoordinates x i l := by
  let A := rA k x (Singleton.singleton i)
  let B := rA k x I
  let C := rA k x J
  letI : Algebra A B := chartIntersectionAlgebra (k := k) (x := x) hi
  letI : Algebra A C := chartIntersectionAlgebra (k := k) (x := x) hj
  let u : A := h.chartPolynomialEquiv i (MvPolynomial.X l)
  change Algebra.TensorProduct.map B.val C.val
    (algebraMap A B u ⊗ₜ[k] (1 : C) - (1 : B) ⊗ₜ[k] algebraMap A C u) = _
  rw [map_sub, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, map_one, map_one]
  change (u : F) ⊗ₜ[k] (1 : F) - (1 : F) ⊗ₜ[k] (u : F) = _
  rw [show (u : F) = chartCoordinates x i l from h.chartPolynomialEquiv_X i l]

/-- On two intersections containing a common chart, the generators
cut out the diagonal and are weakly regular in the tensor ring. -/
theorem IsPd.chartDiagonalGenerators_regular_kernel (h : IsPd k x) (hi : i ∈ I) (hj : i ∈ J) :
    IsWeaklyRegular (tensorChartRing (rA k x I) (rA k x J))
      (List.ofFn (h.chartDiagonalGenerators hi hj)) ∧
      RingHom.ker (tensorChartRingDiagonal (rA k x I) (rA k x J)).toRingHom =
        Ideal.span (Set.range (h.chartDiagonalGenerators hi hj)) := by
  let B := rA k x I
  let C := rA k x J
  letI := chartIntersectionAlgebra (k := k) (x := x) hi
  letI := chartIntersectionAlgebra (k := k) (x := x) hj
  let z (j : Fin d) :=
    diagonalDifference (k := k) B C (h.chartPolynomialEquiv i (MvPolynomial.X j))
  let e := tensorChartRingEquiv B C
  let m := tensorChartRingDiagonal B C
  obtain ⟨hr, hk⟩ := h.localizedChartTensorDiagonal hi hj
  constructor
  · change IsWeaklyRegular _ (List.ofFn fun j => e (z j))
    have hmap : IsWeaklyRegular (tensorChartRing B C) ((List.ofFn z).map e) := by
      refine (e.toAddEquiv.isWeaklyRegular_congr ?_).mp hr
      exact List.forall₂_map_right_iff.mpr
        (List.forall₂_same.mpr fun a _ b => map_mul e a b)
    rw [List.map_ofFn] at hmap
    exact hmap
  · change RingHom.ker m.toRingHom = Ideal.span (Set.range fun j => e (z j))
    have he : RingHom.ker m.toRingHom =
        (RingHom.ker (m.comp e.toAlgHom).toRingHom).map e.toRingHom := by
      rw [show (m.comp e.toAlgHom).toRingHom = m.toRingHom.comp e.toRingHom from rfl,
        ← RingHom.comap_ker]
      exact (Ideal.map_comap_of_surjective e.toRingHom e.surjective _).symm
    rw [he, tensorChartRingDiagonal_comp, hk, Ideal.map_span, ← Set.range_comp']
    rfl

end GlobalTheory.PD
