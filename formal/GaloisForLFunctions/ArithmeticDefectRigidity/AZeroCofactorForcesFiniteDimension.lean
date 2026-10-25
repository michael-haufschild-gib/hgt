import GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorDiagonalsAreHorizonEnergyRatios
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# A zero cofactor forces finite dimension

A vanishing actual cofactor forces every larger cofactor to vanish. The
remaining finitely many generators span the complete module, giving the
cutoff bound dim H <= p-1.
-/

section

noncomputable section
set_option autoImplicit false
open Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

/-- A zero cofactor forces every larger cofactor to vanish by numeric horizon order. -/
theorem vector_eq_zero_of_le_of_kernel_diag_eq_zero {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) {p q : ℕ+} (hpq : p ≤ q)
    (hp : L.kernel p p = 0) : vector L q = 0 := by
  have h := L.scaled_diagonal_antitone hpq
  change (q : ℝ) * L.kernel q q ≤ (p : ℝ) * L.kernel p p at h
  rw [hp, mul_zero] at h
  have hq0 : 0 ≤ L.kernel q q := by rw [← norm_vector_sq]; positivity
  have hq : L.kernel q q = 0 := le_antisymm
    (by
      have hqpos : (0 : ℝ) < q := by positivity
      exact le_of_not_gt fun hpos => _root_.not_lt_of_ge h (mul_pos hqpos hpos)) hq0
  apply norm_eq_zero.mp
  apply sq_eq_zero_iff.mp
  rw [norm_vector_sq, hq]

/-- Vanishing of one actual cofactor leaves only finitely many generators. -/
theorem finiteDimensional_and_finrank_le_of_kernel_diag_eq_zero {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) {p : ℕ+} (hp : L.kernel p p = 0) :
    FiniteDimensional ℂ (Hilbert L) ∧ Module.finrank ℂ (Hilbert L) ≤ (p : ℕ) - 1 := by
  classical
  let v (i : Fin ((p : ℕ) - 1)) : Hilbert L := vector L ⟨i.val + 1, Nat.succ_pos _⟩
  let s : Finset (Hilbert L) := univ.image v
  let S : Submodule ℂ (Hilbert L) := Submodule.span ℂ (s : Set (Hilbert L))
  letI : FiniteDimensional ℂ S := FiniteDimensional.span_finset ℂ s
  have hv (q : ℕ+) : vector L q ∈ S := by
    by_cases hq : (q : ℕ) < (p : ℕ)
    · let i : Fin ((p : ℕ) - 1) := ⟨(q : ℕ) - 1, by
        have hq1 : 1 ≤ (q : ℕ) := q.property
        omega⟩
      have hi : (⟨i.val + 1, Nat.succ_pos _⟩ : ℕ+) = q := by
        apply Subtype.ext
        exact Nat.sub_add_cancel q.property
      apply Submodule.subset_span
      change vector L q ∈ s
      exact mem_image.mpr ⟨i, mem_univ _, by dsimp only [v]; rw [hi]⟩
    · have hpq : p ≤ q := by exact_mod_cast le_of_not_gt hq
      rw [vector_eq_zero_of_le_of_kernel_diag_eq_zero L hpq hp]
      exact S.zero_mem
  have hspan : Submodule.span ℂ (Set.range (vector L)) ≤ S := by
    apply Submodule.span_le.mpr
    rintro x ⟨q, rfl⟩
    exact hv q
  have hdense : Dense (S : Set (Hilbert L)) :=
    (HTGeometry.KernelHilbert.dense_span_vectors (complexKernel L)).mono hspan
  have hset : (S : Set (Hilbert L)) = Set.univ :=
    (Submodule.closed_of_finiteDimensional S).closure_eq.symm.trans hdense.closure_eq
  have hStop : S = ⊤ := SetLike.coe_injective hset
  have hsurj : Function.Surjective S.subtype := by
    intro x
    refine ⟨⟨x, ?_⟩, rfl⟩
    rw [hStop]
    trivial
  have hdim : FiniteDimensional ℂ (Hilbert L) := FiniteDimensional.of_surjective S.subtype hsurj
  letI := hdim
  refine ⟨hdim, ?_⟩
  have hcard : s.card ≤ (p : ℕ) - 1 := by
    simpa only [s, card_univ, Fintype.card_fin] using
      (card_image_le (s := (univ : Finset (Fin ((p : ℕ) - 1)))) (f := v))
  have hbound : Module.finrank ℂ S ≤ (p : ℕ) - 1 :=
    (finrank_span_finset_le_card s).trans hcard
  rw [hStop, finrank_top] at hbound
  exact hbound

/-- Infinite actual cofactor modules retain positive energy at every fixed cofactor. -/
theorem kernel_diag_pos_of_infinite {ε : SubcriticalDamping} (L : ActualCofactorLimit ε)
    (h : ¬ FiniteDimensional ℂ (Hilbert L)) (p : ℕ+) : 0 < L.kernel p p := by
  have hnonneg : 0 ≤ L.kernel p p := by rw [← norm_vector_sq]; positivity
  apply lt_of_le_of_ne hnonneg
  intro hz
  exact h (finiteDimensional_and_finrank_le_of_kernel_diag_eq_zero L hz.symm).1

end GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.finiteDimensional_and_finrank_le_of_kernel_diag_eq_zero
#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.ActualCofactorLimit.kernel_diag_pos_of_infinite
end
end
