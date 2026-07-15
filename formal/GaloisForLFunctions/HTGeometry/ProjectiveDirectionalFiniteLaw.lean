import GaloisForLFunctions.HTGeometry.ComplexDirectionalFiniteLawDichotomy
import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Projective directional finite-law filtration

Nonzero rescaling of a derivation direction diagonally rescales its jet coordinates by nonzero
base-field constants.  The finite directional law loci and the complete hypertranscendental locus
therefore descend from affine coordinates to the actual projectivization of law space.  The
projective finite-law loci are nested, and their countable union is exactly the complement of the
projective complete-jet algebraic-independence locus.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped LinearAlgebra.Projectivization

variable {k K L ι : Type*} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
  [CharZero K] [Fintype ι]

omit [CharZero K] in
/-- Algebraic independence over the intermediate field is invariant under nonzero rescaling of a
direction. -/
theorem directionalJet_algebraicIndependent_smul_iff_over
    (δ : ι → Derivation k L L) (c : ι → k) {a : k} (ha : a ≠ 0)
    (x : L) :
    AlgebraicIndependent K (fun n ↦ directionalJet δ (a • c) n x) ↔
      AlgebraicIndependent K (fun n ↦ directionalJet δ c n x) := by
  simp_rw [directionalJet_smul]
  simpa [Algebra.smul_def, IsScalarTower.algebraMap_apply k K L] using
    (algebraicIndependent_const_mul_coordinates_iff
      (fun n ↦ directionalJet δ c n x)
      (fun n ↦ algebraMap k K (a ^ n))
      (fun n ↦ by
        simpa only [map_zero] using
          (algebraMap k K).injective.ne (pow_ne_zero n ha)))

omit [CharZero K] in
/-- A finite directional law is invariant under nonzero rescaling of the direction. -/
theorem directionalFiniteLawLocus_smul_iff
    (δ : ι → Derivation k L L) (c : ι → k) {a : k} (ha : a ≠ 0)
    (x : L) (n : ℕ) :
    a • c ∈ directionalFiniteLawLocus (K := K) δ x n ↔
      c ∈ directionalFiniteLawLocus (K := K) δ x n := by
  change (¬ AlgebraicIndependent K
      (fun j : Fin (n + 1) ↦ directionalJet δ (a • c) j x)) ↔
    ¬ AlgebraicIndependent K
      (fun j : Fin (n + 1) ↦ directionalJet δ c j x)
  simp_rw [directionalJet_smul]
  apply not_congr
  simpa [Algebra.smul_def, IsScalarTower.algebraMap_apply k K L] using
    (algebraicIndependent_const_mul_coordinates_iff
      (fun j : Fin (n + 1) ↦ directionalJet δ c j x)
      (fun j : Fin (n + 1) ↦ algebraMap k K (a ^ (j : ℕ)))
      (fun j ↦ by
        simpa only [map_zero] using
          (algebraMap k K).injective.ne (pow_ne_zero (j : ℕ) ha)))

/-- The order-`n` finite-law locus on the actual projective law space. -/
def projectiveDirectionalFiniteLawLocus
    (δ : ι → Derivation k L L) (x : L) (n : ℕ) :
    Set (ℙ k (ι → k)) :=
  {p | Projectivization.lift
    (fun c : {c : ι → k // c ≠ 0} ↦
      c.1 ∈ directionalFiniteLawLocus (K := K) δ x n)
    (by
      intro a b t hab
      have ht : t ≠ 0 := by
        intro ht
        apply a.2
        rw [hab, ht, zero_smul]
      apply propext
      change (a.1 ∈ directionalFiniteLawLocus (K := K) δ x n) ↔
        b.1 ∈ directionalFiniteLawLocus (K := K) δ x n
      rw [hab]
      exact directionalFiniteLawLocus_smul_iff δ b.1 ht x n)
    p}

/-- The complete hypertranscendental locus on projective law space. -/
def projectiveDirectionalHTLocus
    (δ : ι → Derivation k L L) (x : L) : Set (ℙ k (ι → k)) :=
  {p | Projectivization.lift
    (fun c : {c : ι → k // c ≠ 0} ↦
      AlgebraicIndependent K (fun n ↦ directionalJet δ c.1 n x))
    (by
      intro a b t hab
      have ht : t ≠ 0 := by
        intro ht
        apply a.2
        rw [hab, ht, zero_smul]
      apply propext
      change AlgebraicIndependent K (fun n ↦ directionalJet δ a.1 n x) ↔
        AlgebraicIndependent K (fun n ↦ directionalJet δ b.1 n x)
      rw [hab]
      exact directionalJet_algebraicIndependent_smul_iff_over δ b.1 ht x)
    p}

omit [CharZero K] in
@[simp]
theorem mk_mem_projectiveDirectionalFiniteLawLocus_iff
    (δ : ι → Derivation k L L) (x : L) (n : ℕ)
    (c : ι → k) (hc : c ≠ 0) :
    Projectivization.mk k c hc ∈
        projectiveDirectionalFiniteLawLocus (K := K) δ x n ↔
      c ∈ directionalFiniteLawLocus (K := K) δ x n := by
  rfl

omit [CharZero K] in
@[simp]
theorem mk_mem_projectiveDirectionalHTLocus_iff
    (δ : ι → Derivation k L L) (x : L)
    (c : ι → k) (hc : c ≠ 0) :
    Projectivization.mk k c hc ∈ projectiveDirectionalHTLocus (K := K) δ x ↔
      AlgebraicIndependent K (fun n ↦ directionalJet δ c n x) := by
  rfl

/-- The projective finite-law filtration is increasing. -/
theorem projectiveDirectionalFiniteLawLocus_mono
    (δ : ι → Derivation k L L) (x : L) (n : ℕ) :
    projectiveDirectionalFiniteLawLocus (K := K) δ x n ⊆
      projectiveDirectionalFiniteLawLocus (K := K) δ x (n + 1) := by
  intro p hp
  induction p using Projectivization.ind with
  | h c hc =>
      rw [mk_mem_projectiveDirectionalFiniteLawLocus_iff] at hp ⊢
      change (¬ AlgebraicIndependent K
        (fun j : Fin (n + 1) ↦ directionalJet δ c j x)) at hp
      change ¬ AlgebraicIndependent K
        (fun j : Fin (n + 2) ↦ directionalJet δ c j x)
      rw [← directionalKaehlerWedge_eq_zero_iff_not_algebraicIndependent] at hp ⊢
      exact directionalKaehlerWedge_zero_mono δ c x hp

/-- The complement of the projective HT locus is exactly the countable union of the projective
finite-law strata. -/
theorem not_mem_projectiveDirectionalHTLocus_iff_exists_finiteLaw
    (δ : ι → Derivation k L L) (x : L) (p : ℙ k (ι → k)) :
    p ∉ projectiveDirectionalHTLocus (K := K) δ x ↔
      ∃ n, p ∈ projectiveDirectionalFiniteLawLocus (K := K) δ x n := by
  induction p using Projectivization.ind with
  | h c hc =>
      rw [mk_mem_projectiveDirectionalHTLocus_iff]
      simp_rw [mk_mem_projectiveDirectionalFiniteLawLocus_iff]
      exact directionalJet_not_algebraicIndependent_iff_exists_kaehlerWedge_zero δ c x
        |>.trans (exists_congr fun n ↦
          directionalKaehlerWedge_eq_zero_iff_not_algebraicIndependent δ c x n)

end

end GaloisForLFunctions.HTGeometry
