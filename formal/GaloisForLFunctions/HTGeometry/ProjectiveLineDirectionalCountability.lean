import GaloisForLFunctions.HTGeometry.ProjectiveDirectionalFiniteLaw
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# The sharp two-law directional dichotomy

On a two-dimensional law space, each proper projective finite-law stratum is finite.  The proof
dehomogenizes one nonzero homogeneous coordinate equation in the affine chart `[t:1]`; its roots
are finite, with at most the additional point at infinity.  Therefore either one finite jet order
collapses in every projective direction, or the union of all exceptional finite-law directions is
countable.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped LinearAlgebra.Projectivization OnePoint

variable {k K L : Type*} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
  [CharZero K]

/-- Dehomogenization of a binary homogeneous polynomial in the affine chart `[t:1]`. -/
def dehomogenizeFin2 (p : MvPolynomial (Fin 2) k) : Polynomial k :=
  MvPolynomial.aeval ![(Polynomial.X : Polynomial k), 1] p

theorem eval_dehomogenizeFin2 (p : MvPolynomial (Fin 2) k) (t : k) :
    (dehomogenizeFin2 p).eval t = MvPolynomial.eval ![t, 1] p := by
  change Polynomial.aeval t (MvPolynomial.aeval ![Polynomial.X, 1] p) =
    MvPolynomial.aeval ![t, 1] p
  rw [MvPolynomial.comp_aeval_apply]
  have hcoord :
      (fun i : Fin 2 ↦ Polynomial.aeval t (![(Polynomial.X : Polynomial k), 1] i)) =
        ![t, 1] := by
    funext i
    fin_cases i <;> simp
  rw [hcoord]

/-- A nonzero binary homogeneous polynomial remains nonzero after dehomogenizing in `[t:1]`. -/
theorem dehomogenizeFin2_ne_zero {p : MvPolynomial (Fin 2) k} {d : ℕ}
    (hp : MvPolynomial.IsHomogeneous p d) (hne : p ≠ 0) :
    dehomogenizeFin2 p ≠ 0 := by
  intro hzero
  have hh : (dehomogenizeFin2 p).homogenize d = p :=
    Polynomial.homogenize_eq_of_isHomogeneous hp rfl
  rw [hzero] at hh
  simp at hh
  exact hne hh.symm

/-- Every proper projective finite-law stratum in a two-dimensional law space is finite. -/
theorem projectiveDirectionalFiniteLawLocus_finite_fin2
    (δ : Fin 2 → Derivation k L L) (x : L) (n : ℕ)
    (hproper : projectiveDirectionalFiniteLawLocus (K := K) δ x n ≠ Set.univ) :
    (projectiveDirectionalFiniteLawLocus (K := K) δ x n).Finite := by
  classical
  obtain ⟨r, P, hP, hzero⟩ :=
    exists_directionalFiniteLawPolynomials (K := K) δ x n
  obtain ⟨z, hz⟩ :=
    (Set.ne_univ_iff_exists_notMem
      (projectiveDirectionalFiniteLawLocus (K := K) δ x n)).mp hproper
  let c : Fin 2 → k := z.rep
  have hc : c ≠ 0 := z.rep_nonzero
  have hz' : c ∉ directionalFiniteLawLocus (K := K) δ x n := by
    intro hmem
    apply hz
    rw [← z.mk_rep]
    exact (mk_mem_projectiveDirectionalFiniteLawLocus_iff δ x n c hc).2 hmem
  have hnotall : ¬ ∀ j, MvPolynomial.eval c (P j) = 0 := by
    intro hall
    apply hz'
    exact (hzero c).mp hall
  push Not at hnotall
  obtain ⟨j, hj⟩ := hnotall
  let q : Polynomial k := dehomogenizeFin2 (P j)
  have hPjne : P j ≠ 0 := by
    intro h
    rw [h] at hj
    simp at hj
  have hqne : q ≠ 0 := dehomogenizeFin2_ne_zero (hP j) hPjne
  let e : OnePoint k ≃ ℙ k (Fin 2 → k) := OnePoint.equivProjectivization k
  let S : Set (ℙ k (Fin 2 → k)) :=
    projectiveDirectionalFiniteLawLocus (K := K) δ x n
  let R : Set k := {t | Polynomial.IsRoot q t}
  have hRfinite : R.Finite := Polynomial.finite_setOf_isRoot hqne
  have hpreSub : e ⁻¹' S ⊆ ({∞} : Set (OnePoint k)) ∪
      ((fun t : k ↦ (t : OnePoint k)) '' R) := by
    intro t ht
    induction t using OnePoint.rec with
    | infty => simp
    | coe t =>
        right
        refine ⟨t, ?_, rfl⟩
        change Polynomial.eval t q = 0
        rw [show q = dehomogenizeFin2 (P j) by rfl,
          eval_dehomogenizeFin2]
        have htS : Projectivization.mk k ![t, 1] (by simp) ∈ S := by
          simpa [e] using ht
        have htLaw : ![t, 1] ∈ directionalFiniteLawLocus (K := K) δ x n := by
          exact (mk_mem_projectiveDirectionalFiniteLawLocus_iff
            δ x n ![t, 1] (by simp)).mp htS
        exact (hzero ![t, 1]).mpr htLaw j
  have hpreFinite : (e ⁻¹' S).Finite :=
    ((Set.finite_singleton ∞).union (hRfinite.image fun t : k ↦ (t : OnePoint k))).subset hpreSub
  have himage : (e '' (e ⁻¹' S)).Finite := hpreFinite.image e
  simpa [e, S] using himage

/-- **Sharp two-law projective dichotomy.** Either one finite order collapses in every projective
direction, or the complete exceptional set of differentially algebraic directions is countable. -/
theorem projectiveDirectionalFiniteLaw_fin2_collapse_or_countableExceptional
    (δ : Fin 2 → Derivation k L L) (x : L) :
    (∃ N, projectiveDirectionalFiniteLawLocus (K := K) δ x N = Set.univ) ∨
      {p : ℙ k (Fin 2 → k) |
        p ∉ projectiveDirectionalHTLocus (K := K) δ x}.Countable := by
  by_cases hcollapse :
      ∃ N, projectiveDirectionalFiniteLawLocus (K := K) δ x N = Set.univ
  · exact Or.inl hcollapse
  · right
    have hproper : ∀ n,
        projectiveDirectionalFiniteLawLocus (K := K) δ x n ≠ Set.univ := by
      intro n hn
      exact hcollapse ⟨n, hn⟩
    have hset : {p : ℙ k (Fin 2 → k) |
        p ∉ projectiveDirectionalHTLocus (K := K) δ x} =
        ⋃ n, projectiveDirectionalFiniteLawLocus (K := K) δ x n := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_iUnion]
      exact not_mem_projectiveDirectionalHTLocus_iff_exists_finiteLaw δ x p
    rw [hset]
    exact Set.countable_iUnion fun n ↦
      (projectiveDirectionalFiniteLawLocus_finite_fin2 δ x n (hproper n)).countable

end

end GaloisForLFunctions.HTGeometry
