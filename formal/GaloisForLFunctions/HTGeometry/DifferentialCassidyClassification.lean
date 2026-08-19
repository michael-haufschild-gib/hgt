import GaloisForLFunctions.HTGeometry.Sl2LineStabiliserBridge
import GaloisForLFunctions.HTGeometry.CassidyMatrixAlgebra
import GaloisForLFunctions.HTGeometry.DifferentialConstantsCollapse

/-!
# Cassidy's classification over the constants of a differential field

A solution set of a monic scalar linear differential equation of order `n` is bounded over the
constants: `n + 1` solutions always admit a nontrivial relation with constant coefficients.  That is
exactly the boundedness the line-stabiliser bridge needs, so a bracket-closed subspace of `sl₂(U)`
that spans and whose line stabilisers are such solution sets is conjugate to `sl₂` over the
constants.

For a matrix group the same input is even lighter: only the scalars `c` with `c • 1` in the span
have to solve one such equation, because they form a ring, and a ring of solutions is algebraic over
the constants.  One conjugation then puts every entry of every group element in the constants.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {U : Type*} [Field U] [Differential U]

/-- **Solution sets of a monic scalar linear differential equation are bounded over the
constants.** -/
theorem boundedOverBase_of_scalarSolution {n : ℕ} (a : Fin n → U) (S : Set U)
    (hsol : ∀ c ∈ S, differentialJet n c = ∑ i, a i * differentialJet (i : ℕ) c) :
    BoundedOverBase (differentialConstants U) S := by
  classical
  refine ⟨n, fun f hf => ?_⟩
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hindep : ∀ (t : Finset (Fin (n + 1))) (d : Fin (n + 1) → U), t.Nonempty →
      (∀ j ∈ t, (d j)′ = 0) → (∀ j ∈ t, d j ≠ 0) → ∑ j ∈ t, d j * f j ≠ 0 := by
    intro t d htne hconst hnz hrel
    set g : Fin (n + 1) → differentialConstants U :=
      fun j => if hj : j ∈ t then ⟨d j, hconst j hj⟩ else 0 with hg
    have hgne : ∃ j, g j ≠ 0 := by
      obtain ⟨j, hj⟩ := htne
      refine ⟨j, ?_⟩
      intro h0
      apply hnz j hj
      have : (g j : U) = d j := by rw [hg]; simp [dif_pos hj]
      rw [← this, h0]
      rfl
    have hgrel : ∑ j, algebraMap (differentialConstants U) U (g j) * f j = 0 := by
      have hsum : ∑ j, algebraMap (differentialConstants U) U (g j) * f j
          = ∑ j ∈ t, d j * f j := by
        rw [← Finset.sum_subset (Finset.subset_univ t)]
        · refine Finset.sum_congr rfl fun j hj => ?_
          have hval : (g j : U) = d j := by rw [hg]; simp [dif_pos hj]
          rw [show algebraMap (differentialConstants U) U (g j) = (g j : U) from rfl, hval]
        · intro j _ hj
          have hval : (g j : U) = 0 := by rw [hg]; simp [dif_neg hj]
          rw [show algebraMap (differentialConstants U) U (g j) = (g j : U) from rfl, hval,
            zero_mul]
      rw [hsum, hrel]
    obtain ⟨j, hj⟩ := hgne
    exact hcon g ⟨j, hj⟩ hgrel
  have hcard := card_le_of_no_constantRelation_scalar a (x := f)
    (fun j => hsol (f j) (hf j)) hindep
  simp at hcard

/-- **Cassidy's classification for `sl₂` over the constants of a differential field.**  If the
scalars in each line stabiliser of `L` solve a monic scalar linear differential equation, then `L`
is conjugate to `sl₂` over the constants. -/
theorem cassidy_sl2_of_differentialSolution [IsAlgClosed U] [CharZero U]
    [IsAlgClosed (differentialConstants U)]
    (L : Submodule (differentialConstants U) (Matrix (Fin 2) (Fin 2) U))
    (htr : ∀ A ∈ L, A.trace = 0)
    (hbr : ∀ A ∈ L, ∀ B ∈ L, A * B - B * A ∈ L)
    (hdense : ∀ Z : Matrix (Fin 2) (Fin 2) U, Z.trace = 0 →
      Z ∈ Submodule.span U (L : Set (Matrix (Fin 2) (Fin 2) U)))
    (hsol : ∀ Y ∈ L, Y ≠ 0 → ∃ (n : ℕ) (a : Fin n → U), ∀ c : U, c • Y ∈ L →
      differentialJet n c = ∑ i, a i * differentialJet (i : ℕ) c) :
    ∃ P Q : Matrix (Fin 2) (Fin 2) U, P * Q = 1 ∧ Q * P = 1 ∧
      L.map (conjLinear (differentialConstants U) P Q)
        = Submodule.span (differentialConstants U) {sl2H U, sl2E U, sl2F U} := by
  refine cassidy_sl2_of_bounded L htr hbr hdense ?_
  intro Y hY hYne
  obtain ⟨n, a, ha⟩ := hsol Y hY hYne
  exact boundedOverBase_of_scalarSolution a _ ha

/-- **A spanning matrix group becomes constant after one conjugation.**  If the scalars `c` with
`c • 1` in the span of the group solve a monic scalar linear differential equation, then a single
conjugation puts every entry of every element of the group in the constants. -/
theorem constant_conjugate_of_differentialSolution [IsAlgClosed U] [CharZero U]
    [IsAlgClosed (differentialConstants U)]
    (G : Set (Matrix (Fin 2) (Fin 2) U))
    (hone : (1 : Matrix (Fin 2) (Fin 2) U) ∈ G)
    (hmulG : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G)
    (hspanG : ∀ Z : Matrix (Fin 2) (Fin 2) U, Z ∈ Submodule.span U G)
    {n : ℕ} (a : Fin n → U)
    (hsol : ∀ c : U, c • (1 : Matrix (Fin 2) (Fin 2) U) ∈
        Submodule.span (differentialConstants U) G →
      differentialJet n c = ∑ i, a i * differentialJet (i : ℕ) c) :
    ∃ P Q : Matrix (Fin 2) (Fin 2) U, P * Q = 1 ∧ Q * P = 1 ∧
      ∀ g ∈ G, ∀ i j, (P * g * Q) i j ∈ differentialConstants U := by
  obtain ⟨P, Q, hPQ, hQP, hconst⟩ :=
    cassidy_gl2_constant_conjugate (C := differentialConstants U) G hone hmulG hspanG
      (exists_eq_algebraMap_of_smul_one_solution _ (Submodule.subset_span hone)
        (mul_mem_span_of_mul_mem G hmulG) a hsol)
  refine ⟨P, Q, hPQ, hQP, fun g hg i j => ?_⟩
  obtain ⟨c, hc⟩ := hconst g hg i j
  rw [hc]
  exact c.2

end

end GaloisForLFunctions.HTGeometry
