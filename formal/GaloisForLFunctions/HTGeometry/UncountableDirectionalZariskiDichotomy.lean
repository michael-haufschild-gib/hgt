import GaloisForLFunctions.HTGeometry.ProjectiveDirectionalFiniteLaw
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Set.Countable

/-!
# Uncountable-field directional Zariski dichotomy

Countably many nonzero polynomials in finitely many variables over an uncountable field admit a
simultaneous nonvanishing point.  The proof is an induction on the number of variables: choose the
remaining coordinates so that one nonzero coefficient of every polynomial survives, then avoid
the countable union of the resulting finite root sets in the last coordinate.

Applied to one nonzero coordinate equation from every proper directional finite-law stratum, this
gives the projective alternative: either one finite order is universal, or the complete-HT locus
meets every principal polynomial open.  This is the concrete Zariski-density statement and uses no
complex topology or Baire theorem.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Countably many nonzero polynomials in finitely many variables over an uncountable field admit
a simultaneous nonvanishing point. -/
theorem exists_forall_mvPolynomial_eval_ne_zero_fin
    {k : Type*} [Field k] [Uncountable k] :
    ∀ m : ℕ, ∀ P : ℕ → MvPolynomial (Fin m) k,
      (∀ n, P n ≠ 0) → ∃ x : Fin m → k, ∀ n, MvPolynomial.eval x (P n) ≠ 0 := by
  intro m
  induction m with
  | zero =>
      intro P hP
      let x : Fin 0 → k := fun i ↦ Fin.elim0 i
      refine ⟨x, ?_⟩
      intro n
      have hn := hP n
      rw [(P n).eq_C_of_isEmpty] at hn ⊢
      simpa using hn
  | succ m ih =>
      intro P hP
      let Q : ℕ → Polynomial (MvPolynomial (Fin m) k) :=
        fun n ↦ MvPolynomial.finSuccEquiv k m (P n)
      have hQ : ∀ n, Q n ≠ 0 := by
        intro n
        exact (MvPolynomial.finSuccEquiv k m).injective.ne (hP n)
      let A : ℕ → MvPolynomial (Fin m) k := fun n ↦ (Q n).leadingCoeff
      have hA : ∀ n, A n ≠ 0 := by
        intro n
        simpa [A] using Polynomial.leadingCoeff_ne_zero.mpr (hQ n)
      obtain ⟨x, hx⟩ := ih A hA
      let U : ℕ → Polynomial k := fun n ↦ (Q n).map (MvPolynomial.eval x)
      have hU : ∀ n, U n ≠ 0 := by
        intro n hzero
        have hcoeff : (U n).coeff (Q n).natDegree ≠ 0 := by
          rw [show U n = (Q n).map (MvPolynomial.eval x) by rfl,
            Polynomial.coeff_map]
          simpa [A] using hx n
        apply hcoeff
        rw [hzero]
        simp
      let T : Set k := ⋃ n, {y | Polynomial.IsRoot (U n) y}
      have hTcount : T.Countable := by
        apply Set.countable_iUnion
        intro n
        exact (Polynomial.finite_setOf_isRoot (hU n)).countable
      have hTne : T ≠ Set.univ := by
        intro h
        have huncount : ¬ (Set.univ : Set k).Countable := Set.not_countable_univ
        apply huncount
        rwa [← h]
      obtain ⟨y, hy⟩ := (Set.ne_univ_iff_exists_notMem T).mp hTne
      refine ⟨Fin.cons y x, ?_⟩
      intro n heval
      apply hy
      exact Set.mem_iUnion.mpr ⟨n, by
        change Polynomial.eval y (U n) = 0
        rw [← MvPolynomial.eval_eq_eval_mv_eval' x y (P n)]
        exact heval⟩

/-- **Uncountable-field projective directional dichotomy.** Either one finite jet order collapses
in every projective direction, or the projective complete-HT locus meets every principal
polynomial open. This is the concrete Zariski-density criterion needed by the directional card. -/
theorem projectiveDirectionalFiniteLaw_collapse_or_zariskiDense
    {k K L : Type*} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    [CharZero K] [Uncountable k]
    (m : ℕ) (δ : Fin (m + 1) → Derivation k L L) (x : L) :
    (∃ N, projectiveDirectionalFiniteLawLocus (K := K) δ x N = Set.univ) ∨
      ∀ Q : MvPolynomial (Fin (m + 1)) k, Q ≠ 0 →
        ∃ c : Fin (m + 1) → k, ∃ hc : c ≠ 0,
          MvPolynomial.eval c Q ≠ 0 ∧
            Projectivization.mk k c hc ∈ projectiveDirectionalHTLocus (K := K) δ x := by
  classical
  by_cases hcollapse :
      ∃ N, projectiveDirectionalFiniteLawLocus (K := K) δ x N = Set.univ
  · exact Or.inl hcollapse
  · right
    have hproper : ∀ n,
        projectiveDirectionalFiniteLawLocus (K := K) δ x n ≠ Set.univ := by
      intro n hn
      exact hcollapse ⟨n, hn⟩
    have hexists : ∀ n, ∃ R : MvPolynomial (Fin (m + 1)) k,
        R ≠ 0 ∧ ∀ c, c ∈ directionalFiniteLawLocus (K := K) δ x n →
          MvPolynomial.eval c R = 0 := by
      intro n
      obtain ⟨r, P, hP, hzero⟩ :=
        exists_directionalFiniteLawPolynomials (K := K) δ x n
      obtain ⟨z, hz⟩ :=
        (Set.ne_univ_iff_exists_notMem
          (projectiveDirectionalFiniteLawLocus (K := K) δ x n)).mp (hproper n)
      let c : Fin (m + 1) → k := z.rep
      have hc : c ≠ 0 := z.rep_nonzero
      have hcnot : c ∉ directionalFiniteLawLocus (K := K) δ x n := by
        intro hmem
        apply hz
        rw [← z.mk_rep]
        exact (mk_mem_projectiveDirectionalFiniteLawLocus_iff δ x n c hc).2 hmem
      have hnotall : ¬ ∀ j, MvPolynomial.eval c (P j) = 0 := by
        intro hall
        exact hcnot ((hzero c).mp hall)
      push Not at hnotall
      obtain ⟨j, hj⟩ := hnotall
      refine ⟨P j, ?_, ?_⟩
      · intro h
        rw [h] at hj
        simp at hj
      · intro y hy
        exact (hzero y).mpr hy j
    choose R hRne hRzero using hexists
    intro Q hQ
    let P : ℕ → MvPolynomial (Fin (m + 1)) k
      | 0 => Q
      | 1 => MvPolynomial.X 0
      | n + 2 => R n
    have hP : ∀ n, P n ≠ 0 := by
      intro n
      rcases n with (_ | _ | n)
      · exact hQ
      · exact MvPolynomial.X_ne_zero (R := k) (0 : Fin (m + 1))
      · exact hRne n
    obtain ⟨c, hcP⟩ :=
      exists_forall_mvPolynomial_eval_ne_zero_fin (m + 1) P hP
    have hc0 : c 0 ≠ 0 := by
      simpa [P] using hcP 1
    have hc : c ≠ 0 := by
      intro h
      apply hc0
      rw [h]
      rfl
    refine ⟨c, hc, ?_, ?_⟩
    · simpa [P] using hcP 0
    · rw [mk_mem_projectiveDirectionalHTLocus_iff]
      rw [algebraicIndependent_nat_iff_initialSegments]
      intro n
      by_contra hdep
      have hvanish := hRzero n c hdep
      exact (hcP (n + 2)) (by simpa [P] using hvanish)

end

end GaloisForLFunctions.HTGeometry
