import GaloisForLFunctions.HTGeometry.RationalInvariantOrbit
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Backward orbits of a polynomial map

Over an algebraically closed field every value of a nonconstant polynomial is attained, so every
point has a backward orbit.  A backward orbit starting at a point which is neither periodic nor in
the forward orbit of a critical point is injective and stays away from the critical set: a
coincidence `b m = b n` with `m < n` pushes forward to a period of the starting point, and a
critical `b (n+1)` pushes forward to the starting point.

Combined with the order transport, such an orbit forces the order of an invariant differential to
vanish at the starting point, because a nonzero rational function has only finitely many zeros and
poles.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial IntermediateField

noncomputable section

variable {K : Type*} [Field K]

/-- A nonconstant polynomial over an algebraically closed field attains every value. -/
theorem exists_eval_eq [IsAlgClosed K] {R : K[X]} (hR : R.natDegree ≠ 0) (y : K) :
    ∃ x : K, R.eval x = y := by
  have hdeg : (R - Polynomial.C y).degree ≠ 0 := by
    intro h
    refine hR ?_
    rw [← natDegree_sub_C (a := y)]
    exact natDegree_eq_of_degree_eq_some (by exact_mod_cast h)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (R - Polynomial.C y) hdeg
  refine ⟨x, ?_⟩
  have := hx
  rw [IsRoot, eval_sub, eval_C, sub_eq_zero] at this
  exact this

/-- A chosen backward orbit of a nonconstant polynomial. -/
def backwardOrbit [IsAlgClosed K] {R : K[X]} (hR : R.natDegree ≠ 0) (c : K) : ℕ → K
  | 0 => c
  | n + 1 => (exists_eval_eq hR (backwardOrbit hR c n)).choose

@[simp]
theorem backwardOrbit_zero [IsAlgClosed K] {R : K[X]} (hR : R.natDegree ≠ 0) (c : K) :
    backwardOrbit hR c 0 = c := rfl

theorem eval_backwardOrbit_succ [IsAlgClosed K] {R : K[X]} (hR : R.natDegree ≠ 0) (c : K) (n : ℕ) :
    R.eval (backwardOrbit hR c (n + 1)) = backwardOrbit hR c n :=
  (exists_eval_eq hR (backwardOrbit hR c n)).choose_spec

/-- Pushing a backward orbit forward returns to an earlier stage. -/
theorem iterate_backwardOrbit [IsAlgClosed K] {R : K[X]} (hR : R.natDegree ≠ 0) (c : K) (n : ℕ) :
    ∀ m : ℕ, (fun x => R.eval x)^[m] (backwardOrbit hR c (n + m)) = backwardOrbit hR c n := by
  intro m
  induction m with
  | zero => rfl
  | succ m ih =>
      rw [show n + (m + 1) = (n + m) + 1 from by ring, Function.iterate_succ_apply]
      show (fun x => R.eval x)^[m] (R.eval (backwardOrbit hR c (n + m + 1))) = _
      rw [eval_backwardOrbit_succ]
      exact ih

/-- **Existence of an injective critical-free backward orbit.**  A point which is not periodic and
does not lie in the forward orbit of any critical point admits one. -/
theorem exists_backward_orbit [IsAlgClosed K] {R : K[X]} (hR : R.natDegree ≠ 0) {c : K}
    (hper : ∀ n : ℕ, 1 ≤ n → (fun x => R.eval x)^[n] c ≠ c)
    (hpc : ∀ a : K, (derivative R).eval a = 0 → ∀ n : ℕ, (fun x => R.eval x)^[n] a ≠ c) :
    ∃ b : ℕ → K, b 0 = c ∧ (∀ n, R.eval (b (n + 1)) = b n) ∧ Function.Injective b
      ∧ ∀ n, (derivative R).eval (b (n + 1)) ≠ 0 := by
  refine ⟨backwardOrbit hR c, rfl, eval_backwardOrbit_succ hR c, ?_, ?_⟩
  · have key : ∀ m n : ℕ, m < n → backwardOrbit hR c m ≠ backwardOrbit hR c n := by
      intro m n hmn heq
      have hiter : (fun x => R.eval x)^[n] (backwardOrbit hR c n) = c := by
        simpa using iterate_backwardOrbit hR c 0 n
      rw [← heq] at hiter
      rw [show n = (n - m) + m from by omega, Function.iterate_add_apply] at hiter
      have hm : (fun x => R.eval x)^[m] (backwardOrbit hR c m) = c := by
        simpa using iterate_backwardOrbit hR c 0 m
      rw [hm] at hiter
      exact hper (n - m) (by omega) hiter
    intro m n heq
    rcases lt_trichotomy m n with h | h | h
    · exact absurd heq (key m n h)
    · exact h
    · exact absurd heq.symm (key n m h)
  · intro n hzero
    refine hpc (backwardOrbit hR c (n + 1)) hzero (n + 1) ?_
    simpa using iterate_backwardOrbit hR c 0 (n + 1)

/-- **An injective critical-free backward orbit kills the order at its starting point.** -/
theorem ratOrder_eq_zero_of_backward_orbit [CharZero K] {R : K[X]} (hRdeg : R.natDegree ≠ 0)
    (hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c)
    {Q : RatFunc K} (hQ : Q ≠ 0) {k : ℤ} {μ : K} (hμ : μ ≠ 0)
    (hrel : ratFuncSubstitutionAlgHom (algebraMap K[X] (RatFunc K) R) hR Q
        * (algebraMap K[X] (RatFunc K) (derivative R)) ^ k = RatFunc.C μ * Q)
    {b : ℕ → K} (hstep : ∀ n, R.eval (b (n + 1)) = b n)
    (hcrit : ∀ n, (derivative R).eval (b (n + 1)) ≠ 0) (hinj : Function.Injective b) :
    ratOrder Q (b 0) = 0 := by
  have hconst : ∀ n, ratOrder Q (b n) = ratOrder Q (b 0) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        have h := ratOrder_eval_eq_of_deriv_ne_zero hRdeg hR hQ hμ hrel (hcrit n)
        rw [hstep n] at h
        rw [← h, ih]
  by_contra hne
  have hsub : Set.range b ⊆ {c : K | ratOrder Q c ≠ 0} := by
    rintro _ ⟨n, rfl⟩
    show ratOrder Q (b n) ≠ 0
    rw [hconst n]
    exact hne
  exact (Set.infinite_range_of_injective hinj) ((finite_support_ratOrder hQ).subset hsub)

/-- **The order vanishes at every aperiodic non-postcritical point.** -/
theorem ratOrder_eq_zero_of_aperiodic [CharZero K] [IsAlgClosed K] {R : K[X]}
    (hRdeg : R.natDegree ≠ 0)
    (hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c)
    {Q : RatFunc K} (hQ : Q ≠ 0) {k : ℤ} {μ : K} (hμ : μ ≠ 0)
    (hrel : ratFuncSubstitutionAlgHom (algebraMap K[X] (RatFunc K) R) hR Q
        * (algebraMap K[X] (RatFunc K) (derivative R)) ^ k = RatFunc.C μ * Q)
    {c : K} (hper : ∀ n : ℕ, 1 ≤ n → (fun x => R.eval x)^[n] c ≠ c)
    (hpc : ∀ a : K, (derivative R).eval a = 0 → ∀ n : ℕ, (fun x => R.eval x)^[n] a ≠ c) :
    ratOrder Q c = 0 := by
  obtain ⟨b, hb0, hstep, hinj, hcrit⟩ := exists_backward_orbit hRdeg hper hpc
  have := ratOrder_eq_zero_of_backward_orbit hRdeg hR hQ hμ hrel hstep hcrit hinj
  rwa [hb0] at this

/-! ## The degree of an invariant differential -/

theorem adjoin_C_mul {μ : K} (hμ : μ ≠ 0) (Q : RatFunc K) :
    K⟮RatFunc.C μ * Q⟯ = K⟮Q⟯ := by
  refine le_antisymm ?_ ?_
  · rw [IntermediateField.adjoin_le_iff]
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact mul_mem (IntermediateField.algebraMap_mem _ μ)
      (IntermediateField.mem_adjoin_simple_self K Q)
  · rw [IntermediateField.adjoin_le_iff]
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    have hmem : RatFunc.C μ⁻¹ * (RatFunc.C μ * Q) ∈ K⟮RatFunc.C μ * Q⟯ :=
      mul_mem (IntermediateField.algebraMap_mem _ μ⁻¹)
        (IntermediateField.mem_adjoin_simple_self K _)
    have hQeq : RatFunc.C μ⁻¹ * (RatFunc.C μ * Q) = Q := by
      rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hμ, map_one, one_mul]
    rw [hQeq] at hmem
    rw [hx]
    exact hmem

theorem ratFuncDegree_C_mul {μ : K} (hμ : μ ≠ 0) (Q : RatFunc K) :
    ratFuncDegree (RatFunc.C μ * Q) = ratFuncDegree Q := by
  show max _ _ = max _ _
  rw [← RatFunc.finrank_eq_max_natDegree, ← RatFunc.finrank_eq_max_natDegree, adjoin_C_mul hμ]

theorem not_isConst_algebraMap {R : K[X]} (hR : R.natDegree ≠ 0) :
    ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c := by
  rintro ⟨c, hc⟩
  refine hR ?_
  have : R = Polynomial.C c :=
    (RatFunc.algebraMap_injective K) (by rw [hc, RatFunc.algebraMap_C])
  rw [this, natDegree_C]

/-- **A weight-zero invariant differential of a map of degree at least two is constant.** -/
theorem eq_C_of_weight_zero_relation {R : K[X]} (hRdeg : 2 ≤ R.natDegree)
    (hR : ¬ ∃ c : K, (algebraMap K[X] (RatFunc K) R) = RatFunc.C c)
    {Q : RatFunc K} {μ : K} (hμ : μ ≠ 0)
    (hrel : ratFuncSubstitutionAlgHom (algebraMap K[X] (RatFunc K) R) hR Q
      = RatFunc.C μ * Q) :
    ∃ c : K, Q = RatFunc.C c := by
  have hdeg := ratFuncDegree_substitution (algebraMap K[X] (RatFunc K) R) Q hR
  rw [hrel, ratFuncDegree_C_mul hμ] at hdeg
  have hRd : ratFuncDegree (algebraMap K[X] (RatFunc K) R) = R.natDegree := by
    show max _ _ = _
    rw [RatFunc.num_algebraMap, RatFunc.denom_algebraMap, natDegree_one]
    omega
  rw [hRd] at hdeg
  have hQ0 : ratFuncDegree Q = 0 := by nlinarith [hdeg, hRdeg, Nat.zero_le (ratFuncDegree Q)]
  rw [RatFunc.eq_C_iff]
  exact Nat.max_eq_zero_iff.mp hQ0

end

end GaloisForLFunctions.HTGeometry
