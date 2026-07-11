import Mathlib
import GaloisForLFunctions.LinearSystemDescent

/-!
# Formal Mahler descent: coefficient-field normalization of differential annihilators

If a power series has all Taylor coefficients in a subfield `K ⊆ ℂ` and satisfies a nonzero
algebraic differential equation over `ℂ` — formally: a nonzero differential polynomial in the
point slot and the jet slots evaluates to the zero series on the formal jets — then it
satisfies one with all coefficients in `K` (`formal_mahler_descent`).

The mechanism is Mahler's normalization argument in its exact formal register: annihilation is
the countable family of Taylor-coefficient conditions, each condition is a `K`-linear equation
in the unknown coefficients of the differential polynomial (because every Taylor coefficient
of a monomial in the jets is a universal integer polynomial in the Taylor coefficients of the
series, which lie in `K`), and nontrivial solvability of such a family descends from `ℂ` to
`K` (`matrix_mulVec_descent_family`).  For `K = ℚ` this produces a rational — after clearing
denominators, integral — annihilator: the integrality input of the Taylor-magnitude
convolution-isolation arguments.
-/

open PowerSeries MvPolynomial

namespace GaloisForLFunctions

/-- The formal jet vector of a power series: the point slot carries `X`, the `j`-th jet slot
the `j`-th formal derivative. -/
noncomputable def formalJets (n : ℕ) (F : ℂ⟦X⟧) : Fin (n + 2) → ℂ⟦X⟧ :=
  Fin.cons PowerSeries.X (fun j : Fin (n + 1) => (⇑(d⁄dX ℂ))^[(j : ℕ)] F)

section CoefficientMembership

variable {K : Subfield ℂ}

theorem coeff_mul_mem {A B : ℂ⟦X⟧} (hA : ∀ k, coeff k A ∈ K) (hB : ∀ k, coeff k B ∈ K)
    (k : ℕ) : coeff k (A * B) ∈ K := by
  rw [PowerSeries.coeff_mul]
  exact sum_mem fun p _ => mul_mem (hA p.1) (hB p.2)

theorem coeff_pow_mem {A : ℂ⟦X⟧} (hA : ∀ k, coeff k A ∈ K) (r : ℕ) :
    ∀ k, coeff k (A ^ r) ∈ K := by
  induction r with
  | zero =>
    intro k
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs
    exacts [one_mem K, zero_mem K]
  | succ r ih =>
    intro k
    rw [pow_succ]
    exact coeff_mul_mem ih hA k

theorem coeff_X_mem : ∀ k, coeff k (PowerSeries.X : ℂ⟦X⟧) ∈ K := by
  intro k
  rw [PowerSeries.coeff_X]
  split_ifs
  exacts [one_mem K, zero_mem K]

theorem coeff_derivative_mem {A : ℂ⟦X⟧} (hA : ∀ k, coeff k A ∈ K) :
    ∀ k, coeff k (d⁄dX ℂ A) ∈ K := by
  intro k
  rw [PowerSeries.coeff_derivative]
  have hcast : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [hcast]
  exact mul_mem (hA _) (natCast_mem K _)

theorem coeff_iterate_derivative_mem {A : ℂ⟦X⟧} (hA : ∀ k, coeff k A ∈ K) (j : ℕ) :
    ∀ k, coeff k ((⇑(d⁄dX ℂ))^[j] A) ∈ K := by
  induction j with
  | zero => simpa using hA
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    exact coeff_derivative_mem ih

theorem coeff_prod_mem {ι : Type*} (s : Finset ι) (g : ι → ℂ⟦X⟧)
    (hg : ∀ i ∈ s, ∀ k, coeff k (g i) ∈ K) : ∀ k, coeff k (∏ i ∈ s, g i) ∈ K := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro k
    rw [Finset.prod_empty, PowerSeries.coeff_one]
    split_ifs
    exacts [one_mem K, zero_mem K]
  | insert i s hi ih =>
    intro k
    rw [Finset.prod_insert hi]
    exact coeff_mul_mem (hg i (Finset.mem_insert_self i s))
      (ih fun i' hi' => hg i' (Finset.mem_insert_of_mem hi')) k

theorem coeff_formalJets_mem {F : ℂ⟦X⟧} (hF : ∀ k, coeff k F ∈ K) (n : ℕ)
    (i : Fin (n + 2)) : ∀ k, coeff k (formalJets n F i) ∈ K := by
  induction i using Fin.cases with
  | zero => simpa [formalJets] using coeff_X_mem (K := K)
  | succ j => simpa [formalJets] using coeff_iterate_derivative_mem hF (j : ℕ)

/-- Every Taylor coefficient of a jet monomial lies in the coefficient field. -/
theorem coeff_aeval_monomial_mem {F : ℂ⟦X⟧} (hF : ∀ k, coeff k F ∈ K) (n : ℕ)
    (m : Fin (n + 2) →₀ ℕ) (N : ℕ) :
    coeff N (aeval (formalJets n F) (monomial m (1 : ℂ))) ∈ K := by
  rw [aeval_monomial, map_one, one_mul, Finsupp.prod]
  exact coeff_prod_mem _ _
    (fun i _ => coeff_pow_mem (coeff_formalJets_mem hF n i) (m i)) N

end CoefficientMembership

/-- Monomial expansion of a jet evaluation. -/
theorem aeval_formalJets_as_sum (n : ℕ) (F : ℂ⟦X⟧) (P : MvPolynomial (Fin (n + 2)) ℂ) :
    aeval (formalJets n F) P
      = ∑ m ∈ P.support,
          MvPolynomial.coeff m P • aeval (formalJets n F) (monomial m (1 : ℂ)) := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [aeval_monomial, aeval_monomial, map_one, one_mul, Algebra.smul_def]

/-- **Formal Mahler descent.**  A power series with Taylor coefficients in a subfield `K ⊆ ℂ`
that satisfies a nonzero formal algebraic differential equation over `ℂ` satisfies one with
all coefficients in `K`. -/
theorem formal_mahler_descent {K : Subfield ℂ} {F : ℂ⟦X⟧}
    (hF : ∀ k, coeff k F ∈ K) {n : ℕ} {P : MvPolynomial (Fin (n + 2)) ℂ} (hP : P ≠ 0)
    (hann : aeval (formalJets n F) P = 0) :
    ∃ Q : MvPolynomial (Fin (n + 2)) ℂ, Q ≠ 0 ∧ (∀ m, MvPolynomial.coeff m Q ∈ K) ∧
      aeval (formalJets n F) Q = 0 := by
  classical
  set A : ℕ → {m // m ∈ P.support} → ↥K := fun N m =>
    ⟨coeff N (aeval (formalJets n F) (monomial m.1 (1 : ℂ))),
      coeff_aeval_monomial_mem hF n m.1 N⟩ with hA
  have hsum_eq : ∀ (c : {m // m ∈ P.support} → ℂ) (N : ℕ),
      ∑ m, algebraMap ↥K ℂ (A N m) * c m
        = coeff N (∑ m ∈ P.support.attach,
            c m • aeval (formalJets n F) (monomial m.1 (1 : ℂ))) := by
    intro c N
    rw [map_sum, Finset.univ_eq_attach]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_smul, smul_eq_mul]
    show coeff N (aeval (formalJets n F) (monomial m.1 (1 : ℂ))) * c m = _
    ring
  have hLsol : ∃ v : {m // m ∈ P.support} → ℂ, v ≠ 0 ∧
      ∀ N, ∑ m, algebraMap ↥K ℂ (A N m) * v m = 0 := by
    refine ⟨fun m => MvPolynomial.coeff m.1 P, ?_, ?_⟩
    · obtain ⟨m₀, hm₀⟩ := MvPolynomial.support_nonempty.mpr hP
      intro h0
      exact (MvPolynomial.mem_support_iff.mp hm₀) (congrFun h0 ⟨m₀, hm₀⟩)
    · intro N
      rw [hsum_eq]
      have hattach : ∑ m ∈ P.support.attach,
          MvPolynomial.coeff m.1 P • aeval (formalJets n F) (monomial m.1 (1 : ℂ))
          = aeval (formalJets n F) P := by
        rw [aeval_formalJets_as_sum]
        exact Finset.sum_attach P.support
          (fun m => MvPolynomial.coeff m P • aeval (formalJets n F) (monomial m (1 : ℂ)))
      rw [hattach, hann, map_zero]
  obtain ⟨w, hw0, hwsol⟩ := matrix_mulVec_descent_family A hLsol
  set Q : MvPolynomial (Fin (n + 2)) ℂ :=
    ∑ m ∈ P.support.attach, ((w m : ℂ)) • monomial m.1 (1 : ℂ) with hQ
  have hQcoeff : ∀ m₀ : {m // m ∈ P.support}, MvPolynomial.coeff m₀.1 Q = (w m₀ : ℂ) := by
    intro m₀
    rw [hQ, MvPolynomial.coeff_sum]
    have h1 : ∀ m ∈ P.support.attach, m ≠ m₀ →
        MvPolynomial.coeff m₀.1 ((w m : ℂ) • monomial m.1 (1 : ℂ)) = 0 := fun m _ hne => by
      rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial,
        if_neg (fun h => hne (Subtype.ext h)), smul_zero]
    rw [Finset.sum_eq_single m₀ h1 (fun h => absurd (Finset.mem_attach _ m₀) h),
      MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, if_pos rfl, smul_eq_mul, mul_one]
  have hQcoeff0 : ∀ μ, μ ∉ P.support → MvPolynomial.coeff μ Q = 0 := by
    intro μ hμ
    rw [hQ, MvPolynomial.coeff_sum]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, if_neg, smul_zero]
    exact fun h => hμ (h ▸ m.2)
  refine ⟨Q, ?_, ?_, ?_⟩
  · obtain ⟨m₀, hm₀⟩ := Function.ne_iff.mp hw0
    intro h0
    apply hm₀
    have := hQcoeff m₀
    rw [h0, MvPolynomial.coeff_zero] at this
    exact_mod_cast this.symm
  · intro μ
    by_cases hμ : μ ∈ P.support
    · rw [hQcoeff ⟨μ, hμ⟩]
      exact SetLike.coe_mem _
    · rw [hQcoeff0 μ hμ]
      exact zero_mem K
  · have haQ : aeval (formalJets n F) Q
        = ∑ m ∈ P.support.attach,
            ((w m : ℂ)) • aeval (formalJets n F) (monomial m.1 (1 : ℂ)) := by
      rw [hQ, map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [map_smul]
    ext N
    rw [haQ, map_zero, ← hsum_eq (fun m => (w m : ℂ)) N]
    have hcast : ∀ m, algebraMap ↥K ℂ (A N m) * (w m : ℂ)
        = algebraMap ↥K ℂ (A N m * w m) := fun m => by
      rw [map_mul]; rfl
    rw [Finset.sum_congr rfl fun m _ => hcast m, ← map_sum, hwsol N, map_zero]

end GaloisForLFunctions
