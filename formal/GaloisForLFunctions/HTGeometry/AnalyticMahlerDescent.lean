import GaloisForLFunctions.HTGeometry.JetTaylorStructure
import GaloisForLFunctions.HTGeometry.EntireIdentityTheorem
import GaloisForLFunctions.HTGeometry.LinearSystemDescent

/-!
# Analytic Mahler descent: coefficient-field normalization for entire functions

An entire function whose derivatives at the origin lie in a subfield `K ⊆ ℂ` and which
satisfies a nonzero algebraic differential equation over `ℂ` satisfies one with all
coefficients in `K` (`analytic_mahler_descent`) — Mahler's normalization in the function
register.

The assembly: annihilation is equivalent to the countable family of Taylor conditions at the
origin; each condition is a `K`-linear form in the coefficients of the candidate annihilator
because the structure constants — the origin Taylor coefficients of the jet monomials — lie
in `K`; nontrivial solvability of such a family descends from `ℂ` to `K`; and the descended
solution reassembles into a `K`-coefficient annihilator, whose flat jet evaluation vanishes
identically by the identity theorem.
-/

open MvPolynomial

namespace GaloisForLFunctions

/-- Iterated derivatives pass through finite sums of scalar multiples of entire functions. -/
theorem iteratedDeriv_finset_sum_mul {ι : Type*} (s : Finset ι) (c : ι → ℂ) (g : ι → ℂ → ℂ)
    (hg : ∀ i ∈ s, Differentiable ℂ (g i)) (k : ℕ) :
    iteratedDeriv k (fun z => ∑ i ∈ s, c i * g i z) 0
      = ∑ i ∈ s, c i * iteratedDeriv k (g i) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    have hgi : Differentiable ℂ (g i) := hg i (Finset.mem_insert_self i s)
    have hgs : Differentiable ℂ (fun z => ∑ j ∈ s, c j * g j z) := by
      have h := Differentiable.sum fun j hj =>
        (differentiable_const (c j)).mul (hg j (Finset.mem_insert_of_mem hj))
      have hfe : (∑ i ∈ s, (fun _ => c i) * g i) = fun z => ∑ j ∈ s, c j * g j z := by
        funext z
        simp
      rwa [hfe] at h
    have hfun : (fun z => ∑ j ∈ insert i s, c j * g j z)
        = (fun z => c i * g i z) + fun z => ∑ j ∈ s, c j * g j z := by
      funext z
      simp [Finset.sum_insert hi]
    rw [hfun]
    have hc1 : ContDiffAt ℂ (k : WithTop ℕ∞) (fun z => c i * g i z) 0 :=
      ((((differentiable_const (c i)).mul hgi).differentiableOn.analyticOnNhd
        isOpen_univ) 0 (Set.mem_univ 0)).contDiffAt
    have hc2 : ContDiffAt ℂ (k : WithTop ℕ∞) (fun z => ∑ j ∈ s, c j * g j z) 0 :=
      ((hgs.differentiableOn.analyticOnNhd isOpen_univ) 0 (Set.mem_univ 0)).contDiffAt
    rw [iteratedDeriv_add hc1 hc2, Finset.sum_insert hi,
      iteratedDeriv_const_mul_field (c i) (g i),
      ih (fun j hj => hg j (Finset.mem_insert_of_mem hj))]

/-- Pointwise monomial expansion of a jet evaluation. -/
theorem jetEval_as_sum {f : ℂ → ℂ} (n : ℕ) (P : MvPolynomial (Fin (n + 2)) ℂ) (z : ℂ) :
    MvPolynomial.eval (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) P
      = ∑ m ∈ P.support, MvPolynomial.coeff m P * MvPolynomial.eval
          (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z)
          (monomial m (1 : ℂ)) := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [eval_monomial, eval_monomial, one_mul]

/-- **Analytic Mahler descent.**  An entire function with `K`-rational derivatives at the
origin that is differentially algebraic over `ℂ` admits a nonzero annihilator with all
coefficients in `K`. -/
theorem analytic_mahler_descent {K : Subfield ℂ} {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (hK : ∀ j, iteratedDeriv j f 0 ∈ K)
    (hDA : DifferentiallyAlgebraic f) :
    ∃ (n : ℕ) (Q : MvPolynomial (Fin (n + 2)) ℂ), Q ≠ 0 ∧
      (∀ m, MvPolynomial.coeff m Q ∈ K) ∧
      ∀ z, MvPolynomial.eval
        (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) Q = 0 := by
  classical
  obtain ⟨n, P, hP0, hPz⟩ := hDA
  set A : ℕ → {m // m ∈ P.support} → ↥K := fun k m =>
    ⟨iteratedDeriv k (fun z => MvPolynomial.eval
        (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z)
        (monomial m.1 (1 : ℂ))) 0,
      iteratedDeriv_jetEval_monomial_mem hf n hK m.1 k⟩ with hA
  have hmono_diff : ∀ m : Fin (n + 2) →₀ ℕ, Differentiable ℂ
      (fun z => MvPolynomial.eval
        (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z)
        (monomial m (1 : ℂ))) :=
    fun m => differentiable_jetEval hf n (monomial m (1 : ℂ))
  have hsum_eq : ∀ (c : {m // m ∈ P.support} → ℂ) (k : ℕ),
      ∑ m, algebraMap ↥K ℂ (A k m) * c m
        = iteratedDeriv k (fun z => ∑ m ∈ P.support.attach,
            c m * MvPolynomial.eval
              (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z)
              (monomial m.1 (1 : ℂ))) 0 := by
    intro c k
    rw [iteratedDeriv_finset_sum_mul _ _ _ (fun m _ => hmono_diff m.1) k,
      Finset.univ_eq_attach]
    refine Finset.sum_congr rfl fun m _ => ?_
    show (A k m : ℂ) * c m = _
    rw [mul_comm]
  have hLsol : ∃ v : {m // m ∈ P.support} → ℂ, v ≠ 0 ∧
      ∀ k, ∑ m, algebraMap ↥K ℂ (A k m) * v m = 0 := by
    refine ⟨fun m => MvPolynomial.coeff m.1 P, ?_, ?_⟩
    · obtain ⟨m₀, hm₀⟩ := MvPolynomial.support_nonempty.mpr hP0
      intro h0
      exact (MvPolynomial.mem_support_iff.mp hm₀) (congrFun h0 ⟨m₀, hm₀⟩)
    · intro k
      rw [hsum_eq]
      have hzero : (fun z => ∑ m ∈ P.support.attach,
          MvPolynomial.coeff m.1 P * MvPolynomial.eval
            (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z)
            (monomial m.1 (1 : ℂ))) = fun _ => 0 := by
        funext z
        rw [Finset.sum_attach P.support (fun m => MvPolynomial.coeff m P *
          MvPolynomial.eval
            (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z)
            (monomial m (1 : ℂ))), ← jetEval_as_sum n P z]
        exact hPz z
      rw [hzero]
      simp
  obtain ⟨w, hw0, hwsol⟩ := matrix_mulVec_descent_family A hLsol
  refine ⟨n, ∑ m ∈ P.support.attach, ((w m : ℂ)) • monomial m.1 (1 : ℂ), ?_, ?_, ?_⟩
  · have hQcoeff : ∀ m₀ : {m // m ∈ P.support}, MvPolynomial.coeff m₀.1
        (∑ m ∈ P.support.attach, ((w m : ℂ)) • monomial m.1 (1 : ℂ)) = (w m₀ : ℂ) := by
      intro m₀
      rw [MvPolynomial.coeff_sum]
      have h1 : ∀ m ∈ P.support.attach, m ≠ m₀ →
          MvPolynomial.coeff m₀.1 ((w m : ℂ) • monomial m.1 (1 : ℂ)) = 0 := fun m _ hne => by
        rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial,
          if_neg (fun h => hne (Subtype.ext h)), smul_zero]
      rw [Finset.sum_eq_single m₀ h1 (fun h => absurd (Finset.mem_attach _ m₀) h),
        MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, if_pos rfl, smul_eq_mul,
        mul_one]
    obtain ⟨m₀, hm₀⟩ := Function.ne_iff.mp hw0
    intro h0
    apply hm₀
    have hc := hQcoeff m₀
    rw [h0, MvPolynomial.coeff_zero] at hc
    exact_mod_cast hc.symm
  · intro μ
    rw [MvPolynomial.coeff_sum]
    refine sum_mem fun m _ => ?_
    rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial]
    split_ifs
    · simp
    · simp
  · have hfun : (fun z => MvPolynomial.eval
        (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z)
        (∑ m ∈ P.support.attach, ((w m : ℂ)) • monomial m.1 (1 : ℂ)))
        = fun z => ∑ m ∈ P.support.attach, (w m : ℂ) * MvPolynomial.eval
            (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z)
            (monomial m.1 (1 : ℂ)) := by
      funext z
      rw [map_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [smul_eval]
    have hflat : ∀ k, iteratedDeriv k (fun z => ∑ m ∈ P.support.attach,
        (w m : ℂ) * MvPolynomial.eval
          (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z)
          (monomial m.1 (1 : ℂ))) 0 = 0 := by
      intro k
      rw [← hsum_eq (fun m => (w m : ℂ)) k]
      have hcast : ∀ m, algebraMap ↥K ℂ (A k m) * (w m : ℂ)
          = algebraMap ↥K ℂ (A k m * w m) := fun m => by
        rw [map_mul]; rfl
      rw [Finset.sum_congr rfl fun m _ => hcast m, ← map_sum, hwsol k, map_zero]
    have hdiff : Differentiable ℂ (fun z => ∑ m ∈ P.support.attach,
        (w m : ℂ) * MvPolynomial.eval
          (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z)
          (monomial m.1 (1 : ℂ))) := by
      have h := Differentiable.sum fun (m : {m // m ∈ P.support}) (_ : m ∈ P.support.attach) =>
        (differentiable_const ((w m : ℂ))).mul (hmono_diff m.1)
      have hfe : (∑ m ∈ P.support.attach, (fun _ => (w m : ℂ)) * fun z =>
          MvPolynomial.eval (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z)
            (monomial m.1 (1 : ℂ)))
          = fun z => ∑ m ∈ P.support.attach, (w m : ℂ) * MvPolynomial.eval
              (Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z)
              (monomial m.1 (1 : ℂ)) := by
        funext z
        simp
      rwa [hfe] at h
    have h0 := entire_eq_zero_of_forall_iteratedDeriv_zero hdiff hflat
    intro z
    rw [congrFun hfun z]
    exact congrFun h0 z

end GaloisForLFunctions
