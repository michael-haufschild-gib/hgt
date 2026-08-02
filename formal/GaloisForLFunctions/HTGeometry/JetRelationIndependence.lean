import GaloisForLFunctions.HTGeometry.InverseJetIndependence

/-!
# Jet relations and algebraic independence of jets

The relation form used by the finite phase law — a sum of monomials in the jets with distinct
exponent vectors and nonzero coefficients — is the concrete face of algebraic independence: a nonzero
multivariate polynomial is exactly such a sum.  This file proves the direction the transfer of
differential transcendence needs: if the jets are algebraically independent, no such relation holds.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {F K : Type*} [Field F] [Field K] [Differential F] [Differential K]
  [Algebra F K] [DifferentialAlgebra F K]

omit [Differential F] [DifferentialAlgebra F K] in
/-- **Algebraically independent jets satisfy no relation.**  With distinct exponent vectors and
nonzero coefficients from the base field, the corresponding sum of jet monomials is nonzero. -/
theorem sum_jet_monomials_ne_zero_of_algebraicIndependent {u : K}
    (h : AlgebraicIndependent F (fun i : ℕ => differentialJet i u))
    {n N : ℕ} (hN : 0 < N) (e : Fin N → Fin (n + 1) → ℕ) (he : Function.Injective e)
    (c : Fin N → F) (hc : ∀ α, c α ≠ 0) :
    ∑ α : Fin N, algebraMap F K (c α)
        * ∏ i : Fin (n + 1), (differentialJet (i : ℕ) u) ^ (e α i) ≠ 0 := by
  classical
  intro hzero
  have hres : AlgebraicIndependent F (fun i : Fin (n + 1) => differentialJet (i : ℕ) u) :=
    h.comp (fun i : Fin (n + 1) => (i : ℕ)) Fin.val_injective
  -- the exponent vectors, as finitely supported functions
  set d : Fin N → (Fin (n + 1) →₀ ℕ) :=
    fun α => Finsupp.indicator (Finset.univ : Finset (Fin (n + 1))) (fun i _ => e α i) with hd
  have hdinj : Function.Injective d := by
    intro α β hab
    refine he ?_
    funext i
    have := congrArg (fun f : Fin (n + 1) →₀ ℕ => f i) hab
    simpa [hd, Finsupp.indicator_apply] using this
  -- the polynomial witnessing the relation
  set p : MvPolynomial (Fin (n + 1)) F :=
    ∑ α : Fin N, MvPolynomial.monomial (d α) (c α) with hp
  have hmono : ∀ α : Fin N,
      (∏ i : Fin (n + 1), (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) F) ^ (e α i))
        = MvPolynomial.monomial (d α) 1 := by
    intro α
    rw [hd]
    exact MvPolynomial.prod_X_pow (fun i => e α i) Finset.univ
  have heval : MvPolynomial.aeval (fun i : Fin (n + 1) => differentialJet (i : ℕ) u) p = 0 := by
    rw [hp, map_sum, ← hzero]
    refine Finset.sum_congr rfl fun α _ => ?_
    have hm : MvPolynomial.monomial (d α) (c α)
        = MvPolynomial.C (c α)
          * ∏ i : Fin (n + 1), (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) F) ^ (e α i) := by
      rw [hmono α, MvPolynomial.C_mul_monomial, mul_one]
    rw [hm, map_mul, MvPolynomial.aeval_C, map_prod]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, MvPolynomial.aeval_X]
  have hp0 : p = 0 := by
    refine hres ?_
    rw [heval, map_zero]
  -- but the coefficient at the first exponent vector is nonzero
  have hcoeff : MvPolynomial.coeff (d ⟨0, hN⟩) p = c ⟨0, hN⟩ := by
    rw [hp, MvPolynomial.coeff_sum]
    rw [Finset.sum_eq_single (⟨0, hN⟩ : Fin N)]
    · rw [MvPolynomial.coeff_monomial, if_pos rfl]
    · intro β _ hβ
      rw [MvPolynomial.coeff_monomial, if_neg]
      intro hdd
      exact hβ (hdinj hdd)
    · intro hmem
      exact absurd (Finset.mem_univ (⟨0, hN⟩ : Fin N)) hmem
  rw [hp0, MvPolynomial.coeff_zero] at hcoeff
  exact hc ⟨0, hN⟩ hcoeff.symm

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

variable {F K : Type*} [Field F] [Field K] [Differential F] [Differential K]
  [Algebra F K] [DifferentialAlgebra F K]

omit [Differential F] [DifferentialAlgebra F K] in
/-- **No relation among the jets means they are algebraically independent.**  A vanishing nonzero
polynomial is enumerated over its support: the exponent vectors are distinct and the coefficients
nonzero, so it is a relation of the shape the finite phase law forbids. -/
theorem algebraicIndependent_of_no_jet_relation {u : K}
    (H : ∀ (n N : ℕ), 0 < N → ∀ e : Fin N → Fin (n + 1) → ℕ, Function.Injective e →
      ∀ c : Fin N → F, (∀ α, c α ≠ 0) →
        ∑ α : Fin N, algebraMap F K (c α)
          * ∏ i : Fin (n + 1), (differentialJet (i : ℕ) u) ^ (e α i) ≠ 0) :
    AlgebraicIndependent F (fun i : ℕ => differentialJet i u) := by
  classical
  rw [algebraicIndependent_iff]
  intro p hp
  by_contra hp0
  -- all variables of `p` are below `n + 1`
  set n : ℕ := p.vars.sup id with hn
  have hvar : ∀ d ∈ p.support, ∀ i ∈ d.support, i ≤ n := by
    intro d hd i hi
    have : i ∈ p.vars := (MvPolynomial.mem_vars_iff_mem_support i).mpr ⟨d, hd, hi⟩
    exact Finset.le_sup (f := id) this
  -- enumerate the support
  set S : Finset (ℕ →₀ ℕ) := p.support with hS
  have hSne : S.Nonempty := by
    rw [hS, Finset.nonempty_iff_ne_empty]
    intro hempty
    exact hp0 (MvPolynomial.support_eq_empty.mp hempty)
  set N : ℕ := S.card with hNdef
  have hNpos : 0 < N := Finset.card_pos.mpr hSne
  set en : Fin N → (ℕ →₀ ℕ) := fun α => ((S.equivFin.symm α : {d // d ∈ S}) : ℕ →₀ ℕ) with hen
  have henmem : ∀ α, en α ∈ S := fun α => (S.equivFin.symm α).2
  have heninj : Function.Injective en := by
    intro α β hab
    have : (S.equivFin.symm α) = (S.equivFin.symm β) := Subtype.ext hab
    exact S.equivFin.symm.injective this
  set e : Fin N → Fin (n + 1) → ℕ := fun α i => (en α) (i : ℕ) with he
  set c : Fin N → F := fun α => MvPolynomial.coeff (en α) p with hc
  have hzero : ∀ (α : Fin N) (i : ℕ), n < i → (en α) i = 0 := by
    intro α i hi
    by_contra hne
    have hmem : i ∈ (en α).support := Finsupp.mem_support_iff.mpr hne
    exact absurd (hvar (en α) (henmem α) i hmem) (by omega)
  have heinj : Function.Injective e := by
    intro α β hab
    refine heninj ?_
    refine Finsupp.ext fun i => ?_
    by_cases hi : i ≤ n
    · have := congrFun hab ⟨i, by omega⟩
      simpa [he] using this
    · rw [hzero α i (by omega), hzero β i (by omega)]
  have hc0 : ∀ α, c α ≠ 0 := by
    intro α
    rw [hc]
    exact MvPolynomial.mem_support_iff.mp (henmem α)
  -- the vanishing polynomial is exactly the forbidden relation
  refine H n N hNpos e heinj c hc0 ?_
  have hprod : ∀ α : Fin N,
      (∏ i ∈ (en α).support, (differentialJet i u) ^ ((en α) i))
        = ∏ i : Fin (n + 1), (differentialJet (i : ℕ) u) ^ (e α i) := by
    intro α
    have hsub : (en α).support ⊆ Finset.range (n + 1) := by
      intro i hi
      have := hvar (en α) (henmem α) i hi
      simpa using by omega
    rw [Finset.prod_subset hsub ?_]
    · rw [Finset.prod_range fun i => (differentialJet i u) ^ ((en α) i)]
    · intro i _ hi
      have : (en α) i = 0 := by
        by_contra hne
        exact hi (Finsupp.mem_support_iff.mpr hne)
      rw [this, pow_zero]
  have hsum : ∑ α : Fin N, algebraMap F K (c α)
      * ∏ i : Fin (n + 1), (differentialJet (i : ℕ) u) ^ (e α i)
      = MvPolynomial.aeval (fun i : ℕ => differentialJet i u) p := by
    rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
    rw [← Finset.sum_coe_sort S (fun d => (algebraMap F K) (MvPolynomial.coeff d p)
      * ∏ i ∈ d.support, (differentialJet i u) ^ d i)]
    refine Fintype.sum_equiv S.equivFin.symm _ _ fun α => ?_
    rw [hc, hprod α]
  rw [hsum, hp]

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

variable {F K : Type*} [Field F] [Field K] [Differential F] [Differential K]
  [Algebra F K] [DifferentialAlgebra F K]

/-- **Inversion preserves the absence of jet relations.**  If no relation with distinct exponents and
nonzero base-field coefficients holds among the jets of a nonzero `u`, then none holds among the jets
of `u⁻¹` either: differential transcendence is invariant under inversion, stated in the relation
language the finite phase law uses. -/
theorem sum_jet_inv_monomials_ne_zero_of_no_jet_relation {u : K} (hu : u ≠ 0)
    (H : ∀ (m M : ℕ), 0 < M → ∀ d : Fin M → Fin (m + 1) → ℕ, Function.Injective d →
      ∀ a : Fin M → F, (∀ α, a α ≠ 0) →
        ∑ α : Fin M, algebraMap F K (a α)
          * ∏ i : Fin (m + 1), (differentialJet (i : ℕ) u) ^ (d α i) ≠ 0)
    {n N : ℕ} (hN : 0 < N) (e : Fin N → Fin (n + 1) → ℕ) (he : Function.Injective e)
    (c : Fin N → F) (hc : ∀ α, c α ≠ 0) :
    ∑ α : Fin N, algebraMap F K (c α)
        * ∏ i : Fin (n + 1), (differentialJet (i : ℕ) u⁻¹) ^ (e α i) ≠ 0 :=
  sum_jet_monomials_ne_zero_of_algebraicIndependent
    (algebraicIndependent_jets_inv hu (algebraicIndependent_of_no_jet_relation H)) hN e he c hc

end GaloisForLFunctions.HTGeometry
