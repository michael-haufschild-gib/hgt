import GaloisForLFunctions.HTGeometry.PermutationSumIndependence
import GaloisForLFunctions.HTGeometry.BlockPermanent

/-!
# Blockwise symmetrised monomials of distinct multiset families are independent

With several carriers the fibre amplitude of a monomial is a product of one-carrier permutation
sums, one per block.  As a polynomial in the frequency variables this is the *blockwise*
symmetrisation of a monomial: the sum over all families of block permutations of the monomial they
produce.

Two such symmetrisations coincide only when the exponent multisets agree block by block, so
blockwise symmetrisations of families that are pairwise distinct blockwise are linearly independent.
The proof is the one-block proof read off the same coefficient: the sorted exponent vector sees only
its own symmetrisation, with positive multiplicity.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {α κ : Type*} [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ]

/-- The exponent vector on the whole index set assembled from blockwise exponents. -/
def concatExp (blk : α → κ) (S : ∀ k : κ, {a : α // blk a = k} → ℕ) : α → ℕ :=
  fun a => S (blk a) ⟨a, rfl⟩

omit [Fintype α] [DecidableEq α] [Fintype κ] [DecidableEq κ] in
/-- Two blockwise exponent families with the same assembled vector agree block by block. -/
theorem eq_of_concatExp_eq {blk : α → κ} {S S' : ∀ k : κ, {a : α // blk a = k} → ℕ}
    (h : concatExp blk S = concatExp blk S') (k : κ) : S k = S' k := by
  funext b
  obtain ⟨a, rfl⟩ := b
  exact congrFun h a

/-- The blockwise symmetrisation of a monomial. -/
def blockPermSum (blk : α → κ) (S : ∀ k : κ, {a : α // blk a = k} → ℕ) : MvPolynomial α ℂ :=
  ∑ τ : ∀ k : κ, Equiv.Perm {a : α // blk a = k},
    MvPolynomial.monomial
      (Finsupp.equivFunOnFinite.symm (concatExp blk fun k => (S k) ∘ (τ k))) 1

theorem coeff_blockPermSum (blk : α → κ) (S : ∀ k : κ, {a : α // blk a = k} → ℕ) (e : α → ℕ) :
    MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm e) (blockPermSum blk S)
      = ((({τ : ∀ k : κ, Equiv.Perm {a : α // blk a = k} |
          concatExp blk (fun k => (S k) ∘ (τ k)) = e} :
        Finset (∀ k : κ, Equiv.Perm {a : α // blk a = k})).card : ℂ)) := by
  classical
  rw [blockPermSum, MvPolynomial.coeff_sum]
  rw [Finset.sum_congr rfl fun τ _ => MvPolynomial.coeff_monomial _ _ _]
  have hcond : ∀ τ : ∀ k : κ, Equiv.Perm {a : α // blk a = k},
      ((Finsupp.equivFunOnFinite.symm (concatExp blk fun k => (S k) ∘ (τ k)))
          = Finsupp.equivFunOnFinite.symm e)
        ↔ (concatExp blk (fun k => (S k) ∘ (τ k)) = e) :=
    fun τ => Equiv.apply_eq_iff_eq _
  simp only [hcond]
  rw [Finset.sum_boole]

/-- The value of a blockwise symmetrisation: the sum over families of block permutations of the
monomial each produces. -/
theorem eval_blockPermSum (blk : α → κ) (S : ∀ k : κ, {a : α // blk a = k} → ℕ) (x : α → ℂ) :
    MvPolynomial.eval x (blockPermSum blk S)
      = ∑ τ : ∀ k : κ, Equiv.Perm {a : α // blk a = k},
          ∏ l : α, x l ^ (S (blk l) (τ (blk l) ⟨l, rfl⟩)) := by
  classical
  rw [blockPermSum, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [MvPolynomial.eval_monomial, one_mul, Finsupp.prod_fintype _ _ fun i => pow_zero (x i)]
  rfl

/-- Permuting the variables of a monomial is permuting its exponents. -/
theorem sum_perm_prod_pow_comm {β : Type*} [Fintype β] [DecidableEq β] (x : β → ℂ)
    (s : β → ℕ) :
    ∑ τ : Equiv.Perm β, ∏ b : β, x (τ b) ^ s b
      = ∑ τ : Equiv.Perm β, ∏ b : β, x b ^ s (τ b) := by
  classical
  have hstep : ∀ τ : Equiv.Perm β, (∏ b : β, x (τ b) ^ s b) = ∏ c : β, x c ^ s (τ.symm c) := by
    intro τ
    refine Fintype.prod_equiv τ _ _ fun b => ?_
    rw [Equiv.symm_apply_apply]
  rw [Finset.sum_congr rfl fun τ _ => hstep τ]
  exact Fintype.sum_equiv (Equiv.inv (Equiv.Perm β)) _ _ fun τ => rfl

/-- **Blockwise symmetrisations of blockwise distinct multiset families are linearly
independent.** -/
theorem eq_zero_of_blockPermSum_combination (blk : α → κ)
    {K : Finset (∀ k : κ, {a : α // blk a = k} → ℕ)}
    (c : (∀ k : κ, {a : α // blk a = k} → ℕ) → ℂ)
    (hdistinct : ∀ S ∈ K, ∀ S' ∈ K, (∀ k, tupleCount (S k) = tupleCount (S' k)) → S = S')
    (h : ∑ S ∈ K, c S • blockPermSum blk S = 0) : ∀ S ∈ K, c S = 0 := by
  classical
  intro S₀ hS₀
  have hcoeff := congrArg
    (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm (concatExp blk S₀))) h
  rw [MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at hcoeff
  set W : (∀ k : κ, {a : α // blk a = k} → ℕ) →
      Finset (∀ k : κ, Equiv.Perm {a : α // blk a = k}) :=
    fun S => {τ | concatExp blk (fun k => (S k) ∘ (τ k)) = concatExp blk S₀} with hW
  have hterm : ∀ S ∈ K,
      MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm (concatExp blk S₀))
          (c S • blockPermSum blk S)
        = if S = S₀ then c S₀ * ((W S₀).card : ℂ) else 0 := by
    intro S hS
    rw [MvPolynomial.coeff_smul, smul_eq_mul, coeff_blockPermSum]
    by_cases hSS : S = S₀
    · subst hSS
      rw [if_pos rfl]
    · rw [if_neg hSS]
      have hempty : W S = ∅ := by
        refine Finset.eq_empty_of_forall_notMem fun τ hτ => ?_
        rw [hW, Finset.mem_filter] at hτ
        refine hSS (hdistinct S hS S₀ hS₀ fun k => ?_)
        have hk : (S k) ∘ (τ k) = S₀ k := eq_of_concatExp_eq hτ.2 k
        have : tupleCount ((S k) ∘ (τ k)) = tupleCount (S₀ k) := by rw [hk]
        rwa [show ((S k) ∘ (τ k)) = fun b => S k (τ k b) from rfl,
          tupleCount_comp_perm] at this
      simp only [hW] at hempty
      rw [hempty]
      simp
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' K S₀, if_pos hS₀] at hcoeff
  have hpos : 0 < (W S₀).card := by
    refine Finset.card_pos.mpr ⟨fun _ => Equiv.refl _, ?_⟩
    rw [hW, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, rfl⟩
  have hne : ((W S₀).card : ℂ) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.mpr hpos.ne'
  exact (mul_eq_zero.mp hcoeff).resolve_right hne

end

end GaloisForLFunctions.HTGeometry
