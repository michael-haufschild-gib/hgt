import GaloisForLFunctions.HTGeometry.BlockCarrierMonomial
import GaloisForLFunctions.HTGeometry.BlockPermSumIndependence

/-!
# The fibre amplitude of a several-carrier monomial is a blockwise symmetrisation

For one carrier the fibre amplitude at the frequency of an injective tuple is the amplitude product
times a symmetric function of the frequencies.  For several carriers supported on disjoint blocks the
same computation gives the amplitude product times the *blockwise* symmetrisation: only the
permutations preserving the blocks survive, they factor over the blocks, and inside a block the
guard is satisfied so the computation is the one-carrier one.

This is the last identity separating the several-carrier expansion from the coefficient-killing
lemma.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {ι : Type*} [DecidableEq ι] {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **The fibre amplitude of a several-carrier monomial.**  With the `j`-th carrier supported on the
block `blk j`, and a test tuple placing each slot's entry in its own block, the fibre amplitude is
the amplitude product times the blockwise symmetrisation of the exponent family. -/
theorem fiberAmplitude_blockMonomial_eq_blockPermSum {omega : ι → ℝ}
    (h : RationallyIndependentSequence omega) {M : ℕ}
    (a : ι → ℂ) (bidx : ι → κ) (blk : Fin M → κ) (s : Fin M → ℕ)
    {i : Fin M → ι} (hi : Function.Injective i) (hib : ∀ j, bidx (i j) = blk j) :
    fiberAmplitude
        (fun n : Fin M → ι =>
          ∏ j, (if bidx (n j) = blk j then a (n j) else 0)
            * (Complex.I * (omega (n j) : ℂ)) ^ s j)
        (tupleFrequency omega) (tupleFrequency omega i)
      = (∏ l, a (i l)) *
        MvPolynomial.eval (fun l => Complex.I * (omega (i l) : ℂ))
          (blockPermSum blk fun _ b => s (b : Fin M)) := by
  classical
  set x : Fin M → ℂ := fun l => Complex.I * (omega (i l) : ℂ) with hx
  set b : Fin M → ι → ℂ := fun j y => if bidx y = blk j then a y else 0 with hb
  set F : Fin M → Fin M → ℂ := fun j l => b j (i l) * x l ^ s j with hF
  rw [fiberAmplitude_blockMonomial h b s hi]
  have hterm : ∀ σ : Equiv.Perm (Fin M),
      (∏ j, b j (i (σ j)) * (Complex.I * (omega (i (σ j)) : ℂ)) ^ s j) = ∏ j, F j (σ j) := by
    intro σ
    rfl
  rw [Finset.sum_congr rfl fun σ _ => hterm σ]
  have hvanish : ∀ j l : Fin M, blk l ≠ blk j → F j l = 0 := by
    intro j l hjl
    show b j (i l) * x l ^ s j = 0
    have : b j (i l) = 0 := by
      show (if bidx (i l) = blk j then a (i l) else 0) = 0
      rw [if_neg]
      rw [hib l]
      exact hjl
    rw [this, zero_mul]
  rw [sum_perm_prod_of_blockVanishing blk F hvanish]
  -- inside a block the guard is satisfied
  have hblock : ∀ (k : κ) (τ : Equiv.Perm {l : Fin M // blk l = k}),
      (∏ bb : {l : Fin M // blk l = k}, F (bb : Fin M) ((τ bb : {l : Fin M // blk l = k}) : Fin M))
        = (∏ bb : {l : Fin M // blk l = k}, a (i (bb : Fin M)))
          * ∏ bb : {l : Fin M // blk l = k},
              x ((τ bb : {l : Fin M // blk l = k}) : Fin M) ^ s (bb : Fin M) := by
    intro k τ
    have hguard : ∀ bb : {l : Fin M // blk l = k},
        F (bb : Fin M) ((τ bb : {l : Fin M // blk l = k}) : Fin M)
          = a (i ((τ bb : {l : Fin M // blk l = k}) : Fin M))
            * x ((τ bb : {l : Fin M // blk l = k}) : Fin M) ^ s (bb : Fin M) := by
      intro bb
      show b (bb : Fin M) (i ((τ bb : {l : Fin M // blk l = k}) : Fin M)) * _ = _
      congr 1
      show (if bidx (i ((τ bb : {l : Fin M // blk l = k}) : Fin M)) = blk (bb : Fin M)
        then a (i ((τ bb : {l : Fin M // blk l = k}) : Fin M)) else 0) = _
      rw [if_pos]
      rw [hib, (τ bb).2, bb.2]
    rw [Finset.prod_congr rfl fun bb _ => hguard bb, Finset.prod_mul_distrib]
    congr 1
    exact Fintype.prod_equiv τ _ _ fun bb => rfl
  rw [Finset.prod_congr rfl fun k _ => by
    rw [Finset.sum_congr rfl fun τ _ => hblock k τ, ← Finset.mul_sum]]
  -- the amplitude factors out of every block
  rw [Finset.prod_mul_distrib]
  congr 1
  · rw [← Fintype.prod_sigma
      (fun p : Σ k : κ, {l : Fin M // blk l = k} => a (i (p.2 : Fin M)))]
    refine Fintype.prod_equiv (Equiv.sigmaFiberEquiv blk)
      (fun p : Σ k : κ, {l : Fin M // blk l = k} => a (i (p.2 : Fin M)))
      (fun l : Fin M => a (i l)) ?_
    rintro ⟨k, ⟨l, rfl⟩⟩
    rfl
  · -- the surviving sums assemble into the blockwise symmetrisation
    rw [eval_blockPermSum]
    have hcomm : ∀ k : κ,
        (∑ τ : Equiv.Perm {l : Fin M // blk l = k},
            ∏ bb : {l : Fin M // blk l = k},
              x ((τ bb : {l : Fin M // blk l = k}) : Fin M) ^ s (bb : Fin M))
          = ∑ τ : Equiv.Perm {l : Fin M // blk l = k},
              ∏ bb : {l : Fin M // blk l = k},
                x (bb : Fin M) ^ s ((τ bb : {l : Fin M // blk l = k}) : Fin M) :=
      fun k => sum_perm_prod_pow_comm (fun bb : {l : Fin M // blk l = k} => x (bb : Fin M))
        (fun bb : {l : Fin M // blk l = k} => s (bb : Fin M))
    rw [Finset.prod_congr rfl fun k _ => hcomm k, Finset.prod_univ_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [← Fintype.prod_sigma
      (fun p : Σ k : κ, {l : Fin M // blk l = k} =>
        x (p.2 : Fin M) ^ s ((τ p.1 p.2 : {l : Fin M // blk l = p.1}) : Fin M))]
    refine Fintype.prod_equiv (Equiv.sigmaFiberEquiv blk)
      (fun p : Σ k : κ, {l : Fin M // blk l = k} =>
        x (p.2 : Fin M) ^ s ((τ p.1 p.2 : {l : Fin M // blk l = p.1}) : Fin M))
      (fun l : Fin M => x l ^ s ((τ (blk l) ⟨l, rfl⟩ : {m : Fin M // blk m = blk l}) : Fin M))
      ?_
    rintro ⟨k, ⟨l, rfl⟩⟩
    rfl

end

end GaloisForLFunctions.HTGeometry
