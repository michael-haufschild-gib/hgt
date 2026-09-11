import GaloisForLFunctions.HTGeometry.ToricIsogenyTailLaw

/-!
# Quotient positions of an arbitrary split-torus isogeny

Theorem A of the isogeny-tail card already holds for every nonsingular integer character matrix
(`torusEndo_stableRangeCore_eq_torusInvariantMonomialField`): the stable tail is the field generated
by the logarithmic currents together with the monomials whose exponent vector is annihilated by the
erased sector.  What the corpus previously computed only for *diagonal* matrices is which exponent
vectors those are.

This leaf supplies the general answer on the survivor side.  For a constant protocol the prefix
matrices are exactly the matrix powers (`prefixMatrix_const`), so the erased sector is the union of
the deck kernels `ker(torusMonomialHom C (Aⁿ))`.  A character pulled back along `Aⁿ`, i.e. of the
form `k ↦ ∑ i, b i * (Aⁿ) i k`, is automatically trivial on that kernel
(`mem_scaleAnnihilator_ker_torusMonomialHom`), because regrouping the double product turns it into a
product of the coordinates of the substituted point.  Hence every character lying in the **eventual
image lattice** `⋂ₙ (Aⁿ)ᵀ ℤʳ` annihilates the whole erased sector
(`mem_scaleAnnihilator_erasedSector_const`), and the corresponding Laurent monomial survives the
infinite coarse-graining:

```text
laurentMonomial_mem_stableRangeCore_of_eventual_image
```

The eventual image lattice is exactly the character lattice of the maximal quotient torus on which
the isogeny is reversible, so this is the *position* half of Theorem B for an arbitrary — not
necessarily diagonal — split-torus isogeny.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

universe u

variable {r : ℕ}

/-- A constant torus protocol accumulates matrix powers. -/
theorem prefixMatrix_const (A : Matrix (Fin r) (Fin r) ℤ) (i n : ℕ) :
    prefixMatrix (fun _ => A) i n = A ^ n := by
  induction n generalizing i with
  | zero => rw [prefixMatrix_zero, pow_zero]
  | succ n ih => rw [prefixMatrix_succ, ih (i + 1), pow_succ]

variable {C : Type u} [Field C]

private theorem zpow_finset_sum (x : Cˣ) (s : Finset (Fin r)) (c : Fin r → ℤ) :
    x ^ (∑ i ∈ s, c i) = ∏ i ∈ s, x ^ (c i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add, ih]

private theorem finset_prod_zpow (s : Finset (Fin r)) (f : Fin r → Cˣ) (m : ℤ) :
    (∏ i ∈ s, f i) ^ m = ∏ i ∈ s, (f i) ^ m := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, mul_zpow, ih]

/-- **Pulled-back characters annihilate the deck kernel.**  A character of the form `Mᵀ b`
is trivial on the kernel of the monomial substitution by `M`. -/
theorem mem_scaleAnnihilator_ker_torusMonomialHom
    (M : Matrix (Fin r) (Fin r) ℤ) (b : Fin r → ℤ) :
    (fun k => ∑ i, b i * M i k) ∈
      scaleAnnihilator C ((torusMonomialHom C M).ker : Set (Fin r → Cˣ)) := by
  classical
  intro u hu
  have hker : torusMonomialHom C M u = 1 := hu
  have hunits : (∏ k, (u k) ^ (∑ i, b i * M i k) : Cˣ) = 1 := by
    calc (∏ k, (u k) ^ (∑ i, b i * M i k) : Cˣ)
        = ∏ k, ∏ i, (u k) ^ (b i * M i k) := by
          exact Finset.prod_congr rfl fun k _ => zpow_finset_sum (u k) _ _
      _ = ∏ i, ∏ k, (u k) ^ (b i * M i k) := Finset.prod_comm
      _ = ∏ i, ∏ k, ((u k) ^ (M i k)) ^ (b i) := by
          refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun k _ => ?_
          rw [← zpow_mul, mul_comm (M i k) (b i)]
      _ = ∏ i, (∏ k, (u k) ^ (M i k)) ^ (b i) := by
          exact Finset.prod_congr rfl fun i _ => (finset_prod_zpow _ _ _).symm
      _ = ∏ i, (torusMonomialHom C M u i) ^ (b i) := rfl
      _ = 1 := by
          rw [hker]
          simp
  have hcoe : (∏ k, ((u k : C)) ^ (∑ i, b i * M i k)) =
      ((∏ k, (u k) ^ (∑ i, b i * M i k) : Cˣ) : C) := by
    push_cast
    rfl
  rw [hcoe, hunits, Units.val_one]

/-- **Characters in the eventual image lattice are erased-sector invariant.**  If a character is a
pullback along every power of the isogeny matrix, it is trivial on the whole erased sector. -/
theorem mem_scaleAnnihilator_erasedSector_const
    (A : Matrix (Fin r) (Fin r) ℤ) (a : Fin r → ℤ)
    (ha : ∀ n : ℕ, ∃ b : Fin r → ℤ, a = fun k => ∑ i, b i * (A ^ n) i k) :
    a ∈ scaleAnnihilator C
      ((erasedSector (torusProtocolGroup C fun _ => A) 0 : Subgroup (Fin r → Cˣ)) :
        Set (Fin r → Cˣ)) := by
  intro u hu
  obtain ⟨n, hn⟩ := (mem_erasedSector_iff (torusProtocolGroup C fun _ => A) 0 u).1 hu
  rw [prefixHom_torusProtocolGroup, prefixMatrix_const] at hn
  obtain ⟨b, hb⟩ := ha n
  have hker : u ∈ ((torusMonomialHom C (A ^ n)).ker : Set (Fin r → Cˣ)) := hn
  have := mem_scaleAnnihilator_ker_torusMonomialHom (C := C) (A ^ n) b u hker
  rw [hb]
  exact this


section Tail

variable {C E : Type u} [Field C] [Field E] [Algebra C E] [Differential C] [Differential E]
  [DifferentialAlgebra C E] [CharZero E] [CharZero C] [IsAlgClosed C]

variable {x : Fin r → E} (hx : DifferentialIndependent C x)
  (hgen : differentialAdjoin C (Set.range x) = ⊤)

include hx hgen in
/-- **Quotient positions of an arbitrary split-torus isogeny lie in its stable tail.**  For every
nonsingular integer character matrix, a Laurent monomial whose exponent vector is a pullback along
every matrix power — that is, a character of the maximal quotient torus on which the isogeny is
reversible — survives the infinite coarse-graining. -/
theorem laurentMonomial_mem_stableRangeCore_of_eventual_image
    (hconst : ∀ c : C, c′ = 0) {A : Matrix (Fin r) (Fin r) ℤ} (hA : A.det ≠ 0)
    (a : Fin r → ℤ)
    (ha : ∀ n : ℕ, ∃ b : Fin r → ℤ, a = fun k => ∑ i, b i * (A ^ n) i k) :
    laurentMonomial x a ∈ stableRangeCore (torusEndo hx hgen hA) := by
  rw [torusEndo_stableRangeCore_eq_torusInvariantMonomialField hx hgen hconst hA]
  have hmem : laurentMonomial x a ∈ torusInvariantMonomialField C x
      ((erasedSector (torusProtocolGroup C fun _ => A) 0 : Subgroup (Fin r → Cˣ)) :
        Set (Fin r → Cˣ)) := by
    refine IntermediateField.subset_adjoin _ _ ?_
    exact ⟨a, mem_scaleAnnihilator_erasedSector_const A a ha, rfl⟩
  exact hmem

end Tail

end

end GaloisForLFunctions.HTGeometry
