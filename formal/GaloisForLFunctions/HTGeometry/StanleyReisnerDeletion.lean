import GaloisForLFunctions.HTGeometry.StanleyReisnerBasis

/-!
# The deletion theorem for Stanley–Reisner rings

Killing a vertex in the Stanley–Reisner ring gives the Stanley–Reisner ring of the deletion:

```text
faceDeletion F v                  the faces of `F` avoiding `v`
isFaceFamily_faceDeletion         the deletion is again downward closed
faceFamilyIdeal_faceDeletion      ** I_{del(v)} = I_F + (X v) **
```

The proof splits a polynomial by whether `v` occurs in a monomial: the part without `v` lies in
`I_F` (a face of `F` avoiding `v` would be a face of the deletion), and the part with `v` is
divisible by `X v`.

Deletion and link are the two operations every induction on a simplicial complex uses — vertex
decomposability, shellability, and Reisner's criterion all reduce a complex to these two.  This is
the first of them.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {K : Type u} [Field K]

/-- The deletion of a vertex from a face family. -/
def faceDeletion (F : Finset (Finset σ)) (v : σ) : Finset (Finset σ) :=
  F.filter (fun S => v ∉ S)

omit [Fintype σ] in
theorem mem_faceDeletion {F : Finset (Finset σ)} {v : σ} {S : Finset σ} :
    S ∈ faceDeletion F v ↔ S ∈ F ∧ v ∉ S := by
  simp [faceDeletion]

omit [Fintype σ] in
theorem isFaceFamily_faceDeletion {F : Finset (Finset σ)} (hF : IsFaceFamily F) (v : σ) :
    IsFaceFamily (faceDeletion F v) := by
  intro S T hT hST
  rw [mem_faceDeletion] at hT ⊢
  exact ⟨hF hT.1 hST, fun hv => hT.2 (hST hv)⟩

/-- **The deletion theorem**: killing a vertex in the Stanley–Reisner ring gives the Stanley–Reisner
ring of the deletion. -/
theorem faceFamilyIdeal_faceDeletion (K : Type u) [Field K] {F : Finset (Finset σ)}
    (hF : IsFaceFamily F) (v : σ) :
    faceFamilyIdeal K (faceDeletion F v)
      = faceFamilyIdeal K F ⊔ Ideal.span {(X v : MvPolynomial σ K)} := by
  classical
  refine le_antisymm ?_ ?_
  · intro p hp
    rw [mem_faceFamilyIdeal_iff (isFaceFamily_faceDeletion hF v)] at hp
    have hsplit : ∑ e ∈ p.support.filter (fun e => v ∉ e.support),
          MvPolynomial.monomial e (MvPolynomial.coeff e p)
        + ∑ e ∈ p.support.filter (fun e => v ∈ e.support),
          MvPolynomial.monomial e (MvPolynomial.coeff e p) = p := by
      rw [add_comm, Finset.sum_filter_add_sum_filter_not]
      exact MvPolynomial.support_sum_monomial_coeff p
    refine Submodule.mem_sup.mpr ⟨_, ?_, _, ?_, hsplit⟩
    · refine Ideal.sum_mem _ fun e he => ?_
      rw [Finset.mem_filter] at he
      rw [mem_faceFamilyIdeal_iff hF]
      intro f hf
      have hfe : f = e := by
        have := MvPolynomial.support_monomial_subset (a := MvPolynomial.coeff e p) (s := e) hf
        simpa using this
      subst hfe
      intro hmem
      exact hp f he.1 (mem_faceDeletion.mpr ⟨hmem, he.2⟩)
    · refine Ideal.sum_mem _ fun e he => ?_
      rw [Finset.mem_filter] at he
      rw [Ideal.mem_span_singleton']
      refine ⟨MvPolynomial.monomial (e - Finsupp.single v 1) (MvPolynomial.coeff e p), ?_⟩
      have hle : Finsupp.single v 1 ≤ e := by
        intro w
        by_cases hw : w = v
        · subst hw
          simp only [Finsupp.single_eq_same]
          exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp he.2)
        · rw [Finsupp.single_apply, if_neg (fun h => hw h.symm)]
          exact Nat.zero_le _
      have hX : (X v : MvPolynomial σ K) = MvPolynomial.monomial (Finsupp.single v 1) 1 := rfl
      rw [hX, MvPolynomial.monomial_mul, mul_one, tsub_add_cancel_of_le hle]
  · refine sup_le ?_ ?_
    · rw [faceFamilyIdeal, faceFamilyIdeal]
      exact Finset.inf_mono (Finset.filter_subset _ _)
    · rw [Ideal.span_le]
      rintro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst hx
      rw [SetLike.mem_coe, mem_faceFamilyIdeal_iff (isFaceFamily_faceDeletion hF v)]
      intro e he
      have hev : e = Finsupp.single v 1 := by
        have := MvPolynomial.support_X (R := K) (n := v)
        rw [this] at he
        simpa using he
      rw [hev, mem_faceDeletion]
      rintro ⟨-, hv⟩
      exact hv (by simp)

end GaloisForLFunctions.HTGeometry
