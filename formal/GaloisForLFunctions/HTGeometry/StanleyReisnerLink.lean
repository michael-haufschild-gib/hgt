import GaloisForLFunctions.HTGeometry.StanleyReisnerDeletion
import GaloisForLFunctions.HTGeometry.MonomialRegularity

/-!
# The link theorem for Stanley–Reisner rings

The link of a vertex is the second operation every induction on a simplicial complex runs on.  Its
Stanley–Reisner ideal is the colon ideal by the vertex, enlarged by the vertex itself:

```text
faceLink F v                   the faces `S` with `v ∉ S` and `S ∪ {v}` a face
isFaceFamily_faceLink          the link is again downward closed
support_X_mul, support_single_add    multiplying by a variable translates the support
faceFamilyIdeal_faceLink       ** I_{lk(v)} = (I_F : X v) + (X v) **
```

Together with `faceFamilyIdeal_faceDeletion` (`I_{del(v)} = I_F + (X v)`) this is the pair of
reductions that vertex decomposability, shellability, and Reisner's criterion all run on.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {K : Type u} [Field K]

/-- The link of a vertex in a face family. -/
def faceLink (F : Finset (Finset σ)) (v : σ) : Finset (Finset σ) :=
  F.filter (fun S => v ∉ S ∧ insert v S ∈ F)

omit [Fintype σ] in
theorem mem_faceLink {F : Finset (Finset σ)} {v : σ} {S : Finset σ} :
    S ∈ faceLink F v ↔ S ∈ F ∧ v ∉ S ∧ insert v S ∈ F := by
  simp [faceLink]

omit [Fintype σ] in
theorem isFaceFamily_faceLink {F : Finset (Finset σ)} (hF : IsFaceFamily F) (v : σ) :
    IsFaceFamily (faceLink F v) := by
  intro S T hT hST
  rw [mem_faceLink] at hT ⊢
  refine ⟨hF hT.1 hST, fun hv => hT.2.1 (hST hv), hF hT.2.2 (Finset.insert_subset_insert v hST)⟩

omit [Fintype σ] [DecidableEq σ] in
theorem support_X_mul (v : σ) (p : MvPolynomial σ K) :
    (X v * p).support = p.support.map (addRightEmbedding (Finsupp.single v 1)) := by
  have hX : (X v : MvPolynomial σ K) = MvPolynomial.monomial (Finsupp.single v 1) 1 := rfl
  rw [hX, mul_comm, support_mul_monomial_one]

omit [Fintype σ] in
theorem support_single_add (v : σ) (f : σ →₀ ℕ) :
    (Finsupp.single v 1 + f).support = insert v f.support := by
  classical
  ext w
  simp only [Finsupp.mem_support_iff, Finsupp.add_apply, Finset.mem_insert]
  by_cases hw : w = v
  · subst hw
    simp
  · rw [Finsupp.single_apply, if_neg (fun h => hw h.symm)]
    simp [hw]

/-- **The link theorem**: the Stanley–Reisner ideal of the link is the colon ideal by the vertex,
enlarged by the vertex itself. -/
theorem faceFamilyIdeal_faceLink (K : Type u) [Field K] {F : Finset (Finset σ)}
    (hF : IsFaceFamily F) (v : σ) :
    faceFamilyIdeal K (faceLink F v)
      = (faceFamilyIdeal K F).colon (Ideal.span {(X v : MvPolynomial σ K)})
        ⊔ Ideal.span {(X v : MvPolynomial σ K)} := by
  classical
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · intro p hp
    rw [mem_faceFamilyIdeal_iff (isFaceFamily_faceLink hF v)] at hp
    have hsplit : ∑ e ∈ p.support.filter (fun e => v ∉ e.support),
          MvPolynomial.monomial e (MvPolynomial.coeff e p)
        + ∑ e ∈ p.support.filter (fun e => v ∈ e.support),
          MvPolynomial.monomial e (MvPolynomial.coeff e p) = p := by
      rw [add_comm, Finset.sum_filter_add_sum_filter_not]
      exact MvPolynomial.support_sum_monomial_coeff p
    refine Submodule.mem_sup.mpr ⟨_, ?_, _, ?_, hsplit⟩
    · have hkey : (X v : MvPolynomial σ K) *
          (∑ e ∈ p.support.filter (fun e => v ∉ e.support),
            MvPolynomial.monomial e (MvPolynomial.coeff e p)) ∈ faceFamilyIdeal K F := by
        rw [Finset.mul_sum]
        refine Ideal.sum_mem _ fun e he => ?_
        rw [Finset.mem_filter] at he
        rw [mem_faceFamilyIdeal_iff hF]
        intro f hf
        rw [support_X_mul] at hf
        simp only [Finset.mem_map, addRightEmbedding_apply] at hf
        obtain ⟨g, hg, rfl⟩ := hf
        have hge : g = e := by
          have := MvPolynomial.support_monomial_subset (a := MvPolynomial.coeff e p) (s := e) hg
          simpa using this
        subst hge
        rw [add_comm, support_single_add]
        intro hmem
        exact hp g he.1 (mem_faceLink.mpr ⟨hF hmem (Finset.subset_insert v _), he.2, hmem⟩)
      rw [Submodule.mem_colon]
      intro y hy
      rw [SetLike.mem_coe, Ideal.mem_span_singleton'] at hy
      obtain ⟨c, rfl⟩ := hy
      rw [smul_eq_mul]
      have hrw : (∑ e ∈ p.support.filter (fun e => v ∉ e.support),
          MvPolynomial.monomial e (MvPolynomial.coeff e p)) * (c * X v)
          = c * ((X v : MvPolynomial σ K) *
            ∑ e ∈ p.support.filter (fun e => v ∉ e.support),
              MvPolynomial.monomial e (MvPolynomial.coeff e p)) := by ring
      rw [hrw]
      exact Ideal.mul_mem_left _ _ hkey
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
  · intro p hp
    rw [Submodule.mem_colon] at hp
    have hpX : (X v : MvPolynomial σ K) * p ∈ faceFamilyIdeal K F := by
      have := hp (X v) (Ideal.subset_span rfl)
      rwa [smul_eq_mul, mul_comm] at this
    rw [mem_faceFamilyIdeal_iff hF] at hpX
    rw [mem_faceFamilyIdeal_iff (isFaceFamily_faceLink hF v)]
    intro f hf hmem
    rw [mem_faceLink] at hmem
    have hin : Finsupp.single v 1 + f ∈ (X v * p).support := by
      rw [support_X_mul]
      simp only [Finset.mem_map, addRightEmbedding_apply]
      exact ⟨f, hf, by rw [add_comm]⟩
    have := hpX _ hin
    rw [support_single_add] at this
    exact this hmem.2.2
  · rw [Ideal.span_le]
    rintro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    rw [SetLike.mem_coe, mem_faceFamilyIdeal_iff (isFaceFamily_faceLink hF v)]
    intro e he
    have hev : e = Finsupp.single v 1 := by
      have := MvPolynomial.support_X (R := K) (n := v)
      rw [this] at he
      simpa using he
    rw [hev, mem_faceLink]
    rintro ⟨-, hv, -⟩
    exact hv (by simp)

end GaloisForLFunctions.HTGeometry
