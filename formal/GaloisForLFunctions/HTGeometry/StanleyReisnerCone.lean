import GaloisForLFunctions.HTGeometry.StanleyReisnerFacets
import GaloisForLFunctions.HTGeometry.CohenMacaulayTransport

/-!
# The cone reduction for Cohen–Macaulayness

If `v` is a cone point of a face family — a vertex that can be added to every face — then `X v` is a
nonzerodivisor on the Stanley–Reisner ring, cutting by it gives exactly the Stanley–Reisner ring of
the deletion, and the dimension drops by one.  So Cohen–Macaulayness transfers:

```text
isRegularOn_bot_of_mem_nonZeroDivisors   a nonzerodivisor is regular modulo ⊥
quotXEquivDeletion                       (K[Δ] ⧸ X v) ≃ K[del(v)]
card_le_of_mem_faceDeletion              the deletion loses exactly one from the face size
faceFamilyIdeal_faceDeletion_ne_top      the deletion ideal is proper
isCohenMacaulayRing_of_isConePoint
    ** K[del(v)] Cohen–Macaulay ⟹ K[Δ] Cohen–Macaulay, at a cone point **
```

This is the first genuine Cohen–Macaulay induction step for simplicial complexes, and the base case
of any vertex-decomposability or shellability argument.  It is assembled from
`faceFamilyIdeal_faceDeletion`, `isRegularOn_X_of_isConePoint`, `ringKrullDim_faceFamilyIdeal`,
`isCohenMacaulayRing_of_quotient` and `IsCohenMacaulayRing.of_ringEquiv`.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {K : Type u} [Field K]

theorem isRegularOn_bot_of_mem_nonZeroDivisors {R : Type*} [CommRing R] {x : R}
    (h : x ∈ nonZeroDivisors R) : IsRegularOn (⊥ : Ideal R) x := by
  rw [IsRegularOn, mem_nonZeroDivisors_iff]
  rw [mem_nonZeroDivisors_iff] at h
  constructor
  · intro z hz
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot] at hz
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot]
    exact h.1 y hz
  · intro z hz
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot] at hz
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_bot]
    exact h.2 y hz

/-- The quotient of a Stanley–Reisner ring by a vertex is the Stanley–Reisner ring of the
deletion. -/
noncomputable def quotXEquivDeletion (K : Type u) [Field K] {F : Finset (Finset σ)}
    (hF : IsFaceFamily F) (v : σ) :
    ((MvPolynomial σ K ⧸ faceFamilyIdeal K F) ⧸
        Ideal.ofList [Ideal.Quotient.mk (faceFamilyIdeal K F) (X v)])
      ≃+* MvPolynomial σ K ⧸ faceFamilyIdeal K (faceDeletion F v) := by
  classical
  have hmap : Ideal.ofList [Ideal.Quotient.mk (faceFamilyIdeal K F) (X v)]
      = (Ideal.span {(X v : MvPolynomial σ K)}).map
        (Ideal.Quotient.mk (faceFamilyIdeal K F)) := by
    rw [Ideal.ofList, Ideal.map_span]
    congr 1
    ext x
    simp
  refine (Ideal.quotEquivOfEq hmap).trans ?_
  refine (DoubleQuot.quotQuotEquivQuotSup _ _).trans ?_
  exact Ideal.quotEquivOfEq (faceFamilyIdeal_faceDeletion K hF v).symm

omit [Fintype σ] in
theorem card_le_of_mem_faceDeletion {F : Finset (Finset σ)} {v : σ} (hv : IsConePoint F v)
    {D : ℕ} (hle : ∀ S ∈ F, S.card ≤ D) {S : Finset σ} (hS : S ∈ faceDeletion F v) :
    S.card ≤ D - 1 := by
  classical
  rw [mem_faceDeletion] at hS
  have hins := hle _ (hv S hS.1)
  rw [Finset.card_insert_of_notMem hS.2] at hins
  omega

omit [Fintype σ] in
theorem erase_mem_faceDeletion {F : Finset (Finset σ)} (hF : IsFaceFamily F) {S₀ : Finset σ}
    (hS₀ : S₀ ∈ F) (v : σ) : S₀.erase v ∈ faceDeletion F v := by
  classical
  rw [mem_faceDeletion]
  exact ⟨hF hS₀ (Finset.erase_subset v S₀), Finset.notMem_erase v S₀⟩

theorem faceFamilyIdeal_faceDeletion_ne_top (K : Type u) [Field K] {F : Finset (Finset σ)}
    (hF : IsFaceFamily F) {v : σ} (hne : F.Nonempty) :
    faceFamilyIdeal K (faceDeletion F v) ≠ ⊤ := by
  classical
  obtain ⟨S, hS⟩ := hne
  have hempty : (∅ : Finset σ) ∈ faceDeletion F v := by
    rw [mem_faceDeletion]
    exact ⟨hF hS (Finset.empty_subset S), Finset.notMem_empty v⟩
  intro htop
  have hone : (1 : MvPolynomial σ K) ∈ faceFamilyIdeal K (faceDeletion F v) := by
    rw [htop]; trivial
  rw [mem_faceFamilyIdeal_iff (isFaceFamily_faceDeletion hF v)] at hone
  have h0 : (0 : σ →₀ ℕ) ∈ (1 : MvPolynomial σ K).support := by
    rw [MvPolynomial.support_one]; simp
  exact hone 0 h0 (by simpa using hempty)

/-- **The cone reduction.**  If `v` is a cone point of the face family, the Stanley–Reisner ring is
Cohen–Macaulay as soon as that of the deletion is: `X v` is a nonzerodivisor and cutting by it gives
exactly the deletion, with the dimension dropping by one. -/
theorem isCohenMacaulayRing_of_isConePoint (K : Type u) [Field K] {F : Finset (Finset σ)} {v : σ}
    (hF : IsFaceFamily F) (hv : IsConePoint F v) (hne : F.Nonempty)
    {D : ℕ} (hle : ∀ S ∈ F, S.card ≤ D)
    {S₀ : Finset σ} (hS₀ : S₀ ∈ faceFacets F) (hcard : S₀.card = D)
    (hCM : IsCohenMacaulayRing (MvPolynomial σ K ⧸ faceFamilyIdeal K (faceDeletion F v))) :
    IsCohenMacaulayRing (MvPolynomial σ K ⧸ faceFamilyIdeal K F) := by
  classical
  have hvS₀ : v ∈ S₀ := mem_of_isConePoint hv hS₀
  have hS₀F : S₀ ∈ F := (mem_faceFacets.mp hS₀).1
  have hD : 1 ≤ D := by
    rw [← hcard]
    exact Finset.card_pos.mpr ⟨v, hvS₀⟩
  have hdimF : ringKrullDim (MvPolynomial σ K ⧸ faceFamilyIdeal K F) = ((D : ℕ) : ℕ∞) :=
    ringKrullDim_faceFamilyIdeal K hle hS₀F hcard
  have hdimDel : ringKrullDim (MvPolynomial σ K ⧸ faceFamilyIdeal K (faceDeletion F v))
      = (((D - 1 : ℕ) : ℕ) : ℕ∞) := by
    refine ringKrullDim_faceFamilyIdeal K (fun S hS => card_le_of_mem_faceDeletion hv hle hS)
      (erase_mem_faceDeletion hF hS₀F v) ?_
    rw [Finset.card_erase_of_mem hvS₀, hcard]
  refine isCohenMacaulayRing_of_quotient
    (rs := [Ideal.Quotient.mk (faceFamilyIdeal K F) (X v)]) ?_ ?_ ?_
  · constructor
    · intro i hi
      have hi0 : i = 0 := by simpa using hi
      subst hi0
      simp only [List.take_zero, ofList_nil]
      have hreg : Ideal.Quotient.mk (faceFamilyIdeal K F) (X v)
          ∈ nonZeroDivisors (MvPolynomial σ K ⧸ faceFamilyIdeal K F) :=
        isRegularOn_X_of_isConePoint K hv
      exact isRegularOn_bot_of_mem_nonZeroDivisors hreg
    · intro htop
      have hsub : Subsingleton ((MvPolynomial σ K ⧸ faceFamilyIdeal K F) ⧸
          Ideal.ofList [Ideal.Quotient.mk (faceFamilyIdeal K F) (X v)]) := by
        rw [htop]
        exact Ideal.Quotient.subsingleton_iff.mpr rfl
      have := (quotXEquivDeletion K hF v).symm.toEquiv.subsingleton_congr.mpr hsub
      have htop2 : faceFamilyIdeal K (faceDeletion F v) = ⊤ :=
        Ideal.Quotient.subsingleton_iff.mp this
      exact faceFamilyIdeal_faceDeletion_ne_top K hF hne htop2
  · exact IsCohenMacaulayRing.of_ringEquiv (quotXEquivDeletion K hF v).symm hCM
  · rw [hdimF]
    have hrw : ringKrullDim ((MvPolynomial σ K ⧸ faceFamilyIdeal K F) ⧸
        Ideal.ofList [Ideal.Quotient.mk (faceFamilyIdeal K F) (X v)])
        = (((D - 1 : ℕ) : ℕ) : ℕ∞) := by
      rw [ringKrullDim_eq_of_ringEquiv (quotXEquivDeletion K hF v)]
      exact hdimDel
    rw [hrw]
    simp only [List.length_cons, List.length_nil]
    have : ((D - 1 : ℕ) : ℕ∞) + ((1 : ℕ) : ℕ∞) = ((D : ℕ) : ℕ∞) := by
      have : (D - 1) + 1 = D := by omega
      rw [← Nat.cast_add, this]
    push_cast
    exact_mod_cast congrArg (fun x : ℕ∞ => (x : WithBot ℕ∞)) this


end GaloisForLFunctions.HTGeometry
