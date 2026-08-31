import GaloisForLFunctions.HTGeometry.SheddingRegularSequence
import GaloisForLFunctions.HTGeometry.StanleyReisnerCone

/-!
# The cone case in regular-sequence form

At a cone point the vertex is a nonzerodivisor and cutting by it gives the deletion, so a regular
sequence on the deletion extends by the vertex:

```text
faceFamilyIdeal_le_deletion    I_F ≤ I_{del(v)}
quotToDeletion                 K[Δ] → K[del(v)]
quotSMulTopEquivDeletion       ** QuotSMulTop (X v) K[Δ] ≃ₗ K[del(v)] **
exists_isRegular_cone
    ** a regular sequence of length n on K[del(v)] gives one of length n+1 on K[Δ] **
```

The module isomorphism is the content: the kernel of `K[Δ] → K[del(v)]` is exactly `X v · K[Δ]`,
because `I_{del(v)} = I_F + (X v)`.  With `RingTheory.Sequence.isRegular_cons_iff` and
`LinearEquiv.isRegular_congr` this turns into the sequence statement.

Together with `exists_isRegular_faceFamily` (the shedding case) these are the two steps of the
Cohen–Macaulay recursion over a simplicial complex, both now in the vocabulary the Cohen–Macaulay
definition uses.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial
open scoped Pointwise

universe u
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {K : Type u} [Field K]

theorem faceFamilyIdeal_le_deletion (K : Type u) [Field K] (F : Finset (Finset σ)) (v : σ) :
    faceFamilyIdeal K F ≤ faceFamilyIdeal K (faceDeletion F v) := by
  rw [faceFamilyIdeal, faceFamilyIdeal]
  exact Finset.inf_mono (Finset.filter_subset _ _)

/-- Cutting the Stanley–Reisner ring by the vertex, as a linear map to the deletion. -/
noncomputable def quotToDeletion (K : Type u) [Field K] (F : Finset (Finset σ)) (v : σ) :
    (MvPolynomial σ K ⧸ faceFamilyIdeal K F) →ₗ[MvPolynomial σ K]
      (MvPolynomial σ K ⧸ faceFamilyIdeal K (faceDeletion F v)) :=
  Submodule.mapQ _ _ LinearMap.id (faceFamilyIdeal_le_deletion K F v)

theorem quotToDeletion_mk (K : Type u) [Field K] (F : Finset (Finset σ)) (v : σ)
    (a : MvPolynomial σ K) :
    quotToDeletion K F v (Submodule.Quotient.mk a) = Submodule.Quotient.mk a := rfl

/-- **Cutting by a cone point is the deletion**, as `R`-modules. -/
noncomputable def quotSMulTopEquivDeletion (K : Type u) [Field K] {F : Finset (Finset σ)}
    (hF : IsFaceFamily F) (v : σ) :
    QuotSMulTop (X v : MvPolynomial σ K) (MvPolynomial σ K ⧸ faceFamilyIdeal K F)
      ≃ₗ[MvPolynomial σ K]
      (MvPolynomial σ K ⧸ faceFamilyIdeal K (faceDeletion F v)) := by
  classical
  have hxv : (X v : MvPolynomial σ K) ∈ faceFamilyIdeal K (faceDeletion F v) := by
    rw [faceFamilyIdeal_faceDeletion K hF v]
    exact Ideal.mem_sup_right (Ideal.subset_span rfl)
  have hkereq : ((X v : MvPolynomial σ K) • (⊤ : Submodule (MvPolynomial σ K)
      (MvPolynomial σ K ⧸ faceFamilyIdeal K F)))
      = LinearMap.ker (quotToDeletion K F v) := by
    refine le_antisymm ?_ ?_
    · intro z hz
      obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hz
      induction y using Submodule.Quotient.induction_on with
      | _ a =>
        rw [LinearMap.mem_ker]
        show quotToDeletion K F v (Submodule.Quotient.mk ((X v : MvPolynomial σ K) * a)) = 0
        rw [quotToDeletion_mk, Submodule.Quotient.mk_eq_zero]
        exact Ideal.mul_mem_right _ _ hxv
    · intro z hz
      induction z using Submodule.Quotient.induction_on with
      | _ a =>
        rw [LinearMap.mem_ker, quotToDeletion_mk, Submodule.Quotient.mk_eq_zero,
          faceFamilyIdeal_faceDeletion K hF v] at hz
        obtain ⟨i, hi, w, hw, hiw⟩ := Submodule.mem_sup.mp hz
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hw
        have hrw : (Submodule.Quotient.mk a : MvPolynomial σ K ⧸ faceFamilyIdeal K F)
            = (X v : MvPolynomial σ K) • Submodule.Quotient.mk c := by
          show _ = Submodule.Quotient.mk ((X v : MvPolynomial σ K) * c)
          rw [Submodule.Quotient.eq]
          have hsub : a - (X v : MvPolynomial σ K) * c = i := by rw [← hiw]; ring
          rw [hsub]
          exact hi
        rw [hrw]
        exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).mpr
          ⟨Submodule.Quotient.mk c, Submodule.mem_top, rfl⟩
  refine LinearEquiv.ofBijective
    (Submodule.liftQ _ (quotToDeletion K F v) (le_of_eq hkereq)) ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot' _ _ hkereq
  · intro w
    induction w using Submodule.Quotient.induction_on with
    | _ a =>
      exact ⟨Submodule.Quotient.mk (Submodule.Quotient.mk a), rfl⟩

/-- **The cone case in regular-sequence form.**  At a cone point, prepending the vertex to a regular
sequence on the deletion gives one on the whole complex. -/
theorem exists_isRegular_cone (K : Type u) [Field K] {F : Finset (Finset σ)}
    (hF : IsFaceFamily F) {v : σ} (hv : IsConePoint F v)
    (𝔪 : Ideal (MvPolynomial σ K)) (hv𝔪 : (X v : MvPolynomial σ K) ∈ 𝔪) {n : ℕ}
    (hdel : ∃ rs : List (MvPolynomial σ K), rs.length = n ∧ (∀ r ∈ rs, r ∈ 𝔪) ∧
      RingTheory.Sequence.IsRegular
        (MvPolynomial σ K ⧸ faceFamilyIdeal K (faceDeletion F v)) rs) :
    ∃ rs : List (MvPolynomial σ K), rs.length = n + 1 ∧ (∀ r ∈ rs, r ∈ 𝔪) ∧
      RingTheory.Sequence.IsRegular (MvPolynomial σ K ⧸ faceFamilyIdeal K F) rs := by
  obtain ⟨rs, hlen, hmem, hreg⟩ := hdel
  refine ⟨(X v : MvPolynomial σ K) :: rs, by simp [hlen], ?_, ?_⟩
  · intro r hr
    rcases List.mem_cons.mp hr with rfl | h
    · exact hv𝔪
    · exact hmem r h
  · rw [RingTheory.Sequence.isRegular_cons_iff]
    refine ⟨(isSMulRegular_quotient_iff _ _).mpr (isRegularOn_X_of_isConePoint K hv), ?_⟩
    exact (LinearEquiv.isRegular_congr (quotSMulTopEquivDeletion K hF v) rs).mpr hreg


end GaloisForLFunctions.HTGeometry
