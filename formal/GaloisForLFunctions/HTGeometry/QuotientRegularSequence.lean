import GaloisForLFunctions.HTGeometry.CoordinateVariableRegular
import GaloisForLFunctions.HTGeometry.PolynomialCohenMacaulay

/-!
# Regular sequences on a quotient ring

Mathlib's `RingTheory.Sequence.IsRegular M rs` for `M = R ⧸ I` is, unwound, the statement that each
entry is a nonzerodivisor modulo `I` together with the earlier entries.  Unwinding it needs the
identification of the successive quotients:

```text
isSMulRegular_congr                 regularity transports along a linear equivalence
smul_top_eq_map_quotient            J • ⊤ inside R ⧸ I is the image ideal
quotQuotLinearEquiv                 the double quotient identification is R-linear
quotSMulTopIdealEquiv               ** (R ⧸ I) ⧸ (J • ⊤) ≃ₗ[R] R ⧸ (I ⊔ J) **
smul_top_eq_top_iff                 and it is everything exactly when I ⊔ J is
isRegular_quotient_of_isRegularOn   ** hence the criterion, entry by entry **
```

For coordinate ideals the criterion is immediate, because the ideal generated at each stage is again
a coordinate ideal and a variable outside one is regular on it:

```text
isRegular_map_X       variables outside a coordinate ideal are a regular sequence on its quotient
isRegular_powerset    ** the base case: on a full simplex the V-variables are regular **
```

The base case is the anchor of the Cohen–Macaulay recursion over a simplicial complex: a full
simplex on `V` has a regular sequence of length `V.card`, which is its dimension.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Pointwise

universe u v
variable {R : Type u} [CommRing R]

theorem isSMulRegular_congr {M M' : Type v} [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] (e : M ≃ₗ[R] M') (x : R) :
    IsSMulRegular M x ↔ IsSMulRegular M' x := by
  constructor
  · intro h a b hab
    have hab' : x • a = x • b := hab
    have hstep : x • e.symm a = x • e.symm b := by
      rw [← map_smul, ← map_smul, hab']
    exact e.symm.injective (h hstep)
  · intro h a b hab
    have hab' : x • a = x • b := hab
    have hstep : x • e a = x • e b := by
      rw [← map_smul, ← map_smul, hab']
    exact e.injective (h hstep)

theorem smul_top_eq_map_quotient (I J : Ideal R) :
    (J • (⊤ : Submodule R (R ⧸ I)))
      = Submodule.restrictScalars R (Ideal.map (Ideal.Quotient.mk I) J) := by
  rw [Ideal.smul_top_eq_map]
  rfl

/-- The double quotient identification is `R`-linear. -/
noncomputable def quotQuotLinearEquiv (I J : Ideal R) :
    ((R ⧸ I) ⧸ Ideal.map (Ideal.Quotient.mk I) J) ≃ₗ[R] (R ⧸ (I ⊔ J)) where
  __ := DoubleQuot.quotQuotEquivQuotSup I J
  map_smul' := by
    intro r x
    induction x using Quotient.inductionOn with
    | h y =>
      induction y using Quotient.inductionOn with
      | h a =>
        simp only [RingHom.id_apply]
        rfl

/-- **Cutting `R ⧸ I` by an ideal gives the quotient by the sum.** -/
noncomputable def quotSMulTopIdealEquiv (I J : Ideal R) :
    ((R ⧸ I) ⧸ (J • (⊤ : Submodule R (R ⧸ I)))) ≃ₗ[R] (R ⧸ (I ⊔ J)) :=
  (Submodule.quotEquivOfEq _ _ (smul_top_eq_map_quotient I J)).trans
    ((Submodule.Quotient.restrictScalarsEquiv R _).trans (quotQuotLinearEquiv I J))


namespace Extra

open scoped Pointwise

theorem smul_top_eq_top_iff (I J : Ideal R) :
    (⊤ : Submodule R (R ⧸ I)) = J • ⊤ ↔ I ⊔ J = ⊤ := by
  constructor
  · intro h
    have hsub : Subsingleton ((R ⧸ I) ⧸ (J • (⊤ : Submodule R (R ⧸ I)))) := by
      rw [Submodule.Quotient.subsingleton_iff]
      exact h.symm
    have : Subsingleton (R ⧸ (I ⊔ J)) :=
      (quotSMulTopIdealEquiv I J).toEquiv.symm.subsingleton
    exact Ideal.Quotient.subsingleton_iff.mp this
  · intro h
    have : Subsingleton (R ⧸ (I ⊔ J)) := Ideal.Quotient.subsingleton_iff.mpr h
    have hsub : Subsingleton ((R ⧸ I) ⧸ (J • (⊤ : Submodule R (R ⧸ I)))) :=
      (quotSMulTopIdealEquiv I J).toEquiv.subsingleton
    exact (Submodule.Quotient.subsingleton_iff.mp hsub).symm

/-- **A sequence is regular on `R ⧸ I` when each entry is a nonzerodivisor modulo `I` together with
the earlier entries.** -/
theorem isRegular_quotient_of_isRegularOn (I : Ideal R) (rs : List R)
    (hreg : ∀ i, ∀ h : i < rs.length, IsRegularOn (I ⊔ Ideal.ofList (rs.take i)) rs[i])
    (hproper : I ⊔ Ideal.ofList rs ≠ ⊤) :
    RingTheory.Sequence.IsRegular (R ⧸ I) rs := by
  refine ⟨⟨fun i hi => ?_⟩, ?_⟩
  · rw [isSMulRegular_congr (quotSMulTopIdealEquiv I (Ideal.ofList (rs.take i)))]
    exact (isSMulRegular_quotient_iff _ _).mpr (hreg i hi)
  · intro htop
    exact hproper ((smul_top_eq_top_iff I (Ideal.ofList rs)).mp htop)

end Extra

section Coordinate

open MvPolynomial

variable {σ : Type*} [DecidableEq σ] {K : Type u} [Field K]

omit [DecidableEq σ] in
theorem ofList_map_X_set (l : List σ) :
    Ideal.ofList (l.map (X : σ → MvPolynomial σ K))
      = Ideal.span (X '' {j : σ | j ∈ l}) := by
  rw [Ideal.ofList]
  congr 1
  ext p
  simp

omit [DecidableEq σ] in
theorem span_X_image_ne_top (S : Set σ) :
    Ideal.span (X '' S) ≠ (⊤ : Ideal (MvPolynomial σ K)) := by
  intro htop
  have hone : (1 : MvPolynomial σ K) ∈ Ideal.span (X '' S) := by rw [htop]; trivial
  rw [MvPolynomial.mem_ideal_span_X_image] at hone
  have hsupp : (0 : σ →₀ ℕ) ∈ (1 : MvPolynomial σ K).support := by
    simp [MvPolynomial.support_one]
  obtain ⟨j, _, hj⟩ := hone _ hsupp
  simp at hj

omit [DecidableEq σ] in
theorem sup_span_X_image (S T : Set σ) :
    (Ideal.span (X '' S) ⊔ Ideal.span (X '' T) : Ideal (MvPolynomial σ K))
      = Ideal.span (X '' (S ∪ T)) := by
  rw [← Ideal.span_union, ← Set.image_union]

/-- **The variables outside a coordinate ideal form a regular sequence on its quotient.**  This is
the regular sequence of the simplex base case: on `K[Δ]` for a full simplex on `V`, the variables of
`V` are regular, one after another, and there are `|V|` of them. -/
theorem isRegular_map_X (W : Set σ) (l : List σ) (hnodup : l.Nodup)
    (hdisj : ∀ j ∈ l, j ∉ W) :
    RingTheory.Sequence.IsRegular
      (MvPolynomial σ K ⧸ (Ideal.span (X '' W) : Ideal (MvPolynomial σ K)))
      (l.map (X : σ → MvPolynomial σ K)) := by
  classical
  refine Extra.isRegular_quotient_of_isRegularOn _ _ (fun i hi => ?_) ?_
  · rw [List.length_map] at hi
    rw [← List.map_take, ofList_map_X_set, sup_span_X_image, List.getElem_map]
    haveI : DecidablePred (· ∈ W ∪ {j : σ | j ∈ l.take i}) := Classical.decPred _
    refine isRegularOn_X_span_X_image ?_
    intro hmem
    rcases hmem with hW | hT
    · exact hdisj _ (List.getElem_mem hi) hW
    · exact getElem_notMem_take_of_nodup hnodup hi hT
  · rw [ofList_map_X_set, sup_span_X_image]
    exact span_X_image_ne_top _

/-- **The base case of the Cohen–Macaulay recursion.**  On the Stanley–Reisner ring of a full
simplex on `V`, the variables of `V` are a regular sequence, of length `V.card`. -/
theorem isRegular_powerset [Fintype σ] (V : Finset σ) :
    RingTheory.Sequence.IsRegular (MvPolynomial σ K ⧸ faceFamilyIdeal K V.powerset)
      (V.toList.map (X : σ → MvPolynomial σ K)) := by
  classical
  rw [faceFamilyIdeal_powerset]
  refine isRegular_map_X _ _ (Finset.nodup_toList V) ?_
  intro j hj
  simp only [Finset.mem_toList] at hj
  simpa using hj

omit [DecidableEq σ] in
theorem length_map_toList [Fintype σ] (V : Finset σ) :
    (V.toList.map (X : σ → MvPolynomial σ K)).length = V.card := by
  rw [List.length_map, Finset.length_toList]

end Coordinate

end GaloisForLFunctions.HTGeometry
