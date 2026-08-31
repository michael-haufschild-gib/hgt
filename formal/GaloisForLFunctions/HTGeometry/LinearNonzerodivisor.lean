import GaloisForLFunctions.HTGeometry.IrrelevantSideCondition

/-!
# A linear nonzerodivisor exists over an infinite field

Over an infinite field a vector space is not a finite union of proper subspaces:

```text
subsingleton_line_meet         a line meets a subspace missing its base point at most once
exists_notMem_of_finite_proper ** a finite family of proper subspaces misses a point **
```

The proof is the line argument: given a point outside all but one subspace, slide along a direction
outside the last one; each earlier subspace can catch the moving point at most once, and an infinite
field has room to avoid finitely many values.

Applied to the degree-one part of a polynomial ring, this produces a nonzerodivisor that is a linear
form:

```text
linearForm, linearFormMap             the linear form with given coefficients
exists_linearForm_isSMulRegular       ** some element of the irrelevant ideal being a nonzerodivisor
                                         forces a linear one **
```

The associated primes of a finitely generated module are finitely many, none of them contains the
regular element, and hence none contains the whole irrelevant ideal — so none contains every
variable, the coefficient vectors it does catch form a proper subspace, and a vector escapes them
all.  This is what makes a *homogeneous* regular sequence available, which is what a degeneration
argument needs when the grading has to be preserved along the way.
-/

namespace GaloisForLFunctions.HTGeometry

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem subsingleton_line_meet {p : Submodule K V} {v w : V} (hv : v ∉ p) :
    {lam : K | v + lam • w ∈ p}.Subsingleton := by
  intro a ha b hb
  by_contra hab
  have hsub : (a - b) • w ∈ p := by
    have : (v + a • w) - (v + b • w) = (a - b) • w := by
      module
    rw [← this]
    exact Submodule.sub_mem _ ha hb
  have hw : w ∈ p := by
    have hne : a - b ≠ 0 := sub_ne_zero.mpr hab
    have := Submodule.smul_mem p (a - b)⁻¹ hsub
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  exact hv (by
    have : v = (v + a • w) - a • w := by module
    rw [this]
    exact Submodule.sub_mem _ ha (Submodule.smul_mem _ _ hw))

/-- **A vector space over an infinite field is not a finite union of proper subspaces.** -/
theorem exists_notMem_of_finite_proper [Infinite K] {s : Set (Submodule K V)} (hs : s.Finite)
    (h : ∀ p ∈ s, p ≠ ⊤) : ∃ v : V, ∀ p ∈ s, v ∉ p := by
  classical
  induction s, hs using Set.Finite.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert q s hq hsfin ih =>
    obtain ⟨v, hv⟩ := ih (fun p hp => h p (Set.mem_insert_of_mem _ hp))
    have hqtop : q ≠ ⊤ := h q (Set.mem_insert _ _)
    by_cases hvq : v ∈ q
    · obtain ⟨w, hw⟩ : ∃ w : V, w ∉ q := by
        by_contra hcon
        exact hqtop (eq_top_iff.mpr fun y _ => not_not.mp (fun hy => hcon ⟨y, hy⟩))
      have hbad : {lam : K | ∃ p ∈ s, v + lam • w ∈ p}.Finite := by
        have : {lam : K | ∃ p ∈ s, v + lam • w ∈ p}
            = ⋃ p ∈ s, {lam : K | v + lam • w ∈ p} := by
          ext lam
          simp
        rw [this]
        exact hsfin.biUnion fun p hp =>
          (subsingleton_line_meet (hv p hp)).finite
      obtain ⟨lam, hlam⟩ := ((hbad.union (Set.finite_singleton (0 : K)))).infinite_compl.nonempty
      refine ⟨v + lam • w, ?_⟩
      intro p hp
      rcases Set.mem_insert_iff.mp hp with rfl | hps
      · intro hcon
        have hlw : lam • w ∈ p := by
          have : lam • w = (v + lam • w) - v := by module
          rw [this]
          exact Submodule.sub_mem _ hcon hvq
        have hlam0 : lam ≠ 0 := by
          intro h0
          exact hlam (Set.mem_union_right _ (by simp [h0]))
        have := Submodule.smul_mem p lam⁻¹ hlw
        rw [smul_smul, inv_mul_cancel₀ hlam0, one_smul] at this
        exact hw this
      · intro hcon
        exact hlam (Set.mem_union_left _ ⟨p, hps, hcon⟩)
    · exact ⟨v, fun p hp => by
        rcases Set.mem_insert_iff.mp hp with rfl | hps
        · exact hvq
        · exact hv p hps⟩

section Linear

open MvPolynomial

universe u

variable {N : ℕ} {K : Type u} [Field K]

/-- The linear form with the given coefficients. -/
noncomputable def linearForm (c : Fin N → K) : MvPolynomial (Fin N) K :=
  ∑ i, MvPolynomial.C (c i) * MvPolynomial.X i

/-- The coefficient vectors whose linear form lies in a given submodule. -/
noncomputable def linearFormMap (K : Type u) [Field K] (N : ℕ) :
    (Fin N → K) →ₗ[K] MvPolynomial (Fin N) K where
  toFun := linearForm
  map_add' a b := by
    simp only [linearForm]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.add_apply, map_add, add_mul]
  map_smul' a b := by
    simp only [linearForm, RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, map_mul, MvPolynomial.smul_eq_C_mul, mul_assoc]

theorem linearFormMap_apply (c : Fin N → K) : linearFormMap K N c = linearForm c := rfl

theorem X_mem_of_forall_linearForm_mem {P : Ideal (MvPolynomial (Fin N) K)}
    (h : ∀ c : Fin N → K, linearForm c ∈ P) (i : Fin N) : (X i : MvPolynomial (Fin N) K) ∈ P := by
  classical
  have := h (fun j => if j = i then 1 else 0)
  rwa [show linearForm (fun j => if j = i then (1 : K) else 0) = X i from by
    rw [linearForm, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [hj]
    · intro hi
      exact absurd (Finset.mem_univ i) hi] at this

/-- **A linear nonzerodivisor exists** whenever some element of the irrelevant ideal is one, over an
infinite field: the associated primes are finitely many and none contains every variable, so their
linear traces are proper subspaces and a coefficient vector escapes them all. -/
theorem exists_linearForm_isSMulRegular [Infinite K] (M : Type u) [AddCommGroup M]
    [Module (MvPolynomial (Fin N) K) M] [Module.Finite (MvPolynomial (Fin N) K) M]
    {x : MvPolynomial (Fin N) K} (hxm : x ∈ irrelevantIdeal K (Fin N))
    (hxreg : IsSMulRegular M x) :
    ∃ c : Fin N → K, IsSMulRegular M (linearForm c) := by
  classical
  have hfin : (associatedPrimes (MvPolynomial (Fin N) K) M).Finite :=
    associatedPrimes.finite (MvPolynomial (Fin N) K) M
  have hcompl := biUnion_associatedPrimes_eq_compl_regular (MvPolynomial (Fin N) K) M
  have hxnot : ∀ P ∈ associatedPrimes (MvPolynomial (Fin N) K) M, x ∉ P := by
    intro P hP hmem
    have h2 : x ∈ ({r : MvPolynomial (Fin N) K | IsSMulRegular M r})ᶜ := by
      rw [← hcompl]
      exact Set.mem_biUnion hP hmem
    exact h2 hxreg
  set W : Ideal (MvPolynomial (Fin N) K) → Submodule K (Fin N → K) :=
    fun P => Submodule.comap (linearFormMap K N) (Submodule.restrictScalars K P) with hW
  have hproper : ∀ P ∈ associatedPrimes (MvPolynomial (Fin N) K) M, W P ≠ ⊤ := by
    intro P hP htop
    have hall : ∀ c : Fin N → K, linearForm c ∈ P := by
      intro c
      have hc : c ∈ W P := by rw [htop]; trivial
      exact hc
    have hle : irrelevantIdeal K (Fin N) ≤ P := by
      rw [irrelevantIdeal, Ideal.span_le]
      rintro y ⟨i, rfl⟩
      exact X_mem_of_forall_linearForm_mem hall i
    exact hxnot P hP (hle hxm)
  obtain ⟨c, hc⟩ := exists_notMem_of_finite_proper (K := K) (V := Fin N → K)
    (hfin.image W) (by
      rintro p ⟨P, hP, rfl⟩
      exact hproper P hP)
  refine ⟨c, ?_⟩
  by_contra hcon
  have hmem : linearForm c ∈ ⋃ p ∈ associatedPrimes (MvPolynomial (Fin N) K) M,
      (p : Set (MvPolynomial (Fin N) K)) := by
    rw [hcompl]
    exact hcon
  obtain ⟨P, hP, hmemP⟩ := Set.mem_iUnion₂.mp hmem
  exact hc (W P) ⟨P, hP, rfl⟩ hmemP

end Linear

end GaloisForLFunctions.HTGeometry
