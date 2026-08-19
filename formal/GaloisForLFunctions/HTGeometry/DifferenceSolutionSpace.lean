import Mathlib

/-!
# Solutions of a linear difference system are constrained by the constants

For a field with a distinguished automorphism, the solutions of a first-order linear difference
system `σ v = A v` with invertible `A` span a space whose dimension is measured by the fixed field
of the automorphism, not by the field itself: any linear relation among solutions can be replaced
by a relation with *shift-invariant* coefficients.

The mechanism is the classical minimal-support argument.  Normalize one coefficient of a relation
to one, apply the automorphism, and use invertibility of the system matrix to see that the shifted
coefficients again give a relation; the difference of the two relations has strictly smaller
support, so by minimality it is trivial and every coefficient is a constant.

This is the finiteness statement underlying difference Galois theory: the solution space of a
system of rank `n` has dimension at most `n` over the constants.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [Field K]

/-- The constants of a difference field: the elements fixed by the automorphism. -/
def differenceConstants (σ : K ≃+* K) : Subfield K where
  carrier := {x | σ x = x}
  mul_mem' := by
    intro a b ha hb
    show σ (a * b) = a * b
    rw [map_mul]
    exact congrArg₂ (· * ·) ha hb
  one_mem' := by show σ 1 = 1; exact map_one σ
  add_mem' := by
    intro a b ha hb
    show σ (a + b) = a + b
    rw [map_add]
    exact congrArg₂ (· + ·) ha hb
  zero_mem' := by show σ 0 = 0; exact map_zero σ
  neg_mem' := by
    intro a ha
    show σ (-a) = -a
    rw [map_neg]
    exact congrArg Neg.neg ha
  inv_mem' := by
    intro a ha
    show σ a⁻¹ = a⁻¹
    rw [map_inv₀]
    exact congrArg Inv.inv ha

@[simp] theorem mem_differenceConstants {σ : K ≃+* K} {x : K} :
    x ∈ differenceConstants σ ↔ σ x = x := Iff.rfl

/-- A solution of the first-order linear difference system with matrix `A`. -/
def IsDifferenceSystemSolution {n : ℕ} (σ : K ≃+* K) (A : Matrix (Fin n) (Fin n) K)
    (v : Fin n → K) : Prop :=
  ∀ i, σ (v i) = A.mulVec v i

/-- **The minimal-support argument.**  A nontrivial linear relation among solutions of an
invertible first-order linear difference system can be replaced by a nontrivial relation with
shift-invariant coefficients supported inside the original support. -/
theorem exists_differenceConstants_relation {n : ℕ} (σ : K ≃+* K)
    {A : Matrix (Fin n) (Fin n) K} (hA : IsUnit A.det)
    {ι : Type*} [DecidableEq ι] {v : ι → Fin n → K}
    (hv : ∀ j, IsDifferenceSystemSolution σ A (v j)) :
    ∀ (s : Finset ι) (c : ι → K), s.Nonempty → (∀ j ∈ s, c j ≠ 0) →
      (∀ i, ∑ j ∈ s, c j * v j i = 0) →
      ∃ (t : Finset ι) (d : ι → K), t.Nonempty ∧ t ⊆ s ∧ (∀ j ∈ t, σ (d j) = d j) ∧
        (∀ j ∈ t, d j ≠ 0) ∧ ∀ i, ∑ j ∈ t, d j * v j i = 0 := by
  classical
  intro s
  induction s using Finset.strongInduction with
  | _ s ih =>
      intro c hne hsupp hrel
      obtain ⟨j₀, hj₀⟩ := hne
      have hc0 : c j₀ ≠ 0 := hsupp j₀ hj₀
      set c' : ι → K := fun j => c j / c j₀ with hc'
      have hc'j₀ : c' j₀ = 1 := by rw [hc']; exact div_self hc0
      have hc'ne : ∀ j ∈ s, c' j ≠ 0 := by
        intro j hj
        rw [hc']
        exact div_ne_zero (hsupp j hj) hc0
      have hrel' : ∀ i, ∑ j ∈ s, c' j * v j i = 0 := by
        intro i
        have : ∑ j ∈ s, c' j * v j i = (∑ j ∈ s, c j * v j i) / c j₀ := by
          rw [Finset.sum_div]
          exact Finset.sum_congr rfl fun j _ => by rw [hc']; ring
        rw [this, hrel i, zero_div]
      -- the shifted coefficients also give a relation
      have hshift : ∀ i, ∑ j ∈ s, σ (c' j) * v j i = 0 := by
        have hmul : ∀ i, A.mulVec (fun k => ∑ j ∈ s, σ (c' j) * v j k) i = 0 := by
          intro i
          have hσ : σ (∑ j ∈ s, c' j * v j i) = 0 := by rw [hrel' i, map_zero]
          rw [map_sum] at hσ
          simp only [map_mul] at hσ
          have hstep : ∀ j, σ (v j i) = A.mulVec (v j) i := fun j => hv j i
          rw [Finset.sum_congr rfl (fun j _ => by rw [hstep j])] at hσ
          have hmv : ∀ u : Fin n → K, A.mulVec u i = ∑ k, A i k * u k := by
            intro u
            simp [Matrix.mulVec, dotProduct]
          rw [hmv]
          calc ∑ k, A i k * ∑ j ∈ s, σ (c' j) * v j k
              = ∑ k, ∑ j ∈ s, A i k * (σ (c' j) * v j k) := by
                exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]
            _ = ∑ j ∈ s, ∑ k, A i k * (σ (c' j) * v j k) := Finset.sum_comm
            _ = ∑ j ∈ s, σ (c' j) * ∑ k, A i k * v j k := by
                refine Finset.sum_congr rfl fun j _ => ?_
                rw [Finset.mul_sum]
                exact Finset.sum_congr rfl fun k _ => by ring
            _ = ∑ j ∈ s, σ (c' j) * A.mulVec (v j) i := by
                exact Finset.sum_congr rfl fun j _ => by rw [hmv]
            _ = 0 := hσ
        intro i
        have hzero : (fun k => ∑ j ∈ s, σ (c' j) * v j k) = 0 := by
          have := (Matrix.mulVec_injective_iff_isUnit (A := A)).2
            ((Matrix.isUnit_iff_isUnit_det A).2 hA)
          have h0 : A.mulVec (fun k => ∑ j ∈ s, σ (c' j) * v j k) = A.mulVec 0 := by
            funext i
            rw [hmul i, Matrix.mulVec_zero]
            rfl
          exact this h0
        have := congrFun hzero i
        simpa using this
      -- the difference of the two relations has smaller support
      set d : ι → K := fun j => σ (c' j) - c' j with hd
      have hdrel : ∀ i, ∑ j ∈ s, d j * v j i = 0 := by
        intro i
        have : ∑ j ∈ s, d j * v j i
            = (∑ j ∈ s, σ (c' j) * v j i) - ∑ j ∈ s, c' j * v j i := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun j _ => by rw [hd]; ring
        rw [this, hshift i, hrel' i, sub_zero]
      have hdj₀ : d j₀ = 0 := by
        show σ (c' j₀) - c' j₀ = 0
        rw [hc'j₀, map_one, sub_self]
      by_cases hall : ∀ j ∈ s, d j = 0
      · -- every normalized coefficient is a constant
        refine ⟨s, c', ⟨j₀, hj₀⟩, le_rfl, ?_, hc'ne, hrel'⟩
        intro j hj
        have := hall j hj
        rw [hd] at this
        exact sub_eq_zero.1 this
      · obtain ⟨j₁, hj₁s, hj₁⟩ : ∃ j ∈ s, d j ≠ 0 := by
          by_contra hcon
          refine hall fun j hj => ?_
          by_contra hne
          exact hcon ⟨j, hj, hne⟩
        set t := s.filter (fun j => d j ≠ 0) with ht
        have htsub : t ⊆ s := Finset.filter_subset _ _
        have htne : t.Nonempty := ⟨j₁, by rw [ht]; exact Finset.mem_filter.2 ⟨hj₁s, hj₁⟩⟩
        have htlt : t ⊂ s := by
          refine ⟨htsub, ?_⟩
          intro hcon
          have : j₀ ∈ t := hcon hj₀
          rw [ht, Finset.mem_filter] at this
          exact this.2 hdj₀
        have htrel : ∀ i, ∑ j ∈ t, d j * v j i = 0 := by
          intro i
          have hsum : ∑ j ∈ t, d j * v j i = ∑ j ∈ s, d j * v j i := by
            refine Finset.sum_subset (f := fun j => d j * v j i) htsub ?_
            intro j hjs hjt
            rw [ht, Finset.mem_filter] at hjt
            have hdj : d j = 0 := by
              by_contra hne
              exact hjt ⟨hjs, hne⟩
            rw [hdj, zero_mul]
          rw [hsum, hdrel i]
        obtain ⟨t', d', ht'ne, ht'sub, ht'const, ht'nz, ht'rel⟩ :=
          ih t htlt d htne (fun j hj => by
            rw [ht, Finset.mem_filter] at hj; exact hj.2) htrel
        exact ⟨t', d', ht'ne, ht'sub.trans htsub, ht'const, ht'nz, ht'rel⟩

/-- The same statement for a relation whose coefficients may vanish, provided one of them does
not. -/
theorem exists_differenceConstants_relation_of_ne_zero {n : ℕ} (σ : K ≃+* K)
    {A : Matrix (Fin n) (Fin n) K} (hA : IsUnit A.det)
    {ι : Type*} [DecidableEq ι] {v : ι → Fin n → K}
    (hv : ∀ j, IsDifferenceSystemSolution σ A (v j))
    (s : Finset ι) (c : ι → K) {j₀ : ι} (hj₀ : j₀ ∈ s) (hcj₀ : c j₀ ≠ 0)
    (hrel : ∀ i, ∑ j ∈ s, c j * v j i = 0) :
    ∃ (t : Finset ι) (d : ι → K), t.Nonempty ∧ (∀ j ∈ t, σ (d j) = d j) ∧
      (∀ j ∈ t, d j ≠ 0) ∧ ∀ i, ∑ j ∈ t, d j * v j i = 0 := by
  classical
  set s' := s.filter (fun j => c j ≠ 0) with hs'
  have hs'sub : s' ⊆ s := Finset.filter_subset _ _
  have hj₀' : j₀ ∈ s' := by rw [hs']; exact Finset.mem_filter.2 ⟨hj₀, hcj₀⟩
  have hrel' : ∀ i, ∑ j ∈ s', c j * v j i = 0 := by
    intro i
    have hsum : ∑ j ∈ s', c j * v j i = ∑ j ∈ s, c j * v j i := by
      refine Finset.sum_subset (f := fun j => c j * v j i) hs'sub ?_
      intro j hjs hjs'
      rw [hs', Finset.mem_filter] at hjs'
      have hcj : c j = 0 := by
        by_contra hne
        exact hjs' ⟨hjs, hne⟩
      rw [hcj, zero_mul]
    rw [hsum, hrel i]
  obtain ⟨t, d, htne, _, hconst, hnz, hdrel⟩ :=
    exists_differenceConstants_relation σ hA hv s' c ⟨j₀, hj₀'⟩
      (fun j hj => by rw [hs', Finset.mem_filter] at hj; exact hj.2) hrel'
  exact ⟨t, d, htne, hconst, hnz, hdrel⟩

/-- **The solution space of a rank-`n` difference system has dimension at most `n` over the
constants.**  If no nontrivial relation with shift-invariant coefficients holds among a finite
family of solutions, the family has at most `n` members. -/
theorem card_le_of_no_differenceConstants_relation {n : ℕ} (σ : K ≃+* K)
    {A : Matrix (Fin n) (Fin n) K} (hA : IsUnit A.det)
    {ι : Type*} [DecidableEq ι] [Fintype ι] {v : ι → Fin n → K}
    (hv : ∀ j, IsDifferenceSystemSolution σ A (v j))
    (hindep : ∀ (t : Finset ι) (d : ι → K), t.Nonempty → (∀ j ∈ t, σ (d j) = d j) →
      (∀ j ∈ t, d j ≠ 0) → ∃ i, ∑ j ∈ t, d j * v j i ≠ 0) :
    Fintype.card ι ≤ n := by
  classical
  by_contra hcon
  rw [not_le] at hcon
  have hnli : ¬ LinearIndependent K v := by
    intro hli
    have hle := hli.fintype_card_le_finrank
    rw [Module.finrank_fin_fun K] at hle
    omega
  obtain ⟨g, hg, j₀, hj₀⟩ := Fintype.not_linearIndependent_iff.1 hnli
  have hrel : ∀ i, ∑ j ∈ Finset.univ, g j * v j i = 0 := by
    intro i
    have := congrFun hg i
    simpa [Finset.sum_apply] using this
  obtain ⟨t, d, htne, hconst, hnz, hdrel⟩ :=
    exists_differenceConstants_relation_of_ne_zero σ hA hv Finset.univ g
      (Finset.mem_univ j₀) hj₀ hrel
  obtain ⟨i, hi⟩ := hindep t d htne hconst hnz
  exact hi (hdrel i)

/-! ### The solution set is a module over the constants -/

theorem isDifferenceSystemSolution_zero {n : ℕ} (σ : K ≃+* K) (A : Matrix (Fin n) (Fin n) K) :
    IsDifferenceSystemSolution σ A 0 := by
  intro i
  simp

theorem IsDifferenceSystemSolution.add {n : ℕ} {σ : K ≃+* K} {A : Matrix (Fin n) (Fin n) K}
    {v w : Fin n → K} (hv : IsDifferenceSystemSolution σ A v)
    (hw : IsDifferenceSystemSolution σ A w) :
    IsDifferenceSystemSolution σ A (v + w) := by
  intro i
  rw [Pi.add_apply, map_add, hv i, hw i, Matrix.mulVec_add, Pi.add_apply]

theorem IsDifferenceSystemSolution.smul {n : ℕ} {σ : K ≃+* K} {A : Matrix (Fin n) (Fin n) K}
    {c : K} (hc : σ c = c) {v : Fin n → K} (hv : IsDifferenceSystemSolution σ A v) :
    IsDifferenceSystemSolution σ A (c • v) := by
  intro i
  rw [Pi.smul_apply, smul_eq_mul, map_mul, hc, hv i, Matrix.mulVec_smul, Pi.smul_apply,
    smul_eq_mul]

/-! ### Scalar equations as first-order systems -/

/-- The companion matrix of the scalar difference equation `σ^n y = Σ a j σ^j y`. -/
def differenceCompanion {n : ℕ} (a : Fin n → K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => if (i : ℕ) + 1 < n then (if (j : ℕ) = (i : ℕ) + 1 then 1 else 0) else a j

/-- The shift vector of a scalar solution. -/
def differenceScalarVec {n : ℕ} (σ : K ≃+* K) (y : K) : Fin n → K := fun i => (⇑σ)^[(i : ℕ)] y

/-- **Companion reduction.**  A solution of a scalar linear difference equation gives a solution of
the first-order system with the companion matrix. -/
theorem isDifferenceSystemSolution_differenceScalarVec {n : ℕ} (σ : K ≃+* K) {a : Fin n → K}
    {y : K} (hy : (⇑σ)^[n] y = ∑ j, a j * (⇑σ)^[(j : ℕ)] y) :
    IsDifferenceSystemSolution σ (differenceCompanion a) (differenceScalarVec σ y) := by
  classical
  intro i
  by_cases hi : (i : ℕ) + 1 < n
  · have hrow : ∀ j : Fin n, differenceCompanion a i j
        = if (j : ℕ) = (i : ℕ) + 1 then 1 else 0 := by
      intro j
      simp [differenceCompanion, hi]
    have hsum : (differenceCompanion a).mulVec (differenceScalarVec σ y) i
        = differenceScalarVec σ y ⟨(i : ℕ) + 1, hi⟩ := by
      simp only [Matrix.mulVec, dotProduct]
      rw [Finset.sum_eq_single (⟨(i : ℕ) + 1, hi⟩ : Fin n)]
      · rw [hrow]
        simp
      · intro j _ hj
        rw [hrow]
        have : (j : ℕ) ≠ (i : ℕ) + 1 := by
          intro hcon
          exact hj (Fin.ext hcon)
        simp [this]
      · intro hcon
        exact absurd (Finset.mem_univ _) hcon
    rw [hsum]
    show σ ((⇑σ)^[(i : ℕ)] y) = (⇑σ)^[(i : ℕ) + 1] y
    rw [Function.iterate_succ_apply']
  · have hlast : (i : ℕ) + 1 = n := by
      have := i.isLt
      omega
    have hrow : ∀ j : Fin n, differenceCompanion a i j = a j := by
      intro j
      simp [differenceCompanion, hi]
    have hsum : (differenceCompanion a).mulVec (differenceScalarVec σ y) i
        = ∑ j, a j * (⇑σ)^[(j : ℕ)] y := by
      simp only [Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun j _ => by rw [hrow]; rfl
    rw [hsum, ← hy]
    show σ ((⇑σ)^[(i : ℕ)] y) = (⇑σ)^[n] y
    rw [(Function.iterate_succ_apply' (⇑σ) (i : ℕ) y).symm]
    exact congrArg (fun m => (⇑σ)^[m] y) hlast

/-- For a rank-two scalar equation the companion matrix is invertible exactly when the trailing
coefficient is. -/
theorem isUnit_det_differenceCompanion_two {a : Fin 2 → K} (ha : a 0 ≠ 0) :
    IsUnit (differenceCompanion a).det := by
  have hdet : (differenceCompanion a).det = -a 0 := by
    rw [Matrix.det_fin_two]
    simp [differenceCompanion]
  rw [hdet]
  exact (IsUnit.neg_iff _).2 (isUnit_iff_ne_zero.2 ha)

end

end GaloisForLFunctions.HTGeometry
