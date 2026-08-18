import GaloisForLFunctions.HTGeometry.MatrixUnitCasimirGap
import GaloisForLFunctions.HTGeometry.AllReplicaCollectivePauliCasimir
import GaloisForLFunctions.HTGeometry.AllReplicaTwoLocalPauliLieGeneration

/-!
# The collective matrix-unit family on the replica space

Lifting a one-copy matrix unit to every replica site and vectorizing its commutator action produces
a matrix-unit family on the doubled replica index.  Its weight at a vectorized coordinate is the
difference of the letter counts of the row and column words, and the family satisfies the bracket
relations, the adjoint relation and the weight system of the abstract Casimir gap.
-/

open scoped BigOperators Matrix Kronecker

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Collective

variable {R : Type*} [Fintype R] [DecidableEq R]
variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The one-copy matrix unit. -/
def unitMatrix (a b : α) : Matrix α α ℂ := fun i j => if i = a ∧ j = b then 1 else 0

theorem unitMatrix_apply (a b i j : α) :
    unitMatrix a b i j = if i = a ∧ j = b then (1 : ℂ) else 0 := rfl

theorem unitMatrix_conjTranspose (a b : α) : (unitMatrix a b : Matrix α α ℂ)ᴴ = unitMatrix b a := by
  funext i j
  rw [Matrix.conjTranspose_apply, unitMatrix_apply, unitMatrix_apply]
  by_cases h1 : j = a
  · by_cases h2 : i = b
    · rw [if_pos ⟨h1, h2⟩, if_pos ⟨h2, h1⟩]
      simp
    · rw [if_neg (fun hh => h2 hh.2), if_neg (fun hh => h2 hh.1)]
      simp
  · rw [if_neg (fun hh => h1 hh.1), if_neg (fun hh => h1 hh.2)]
    simp

theorem unitMatrix_apply' (a b i j : α) :
    unitMatrix a b i j = (if i = a then (1 : ℂ) else 0) * (if j = b then (1 : ℂ) else 0) := by
  rw [unitMatrix_apply]
  by_cases h1 : i = a <;> by_cases h2 : j = b <;> simp [h1, h2]

theorem unitMatrix_mul (a b c d : α) :
    (unitMatrix a b : Matrix α α ℂ) * unitMatrix c d
      = if b = c then unitMatrix a d else 0 := by
  funext i j
  rw [Matrix.mul_apply]
  have hterm : ∀ k : α, unitMatrix a b i k * unitMatrix c d k j
      = ((if i = a then (1 : ℂ) else 0) * (if j = d then (1 : ℂ) else 0)) *
        ((if k = b then (1 : ℂ) else 0) * (if k = c then (1 : ℂ) else 0)) := by
    intro k
    rw [unitMatrix_apply', unitMatrix_apply']
    ring
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.mul_sum]
  have hsum : (∑ k : α, (if k = b then (1 : ℂ) else 0) * (if k = c then (1 : ℂ) else 0))
      = if b = c then 1 else 0 := by
    have hstep : ∀ k : α, (if k = b then (1 : ℂ) else 0) * (if k = c then (1 : ℂ) else 0)
        = if k = b then (if b = c then (1 : ℂ) else 0) else 0 := by
      intro k
      by_cases hk : k = b
      · subst hk
        simp
      · simp [hk]
    rw [Finset.sum_congr rfl fun k _ => hstep k,
      Finset.sum_ite_eq' Finset.univ b (fun _ => (if b = c then (1 : ℂ) else 0))]
    simp
  rw [hsum]
  by_cases h : b = c
  · rw [if_pos h, if_pos h, mul_one, unitMatrix_apply']
  · rw [if_neg h, if_neg h, mul_zero]
    simp

/-- The bracket of two matrix units. -/
theorem unitMatrix_bracket (a b c d : α) :
    (unitMatrix a b : Matrix α α ℂ) * unitMatrix c d - unitMatrix c d * unitMatrix a b
      = (if b = c then unitMatrix a d else 0) - (if d = a then unitMatrix c b else 0) := by
  rw [unitMatrix_mul, unitMatrix_mul]

/-- The number of replica sites carrying a letter. -/
def siteCount (x : R → α) (a : α) : ℕ := (Finset.univ.filter fun r => x r = a).card

theorem sum_siteCount (x : R → α) : ∑ a, siteCount x a = Fintype.card R := by
  classical
  have h : ∀ a : α, siteCount x a = (Finset.univ.filter fun r => x r = a).card := fun _ => rfl
  have hdisj : ∀ a ∈ (Finset.univ : Finset α), ∀ b ∈ (Finset.univ : Finset α), a ≠ b →
      Disjoint (Finset.univ.filter fun r => x r = a) (Finset.univ.filter fun r => x r = b) := by
    intro a _ b _ hab
    rw [Finset.disjoint_left]
    intro r ha hb
    simp only [Finset.mem_filter] at ha hb
    exact hab (ha.2.symm.trans hb.2)
  rw [Finset.sum_congr rfl fun a _ => h a, ← Finset.card_biUnion hdisj]
  have huniv : (Finset.univ.biUnion fun a : α => Finset.univ.filter fun r => x r = a)
      = (Finset.univ : Finset R) := by
    ext r
    simp
  rw [huniv, Finset.card_univ]


theorem siteCount_erase (x : R → α) (c : α) (r : R) :
    siteCount x c = ((Finset.univ.erase r).filter fun s => x s = c).card
      + (if x r = c then 1 else 0) := by
  classical
  have hsc : siteCount x c = (Finset.univ.filter fun s => x s = c).card := rfl
  have hu : (Finset.univ : Finset R) = (Finset.univ.erase r) ∪ {r} := by
    ext s
    simp only [Finset.mem_univ, true_iff, Finset.mem_union, Finset.mem_erase, Finset.mem_singleton]
    by_cases hs : s = r <;> simp [hs]
  have hdisj : Disjoint (Finset.univ.erase r) ({r} : Finset R) := by
    rw [Finset.disjoint_singleton_right]
    exact Finset.notMem_erase r Finset.univ
  rw [hsc]
  conv_lhs => rw [hu]
  rw [Finset.filter_union,
    Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj),
    Finset.filter_singleton]
  by_cases h : x r = c
  · rw [if_pos h, if_pos h, Finset.card_singleton]
  · rw [if_neg h, if_neg h, Finset.card_empty]

/-- The collective lift of a one-copy matrix unit. -/
def collUnit (R : Type*) [Fintype R] [DecidableEq R] (a b : α) : Matrix (R → α) (R → α) ℂ :=
  finiteReplicaCollectiveMatrix R α (unitMatrix a b)

theorem collUnit_apply (a b : α) (x y : R → α) :
    collUnit R a b x y
      = ∑ r : R, unitMatrix a b (x r) (y r) *
          ∏ s ∈ Finset.univ.erase r, (1 : Matrix α α ℂ) (x s) (y s) := by
  rw [collUnit, finiteReplicaCollectiveMatrix, Matrix.sum_apply]
  exact Finset.sum_congr rfl fun r _ => finiteTensorSingleSiteMatrix_apply r _ x y

theorem offDiag_prod_eq_zero {x y : R → α} {r t : R} (hrt : t ≠ r) (h : x t ≠ y t) :
    (∏ s ∈ Finset.univ.erase r, (1 : Matrix α α ℂ) (x s) (y s)) = 0 :=
  Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hrt, Finset.mem_univ t⟩)
    (by rw [Matrix.one_apply, if_neg h])

theorem offDiag_prod_ne_zero {x y : R → α} {r : R}
    (h : (∏ s ∈ Finset.univ.erase r, (1 : Matrix α α ℂ) (x s) (y s)) ≠ 0) :
    ∀ s, s ≠ r → x s = y s := by
  intro s hs
  by_contra hne
  exact h (offDiag_prod_eq_zero hs hne)

/-- **The Cartan lift is diagonal, with the letter counts as entries.** -/
theorem collUnit_diag (a : α) (x y : R → α) :
    collUnit R a a x y = if x = y then ((siteCount x a : ℕ) : ℂ) else 0 := by
  classical
  rw [collUnit_apply]
  by_cases hxy : x = y
  · subst hxy
    rw [if_pos rfl]
    have hterm : ∀ r : R, unitMatrix a a (x r) (x r) *
        ∏ s ∈ Finset.univ.erase r, (1 : Matrix α α ℂ) (x s) (x s)
        = if x r = a then (1 : ℂ) else 0 := by
      intro r
      have hprod : (∏ s ∈ Finset.univ.erase r, (1 : Matrix α α ℂ) (x s) (x s)) = 1 :=
        Finset.prod_eq_one fun s _ => by rw [Matrix.one_apply, if_pos rfl]
      rw [hprod, mul_one, unitMatrix_apply]
      by_cases h : x r = a
      · rw [if_pos ⟨h, h⟩, if_pos h]
      · rw [if_neg (fun hh => h hh.1), if_neg h]
    rw [Finset.sum_congr rfl fun r _ => hterm r, ← Finset.sum_filter, Finset.sum_const,
      nsmul_eq_mul, mul_one]
    rfl
  · rw [if_neg hxy]
    obtain ⟨t, ht⟩ : ∃ t, x t ≠ y t := by
      by_contra hc
      exact hxy (funext fun t => not_not.mp fun h => hc ⟨t, h⟩)
    refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hrt : t = r
    · subst hrt
      rw [unitMatrix_apply, if_neg, zero_mul]
      intro hh
      exact ht (hh.1.trans hh.2.symm)
    · rw [offDiag_prod_eq_zero hrt ht, mul_zero]

/-- **A raising lift shifts the letter counts by one step.** -/
theorem collUnit_shift (a b : α) {x y : R → α} (h : collUnit R a b x y ≠ 0) (c : α) :
    ((siteCount x c : ℕ) : ℤ)
      = ((siteCount y c : ℕ) : ℤ) + (if c = a then 1 else 0) - (if c = b then 1 else 0) := by
  classical
  rw [collUnit_apply] at h
  obtain ⟨r, -, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hprod : (∏ s ∈ Finset.univ.erase r, (1 : Matrix α α ℂ) (x s) (y s)) ≠ 0 := by
    intro hz
    exact hr (by rw [hz, mul_zero])
  have hunit : unitMatrix a b (x r) (y r) ≠ 0 := by
    intro hz
    exact hr (by rw [hz, zero_mul])
  have hxr : x r = a ∧ y r = b := by
    by_contra hc
    exact hunit (by rw [unitMatrix_apply, if_neg hc])
  have hoff := offDiag_prod_ne_zero hprod
  have hfilt : ((Finset.univ.erase r).filter fun s => x s = c)
      = ((Finset.univ.erase r).filter fun s => y s = c) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨⟨hs, -⟩, hxs⟩
      exact ⟨⟨hs, Finset.mem_univ s⟩, by rw [← hoff s hs]; exact hxs⟩
    · rintro ⟨⟨hs, -⟩, hys⟩
      exact ⟨⟨hs, Finset.mem_univ s⟩, by rw [hoff s hs]; exact hys⟩
  rw [siteCount_erase x c r, siteCount_erase y c r, hfilt, hxr.1, hxr.2]
  push_cast
  by_cases h1 : a = c
  · by_cases h2 : b = c
    · rw [if_pos h1, if_pos h2, if_pos h1.symm, if_pos h2.symm]
      ring
    · rw [if_pos h1, if_neg h2, if_pos h1.symm, if_neg fun hh => h2 hh.symm]
      ring
  · by_cases h2 : b = c
    · rw [if_neg h1, if_pos h2, if_neg fun hh => h1 hh.symm, if_pos h2.symm]
      ring
    · rw [if_neg h1, if_neg h2, if_neg fun hh => h1 hh.symm, if_neg fun hh => h2 hh.symm]
      ring

theorem collUnit_conjTranspose (a b : α) :
    (collUnit R a b : Matrix (R → α) (R → α) ℂ)ᴴ = collUnit R b a := by
  classical
  funext x y
  rw [Matrix.conjTranspose_apply, collUnit_apply, collUnit_apply, RCLike.star_def, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_mul]
  congr 1
  · rw [unitMatrix_apply, unitMatrix_apply]
    by_cases h : y r = a ∧ x r = b
    · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
      simp
    · rw [if_neg h, if_neg (fun hh => h ⟨hh.2, hh.1⟩)]
      simp
  · rw [map_prod]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [Matrix.one_apply, Matrix.one_apply]
    by_cases h : y s = x s
    · rw [if_pos h, if_pos h.symm]
      simp
    · rw [if_neg h, if_neg fun hh => h hh.symm]
      simp

theorem collUnit_bracket (a b c d : α) :
    (collUnit R a b : Matrix (R → α) (R → α) ℂ) * collUnit R c d
        - collUnit R c d * collUnit R a b
      = (if b = c then collUnit R a d else 0) - (if d = a then collUnit R c b else 0) := by
  classical
  have hlin : ∀ A B : Matrix α α ℂ,
      finiteReplicaCollectiveMatrix R α (A - B)
        = finiteReplicaCollectiveMatrix R α A - finiteReplicaCollectiveMatrix R α B := by
    intro A B
    have h1 : (finiteReplicaCollectiveMatrixLinear R α) (A - B)
        = (finiteReplicaCollectiveMatrixLinear R α) A
          - (finiteReplicaCollectiveMatrixLinear R α) B := map_sub _ A B
    exact h1
  have hz : finiteReplicaCollectiveMatrix R α (0 : Matrix α α ℂ) = 0 := by
    have h1 : (finiteReplicaCollectiveMatrixLinear R α) (0 : Matrix α α ℂ) = 0 := map_zero _
    exact h1
  have h := finiteReplicaCollectiveMatrix_bracket R α (unitMatrix a b) (unitMatrix c d)
  rw [ringCommutator, ringCommutator, unitMatrix_mul, unitMatrix_mul] at h
  rw [collUnit, collUnit, collUnit, collUnit, h, hlin]
  congr 1
  · by_cases hbc : b = c
    · rw [if_pos hbc, if_pos hbc]
    · rw [if_neg hbc, if_neg hbc, hz]
  · by_cases hda : d = a
    · rw [if_pos hda, if_pos hda]
    · rw [if_neg hda, if_neg hda, hz]


theorem matrixCommutatorRepresentation_conjTranspose'' {C : Type*} [Fintype C] [DecidableEq C]
    (G : Matrix C C ℂ) :
    (matrixCommutatorRepresentation G)ᴴ = matrixCommutatorRepresentation Gᴴ := by
  change (((1 : Matrix C C ℂ) ⊗ₖ G - G.transpose ⊗ₖ (1 : Matrix C C ℂ))ᴴ)
    = (1 : Matrix C C ℂ) ⊗ₖ Gᴴ - (Gᴴ).transpose ⊗ₖ (1 : Matrix C C ℂ)
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_kronecker,
    Matrix.conjTranspose_one, Matrix.conjTranspose_transpose_eq_transpose_conjTranspose]

/-- The vectorized collective matrix-unit family. -/
def collGen (R : Type*) [Fintype R] [DecidableEq R] (a b : α) :
    Matrix ((R → α) × (R → α)) ((R → α) × (R → α)) ℂ :=
  matrixCommutatorRepresentation (collUnit R a b)

theorem collGen_apply (a b : α) (p q : (R → α) × (R → α)) :
    collGen R a b p q
      = (if p.1 = q.1 then (1 : ℂ) else 0) * collUnit R a b p.2 q.2
        - collUnit R a b q.1 p.1 * (if p.2 = q.2 then (1 : ℂ) else 0) := by
  show ((1 : Matrix (R → α) (R → α) ℂ) ⊗ₖ collUnit R a b
      - (collUnit R a b).transpose ⊗ₖ (1 : Matrix (R → α) (R → α) ℂ)) p q = _
  rw [Matrix.sub_apply, Matrix.kronecker_apply, Matrix.kronecker_apply, Matrix.one_apply,
    Matrix.one_apply, Matrix.transpose_apply]

theorem collGen_conjTranspose (a b : α) :
    (collGen R a b : Matrix ((R → α) × (R → α)) ((R → α) × (R → α)) ℂ)ᴴ = collGen R b a := by
  rw [collGen, collGen, matrixCommutatorRepresentation_conjTranspose'', collUnit_conjTranspose]

theorem isMatrixUnitFamily_collGen :
    IsMatrixUnitFamily (fun a b : α => collGen R a b) := by
  classical
  refine ⟨fun a b => collGen_conjTranspose a b, fun a b c d => ?_⟩
  have hbr := matrixCommutatorRepresentation_bracket (collUnit R a b) (collUnit R c d)
  have hsub := collUnit_bracket (R := R) a b c d
  show matrixCommutatorRepresentation (collUnit R a b) *
      matrixCommutatorRepresentation (collUnit R c d)
      - matrixCommutatorRepresentation (collUnit R c d) *
        matrixCommutatorRepresentation (collUnit R a b) = _
  rw [hbr, hsub, map_sub]
  congr 1
  · by_cases hbc : b = c
    · rw [if_pos hbc, if_pos hbc]
      rfl
    · rw [if_neg hbc, if_neg hbc, map_zero]
  · by_cases hda : d = a
    · rw [if_pos hda, if_pos hda]
      rfl
    · rw [if_neg hda, if_neg hda, map_zero]

/-- The weight of a vectorized replica coordinate. -/
def collWeight (p : (R → α) × (R → α)) (c : α) : ℤ :=
  ((siteCount p.2 c : ℕ) : ℤ) - ((siteCount p.1 c : ℕ) : ℤ)

theorem isWeightSystem_collGen :
    IsWeightSystem (fun a b : α => collGen R a b) (fun p : (R → α) × (R → α) => collWeight p) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro a p q
    rw [collGen_apply, collUnit_diag, collUnit_diag]
    by_cases hpq : p = q
    · have h1 : p.1 = q.1 := by rw [hpq]
      have h2 : p.2 = q.2 := by rw [hpq]
      simp only [if_pos h1, if_pos h2, if_pos h1.symm, if_pos hpq]
      rw [← h1]
      show (1 : ℂ) * ((siteCount p.2 a : ℕ) : ℂ) - ((siteCount p.1 a : ℕ) : ℂ) * 1
        = (((((siteCount p.2 a : ℕ) : ℤ) - ((siteCount p.1 a : ℕ) : ℤ)) : ℤ) : ℂ)
      push_cast
      ring
    · rw [if_neg hpq]
      by_cases h1 : p.1 = q.1
      · have h2 : p.2 ≠ q.2 := by
          intro hh
          exact hpq (Prod.ext_iff.mpr ⟨h1, hh⟩)
        simp only [if_neg h2]
        ring
      · simp only [if_neg h1, if_neg fun hh : q.1 = p.1 => h1 hh.symm]
        ring
  · intro a b p q hne
    rw [collGen_apply] at hne
    have hsplit : (if p.1 = q.1 then (1 : ℂ) else 0) * collUnit R a b p.2 q.2 ≠ 0 ∨
        collUnit R a b q.1 p.1 * (if p.2 = q.2 then (1 : ℂ) else 0) ≠ 0 := by
      by_contra hc
      have h1 : (if p.1 = q.1 then (1 : ℂ) else 0) * collUnit R a b p.2 q.2 = 0 :=
        not_not.mp fun h => hc (Or.inl h)
      have h2 : collUnit R a b q.1 p.1 * (if p.2 = q.2 then (1 : ℂ) else 0) = 0 :=
        not_not.mp fun h => hc (Or.inr h)
      exact hne (by rw [h1, h2, sub_self])
    funext c
    show ((siteCount p.2 c : ℕ) : ℤ) - ((siteCount p.1 c : ℕ) : ℤ)
        = (((siteCount q.2 c : ℕ) : ℤ) - ((siteCount q.1 c : ℕ) : ℤ))
          + (if c = a then (1 : ℤ) else 0) - (if c = b then 1 else 0)
    rcases hsplit with h | h
    · have h1 : p.1 = q.1 := by
        by_contra hh
        exact h (by rw [if_neg hh, zero_mul])
      have h2 : collUnit R a b p.2 q.2 ≠ 0 := by
        intro hz
        exact h (by rw [hz, mul_zero])
      have hshift := collUnit_shift a b h2 c
      rw [h1, hshift]
      ring
    · have h1 : p.2 = q.2 := by
        by_contra hh
        exact h (by rw [if_neg hh, mul_zero])
      have h2 : collUnit R a b q.1 p.1 ≠ 0 := by
        intro hz
        exact h (by rw [hz, zero_mul])
      have hshift := collUnit_shift a b h2 c
      rw [h1, hshift]
      ring
  · intro p
    have hexp : ∀ c : α, collWeight p c
        = ((siteCount p.2 c : ℕ) : ℤ) - ((siteCount p.1 c : ℕ) : ℤ) := fun _ => rfl
    show (∑ c : α, collWeight p c) = 0
    rw [Finset.sum_congr rfl fun c _ => hexp c, Finset.sum_sub_distrib]
    have h1 : (∑ c : α, ((siteCount p.2 c : ℕ) : ℤ)) = (Fintype.card R : ℤ) := by
      rw [← Nat.cast_sum, sum_siteCount]
    have h2 : (∑ c : α, ((siteCount p.1 c : ℕ) : ℤ)) = (Fintype.card R : ℤ) := by
      rw [← Nat.cast_sum, sum_siteCount]
    rw [h1, h2, sub_self]

/-- **The collective Casimir gap.**  Every nonzero eigenvalue of the collective matrix-unit
Casimir on the vectorized replica space is at least twice the one-copy dimension. -/
theorem collectiveCasimir_eigenvalue_gap [LinearOrder α] {lam : ℝ}
    {Y : (R → α) × (R → α) → ℂ} (hY : Y ≠ 0)
    (heig : familyCasimir (fun a b : α => collGen R a b) *ᵥ Y = (lam : ℂ) • Y) :
    lam = 0 ∨ 2 * (Fintype.card α : ℝ) ≤ lam :=
  casimir_eigenvalue_gap isMatrixUnitFamily_collGen isWeightSystem_collGen hY heig

end Collective

end

end GaloisForLFunctions.HTGeometry
