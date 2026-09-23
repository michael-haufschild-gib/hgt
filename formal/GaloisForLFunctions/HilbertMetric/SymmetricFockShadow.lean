import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Data.Finset.Sym

/-!
# Symmetric-Fock lowering shadows

This module proves a sharp dimension law for the canonical lowering maps between consecutive
homogeneous levels of finite symmetric Fock space.  If `U` is any subspace of level `n + 1` and
`∂U` is the span of all one-mode lowerings of `U`, then

`(n + 1) * dim U ≤ (n + e) * dim (∂U)`,

where `e` is the number of modes.  The proof is Hilbert-theoretic: the lowering maps have exact
left and right energy identities, and Parseval/Bessel comparison transfers those identities to
arbitrary subspaces.  No monomial or generic-position assumption is used.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Matrix of the canonical mode-`i` lowering map from symmetric degree `n + 1` to degree `n`. -/
def symmetricFockAnnihilationMatrix (n : ℕ) (i : I) :
    Matrix (Sym I n) (Sym I (n + 1)) ℝ :=
  fun α β => if β = i ::ₛ α then
    Real.sqrt (Multiset.count i (β : Multiset I)) else 0

private lemma annihilationMatrix_transpose_mul_apply
    (n : ℕ) (i : I) (β γ : Sym I (n + 1)) :
    ((symmetricFockAnnihilationMatrix n i).transpose *
        symmetricFockAnnihilationMatrix n i) β γ =
      if β = γ then (Multiset.count i (β : Multiset I) : ℝ) else 0 := by
  classical
  rw [Matrix.mul_apply]
  by_cases hβγ : β = γ
  · subst γ
    simp only [Matrix.transpose_apply, symmetricFockAnnihilationMatrix]
    by_cases hi : i ∈ β
    · let α : Sym I n := β.erase i hi
      rw [Finset.sum_eq_single α]
      · rw [show β = i ::ₛ α by exact (β.cons_erase hi).symm]
        simp
      · intro δ _ hδα
        have hne : β ≠ i ::ₛ δ := by
          intro h
          have : δ = α := by
            apply (Sym.cons_inj_right i δ α).mp
            exact h.symm.trans (β.cons_erase hi).symm
          exact hδα this
        simp [hne]
      · simp
    · simp only [if_true]
      have hicount : Multiset.count i (β : Multiset I) = 0 :=
        Multiset.count_eq_zero_of_notMem hi
      rw [show (Multiset.count i (β : Multiset I) : ℝ) = 0 by exact_mod_cast hicount]
      apply Finset.sum_eq_zero
      intro α _
      have hne : β ≠ i ::ₛ α := by
        intro h
        exact hi (h ▸ Sym.mem_cons_self i α)
      simp [hne]
  · simp only [if_neg hβγ, Matrix.transpose_apply, symmetricFockAnnihilationMatrix]
    apply Finset.sum_eq_zero
    intro α _
    by_cases hβα : β = i ::ₛ α
    · have hγα : γ ≠ i ::ₛ α := by
        intro h
        exact hβγ (hβα.trans h.symm)
      simp [hβα, hγα]
    · simp [hβα]

private lemma annihilationMatrix_mul_transpose_apply
    (n : ℕ) (i : I) (α δ : Sym I n) :
    (symmetricFockAnnihilationMatrix n i *
        (symmetricFockAnnihilationMatrix n i).transpose) α δ =
      if α = δ then (Multiset.count i (α : Multiset I) : ℝ) + 1 else 0 := by
  classical
  rw [Matrix.mul_apply]
  by_cases hαδ : α = δ
  · subst δ
    simp only [Matrix.transpose_apply, symmetricFockAnnihilationMatrix]
    rw [Finset.sum_eq_single (i ::ₛ α)]
    · simp only [Sym.coe_cons, Multiset.count_cons_self]
      simp only [if_true]
      rw [← sq]
      rw [Real.sq_sqrt (Nat.cast_nonneg _), Nat.cast_add, Nat.cast_one]
    · intro β _ hβα
      have hne : β ≠ i ::ₛ α := hβα
      simp [hne]
    · simp
  · simp only [if_neg hαδ, Matrix.transpose_apply, symmetricFockAnnihilationMatrix]
    apply Finset.sum_eq_zero
    intro β _
    by_cases hβα : β = i ::ₛ α
    · have hβδ : β ≠ i ::ₛ δ := by
        intro h
        exact hαδ ((Sym.cons_inj_right i α δ).mp (hβα.symm.trans h))
      simp [hβα, hαδ]
    · simp [hβα]

private lemma sum_annihilationMatrix_transpose_mul_apply
    (n : ℕ) (β γ : Sym I (n + 1)) :
    ∑ i : I, (((symmetricFockAnnihilationMatrix n i).transpose *
        symmetricFockAnnihilationMatrix n i) β γ) =
      if β = γ then (n + 1 : ℝ) else 0 := by
  classical
  simp_rw [annihilationMatrix_transpose_mul_apply]
  by_cases hβγ : β = γ
  · subst γ
    simp only [if_true]
    have hcount := Multiset.sum_count_eq_card
      (m := (β : Multiset I)) (s := Finset.univ) (fun _ _ => Finset.mem_univ _)
    norm_cast
    simp [Sym.card_coe] at hcount ⊢
  · simp [hβγ]

private lemma sum_annihilationMatrix_mul_transpose_apply
    (n : ℕ) (α δ : Sym I n) :
    ∑ i : I, ((symmetricFockAnnihilationMatrix n i *
        (symmetricFockAnnihilationMatrix n i).transpose) α δ) =
      if α = δ then (n + Fintype.card I : ℝ) else 0 := by
  classical
  simp_rw [annihilationMatrix_mul_transpose_apply]
  by_cases hαδ : α = δ
  · subst δ
    simp only [if_true]
    have hcount := Multiset.sum_count_eq_card
      (m := (α : Multiset I)) (s := Finset.univ) (fun _ _ => Finset.mem_univ _)
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    congr 1
    norm_cast
    simp [Sym.card_coe] at hcount ⊢
  · simp [hαδ]

/-- The total lowering energy on symmetric degree `n + 1` is the number operator `n + 1`. -/
theorem sum_symmetricFockAnnihilationMatrix_transpose_mul (n : ℕ) :
    ∑ i : I, (symmetricFockAnnihilationMatrix n i).transpose *
        symmetricFockAnnihilationMatrix n i =
      (n + 1 : ℝ) • (1 : Matrix (Sym I (n + 1)) (Sym I (n + 1)) ℝ) := by
  classical
  ext β γ
  rw [Matrix.sum_apply β γ Finset.univ, sum_annihilationMatrix_transpose_mul_apply]
  by_cases hβγ : β = γ
  · subst γ
    simp
  · simp [hβγ]

/-- The total creation energy on symmetric degree `n` is the shifted number operator `n + e`. -/
theorem sum_symmetricFockAnnihilationMatrix_mul_transpose (n : ℕ) :
    ∑ i : I, symmetricFockAnnihilationMatrix n i *
        (symmetricFockAnnihilationMatrix n i).transpose =
      (n + Fintype.card I : ℝ) • (1 : Matrix (Sym I n) (Sym I n) ℝ) := by
  classical
  ext α δ
  rw [Matrix.sum_apply α δ Finset.univ, sum_annihilationMatrix_mul_transpose_apply]
  by_cases hαδ : α = δ
  · subst δ
    simp
  · simp [hαδ]

private lemma transpose_mul_toEuclideanLin
    {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (B : Matrix Y X ℝ) :
    (B.transpose * B).toEuclideanLin =
      B.toEuclideanLin.adjoint ∘ₗ B.toEuclideanLin := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    Matrix.conjTranspose_eq_transpose_of_trivial]
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, Matrix.toLpLin_apply]
  rw [Matrix.mulVec_mulVec]

private lemma mul_transpose_toEuclideanLin
    {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (B : Matrix Y X ℝ) :
    (B * B.transpose).toEuclideanLin =
      B.toEuclideanLin ∘ₗ B.toEuclideanLin.adjoint := by
  rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    Matrix.conjTranspose_eq_transpose_of_trivial]
  ext y
  simp only [LinearMap.coe_comp, Function.comp_apply, Matrix.toLpLin_apply]
  rw [Matrix.mulVec_mulVec]

/-- Canonical mode-`i` lowering operator from symmetric degree `n + 1` to degree `n`. -/
def symmetricFockAnnihilation (n : ℕ) (i : I) :
    EuclideanSpace ℝ (Sym I (n + 1)) →ₗ[ℝ] EuclideanSpace ℝ (Sym I n) :=
  (symmetricFockAnnihilationMatrix n i).toEuclideanLin

/-- Exact Parseval identity for the family of canonical lowering operators. -/
theorem symmetricFockAnnihilation_energy (n : ℕ)
    (x : EuclideanSpace ℝ (Sym I (n + 1))) :
    ∑ i, ‖symmetricFockAnnihilation n i x‖ ^ (2 : ℕ) = (n + 1 : ℝ) * ‖x‖ ^ (2 : ℕ) := by
  classical
  calc
    ∑ i, ‖symmetricFockAnnihilation n i x‖ ^ (2 : ℕ) =
        ∑ i, inner ℝ x (Matrix.toEuclideanLin
          ((symmetricFockAnnihilationMatrix n i).transpose *
            symmetricFockAnnihilationMatrix n i) x) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← real_inner_self_eq_norm_sq]
          change inner ℝ ((symmetricFockAnnihilationMatrix n i).toEuclideanLin x)
            ((symmetricFockAnnihilationMatrix n i).toEuclideanLin x) = _
          rw [← LinearMap.adjoint_inner_right, ← LinearMap.comp_apply,
            ← transpose_mul_toEuclideanLin]
    _ = inner ℝ x ((∑ i, Matrix.toEuclideanLin
        ((symmetricFockAnnihilationMatrix n i).transpose *
          symmetricFockAnnihilationMatrix n i)) x) := by
          simp [inner_sum]
    _ = inner ℝ x (Matrix.toEuclideanLin
        (∑ i, (symmetricFockAnnihilationMatrix n i).transpose *
          symmetricFockAnnihilationMatrix n i) x) := by
          rw [map_sum]
    _ = (n + 1 : ℝ) * ‖x‖ ^ (2 : ℕ) := by
          rw [sum_symmetricFockAnnihilationMatrix_transpose_mul]
          simp only [map_smul, LinearMap.smul_apply]
          rw [show Matrix.toEuclideanLin
              (1 : Matrix (Sym I (n + 1)) (Sym I (n + 1)) ℝ) x = x by simp]
          change inner ℝ x ((n + 1 : ℝ) • x) = _
          rw [inner_smul_right, real_inner_self_eq_norm_sq]

/-- Exact Parseval identity for the adjoints of the canonical lowering operators. -/
theorem symmetricFockAnnihilation_adjoint_energy (n : ℕ)
    (y : EuclideanSpace ℝ (Sym I n)) :
    ∑ i, ‖(symmetricFockAnnihilation n i).adjoint y‖ ^ (2 : ℕ) =
      (n + Fintype.card I : ℝ) * ‖y‖ ^ (2 : ℕ) := by
  classical
  calc
    ∑ i, ‖(symmetricFockAnnihilation n i).adjoint y‖ ^ (2 : ℕ) =
        ∑ i, inner ℝ y (Matrix.toEuclideanLin
          (symmetricFockAnnihilationMatrix n i *
            (symmetricFockAnnihilationMatrix n i).transpose) y) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← real_inner_self_eq_norm_sq]
          change inner ℝ ((symmetricFockAnnihilationMatrix n i).toEuclideanLin.adjoint y)
            ((symmetricFockAnnihilationMatrix n i).toEuclideanLin.adjoint y) = _
          rw [LinearMap.adjoint_inner_left,
            ← LinearMap.comp_apply, ← mul_transpose_toEuclideanLin]
    _ = inner ℝ y ((∑ i, Matrix.toEuclideanLin
        (symmetricFockAnnihilationMatrix n i *
          (symmetricFockAnnihilationMatrix n i).transpose)) y) := by
          simp [inner_sum]
    _ = inner ℝ y (Matrix.toEuclideanLin
        (∑ i, symmetricFockAnnihilationMatrix n i *
          (symmetricFockAnnihilationMatrix n i).transpose) y) := by
          rw [map_sum]
    _ = (n + Fintype.card I : ℝ) * ‖y‖ ^ (2 : ℕ) := by
          rw [sum_symmetricFockAnnihilationMatrix_mul_transpose]
          simp only [map_smul, LinearMap.smul_apply]
          rw [show Matrix.toEuclideanLin
              (1 : Matrix (Sym I n) (Sym I n) ℝ) y = y by simp]
          change inner ℝ y ((n + Fintype.card I : ℝ) • y) = _
          rw [inner_smul_right, real_inner_self_eq_norm_sq]

/-- A finite family with exact left and right Hilbert-energy constants expands every subspace by
the ratio of those constants. -/
theorem tightOperatorFamily_subspace_finrank
    {X Y J : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    [Fintype J]
    (T : J → X →ₗ[ℝ] Y) (a b : ℝ)
    (hleft : ∀ x, ∑ j, ‖T j x‖ ^ (2 : ℕ) = a * ‖x‖ ^ (2 : ℕ))
    (hright : ∀ y, ∑ j, ‖(T j).adjoint y‖ ^ (2 : ℕ) = b * ‖y‖ ^ (2 : ℕ))
    (U : Submodule ℝ X) (V : Submodule ℝ Y)
    (hUV : ∀ j x, x ∈ U → T j x ∈ V) :
    a * (Module.finrank ℝ U : ℝ) ≤ b * (Module.finrank ℝ V : ℝ) := by
  let u := stdOrthonormalBasis ℝ U
  let v := stdOrthonormalBasis ℝ V
  have hu : Orthonormal ℝ (fun p => ((u p : U) : X)) := by
    refine ⟨?_, ?_⟩
    · intro p
      change ‖u p‖ = 1
      exact u.orthonormal.1 p
    · intro p q hpq
      change inner ℝ (u p) (u q) = 0
      exact u.orthonormal.2 hpq
  have hvnorm (q) : ‖((v q : V) : Y)‖ ^ (2 : ℕ) = 1 := by
    change ‖v q‖ ^ (2 : ℕ) = 1
    rw [v.orthonormal.1 q]
    norm_num
  have hunorm (p) : ‖((u p : U) : X)‖ ^ (2 : ℕ) = 1 := by
    change ‖u p‖ ^ (2 : ℕ) = 1
    rw [u.orthonormal.1 p]
    norm_num
  rw [show a * (Module.finrank ℝ U : ℝ) =
      ∑ p, a * ‖((u p : U) : X)‖ ^ (2 : ℕ) by
        simp [hunorm, mul_comm],
    show b * (Module.finrank ℝ V : ℝ) =
      ∑ q, b * ‖((v q : V) : Y)‖ ^ (2 : ℕ) by
        simp [hvnorm, mul_comm]]
  rw [show (∑ p, a * ‖((u p : U) : X)‖ ^ (2 : ℕ)) =
      ∑ p, ∑ j, ‖T j ((u p : U) : X)‖ ^ (2 : ℕ) by
        apply Finset.sum_congr rfl
        intro p _
        exact (hleft _).symm]
  rw [Finset.sum_comm]
  calc
    ∑ j, ∑ p, ‖T j ((u p : U) : X)‖ ^ (2 : ℕ) =
        ∑ j, ∑ p, ∑ q,
          inner ℝ ((v q : V) : Y) (T j ((u p : U) : X)) ^ (2 : ℕ) := by
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro p _
          let z : V := ⟨T j ((u p : U) : X), hUV j _ (u p).property⟩
          simpa [z] using (v.sum_sq_inner_right z).symm
    _ = ∑ j, ∑ q, ∑ p,
        inner ℝ ((u p : U) : X) ((T j).adjoint ((v q : V) : Y)) ^ (2 : ℕ) := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro q _
          apply Finset.sum_congr rfl
          intro p _
          rw [← (T j).adjoint_inner_left, real_inner_comm]
    _ ≤ ∑ j, ∑ q, ‖(T j).adjoint ((v q : V) : Y)‖ ^ (2 : ℕ) := by
          apply Finset.sum_le_sum
          intro j _
          apply Finset.sum_le_sum
          intro q _
          simpa using (hu.sum_inner_products_le
            ((T j).adjoint ((v q : V) : Y)) (s := Finset.univ))
    _ = ∑ q, ∑ j, ‖(T j).adjoint ((v q : V) : Y)‖ ^ (2 : ℕ) := by
          rw [Finset.sum_comm]
    _ = ∑ q, b * ‖((v q : V) : Y)‖ ^ (2 : ℕ) := by
          apply Finset.sum_congr rfl
          intro q _
          exact hright _

/-- Span of all canonical one-mode lowerings of a subspace of symmetric degree `n + 1`. -/
def symmetricFockLoweringShadow (n : ℕ)
    (U : Submodule ℝ (EuclideanSpace ℝ (Sym I (n + 1)))) :
    Submodule ℝ (EuclideanSpace ℝ (Sym I n)) :=
  ⨆ i, U.map (symmetricFockAnnihilation n i)

theorem annihilation_mem_loweringShadow (n : ℕ)
    (U : Submodule ℝ (EuclideanSpace ℝ (Sym I (n + 1))))
    (i : I) (x : EuclideanSpace ℝ (Sym I (n + 1))) (hx : x ∈ U) :
    symmetricFockAnnihilation n i x ∈ symmetricFockLoweringShadow n U := by
  apply (show U.map (symmetricFockAnnihilation n i) ≤ symmetricFockLoweringShadow n U from
    le_iSup (fun j : I => U.map (symmetricFockAnnihilation n j)) i)
  exact ⟨x, hx, rfl⟩

/-- **Sharp symmetric-Fock shadow law.**  Every subspace of symmetric degree `n + 1` has a
canonical lowering shadow satisfying `(n + 1) dim U ≤ (n + e) dim (∂U)`. -/
theorem symmetricFockLoweringShadow_finrank (n : ℕ)
    (U : Submodule ℝ (EuclideanSpace ℝ (Sym I (n + 1)))) :
    (n + 1 : ℝ) * (Module.finrank ℝ U : ℝ) ≤
      (n + Fintype.card I : ℝ) *
        (Module.finrank ℝ (symmetricFockLoweringShadow n U) : ℝ) := by
  apply tightOperatorFamily_subspace_finrank
    (T := symmetricFockAnnihilation n)
    (a := (n + 1 : ℝ))
    (b := (n + Fintype.card I : ℝ))
    (U := U)
    (V := symmetricFockLoweringShadow n U)
  · exact symmetricFockAnnihilation_energy n
  · exact symmetricFockAnnihilation_adjoint_energy n
  · intro i x hx
    exact annihilation_mem_loweringShadow n U i x hx

/-! ### Weighted lowering charge -/

/-- The weighted adjacent-level defects telescope to the endpoint charge. -/
theorem weightedFockShadow_telescope (e M : ℕ) (h : ℕ → ℝ) :
    ∑ n ∈ Finset.range M,
        (n : ℝ) * (((n + e : ℕ) : ℝ) * h n - ((n + 1 : ℕ) : ℝ) * h (n + 1)) =
      ((e + 1 : ℕ) : ℝ) * ∑ n ∈ Finset.range M, (n : ℝ) * h n -
        (M : ℝ) * ((M : ℝ) - 1) * h M := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

/-- Every sequence obeying the adjacent symmetric-Fock shadow inequalities satisfies the sharp
weighted endpoint charge bound. -/
theorem weightedFockShadowCharge_lower_bound
    (e M : ℕ) (h : ℕ → ℝ)
    (hstep : ∀ n < M,
      ((n + 1 : ℕ) : ℝ) * h (n + 1) ≤ ((n + e : ℕ) : ℝ) * h n) :
    (M : ℝ) * ((M : ℝ) - 1) * h M ≤
      ((e + 1 : ℕ) : ℝ) * ∑ n ∈ Finset.range M, (n : ℝ) * h n := by
  have hs : 0 ≤ ∑ n ∈ Finset.range M,
      (n : ℝ) * (((n + e : ℕ) : ℝ) * h n - ((n + 1 : ℕ) : ℝ) * h (n + 1)) := by
    apply Finset.sum_nonneg
    intro n hn
    apply mul_nonneg (Nat.cast_nonneg n)
    linarith [hstep n (Finset.mem_range.mp hn)]
  rw [weightedFockShadow_telescope] at hs
  linarith

/-- Weighted dimension carried by all levels strictly below `M` in a graded Fock family. -/
def gradedFockLoweringCharge (M : ℕ)
    (U : (n : ℕ) → Submodule ℝ (EuclideanSpace ℝ (Sym I n))) : ℝ :=
  ∑ n ∈ Finset.range M, (n : ℝ) * (Module.finrank ℝ (U n) : ℝ)

/-- **Sharp graded Fock charge law.**  If every degree contains the canonical lowering shadow of
the next degree, then `(e + 1) B ≥ M (M - 1) dim U_M`. -/
theorem gradedFockLoweringCharge_lower_bound
    (M : ℕ)
    (U : (n : ℕ) → Submodule ℝ (EuclideanSpace ℝ (Sym I n)))
    (hshadow : ∀ n < M, symmetricFockLoweringShadow n (U (n + 1)) ≤ U n) :
    (M : ℝ) * ((M : ℝ) - 1) * (Module.finrank ℝ (U M) : ℝ) ≤
      ((Fintype.card I + 1 : ℕ) : ℝ) * gradedFockLoweringCharge M U := by
  unfold gradedFockLoweringCharge
  apply weightedFockShadowCharge_lower_bound (Fintype.card I) M
  intro n hn
  norm_num only [Nat.cast_add, Nat.cast_one]
  calc
    ((n : ℝ) + 1) * (Module.finrank ℝ (U (n + 1)) : ℝ) ≤
        ((n : ℝ) + (Fintype.card I : ℝ)) *
          (Module.finrank ℝ (symmetricFockLoweringShadow n (U (n + 1))) : ℝ) :=
      symmetricFockLoweringShadow_finrank n (U (n + 1))
    _ ≤ ((n : ℝ) + (Fintype.card I : ℝ)) * (Module.finrank ℝ (U n) : ℝ) := by
      gcongr
      exact_mod_cast Submodule.finrank_mono (hshadow n hn)

end

end GaloisForLFunctions.HilbertMetric
