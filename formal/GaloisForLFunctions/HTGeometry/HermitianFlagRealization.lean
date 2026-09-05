import GaloisForLFunctions.HTGeometry.HermitianFlagSimplex

/-!
# Every flag of the building is a degeneration flag

A Hermitian direction produces a flag of subspaces, its eigenvalue filtration.  Conversely every
flag arises this way: given a chain of proper nonzero subspaces, the orthogonal decomposition it
induces carries a Hermitian operator that is a distinct real scalar on each graded piece, and the
eigenvalue filtration of that operator is the given chain.

So the degeneration flags of Hermitian directions are exactly the simplices of the building, and no
horizon flag is missed by the asymptotics of observer metrics.
-/

namespace GaloisForLFunctions.HTGeometry

open Module Submodule

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-! ## Orthogonal complements from an orthogonal splitting -/

omit [FiniteDimensional ℂ E] in
/-- **Orthogonal subspaces that span everything are each other's complements.** -/
theorem orthogonal_eq_of_sup_eq_top {A B : Submodule ℂ E}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, inner ℂ a b = (0 : ℂ)) (hsup : A ⊔ B = ⊤) : Bᗮ = A := by
  refine le_antisymm (fun x hx => ?_) ?_
  · obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top : x ∈ A ⊔ B)
    have hxb : inner ℂ (a + b) b = (0 : ℂ) := (Submodule.mem_orthogonal' _ _).1 hx b hb
    have hab : inner ℂ a b = (0 : ℂ) := hAB a ha b hb
    have hbb : inner ℂ b b = (0 : ℂ) := by
      rw [inner_add_left, hab, zero_add] at hxb
      exact hxb
    have : b = 0 := by
      simpa using inner_self_eq_zero (𝕜 := ℂ) |>.1 hbb
    rw [this, add_zero]
    exact ha
  · intro a ha
    exact (Submodule.mem_orthogonal' _ _).2 fun b hb => hAB a ha b hb

omit [FiniteDimensional ℂ E] in
theorem inner_eq_zero_comm {x y : E} (h : inner ℂ x y = (0 : ℂ)) : inner ℂ y x = (0 : ℂ) :=
  inner_eq_zero_symm.1 h

omit [FiniteDimensional ℂ E] in
/-- A vector orthogonal to every piece of a family is orthogonal to their supremum. -/
theorem mem_orthogonal_iSup {ι : Type*} {Q : ι → Submodule ℂ E} {s : Set ι} {x : E}
    (h : ∀ i ∈ s, ∀ y ∈ Q i, inner ℂ x y = (0 : ℂ)) :
    x ∈ (⨆ i ∈ s, Q i)ᗮ := by
  refine (Submodule.mem_orthogonal' _ _).2 fun y hy => ?_
  refine Submodule.iSup_induction (fun i => ⨆ _ : i ∈ s, Q i)
    (motive := fun y => inner ℂ x y = (0 : ℂ)) hy ?_ (by simp)
    (fun a b ha hb => by rw [inner_add_right, ha, hb, add_zero])
  intro i y hyi
  exact Submodule.iSup_induction (fun _ : i ∈ s => Q i)
    (motive := fun y => inner ℂ x y = (0 : ℂ)) hyi (fun hi y hy => h i hi y hy) (by simp)
    (fun a b ha hb => by rw [inner_add_right, ha, hb, add_zero])

/-! ## A Hermitian operator that is a scalar on each piece -/

/-- The orthogonal projection to a subspace kills its orthogonal complement. -/
theorem starProjection_eq_zero_of_mem_orthogonal {K : Submodule ℂ E} {x : E} (hx : x ∈ Kᗮ) :
    K.starProjection x = 0 :=
  Submodule.eq_starProjection_of_mem_orthogonal K.zero_mem (by simpa using hx)

omit [FiniteDimensional ℂ E] in
theorem isSymmetric_smul_real {T : E →ₗ[ℂ] E} (h : T.IsSymmetric) (r : ℝ) :
    ((r : ℂ) • T).IsSymmetric := by
  intro x y
  simp only [LinearMap.smul_apply, inner_smul_left, inner_smul_right, Complex.conj_ofReal]
  rw [h x y]

omit [FiniteDimensional ℂ E] in
theorem isSymmetric_sum {ι : Type*} (s : Finset ι) (T : ι → E →ₗ[ℂ] E)
    (h : ∀ i ∈ s, (T i).IsSymmetric) : (∑ i ∈ s, T i).IsSymmetric := by
  classical
  induction s using Finset.induction with
  | empty => intro x y; simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (h i (Finset.mem_insert_self i s)).add
        (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/-- The operator that is the real scalar `w i` on the piece `Q i`. -/
noncomputable def pieceOperator {ι : Type*} [Fintype ι] (Q : ι → Submodule ℂ E) (w : ι → ℝ) :
    E →ₗ[ℂ] E :=
  ∑ i, (w i : ℂ) • ((Q i).starProjection : E →L[ℂ] E).toLinearMap

theorem isSymmetric_pieceOperator {ι : Type*} [Fintype ι] (Q : ι → Submodule ℂ E) (w : ι → ℝ) :
    (pieceOperator Q w).IsSymmetric :=
  isSymmetric_sum _ _ fun i _ => isSymmetric_smul_real (Q i).starProjection_isSymmetric _

theorem pieceOperator_apply_of_mem {ι : Type*} [Fintype ι] {Q : ι → Submodule ℂ E} (w : ι → ℝ)
    (horth : ∀ i j, i ≠ j → ∀ x ∈ Q i, ∀ y ∈ Q j, inner ℂ x y = (0 : ℂ)) {i : ι} {x : E}
    (hx : x ∈ Q i) : pieceOperator Q w x = (w i : ℂ) • x := by
  classical
  have hzero : ∀ j, j ≠ i → (Q j).starProjection x = 0 := by
    intro j hj
    refine starProjection_eq_zero_of_mem_orthogonal ?_
    exact (Submodule.mem_orthogonal' _ _).2 fun y hy => horth i j (Ne.symm hj) x hx y hy
  have hself : (Q i).starProjection x = x := Submodule.starProjection_eq_self_iff.2 hx
  simp only [pieceOperator, LinearMap.sum_apply, LinearMap.smul_apply,
    ContinuousLinearMap.coe_coe]
  rw [Finset.sum_eq_single i]
  · rw [hself]
  · intro j _ hj
    rw [hzero j hj, smul_zero]
  · intro hcon
    exact absurd (Finset.mem_univ i) hcon

/-! ## The flag of such an operator -/

/-- **The degeneration flag of a piecewise-scalar Hermitian operator** collects the pieces whose
scalar is above the threshold. -/
theorem eigenSum_pieceOperator {ι : Type*} [Fintype ι] {Q : ι → Submodule ℂ E} (w : ι → ℝ)
    (horth : ∀ i j, i ≠ j → ∀ x ∈ Q i, ∀ y ∈ Q j, inner ℂ x y = (0 : ℂ))
    (htop : (⨆ i, Q i) = ⊤) (c : ℝ) :
    eigenSum (pieceOperator Q w) c = ⨆ i ∈ {i | c < w i}, Q i := by
  classical
  set T := pieceOperator Q w with hT
  refine le_antisymm (iSup₂_le fun μ hμ => ?_) (iSup₂_le fun i hi => ?_)
  · -- an eigenvector with eigenvalue `μ > c` lies in the pieces with scalar exactly `μ`
    set A : Submodule ℂ E := ⨆ i ∈ {i | w i = μ}, Q i with hA
    set B : Submodule ℂ E := ⨆ i ∈ {i | w i ≠ μ}, Q i with hB
    have hAB : ∀ a ∈ A, ∀ b ∈ B, inner ℂ a b = (0 : ℂ) := by
      intro a ha b hb
      have haB : a ∈ Bᗮ := by
        refine mem_orthogonal_iSup (Q := Q) (s := {i | w i ≠ μ}) ?_
        intro j hj z hz
        have hzA : z ∈ Aᗮ := by
          refine mem_orthogonal_iSup (Q := Q) (s := {i | w i = μ}) ?_
          intro i hi y hy
          exact horth j i (by rintro rfl; exact hj hi) _ hz _ hy
        exact inner_eq_zero_comm ((Submodule.mem_orthogonal' _ _).1 hzA a ha)
      exact (Submodule.mem_orthogonal' _ _).1 haB b hb
    have hsup : A ⊔ B = ⊤ := by
      refine le_antisymm le_top ?_
      rw [← htop]
      refine iSup_le fun i => ?_
      by_cases hi : w i = μ
      · exact le_sup_of_le_left (le_iSup₂ (f := fun i (_ : i ∈ {i | w i = μ}) => Q i) i hi)
      · exact le_sup_of_le_right (le_iSup₂ (f := fun i (_ : i ∈ {i | w i ≠ μ}) => Q i) i hi)
    have hBA : Bᗮ = A := orthogonal_eq_of_sup_eq_top hAB hsup
    have hsub : Module.End.eigenspace T (μ : ℂ) ≤ A := by
      intro x hx
      rw [← hBA]
      refine mem_orthogonal_iSup (Q := Q) (s := {i | w i ≠ μ}) ?_
      intro i hi y hy
      have hTy : T y = (w i : ℂ) • y := pieceOperator_apply_of_mem w horth hy
      have hTx : T x = (μ : ℂ) • x := Module.End.mem_eigenspace_iff.1 hx
      have hkey : inner ℂ (T x) y = inner ℂ x (T y) := isSymmetric_pieceOperator Q w x y
      rw [hTx, hTy, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at hkey
      have hne : ((μ : ℂ) - (w i : ℂ)) ≠ 0 := by
        simp only [sub_ne_zero]
        exact fun hcon => hi (by exact_mod_cast hcon.symm)
      have : ((μ : ℂ) - (w i : ℂ)) * inner ℂ x y = 0 := by
        rw [sub_mul, hkey, sub_self]
      exact (mul_eq_zero.1 this).resolve_left hne
    refine le_trans hsub (iSup₂_le fun i hi => ?_)
    exact le_iSup₂ (f := fun i (_ : i ∈ {i | c < w i}) => Q i) i (by
      simp only [Set.mem_setOf_eq] at hi ⊢
      rw [hi]
      exact hμ)
  · -- each piece with scalar above the threshold is an eigenspace inside the flag
    refine le_trans (fun x hx => ?_) (eigenspace_le_eigenSum (T := T) (μ := w i) hi)
    exact Module.End.mem_eigenspace_iff.2 (pieceOperator_apply_of_mem w horth hx)

/-! ## The graded pieces of a filtration -/

section Graded

variable {m : ℕ}

theorem le_castSucc_of_lt_succ {i : Fin (m + 2)} {j : Fin (m + 1)} (h : i < j.succ) :
    i ≤ j.castSucc := by
  rw [Fin.lt_def, Fin.val_succ] at h
  rw [Fin.le_def, Fin.val_castSucc]
  omega

theorem lt_succ_of_le_castSucc {i : Fin (m + 2)} {j : Fin (m + 1)} (h : i ≤ j.castSucc) :
    i < j.succ := by
  rw [Fin.le_def, Fin.val_castSucc] at h
  rw [Fin.lt_def, Fin.val_succ]
  omega

theorem castSucc_lt_succ' (j : Fin (m + 1)) : j.castSucc < j.succ := by
  rw [Fin.lt_def, Fin.val_castSucc, Fin.val_succ]
  omega

/-- The new part of a member of a filtration: what it adds orthogonally to everything below. -/
noncomputable def gradedPiece (A : Fin (m + 2) → Submodule ℂ E) (j : Fin (m + 2)) :
    Submodule ℂ E :=
  A j ⊓ (⨆ i ∈ {i : Fin (m + 2) | i < j}, A i)ᗮ

omit [FiniteDimensional ℂ E] in
theorem gradedPiece_le (A : Fin (m + 2) → Submodule ℂ E) (j : Fin (m + 2)) :
    gradedPiece A j ≤ A j := inf_le_left

omit [FiniteDimensional ℂ E] in
theorem inner_gradedPiece_eq_zero_of_lt (A : Fin (m + 2) → Submodule ℂ E) {i j : Fin (m + 2)}
    (hij : i < j) {x y : E} (hx : x ∈ gradedPiece A i) (hy : y ∈ gradedPiece A j) :
    inner ℂ x y = (0 : ℂ) := by
  have hxP : x ∈ ⨆ k ∈ {k : Fin (m + 2) | k < j}, A k :=
    le_iSup₂ (f := fun k (_ : k ∈ {k : Fin (m + 2) | k < j}) => A k) i hij hx.1
  exact inner_eq_zero_comm ((Submodule.mem_orthogonal' _ _).1 hy.2 x hxP)

omit [FiniteDimensional ℂ E] in
theorem inner_gradedPiece_eq_zero (A : Fin (m + 2) → Submodule ℂ E) {i j : Fin (m + 2)}
    (hij : i ≠ j) {x y : E} (hx : x ∈ gradedPiece A i) (hy : y ∈ gradedPiece A j) :
    inner ℂ x y = (0 : ℂ) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact inner_gradedPiece_eq_zero_of_lt A h hx hy
  · exact inner_eq_zero_comm (inner_gradedPiece_eq_zero_of_lt A h hy hx)

theorem sup_gradedPiece (A : Fin (m + 2) → Submodule ℂ E) (hA : Monotone A) (j : Fin (m + 2)) :
    (⨆ i ∈ {i : Fin (m + 2) | i < j}, A i) ⊔ gradedPiece A j = A j := by
  have hle : (⨆ i ∈ {i : Fin (m + 2) | i < j}, A i) ≤ A j := iSup₂_le fun i hi => hA (le_of_lt hi)
  have hproj : (⨆ i ∈ {i : Fin (m + 2) | i < j}, A i).HasOrthogonalProjection := inferInstance
  show (⨆ i ∈ {i : Fin (m + 2) | i < j}, A i) ⊔ (A j ⊓ (⨆ i ∈ {i : Fin (m + 2) | i < j}, A i)ᗮ)
      = A j
  rw [inf_comm]
  exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hle

omit [FiniteDimensional ℂ E] in
theorem iSup_below_eq (A : Fin (m + 2) → Submodule ℂ E) (hA : Monotone A) (j : Fin (m + 1)) :
    (⨆ i ∈ {i : Fin (m + 2) | i < j.succ}, A i) = A j.castSucc := by
  refine le_antisymm (iSup₂_le fun i hi => hA (le_castSucc_of_lt_succ hi)) ?_
  exact le_iSup₂ (f := fun i (_ : i ∈ {i : Fin (m + 2) | i < j.succ}) => A i) j.castSucc
    (castSucc_lt_succ' j)

theorem iSup_gradedPiece_eq (A : Fin (m + 2) → Submodule ℂ E) (hA : Monotone A)
    (j : Fin (m + 2)) :
    (⨆ i ∈ {i : Fin (m + 2) | i ≤ j}, gradedPiece A i) = A j := by
  induction j using Fin.induction with
  | zero =>
      have hbot : (⨆ i ∈ {i : Fin (m + 2) | i < (0 : Fin (m + 2))}, A i) = ⊥ :=
        iSup₂_eq_bot.2 fun i hi => absurd hi (by simp)
      have h0 : (0 : Fin (m + 2)) ∈ {i : Fin (m + 2) | i ≤ (0 : Fin (m + 2))} := by
        simp only [Set.mem_setOf_eq]
        exact le_rfl
      have hone : (⨆ i ∈ {i : Fin (m + 2) | i ≤ (0 : Fin (m + 2))}, gradedPiece A i)
          = gradedPiece A 0 := by
        refine le_antisymm (iSup₂_le fun i hi => ?_)
          (le_iSup₂ (f := fun i (_ : i ∈ {i : Fin (m + 2) | i ≤ (0 : Fin (m + 2))}) =>
            gradedPiece A i) 0 h0)
        rw [le_antisymm hi (Fin.zero_le i)]
      rw [hone, ← sup_gradedPiece A hA 0, hbot, bot_sup_eq]
  | succ j ih =>
      have hsplit : (⨆ i ∈ {i : Fin (m + 2) | i ≤ j.succ}, gradedPiece A i)
          = (⨆ i ∈ {i : Fin (m + 2) | i ≤ j.castSucc}, gradedPiece A i) ⊔ gradedPiece A j.succ := by
        have hsucc : j.succ ∈ {i : Fin (m + 2) | i ≤ j.succ} := by
          simp only [Set.mem_setOf_eq]
          exact le_rfl
        refine le_antisymm (iSup₂_le fun i hi => ?_) (sup_le (iSup₂_le fun i hi => ?_) ?_)
        · rcases eq_or_lt_of_le (show i ≤ j.succ from hi) with h | h
          · exact le_sup_of_le_right (le_of_eq (by rw [h]))
          · exact le_sup_of_le_left
              (le_iSup₂ (f := fun i (_ : i ∈ {i : Fin (m + 2) | i ≤ j.castSucc}) =>
                gradedPiece A i) i (le_castSucc_of_lt_succ h))
        · exact le_iSup₂ (f := fun i (_ : i ∈ {i : Fin (m + 2) | i ≤ j.succ}) => gradedPiece A i) i
            (le_of_lt (lt_succ_of_le_castSucc hi))
        · exact le_iSup₂ (f := fun i (_ : i ∈ {i : Fin (m + 2) | i ≤ j.succ}) => gradedPiece A i)
            j.succ hsucc
      rw [hsplit, ih, ← iSup_below_eq A hA j]
      exact sup_gradedPiece A hA j.succ

theorem iSup_gradedPiece_top (A : Fin (m + 2) → Submodule ℂ E) (hA : Monotone A)
    (htop : A (Fin.last (m + 1)) = ⊤) : (⨆ i, gradedPiece A i) = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← htop, ← iSup_gradedPiece_eq A hA (Fin.last (m + 1))]
  exact iSup₂_le fun i _ => le_iSup (fun i => gradedPiece A i) i

/-- **The degeneration flag of the operator built from a filtration is that filtration.** -/
theorem eigenSum_pieceOperator_filtration (A : Fin (m + 2) → Submodule ℂ E) (hA : Monotone A)
    (htop : A (Fin.last (m + 1)) = ⊤) (j : Fin (m + 2)) :
    eigenSum (pieceOperator (gradedPiece A) (fun i => -((i : ℕ) : ℝ)))
        (-((j : ℕ) : ℝ) - 1 / 2) = A j := by
  rw [eigenSum_pieceOperator _ (fun i j hij x hx y hy => inner_gradedPiece_eq_zero A hij hx hy)
    (iSup_gradedPiece_top A hA htop), ← iSup_gradedPiece_eq A hA j]
  have hset : {i : Fin (m + 2) | -((j : ℕ) : ℝ) - 1 / 2 < -((i : ℕ) : ℝ)}
      = {i : Fin (m + 2) | i ≤ j} := by
    ext i
    simp only [Set.mem_setOf_eq, Fin.le_def]
    constructor
    · intro h
      by_contra hcon
      have hji : (j : ℕ) + 1 ≤ (i : ℕ) := by omega
      have : ((j : ℕ) : ℝ) + 1 ≤ ((i : ℕ) : ℝ) := by exact_mod_cast hji
      linarith
    · intro h
      have : ((i : ℕ) : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast h
      linarith
  rw [hset]

end Graded

/-! ## Realizing a given flag -/

/-- **Every flag of the building is the degeneration flag of a Hermitian direction.**  So the
simplices of the building are exactly the asymptotic degeneration patterns of observer metrics: no
horizon flag is missed. -/
theorem exists_isSymmetric_eigenSum_eq {m : ℕ} (f : Fin (m + 1) → properPart (Submodule ℂ E))
    (hf : StrictMono f) :
    ∃ T : E →ₗ[ℂ] E, T.IsSymmetric ∧ ∀ j, ∃ c : ℝ, eigenSum T c = (f j : Submodule ℂ E) := by
  classical
  set A : Fin (m + 2) → Submodule ℂ E :=
    fun j => if h : (j : ℕ) < m + 1 then (f ⟨j, h⟩ : Submodule ℂ E) else ⊤ with hA
  have hAmono : Monotone A := by
    intro i j hij
    simp only [hA]
    split_ifs with hi hj hj
    · exact hf.monotone (show (⟨i, hi⟩ : Fin (m + 1)) ≤ ⟨j, hj⟩ from hij)
    · exact le_top
    · exact absurd (lt_of_le_of_lt (show (i : ℕ) ≤ (j : ℕ) from hij) hj) hi
    · exact le_rfl
  have hAtop : A (Fin.last (m + 1)) = ⊤ := by
    simp only [hA, Fin.val_last]
    rw [dif_neg (by omega)]
  refine ⟨pieceOperator (gradedPiece A) (fun i => -((i : ℕ) : ℝ)),
    isSymmetric_pieceOperator _ _, fun j => ?_⟩
  have hAf : A j.castSucc = (f j : Submodule ℂ E) := by
    simp only [hA, Fin.val_castSucc]
    rw [dif_pos j.2]
  exact ⟨-((j.castSucc : ℕ) : ℝ) - 1 / 2, by
    rw [eigenSum_pieceOperator_filtration A hAmono hAtop j.castSucc, hAf]⟩

end GaloisForLFunctions.HTGeometry
