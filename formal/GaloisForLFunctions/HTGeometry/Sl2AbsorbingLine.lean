import GaloisForLFunctions.HTGeometry.CassidySl2Graded

/-!
# Absorption: one `U`-line inside a spanning Lie subalgebra of `sl₂` forces all of `sl₂`

Let `C ⊆ U` be fields and `L ⊆ sl₂(U)` a `C`-subspace closed under the bracket whose `U`-span is all
of `sl₂(U)`.  If `L` contains a whole `U`-line `U · Y` with `Y ≠ 0`, then `L` is all of `sl₂(U)`.

The mechanism is that the matrices whose entire `U`-line lies in `L` form a `U`-submodule which is an
ideal for the bracket against `span_U L = sl₂(U)`, and `sl₂` is simple: two brackets against the
raising matrix return a multiple of the raising matrix, two against the lowering matrix return a
multiple of the lowering matrix, and a diagonal matrix is handled by a single bracket.

This is the statement that removes the finite-dimensionality hypothesis from Cassidy's
classification: a bracket-closed spanning `C`-subspace of `sl₂(U)` either has all its line
stabilisers proper, or it is the whole of `sl₂(U)`.

* `absorbSubmodule`, `bracket_mem_absorbSubmodule`;
* `sl2_eq_of_absorbing` — the absorption theorem.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C U : Type*} [Field C] [Field U] [Algebra C U]

/-! ### Entries of the standard basis -/

@[simp] theorem sl2E_00 : (sl2E U) 0 0 = 0 := by simp [sl2E]
@[simp] theorem sl2E_01 : (sl2E U) 0 1 = 1 := by simp [sl2E]
@[simp] theorem sl2E_10 : (sl2E U) 1 0 = 0 := by simp [sl2E]
@[simp] theorem sl2E_11 : (sl2E U) 1 1 = 0 := by simp [sl2E]
@[simp] theorem sl2F_00 : (sl2F U) 0 0 = 0 := by simp [sl2F]
@[simp] theorem sl2F_01 : (sl2F U) 0 1 = 0 := by simp [sl2F]
@[simp] theorem sl2F_10 : (sl2F U) 1 0 = 1 := by simp [sl2F]
@[simp] theorem sl2F_11 : (sl2F U) 1 1 = 0 := by simp [sl2F]
@[simp] theorem sl2H_00 : (sl2H U) 0 0 = 1 := by simp [sl2H]
@[simp] theorem sl2H_01 : (sl2H U) 0 1 = 0 := by simp [sl2H]
@[simp] theorem sl2H_10 : (sl2H U) 1 0 = 0 := by simp [sl2H]
@[simp] theorem sl2H_11 : (sl2H U) 1 1 = -1 := by simp [sl2H]

section Brackets

attribute [local simp] Matrix.sub_apply Matrix.add_apply Matrix.smul_apply Matrix.mul_apply
  Fin.sum_univ_two smul_eq_mul Fin.zero_eta Fin.mk_one

/-- The bracket of the raising matrix against an arbitrary matrix. -/
theorem sl2_bracket_E (Z : Matrix (Fin 2) (Fin 2) U) :
    sl2E U * Z - Z * sl2E U = (Z 1 0) • sl2H U + (Z 1 1 - Z 0 0) • sl2E U := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- Two brackets against the raising matrix return a multiple of the raising matrix. -/
theorem sl2_bracket_E_E (Z : Matrix (Fin 2) (Fin 2) U) :
    sl2E U * (sl2E U * Z - Z * sl2E U) - (sl2E U * Z - Z * sl2E U) * sl2E U
      = (-2 * Z 1 0) • sl2E U := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

/-- Two brackets against the lowering matrix return a multiple of the lowering matrix. -/
theorem sl2_bracket_F_F (Z : Matrix (Fin 2) (Fin 2) U) :
    sl2F U * (sl2F U * Z - Z * sl2F U) - (sl2F U * Z - Z * sl2F U) * sl2F U
      = (-2 * Z 0 1) • sl2F U := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem sl2_bracket_EF : sl2E U * sl2F U - sl2F U * sl2E U = sl2H U := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem sl2_bracket_FE : sl2F U * sl2E U - sl2E U * sl2F U = (-1 : U) • sl2H U := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem sl2_bracket_HE : sl2H U * sl2E U - sl2E U * sl2H U = (2 : U) • sl2E U := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

theorem sl2_bracket_HF : sl2H U * sl2F U - sl2F U * sl2H U = (-2 : U) • sl2F U := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

@[simp] theorem trace_sl2E : (sl2E U).trace = 0 := by simp [Matrix.trace_fin_two]
@[simp] theorem trace_sl2F : (sl2F U).trace = 0 := by simp [Matrix.trace_fin_two]
@[simp] theorem trace_sl2H : (sl2H U).trace = 0 := by simp [Matrix.trace_fin_two]

/-- A traceless matrix is the obvious combination of `h`, `e`, `f`. -/
theorem sl2_traceless_decomp {Z : Matrix (Fin 2) (Fin 2) U} (hZ : Z.trace = 0) :
    Z = (Z 0 0) • sl2H U + (Z 0 1) • sl2E U + (Z 1 0) • sl2F U := by
  rw [Matrix.trace_fin_two] at hZ
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> linear_combination hZ

end Brackets

/-! ### The absorbing submodule -/

/-- The matrices all of whose `U`-multiples lie in `L`. -/
def absorbSubmodule (L : Submodule C (Matrix (Fin 2) (Fin 2) U)) :
    Submodule U (Matrix (Fin 2) (Fin 2) U) where
  carrier := {Z | ∀ c : U, c • Z ∈ L}
  zero_mem' := by
    intro c
    simpa using L.zero_mem
  add_mem' := by
    intro a b ha hb c
    have h := L.add_mem (ha c) (hb c)
    rwa [← smul_add] at h
  smul_mem' := by
    intro u Z hZ c
    have h := hZ (c * u)
    rwa [mul_smul] at h

theorem mem_absorbSubmodule {L : Submodule C (Matrix (Fin 2) (Fin 2) U)}
    {Z : Matrix (Fin 2) (Fin 2) U} :
    Z ∈ absorbSubmodule L ↔ ∀ c : U, c • Z ∈ L := Iff.rfl

theorem mem_of_mem_absorbSubmodule {L : Submodule C (Matrix (Fin 2) (Fin 2) U)}
    {Z : Matrix (Fin 2) (Fin 2) U} (hZ : Z ∈ absorbSubmodule L) : Z ∈ L := by
  have h := hZ 1
  rwa [one_smul] at h

/-- The absorbing submodule is a bracket ideal against every traceless matrix. -/
theorem bracket_mem_absorbSubmodule {L : Submodule C (Matrix (Fin 2) (Fin 2) U)}
    (hbr : ∀ A ∈ L, ∀ B ∈ L, A * B - B * A ∈ L)
    (hdense : ∀ Z : Matrix (Fin 2) (Fin 2) U, Z.trace = 0 →
      Z ∈ Submodule.span U (L : Set (Matrix (Fin 2) (Fin 2) U)))
    {Z : Matrix (Fin 2) (Fin 2) U} (hZ : Z ∈ absorbSubmodule L)
    {W : Matrix (Fin 2) (Fin 2) U} (hW : W.trace = 0) :
    Z * W - W * Z ∈ absorbSubmodule L := by
  classical
  set N : Submodule U (Matrix (Fin 2) (Fin 2) U) :=
    { carrier := {W | Z * W - W * Z ∈ absorbSubmodule L}
      zero_mem' := by
        show Z * 0 - 0 * Z ∈ absorbSubmodule L
        simpa using (absorbSubmodule L).zero_mem
      add_mem' := by
        intro a b ha hb
        have ha' : Z * a - a * Z ∈ absorbSubmodule L := ha
        have hb' : Z * b - b * Z ∈ absorbSubmodule L := hb
        show Z * (a + b) - (a + b) * Z ∈ absorbSubmodule L
        have hid : Z * (a + b) - (a + b) * Z = (Z * a - a * Z) + (Z * b - b * Z) := by
          rw [Matrix.mul_add, Matrix.add_mul]; abel
        rw [hid]
        exact (absorbSubmodule L).add_mem ha' hb'
      smul_mem' := by
        intro u a ha
        have ha' : Z * a - a * Z ∈ absorbSubmodule L := ha
        show Z * (u • a) - (u • a) * Z ∈ absorbSubmodule L
        have hid : Z * (u • a) - (u • a) * Z = u • (Z * a - a * Z) := by
          rw [Matrix.mul_smul, Matrix.smul_mul, smul_sub]
        rw [hid]
        exact (absorbSubmodule L).smul_mem u ha' } with hN
  have hLN : (L : Set (Matrix (Fin 2) (Fin 2) U)) ⊆ (N : Set (Matrix (Fin 2) (Fin 2) U)) := by
    intro A hA
    show Z * A - A * Z ∈ absorbSubmodule L
    intro c
    have hid : c • (Z * A - A * Z) = (c • Z) * A - A * (c • Z) := by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_sub]
    rw [hid]
    exact hbr _ (hZ c) _ hA
  have hspan : Submodule.span U (L : Set (Matrix (Fin 2) (Fin 2) U)) ≤ N :=
    Submodule.span_le.mpr hLN
  exact hspan (hdense W hW)

/-- **Absorption.**  A bracket-closed `C`-subspace of `sl₂(U)` whose `U`-span is all of `sl₂(U)` and
which contains one whole `U`-line is all of `sl₂(U)`. -/
theorem sl2_eq_of_absorbing [CharZero U] (L : Submodule C (Matrix (Fin 2) (Fin 2) U))
    (htr : ∀ A ∈ L, A.trace = 0)
    (hbr : ∀ A ∈ L, ∀ B ∈ L, A * B - B * A ∈ L)
    (hdense : ∀ Z : Matrix (Fin 2) (Fin 2) U, Z.trace = 0 →
      Z ∈ Submodule.span U (L : Set (Matrix (Fin 2) (Fin 2) U)))
    {Y : Matrix (Fin 2) (Fin 2) U} (hYne : Y ≠ 0) (hY : ∀ c : U, c • Y ∈ L) :
    ∀ Z : Matrix (Fin 2) (Fin 2) U, Z.trace = 0 → Z ∈ L := by
  classical
  set M := absorbSubmodule L with hM
  have hYM : Y ∈ M := hY
  have hbrM : ∀ Z ∈ M, ∀ W : Matrix (Fin 2) (Fin 2) U, W.trace = 0 → Z * W - W * Z ∈ M :=
    fun Z hZ W hW => bracket_mem_absorbSubmodule hbr hdense hZ hW
  have hbrM' : ∀ Z ∈ M, ∀ W : Matrix (Fin 2) (Fin 2) U, W.trace = 0 → W * Z - Z * W ∈ M := by
    intro Z hZ W hW
    have h := hbrM Z hZ W hW
    have hneg := M.neg_mem h
    rwa [neg_sub] at hneg
  -- the raising or the lowering matrix is absorbed
  have hEF : sl2E U ∈ M ∨ sl2F U ∈ M := by
    have hYtr : Y.trace = 0 := htr Y (mem_of_mem_absorbSubmodule hYM)
    by_cases h10 : Y 1 0 = 0
    · by_cases h01 : Y 0 1 = 0
      · left
        have hdiag := sl2_traceless_decomp hYtr
        have h00 : Y 0 0 ≠ 0 := by
          intro h
          apply hYne
          rw [hdiag, h, h01, h10]
          simp
        have h1 : sl2E U * Y - Y * sl2E U ∈ M := hbrM' Y hYM (sl2E U) trace_sl2E
        have htr2 : Y 1 1 = -(Y 0 0) := by
          rw [Matrix.trace_fin_two] at hYtr
          linear_combination hYtr
        rw [sl2_bracket_E, h10, htr2] at h1
        have hsimp : (0 : U) • sl2H U + (-(Y 0 0) - Y 0 0) • sl2E U = (-2 * Y 0 0) • sl2E U := by
          rw [zero_smul, zero_add]
          congr 1
          ring
        rw [hsimp] at h1
        have hne : (-2 * Y 0 0) ≠ 0 := by
          simp only [ne_eq, mul_eq_zero, not_or]
          exact ⟨by norm_num, h00⟩
        have := M.smul_mem (-2 * Y 0 0)⁻¹ h1
        rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
      · right
        have h1 : sl2F U * Y - Y * sl2F U ∈ M := hbrM' Y hYM (sl2F U) trace_sl2F
        have h2 : sl2F U * (sl2F U * Y - Y * sl2F U) - (sl2F U * Y - Y * sl2F U) * sl2F U ∈ M :=
          hbrM' _ h1 (sl2F U) trace_sl2F
        rw [sl2_bracket_F_F] at h2
        have hne : (-2 * Y 0 1) ≠ 0 := by
          simp only [ne_eq, mul_eq_zero, not_or]
          exact ⟨by norm_num, h01⟩
        have := M.smul_mem (-2 * Y 0 1)⁻¹ h2
        rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
    · left
      have h1 : sl2E U * Y - Y * sl2E U ∈ M := hbrM' Y hYM (sl2E U) trace_sl2E
      have h2 : sl2E U * (sl2E U * Y - Y * sl2E U) - (sl2E U * Y - Y * sl2E U) * sl2E U ∈ M :=
        hbrM' _ h1 (sl2E U) trace_sl2E
      rw [sl2_bracket_E_E] at h2
      have hne : (-2 * Y 1 0) ≠ 0 := by
        simp only [ne_eq, mul_eq_zero, not_or]
        exact ⟨by norm_num, h10⟩
      have := M.smul_mem (-2 * Y 1 0)⁻¹ h2
      rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
  -- all three basis vectors are absorbed
  have hall : sl2H U ∈ M ∧ sl2E U ∈ M ∧ sl2F U ∈ M := by
    rcases hEF with hE | hF
    · have hH : sl2H U ∈ M := by
        have h := hbrM (sl2E U) hE (sl2F U) trace_sl2F
        rwa [sl2_bracket_EF] at h
      have hF : sl2F U ∈ M := by
        have h := hbrM (sl2H U) hH (sl2F U) trace_sl2F
        rw [sl2_bracket_HF] at h
        have := M.smul_mem (-2 : U)⁻¹ h
        rwa [smul_smul, inv_mul_cancel₀ (by norm_num : (-2 : U) ≠ 0), one_smul] at this
      exact ⟨hH, hE, hF⟩
    · have hH : sl2H U ∈ M := by
        have h := hbrM (sl2F U) hF (sl2E U) trace_sl2E
        rw [sl2_bracket_FE] at h
        have := M.smul_mem (-1 : U)⁻¹ h
        rwa [smul_smul, inv_mul_cancel₀ (by norm_num : (-1 : U) ≠ 0), one_smul] at this
      have hE : sl2E U ∈ M := by
        have h := hbrM (sl2H U) hH (sl2E U) trace_sl2E
        rw [sl2_bracket_HE] at h
        have := M.smul_mem (2 : U)⁻¹ h
        rwa [smul_smul, inv_mul_cancel₀ (by norm_num : (2 : U) ≠ 0), one_smul] at this
      exact ⟨hH, hE, hF⟩
  intro Z hZ
  obtain ⟨hH, hE, hF⟩ := hall
  have hZM : Z ∈ M := by
    rw [sl2_traceless_decomp hZ]
    exact M.add_mem (M.add_mem (M.smul_mem _ hH) (M.smul_mem _ hE)) (M.smul_mem _ hF)
  exact mem_of_mem_absorbSubmodule hZM

end

end GaloisForLFunctions.HTGeometry
