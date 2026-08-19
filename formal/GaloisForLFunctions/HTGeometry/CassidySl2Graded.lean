import Mathlib

/-!
# Cassidy's classification for `sl₂`: the graded case

A differential algebraic subgroup of `SL₂` is described by its Lie algebra, a `k`-Lie subalgebra of
`sl₂(U)` over the constants `k`, and Cassidy's theorem says that a Zariski-dense one is conjugate to
`sl₂(k')`.  This file proves the computational heart in the graded (toral) case.

If the subalgebra is graded by the standard torus, it has the form `k·h + V·e + W·f` for `k`-subspaces
`V, W ⊆ U`, and closure under `[V·e, W·f] = (V·W)·h` forces `V·W ⊆ k`.  Two nonzero `k`-subspaces of a
field whose product lands in `k` are both `k`-lines: dividing two elements of `V` by a common element
of `W` puts their ratio in `k`.  Conjugating by `diag(1, v₀)` then normalises the subalgebra to
`sl₂(k)` — no square root is needed, so the statement holds over any field.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### Two subspaces whose product lands in the base -/

/-- **A subspace whose product with a nonzero subspace lands in the base is a line.** -/
theorem eq_span_singleton_of_mul_mem_range
    {k U : Type*} [Field k] [Field U] [Algebra k U]
    (V W : Submodule k U) (hV : V ≠ ⊥) (hW : W ≠ ⊥)
    (hmul : ∀ v ∈ V, ∀ w ∈ W, ∃ c : k, v * w = algebraMap k U c) :
    ∃ v₀ ∈ V, v₀ ≠ 0 ∧ V = Submodule.span k {v₀} := by
  obtain ⟨v₀, hv₀V, hv₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
  obtain ⟨w₀, hw₀W, hw₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  refine ⟨v₀, hv₀V, hv₀, le_antisymm ?_ ?_⟩
  · intro v hv
    obtain ⟨a, ha⟩ := hmul v hv w₀ hw₀W
    obtain ⟨b, hb⟩ := hmul v₀ hv₀V w₀ hw₀W
    have hbne : b ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hb
      exact (mul_ne_zero hv₀ hw₀) hb
    have hkey : v * (v₀ * w₀) = (v * w₀) * v₀ := by ring
    rw [hb, ha] at hkey
    have hbU : algebraMap k U b ≠ 0 := by
      simpa using (map_ne_zero_iff (algebraMap k U) (algebraMap k U).injective).mpr hbne
    have hv_eq : v = algebraMap k U (a * b⁻¹) * v₀ := by
      rw [map_mul, map_inv₀]
      field_simp
      linear_combination hkey
    refine Submodule.mem_span_singleton.mpr ⟨a * b⁻¹, ?_⟩
    rw [Algebra.smul_def]
    exact hv_eq.symm
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hv₀V

/-! ### The graded subalgebra of `sl₂` -/

variable (U : Type*) [Field U]

/-- The raising matrix. -/
def sl2E : Matrix (Fin 2) (Fin 2) U := !![0, 1; 0, 0]

/-- The lowering matrix. -/
def sl2F : Matrix (Fin 2) (Fin 2) U := !![0, 0; 1, 0]

/-- The toral matrix. -/
def sl2H : Matrix (Fin 2) (Fin 2) U := !![1, 0; 0, -1]

variable {U}

/-- The root bracket: `[v e, w f] = (v w) h`. -/
theorem sl2_bracket_smul_E_F (v w : U) :
    (v • sl2E U) * (w • sl2F U) - (w • sl2F U) * (v • sl2E U) = (v * w) • sl2H U := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2E, sl2F, sl2H, mul_comm]

/-- The diagonal conjugator `diag(1, v)`. -/
def sl2Diag (v : U) : Matrix (Fin 2) (Fin 2) U := !![1, 0; 0, v]

theorem sl2Diag_conj_E {v : U} (hv : v ≠ 0) :
    sl2Diag v * (v • sl2E U) * sl2Diag v⁻¹ = sl2E U := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Diag, sl2E, Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ hv]

theorem sl2Diag_conj_F (v w : U) :
    sl2Diag v * (w • sl2F U) * sl2Diag v⁻¹ = (v * w) • sl2F U := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Diag, sl2F, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2Diag_conj_H {v : U} (hv : v ≠ 0) :
    sl2Diag v * sl2H U * sl2Diag v⁻¹ = sl2H U := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Diag, sl2H, Matrix.mul_apply, Fin.sum_univ_two, mul_inv_cancel₀ hv]

/-- **The graded case of Cassidy's classification for `sl₂`.**  A graded `k`-Lie subalgebra of
`sl₂(U)` with both root spaces nonzero has `k`-lines as root spaces, and conjugating by
`diag(1, v₀)` normalises it to `sl₂(k)`. -/
theorem graded_cassidy_sl2 {k : Type*} [Field k] [Algebra k U]
    (V W : Submodule k U) (hV : V ≠ ⊥) (hW : W ≠ ⊥)
    (hclosed : ∀ v ∈ V, ∀ w ∈ W, ∃ c : k,
      (v • sl2E U) * (w • sl2F U) - (w • sl2F U) * (v • sl2E U)
        = (algebraMap k U c) • sl2H U) :
    ∃ (v₀ w₀ : U) (b : k), v₀ ≠ 0 ∧ w₀ ≠ 0 ∧ b ≠ 0 ∧
      V = Submodule.span k {v₀} ∧ W = Submodule.span k {w₀} ∧
      v₀ * w₀ = algebraMap k U b ∧
      sl2Diag v₀ * (v₀ • sl2E U) * sl2Diag v₀⁻¹ = sl2E U ∧
      sl2Diag v₀ * (w₀ • sl2F U) * sl2Diag v₀⁻¹ = (algebraMap k U b) • sl2F U ∧
      sl2Diag v₀ * sl2H U * sl2Diag v₀⁻¹ = sl2H U := by
  have hmul : ∀ v ∈ V, ∀ w ∈ W, ∃ c : k, v * w = algebraMap k U c := by
    intro v hv w hw
    obtain ⟨c, hc⟩ := hclosed v hv w hw
    refine ⟨c, ?_⟩
    rw [sl2_bracket_smul_E_F] at hc
    have := congrFun (congrFun hc 0) 0
    simpa [sl2H] using this
  have hmul' : ∀ w ∈ W, ∀ v ∈ V, ∃ c : k, w * v = algebraMap k U c := by
    intro w hw v hv
    obtain ⟨c, hc⟩ := hmul v hv w hw
    exact ⟨c, by rw [mul_comm]; exact hc⟩
  obtain ⟨v₀, hv₀V, hv₀, hVspan⟩ := eq_span_singleton_of_mul_mem_range V W hV hW hmul
  obtain ⟨w₀, hw₀W, hw₀, hWspan⟩ := eq_span_singleton_of_mul_mem_range W V hW hV hmul'
  obtain ⟨b, hb⟩ := hmul v₀ hv₀V w₀ hw₀W
  have hbne : b ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hb
    exact (mul_ne_zero hv₀ hw₀) hb
  refine ⟨v₀, w₀, b, hv₀, hw₀, hbne, hVspan, hWspan, hb, sl2Diag_conj_E hv₀, ?_,
    sl2Diag_conj_H hv₀⟩
  rw [sl2Diag_conj_F, hb]

end

end GaloisForLFunctions.HTGeometry
