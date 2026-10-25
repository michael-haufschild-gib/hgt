import GaloisForLFunctions.ArithmeticDefectRigidity.ResettingTheMovingOriginAddsTheMaxKernel

/-!
# A constant origin boundary violates cofactor contraction

Adding positive constant Gram mass gives a diagonal bounded away from zero.
It cannot be the kernel of any actual zero-origin common cofactor limit.
-/

section
noncomputable section
set_option autoImplicit false
open Filter Topology

namespace GaloisForLFunctions.ArithmeticDefectRigidity

/-- A nonzero unreset origin trace violates the actual zero-origin dilation diagonal. -/
theorem unreset_boundary_violates_diagonal {ε : SubcriticalDamping}
    (L : ActualCofactorLimit ε) {c : ℝ} (hc : 0 < c) :
    ¬ ∀ j : ℕ+, |(L.kernel j j + c) / (1 + c)| ≤ 1 / (j : ℝ) := by
  intro h
  have hden : 0 < 1 + c := by linarith only [hc]
  obtain ⟨n, hn⟩ := exists_nat_gt ((1 + c) / c)
  have hn0 : (0 : ℝ) < n := (div_pos hden hc).trans hn
  let j : ℕ+ := ⟨n, by exact_mod_cast hn0⟩
  have hK : 0 ≤ L.kernel j j := by
    rw [← ActualCofactorLimit.norm_vector_sq]
    exact sq_nonneg _
  have hle : c / (1 + c) ≤ 1 / (n : ℝ) :=
    (div_le_div_of_nonneg_right (le_add_of_nonneg_left hK) hden.le).trans
      ((le_abs_self _).trans (h j))
  have hmul := (div_le_div_iff₀ hden hn0).mp hle
  have hstrict := (div_lt_iff₀ hc).mp hn
  nlinarith only [hmul, hstrict]

/-- The unreset boundary cannot be another actual common zero-origin cofactor limit. -/
theorem unreset_boundary_ne_actual_kernel {ε δ : SubcriticalDamping}
    (L : ActualCofactorLimit ε) (M : ActualCofactorLimit δ) {c : ℝ} (hc : 0 < c) :
    ¬ ∀ j k : ℕ+, M.kernel j k = (L.kernel j k + c) / (1 + c) := by
  intro h
  apply unreset_boundary_violates_diagonal L hc
  intro j
  have hb := M.abs_kernel_le j j
  rw [h j j] at hb
  have hr : cofactorGramRadius j j = 1 / (j : ℝ) := by
    unfold cofactorGramRadius
    rw [← pow_two, div_pow, one_pow, Real.sq_sqrt (by positivity)]
  rwa [hr] at hb

end GaloisForLFunctions.ArithmeticDefectRigidity

#print axioms GaloisForLFunctions.ArithmeticDefectRigidity.unreset_boundary_ne_actual_kernel
end
end
