import GaloisForLFunctions.RHTower.XiDeterminantIdealConsequences

/-!
# Minimal regularized determinant genus

Genus `g` is admissible precisely when the approximation-number spectrum is
`(g+1)`-summable.  This records minimality as a first-class predicate and proves that every
exact self-adjoint Xi determinant carrier has minimal genus one: genus one converges, genus zero
fails.
-/

open Complex
open HilbertSchmidt

namespace RHTower

noncomputable section

/-- Genus `g` is admissible exactly when the approximation-number spectrum is summable to
power `g+1`, the convergence condition for canonical factors of genus `g`. -/
def AdmitsRegularizedDeterminantGenus
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (g : ℕ) : Prop :=
  MemSchattenClass (g + 1 : ℝ) T

/-- A genus is minimal when it is admissible and every smaller genus fails. -/
def HasMinimalRegularizedDeterminantGenus
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) (g : ℕ) : Prop :=
  AdmitsRegularizedDeterminantGenus T g ∧
    ∀ k < g, ¬ AdmitsRegularizedDeterminantGenus T k

theorem hasMinimalRegularizedDeterminantGenus_one_iff
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (T : H →L[ℂ] H) :
    HasMinimalRegularizedDeterminantGenus T 1 ↔
      MemSchattenClass 2 T ∧ ¬ MemSchattenClass 1 T := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have hgen := h.1
      norm_num [HasMinimalRegularizedDeterminantGenus,
        AdmitsRegularizedDeterminantGenus] at hgen
      exact hgen
    · have hzero := h.2 0 Nat.zero_lt_one
      simpa [AdmitsRegularizedDeterminantGenus] using hzero
  · rintro ⟨h2, h1⟩
    refine ⟨?_, ?_⟩
    · norm_num [AdmitsRegularizedDeterminantGenus]
      exact h2
    · intro k hk
      have hk0 : k = 0 := by omega
      subst k
      simpa [AdmitsRegularizedDeterminantGenus] using h1

theorem exactXiDeterminant_hasMinimalRegularizedDeterminantGenus_one
    {ι : Type*} [DecidableEq ι]
    {K : ι × ι → ℂ} (hK : IsHS K)
    (hself : IsSelfAdjoint (toOperator hK))
    (H : ℂ → ℂ) (hHanalytic : Differentiable ℂ H)
    (hH : ∀ z, H z ≠ 0)
    (hXi : ∀ z, XiC z = H z *
      GaloisForLFunctions.HTGeometry.entireDet2 K z) :
    HasMinimalRegularizedDeterminantGenus (toOperator hK) 1 := by
  rw [hasMinimalRegularizedDeterminantGenus_one_iff]
  exact ⟨exactXiDeterminant_memSchattenClass_two
      hK hself H hHanalytic hH hXi,
    exactXiDeterminant_not_memSchattenClass_one
      hK hself H hHanalytic hH hXi⟩

end

end RHTower

