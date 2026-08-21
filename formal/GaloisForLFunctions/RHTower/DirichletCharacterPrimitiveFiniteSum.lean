import GaloisForLFunctions.RHTower.DirichletCharacterPrimitiveDepletion

noncomputable section

namespace RHTower

/-- Closed finite Dirichlet-polynomial transport from an imprimitive nonprincipal character to
its primitive conductor character.  The original level survives exactly as the explicit filter
on coefficient indices coprime to `n + 1`; no analytic Euler-product identity is assumed. -/
theorem cglPrimitiveCharacterReduction_sum_eq_filteredPrimitive
    (n : ℕ) (χ : NonprincipalDirichletCharacter n)
    (s : Finset ℕ) (f : ℕ → ℂ) :
    (∑ m ∈ s, f m * χ.1 m) =
      ∑ m ∈ s.filter (fun m => m.Coprime (n + 1)),
        f m * (cglPrimitiveCharacterReduction n χ).primitiveCharacter m := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hcop : m.Coprime (n + 1)
  · simp only [if_pos hcop]
    rw [cglPrimitiveCharacterReduction_apply_eq_levelDepletion]
    simp [hcop]
  · simp only [if_neg hcop]
    rw [cglPrimitiveCharacterReduction_apply_eq_levelDepletion]
    simp [hcop]

end RHTower
