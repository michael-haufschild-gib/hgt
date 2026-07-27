import GaloisForLFunctions.RHTower.DirichletLZeroHalfPlane

/-!
# The zero abscissa of a Dirichlet L-function

For a nontrivial primitive character the zero set of `L(·,χ)` is nonempty and lies strictly left of
`Re = 1`, so the supremum

```
Θ_χ = sup { Re ρ : L(ρ,χ) = 0 }
```

exists and satisfies `1/2 ≤ Θ_χ ≤ 1`.  It is the zero frontier appearing in the order laws: no zero
lies to the right of it, and zeros accumulate arbitrarily close to it from the left.
-/

open Complex

namespace RHTower

variable {N : ℕ} [NeZero N]

/-- Real parts of the zeros of `L(·,χ)`. -/
def zeroReSet (χ : DirichletCharacter ℂ N) : Set ℝ :=
  {x : ℝ | ∃ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 ∧ ρ.re = x}

/-- **The zero abscissa** `Θ_χ`. -/
noncomputable def zeroAbscissa (χ : DirichletCharacter ℂ N) : ℝ := sSup (zeroReSet χ)

theorem bddAbove_zeroReSet {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    BddAbove (zeroReSet χ) := by
  refine ⟨1, fun x hx => ?_⟩
  obtain ⟨ρ, hzero, rfl⟩ := hx
  by_contra hcon
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (le_of_lt (not_le.mp hcon))
    hzero

theorem zeroReSet_nonempty {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) :
    (zeroReSet χ).Nonempty := by
  obtain ⟨ρ, _, hzero⟩ := exists_LFunction_eq_zero_half_le_re hχ hprim
  exact ⟨ρ.re, ρ, hzero, rfl⟩

/-- Every zero lies at or left of the abscissa. -/
theorem re_le_zeroAbscissa {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0) : ρ.re ≤ zeroAbscissa χ :=
  le_csSup (bddAbove_zeroReSet hχ) ⟨ρ, hzero, rfl⟩

/-- **Nonvanishing right of the abscissa.** -/
theorem LFunction_ne_zero_of_zeroAbscissa_lt {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {s : ℂ}
    (hs : zeroAbscissa χ < s.re) : DirichletCharacter.LFunction χ s ≠ 0 := fun hzero =>
  absurd (re_le_zeroAbscissa hχ hzero) (not_le.mpr hs)

/-- **Zeros accumulate at the abscissa.** -/
theorem exists_zero_lt_re {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hprim : χ.IsPrimitive)
    {b : ℝ} (hb : b < zeroAbscissa χ) :
    ∃ ρ : ℂ, DirichletCharacter.LFunction χ ρ = 0 ∧ b < ρ.re := by
  obtain ⟨x, hx, hbx⟩ := exists_lt_of_lt_csSup (zeroReSet_nonempty hχ hprim) hb
  obtain ⟨ρ, hzero, hre⟩ := hx
  exact ⟨ρ, hzero, by rw [hre]; exact hbx⟩

/-- The abscissa reaches the critical line. -/
theorem half_le_zeroAbscissa {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) :
    (1 / 2 : ℝ) ≤ zeroAbscissa χ := by
  obtain ⟨ρ, hρre, hzero⟩ := exists_LFunction_eq_zero_half_le_re hχ hprim
  exact le_trans hρre (re_le_zeroAbscissa hχ hzero)

/-- The abscissa does not exceed `1`. -/
theorem zeroAbscissa_le_one {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) :
    zeroAbscissa χ ≤ 1 :=
  csSup_le (zeroReSet_nonempty hχ hprim) fun x hx => by
    obtain ⟨ρ, hzero, rfl⟩ := hx
    by_contra hcon
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
      (le_of_lt (not_le.mp hcon)) hzero

/-- The abscissa is positive. -/
theorem zeroAbscissa_pos {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) :
    0 < zeroAbscissa χ := by
  have := half_le_zeroAbscissa hχ hprim
  linarith

end RHTower
