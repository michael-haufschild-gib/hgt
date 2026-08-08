import GaloisForLFunctions.RHTower.RiemannXiZerosInfinite

/-!
# The zero abscissa of the Riemann zeta function

The zero set of `ζ` is nonempty and lies strictly left of `Re = 1`, so

```
Θ = sup { Re ρ : ζ ρ = 0 }
```

exists and satisfies `1/2 ≤ Θ ≤ 1`.  Nonemptiness is the unconditional zero-existence theorem
`exists_riemannZeta_zero_mem_openStrip`; the lower bound `1/2 ≤ Θ` comes from the functional
equation, which reflects a zero at `ρ` to a zero at `1 - ρ`.

No zero lies to the right of `Θ` (`riemannZeta_ne_zero_of_zetaZeroAbscissa_lt`) and zeros
accumulate arbitrarily close to it from the left (`exists_zetaZero_lt_re`).
-/

open Complex

namespace RHTower

/-- Real parts of the zeros of `ζ`. -/
def zetaZeroReSet : Set ℝ := {x : ℝ | ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ.re = x}

/-- **The zeta zero abscissa** `Θ`. -/
noncomputable def zetaZeroAbscissa : ℝ := sSup zetaZeroReSet

theorem bddAbove_zetaZeroReSet : BddAbove zetaZeroReSet := by
  refine ⟨1, fun x hx => ?_⟩
  obtain ⟨ρ, hzero, rfl⟩ := hx
  by_contra hcon
  exact riemannZeta_ne_zero_of_one_le_re (le_of_lt (not_le.mp hcon)) hzero

theorem zetaZeroReSet_nonempty : zetaZeroReSet.Nonempty := by
  obtain ⟨ρ, -, -, hzero⟩ := exists_riemannZeta_zero_mem_openStrip
  exact ⟨ρ.re, ρ, hzero, rfl⟩

/-- Every zero lies at or left of the abscissa. -/
theorem re_le_zetaZeroAbscissa {ρ : ℂ} (hzero : riemannZeta ρ = 0) :
    ρ.re ≤ zetaZeroAbscissa :=
  le_csSup bddAbove_zetaZeroReSet ⟨ρ, hzero, rfl⟩

/-- **Nonvanishing right of the abscissa.** -/
theorem riemannZeta_ne_zero_of_zetaZeroAbscissa_lt {s : ℂ} (hs : zetaZeroAbscissa < s.re) :
    riemannZeta s ≠ 0 := fun hzero =>
  absurd (re_le_zetaZeroAbscissa hzero) (not_le.mpr hs)

/-- **Zeros accumulate at the abscissa.** -/
theorem exists_zetaZero_lt_re {b : ℝ} (hb : b < zetaZeroAbscissa) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ b < ρ.re := by
  obtain ⟨x, hx, hbx⟩ := exists_lt_of_lt_csSup zetaZeroReSet_nonempty hb
  obtain ⟨ρ, hzero, hre⟩ := hx
  exact ⟨ρ, hzero, by rw [hre]; exact hbx⟩

/-- The functional equation reflects a nontrivial zero across the critical line. -/
theorem riemannZeta_one_sub_eq_zero_of_mem_openStrip {ρ : ℂ}
    (hzero : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    riemannZeta (1 - ρ) = 0 := by
  have hρ0 : ρ ≠ 0 := by
    intro h
    rw [h] at h0
    simp at h0
  have hΓ : Complex.Gammaℝ ρ ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos h0
  have hLam : completedRiemannZeta ρ = 0 := by
    have h := riemannZeta_def_of_ne_zero hρ0
    rw [hzero] at h
    field_simp at h
    simpa using h.symm
  have hsub0 : (1 : ℂ) - ρ ≠ 0 := by
    intro h
    have : ρ = 1 := by linear_combination -h
    rw [this] at h1
    simp at h1
  rw [riemannZeta_def_of_ne_zero hsub0, completedRiemannZeta_one_sub, hLam, zero_div]

/-- The abscissa reaches the critical line. -/
theorem half_le_zetaZeroAbscissa : (1 / 2 : ℝ) ≤ zetaZeroAbscissa := by
  obtain ⟨ρ, h0, h1, hzero⟩ := exists_riemannZeta_zero_mem_openStrip
  rcases le_or_gt (1 / 2 : ℝ) ρ.re with h | h
  · exact le_trans h (re_le_zetaZeroAbscissa hzero)
  · have hrefl := riemannZeta_one_sub_eq_zero_of_mem_openStrip hzero h0 h1
    have hre : ((1 : ℂ) - ρ).re = 1 - ρ.re := by simp
    have := re_le_zetaZeroAbscissa hrefl
    rw [hre] at this
    linarith

/-- The abscissa does not exceed `1`. -/
theorem zetaZeroAbscissa_le_one : zetaZeroAbscissa ≤ 1 :=
  csSup_le zetaZeroReSet_nonempty fun x hx => by
    obtain ⟨ρ, hzero, rfl⟩ := hx
    by_contra hcon
    exact riemannZeta_ne_zero_of_one_le_re (le_of_lt (not_le.mp hcon)) hzero

theorem zetaZeroAbscissa_pos : 0 < zetaZeroAbscissa := by
  have := half_le_zetaZeroAbscissa
  linarith

/-- **A zero in the open strip strictly right of any subcritical level.** -/
theorem exists_zetaZero_mem_openStrip_lt_re {b : ℝ} (hb : b < zetaZeroAbscissa) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ.re < 1 ∧ b < ρ.re := by
  obtain ⟨ρ, hzero, hbρ⟩ := exists_zetaZero_lt_re hb
  refine ⟨ρ, hzero, ?_, hbρ⟩
  by_contra hcon
  exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hcon) hzero

end RHTower
