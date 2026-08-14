import GaloisForLFunctions.HTGeometry.ModularMonodromyCover

/-!
# Principal congruence subgroups are torsion free, and the modular curves `X(n)`

For `n ≥ 3` the principal congruence subgroup `Γ(n) ⊆ SL(2,ℤ)` contains no element whose square
or cube is `±1` other than `±1` itself: an element of `SL(2,ℤ)` with `A² = ±1` or `A³ = ±1` has
trace in `{0, ±1, ±2}`, while a matrix congruent to the identity mod `n` has trace congruent to
`2`, and the remaining cases collapse to `A = ±1`.  Equivalently, the image `Γ(n)` in
`PSL(2,ℤ)` is torsion free.

Consequently the action of `SL(2,ℤ)` on the cosets of `Γ(n)·{±1}` has the two elliptic
generators `S` and `S·T` acting freely, so it is the monodromy of a connected unramified cover of
the modular orbifold — the modular curve `X(n)` — and

```text
[PSL(2,ℤ) : Γ(n)] = 6 (2g + s − 2)
```

with `g` its genus and `s` its number of cusps.  The index is at least `n`, so these covers have
unbounded degree.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix CongruenceSubgroup ModularGroup
open scoped MatrixGroups

section NegOne

/-- `-1` in `SL(2, ℤ)`. -/
def slNegOne : SL(2, ℤ) := ⟨!![-1, 0; 0, -1], by norm_num [Matrix.det_fin_two_of]⟩

@[simp] theorem slNegOne_coe :
    (slNegOne : Matrix (Fin 2) (Fin 2) ℤ) = !![-1, 0; 0, -1] := rfl

theorem slNegOne_mul_self : slNegOne * slNegOne = 1 := by
  apply Subtype.ext
  show (!![(-1 : ℤ), 0; 0, -1]) * !![(-1 : ℤ), 0; 0, -1] = (1 : Matrix (Fin 2) (Fin 2) ℤ)
  norm_num [Matrix.mul_fin_two, ← Matrix.one_fin_two]

theorem slNegOne_ne_one : slNegOne ≠ 1 := by
  intro h
  have := congrArg (fun A : SL(2, ℤ) => (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0) h
  simp [Matrix.one_apply] at this

theorem slNegOne_central (A : SL(2, ℤ)) : Commute slNegOne A := by
  show slNegOne * A = A * slNegOne
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply] <;> ring

/-- The central subgroup `{±1}` of `SL(2, ℤ)`. -/
def slPM : Subgroup SL(2, ℤ) where
  carrier := {A | A = 1 ∨ A = slNegOne}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro A B (rfl | rfl) (rfl | rfl)
    · exact Or.inl (one_mul _)
    · exact Or.inr (one_mul _)
    · exact Or.inr (mul_one _)
    · exact Or.inl slNegOne_mul_self
  inv_mem' := by
    rintro A (rfl | rfl)
    · exact Or.inl inv_one
    · exact Or.inr (by
        have := slNegOne_mul_self
        exact inv_eq_of_mul_eq_one_right this)

theorem mem_slPM {A : SL(2, ℤ)} : A ∈ slPM ↔ A = 1 ∨ A = slNegOne := Iff.rfl

end NegOne

section Cayley

/-- The trace of an element of `SL(2, ℤ)`. -/
def slTrace (A : SL(2, ℤ)) : ℤ := (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 + A 1 1

theorem sl_det (A : SL(2, ℤ)) :
    (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
  have h := A.2
  rwa [Matrix.det_fin_two] at h

/-- Cayley–Hamilton for `SL(2, ℤ)`: `A² = (tr A)·A − 1`. -/
theorem sl_sq_eq (A : SL(2, ℤ)) :
    ((A * A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = slTrace A • (A : Matrix (Fin 2) (Fin 2) ℤ) - 1 := by
  have hdet := sl_det A
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [slTrace, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply] <;> linarith [hdet]

/-- `A³ = (tr² − 1)·A − (tr)·1`. -/
theorem sl_cube_eq (A : SL(2, ℤ)) :
    ((A * A * A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = (slTrace A ^ 2 - 1) • (A : Matrix (Fin 2) (Fin 2) ℤ) - slTrace A • 1 := by
  have h2 := sl_sq_eq A
  have hdet := sl_det A
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [slTrace, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply] <;> ring_nf <;> nlinarith [hdet]

end Cayley

section Torsion

variable {n : ℕ}

/-- Off-diagonal vanishing and equal diagonal force `±1`. -/
theorem sl_eq_pm_one_of_offdiag {A : SL(2, ℤ)}
    (hb : (A : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = 0) (hc : (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = 0)
    (had : (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = A 1 1) : A = 1 ∨ A = slNegOne := by
  have hdet := sl_det A
  rw [hb, hc, ← had] at hdet
  have hsq : (A : Matrix (Fin 2) (Fin 2) ℤ) 0 0 * A 0 0 = 1 := by linarith
  have := Int.eq_one_or_self_of_prime
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hsq with ⟨h1, _⟩ | ⟨h1, _⟩
  · left
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.one_apply, hb, hc, h1, ← had, h1]
  · right
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.one_apply, hb, hc, h1, ← had, h1]

end Torsion

end GaloisForLFunctions.HTGeometry
