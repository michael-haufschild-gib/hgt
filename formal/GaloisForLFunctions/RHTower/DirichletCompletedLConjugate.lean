import GaloisForLFunctions.RHTower.DirichletCompletedLOrderOne
import GaloisForLFunctions.HTGeometry.MellinConjugate

/-!
# The completed Dirichlet L-function under conjugation

All four theta kernels are real, so the Hurwitz completions satisfy the reflection principle
`Λ(a, conj s) = conj Λ(a, s)`.  A Dirichlet character takes values of modulus one on units, so
`conj (χ j) = χ⁻¹ j`.  Combining these in the entire representation of the completed L-function
gives

```
conj (Λ(s, χ)) = Λ(conj s, χ⁻¹).
```

Together with the functional equation this makes the zero divisor of `Λ(·,χ)` invariant under
`ρ ↦ 1 - conj ρ`, the reflection in the critical line.
-/

open Complex HurwitzZeta
open GaloisForLFunctions.HTGeometry

namespace RHTower

variable {N : ℕ} [NeZero N]

theorem conj_two : (starRingEnd ℂ) (2 : ℂ) = 2 := by
  rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.conj_ofReal]

/-- The modified kernel of a functional-equation pair with real data is real. -/
theorem conj_f_modif (P : WeakFEPair ℂ)
    (hf : ∀ x, (starRingEnd ℂ) (P.f x) = P.f x)
    (hf₀ : (starRingEnd ℂ) P.f₀ = P.f₀)
    (hg₀ : (starRingEnd ℂ) P.g₀ = P.g₀)
    (hε : (starRingEnd ℂ) P.ε = P.ε) (t : ℝ) :
    (starRingEnd ℂ) (P.f_modif t) = P.f_modif t := by
  rw [WeakFEPair.f_modif, Pi.add_apply, map_add]
  congr 1
  · exact conj_indicator (fun x => by rw [map_sub, hf, hf₀]) t
  · refine conj_indicator (fun x => ?_) t
    rw [smul_eq_mul, map_sub, hf, map_mul, map_mul, hε, Complex.conj_ofReal, hg₀]

/-- The modified even theta kernel is real. -/
theorem conj_hurwitzEvenFEPair_f_modif (a : UnitAddCircle) (t : ℝ) :
    (starRingEnd ℂ) ((hurwitzEvenFEPair a).f_modif t) = (hurwitzEvenFEPair a).f_modif t := by
  refine conj_f_modif (hurwitzEvenFEPair a) (fun x => ?_) ?_ ?_ ?_ t
  · exact Complex.conj_ofReal (evenKernel a x)
  · show (starRingEnd ℂ) (if a = 0 then (1 : ℂ) else 0) = (if a = 0 then (1 : ℂ) else 0)
    split_ifs <;> simp
  · show (starRingEnd ℂ) (1 : ℂ) = 1
    simp
  · show (starRingEnd ℂ) (1 : ℂ) = 1
    simp

/-- **Reflection principle for the entire even Hurwitz completion.** -/
theorem conj_completedHurwitzZetaEven₀ (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaEven₀ a ((starRingEnd ℂ) s)
      = (starRingEnd ℂ) (completedHurwitzZetaEven₀ a s) := by
  have hm := mellin_conj_of_conj_invariant (conj_hurwitzEvenFEPair_f_modif a) (s / 2)
  have hcs : (starRingEnd ℂ) (s / 2) = (starRingEnd ℂ) s / 2 := by simp [conj_two]
  rw [hcs] at hm
  show mellin ((hurwitzEvenFEPair a).f_modif) ((starRingEnd ℂ) s / 2) / 2
      = (starRingEnd ℂ) (mellin ((hurwitzEvenFEPair a).f_modif) (s / 2) / 2)
  rw [hm]
  simp [conj_two]

/-- **Reflection principle for the odd Hurwitz completion.** -/
theorem conj_completedHurwitzZetaOdd (a : UnitAddCircle) (s : ℂ) :
    completedHurwitzZetaOdd a ((starRingEnd ℂ) s)
      = (starRingEnd ℂ) (completedHurwitzZetaOdd a s) := by
  have hreal : ∀ t : ℝ, (starRingEnd ℂ) ((hurwitzOddFEPair a).f t)
      = (hurwitzOddFEPair a).f t := fun t => Complex.conj_ofReal (oddKernel a t)
  have hm := mellin_conj_of_conj_invariant hreal ((s + 1) / 2)
  have hcs : (starRingEnd ℂ) ((s + 1) / 2) = ((starRingEnd ℂ) s + 1) / 2 := by simp [conj_two]
  rw [hcs] at hm
  simp only [completedHurwitzZetaOdd, (isStrong_hurwitzOddFEPair a).Λ_eq]
  rw [hm]
  simp [conj_two]

/-- A Dirichlet character has unit modulus on units: its values are roots of unity. -/
theorem norm_dirichletCharacter_apply (χ : DirichletCharacter ℂ N) {a : ZMod N} (ha : IsUnit a) :
    ‖χ a‖ = 1 := by
  obtain ⟨u, rfl⟩ := ha
  have hc : 0 < Fintype.card (ZMod N)ˣ := Fintype.card_pos
  have hpow : (χ (u : ZMod N)) ^ (Fintype.card (ZMod N)ˣ) = 1 := by
    have hone := congrArg (fun ψ : MulChar (ZMod N) ℂ => ψ (u : ZMod N)) χ.pow_card_eq_one
    simpa [MulChar.pow_apply_coe, MulChar.one_apply_coe] using hone
  have hnorm : ‖χ (u : ZMod N)‖ ^ (Fintype.card (ZMod N)ˣ) = 1 := by
    rw [← norm_pow, hpow, norm_one]
  have hn := norm_nonneg (χ (u : ZMod N))
  rcases lt_trichotomy (‖χ (u : ZMod N)‖) 1 with h | h | h
  · exact absurd hnorm (ne_of_lt (pow_lt_one₀ hn h hc.ne'))
  · exact h
  · exact absurd hnorm (ne_of_gt (one_lt_pow₀ h hc.ne'))

/-- **Conjugation of a Dirichlet character is inversion.** -/
theorem conj_dirichletCharacter_apply (χ : DirichletCharacter ℂ N) (a : ZMod N) :
    (starRingEnd ℂ) (χ a) = χ⁻¹ a := by
  by_cases ha : IsUnit a
  · rw [MulChar.inv_apply_eq_inv', Complex.inv_eq_conj (norm_dirichletCharacter_apply χ ha)]
  · rw [χ.map_nonunit ha, (χ⁻¹).map_nonunit ha, map_zero]

/-- **The completed L-function under conjugation.** -/
theorem conj_completedLFunction {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (s : ℂ) :
    (starRingEnd ℂ) (DirichletCharacter.completedLFunction χ s)
      = DirichletCharacter.completedLFunction χ⁻¹ ((starRingEnd ℂ) s) := by
  have hχinv : χ⁻¹ ≠ 1 := by
    intro h
    exact hχ (by rw [← inv_inv χ, h, inv_one])
  have hsum1 : (starRingEnd ℂ)
      (∑ j : ZMod N, (χ : ZMod N → ℂ) j * completedHurwitzZetaEven₀ (ZMod.toAddCircle j) s)
      = ∑ j : ZMod N, χ⁻¹ j
          * completedHurwitzZetaEven₀ (ZMod.toAddCircle j) ((starRingEnd ℂ) s) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, conj_dirichletCharacter_apply, ← conj_completedHurwitzZetaEven₀]
  have hsum2 : (starRingEnd ℂ)
      (∑ j : ZMod N, (χ : ZMod N → ℂ) j * completedHurwitzZetaOdd (ZMod.toAddCircle j) s)
      = ∑ j : ZMod N, χ⁻¹ j
          * completedHurwitzZetaOdd (ZMod.toAddCircle j) ((starRingEnd ℂ) s) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, conj_dirichletCharacter_apply, ← conj_completedHurwitzZetaOdd]
  rw [completedLFunction_eq_sum hχ s, completedLFunction_eq_sum hχinv ((starRingEnd ℂ) s),
    map_add, map_mul, map_mul, conj_natCast_cpow_neg, hsum1, hsum2]

end RHTower
