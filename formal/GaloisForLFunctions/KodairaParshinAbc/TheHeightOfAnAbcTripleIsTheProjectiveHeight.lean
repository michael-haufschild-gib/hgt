import GaloisForLFunctions.KodairaParshinAbc.TheLegendreInvariantOfAnAbcTriple
import Mathlib.NumberTheory.Height.NumberField

/-!
# The height of an `abc` triple is its projective height

The uniform `abc` inequality bounds `H(a, b, c) = ∏_v max(‖a‖_v, ‖b‖_v, ‖c‖_v)`, which is the
multiplicative projective height of the point `(a : b : c) ∈ P²`.  Over `ℚ`, for coprime integers
`a, b`, this is `max(|a|, |b|, |a + b|)` (`tripleHeight`), and it is also the height of the point
`(λ : 1 - λ : 1)` with `λ = a/(a + b)` that enters the height comparison for the Legendre
invariant:

  `h(a : b : a+b) = h(λ : 1-λ : 1) = log max(|a|, |b|, |a+b|)`.
-/

noncomputable section

open Height Real

namespace GaloisForLFunctions.KodairaParshinAbc

/-- The coordinates of a coprime triple have gcd `1`. -/
theorem gcd_abc_eq_one {a b : ℤ} (h : IsCoprime a b) :
    (Finset.univ : Finset (Fin 3)).gcd ![a, b, a + b] = 1 := by
  set g := (Finset.univ : Finset (Fin 3)).gcd ![a, b, a + b]
  have ha : g ∣ a := Finset.gcd_dvd (Finset.mem_univ (0 : Fin 3))
  have hb : g ∣ b := Finset.gcd_dvd (Finset.mem_univ (1 : Fin 3))
  have hu : IsUnit g := h.isUnit_of_dvd' ha hb
  have hn : normalize g = g := Finset.normalize_gcd
  rw [← hn]
  exact normalize_eq_one.mpr hu

theorem iSup_abs_abc (a b : ℤ) : (⨆ i, |(![a, b, a + b] : Fin 3 → ℤ) i|) = tripleHeight a b := by
  apply le_antisymm
  · refine ciSup_le fun i => ?_
    obtain ⟨h0, h1, h2⟩ := abs_le_tripleHeight a b
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  · have hbdd : BddAbove (Set.range fun i => |(![a, b, a + b] : Fin 3 → ℤ) i|) :=
      (Set.finite_range _).bddAbove
    rcases tripleHeight_mem a b with h | h | h <;> rw [h]
    · exact le_ciSup hbdd (0 : Fin 3)
    · exact le_ciSup hbdd (1 : Fin 3)
    · exact le_ciSup hbdd (2 : Fin 3)

/-- **`h(a : b : a+b) = log max(|a|, |b|, |a+b|)`** for coprime `a, b`. -/
theorem logHeight_abc {a b : ℤ} (h : IsCoprime a b) :
    logHeight (((↑) : ℤ → ℚ) ∘ ![a, b, a + b]) = Real.log (tripleHeight a b : ℝ) := by
  rw [Rat.logHeight_eq_max_abs_of_gcd_eq_one (gcd_abc_eq_one h), iSup_abs_abc]

/-- The point `(λ : 1-λ : 1)`, `λ = a/(a+b)`, is the point `(a : b : a+b)`. -/
theorem logHeight_legendrePoint {a b : ℤ} (hc : a + b ≠ 0) :
    logHeight ![((a : ℚ) / (a + b)), 1 - (a : ℚ) / (a + b), 1] =
      logHeight (((↑) : ℤ → ℚ) ∘ ![a, b, a + b]) := by
  have hc' : ((a : ℚ) + b) ≠ 0 := by exact_mod_cast hc
  have hinv : ((a : ℚ) + b)⁻¹ ≠ 0 := inv_ne_zero hc'
  rw [← logHeight_smul_eq_logHeight (((↑) : ℤ → ℚ) ∘ ![a, b, a + b]) hinv]
  congr 1
  funext i
  fin_cases i <;> simp <;> field_simp
  ring

/-- **The paper's height of the triple**: for coprime `a, b` with `a + b ≠ 0`,
`h(λ : 1-λ : 1) = log max(|a|, |b|, |a+b|)`. -/
theorem logHeight_legendrePoint_eq {a b : ℤ} (h : IsCoprime a b) (hc : a + b ≠ 0) :
    logHeight ![((a : ℚ) / (a + b)), 1 - (a : ℚ) / (a + b), 1] =
      Real.log (tripleHeight a b : ℝ) := by
  rw [logHeight_legendrePoint hc, logHeight_abc h]

end GaloisForLFunctions.KodairaParshinAbc
