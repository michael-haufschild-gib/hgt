import GaloisForLFunctions.RHTower.XiEntireReal

/-!
# Determinant-line trivialization is blind to the zero divisor

Over an interval a complex line bundle is trivial, so a section is a scalar function; and every
prescribed finite divisor with positive multiplicities is realized by such a section — the explicit
polynomial `∏ⱼ (λ - λⱼ)^{mⱼ}` has exactly that root multiset.  So a trivialization or null-homotopy
of the line places no restriction on the zero divisor of a section.

What does restrict it is a homotopy through nowhere-zero sections: the initial stage of such a
homotopy is nowhere zero, which is already the nonvanishing statement one wanted to prove.

Finally, a signed crossing count is not a zero count: `λ² - 1` vanishes twice, with crossing
derivatives of opposite sign summing to zero.
-/

noncomputable section

namespace RHTower

open Complex Polynomial

/-- The polynomial section realizing a prescribed finite divisor. -/
def divisorSectionPoly {n : ℕ} (lam : Fin n → ℝ) (mult : Fin n → ℕ) : Polynomial ℂ :=
  ∏ j : Fin n, (X - Polynomial.C ((lam j : ℝ) : ℂ)) ^ (mult j)

theorem divisorSectionPoly_ne_zero {n : ℕ} (lam : Fin n → ℝ) (mult : Fin n → ℕ) :
    divisorSectionPoly lam mult ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr (fun j _ => ?_)
  exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _)

/-- **The prescribed divisor is realized exactly.**  The root multiset of the section is the
prescribed divisor. -/
theorem divisorSectionPoly_roots {n : ℕ} (lam : Fin n → ℝ) (mult : Fin n → ℕ) :
    (divisorSectionPoly lam mult).roots =
      ∑ j : Fin n, (mult j) • ({((lam j : ℝ) : ℂ)} : Multiset ℂ) := by
  rw [divisorSectionPoly, Polynomial.roots_prod _ _ (divisorSectionPoly_ne_zero lam mult)]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Polynomial.roots_pow, Polynomial.roots_X_sub_C]

/-- The section as a function on the spectral parameter. -/
def divisorSection {n : ℕ} (lam : Fin n → ℝ) (mult : Fin n → ℕ) (t : ℝ) : ℂ :=
  ∏ j : Fin n, ((t : ℂ) - ((lam j : ℝ) : ℂ)) ^ (mult j)

theorem divisorSection_eq_eval {n : ℕ} (lam : Fin n → ℝ) (mult : Fin n → ℕ) (t : ℝ) :
    divisorSection lam mult t = (divisorSectionPoly lam mult).eval ((t : ℝ) : ℂ) := by
  rw [divisorSection, divisorSectionPoly, Polynomial.eval_prod]
  exact Finset.prod_congr rfl (fun j _ => by simp)

/-- **The zero set is exactly the prescribed one.** -/
theorem divisorSection_eq_zero_iff {n : ℕ} (lam : Fin n → ℝ) {mult : Fin n → ℕ}
    (hm : ∀ j, 0 < mult j) (t : ℝ) :
    divisorSection lam mult t = 0 ↔ ∃ j : Fin n, t = lam j := by
  rw [divisorSection, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨j, -, hj⟩
    refine ⟨j, ?_⟩
    have := pow_eq_zero_iff (n := mult j) (hm j).ne' |>.mp hj
    have hsub : ((t : ℝ) : ℂ) = ((lam j : ℝ) : ℂ) := by
      linear_combination this
    exact_mod_cast hsub
  · rintro ⟨j, rfl⟩
    exact ⟨j, Finset.mem_univ j, by simp [pow_eq_zero_iff (n := mult j) (hm j).ne']⟩

/-- **Triviality does not exclude zeros.**  Every prescribed finite divisor with positive
multiplicities is realized by a section of the trivial line. -/
theorem exists_section_with_prescribed_divisor {n : ℕ} (lam : Fin n → ℝ) {mult : Fin n → ℕ}
    (hm : ∀ j, 0 < mult j) :
    ∃ e : ℝ → ℂ, Continuous e ∧ (∀ t : ℝ, e t = 0 ↔ ∃ j : Fin n, t = lam j) ∧
      ∃ p : Polynomial ℂ, p ≠ 0 ∧ (∀ t : ℝ, e t = p.eval ((t : ℝ) : ℂ)) ∧
        p.roots = ∑ j : Fin n, (mult j) • ({((lam j : ℝ) : ℂ)} : Multiset ℂ) := by
  refine ⟨divisorSection lam mult, ?_, divisorSection_eq_zero_iff lam hm,
    divisorSectionPoly lam mult, divisorSectionPoly_ne_zero lam mult,
    divisorSection_eq_eval lam mult, divisorSectionPoly_roots lam mult⟩
  refine continuous_finsetProd _ (fun j _ => ?_)
  exact ((Complex.continuous_ofReal.sub continuous_const).pow _)

/-- **A nowhere-zero homotopy forces nonvanishing.**  If every stage of a homotopy of sections is
nowhere zero, then so is the initial section; a null-homotopy of the line itself says nothing. -/
theorem nonvanishing_of_nowhereZero_homotopy {H : ℝ → ℝ → ℂ}
    (hH : ∀ s t : ℝ, H s t ≠ 0) (t : ℝ) : H 0 t ≠ 0 := hH 0 t

/-! ### Cancelling crossings -/

/-- A section with two simple zeros of opposite crossing sign. -/
def crossingExample (t : ℝ) : ℝ := t ^ 2 - 1

theorem crossingExample_eq_zero_iff (t : ℝ) : crossingExample t = 0 ↔ t = 1 ∨ t = -1 := by
  rw [crossingExample, sub_eq_zero]
  constructor
  · intro h
    have hfac : (t - 1) * (t + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp hfac with h1 | h1
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> norm_num

theorem crossingExample_hasDerivAt (t : ℝ) : HasDerivAt crossingExample (2 * t) t := by
  have h : HasDerivAt (fun x : ℝ => x ^ 2 - 1) (2 * t) t := by
    simpa using ((hasDerivAt_pow 2 t).sub_const 1)
  exact h

/-- **Opposite crossing signs cancel.**  The section vanishes at two points, but its crossing
derivatives have opposite signs, so the signed crossing count is zero while both zeros remain. -/
theorem crossingExample_signs :
    crossingExample (-1) = 0 ∧ crossingExample 1 = 0 ∧
      deriv crossingExample (-1) < 0 ∧ 0 < deriv crossingExample 1 ∧
      deriv crossingExample (-1) + deriv crossingExample 1 = 0 := by
  have h1 : deriv crossingExample (-1) = -2 := by
    simpa using (crossingExample_hasDerivAt (-1)).deriv
  have h2 : deriv crossingExample 1 = 2 := by
    simpa using (crossingExample_hasDerivAt 1).deriv
  refine ⟨by norm_num [crossingExample], by norm_num [crossingExample], ?_, ?_, ?_⟩
  · rw [h1]; norm_num
  · rw [h2]; norm_num
  · rw [h1, h2]; norm_num

end RHTower
