import GaloisForLFunctions.HTGeometry.DigammaTranslatesIndependent
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Digamma and its half-translate are independent over the rational functions

The digamma recurrence `ψ(z+1) = ψ(z) + 1/z` turns a relation

  `E·ψ(z) + O·ψ(z+1/2) = P(z)/Q(z)`

into the shift-difference equation `R(z+1) - R(z) = E/z + O/(z+1/2)` for the rational function
`R = P/Q`.  Its pole part is supported on the two `ℤ`-orbits of `0` and `-1/2`, which differ by a
half-integer, so the two-orbit difference brick forces both residues to vanish.

Consequently `ψ(z)` and `ψ(z+1/2)` are linearly independent over `ℂ(z)`: no `ℂ`-combination of the
two is a rational function unless it is trivial.  This is the independence of the two digamma modes
that the archimedean factor of the completed zeta function carries, one for each parity class of
integer shifts.

The hypothesis is allowed to fail on a finite exceptional set, and the quotient need not be in lowest
terms: passing to the reduced fraction only enlarges that exceptional set.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- **Half-translate digamma independence, cofinite form.** If a `ℂ`-combination of `ψ(z)` and
`ψ(z+1/2)` agrees with a rational function in lowest terms on a right half-plane off a finite
exceptional set and off the denominator's zeros, both coefficients vanish. -/
theorem digamma_half_translate_independent_of_cofinite {E O : ℂ} {P Q : Polynomial ℂ}
    (hQ : Q ≠ 0) (hco : IsCoprime P Q) {T : Set ℂ} (hT : T.Finite)
    (h : ∀ z : ℂ, 0 < z.re → z ∉ T → Q.eval z ≠ 0 →
      E * Complex.digamma z + O * Complex.digamma (z + 1 / 2) = P.eval z / Q.eval z) :
    E = 0 ∧ O = 0 := by
  classical
  have hhalf : ∀ m : ℤ, ((1 : ℂ) / 2) ≠ (m : ℂ) := by
    intro m hc
    have hre := congrArg Complex.re hc
    have h2 : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
    rw [h2, Complex.intCast_re] at hre
    have hint : (2 * m : ℤ) = 1 := by
      have : (2 : ℝ) * (m : ℝ) = 1 := by linarith
      exact_mod_cast this
    omega
  set a : Fin 2 → ℂ := ![0, 1 / 2] with ha
  set Ev : Fin 2 → ℂ := ![E, O] with hEv
  have ha0 : a 0 = 0 := by simp [ha]
  have ha1 : a 1 = 1 / 2 := by simp [ha]
  have hfin2 : ∀ i : Fin 2, i = 0 ∨ i = 1 := by
    intro i
    rcases i with ⟨v, hv⟩
    interval_cases v
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hsep : ∀ i j : Fin 2, i ≠ j → ∀ m : ℤ, a i - a j ≠ (m : ℂ) := by
    intro i j hij m hc
    rcases hfin2 i with hi | hi <;> rcases hfin2 j with hj | hj <;> subst hi <;> subst hj
    · exact hij rfl
    · rw [ha0, ha1] at hc
      exact hhalf (-m) (by push_cast; linear_combination -hc)
    · rw [ha0, ha1] at hc
      exact hhalf m (by linear_combination hc)
    · exact hij rfl
  have hmain : ∀ z : ℂ, (∀ i, 0 < (z + a i).re) → z ∉ T → Q.eval z ≠ 0 →
      ∑ i, Ev i * Complex.digamma (z + a i) = P.eval z / Q.eval z := by
    intro z hz hzT hQz
    have hz0 : 0 < z.re := by
      have := hz 0
      rwa [ha0, add_zero] at this
    rw [Fin.sum_univ_two, ha0, ha1, add_zero]
    have hE0 : Ev 0 = E := by simp [hEv]
    have hE1 : Ev 1 = O := by simp [hEv]
    rw [hE0, hE1]
    exact h z hz0 hzT hQz
  have hkey := digamma_translates_independent hsep hQ hco hT hmain
  refine ⟨?_, ?_⟩
  · have := hkey 0
    simpa [hEv] using this
  · have := hkey 1
    simpa [hEv] using this

/-- **Half-translate digamma independence.** -/
theorem digamma_half_translate_independent {E O : ℂ} {P Q : Polynomial ℂ}
    (hQ : Q ≠ 0) (hco : IsCoprime P Q)
    (h : ∀ z : ℂ, 0 < z.re → Q.eval z ≠ 0 →
      E * Complex.digamma z + O * Complex.digamma (z + 1 / 2) = P.eval z / Q.eval z) :
    E = 0 ∧ O = 0 :=
  digamma_half_translate_independent_of_cofinite hQ hco Set.finite_empty
    fun z hz _ hQz => h z hz hQz

/-- **Half-translate digamma independence for an arbitrary quotient.** The fraction need not be in
lowest terms and the identity may fail on a finite exceptional set. -/
theorem digamma_half_translate_independent_of_quotient {E O : ℂ} {P Q : Polynomial ℂ}
    (hQ : Q ≠ 0) {T : Set ℂ} (hT : T.Finite)
    (h : ∀ z : ℂ, 0 < z.re → z ∉ T → Q.eval z ≠ 0 →
      E * Complex.digamma z + O * Complex.digamma (z + 1 / 2) = P.eval z / Q.eval z) :
    E = 0 ∧ O = 0 := by
  classical
  set R : RatFunc ℂ :=
    algebraMap (Polynomial ℂ) (RatFunc ℂ) P / algebraMap (Polynomial ℂ) (RatFunc ℂ) Q with hR_def
  have hQK : algebraMap (Polynomial ℂ) (RatFunc ℂ) Q ≠ 0 := fun h0 =>
    hQ (RatFunc.algebraMap_injective ℂ (by rw [h0, map_zero]))
  have hdenK : algebraMap (Polynomial ℂ) (RatFunc ℂ) R.denom ≠ 0 := fun h0 =>
    R.denom_ne_zero (RatFunc.algebraMap_injective ℂ (by rw [h0, map_zero]))
  have hcrossK : algebraMap (Polynomial ℂ) (RatFunc ℂ) (R.num * Q)
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (P * R.denom) := by
    rw [map_mul, map_mul]
    have hnd := RatFunc.num_div_denom R
    rw [hR_def] at hnd
    rw [div_eq_div_iff hdenK hQK] at hnd
    linear_combination hnd
  have hcross : R.num * Q = P * R.denom := RatFunc.algebraMap_injective ℂ hcrossK
  refine digamma_half_translate_independent_of_cofinite R.denom_ne_zero R.isCoprime_num_denom
    (T := T ∪ {z : ℂ | Q.eval z = 0}) (hT.union (Polynomial.finite_setOf_isRoot hQ)) ?_
  intro z hz hzT hden
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hzT
  have hQz : Q.eval z ≠ 0 := hzT.2
  have hval := h z hz hzT.1 hQz
  rw [hval]
  have := congrArg (Polynomial.eval z) hcross
  simp only [Polynomial.eval_mul] at this
  field_simp
  linear_combination -this

end GaloisForLFunctions.HTGeometry
