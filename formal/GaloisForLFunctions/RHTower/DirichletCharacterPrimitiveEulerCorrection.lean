import GaloisForLFunctions.RHTower.DirichletCharacterPrimitiveDepletion
import GaloisForLFunctions.RHTower.Mollifier

/-!
# Finite Euler correction for primitive conductor reduction

This file proves a coefficientwise finite convolution identity.  It transports an
imprimitive nonprincipal Dirichlet character at level `n + 1` to its primitive
conductor character, with the missing Euler factors represented by a finite
Möbius correction supported on divisors of `n + 1`.

It does not assert an infinite Euler-product identity, an analytic continuation,
or a statement about zeros of an `L`-function.
-/

open ArithmeticFunction LSeries

noncomputable section

namespace RHTower

/-- Finite Möbius correction removing the prime factors of the original level. -/
noncomputable def cglPrimitiveEulerCorrection
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) : ℕ → ℂ :=
  fun d => if d ∈ (n + 1).divisors then
    (moebius d : ℂ) * (cglPrimitiveCharacterReduction n χ).primitiveCharacter d else 0

private theorem cgl_divisors_filter_eq_gcd_divisors
    (n q : ℕ) (hn : n ≠ 0) (hq : q ≠ 0) :
    n.divisors.filter (fun d => d ∈ q.divisors) = (n.gcd q).divisors := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hdn, _⟩, ⟨hdq, _⟩⟩
    exact ⟨Nat.dvd_gcd hdn hdq, (Nat.gcd_pos_of_pos_left q (Nat.pos_of_ne_zero hn)).ne'⟩
  · rintro ⟨hdgcd, _⟩
    exact ⟨⟨hdgcd.trans (Nat.gcd_dvd_left _ _), hn⟩,
      ⟨hdgcd.trans (Nat.gcd_dvd_right _ _), hq⟩⟩

/-- The finite correction convolved with the primitive character is exactly its
level-depletion to the original modulus. -/
theorem cglPrimitiveEulerCorrection_convolution_eq_levelDepletion
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (m : ℕ) :
    LSeries.convolution (cglPrimitiveEulerCorrection n χ)
      (fun k => (cglPrimitiveCharacterReduction n χ).primitiveCharacter k) m =
      if m.Coprime (n + 1) then
        (cglPrimitiveCharacterReduction n χ).primitiveCharacter m else 0 := by
  simp only [LSeries.convolution_def]
  by_cases hmzero : m = 0
  · subst hmzero
    by_cases hnzero : n = 0
    · subst hnzero
      exfalso
      exact χ.2 (DirichletCharacter.level_one χ.1)
    · simp [cglPrimitiveEulerCorrection, hnzero]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hmzero
    rw [Nat.sum_divisorsAntidiagonal
      (fun d e => cglPrimitiveEulerCorrection n χ d *
        (cglPrimitiveCharacterReduction n χ).primitiveCharacter e)]
    have hfactor :
        (∑ d ∈ m.divisors,
          (cglPrimitiveEulerCorrection n χ d) *
            (cglPrimitiveCharacterReduction n χ).primitiveCharacter (m / d)) =
          (∑ d ∈ m.divisors,
            if d ∈ (n + 1).divisors then (moebius d : ℂ) else 0) *
            (cglPrimitiveCharacterReduction n χ).primitiveCharacter m := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      have hdm : d ∣ m := Nat.dvd_of_mem_divisors hd
      rw [cglPrimitiveEulerCorrection]
      by_cases hdq : d ∈ (n + 1).divisors
      · rw [if_pos hdq]
        have hchar :
            (cglPrimitiveCharacterReduction n χ).primitiveCharacter d *
              (cglPrimitiveCharacterReduction n χ).primitiveCharacter (m / d) =
              (cglPrimitiveCharacterReduction n χ).primitiveCharacter m := by
          rw [← map_mul]
          have hmul :
              (d : ZMod (cglPrimitiveCharacterReduction n χ).conductor) *
                (m / d : ZMod (cglPrimitiveCharacterReduction n χ).conductor) =
                (m : ZMod (cglPrimitiveCharacterReduction n χ).conductor) := by
            rw [← Nat.cast_mul, Nat.mul_div_cancel' hdm]
          rw [hmul]
        calc
          (moebius d : ℂ) * (cglPrimitiveCharacterReduction n χ).primitiveCharacter d *
              (cglPrimitiveCharacterReduction n χ).primitiveCharacter (m / d) =
            (moebius d : ℂ) *
              ((cglPrimitiveCharacterReduction n χ).primitiveCharacter d *
                (cglPrimitiveCharacterReduction n χ).primitiveCharacter (m / d)) := by ring
          _ = (moebius d : ℂ) * (cglPrimitiveCharacterReduction n χ).primitiveCharacter m := by
            rw [hchar]
          _ = (if d ∈ (n + 1).divisors then (moebius d : ℂ) else 0) *
              (cglPrimitiveCharacterReduction n χ).primitiveCharacter m := by
            simp [hdq]
      · rw [if_neg hdq]
        simp [hdq]
    rw [hfactor]
    rw [← Finset.sum_filter]
    rw [cgl_divisors_filter_eq_gcd_divisors m (n + 1) hmzero (Nat.succ_ne_zero n)]
    have hmob : (∑ d ∈ (m.gcd (n + 1)).divisors, (moebius d : ℂ)) =
        if m.gcd (n + 1) = 1 then 1 else 0 := by
      exact_mod_cast sum_moebius_divisors (m.gcd (n + 1))
    rw [hmob]
    by_cases hcop : m.Coprime (n + 1)
    · have hgcd : m.gcd (n + 1) = 1 := Nat.coprime_iff_gcd_eq_one.mpr hcop
      simp [hgcd]
    · have hgcd : m.gcd (n + 1) ≠ 1 := by
        intro hgcd
        exact hcop (Nat.coprime_iff_gcd_eq_one.mpr hgcd)
      simp [hgcd]

/-- The finite primitive Euler correction recovers the original character
coefficientwise. -/
theorem cglPrimitiveEulerCorrection_convolution_eq_input
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (m : ℕ) :
    LSeries.convolution (cglPrimitiveEulerCorrection n χ)
      (fun k => (cglPrimitiveCharacterReduction n χ).primitiveCharacter k) m = χ.1 m := by
  rw [cglPrimitiveEulerCorrection_convolution_eq_levelDepletion,
    cglPrimitiveCharacterReduction_apply_eq_levelDepletion]

end RHTower
