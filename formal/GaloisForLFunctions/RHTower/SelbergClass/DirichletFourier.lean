import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Finite Fourier inversion over Dirichlet characters

This is the exact Fourier core of Kaczorowski--Perelli's additive-phase decomposition.  It expands
arbitrary complex data restricted to the units of `ZMod D` in the complete family of Dirichlet
characters modulo `D`.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Fourier coefficient of `f` against the inverse of a Dirichlet character. -/
def dirichletCharacterFourierCoeff {D : ℕ} [NeZero D] (f : ZMod D → ℂ)
    (χ : DirichletCharacter ℂ D) : ℂ :=
  ∑ x : ZMod D, χ⁻¹ x * f x

private lemma ringInverse_eq_zmodInv_of_isUnit {D : ℕ} {x : ZMod D} (hx : IsUnit x) :
    Ring.inverse x = x⁻¹ := by
  rcases hx with ⟨u, rfl⟩
  rw [Ring.inverse_of_isUnit u.isUnit]
  simp

/-- Unnormalized finite Fourier inversion over all Dirichlet characters modulo `D`. -/
theorem dirichletCharacterFourier_sum_eq {D : ℕ} [NeZero D] (f : ZMod D → ℂ)
    (n : ZMod D) :
    ∑ χ : DirichletCharacter ℂ D, dirichletCharacterFourierCoeff f χ * χ n =
      (D.totient : ℂ) * ((1 : DirichletCharacter ℂ D) n * f n) := by
  classical
  by_cases hn : IsUnit n
  · rw [MulChar.one_apply hn, one_mul]
    calc
      ∑ χ : DirichletCharacter ℂ D, dirichletCharacterFourierCoeff f χ * χ n =
          ∑ χ : DirichletCharacter ℂ D, ∑ x : ZMod D, (χ⁻¹ x * f x) * χ n := by
            simp only [dirichletCharacterFourierCoeff, Finset.sum_mul]
      _ = ∑ x : ZMod D, ∑ χ : DirichletCharacter ℂ D, (χ⁻¹ x * f x) * χ n :=
        Finset.sum_comm
      _ = ∑ x : ZMod D, f x * ∑ χ : DirichletCharacter ℂ D, χ⁻¹ x * χ n := by
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro χ _
        ring
      _ = f n * ∑ χ : DirichletCharacter ℂ D, χ⁻¹ n * χ n := by
        apply Finset.sum_eq_single n
        · intro x _ hxn
          by_cases hx : IsUnit x
          · simp_rw [MulChar.inv_apply]
            rw [ringInverse_eq_zmodInv_of_isUnit hx]
            rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hx n, if_neg hxn]
            simp
          · simp [MulChar.map_nonunit _ hx]
        · intro hnmem
          exact (hnmem (Finset.mem_univ n)).elim
      _ = f n * (D.totient : ℂ) := by
        simp_rw [MulChar.inv_apply]
        rw [ringInverse_eq_zmodInv_of_isUnit hn]
        rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hn n, if_pos rfl]
      _ = (D.totient : ℂ) * f n := mul_comm _ _
  · simp [MulChar.map_nonunit _ hn]

/-- Exact finite Fourier inversion for data restricted to reduced residue classes modulo `D`. -/
theorem dirichletCharacterFourier_expansion {D : ℕ} [NeZero D] (f : ZMod D → ℂ)
    (n : ZMod D) :
    (1 : DirichletCharacter ℂ D) n * f n =
      (D.totient : ℂ)⁻¹ *
        ∑ χ : DirichletCharacter ℂ D, dirichletCharacterFourierCoeff f χ * χ n := by
  rw [dirichletCharacterFourier_sum_eq]
  have hD : (D.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne D))).ne'
  field_simp

end


end RHTower
