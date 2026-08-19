import GaloisForLFunctions.HTGeometry.CompletelyPositiveSchwarz

/-!
# A unital completely positive bijection with completely positive inverse is multiplicative

If `Θ` and `Ξ` are unital completely positive maps of matrices which are mutually inverse, then
the Kadison--Schwarz inequality holds in both directions and therefore with equality:

`Θ(Xᴴ X) = Θ(X)ᴴ Θ(X)` for every `X`.

Polarising that identity in `X = A + B` and `X = A + iB` turns it into full multiplicativity,
so `Θ` is a unital star algebra automorphism of the matrix algebra.
-/

open Matrix
open scoped Matrix ComplexOrder MatrixOrder BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A positive linear map is monotone for the Loewner order. -/
theorem IsCP.monotone {Ξ : Matrix n n ℂ → Matrix n n ℂ} (hΞ : IsCP Ξ)
    {A B : Matrix n n ℂ} (hAB : A ≤ B) : Ξ A ≤ Ξ B := by
  rw [Matrix.le_iff] at hAB ⊢
  rw [← hΞ.map_sub]
  exact hΞ.pos hAB

/-- **Schwarz equality.**  Two mutually inverse unital completely positive maps saturate the
Kadison--Schwarz inequality. -/
theorem IsCP.schwarz_eq {Θ Ξ : Matrix n n ℂ → Matrix n n ℂ} (hΘ : IsCP Θ) (hΞ : IsCP Ξ)
    (hΘ1 : Θ 1 = 1) (hΞ1 : Ξ 1 = 1) (hΞΘ : ∀ X, Ξ (Θ X) = X) (hΘΞ : ∀ X, Θ (Ξ X) = X)
    (X : Matrix n n ℂ) : Θ (Xᴴ * X) = (Θ X)ᴴ * Θ X := by
  have h1 : (Θ X)ᴴ * Θ X ≤ Θ (Xᴴ * X) := hΘ.schwarz hΘ1 X
  have h2 : Ξ ((Θ X)ᴴ * Θ X) ≤ Xᴴ * X := by
    have := hΞ.monotone h1
    rwa [hΞΘ] at this
  have h3 : Xᴴ * X ≤ Ξ ((Θ X)ᴴ * Θ X) := by
    have := hΞ.schwarz hΞ1 (Θ X)
    rwa [hΞΘ] at this
  have h4 : Ξ ((Θ X)ᴴ * Θ X) = Ξ (Θ (Xᴴ * X)) := by
    rw [hΞΘ]
    exact le_antisymm h2 h3
  have hinj : Function.Injective Ξ := Function.LeftInverse.injective hΘΞ
  exact (hinj h4).symm

/-- **Multiplicativity.**  A unital completely positive bijection with completely positive
inverse is a homomorphism of the matrix algebra. -/
theorem IsCP.map_mul_of_inverse {Θ Ξ : Matrix n n ℂ → Matrix n n ℂ} (hΘ : IsCP Θ) (hΞ : IsCP Ξ)
    (hΘ1 : Θ 1 = 1) (hΞ1 : Ξ 1 = 1) (hΞΘ : ∀ X, Ξ (Θ X) = X) (hΘΞ : ∀ X, Θ (Ξ X) = X)
    (C B : Matrix n n ℂ) : Θ (C * B) = Θ C * Θ B := by
  have hstar := hΘ.schwarz_eq hΞ hΘ1 hΞ1 hΞΘ hΘΞ
  have key : ∀ A B : Matrix n n ℂ, Θ (Aᴴ * B) = (Θ A)ᴴ * Θ B := by
    intro A B
    have hA := hstar A
    have hB := hstar B
    have E1 := hstar (A + B)
    have E2 := hstar (A + Complex.I • B)
    have expand1 : (A + B)ᴴ * (A + B) = Aᴴ * A + Aᴴ * B + (Bᴴ * A + Bᴴ * B) := by
      rw [Matrix.conjTranspose_add]
      noncomm_ring
    have expand2 : (A + Complex.I • B)ᴴ * (A + Complex.I • B)
        = Aᴴ * A + Complex.I • (Aᴴ * B) + ((-Complex.I) • (Bᴴ * A) + Bᴴ * B) := by
      rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul]
      simp only [RCLike.star_def, Complex.conj_I]
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.smul_mul, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.mul_smul, smul_smul,
        show (-Complex.I) * Complex.I = 1 by rw [neg_mul, Complex.I_mul_I]; ring, one_smul]
    rw [expand1] at E1
    simp only [hΘ.map_add] at E1
    simp only [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add] at E1
    rw [hA, hB] at E1
    rw [expand2] at E2
    simp only [hΘ.map_add, hΘ.map_smul] at E2
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul,
      Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, smul_add, smul_smul, RCLike.star_def,
      Complex.conj_I] at E2
    rw [show Complex.I * -Complex.I = 1 by rw [mul_neg, Complex.I_mul_I]; ring, one_smul] at E2
    rw [hA, hB] at E2
    obtain ⟨P, hPdef⟩ : ∃ P : Matrix n n ℂ, P = Θ (Aᴴ * B) := ⟨_, rfl⟩
    obtain ⟨Q, hQdef⟩ : ∃ Q : Matrix n n ℂ, Q = Θ (Bᴴ * A) := ⟨_, rfl⟩
    obtain ⟨P', hP'def⟩ : ∃ P' : Matrix n n ℂ, P' = (Θ A)ᴴ * Θ B := ⟨_, rfl⟩
    obtain ⟨Q', hQ'def⟩ : ∃ Q' : Matrix n n ℂ, Q' = (Θ B)ᴴ * Θ A := ⟨_, rfl⟩
    obtain ⟨P₀, hP₀def⟩ : ∃ P₀ : Matrix n n ℂ, P₀ = (Θ A)ᴴ * Θ A := ⟨_, rfl⟩
    obtain ⟨Q₀, hQ₀def⟩ : ∃ Q₀ : Matrix n n ℂ, Q₀ = (Θ B)ᴴ * Θ B := ⟨_, rfl⟩
    rw [← hPdef, ← hQdef, ← hP'def, ← hQ'def, ← hP₀def, ← hQ₀def] at E1 E2
    rw [← hPdef, ← hP'def]
    have h1 : P + Q = P' + Q' := by
      have e : P₀ + (P + Q) + Q₀ = P₀ + (P' + Q') + Q₀ := by
        rw [show P₀ + (P + Q) + Q₀ = P₀ + P + (Q + Q₀) by abel,
          show P₀ + (P' + Q') + Q₀ = P₀ + Q' + (P' + Q₀) by abel]
        exact E1
      exact add_left_cancel (add_right_cancel e)
    have h2 : Complex.I • P + (-Complex.I) • Q = Complex.I • P' + (-Complex.I) • Q' := by
      have e : P₀ + (Complex.I • P + (-Complex.I) • Q) + Q₀
          = P₀ + (Complex.I • P' + (-Complex.I) • Q') + Q₀ := by
        rw [show P₀ + (Complex.I • P + (-Complex.I) • Q) + Q₀
            = P₀ + Complex.I • P + ((-Complex.I) • Q + Q₀) by module,
          show P₀ + (Complex.I • P' + (-Complex.I) • Q') + Q₀
            = P₀ + (-Complex.I) • Q' + (Complex.I • P' + Q₀) by module]
        exact E2
      exact add_left_cancel (add_right_cancel e)
    have hI1 : Complex.I • P + Complex.I • Q = Complex.I • P' + Complex.I • Q' := by
      rw [← smul_add, ← smul_add, h1]
    have h4 : ((2 : ℂ) * Complex.I) • P = ((2 : ℂ) * Complex.I) • P' := by
      have hsum := congrArg₂ (fun X Y : Matrix n n ℂ => X + Y) hI1 h2
      rw [show (Complex.I • P + Complex.I • Q) + (Complex.I • P + (-Complex.I) • Q)
            = ((2 : ℂ) * Complex.I) • P by module,
        show (Complex.I • P' + Complex.I • Q') + (Complex.I • P' + (-Complex.I) • Q')
            = ((2 : ℂ) * Complex.I) • P' by module] at hsum
      exact hsum
    exact smul_right_injective (Matrix n n ℂ)
      (mul_ne_zero (by norm_num) Complex.I_ne_zero) h4
  have := key Cᴴ B
  rwa [Matrix.conjTranspose_conjTranspose, hΘ.map_conjTranspose,
    Matrix.conjTranspose_conjTranspose] at this

end

end GaloisForLFunctions.HTGeometry
