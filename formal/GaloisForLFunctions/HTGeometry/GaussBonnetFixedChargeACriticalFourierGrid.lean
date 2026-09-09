import GaloisForLFunctions.QuantumAlg.Primitives.QFT
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeACriticalGramRank

/-!
Exact roots-of-unity formula for the critical Gibbs Gram derived from
arXiv:2609.00025. All dyadic grids are included, before separating aliased modes.
-/
namespace GaloisForLFunctions.HTGeometry

open QuantumAlg

noncomputable section

/-- Equally spaced inputs across the critical kernel's period π. -/
def egbFixedChargeAFourierGrid (n : ℕ) (j : Fin (2 ^ n)) : ℝ :=
  Real.pi * j.val / (2 : ℝ) ^ n

/-- The first difference character on the dyadic input grid. -/
def egbFixedChargeAFourierCharacter (n : ℕ) (i j : Fin (2 ^ n)) : ℂ :=
  omega n ^ i.val * star (omega n ^ j.val)

/-- The corpus root of unity is exactly the grid's trigonometric phase. -/
theorem egbFixedChargeAFourierCharacter_exp
    (n : ℕ) (i j : Fin (2 ^ n)) :
    egbFixedChargeAFourierCharacter n i j =
      Complex.exp ((2 * (egbFixedChargeAFourierGrid n i -
        egbFixedChargeAFourierGrid n j) : ℝ) * Complex.I) := by
  unfold egbFixedChargeAFourierCharacter omega
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, Complex.star_def,
    ← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  unfold egbFixedChargeAFourierGrid
  push_cast
  simp only [map_natCast]
  ring

/-- The character and its conjugate recover the second angular harmonic. -/
theorem egbFixedChargeAFourierCharacter_pair
    (n : ℕ) (i j : Fin (2 ^ n)) :
    egbFixedChargeAFourierCharacter n i j +
      star (egbFixedChargeAFourierCharacter n i j) =
        2 * (Real.cos (2 * (egbFixedChargeAFourierGrid n i -
          egbFixedChargeAFourierGrid n j)) : ℂ) := by
  rw [egbFixedChargeAFourierCharacter_exp, Complex.exp_ofReal_mul_I]
  simp only [star_add, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- Squared characters recover the fourth angular harmonic. -/
theorem egbFixedChargeAFourierCharacter_square_pair
    (n : ℕ) (i j : Fin (2 ^ n)) :
    egbFixedChargeAFourierCharacter n i j ^ 2 +
      star (egbFixedChargeAFourierCharacter n i j) ^ 2 =
        2 * (Real.cos (4 * (egbFixedChargeAFourierGrid n i -
          egbFixedChargeAFourierGrid n j)) : ℂ) := by
  have he : egbFixedChargeAFourierCharacter n i j ^ 2 =
      Complex.exp ((4 * (egbFixedChargeAFourierGrid n i -
        egbFixedChargeAFourierGrid n j) : ℝ) * Complex.I) := by
    rw [egbFixedChargeAFourierCharacter_exp, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [← star_pow, he, Complex.exp_ofReal_mul_I]
  simp only [star_add, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.conj_I]
  ring

/-- Five Laurent characters give every entry of the actual critical Gram matrix. -/
theorem egbFixedChargeACriticalGram_fourier_entry
    (n : ℕ) (i j : Fin (2 ^ n)) :
    egbFixedChargeACriticalGram (2 ^ n) (egbFixedChargeAFourierGrid n) i j =
      3 / 8 +
      (egbFixedChargeAFourierCharacter n i j +
        star (egbFixedChargeAFourierCharacter n i j)) / 4 +
      (egbFixedChargeAFourierCharacter n i j ^ 2 +
        star (egbFixedChargeAFourierCharacter n i j) ^ 2) / 16 := by
  rw [egbFixedChargeAFourierCharacter_pair, egbFixedChargeAFourierCharacter_square_pair]
  change (Real.cos (egbFixedChargeAFourierGrid n i -
      egbFixedChargeAFourierGrid n j) ^ 4 : ℂ) = _
  have h := congrArg (fun r : ℝ => (r : ℂ))
    (egbFixedChargeAQuarticProfile_harmonic_decomposition
      (egbFixedChargeAFourierGrid n i - egbFixedChargeAFourierGrid n j))
  norm_num only [Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_mul,
    Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one] at h
  rw [h]
  ring

end

end GaloisForLFunctions.HTGeometry
