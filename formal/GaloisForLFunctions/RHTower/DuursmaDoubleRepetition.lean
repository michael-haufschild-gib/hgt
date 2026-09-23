import GaloisForLFunctions.RHTower.IharaBlockSelector

/-!
# The first nontrivial self-dual binary code zeta block

For the binary repetition code `[2,1,2]`, the Duursma zeta polynomial is `1`.  Its direct sum with
itself is the self-dual `[4,2,2]` code with weight enumerator

`x⁴ + 2x²y² + y⁴ = (x²+y²)²`.

The defining Duursma coefficient extraction gives the unique degree-two zeta polynomial

`P(T)=(1+2T²)/3`.

Thus Duursma zeta is not multiplicative under this direct sum: the smallest assembly already
creates a genuine quadratic interaction term.  Its zeros nevertheless lie on the binary critical
circle `|T|²=1/2`.  This finite calculation is a positive baseline for the prime-syndrome code
detour: code assembly can create cross-coordinate zeta information instead of merely multiplying
disconnected local numerators.
-/

open scoped ComplexOrder

namespace GaloisForLFunctions

noncomputable section

/-- Degree-two Duursma coefficient extractor for a binary length-four code.

The coefficients `1,3,7` are the terms through degree two of
`1 / ((1-T)(1-2T))`; the three displayed summands are the degree-two coefficient
after multiplying `(a+bT+cT²)` by `(y(1-T)+xT)⁴`. -/
def binaryDegreeTwoDuursmaCoefficient
    (a b c x y : ℝ) : ℝ :=
  a * (6 * y ^ (2 : ℕ) * (x - y) ^ (2 : ℕ)) +
    (3 * a + b) * (4 * y ^ (3 : ℕ) * (x - y)) +
      (7 * a + 3 * b + c) * y ^ (4 : ℕ)

/-- `(W(x,y)-x⁴)/(2-1)` for the binary self-dual `[4,2,2]` double repetition code. -/
def doubleRepetitionWeightRemainder (x y : ℝ) : ℝ :=
  2 * x ^ (2 : ℕ) * y ^ (2 : ℕ) + y ^ (4 : ℕ)

theorem binaryDegreeTwoDuursmaCoefficient_expanded
    (a b c x y : ℝ) :
    binaryDegreeTwoDuursmaCoefficient a b c x y =
      6 * a * x ^ (2 : ℕ) * y ^ (2 : ℕ) + 4 * b * x * y ^ (3 : ℕ) +
        (a - b + c) * y ^ (4 : ℕ) := by
  unfold binaryDegreeTwoDuursmaCoefficient
  ring

/-- The polynomial `(1+2T²)/3` satisfies the defining coefficient identity. -/
theorem doubleRepetition_duursma_definingCoefficient
    (x y : ℝ) :
    binaryDegreeTwoDuursmaCoefficient (1 / 3) 0 (2 / 3) x y =
      doubleRepetitionWeightRemainder x y := by
  rw [binaryDegreeTwoDuursmaCoefficient_expanded]
  unfold doubleRepetitionWeightRemainder
  ring

/-- The defining coefficient identity uniquely determines the three zeta coefficients. -/
theorem doubleRepetition_duursma_coefficients_unique
    (a b c : ℝ) :
    (∀ x y : ℝ,
      binaryDegreeTwoDuursmaCoefficient a b c x y =
        doubleRepetitionWeightRemainder x y) ↔
      a = 1 / 3 ∧ b = 0 ∧ c = 2 / 3 := by
  constructor
  · intro h
    have h01 := h 0 1
    have h11 := h 1 1
    have h1m1 := h 1 (-1)
    rw [binaryDegreeTwoDuursmaCoefficient_expanded] at h01 h11 h1m1
    norm_num [doubleRepetitionWeightRemainder] at h01 h11 h1m1
    constructor
    · linarith
    constructor <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩
    exact doubleRepetition_duursma_definingCoefficient

/-- Zeta polynomial of the binary `[2,1,2]` repetition code. -/
def repetitionDuursmaZeta (_ : ℂ) : ℂ := 1

/-- Zeta polynomial of the binary self-dual `[4,2,2]` double repetition code. -/
def doubleRepetitionDuursmaZeta (T : ℂ) : ℂ :=
  (1 + 2 * T ^ (2 : ℕ)) / 3

theorem doubleRepetitionDuursmaZeta_eq_scaled_iharaBlock (T : ℂ) :
    doubleRepetitionDuursmaZeta T =
      (1 / 3 : ℂ) * iharaBlock 2 0 T := by
  unfold doubleRepetitionDuursmaZeta iharaBlock
  norm_num
  ring

/-- Direct sum creates a nonzero normalized quadratic interaction correction. -/
theorem doubleRepetitionDuursmaZeta_directSumInteraction (T : ℂ) :
    doubleRepetitionDuursmaZeta T =
      repetitionDuursmaZeta T * repetitionDuursmaZeta T +
        (2 / 3 : ℂ) * (T ^ (2 : ℕ) - 1) := by
  unfold doubleRepetitionDuursmaZeta repetitionDuursmaZeta
  ring

theorem doubleRepetitionDuursmaZeta_not_multiplicative :
    doubleRepetitionDuursmaZeta ≠
      fun T => repetitionDuursmaZeta T * repetitionDuursmaZeta T := by
  intro h
  have h0 := congrFun h 0
  norm_num [doubleRepetitionDuursmaZeta, repetitionDuursmaZeta] at h0

/-- The first assembled code zeta block satisfies the binary code Riemann hypothesis. -/
theorem doubleRepetitionDuursmaZeta_zero_criticalCircle
    {T : ℂ} (hT : doubleRepetitionDuursmaZeta T = 0) :
    Complex.normSq T = (2 : ℝ)⁻¹ := by
  have hblock : iharaBlock 2 0 T = 0 := by
    rw [doubleRepetitionDuursmaZeta_eq_scaled_iharaBlock] at hT
    exact (mul_eq_zero.mp hT).resolve_left (by norm_num)
  exact zerosOnCriticalCircle_of_spectral_bound (q := 2) (lambda := 0)
    (by norm_num) (by norm_num [blockSpectralBound]) T hblock

end

end GaloisForLFunctions
