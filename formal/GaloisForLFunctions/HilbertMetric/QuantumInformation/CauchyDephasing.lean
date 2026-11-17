import GaloisForLFunctions.HilbertMetric.QuantumInformation.CauchyJordanInverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Cauchy dephasing with a sharp fixed algebra

Normalizing inverse Jordan averaging by the square roots of its positive
rates gives the Schur coherence kernel `sech((s-t)/2)`. The resulting map
preserves positivity in every auxiliary dimension, the identity, and trace.
It fixes precisely the matrix blocks with equal logarithmic rates.
-/

noncomputable section
open Matrix
open scoped ComplexOrder BigOperators
namespace GaloisForLFunctions.HilbertMetric.CauchyDephasing
open CauchyJordan

/-- Normalized Cauchy coherence between two logarithmic rates. -/
def coherence (s t : ℝ) : ℝ :=
  2 * Real.exp (s / 2) * Real.exp (t / 2) / (Real.exp s + Real.exp t)

private theorem half_exp_sq (s : ℝ) : Real.exp (s / 2) ^ 2 = Real.exp s := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

theorem coherence_pos (s t : ℝ) : 0 < coherence s t := by
  unfold coherence
  positivity

theorem coherence_symm (s t : ℝ) : coherence s t = coherence t s := by
  unfold coherence
  rw [add_comm (Real.exp s)]
  ring

theorem coherence_defect (s t : ℝ) :
    1 - coherence s t = (Real.exp (s / 2) - Real.exp (t / 2)) ^ 2 /
      (Real.exp s + Real.exp t) := by
  unfold coherence
  rw [← half_exp_sq s, ← half_exp_sq t]
  have hd : Real.exp (s / 2) ^ 2 + Real.exp (t / 2) ^ 2 ≠ 0 := by positivity
  field_simp [hd]
  ring

theorem coherence_le_one (s t : ℝ) : coherence s t ≤ 1 := by
  have h := div_nonneg (sq_nonneg (Real.exp (s / 2) - Real.exp (t / 2)))
    (add_pos (Real.exp_pos s) (Real.exp_pos t)).le
  rw [← coherence_defect] at h
  exact sub_nonneg.mp h

theorem coherence_self (s : ℝ) : coherence s s = 1 := by
  have h := coherence_defect s s
  rw [sub_self, zero_pow (by norm_num), zero_div] at h
  exact (sub_eq_zero.mp h).symm

theorem coherence_eq_one_iff (s t : ℝ) : coherence s t = 1 ↔ s = t := by
  constructor
  · intro h
    have hd := coherence_defect s t
    rw [h, sub_self] at hd
    have hs : (Real.exp (s / 2) - Real.exp (t / 2)) ^ 2 = 0 :=
      (div_eq_zero_iff).mp hd.symm |>.resolve_right (add_pos (Real.exp_pos s) (Real.exp_pos t)).ne'
    have he := Real.exp_injective (sub_eq_zero.mp (sq_eq_zero_iff.mp hs))
    linarith only [he]
  · rintro rfl
    exact coherence_self s

theorem coherence_eq_cosh_inv (s t : ℝ) : coherence s t = (Real.cosh ((s - t) / 2))⁻¹ := by
  have he1 : Real.exp ((s - t) / 2) = Real.exp (s / 2) / Real.exp (t / 2) := by
    rw [show (s - t) / 2 = s / 2 - t / 2 by ring, Real.exp_sub]
  have he2 : Real.exp (-((s - t) / 2)) = Real.exp (t / 2) / Real.exp (s / 2) := by
    rw [show -((s - t) / 2) = t / 2 - s / 2 by ring, Real.exp_sub]
  rw [Real.cosh_eq, he1, he2]
  unfold coherence
  rw [← half_exp_sq s, ← half_exp_sq t]
  have hd : Real.exp (s / 2) ^ 2 + Real.exp (t / 2) ^ 2 ≠ 0 := by positivity
  field_simp [Real.exp_ne_zero, hd]


/-- Square-root rate normalization. -/
def rateDiagonal {n : ℕ} (r : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  diagonal fun i => (Real.exp (r i / 2) : ℂ)

private theorem rateDiagonal_conjTranspose {n : ℕ} (r : Fin n → ℝ) :
    (rateDiagonal r)ᴴ = rateDiagonal r := by
  ext i j
  by_cases h : i = j
  · subst j
    simp only [rateDiagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply_eq,
      Complex.star_def, Complex.conj_ofReal]
  · simp only [rateDiagonal, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
      if_neg h, if_neg (Ne.symm h), star_zero]

/-- The correlation matrix of the Cauchy channel. -/
def symbol {n : ℕ} (r : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (coherence (r i) (r j) : ℂ)

/-- The normalized Cauchy correlation matrix is positive in every dimension. -/
theorem symbol_posSemidef {n : ℕ} (r : Fin n → ℝ) : (symbol r).PosSemidef := by
  have heq : symbol r =
      (rateDiagonal r)ᴴ * ((2 : ℂ) • cauchySymbol r) * rateDiagonal r := by
    rw [rateDiagonal_conjTranspose]
    ext i j
    rw [rateDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul]
    change ((2 * Real.exp (r i / 2) * Real.exp (r j / 2) /
      (Real.exp (r i) + Real.exp (r j)) : ℝ) : ℂ) =
      (Real.exp (r i / 2) : ℂ) *
        (2 * ((1 / (Real.exp (r i) + Real.exp (r j)) : ℝ) : ℂ)) *
          (Real.exp (r j / 2) : ℂ)
    simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_add,
      Complex.ofReal_ofNat, Complex.ofReal_one]
    ring
  rw [heq]
  exact ((cauchySymbol_posSemidef r).smul (by norm_num : 0 ≤ (2 : ℂ))).conjTranspose_mul_mul_same _

/-- The trace-preserving normalization of inverse Jordan averaging. -/
def channel {n : ℕ} (r : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := fun i j => (coherence (r i) (r j) : ℂ) * A i j

/-- Exact identification with the positive diagonal normalization of inverse Jordan averaging. -/
theorem channel_eq_inverseJordan {n : ℕ} (r : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    channel r A = rateDiagonal r * inverseJordan r A * rateDiagonal r := by
  ext i j
  simp only [channel, coherence, rateDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul,
    inverseJordan, rate, Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_add,
    Complex.ofReal_ofNat]
  ring

/-- The normalized inverse is a Schur multiplier by the coherence matrix. -/
theorem channel_eq_hadamard {n : ℕ} (r : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) : channel r A = A ⊙ symbol r := by
  ext i j
  exact mul_comm _ _

/-- Every Gram input remains positive under the normalized channel. -/
theorem channel_gram_posSemidef {n m : ℕ} (r : Fin n → ℝ)
    (B : Matrix (Fin m) (Fin n) ℂ) : (channel r (Bᴴ * B)).PosSemidef := by
  rw [channel_eq_hadamard]
  exact (posSemidef_conjTranspose_mul_self B).hadamard (symbol_posSemidef r)

/-- The channel fixes the identity exactly. -/
theorem channel_one {n : ℕ} (r : Fin n → ℝ) : channel r 1 = 1 := by
  ext i j
  by_cases h : i = j
  · subst j
    simp only [channel, coherence_self, Complex.ofReal_one, one_mul]
  · simp only [channel, Matrix.one_apply_ne h, mul_zero]

/-- Every matrix retains its trace, including indefinite and non-Hermitian inputs. -/
theorem trace_channel {n : ℕ} (r : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) : trace (channel r A) = trace A := by
  simp only [Matrix.trace, Matrix.diag_apply, channel, coherence_self,
    Complex.ofReal_one, one_mul]

/-- Fixed matrices have no coefficients between unequal logarithmic rates. -/
theorem channel_fixed_iff {n : ℕ} (r : Fin n → ℝ)
    (A : Matrix (Fin n) (Fin n) ℂ) :
    channel r A = A ↔ ∀ i j, r i ≠ r j → A i j = 0 := by
  constructor
  · intro h i j hij
    have hc := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M i j) h
    change (coherence (r i) (r j) : ℂ) * A i j = A i j at hc
    have hp : ((coherence (r i) (r j) : ℂ) - 1) * A i j = 0 := by
      linear_combination hc
    rcases mul_eq_zero.mp hp with hq | hA
    · have hreal : coherence (r i) (r j) = 1 := by
        exact_mod_cast sub_eq_zero.mp hq
      exact (hij ((coherence_eq_one_iff _ _).mp hreal)).elim
    · exact hA
  · intro h
    ext i j
    by_cases hij : r i = r j
    · simp only [channel, hij, coherence_self, Complex.ofReal_one, one_mul]
    · simp only [channel, h i j hij, mul_zero]

/-- The channel acts on the first tensor factor of an arbitrary auxiliary system. -/
def amplifiedChannel {n m : ℕ} (r : Fin n → ℝ)
    (A : Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ) :
    Matrix (Fin n × Fin m) (Fin n × Fin m) ℂ :=
  fun i j => (coherence (r i.1) (r j.1) : ℂ) * A i j

/-- Positivity holds in every auxiliary dimension, with an explicit Schur Gram proof. -/
theorem amplifiedChannel_gram_posSemidef {n m k : ℕ} (r : Fin n → ℝ)
    (B : Matrix (Fin k) (Fin n × Fin m) ℂ) :
    (amplifiedChannel r (Bᴴ * B)).PosSemidef := by
  have heq : amplifiedChannel r (Bᴴ * B) =
      (Bᴴ * B) ⊙ (symbol r).submatrix Prod.fst Prod.fst := by
    ext i j
    exact mul_comm _ _
  rw [heq]
  exact (posSemidef_conjTranspose_mul_self B).hadamard ((symbol_posSemidef r).submatrix Prod.fst)

#print axioms coherence_defect
#print axioms coherence_eq_cosh_inv
#print axioms symbol_posSemidef
#print axioms channel_eq_inverseJordan
#print axioms channel_gram_posSemidef
#print axioms channel_one
#print axioms trace_channel
#print axioms channel_fixed_iff
#print axioms amplifiedChannel_gram_posSemidef

end GaloisForLFunctions.HilbertMetric.CauchyDephasing
