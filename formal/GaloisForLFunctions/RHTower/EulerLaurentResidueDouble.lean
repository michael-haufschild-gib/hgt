import GaloisForLFunctions.HTGeometry.ProjectiveHorizonLaurentResidueSeam

/-!
# The source-frequency Laurent residue double of the Euler clock

Centering the Euler spectral coordinate at the functional-equation fixed point turns every
Dirichlet character into a real-frequency mode `exp (-lambda z)`. Reflection sends `lambda` to
`-lambda` and therefore supplies the opposite Laurent half from the source.

This file lifts the integer-degree Laurent residue seam from HTGeometry to arbitrary real Euler
frequencies. Both frequency half-lines are residue-isotropic, every nonzero opposite pair has exact
seam weight `lambda`, and the matrix-valued lift obeys the Lie `2`-cocycle identity. In particular,
the prime mode `log p` has a nonzero source-reflected seam of exact weight `log p`.
-/

namespace GaloisForLFunctions

noncomputable section

/-- The centered Euler character with real source frequency `lambda`. -/
def eulerLaurentCharacter (lambda : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(lambda : ℂ) * z)

/-- Multiplication of centered Euler characters adds their real source frequencies. -/
theorem eulerLaurentCharacter_add (lambda mu : ℝ) (z : ℂ) :
    eulerLaurentCharacter (lambda + mu) z =
      eulerLaurentCharacter lambda z * eulerLaurentCharacter mu z := by
  simp only [eulerLaurentCharacter]
  rw [← Complex.exp_add]
  apply congrArg Complex.exp
  push_cast
  ring

/-- Functional-equation reflection supplies the opposite real-frequency mode. -/
theorem eulerLaurentCharacter_reflection (lambda : ℝ) (z : ℂ) :
    eulerLaurentCharacter lambda (-z) = eulerLaurentCharacter (-lambda) z := by
  simp only [eulerLaurentCharacter]
  apply congrArg Complex.exp
  push_cast
  ring

/-- The reflected character is the multiplicative inverse of the original character. -/
theorem eulerLaurentCharacter_reflection_eq_inv (lambda : ℝ) (z : ℂ) :
    eulerLaurentCharacter lambda (-z) = (eulerLaurentCharacter lambda z)⁻¹ := by
  rw [eulerLaurentCharacter_reflection]
  simp only [eulerLaurentCharacter]
  rw [← Complex.exp_neg]
  apply congrArg Complex.exp
  push_cast
  ring

/-- Constant-term residue weight for modes `exp (-lambda z)` and `exp (-mu z)`. -/
def eulerLaurentResidueWeight (lambda mu : ℝ) : ℝ :=
  if lambda + mu = 0 then -mu else 0

/-- The source-frequency residue weight is alternating. -/
theorem eulerLaurentResidueWeight_swap (lambda mu : ℝ) :
    eulerLaurentResidueWeight lambda mu = -eulerLaurentResidueWeight mu lambda := by
  by_cases h : lambda + mu = 0
  · have h' : mu + lambda = 0 := by linarith
    simp [eulerLaurentResidueWeight, h, h']
    linarith
  · have h' : mu + lambda ≠ 0 := by
      intro hzero
      apply h
      linarith
    simp [eulerLaurentResidueWeight, h, h']

/-- The nonnegative Euler-frequency half is residue-isotropic. -/
theorem eulerLaurentResidueWeight_nonneg_zero
    (lambda mu : ℝ) (hlambda : 0 ≤ lambda) (hmu : 0 ≤ mu) :
    eulerLaurentResidueWeight lambda mu = 0 := by
  by_cases h : lambda + mu = 0
  · have hlambda0 : lambda = 0 := by linarith
    have hmu0 : mu = 0 := by linarith
    simp [eulerLaurentResidueWeight, hlambda0, hmu0]
  · simp [eulerLaurentResidueWeight, h]

/-- The nonpositive reflected Euler-frequency half is residue-isotropic. -/
theorem eulerLaurentResidueWeight_nonpos_zero
    (lambda mu : ℝ) (hlambda : lambda ≤ 0) (hmu : mu ≤ 0) :
    eulerLaurentResidueWeight lambda mu = 0 := by
  by_cases h : lambda + mu = 0
  · have hlambda0 : lambda = 0 := by linarith
    have hmu0 : mu = 0 := by linarith
    simp [eulerLaurentResidueWeight, hlambda0, hmu0]
  · simp [eulerLaurentResidueWeight, h]

/-- Every mode and its reflected opposite have exact seam weight `lambda`. -/
@[simp]
theorem eulerLaurentResidueWeight_opposite (lambda : ℝ) :
    eulerLaurentResidueWeight lambda (-lambda) = lambda := by
  simp [eulerLaurentResidueWeight]

/-- Every nonzero source frequency has a nontrivial reflected seam. -/
theorem eulerLaurentResidueWeight_opposite_ne_zero
    {lambda : ℝ} (hlambda : lambda ≠ 0) :
    eulerLaurentResidueWeight lambda (-lambda) ≠ 0 := by
  simpa using hlambda

/-- Every prime contributes a strictly positive opposite-mode residue weight. -/
theorem eulerPrimeLaurentResidueWeight_pos (p : Nat.Primes) :
    0 < eulerLaurentResidueWeight (Real.log (p : ℝ)) (-Real.log (p : ℝ)) := by
  rw [eulerLaurentResidueWeight_opposite]
  exact Real.log_pos (by exact_mod_cast p.property.one_lt)

/-- The `A₂` current-algebra lift of the centered Euler residue weight. -/
def eulerA2LaurentResiduePairing
    (lambda mu : ℝ) (A B : Matrix (Fin 3) (Fin 3) ℂ) : ℂ :=
  (eulerLaurentResidueWeight lambda mu : ℂ) * Matrix.trace (A * B)

/-- The source-frequency `A₂` residue pairing is alternating. -/
theorem eulerA2LaurentResiduePairing_swap
    (lambda mu : ℝ) (A B : Matrix (Fin 3) (Fin 3) ℂ) :
    eulerA2LaurentResiduePairing lambda mu A B =
      -eulerA2LaurentResiduePairing mu lambda B A := by
  rw [eulerA2LaurentResiduePairing, eulerA2LaurentResiduePairing,
    eulerLaurentResidueWeight_swap, Matrix.trace_mul_comm]
  push_cast
  ring

/-- The nonnegative `A₂` Euler-current half is residue-isotropic. -/
theorem eulerA2LaurentResiduePairing_nonneg_zero
    (lambda mu : ℝ) (A B : Matrix (Fin 3) (Fin 3) ℂ)
    (hlambda : 0 ≤ lambda) (hmu : 0 ≤ mu) :
    eulerA2LaurentResiduePairing lambda mu A B = 0 := by
  rw [eulerA2LaurentResiduePairing,
    eulerLaurentResidueWeight_nonneg_zero lambda mu hlambda hmu]
  simp

/-- The nonpositive reflected `A₂` Euler-current half is residue-isotropic. -/
theorem eulerA2LaurentResiduePairing_nonpos_zero
    (lambda mu : ℝ) (A B : Matrix (Fin 3) (Fin 3) ℂ)
    (hlambda : lambda ≤ 0) (hmu : mu ≤ 0) :
    eulerA2LaurentResiduePairing lambda mu A B = 0 := by
  rw [eulerA2LaurentResiduePairing,
    eulerLaurentResidueWeight_nonpos_zero lambda mu hlambda hmu]
  simp

/-- The first opposite Chevalley-root pair has exact real-frequency seam `lambda`. -/
theorem eulerA2LaurentResiduePairing_opposite_E01 (lambda : ℝ) :
    eulerA2LaurentResiduePairing lambda (-lambda)
        (a2ConstantE01 ℂ) (a2ConstantE10 ℂ) = (lambda : ℂ) := by
  simp [eulerA2LaurentResiduePairing, a2ConstantE01, a2ConstantE10,
    Matrix.trace, Fin.sum_univ_succ]

/-- Every prime has a nonzero source-reflected seam on an opposite `A₂` root pair. -/
theorem eulerPrimeA2LaurentResiduePairing_opposite_E01_ne_zero
    (p : Nat.Primes) :
    eulerA2LaurentResiduePairing (Real.log (p : ℝ)) (-Real.log (p : ℝ))
        (a2ConstantE01 ℂ) (a2ConstantE10 ℂ) ≠ 0 := by
  rw [eulerA2LaurentResiduePairing_opposite_E01]
  exact Complex.ofReal_ne_zero.mpr
    (Real.log_pos (by exact_mod_cast p.property.one_lt)).ne'

/-- Raw current-mode coefficient whose residue norm matches one Fisher excitation. -/
def eulerLaurentHalfDensityAmplitude (epsilon lambda q : ℝ) : ℝ :=
  2 * epsilon * Real.sqrt lambda * Real.sqrt q / (1 + q)

/-- The one-prime Fisher energy in source frequency and occupation coordinates. -/
def eulerFisherModeEnergy (epsilon lambda q : ℝ) : ℝ :=
  4 * epsilon ^ (2 : ℕ) * lambda ^ (2 : ℕ) * q / (1 + q) ^ (2 : ℕ)

/-- The source half-density turns the frequency-weighted residue norm into the Fisher norm. -/
theorem eulerLaurentResidue_halfDensity_isometry
    (epsilon lambda q : ℝ) (hlambda : 0 ≤ lambda) (hq : 0 ≤ q) :
    lambda * eulerLaurentHalfDensityAmplitude epsilon lambda q ^ (2 : ℕ) =
      eulerFisherModeEnergy epsilon lambda q := by
  have hden : 1 + q ≠ 0 := by linarith
  rw [eulerLaurentHalfDensityAmplitude, eulerFisherModeEnergy, div_pow]
  field_simp
  rw [Real.sq_sqrt hlambda, Real.sq_sqrt hq]
  ring

private theorem trace_lie_mul_cyclic_complex
    (A B C : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix.trace (⁅A, B⁆ * C) = Matrix.trace (⁅B, C⁆ * A) := by
  simp only [LieRing.of_associative_ring_bracket, sub_mul, Matrix.trace_sub]
  have hpos : Matrix.trace ((A * B) * C) = Matrix.trace ((B * C) * A) := by
    rw [Matrix.mul_assoc]
    exact Matrix.trace_mul_comm A (B * C)
  have hneg : Matrix.trace ((B * A) * C) = Matrix.trace ((C * B) * A) := by
    rw [Matrix.trace_mul_comm (B * A) C, Matrix.mul_assoc]
  rw [hpos, hneg]

/-- The source-frequency Euler seam obeys the Lie `2`-cocycle identity on pure `A₂` modes. -/
theorem eulerA2LaurentResiduePairing_cocycle
    (lambda mu nu : ℝ) (A B C : Matrix (Fin 3) (Fin 3) ℂ) :
    eulerA2LaurentResiduePairing (lambda + mu) nu ⁅A, B⁆ C +
      eulerA2LaurentResiduePairing (mu + nu) lambda ⁅B, C⁆ A +
      eulerA2LaurentResiduePairing (nu + lambda) mu ⁅C, A⁆ B = 0 := by
  by_cases h : lambda + mu + nu = 0
  · have h1 : lambda + mu + nu = 0 := h
    have h2 : mu + nu + lambda = 0 := by linarith
    have h3 : nu + lambda + mu = 0 := by linarith
    simp only [eulerA2LaurentResiduePairing, eulerLaurentResidueWeight,
      if_pos h1, if_pos h2, if_pos h3]
    rw [trace_lie_mul_cyclic_complex A B C, trace_lie_mul_cyclic_complex B C A]
    have hcast : ((-nu : ℝ) : ℂ) + ((-lambda : ℝ) : ℂ) + ((-mu : ℝ) : ℂ) = 0 := by
      have hreal : -nu + -lambda + -mu = 0 := by linarith
      exact_mod_cast hreal
    calc
      ((-nu : ℝ) : ℂ) * Matrix.trace (⁅C, A⁆ * B) +
            ((-lambda : ℝ) : ℂ) * Matrix.trace (⁅C, A⁆ * B) +
            ((-mu : ℝ) : ℂ) * Matrix.trace (⁅C, A⁆ * B) =
          (((-nu : ℝ) : ℂ) + ((-lambda : ℝ) : ℂ) + ((-mu : ℝ) : ℂ)) *
            Matrix.trace (⁅C, A⁆ * B) := by ring
      _ = 0 := by rw [hcast]; simp
  · have h1 : lambda + mu + nu ≠ 0 := h
    have h2 : mu + nu + lambda ≠ 0 := by
      intro hzero
      apply h
      linarith
    have h3 : nu + lambda + mu ≠ 0 := by
      intro hzero
      apply h
      linarith
    simp [eulerA2LaurentResiduePairing, eulerLaurentResidueWeight, h1, h2, h3]

end

end GaloisForLFunctions
