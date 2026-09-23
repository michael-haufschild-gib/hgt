import GaloisForLFunctions.RHTower.EulerSquarefreeWickPrimitiveCompletedInteraction
import GaloisForLFunctions.RHTower.XiSelectedBilateralPositiveSourceReceiver
import GaloisForLFunctions.RHTower.DirichletLZeroExistence

/-!
# The EWQ conductor is a composite Meyer modular character

The primitive Euler--Wick interaction has conductor `12 = 2^(2 : ℕ) * 3`.  This arithmetic factor is
exactly the product of two prime-two Meyer/Koszul characters and one prime-three character:

`12^(1/2-s) = delta_s(2)^(2 : ℕ) delta_s(3)`.

Consequently reflection of the conductor half-density `12^(s/2)` produces the exact composite
Meyer character, while reflection of the unrenormalized completed Dirichlet L-function produces
its inverse.  The constant-root-number EWQ completion cancels these two non-unitary factors.

This is the first coefficient-exact bridge from the primitive EWQ completion to the genuine
Xi-selected Meyer modular weights.  It also exposes a normalization wall.  Off the critical line
the conductor half-density cannot have equal reflected mass; the fully completed EWQ carrier hides
that displacement by cancellation.  Thus a successful EWQ orientation law must retain the
conductor/Meyer factor through the positive landing instead of reading only the constant-root
completed scalar.
-/

open Complex

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Composite Meyer character carried by the primitive EWQ conductor. -/
def ewqConductorMeyerCharacter (s : ℂ) : ℂ :=
  _root_.RHTower.deltaS 12 s

/-- Conductor half-density used in the constant-root-number Dirichlet completion. -/
def ewqConductorHalfDensity (s : ℂ) : ℂ :=
  (12 : ℂ) ^ (s / 2)

private theorem natCast_mul_cpow (m n : ℕ) (z : ℂ) :
    ((m * n : ℕ) : ℂ) ^ z = ((m : ℕ) : ℂ) ^ z * ((n : ℕ) : ℂ) ^ z := by
  push_cast
  rw [show (m : ℂ) = ((m : ℝ) : ℂ) by push_cast; rfl,
    show (n : ℂ) = ((n : ℝ) : ℂ) by push_cast; rfl,
    Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)]

/-- The conductor-twelve character is exactly the product of its `4`- and `3`-primary Meyer
characters, with the `4`-part resolved into two prime-two clocks. -/
theorem ewqConductorMeyerCharacter_eq_primeProduct (s : ℂ) :
    ewqConductorMeyerCharacter s =
      _root_.RHTower.deltaS 2 s ^ (2 : ℕ) * _root_.RHTower.deltaS 3 s := by
  rw [ewqConductorMeyerCharacter, _root_.RHTower.deltaS,
    _root_.RHTower.deltaS, _root_.RHTower.deltaS]
  let z : ℂ := 1 / 2 - s
  calc
    ((12 : ℕ) : ℂ) ^ z = (((4 * 3 : ℕ) : ℂ) ^ z) := by norm_num
    _ = ((4 : ℕ) : ℂ) ^ z * ((3 : ℕ) : ℂ) ^ z := natCast_mul_cpow 4 3 z
    _ = (((2 * 2 : ℕ) : ℂ) ^ z) * ((3 : ℕ) : ℂ) ^ z := by norm_num
    _ = (((2 : ℕ) : ℂ) ^ z * ((2 : ℕ) : ℂ) ^ z) *
        ((3 : ℕ) : ℂ) ^ z := by rw [natCast_mul_cpow 2 2 z]
    _ = (((2 : ℕ) : ℂ) ^ z) ^ (2 : ℕ) * ((3 : ℕ) : ℂ) ^ z := by ring

/-- Reflection of the EWQ conductor half-density is multiplication by the composite Meyer
character. -/
theorem ewqConductorHalfDensity_reflection (s : ℂ) :
    ewqConductorHalfDensity (1 - s) =
      ewqConductorMeyerCharacter s * ewqConductorHalfDensity s := by
  rw [ewqConductorHalfDensity, ewqConductorHalfDensity,
    ewqConductorMeyerCharacter, _root_.RHTower.deltaS]
  calc
    (12 : ℂ) ^ ((1 - s) / 2) =
        (12 : ℂ) ^ ((1 / 2 - s) + s / 2) := by
          congr 1
          ring
    _ = (12 : ℂ) ^ (1 / 2 - s) * (12 : ℂ) ^ (s / 2) := by
      rw [Complex.cpow_add _ _ (by norm_num : (12 : ℂ) ≠ 0)]

/-- The ordinary completed L-function transforms by the inverse composite Meyer character.  The
conductor half-density above is exactly what cancels this multiplier in `dirichletXi`. -/
theorem ewqCompletedLFunction_one_sub_meyer (s : ℂ) :
    DirichletCharacter.completedLFunction quadraticCharacterTwelve (1 - s) =
      (ewqConductorMeyerCharacter s)⁻¹ * quadraticCharacterTwelve.rootNumber *
        DirichletCharacter.completedLFunction quadraticCharacterTwelve s := by
  rw [quadraticCharacterTwelve_isPrimitive.completedLFunction_one_sub,
    quadraticCharacterTwelve_inv]
  congr 1
  rw [ewqConductorMeyerCharacter, _root_.RHTower.deltaS]
  rw [show (1 / 2 : ℂ) - s = -(s - 1 / 2) by ring, Complex.cpow_neg]
  simp

/-- On an actual Xi divisor, the conductor character is built from the same genuine prime-flow
reporters used by the Meyer/Koszul/Gamma source. -/
theorem ewqConductorMeyerCharacter_eq_selectedPrimeProduct
    (rho : _root_.RHTower.XiDivisorSupport) :
    ewqConductorMeyerCharacter (rho : ℂ) =
      _root_.RHTower.deningerMeyerXiPrimeGammaCharacter rho ewqPrimeTwo ^ (2 : ℕ) *
        _root_.RHTower.deningerMeyerXiPrimeGammaCharacter rho ewqPrimeThree := by
  rw [_root_.RHTower.deningerMeyerXiPrimeGammaCharacter_eq_deltaS,
    _root_.RHTower.deningerMeyerXiPrimeGammaCharacter_eq_deltaS]
  exact ewqConductorMeyerCharacter_eq_primeProduct (rho : ℂ)

/-- Exact horizontal modulus of the conductor/Meyer character. -/
theorem norm_ewqConductorMeyerCharacter (s : ℂ) :
    ‖ewqConductorMeyerCharacter s‖ = (12 : ℝ) ^ (1 / 2 - s.re) := by
  exact _root_.RHTower.norm_deltaS (by norm_num : 0 < 12) s

/-- The composite conductor character is unitary exactly on the critical line. -/
theorem norm_ewqConductorMeyerCharacter_eq_one_iff (s : ℂ) :
    ‖ewqConductorMeyerCharacter s‖ = 1 ↔ s.re = 1 / 2 := by
  exact _root_.RHTower.norm_deltaS_eq_one_iff (by norm_num : 2 ≤ 12) s

/-- Its Hermitian square is exactly the product of the actual prime-two and prime-three modular
weights, with conductor multiplicity `12 = 2^(2 : ℕ) * 3`. -/
theorem norm_sq_ewqConductorMeyerCharacter_eq_selectedModularWeightProduct
    (rho : _root_.RHTower.XiDivisorSupport) :
    ‖ewqConductorMeyerCharacter (rho : ℂ)‖ ^ (2 : ℕ) =
      (_root_.RHTower.deningerMeyerXiPrimeGammaModularWeight rho ewqPrimeTwo) ^ (2 : ℕ) *
        _root_.RHTower.deningerMeyerXiPrimeGammaModularWeight rho ewqPrimeThree := by
  rw [ewqConductorMeyerCharacter_eq_selectedPrimeProduct, norm_mul, norm_pow,
    _root_.RHTower.deningerMeyerXiPrimeGammaModularWeight,
    _root_.RHTower.deningerMeyerXiPrimeGammaModularWeight]
  ring

/-- Ratio form of the conductor reflection law. -/
theorem ewqConductorHalfDensity_reflection_div (s : ℂ) :
    ewqConductorHalfDensity (1 - s) / ewqConductorHalfDensity s =
      ewqConductorMeyerCharacter s := by
  rw [ewqConductorHalfDensity_reflection]
  have hne : ewqConductorHalfDensity s ≠ 0 := by
    rw [ewqConductorHalfDensity, Complex.cpow_def_of_ne_zero (by norm_num)]
    exact Complex.exp_ne_zero _
  field_simp [hne]

/-- **Conductor normalization wall.**  The reflected and direct conductor half-densities have
equal mass exactly on the critical line.  Constant-root completion cancels, rather than proves,
this equality. -/
theorem norm_ewqConductorHalfDensity_reflection_eq_iff (s : ℂ) :
    ‖ewqConductorHalfDensity (1 - s)‖ = ‖ewqConductorHalfDensity s‖ ↔
      s.re = 1 / 2 := by
  rw [ewqConductorHalfDensity_reflection, norm_mul]
  have hne : ewqConductorHalfDensity s ≠ 0 := by
    rw [ewqConductorHalfDensity, Complex.cpow_def_of_ne_zero (by norm_num)]
    exact Complex.exp_ne_zero _
  have hpos : 0 < ‖ewqConductorHalfDensity s‖ := norm_pos_iff.mpr hne
  constructor
  · intro h
    apply (norm_ewqConductorMeyerCharacter_eq_one_iff s).1
    nlinarith
  · intro hline
    rw [(norm_ewqConductorMeyerCharacter_eq_one_iff s).2 hline, one_mul]

/-! ## What root correction retains -/

/-- Root-corrected reflection pair of the fully renormalized primitive EWQ carrier. -/
def ewqRootCorrectedDirichletXiReflectionPair (s : ℂ) : Fin 2 → ℂ :=
  ![eulerWickQuadraticPrimitiveCompletedInteraction s,
    quadraticCharacterTwelve.rootNumber⁻¹ *
      eulerWickQuadraticPrimitiveCompletedInteraction (1 - s)]

/-- **Completed-pair collapse.**  After correcting the constant root-number phase, the two
reflected completed EWQ components are literally equal.  The completed pair is the trivial
Pauli-`+` direction and contains no Meyer modulus. -/
theorem ewqRootCorrectedDirichletXiReflectionPair_eq_constant (s : ℂ) :
    ewqRootCorrectedDirichletXiReflectionPair s =
      ![eulerWickQuadraticPrimitiveCompletedInteraction s,
        eulerWickQuadraticPrimitiveCompletedInteraction s] := by
  funext i
  fin_cases i
  · rfl
  · change quadraticCharacterTwelve.rootNumber⁻¹ *
        eulerWickQuadraticPrimitiveCompletedInteraction (1 - s) =
      eulerWickQuadraticPrimitiveCompletedInteraction s
    rw [eulerWickQuadraticPrimitiveCompletedInteraction_one_sub]
    field_simp [_root_.RHTower.rootNumber_ne_zero quadraticCharacterTwelve_isPrimitive]

/-- Root-corrected reflection pair before multiplying by the conductor half-density. -/
def ewqRootCorrectedCompletedLReflectionPair (s : ℂ) : Fin 2 → ℂ :=
  ![DirichletCharacter.completedLFunction quadraticCharacterTwelve s,
    quadraticCharacterTwelve.rootNumber⁻¹ *
      DirichletCharacter.completedLFunction quadraticCharacterTwelve (1 - s)]

/-- Before constant-root renormalization, the reflected component retains exactly the inverse
composite Meyer character. -/
theorem ewqRootCorrectedCompletedLReflectionPair_eq_meyer (s : ℂ) :
    ewqRootCorrectedCompletedLReflectionPair s =
      ![DirichletCharacter.completedLFunction quadraticCharacterTwelve s,
        (ewqConductorMeyerCharacter s)⁻¹ *
          DirichletCharacter.completedLFunction quadraticCharacterTwelve s] := by
  funext i
  fin_cases i
  · rfl
  · change quadraticCharacterTwelve.rootNumber⁻¹ *
        DirichletCharacter.completedLFunction quadraticCharacterTwelve (1 - s) =
      (ewqConductorMeyerCharacter s)⁻¹ *
        DirichletCharacter.completedLFunction quadraticCharacterTwelve s
    rw [ewqCompletedLFunction_one_sub_meyer]
    field_simp [_root_.RHTower.rootNumber_ne_zero quadraticCharacterTwelve_isPrimitive]

/-- **Raw-pair normalization wall.**  At a point where the primitive completed L-function is
nonzero, its two root-corrected reflected components have equal norm exactly on the critical
line.  The fully renormalized pair above obtains equality only by absorbing this character into
the conductor half-density. -/
theorem norm_ewqRootCorrectedCompletedLReflectionPair_eq_iff
    (s : ℂ)
    (hL : DirichletCharacter.completedLFunction quadraticCharacterTwelve s ≠ 0) :
    ‖ewqRootCorrectedCompletedLReflectionPair s 0‖ =
        ‖ewqRootCorrectedCompletedLReflectionPair s 1‖ ↔
      s.re = 1 / 2 := by
  rw [ewqRootCorrectedCompletedLReflectionPair_eq_meyer]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, norm_mul, norm_inv]
  have hdelta : ewqConductorMeyerCharacter s ≠ 0 := by
    rw [ewqConductorMeyerCharacter, _root_.RHTower.deltaS,
      Complex.cpow_def_of_ne_zero (by norm_num)]
    exact Complex.exp_ne_zero _
  have hdeltaPos : 0 < ‖ewqConductorMeyerCharacter s‖ := norm_pos_iff.mpr hdelta
  have hLPos : 0 < ‖DirichletCharacter.completedLFunction quadraticCharacterTwelve s‖ :=
    norm_pos_iff.mpr hL
  constructor
  · intro hnorm
    apply (norm_ewqConductorMeyerCharacter_eq_one_iff s).1
    have hinv : ‖ewqConductorMeyerCharacter s‖⁻¹ = 1 := by
      nlinarith
    simpa using congrArg Inv.inv hinv
  · intro hline
    rw [(norm_ewqConductorMeyerCharacter_eq_one_iff s).2 hline]
    norm_num

end

end GaloisForLFunctions.RHTower
