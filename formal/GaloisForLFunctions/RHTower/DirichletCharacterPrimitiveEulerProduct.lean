import GaloisForLFunctions.RHTower.DirichletCharacterPrimitiveEulerFactor

/-!
# Global finite Euler product for primitive conductor reduction

For a nonprincipal Dirichlet character at an ambient modulus, this file uses
the canonical primitive conductor reduction to give Mathlib's global
change-level factorization. It then proves the finite product is nonzero on
`Re(s) > 0`, and consequently transports zeros of both uncompleted and
completed Dirichlet `L`-functions between the original and primitive
characters in that region.

This is a character-by-character zero transport. It does not yet reindex
zero divisors with multiplicity or establish a conductor-uniform density
estimate.
-/

open Complex LSeries DirichletCharacter

noncomputable section

namespace RHTower

/-- The finite product of omitted Euler factors relating an imprimitive
character to its canonical primitive conductor character. -/
noncomputable def cglPrimitiveEulerProduct
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (s : ℂ) : ℂ :=
  ∏ p ∈ (n + 1).primeFactors,
    (1 - (cglPrimitiveCharacterReduction n χ).primitiveCharacter p * (p : ℂ) ^ (-s))

/-- Global change-level factorization of a nonprincipal character `L`-function
through its canonical primitive conductor character. -/
theorem cglPrimitiveLFunction_changeLevel
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (s : ℂ) :
    DirichletCharacter.LFunction χ.1 s =
      cglPrimitiveLFunction n χ s * cglPrimitiveEulerProduct n χ s := by
  unfold cglPrimitiveLFunction cglPrimitiveEulerProduct
  letI : NeZero (cglPrimitiveCharacterReduction n χ).conductor :=
    ⟨Nat.ne_of_gt (cglPrimitiveCharacterReduction n χ).conductor_pos⟩
  rw [← (cglPrimitiveCharacterReduction n χ).induced_eq]
  exact DirichletCharacter.LFunction_changeLevel
    (cglPrimitiveCharacterReduction n χ).conductor_dvd_modulus
    (cglPrimitiveCharacterReduction n χ).primitiveCharacter
    (Or.inl (cglPrimitiveCharacterReduction n χ).nonprincipal)

/-- A complex evaluation point strictly to the right of the imaginary axis. -/
def CGLPositiveRealPartPoint := {s : ℂ // 0 < s.re}

private theorem cglPrimitiveEulerProduct_factor_ne_zero
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (s : CGLPositiveRealPartPoint)
    (p : ↑((n + 1).primeFactors)) :
    1 - (cglPrimitiveCharacterReduction n χ).primitiveCharacter p.1 * (p.1 : ℂ) ^ (-s.1) ≠ 0 := by
  have hpprime : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  have hpcastpos : 0 < (p.1 : ℝ) := by exact_mod_cast hpprime.pos
  have hpow : ‖(p.1 : ℂ) ^ (-s.1)‖ < 1 := by
    change ‖((p.1 : ℝ) : ℂ) ^ (-(s.1 : ℂ))‖ < 1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpcastpos]
    rw [Complex.neg_re]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hpprime.one_lt) (by linarith [s.2])
  have hchar : ‖(cglPrimitiveCharacterReduction n χ).primitiveCharacter p.1‖ ≤ 1 :=
    (cglPrimitiveCharacterReduction n χ).primitiveCharacter.norm_le_one p.1
  have hmul : ‖(cglPrimitiveCharacterReduction n χ).primitiveCharacter p.1 *
      (p.1 : ℂ) ^ (-s.1)‖ < 1 := by
    calc
      ‖(cglPrimitiveCharacterReduction n χ).primitiveCharacter p.1 *
          (p.1 : ℂ) ^ (-s.1)‖ =
          ‖(cglPrimitiveCharacterReduction n χ).primitiveCharacter p.1‖ *
            ‖(p.1 : ℂ) ^ (-s.1)‖ := norm_mul _ _
      _ ≤ 1 * ‖(p.1 : ℂ) ^ (-s.1)‖ :=
        mul_le_mul_of_nonneg_right hchar (norm_nonneg _)
      _ < 1 := by simpa using hpow
  intro hzero
  have hone : (cglPrimitiveCharacterReduction n χ).primitiveCharacter p.1 *
      (p.1 : ℂ) ^ (-s.1) = 1 := (sub_eq_zero.mp hzero).symm
  have hnorm := congrArg norm hone
  rw [norm_one] at hnorm
  linarith

/-- The finite omitted-prime Euler product is nonzero at every point with
positive real part. -/
theorem cglPrimitiveEulerProduct_ne_zero
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (s : CGLPositiveRealPartPoint) :
    cglPrimitiveEulerProduct n χ s.1 ≠ 0 := by
  unfold cglPrimitiveEulerProduct
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  exact cglPrimitiveEulerProduct_factor_ne_zero n χ s ⟨p, hp⟩

/-- In `Re(s) > 0`, the canonical primitive conductor `L`-function vanishes
exactly when the original nonprincipal character `L`-function vanishes. -/
theorem cglPrimitiveLFunction_zero_iff_input
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (s : CGLPositiveRealPartPoint) :
    cglPrimitiveLFunction n χ s.1 = 0 ↔
      DirichletCharacter.LFunction χ.1 s.1 = 0 := by
  rw [cglPrimitiveLFunction_changeLevel]
  constructor
  · intro h
    simp [h]
  · intro h
    exact (mul_eq_zero.mp h).resolve_right (cglPrimitiveEulerProduct_ne_zero n χ s)

private theorem cgl_gammaFactor_ne_zero_of_pos_re
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : CGLPositiveRealPartPoint) :
    DirichletCharacter.gammaFactor χ s.1 ≠ 0 := by
  rcases χ.even_or_odd with hχ | hχ
  · rw [hχ.gammaFactor_def]
    exact Gammaℝ_ne_zero_of_re_pos s.2
  · rw [hχ.gammaFactor_def]
    apply Gammaℝ_ne_zero_of_re_pos
    change 0 < s.1.re + 1
    linarith [s.2]

private theorem cgl_lfunction_zero_iff_completed_of_pos_re
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (s : CGLPositiveRealPartPoint) :
    DirichletCharacter.LFunction χ s.1 = 0 ↔
      DirichletCharacter.completedLFunction χ s.1 = 0 := by
  have hsne : s.1 ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp only [zero_re] at hre
    linarith [s.2]
  rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s.1 (Or.inl hsne)]
  constructor
  · intro hzero
    exact (div_eq_zero_iff.mp hzero).resolve_right
      (cgl_gammaFactor_ne_zero_of_pos_re χ s)
  · intro hzero
    rw [hzero, zero_div]

/-- In `Re(s) > 0`, zeros of the original uncompleted and completed
nonprincipal Dirichlet `L`-functions agree. -/
theorem cglLFunction_zero_iff_completedLFunction
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (s : CGLPositiveRealPartPoint) :
    DirichletCharacter.LFunction χ.1 s.1 = 0 ↔
      DirichletCharacter.completedLFunction χ.1 s.1 = 0 :=
  cgl_lfunction_zero_iff_completed_of_pos_re χ.1 s

/-- The completed `L`-function of the canonical primitive conductor character.
The required nonzero conductor is discharged internally. -/
noncomputable def cglPrimitiveCompletedLFunction
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (s : ℂ) : ℂ := by
  letI : NeZero (cglPrimitiveCharacterReduction n χ).conductor :=
    ⟨Nat.ne_of_gt (cglPrimitiveCharacterReduction n χ).conductor_pos⟩
  exact DirichletCharacter.completedLFunction
    (cglPrimitiveCharacterReduction n χ).primitiveCharacter s

/-- In `Re(s) > 0`, the canonical primitive and original completed
Dirichlet `L`-functions have exactly the same zero set. -/
theorem cglPrimitiveCompletedLFunction_zero_iff_input
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (s : CGLPositiveRealPartPoint) :
    cglPrimitiveCompletedLFunction n χ s.1 = 0 ↔
      DirichletCharacter.completedLFunction χ.1 s.1 = 0 := by
  unfold cglPrimitiveCompletedLFunction
  letI : NeZero (cglPrimitiveCharacterReduction n χ).conductor :=
    ⟨Nat.ne_of_gt (cglPrimitiveCharacterReduction n χ).conductor_pos⟩
  have hprimitive : cglPrimitiveLFunction n χ s.1 = 0 ↔
      DirichletCharacter.completedLFunction
        (cglPrimitiveCharacterReduction n χ).primitiveCharacter s.1 = 0 := by
    unfold cglPrimitiveLFunction
    exact cgl_lfunction_zero_iff_completed_of_pos_re
      (cglPrimitiveCharacterReduction n χ).primitiveCharacter s
  rw [← hprimitive, cglPrimitiveLFunction_zero_iff_input,
    cglLFunction_zero_iff_completedLFunction]

end RHTower
