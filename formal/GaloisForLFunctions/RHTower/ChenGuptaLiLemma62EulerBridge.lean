import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62FunctionalEquation
import GaloisForLFunctions.RHTower.DirichletCharacterPrimitiveEulerProduct

/-!
# Chen--Gupta--Li Lemma 6.2: imprimitive Euler-factor bridge

After applying the primitive functional equation on CGL's shifted line,
the original imprimitive character reappears through a quotient of two finite
Euler products.  This module formalizes that quotient and the change-level
identity on the exact `Re = -1` / `Re = 2` pair of vertical lines.
-/

open Complex
open scoped BigOperators

noncomputable section

namespace RHTower

/-- A nonprincipal ambient character together with its primitive inducing
character.  The ambient induction equality is certified data, never a raw
premise of an exported CGL theorem. -/
structure CGLLemma62InducedCharacter where
  ambient : CGLPositiveModulus
  character : DirichletCharacter ℂ ambient.value
  nonprincipal : character ≠ 1
  primitive : CGLLemma62PrimitiveCharacter
  conductor_dvd_ambient : primitive.modulus.value ∣ ambient.value
  induced_eq : DirichletCharacter.changeLevel conductor_dvd_ambient primitive.character = character

/-- Construct the exact inducing-character packet from the corpus's canonical
primitive-conductor reduction of a nonprincipal Dirichlet character. -/
noncomputable def cglLemma62InducedCharacterOfNonprincipal
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) : CGLLemma62InducedCharacter where
  ambient := ⟨n + 1, Nat.succ_pos n⟩
  character := χ.1
  nonprincipal := χ.2
  primitive :=
    { modulus := ⟨(cglPrimitiveCharacterReduction n χ).conductor,
        (cglPrimitiveCharacterReduction n χ).conductor_pos⟩
      character := (cglPrimitiveCharacterReduction n χ).primitiveCharacter
      nonprincipal := (cglPrimitiveCharacterReduction n χ).nonprincipal
      primitive := (cglPrimitiveCharacterReduction n χ).primitive }
  conductor_dvd_ambient := (cglPrimitiveCharacterReduction n χ).conductor_dvd_modulus
  induced_eq := (cglPrimitiveCharacterReduction n χ).induced_eq

/-- The shifted argument of the primitive source `L`-function in CGL (6.3). -/
def cglLemma62LeftPoint (t v : ℝ) : ℂ :=
  (-1 : ℂ) + ((v - t : ℝ) : ℂ) * I

/-- The reflected, absolutely convergent argument in CGL (6.3). -/
def cglLemma62RightPoint (t v : ℝ) : ℂ :=
  (2 : ℂ) + ((t - v : ℝ) : ℂ) * I

/-- The finite Euler product multiplying the primitive `L`-function on the
left CGL contour. -/
def cglLemma62EulerLeftFactor (B : CGLLemma62InducedCharacter) (t v : ℝ) : ℂ :=
  ∏ p ∈ B.ambient.value.primeFactors,
    (1 - B.primitive.character p * (p : ℂ) ^ (-cglLemma62LeftPoint t v))

/-- The finite Euler product multiplying the inverse primitive `L`-function
on CGL's reflected right line. -/
def cglLemma62EulerRightFactor (B : CGLLemma62InducedCharacter) (t v : ℝ) : ℂ :=
  ∏ p ∈ B.ambient.value.primeFactors,
    (1 - B.primitive.character⁻¹ p * (p : ℂ) ^ (-cglLemma62RightPoint t v))

private theorem cglLemma62EulerRightFactor_factor_ne_zero
    (B : CGLLemma62InducedCharacter) (t v : ℝ)
    (p : ↑B.ambient.value.primeFactors) :
    1 - B.primitive.character⁻¹ p.1 * (p.1 : ℂ) ^
      (-cglLemma62RightPoint t v) ≠ 0 := by
  have hpprime : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  have hpcastpos : 0 < (p.1 : ℝ) := by exact_mod_cast hpprime.pos
  let z : ℂ := (p.1 : ℂ) ^ (-cglLemma62RightPoint t v)
  have hpow : ‖z‖ < 1 := by
    dsimp [z]
    rw [cglLemma62RightPoint]
    change ‖((p.1 : ℝ) : ℂ) ^ (-((2 : ℂ) + ((t - v : ℝ) : ℂ) * I))‖ < 1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpcastpos]
    rw [Complex.neg_re]
    apply Real.rpow_lt_one_of_one_lt_of_neg
    · exact_mod_cast hpprime.one_lt
    · simp
  have hchar : ‖B.primitive.character⁻¹ p.1‖ ≤ 1 :=
    B.primitive.character⁻¹.norm_le_one p.1
  have hmul : ‖B.primitive.character⁻¹ p.1 * z‖ < 1 := by
    calc
      ‖B.primitive.character⁻¹ p.1 * z‖ = ‖B.primitive.character⁻¹ p.1‖ * ‖z‖ :=
        norm_mul _ _
      _ ≤ 1 * ‖z‖ :=
        mul_le_mul_of_nonneg_right hchar (norm_nonneg _)
      _ < 1 := by simpa using hpow
  intro hzero
  have hzero' : 1 - B.primitive.character⁻¹ p.1 * z = 0 := by
    simpa only [z] using hzero
  have hone : B.primitive.character⁻¹ p.1 * z = 1 :=
    (sub_eq_zero.mp hzero').symm
  have hnorm := congrArg norm hone
  rw [norm_one] at hnorm
  linarith

/-- The right-line Euler product is nonzero.  Its factors have norm strictly
less than one before subtraction because that line has real part two. -/
theorem cglLemma62EulerRightFactor_ne_zero
    (B : CGLLemma62InducedCharacter) (t v : ℝ) :
    cglLemma62EulerRightFactor B t v ≠ 0 := by
  unfold cglLemma62EulerRightFactor
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  exact cglLemma62EulerRightFactor_factor_ne_zero B t v ⟨p, hp⟩

/-- CGL's finite Euler correction `P(s-it)` on the shifted contour. -/
def cglLemma62EulerCorrection (B : CGLLemma62InducedCharacter) (t v : ℝ) : ℂ :=
  cglLemma62EulerLeftFactor B t v / cglLemma62EulerRightFactor B t v

/-- The correction times its nonzero reflected denominator recovers the left
Euler product exactly. -/
theorem cglLemma62EulerCorrection_mul_rightFactor
    (B : CGLLemma62InducedCharacter) (t v : ℝ) :
    cglLemma62EulerCorrection B t v * cglLemma62EulerRightFactor B t v =
      cglLemma62EulerLeftFactor B t v := by
  unfold cglLemma62EulerCorrection
  field_simp [cglLemma62EulerRightFactor_ne_zero B t v]

/-- Inverting the certified inducing identity commutes with changing level. -/
theorem cglLemma62InducedCharacter_inverse_induced_eq
    (B : CGLLemma62InducedCharacter) :
    DirichletCharacter.changeLevel B.conductor_dvd_ambient B.primitive.character⁻¹ =
      B.character⁻¹ := by
  calc
    DirichletCharacter.changeLevel B.conductor_dvd_ambient B.primitive.character⁻¹ =
        (DirichletCharacter.changeLevel B.conductor_dvd_ambient B.primitive.character)⁻¹ :=
      map_inv _ _
    _ = B.character⁻¹ := congrArg Inv.inv B.induced_eq

/-- The inverse primitive character is nonprincipal. -/
theorem cglLemma62PrimitiveCharacter_inverse_nonprincipal
    (B : CGLLemma62InducedCharacter) : B.primitive.character⁻¹ ≠ 1 := by
  intro hinv
  apply B.primitive.nonprincipal
  calc
    B.primitive.character = (B.primitive.character⁻¹)⁻¹ := (inv_inv _).symm
    _ = (1 : DirichletCharacter ℂ B.primitive.modulus.value)⁻¹ := congrArg Inv.inv hinv
    _ = 1 := inv_one

/-- Exact left-line change-level factorization in CGL (6.3). -/
theorem cglLemma62InducedCharacter_lfunction_leftFactor
    (B : CGLLemma62InducedCharacter) (t v : ℝ) :
    DirichletCharacter.LFunction B.character (cglLemma62LeftPoint t v) =
      DirichletCharacter.LFunction B.primitive.character (cglLemma62LeftPoint t v) *
        cglLemma62EulerLeftFactor B t v := by
  rw [← B.induced_eq]
  simpa only [cglLemma62EulerLeftFactor] using
    (DirichletCharacter.LFunction_changeLevel B.conductor_dvd_ambient B.primitive.character
      (Or.inl B.primitive.nonprincipal))

/-- Exact reflected-right-line change-level factorization for the inverse
character. -/
theorem cglLemma62InducedCharacter_inverse_lfunction_rightFactor
    (B : CGLLemma62InducedCharacter) (t v : ℝ) :
    DirichletCharacter.LFunction B.character⁻¹ (cglLemma62RightPoint t v) =
      DirichletCharacter.LFunction B.primitive.character⁻¹ (cglLemma62RightPoint t v) *
        cglLemma62EulerRightFactor B t v := by
  rw [← cglLemma62InducedCharacter_inverse_induced_eq]
  simpa only [cglLemma62EulerRightFactor] using
    (DirichletCharacter.LFunction_changeLevel B.conductor_dvd_ambient B.primitive.character⁻¹
      (Or.inl (cglLemma62PrimitiveCharacter_inverse_nonprincipal B)))

/-- **CGL (6.3), reflected Euler-factor identity.**  The finite Euler
correction transfers the reflected primitive `L`-function to the original
inverse character without a denominator hypothesis. -/
theorem cglLemma62EulerCorrection_reflected_lfunction
    (B : CGLLemma62InducedCharacter) (t v : ℝ) :
    cglLemma62EulerCorrection B t v *
        DirichletCharacter.LFunction B.character⁻¹ (cglLemma62RightPoint t v) =
      cglLemma62EulerLeftFactor B t v *
        DirichletCharacter.LFunction B.primitive.character⁻¹
          (cglLemma62RightPoint t v) := by
  rw [cglLemma62InducedCharacter_inverse_lfunction_rightFactor]
  rw [show cglLemma62EulerCorrection B t v *
      (DirichletCharacter.LFunction B.primitive.character⁻¹ (cglLemma62RightPoint t v) *
        cglLemma62EulerRightFactor B t v) =
      (cglLemma62EulerCorrection B t v * cglLemma62EulerRightFactor B t v) *
        DirichletCharacter.LFunction B.primitive.character⁻¹ (cglLemma62RightPoint t v) by
      ring]
  rw [cglLemma62EulerCorrection_mul_rightFactor]

end RHTower
