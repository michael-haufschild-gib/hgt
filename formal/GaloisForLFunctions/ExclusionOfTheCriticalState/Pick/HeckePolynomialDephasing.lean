import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeHeckeAdjointAction

/-!
# Momentum-dependent decoherence on the finite Weil probe hull

Equations (5)–(9) of Donadi–Lobo–Fadel, arXiv:2611.17260, give a decay
rate equal to a squared difference of jump eigenvalues. Polynomial jumps
on the Hecke hull have two eigenvalues. Their difference determines the
whole double commutator, including at a collision of polynomial values.
-/

noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
open _root_.Polynomial
variable {N : ℕ} (p : Fin N → {x : ℝ // 1 ≤ x})
local notation "A" => Module.End ℂ (reflectionHull p)

/-- Commutator with a polynomial of the specialized Hecke generator. -/
def jumpBracket (q : ℂ) (f : Polynomial ℂ) (X : A) : A :=
  aeval (hullHecke p q) f * X - X * aeval (hullHecke p q) f

private theorem jump_affine (q : ℂ) (f : Polynomial ℂ) :
    aeval (hullHecke p q) f =
      f.eval (q^2) • (1 : A) + (f.eval (q^2)-f.eval (-1)) • hullHecke p 0 := by
  rw [hullHecke_polynomial,hullHecke_zero,← hullPositive_add_hullNegative p]
  simp only [smul_add,smul_neg,sub_smul]
  abel

/-- The first commutator reads a signed difference of jump eigenvalues. -/
theorem jumpBracket_gap (q : ℂ) (f : Polynomial ℂ) (X : A) :
    jumpBracket p q f X = (f.eval (q^2)-f.eval (-1)) • hullHeckeCommutator p 0 X := by
  rw [jumpBracket,jump_affine,hullHeckeCommutator]
  simp only [add_mul,mul_add,smul_mul_assoc,mul_smul_comm,one_mul,mul_one,smul_sub]
  abel

/-- Two different jumps polarize the squared rate. They need not have
the same polynomial or the same Hecke parameter. -/
theorem jumpBracket_cross (q r : ℂ) (f g : Polynomial ℂ) (X : A) :
    jumpBracket p q f (jumpBracket p r g X) =
      ((f.eval (q^2)-f.eval (-1))*(g.eval (r^2)-g.eval (-1))) • hullMixedPart p X := by
  rw [jumpBracket_gap,jumpBracket_gap]
  have hs (c : ℂ) (Y : A) : hullHeckeCommutator p 0 (c • Y) =
      c • hullHeckeCommutator p 0 Y := by
    simp only [hullHeckeCommutator,mul_smul_comm,smul_mul_assoc,smul_sub]
  rw [hs,hullHeckeCommutator_square]
  simp only [zero_pow (by norm_num : 2 ≠ 0),zero_add,one_pow,one_smul,smul_smul]

/-- Complete kernel of the polynomial double commutator. -/
theorem jumpBracket_square_zero_iff (q : ℂ) (f : Polynomial ℂ) (X : A) :
    jumpBracket p q f (jumpBracket p q f X) = 0 ↔
      f.eval (q^2) = f.eval (-1) ∨ Commute (hullReflection p) X := by
  simp only [jumpBracket_cross,smul_eq_zero,mul_eq_zero,or_self,sub_eq_zero,hullMixedPart_zero_iff]

/-- For a reflected pair, even momentum powers protect every observable.
Odd powers damp the sector-exchanging part at the same normalized rate. -/
theorem momentum_power_at_reflection (j : ℕ) (X : A) :
    jumpBracket p 1 (Polynomial.X^j) (jumpBracket p 1 (Polynomial.X^j) X) =
      (if Even j then 0 else (4:ℂ)) • hullMixedPart p X := by
  rw [jumpBracket_cross]
  simp only [one_pow, eval_pow, eval_X]
  rcases Nat.even_or_odd j with he | ho
  · simp [he,he.neg_one_pow]
  · simp [ho.not_even,ho.neg_one_pow]
    <;> norm_num

/-- Multiplying only mixed-sector observables by z. -/
def hullAttenuation (z : ℂ) (X : A) : A := X + (z-1) • hullMixedPart p X

private theorem mixed_add (X Y : A) : hullMixedPart p (X+Y) = hullMixedPart p X + hullMixedPart p Y := by
  simp only [hullMixedPart,mul_add,add_mul,smul_add,smul_sub]
  abel

private theorem mixed_smul (c : ℂ) (X : A) : hullMixedPart p (c • X) = c • hullMixedPart p X := by
  simp only [hullMixedPart,mul_smul_comm,smul_mul_assoc,← smul_sub]
  exact smul_comm _ _ _

theorem mixed_attenuation (z : ℂ) (X : A) :
    hullMixedPart p (hullAttenuation p z X) = z • hullMixedPart p X := by
  rw [hullAttenuation,mixed_add,mixed_smul,hullMixedPart_twice,sub_smul,one_smul]
  abel

/-- Independent attenuation steps multiply, even when one step is complete pinching. -/
theorem hullAttenuation_mul (z w : ℂ) (X : A) :
    hullAttenuation p z (hullAttenuation p w X) = hullAttenuation p (z*w) X := by
  rw [hullAttenuation p z,mixed_attenuation]
  simp only [hullAttenuation,smul_smul]
  module

/-- For a real jump gap the exact dephasing multiplier is exp(−t gap²). -/
def gapFlow (gap t : ℝ) (X : A) : A :=
  hullAttenuation p (Real.exp (-t*gap^2) : ℂ) X

theorem gapFlow_add (g s t : ℝ) (X : A) :
    gapFlow p g (s+t) X = gapFlow p g s (gapFlow p g t X) := by
  simp only [gapFlow,hullAttenuation_mul,neg_add,add_mul,Real.exp_add,Complex.ofReal_mul]

/-- At positive time a polynomial jump protects all and only the equal-value
blocks. Time zero and a vanishing gap are retained in the same criterion. -/
theorem gapFlow_fixed_iff (g t : ℝ) (X : A) :
    gapFlow p g t X = X ↔ t = 0 ∨ g = 0 ∨ Commute (hullReflection p) X := by
  change X + _ • hullMixedPart p X = X ↔ _
  rw [add_eq_left,smul_eq_zero,sub_eq_zero,hullMixedPart_zero_iff]
  have he : (Real.exp (-t*g^2) : ℂ) = 1 ↔ t = 0 ∨ g = 0 := by
    rw [← Complex.ofReal_one,Complex.ofReal_inj,Real.exp_eq_one_iff]
    simp only [mul_eq_zero,neg_eq_zero,sq_eq_zero_iff]
  rw [he,or_assoc]

#print axioms jumpBracket_gap
#print axioms jumpBracket_cross
#print axioms jumpBracket_square_zero_iff
#print axioms momentum_power_at_reflection
#print axioms mixed_attenuation
#print axioms hullAttenuation_mul
#print axioms gapFlow_add
#print axioms gapFlow_fixed_iff
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
