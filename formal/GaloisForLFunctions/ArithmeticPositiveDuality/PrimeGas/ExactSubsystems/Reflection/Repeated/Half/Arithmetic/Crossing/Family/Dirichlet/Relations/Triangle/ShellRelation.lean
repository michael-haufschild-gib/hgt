import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.Triangle.Exponents
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations.RelativeCoordinates

/-! # Realizing torsion triangles from integer shell relations -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations

open Real MvPolynomial

def delta (a c : ℕ+) := energy a-energy c

/-- A relation among the actual three shell weights, before normalizing a side. -/
def shellRelation (A B C : ℤ) (a b c : ℕ+) (t : ℝ) : Prop :=
  (A : ℝ)*shellPower t a+(B : ℝ)*shellPower t b=(C : ℝ)*shellPower t c

theorem gapExp_shell (a c : ℕ+) (s : ℝ) :
    gapExp (delta a c) s=(shellPower s a : ℂ)/(shellPower s c : ℂ) := by
  rw [← Complex.ofReal_div,gapExp,delta,← relativePower_exp]
  rfl

theorem gapExp_one_algebraic (a c : ℕ+) : IsAlgebraic ℚ (gapExp (delta a c) 1) := by
  have h := isAlgebraic_rat (A := ℂ) ℚ ((a.val : ℚ)/c.val)
  simpa only [gapExp_shell,shellPower,rpow_one,Rat.cast_div,Rat.cast_natCast,Complex.ofReal_natCast] using h

private theorem normalize {K : Type} [Field K] (A B C X Y Z U V W : K)
    (c : C ≠ 0) (z : Z ≠ 0) (w : W ≠ 0) (eq : A*(U*X)+B*(V*Y)=C*(W*Z)) :
    (A/C)*(X/Z)*(U/W)+(B/C)*(Y/Z)*(V/W)=1 := by
  field_simp
  linear_combination eq

theorem normalized_source {A B C : ℤ} {a b c : ℕ+} {t : ℝ} (hn : C ≠ 0)
    (h : shellRelation A B C a b c t) :
    (((A : ℚ)/C : ℚ) : ℝ)*exp (t*delta a c)+(((B : ℚ)/C : ℚ) : ℝ)*exp (t*delta b c)=1 := by
  have eq := normalize (K := ℝ) A B C (shellPower t a) (shellPower t b) (shellPower t c)
    1 1 1 (Int.cast_ne_zero.mpr hn) (shellPower_pos t c).ne' one_ne_zero (by simpa only [shellRelation,one_mul] using h)
  simpa only [div_one,mul_one,Rat.cast_div,Rat.cast_intCast,← relativePower_exp,relativePower,delta] using eq

theorem twisted_relation {A B C : ℤ} {a b c : ℕ+} {t v : ℝ} {m : ℕ}
    (hm : 0 < m) (hc : C ≠ 0) (h : shellRelation A B C a b c t) (spec : TorsionSpecialization m t v) :
    ∃ U V : ℂ, U^m=1 ∧ V^m=1 ∧
      (((A : ℚ)/C : ℚ) : ℂ)*gapExp (delta a c) v*U+(((B : ℚ)/C : ℚ) : ℂ)*gapExp (delta b c) v*V=1 := by
  obtain ⟨e,ω,unit,atoms,keep⟩ := twisted_evaluation spec
  let P : PolynomialRing := (A : PolynomialRing)*atom a+(B : PolynomialRing)*atom b-(C : PolynomialRing)*atom c
  have src (n : ℕ+) : value t (atom n)=shellPower t n := (value_atom n t).trans (shellPower_exp t n).symm
  have hit := keep P (by simp only [P,map_sub,map_add,map_mul,map_intCast,src]; exact sub_eq_zero.mpr h)
  simp only [P,map_sub,map_add,map_mul,map_intCast,atoms,sub_eq_zero] at hit
  have denom : ω c ≠ 0 := norm_pos_iff.mp (by rw [phase_norm hm (unit _)]; exact zero_lt_one)
  have power (n : ℕ+) : (ω n/ω c)^m=1 := by rw [div_pow,unit,unit,div_one]
  refine ⟨ω a/ω c,ω b/ω c,power a,power b,?_⟩
  simp only [Rat.cast_div,Rat.cast_intCast,gapExp_shell]
  exact normalize _ _ _ _ _ _ _ _ _ (Int.cast_ne_zero.mpr hc)
    (Complex.ofReal_ne_zero.mpr (shellPower_pos v c).ne') denom hit

#print axioms normalized_source
#print axioms twisted_relation

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Dirichlet.Relations
