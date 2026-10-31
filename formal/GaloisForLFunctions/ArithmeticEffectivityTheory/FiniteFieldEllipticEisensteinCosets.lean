import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticLoopCharacters
import Mathlib.GroupTheory.Coset.Defs

/-!
# Arithmetic cosets and the actual elliptic Eisenstein summand

The Borel character is trivial on the actual arithmetic intersection.
Consequently the Iwasawa section defines a function of arithmetic Borel
cosets. The associated series is defined independently of any Weyl sum;
its convergence is a separate assertion.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
noncomputable section

/-- The actual Borel intersection inside the restricted rational loop group. -/
def arithmeticPositiveBorel : Subgroup restrictedRationalLoop :=
  adelicPositiveBorel.comap arithmeticLoopEmbedding

/-- Arithmetic cosets represented as `γ(Γ ∩ B)`. -/
abbrev ArithmeticBorelCosets := restrictedRationalLoop ⧸ arithmeticPositiveBorel

/-- Right arithmetic-Borel multiplication preserves every actual spectral summand. -/
theorem adelicIwasawaSection_arithmetic_coset (s t : ℂ) (g : AdelicLoop)
    (a b : restrictedRationalLoop) (hab : a⁻¹ * b ∈ arithmeticPositiveBorel) :
    adelicIwasawaSection s t (g * arithmeticLoopEmbedding a) =
      adelicIwasawaSection s t (g * arithmeticLoopEmbedding b) := by
  let d : adelicPositiveBorel := ⟨arithmeticLoopEmbedding (a⁻¹ * b), hab⟩
  have hd : adelicBorelCharacter s t d = 1 :=
    adelicBorelCharacter_arithmetic s t d ⟨a⁻¹ * b, rfl⟩
  have hr : a * (a⁻¹ * b) = b := by
    rw [← mul_assoc a a⁻¹ b, mul_inv_cancel a, one_mul b]
  have he : arithmeticLoopEmbedding a * (d : AdelicLoop) = arithmeticLoopEmbedding b :=
    (arithmeticLoopEmbedding.map_mul a (a⁻¹ * b)).symm.trans
      (congrArg arithmeticLoopEmbedding hr)
  symm
  calc
    adelicIwasawaSection s t (g * arithmeticLoopEmbedding b) =
        adelicIwasawaSection s t (g * (arithmeticLoopEmbedding a * (d : AdelicLoop))) :=
      congrArg (fun z : AdelicLoop => adelicIwasawaSection s t (g * z)) he.symm
    _ = adelicIwasawaSection s t ((g * arithmeticLoopEmbedding a) * (d : AdelicLoop)) :=
      congrArg (adelicIwasawaSection s t)
        (mul_assoc g (arithmeticLoopEmbedding a) (d : AdelicLoop)).symm
    _ = adelicIwasawaSection s t (g * arithmeticLoopEmbedding a) * adelicBorelCharacter s t d :=
      adelicIwasawaSection_right_borel s t (g * arithmeticLoopEmbedding a) d
    _ = adelicIwasawaSection s t (g * arithmeticLoopEmbedding a) := by rw [hd, mul_one]

/-- The independently defined summand on actual arithmetic Borel cosets. -/
def ellipticEisensteinSummand (s t : ℂ) (g : AdelicLoop) : ArithmeticBorelCosets → ℂ :=
  Quotient.lift (fun r => adelicIwasawaSection s t (g * arithmeticLoopEmbedding r))
    (fun a b h => adelicIwasawaSection_arithmetic_coset s t g a b
      (QuotientGroup.leftRel_apply.mp h))

/-- The arithmetic Eisenstein series; convergence must be established separately. -/
def ellipticEisensteinSeries (s t : ℂ) (g : AdelicLoop) : ℂ :=
  ∑' c : ArithmeticBorelCosets, ellipticEisensteinSummand s t g c

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.adelicIwasawaSection_arithmetic_coset
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.ellipticEisensteinSummand
