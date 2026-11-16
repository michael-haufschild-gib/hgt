import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerThreePointExtensionRamification
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.PolynomialNormalizationResidues
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerConstantField

/-!
# Full constants after changing the constant field

The simple origin remains a rational normalization prime over any
extension of the stated constants. Specializing algebraic constants
there shows that the enlarged coefficient field is still the full
constant field of the fixed-degree three-point equation.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial IsDedekindDomain
variable (p : ℕ) [Fact p.Prime] (d n : ℕ)
    (E : Type*) [Field E]
    [Algebra (SquareConstantField p (kummerSquareIndex d n)) E]
    (c : Eˣ) (a : ℕ)
local notation "L" => PrimePowerThreePointExtensionField p d n E c a
local notation "B" => PrimePowerThreePointExtensionNormalization p d n E c a

/-- Every element algebraic over the enlarged constants is already in that constant field. -/
theorem primePowerThreePointExtension_constantField (z : L) (hz : IsAlgebraic E z) :
    ∃ t : E, algebraMap E L t = z := by
  classical
  let v := GaloisForLFunctions.HTGeometry.polyPlace (irreducible_X_sub_C (0 : E))
  letI : (Ideal.span {X - C (0 : E)}).IsMaximal := v.isPrime.isMaximal v.ne_bot
  have hv0 : (Ideal.span {X - C (0 : E)}) ≠ ⊥ := v.ne_bot
  obtain ⟨P, hP, hf⟩ := primePowerThreePointExtension_origin_singleton p d n E c a
  have hm : P ∈ IsDedekindDomain.primesOverFinset (Ideal.span {X - C (0 : E)}) B := by
    rw [hP]
    exact Finset.mem_singleton_self _
  obtain ⟨hp, hover⟩ := (IsDedekindDomain.mem_primesOverFinset_iff hv0 B).mp hm
  letI := hp
  letI := hover
  let w : HeightOneSpectrum B := ⟨P, hp, Ideal.ne_bot_of_liesOver_of_ne_bot hv0 P⟩
  exact constant_of_integral_of_rational_residue P
    (heightOne_linearPrime_constant_residue_surjective w 0 hf) hz.isIntegral

/-- The integral closure of the enlarged constant field inside the three-point field is precisely the constants. -/
theorem primePowerThreePointExtension_integralConstants : integralClosure E L = ⊥ := by
  apply bot_unique
  intro z hz
  exact Algebra.mem_bot.mpr (primePowerThreePointExtension_constantField p d n E c a z
    (show IsIntegral E z from hz).isAlgebraic)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

