import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.SplitInfinityRegulatorDomain
import GaloisForLFunctions.HTGeometry.LoopEisenstein.LaurentIwahoriCriteria
import GaloisForLFunctions.HTGeometry.LoopEisenstein.LaurentMonomialTorus

/-!
# The tame pairing on a regulator orbit

At a split infinite place the tame pairing depends only on the signed
degrees. Multiplying both entries by a common constant detects the sum of
the two test degrees. The fundamental unit gives the remaining obstruction
to descent to Molla's regulator strip.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SplitInfinity
open HTGeometry HTGeometry.LoopEisenstein
variable {F : Type*} [Field F]

private abbrev D (F : Type*) [Field F] := tameDataOfValuation (laurentValuation F)

private theorem valuation_uniformizer : (D F).v (laurentXUnit F) = 1 := by
  have h : (((tameUnzero (laurentValuation F) (laurentXUnit F)) : Multiplicative ℤ) :
      WithZero (Multiplicative ℤ)) = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) :
      WithZero (Multiplicative ℤ)) := by
    rw [coe_tameUnzero,coe_laurentXUnit]
    exact LaurentSeries.valuation_single_zpow F 1
  change Multiplicative.toAdd (tameValHom (laurentValuation F) (laurentXUnit F)) = 1
  rw [tameValHom_toAdd,WithZero.coe_inj.mp h]
  rfl

/-- The Milnor valuation on a Laurent unit is the negative of its infinite degree. -/
theorem tame_valuation (x : LocalUnit F) : (D F).v x = -degree x := by
  have h := congrArg (D F).v (laurentUnit_monomial_factor F x)
  have hv := ((D F).mem_ker_iff _).1 (powerSeriesLaurentUnit_mem_kernel F (laurentUnitPowerSeriesPart F x))
  rw [(D F).v_mul,(D F).v_zpow,valuation_uniformizer,hv,mul_one,add_zero] at h
  simpa only [degree,neg_neg] using h

private theorem sign_neg_unit : sign (-1 : LocalUnit F) = -1 := by
  apply Units.ext
  simp [sign]

/-- Tame symbols are determined by degrees and leading coefficients, including
the parity factor when both orders are odd. -/
theorem tame_signed_degrees (x y : LocalUnit F) :
    laurentTameSymbol F x y =
      (-1 : Fˣ)^(degree x*degree y) * sign x^(-degree y) * sign y^(degree x) := by
  let z := (D F).symbolUnit x y
  have hv := ((D F).mem_ker_iff z).1 ((D F).symbolUnit_mem x y)
  rw [tame_valuation] at hv
  have ho : (z : LaurentSeries F).order = 0 := by simpa only [degree,neg_neg] using hv
  have ht : laurentTameSymbol F x y=sign z := by
    apply Units.ext
    rw [laurentTameSymbol_coe_eq_coeff_zero]
    change (z : LaurentSeries F).coeff 0=(z : LaurentSeries F).leadingCoeff
    rw [HahnSeries.leadingCoeff_eq,ho]
  rw [ht]
  simp only [z,TameData.symbolUnit,sign_mul,sign_pow,sign_neg_unit,tame_valuation,
    neg_mul_neg,neg_neg]

/-- The principal unit of either argument is undetectable at either place. -/
theorem angular_pairs_trivially (x y : LocalUnit F) :
    laurentTameSymbol F (angular x) y=1 ∧ laurentTameSymbol F y (angular x)=1 := by
  simp [tame_signed_degrees,(angular_invariants x).1,(angular_invariants x).2]

/-- Product of the two local symbols at the split infinite places. -/
def pairSymbol (x y : LocalUnit F × LocalUnit F) : Fˣ :=
  laurentTameSymbol F x.1 y.1 * laurentTameSymbol F x.2 y.2

private def symbolHom (y : LocalUnit F) : LocalUnit F →* Fˣ where
  toFun := fun x => laurentTameSymbol F x y
  map_one' := laurentTameSymbol_one_left F _
  map_mul' := fun a b => laurentTameSymbol_mul_left F a b y

/-- A change of representative separates into one constant character and one
fundamental-unit character. -/
theorem translate_symbol (e x y : LocalUnit F × LocalUnit F) (c : Fˣ) (j : ℤ) :
    pairSymbol (translate e x c j) y =
      c^(-(degree y.1+degree y.2)) * (pairSymbol e y)^j * pairSymbol x y := by
  have hp (p q : LocalUnit F) : laurentTameSymbol F (p^j) q = laurentTameSymbol F p q ^ j :=
    map_zpow (symbolHom q) p j
  have hc (q : LocalUnit F) : laurentTameSymbol F (monomial c 0) q=c^(-degree q) := by
    simp [tame_signed_degrees,degree_monomial,sign_monomial]
  simp only [pairSymbol,translate,laurentTameSymbol_mul_left,hc,hp,mul_zpow,neg_add,zpow_add]
  ac_rfl

/-- The fundamental-unit obstruction uses only the relative degrees, ratio
of leading coefficients and second-place leading sign of the generator. -/
theorem generator_symbol (R : ℕ+) (u v : LocalUnit F) (w : Fˣ) (y : LocalUnit F × LocalUnit F) :
    pairSymbol (generator R u v w) y =
      (-1 : Fˣ)^((R : ℤ)*(degree y.1-degree y.2)) *
      w^(-degree y.2) * (sign y.1 / sign y.2)^(R : ℤ) := by
  have h := generator_invariants R u v w
  simp only [pairSymbol,tame_signed_degrees,h.1,h.2.1,h.2.2.1,h.2.2.2,one_zpow,mul_one,
    mul_sub,zpow_sub,div_zpow,neg_mul,zpow_neg,div_eq_mul_inv]
  ac_rfl

/-- The pair character descends to every translate exactly when both
generators of the regulator action pair trivially. -/
theorem descends_iff (e y : LocalUnit F × LocalUnit F) :
    (∀ x c j, pairSymbol (translate e x c j) y = pairSymbol x y) ↔
      (∀ c : Fˣ, c^(degree y.1+degree y.2)=1) ∧ pairSymbol e y=1 := by
  simp_rw [translate_symbol]
  constructor
  · intro H
    constructor
    · intro c
      have h := H e c 0
      simpa [zpow_neg] using h
    · have h := H e 1 1
      simpa using h
  · rintro ⟨hc,he⟩ x c j
    simp [zpow_neg,hc,he]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SplitInfinity

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SplitInfinity.tame_valuation
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SplitInfinity.tame_signed_degrees
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SplitInfinity.angular_pairs_trivially
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SplitInfinity.translate_symbol
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SplitInfinity.generator_symbol
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SplitInfinity.descends_iff
