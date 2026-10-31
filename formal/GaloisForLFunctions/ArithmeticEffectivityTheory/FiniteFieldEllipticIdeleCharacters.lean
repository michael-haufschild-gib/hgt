import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticPlaceNormalization
import GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticAdeleHaar
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Multiplicative characters of the actual elliptic ideles

Finite adelic units have valuation one outside finitely many places. The
normalized product is therefore multiplicative, and the actual curve
product formula makes every complex power trivial on diagonal field units.
-/

namespace GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase
open IsDedekindDomain Function Filter
open scoped NNReal Topology WithZero WithZeroMulInt
noncomputable section

/-- Units of the actual full adele ring. -/
abbrev Ideles := Adelesˣ

private theorem finiteCompletionMagnitude_support (a : Ideles) :
    HasFiniteMulSupport (fun v : FinitePlace =>
      finiteCompletionMagnitude v ((a : Adeles).1 v)) := by
  have ha : IsUnit (a : Adeles).1 :=
    a.isUnit.map (RingHom.fst FiniteAdeles InfinityCompletion)
  have hv := (FiniteAdeleRing.isUnit_iff.mp ha).2
  have he : ∀ᶠ v in cofinite,
      finiteCompletionMagnitude v ((a : Adeles).1 v) = 1 := by
    filter_upwards [hv] with v hv
    change (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).toMonoidWithZeroHom
      ((a : Adeles).1 v) = 1 at hv
    simp only [finiteCompletionMagnitude, MonoidWithZeroHom.comp_apply, hv, map_one]
  exact Filter.eventually_cofinite.mp he

/-- Product of all actual normalized local magnitudes. -/
def ideleMagnitude : Ideles →* ℝ≥0 where
  toFun a := infinityCompletionMagnitude (a : Adeles).2 *
    ∏ᶠ v : FinitePlace, finiteCompletionMagnitude v ((a : Adeles).1 v)
  map_one' := by
    change infinityCompletionMagnitude 1 *
      (∏ᶠ v : FinitePlace, finiteCompletionMagnitude v (1 : v.adicCompletion K)) = 1
    simp only [map_one, finprod_one, mul_one]
  map_mul' a b := by
    change infinityCompletionMagnitude ((a : Adeles).2 * (b : Adeles).2) *
      (∏ᶠ v : FinitePlace,
        finiteCompletionMagnitude v ((a : Adeles).1 v * (b : Adeles).1 v)) = _
    simp only [map_mul]
    rw [finprod_mul_distrib (finiteCompletionMagnitude_support a) (finiteCompletionMagnitude_support b)]
    ring

/-- Every idele has strictly positive global magnitude. -/
theorem ideleMagnitude_pos (a : Ideles) : 0 < (ideleMagnitude a : ℝ) := by
  have hunit : IsUnit (ideleMagnitude a) := (Group.isUnit a).map ideleMagnitude
  exact_mod_cast (pos_iff_ne_zero.mpr (isUnit_iff_ne_zero.mp hunit) : (0 : ℝ≥0) < ideleMagnitude a)

/-- Diagonal field units, in the actual restricted adelic unit group. -/
def diagonalIdeles : Kˣ →* Ideles := Units.map adeleEmbedding.toMonoidHom

/-- The arithmetic product formula is precisely triviality of the idele magnitude on diagonal units. -/
theorem ideleMagnitude_diagonal (z : Kˣ) : ideleMagnitude (diagonalIdeles z) = 1 :=
  adelic_product_formula (Units.ne_zero z)

private theorem eq_one_of_mul_eq_one_of_le_one {a b : ℤᵐ⁰}
    (ha : a ≤ 1) (hb : b ≤ 1) (hab : a * b = 1) : a = 1 := by
  apply le_antisymm ha
  calc
    1 = a * b := hab.symm
    _ ≤ a * 1 := mul_le_mul_left' hb a
    _ = a := mul_one _

private theorem ideleMagnitude_eq_one_of_integral (a : Ideles)
    (ha : (a : Adeles) ∈ integralAdeles)
    (hi : ((a⁻¹ : Ideles) : Adeles) ∈ integralAdeles) : ideleMagnitude a = 1 := by
  have hmul : (a : Adeles) * ((a⁻¹ : Ideles) : Adeles) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hfinite (v : FinitePlace) :
      finiteCompletionMagnitude v ((a : Adeles).1 v) = 1 := by
    have he : (a : Adeles).1 v * ((a⁻¹ : Ideles) : Adeles).1 v = 1 :=
      congrArg (fun z : Adeles => z.1 v) hmul
    have hv : Valued.v ((a : Adeles).1 v) = 1 :=
      eq_one_of_mul_eq_one_of_le_one (ha.1 v) (hi.1 v)
        (by rw [← map_mul, he, map_one])
    change (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰).toMonoidWithZeroHom
      ((a : Adeles).1 v) = 1 at hv
    simp only [finiteCompletionMagnitude, MonoidWithZeroHom.comp_apply, hv, map_one]
  have hinfinity : infinityCompletionMagnitude (a : Adeles).2 = 1 := by
    have he : (a : Adeles).2 * ((a⁻¹ : Ideles) : Adeles).2 = 1 :=
      congrArg (fun z : Adeles => z.2) hmul
    have hv : Valued.v (a : Adeles).2 = 1 :=
      eq_one_of_mul_eq_one_of_le_one ha.2 hi.2
        (by rw [← map_mul, he, map_one])
    change (Valued.v : Valuation InfinityCompletion ℤᵐ⁰).toMonoidWithZeroHom
      (a : Adeles).2 = 1 at hv
    simp only [infinityCompletionMagnitude, MonoidWithZeroHom.comp_apply, hv, map_one]
  change infinityCompletionMagnitude (a : Adeles).2 *
    (∏ᶠ v : FinitePlace, finiteCompletionMagnitude v ((a : Adeles).1 v)) = 1
  simp only [hinfinity, hfinite, finprod_one, one_mul]

/-- The global magnitude is locally constant on an actual open idele-unit neighborhood. -/
theorem continuous_ideleMagnitude : Continuous ideleMagnitude := by
  apply continuous_of_continuousAt_one ideleMagnitude
  let V : Set Ideles := {a | (a : Adeles) ∈ integralAdeles ∧
    ((a⁻¹ : Ideles) : Adeles) ∈ integralAdeles}
  have hopen : IsOpen V :=
    (integralAdeles_isOpen.preimage Units.continuous_val).inter
      (integralAdeles_isOpen.preimage (Units.continuous_val.comp continuous_inv))
  have hone : (1 : Adeles) ∈ integralAdeles :=
    ⟨fun _ => one_mem _, one_mem _⟩
  have hmem : (1 : Ideles) ∈ V := by
    change ((1 : Ideles) : Adeles) ∈ integralAdeles ∧
      (((1 : Ideles)⁻¹ : Ideles) : Adeles) ∈ integralAdeles
    simpa only [inv_one, Units.val_one] using And.intro hone hone
  have heq : (fun _ : Ideles => (1 : ℝ≥0)) =ᶠ[𝓝 (1 : Ideles)] ideleMagnitude := by
    filter_upwards [hopen.mem_nhds hmem] with a ha
    exact (ideleMagnitude_eq_one_of_integral a ha.1 ha.2).symm
  change Tendsto ideleMagnitude (𝓝 (1 : Ideles)) (𝓝 (ideleMagnitude 1))
  rw [map_one]
  exact tendsto_const_nhds.congr' heq

/-- The complex character determined by a spectral parameter and the global magnitude. -/
def ideleCharacter (s : ℂ) : Ideles →* ℂ where
  toFun a := Complex.exp (s * (Real.log (ideleMagnitude a : ℝ) : ℂ))
  map_one' := by rw [map_one]; simp only [NNReal.coe_one, Real.log_one, Complex.ofReal_zero,
    mul_zero, Complex.exp_zero]
  map_mul' a b := by
    rw [map_mul, NNReal.coe_mul, Real.log_mul (ideleMagnitude_pos a).ne' (ideleMagnitude_pos b).ne',
      Complex.ofReal_add, mul_add, Complex.exp_add]

theorem ideleCharacter_ne_zero (s : ℂ) (a : Ideles) : ideleCharacter s a ≠ 0 :=
  Complex.exp_ne_zero _

/-- Spectral characters are continuous on the actual idele group. -/
theorem continuous_ideleCharacter (s : ℂ) : Continuous (ideleCharacter s) := by
  have hlog : Continuous (fun a : Ideles => Real.log (ideleMagnitude a : ℝ)) :=
    (NNReal.continuous_coe.comp continuous_ideleMagnitude).log
      (fun a => (ideleMagnitude_pos a).ne')
  exact Complex.continuous_exp.comp
    (continuous_const.mul (Complex.continuous_ofReal.comp hlog))

/-- Every spectral character is trivial on the actual diagonal field units. -/
theorem ideleCharacter_diagonal (s : ℂ) (z : Kˣ) :
    ideleCharacter s (diagonalIdeles z) = 1 := by
  change Complex.exp (s * (Real.log (ideleMagnitude (diagonalIdeles z) : ℝ) : ℂ)) = 1
  rw [ideleMagnitude_diagonal]
  simp only [NNReal.coe_one, Real.log_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]

/-- Two independent torus coordinates with their spectral characters. -/
def ideleTorusCharacter (s t : ℂ) : Ideles × Ideles →* ℂ where
  toFun a := ideleCharacter s a.1 * ideleCharacter t a.2
  map_one' := by
    change ideleCharacter s 1 * ideleCharacter t 1 = 1
    rw [map_one, map_one, one_mul]
  map_mul' a b := by
    change ideleCharacter s (a.1 * b.1) * ideleCharacter t (a.2 * b.2) =
      (ideleCharacter s a.1 * ideleCharacter t a.2) *
        (ideleCharacter s b.1 * ideleCharacter t b.2)
    rw [map_mul, map_mul]
    ring

theorem continuous_ideleTorusCharacter (s t : ℂ) :
    Continuous (ideleTorusCharacter s t) :=
  ((continuous_ideleCharacter s).comp continuous_fst).mul
    ((continuous_ideleCharacter t).comp continuous_snd)

theorem ideleTorusCharacter_diagonal (s t : ℂ) (z w : Kˣ) :
    ideleTorusCharacter s t (diagonalIdeles z, diagonalIdeles w) = 1 := by
  change ideleCharacter s (diagonalIdeles z) * ideleCharacter t (diagonalIdeles w) = 1
  rw [ideleCharacter_diagonal, ideleCharacter_diagonal, one_mul]

end
end GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase

#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.ideleMagnitude
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.ideleMagnitude_diagonal
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.ideleTorusCharacter_diagonal
#print axioms GaloisForLFunctions.ArithmeticEffectivityTheory.FiniteFieldEllipticBase.continuous_ideleCharacter
