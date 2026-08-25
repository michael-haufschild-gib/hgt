import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionDeterminantDegreePower
import GaloisForLFunctions.HTGeometry.ABHN.CentralDivisionDeterminantValueGroup
import GaloisForLFunctions.HTGeometry.ABHN.RationalFiniteLocalField
import GaloisForLFunctions.HTGeometry.ABHN.NonarchimedeanLocalFieldValuationSequence
import Mathlib.Data.ZMod.Basic

/-!
# Degree bounds for local division-algebra value groups

For a locally compact nonarchimedean normed field, normalize the norm valuation to an integer
valuation.  If a central division algebra has degree `n`, every regular determinant is an `n`-th
power while every determinant of a central scalar is an `n²`-th power.  Taking integer valuations
therefore embeds the relative determinant value quotient into `ℤ/nℤ`.

This proves `|Γ_A / Γ_F| ≤ n`, the degree bound needed with value--residue equality to force the
local identities `e = f = n`.
-/

namespace GaloisForLFunctions.HTGeometry.ABHN

noncomputable section

open scoped NormedField ValuativeRel

universe u

variable {F : Type u} [NontriviallyNormedField F] [CompleteSpace F]
  [IsUltrametricDist F] [LocallyCompactSpace F]

omit [CompleteSpace F] in
/-- Equality of normalized integer valuations on field units is equivalent to equality of their
norms. -/
theorem normedLocalField_tameVal_eq_iff_norm_eq (a b : Fˣ) :
    letI : ValuativeRel F := .ofValuation (NormedField.valuation (K := F))
    letI : (Valued.v : Valuation F NNReal).IsNontrivial := by
      change (NormedField.valuation (K := F)).IsNontrivial
      infer_instance
    letI : IsNonarchimedeanLocalField F :=
      isNonarchimedeanLocalField_of_valued_of_locallyCompact F NNReal
    Multiplicative.toAdd
          (tameValHom (nonarchimedeanLocalFieldIntValuation F) a) =
        Multiplicative.toAdd
          (tameValHom (nonarchimedeanLocalFieldIntValuation F) b) ↔
      ‖(a : F)‖ = ‖(b : F)‖ := by
  letI : ValuativeRel F := .ofValuation (NormedField.valuation (K := F))
  letI : (NormedField.valuation (K := F)).Compatible := .ofValuation _
  letI : (Valued.v : Valuation F NNReal).IsNontrivial := by
    change (NormedField.valuation (K := F)).IsNontrivial
    infer_instance
  letI : IsNonarchimedeanLocalField F :=
    isNonarchimedeanLocalField_of_valued_of_locallyCompact F NNReal
  let vint := nonarchimedeanLocalFieldIntValuation F
  letI : vint.Compatible := by
    constructor
    intro x y
    change x ≤ᵥ y ↔
      IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
          (ValuativeRel.valuation F x) ≤
        IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
          (ValuativeRel.valuation F y)
    constructor
    · intro h
      exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).toOrderIso.monotone
        ((Valuation.Compatible.vle_iff_le
          (v := ValuativeRel.valuation F) x y).mp h)
    · intro h
      apply (Valuation.Compatible.vle_iff_le
        (v := ValuativeRel.valuation F) x y).mpr
      exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).toOrderIso.le_iff_le.mp h
  have hequiv : (NormedField.valuation (K := F)).IsEquiv vint :=
    ValuativeRel.isEquiv (NormedField.valuation (K := F)) vint
  constructor
  · intro h
    have htame : tameValHom vint a = tameValHom vint b := h
    have hun : tameUnzero vint a = tameUnzero vint b := inv_injective htame
    have hvint : vint (a : F) = vint (b : F) := by
      rw [← coe_tameUnzero vint a, ← coe_tameUnzero vint b, hun]
    have hvnorm : NormedField.valuation (a : F) = NormedField.valuation (b : F) :=
      (Valuation.IsEquiv.eq_iff hequiv).mpr hvint
    exact congrArg (fun z : NNReal => (z : ℝ)) hvnorm
  · intro hnorm
    have hvnorm : NormedField.valuation (a : F) = NormedField.valuation (b : F) :=
      NNReal.eq hnorm
    have hvint : vint (a : F) = vint (b : F) :=
      (Valuation.IsEquiv.eq_iff hequiv).mp hvnorm
    have hun : tameUnzero vint a = tameUnzero vint b := by
      exact WithZero.coe_injective <| by
        rw [coe_tameUnzero vint a, coe_tameUnzero vint b, hvint]
    exact congrArg Multiplicative.toAdd <| by
      rw [tameValHom_eq, tameValHom_eq, hun]

variable {A : Type u} [DivisionRing A] [Algebra F A] [Module.Finite F A]
  [Algebra.IsCentral F A]

/-- Relative determinant value-group index is at most the degree of a finite central division
algebra over a locally compact nonarchimedean field. -/
theorem divisionAlgebraDeterminantValueQuotient_natCard_le_degree :
    Nat.card (DivisionAlgebraDeterminantValueQuotient (F := F) (A := A)) ≤
      divisionAlgebraDegree (F := F) (A := A) := by
  letI : ValuativeRel F := .ofValuation (NormedField.valuation (K := F))
  letI : (NormedField.valuation (K := F)).Compatible := .ofValuation _
  letI : (Valued.v : Valuation F NNReal).IsNontrivial := by
    change (NormedField.valuation (K := F)).IsNontrivial
    infer_instance
  letI : IsNonarchimedeanLocalField F :=
    isNonarchimedeanLocalField_of_valued_of_locallyCompact F NNReal
  let vint := nonarchimedeanLocalFieldIntValuation F
  let n := divisionAlgebraDegree (F := F) (A := A)
  letI : NeZero n := ⟨divisionAlgebraDegree_pos (F := F) (A := A) |>.ne'⟩
  let root : DivisionAlgebraDeterminantValueQuotient (F := F) (A := A) → Fˣ :=
    fun q => divisionAlgebraDeterminantDegreeRoot (F := F) (A := A)
      (divisionAlgebraDeterminantValueRepresentative q)
  let code : DivisionAlgebraDeterminantValueQuotient (F := F) (A := A) → ZMod n :=
    fun q => ((Multiplicative.toAdd (tameValHom vint (root q)) : ℤ) : ZMod n)
  have hcode : Function.Injective code := by
    intro q r hqr
    have hdiv : (n : ℤ) ∣
        Multiplicative.toAdd (tameValHom vint (root r)) -
          Multiplicative.toAdd (tameValHom vint (root q)) :=
      (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ n).mp hqr
    obtain ⟨k, hk⟩ := hdiv
    let ell : ℤ := -k
    let cu : Fˣ := nonarchimedeanLocalFieldUniformizerUnit F ^ ell
    let lhs : Fˣ := cu ^ (n * n)
    let rhs : Fˣ := (root q / root r) ^ n
    have hpi : Multiplicative.toAdd
        (tameValHom vint (nonarchimedeanLocalFieldUniformizerUnit F)) = 1 :=
      nonarchimedeanLocalFieldUniformizer_tameVal F
    have htame : Multiplicative.toAdd (tameValHom vint lhs) =
        Multiplicative.toAdd (tameValHom vint rhs) := by
      simp [lhs, rhs, cu, hpi]
      dsimp [ell]
      linear_combination (n : ℤ) * hk
    have hnorm : ‖(lhs : F)‖ = ‖(rhs : F)‖ :=
      (normedLocalField_tameVal_eq_iff_norm_eq (F := F) lhs rhs).mp htame
    change ‖(((cu ^ (n * n) : Fˣ) : F))‖ =
      ‖((((root q / root r) ^ n : Fˣ) : F))‖ at hnorm
    have hnorm' : ‖(cu : F)‖ ^ (n * n) =
        ‖((((root q / root r) ^ n : Fˣ) : F))‖ := by
      simpa only [Units.val_pow_eq_pow_val, norm_pow] using hnorm
    have habs : ‖Algebra.norm F
        (((baseUnitsToDivisionAlgebraUnits (F := F) (A := A) cu) : Aˣ) : A)‖ =
      ‖Algebra.norm F
        (((divisionAlgebraDeterminantValueRepresentative q /
          divisionAlgebraDeterminantValueRepresentative r : Aˣ)) : A)‖ := by
      calc
        ‖Algebra.norm F
            (((baseUnitsToDivisionAlgebraUnits (F := F) (A := A) cu) : Aˣ) : A)‖ =
            ‖(cu : F)‖ ^ (n * n) := by
          rw [baseUnitsToDivisionAlgebraUnits_coe, Algebra.norm_algebraMap,
            norm_pow, divisionAlgebraDegree_mul_self (F := F) (A := A)]
        _ = ‖((((root q / root r) ^ n : Fˣ) : F))‖ := hnorm'
        _ = ‖Algebra.norm F
            (((divisionAlgebraDeterminantValueRepresentative q /
              divisionAlgebraDeterminantValueRepresentative r : Aˣ)) : A)‖ := by
          rw [Units.val_pow_eq_pow_val, Units.val_div_eq_div_val]
          have hrootq : Algebra.norm F
              (divisionAlgebraDeterminantValueRepresentative q : A) =
                (root q : F) ^ n :=
            divisionAlgebraDeterminantDegreeRoot_pow
              (F := F) (A := A) (divisionAlgebraDeterminantValueRepresentative q)
          have hrootr : Algebra.norm F
              (divisionAlgebraDeterminantValueRepresentative r : A) =
                (root r : F) ^ n :=
            divisionAlgebraDeterminantDegreeRoot_pow
              (F := F) (A := A) (divisionAlgebraDeterminantValueRepresentative r)
          have hndiv : Algebra.norm F
              ((divisionAlgebraDeterminantValueRepresentative q : A) /
                (divisionAlgebraDeterminantValueRepresentative r : A)) =
              Algebra.norm F (divisionAlgebraDeterminantValueRepresentative q : A) /
                Algebra.norm F (divisionAlgebraDeterminantValueRepresentative r : A) := by
            simp only [div_eq_mul_inv, map_mul, Algebra.norm_inv]
          apply congrArg norm
          rw [show (((divisionAlgebraDeterminantValueRepresentative q /
              divisionAlgebraDeterminantValueRepresentative r : Aˣ)) : A) =
                (divisionAlgebraDeterminantValueRepresentative q : A) /
                  (divisionAlgebraDeterminantValueRepresentative r : A) by
              simp [div_eq_mul_inv], hndiv, hrootq, hrootr, div_pow]
    have hker : divisionAlgebraDeterminantValueRepresentative q /
        divisionAlgebraDeterminantValueRepresentative r ∈
          divisionAlgebraDeterminantValueKernel (F := F) (A := A) := by
      rw [divisionAlgebraDeterminantValueKernel, Subgroup.mem_comap,
        divisionAlgebraBaseDeterminantValueSubgroup, MonoidHom.mem_range]
      refine ⟨cu, ?_⟩
      apply Units.ext
      apply NNReal.eq
      exact habs
    rw [← divisionAlgebraDeterminantValueRepresentative_mk q,
      ← divisionAlgebraDeterminantValueRepresentative_mk r]
    exact QuotientGroup.eq_iff_div_mem.mpr hker
  letI : Fintype (DivisionAlgebraDeterminantValueQuotient (F := F) (A := A)) :=
    Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  calc
    Fintype.card (DivisionAlgebraDeterminantValueQuotient (F := F) (A := A)) ≤
        Fintype.card (ZMod n) := Fintype.card_le_of_injective code hcode
    _ = n := ZMod.card n

end

end GaloisForLFunctions.HTGeometry.ABHN
