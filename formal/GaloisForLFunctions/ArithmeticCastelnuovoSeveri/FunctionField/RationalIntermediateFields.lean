import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FunctionField.KummerRationalSubcover
import GaloisForLFunctions.HTGeometry.IntermediateFieldComap
import Mathlib.FieldTheory.RatFunc.Luroth


/-!
# Rational intermediate subcovers

Lüroth's theorem transports through an explicit rational presentation.
Every intermediate Kummer field contained in the quotient-radical field
is therefore rational over the constant field.
-/

noncomputable section
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open Polynomial
open scoped nonZeroDivisors

/-- Every nonconstant intermediate field inside an explicitly rational field is rational. -/
def rationalIntermediateFieldEquiv {K L : Type*} [Field K] [Field L] [Algebra K L]
    (S : IntermediateField K L) (e : RatFunc K ≃ₐ[K] S)
    (E : IntermediateField K L) (hES : E ≤ S) (hE : E ≠ ⊥) : RatFunc K ≃ₐ[K] E := by
  let T := (E.comap S.val).comap e.toAlgHom
  have hm : T.map e.toAlgHom = E.comap S.val :=
    IntermediateField.map_comap_eq_self (fun x _ => e.surjective x)
  let eT : T ≃ₐ[K] E := ((IntermediateField.equivMap T e.toAlgHom).trans
    (IntermediateField.equivOfEq hm)).trans (GaloisForLFunctions.HTGeometry.comapValEquiv hES)
  have hT : T ≠ ⊥ := by
    intro h
    apply hE
    apply bot_unique
    intro x hx
    let t := eT.symm ⟨x, hx⟩
    have ht : (t : RatFunc K) ∈ (⊥ : IntermediateField K (RatFunc K)) := h ▸ t.property
    obtain ⟨a, ha⟩ := IntermediateField.mem_bot.mp ht
    have hta : algebraMap K T a = t := Subtype.ext ha
    have hxconst := congrArg eT hta
    change eT (algebraMap K T a) = eT (eT.symm ⟨x, hx⟩) at hxconst
    rw [eT.commutes, eT.apply_symm_apply] at hxconst
    exact IntermediateField.mem_bot.mpr ⟨a, congrArg Subtype.val hxconst⟩
  exact (RatFunc.Luroth.algEquiv (E := T) hT).trans eT

/-- Every intermediate Kummer subcover below the quotient-radical field is rational over constants. -/
def kummerIntermediateField_rationalEquiv {K : Type*} [Field K]
    (c : Kˣ) (b R n : ℕ)
    (E : IntermediateField (FractionRing K[X]) (KummerBranchField c b R n))
    (hE : E ≤ kummerBranchUnitSubfield c b R n) : FractionRing K[X] ≃ₐ[K] E := by
  let F := FractionRing K[X]
  let L := KummerBranchField c b R n
  let S := (kummerBranchUnitSubfield c b R n).restrictScalars K
  let E' := E.restrictScalars K
  let f : FractionRing K[X] ≃ₐ[K] RatFunc K :=
    (IsLocalization.algEquiv K[X]⁰ (FractionRing K[X]) (RatFunc K)).restrictScalars K
  let e : RatFunc K ≃ₐ[K] S := f.symm.trans (kummerBranchUnitSubfield_rationalEquiv c b R n)
  have hE' : E' ≠ ⊥ := by
    intro h
    have hy : algebraMap K[X] L X ∈ E' := by
      rw [IsScalarTower.algebraMap_apply K[X] F L]
      exact E.algebraMap_mem _
    rw [h, IntermediateField.mem_bot] at hy
    obtain ⟨a, ha⟩ := hy
    apply kummerBranchField_coordinate_transcendental c b R n
    rw [← ha]
    exact isAlgebraic_algebraMap a
  exact f.trans (rationalIntermediateFieldEquiv S e E' hE hE')

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
