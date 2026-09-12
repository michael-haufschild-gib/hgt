import GaloisForLFunctions.RHTower.IntegralSubgroupQuotientMeasure
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The actual integral-subgroup quotient unitary representation

The constructed nonzero Haar quotient measure gives a genuine strongly continuous
unitary representation of SL2(R) on L2(G/Gamma), for every integral subgroup.
Its operators are literal inverse-translation pullbacks. This builds the ambient
Hilbert representation; admitting the original Maass lift and identifying its
norm with the already constructed finite-coset source still require the Iwasawa
measure comparison. No temperedness or spectral-gap claim is made here.
-/

open MeasureTheory Filter
namespace GaloisForLFunctions.RHTower

/-- Left regular action by genuine complex linear isometric automorphisms. -/
noncomputable def integralSubgroupUnitary (Γ : Subgroup SL2Z) (g : SL2R) :
    Lp ℂ 2 (integralSubgroupQuotientMeasure Γ) ≃ₗᵢ[ℂ]
      Lp ℂ 2 (integralSubgroupQuotientMeasure Γ) where
  toLinearEquiv := DistribMulAction.toLinearEquiv ℂ _ (DomMulAct.mk g⁻¹)
  norm_map' := DomMulAct.norm_smul_Lp _

/-- Identity acts identically. -/
theorem integralSubgroupUnitary_one (Γ : Subgroup SL2Z)
    (v : Lp ℂ 2 (integralSubgroupQuotientMeasure Γ)) :
    integralSubgroupUnitary Γ 1 v = v := by
  change DomMulAct.mk (1 : SL2R)⁻¹ • v = v
  simp only [inv_one, DomMulAct.mk_one, one_smul]

/-- The inverse in pullback gives the usual representation multiplication order. -/
theorem integralSubgroupUnitary_mul (Γ : Subgroup SL2Z) (g h : SL2R)
    (v : Lp ℂ 2 (integralSubgroupQuotientMeasure Γ)) :
    integralSubgroupUnitary Γ (g * h) v =
      integralSubgroupUnitary Γ g (integralSubgroupUnitary Γ h v) := by
  change DomMulAct.mk (g * h)⁻¹ • v = DomMulAct.mk g⁻¹ • (DomMulAct.mk h⁻¹ • v)
  simp only [mul_inv_rev, DomMulAct.mk_mul, mul_smul]

/-- The actual SL2(R) representation on the integral-subgroup quotient Hilbert space. -/
noncomputable def integralSubgroupRegularRepresentation (Γ : Subgroup SL2Z) :
    Representation ℂ SL2R (Lp ℂ 2 (integralSubgroupQuotientMeasure Γ)) where
  toFun g := (integralSubgroupUnitary Γ g).toLinearMap
  map_one' := by apply LinearMap.ext; intro v; exact integralSubgroupUnitary_one Γ v
  map_mul' g h := by apply LinearMap.ext; intro v; exact integralSubgroupUnitary_mul Γ g h v

/-- The operator is literal pullback by inverse left translation, almost everywhere. -/
theorem integralSubgroupUnitary_ae_eq (Γ : Subgroup SL2Z) (g : SL2R)
    (v : Lp ℂ 2 (integralSubgroupQuotientMeasure Γ)) :
    integralSubgroupUnitary Γ g v =ᵐ[integralSubgroupQuotientMeasure Γ]
      fun q => v (g⁻¹ • q) :=
  DomMulAct.smul_Lp_ae_eq (DomMulAct.mk g⁻¹) v

/-- Joint continuity, hence strong continuity, of the actual unitary action. -/
theorem integralSubgroupUnitary_continuous (Γ : Subgroup SL2Z) :
    Continuous (fun p : SL2R × Lp ℂ 2 (integralSubgroupQuotientMeasure Γ) =>
      integralSubgroupUnitary Γ p.1 p.2) := by
  change Continuous (fun p : SL2R × Lp ℂ 2 (integralSubgroupQuotientMeasure Γ) =>
    DomMulAct.mk p.1⁻¹ • p.2)
  haveI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  exact (DomMulAct.continuous_mk.comp continuous_fst.inv).smul continuous_snd

/-- The actual complex Hilbert inner product is preserved. -/
theorem integralSubgroupUnitary_inner (Γ : Subgroup SL2Z) (g : SL2R)
    (v w : Lp ℂ 2 (integralSubgroupQuotientMeasure Γ)) :
    inner ℂ (integralSubgroupUnitary Γ g v) (integralSubgroupUnitary Γ g w) = inner ℂ v w :=
  (integralSubgroupUnitary Γ g).inner_map_map v w

end GaloisForLFunctions.RHTower
