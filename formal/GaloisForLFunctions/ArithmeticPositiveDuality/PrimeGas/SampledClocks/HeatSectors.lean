import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CopyExchange.PermutationTrace
import GaloisForLFunctions.HTGeometry.LpInjectionCoordinates
import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanPhaseWeilBridge

/-!
# Heat on a measured sector of copy occupations

Zero extension identifies the accepted labels with a closed subspace of the
full tuple Hilbert space. On that subspace a heat realization is trace class
exactly when the absolute sum of the accepted heat weights converges.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks

open CopyExchange ContinuousLinearMap
open scoped Classical
variable {I : Type*} [Fintype I] (P : (I → ℕ+) → Prop)

def embed : LabelSpace {x // P x} →ₗᵢ[ℂ] LabelSpace (I → ℕ+) :=
  _root_.RHTower.lpScalarInjection Subtype.val Subtype.val_injective

abbrev Sector := (embed P).toLinearMap.range

instance sectorComplete : CompleteSpace (Sector P) :=
  (embed P).isometry.isClosedEmbedding.isClosed_range.completeSpace_coe

def sectorEquiv : LabelSpace {x // P x} ≃ₗᵢ[ℂ] Sector P := (embed P).equivRange

theorem sector_mem (f : LabelSpace (I → ℕ+)) : f ∈ Sector P ↔ ∀ x, ¬P x → f x = 0 := by
  have miss (x : I → ℕ+) (hx : ¬P x) : x ∉ Set.range (Subtype.val : {x // P x} → _) := by
    rintro ⟨u,rfl⟩
    exact hx u.property
  constructor
  · rintro ⟨g,rfl⟩ x hx
    exact _root_.RHTower.lpScalarInjection_coordinate_of_not_mem _ _ g x (miss x hx)
  · intro h
    let g := _root_.RHTower.lpCoordinatePullback (E := ℂ) (Subtype.val : {x // P x} → _) Subtype.val_injective f
    refine ⟨g,?_⟩
    apply lp.ext
    funext x
    by_cases hx : P x
    · exact _root_.RHTower.lpScalarInjection_coordinate _ _ g (⟨x,hx⟩ : {x // P x})
    · exact (_root_.RHTower.lpScalarInjection_coordinate_of_not_mem _ _ g x (miss x hx)).trans (h x hx).symm

private theorem embed_at (f : LabelSpace {x // P x}) (x : {x // P x}) :
    (sectorEquiv P f : LabelSpace (I → ℕ+)) x.val = f x :=
  _root_.RHTower.lpScalarInjection_coordinate Subtype.val Subtype.val_injective f x

private theorem read_at (v : Sector P) (x : {x // P x}) :
    (sectorEquiv P).symm v x = (v : LabelSpace (I → ℕ+)) x.val := by
  have h := embed_at P ((sectorEquiv P).symm v) x
  simpa only [LinearIsometryEquiv.apply_symm_apply] using h.symm

abbrev AbsoluteHeat (s : ℂ) := Summable fun x : {x // P x} => ‖wordHeat s x.val‖

private def half (s : {z : ℂ // AbsoluteHeat P z}) :
    LabelSpace {x // P x} →L[ℂ] LabelSpace {x // P x} :=
  HilbertSchmidt.diagOp (fun x : {x // P x} => wordHeat (s.val/2) x.val)
    (by simpa only [wordHeat_half_norm_sq] using s.property)

private theorem half_product_tc (s : {z : ℂ // AbsoluteHeat P z}) : (half P s ∘L half P s).IsTraceClass :=
  (HilbertSchmidt.isHilbertSchmidt_diagOp _ _).comp_isTraceClass
    (HilbertSchmidt.isHilbertSchmidt_diagOp _ _)

def sectorHeat (s : {z : ℂ // AbsoluteHeat P z}) : Sector P →L[ℂ] Sector P :=
  (sectorEquiv P).toLinearIsometry.toContinuousLinearMap ∘L (half P s ∘L half P s) ∘L
    (sectorEquiv P).symm.toLinearIsometry.toContinuousLinearMap

theorem sectorHeat_trace (s : {z : ℂ // AbsoluteHeat P z}) :
    opTrace (sectorHeat P s) = ∑' x : {x // P x}, wordHeat s.val x.val := by
  refine (_root_.RHTower.opTrace_unitaryConjugate_of_isTraceClass (sectorEquiv P).symm _ (half_product_tc P s)).trans ?_
  rw [half,HilbertSchmidt.opTrace_diagOp_comp]
  exact tsum_congr fun _ => by rw [← wordHeat_add,add_halves]

def HasSectorHeat (s : ℂ) : Prop :=
  ∃ T : Sector P →L[ℂ] Sector P, T.IsTraceClass ∧ ∀ (v : Sector P) (x : {x // P x}),
    (T v : LabelSpace (I → ℕ+)) x.val = wordHeat s x.val * (v : LabelSpace (I → ℕ+)) x.val

theorem sectorHeat_iff (s : ℂ) : HasSectorHeat P s ↔ AbsoluteHeat P s := by
  constructor
  · rintro ⟨T,hT,ha⟩
    let e := sectorEquiv P
    let S := e.symm.toLinearIsometry.toContinuousLinearMap ∘L T ∘L e.toLinearIsometry.toContinuousLinearMap
    have hS : S.IsTraceClass := _root_.RHTower.ccmIsTraceClass_unitaryConjugate e T hT
    have act (f : LabelSpace {x // P x}) (x : {x // P x}) : S f x = wordHeat s x.val * f x := by
      change (sectorEquiv P).symm (T (sectorEquiv P f)) x = _
      rw [read_at,ha,embed_at]
    obtain ⟨A,B,hA,hB,hAB⟩ := hS
    refine (summable_inner_diag_comp hA hB (HilbertSchmidt.lpBasis {x // P x})).norm.congr fun x => ?_
    rw [← hAB,HilbertSchmidt.lpBasis_apply,lp.inner_single_left]
    simp only [RCLike.inner_apply,map_one,mul_one,act,lp.single_apply_self]
  · intro h
    let z : {z : ℂ // AbsoluteHeat P z} := ⟨s,h⟩
    refine ⟨sectorHeat P z,_root_.RHTower.ccmIsTraceClass_unitaryConjugate (sectorEquiv P).symm _
      (half_product_tc P z),?_⟩
    intro v x
    change (sectorEquiv P ((half P z ∘L half P z) ((sectorEquiv P).symm v)) : LabelSpace (I → ℕ+)) x.val = _
    rw [embed_at,comp_apply,half,HilbertSchmidt.diagOp_apply,HilbertSchmidt.diagOp_apply,← mul_assoc,
      ← wordHeat_add,add_halves,read_at]

#print axioms sector_mem
#print axioms sectorHeat_trace
#print axioms sectorHeat_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks
