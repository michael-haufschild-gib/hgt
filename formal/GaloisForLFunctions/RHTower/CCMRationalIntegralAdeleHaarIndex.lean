import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Comap
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import GaloisForLFunctions.RHTower.CCMRationalIntegralAdeleIndex

/-!
# Haar mass of integral finite-adele sublattices

The compact open subring of rational integral finite adeles is bundled as an additive subgroup.
Its pullback of normalized ambient Haar measure is translation invariant.  Combining the exact
arithmetic index theorem with the finite-index coset formula proves

`vol(n Ẑ̂) = n⁻¹`.

This is the measure-theoretic bridge needed to compute the topological Haar character of rational
scaling on the actual finite adele ring.
-/

noncomputable section

open MeasureTheory
open IsDedekindDomain

namespace GaloisForLFunctions
namespace RHTower

/-- Integral finite adeles as an additive subgroup of the actual finite adele ring. -/
noncomputable def ccmRationalIntegralFiniteAdelesAddSubgroup :
    AddSubgroup CCMRationalFiniteAdele where
  carrier := ccmRationalIntegralFiniteAdeles
  zero_mem' := fun _ ↦ zero_mem _
  add_mem' := fun hx hy v ↦ add_mem (hx v) (hy v)
  neg_mem' := fun hx v ↦ neg_mem (hx v)

@[simp]
theorem ccmRationalIntegralFiniteAdelesAddSubgroup_mem
    (x : CCMRationalFiniteAdele) :
    x ∈ ccmRationalIntegralFiniteAdelesAddSubgroup ↔
      ∀ v, x v ∈
        (CCMRationalLocalIntegers v : Set (CCMRationalLocalField v)) :=
  Iff.rfl

/-- Product of rational local integer rings identified with the integral finite-adele subgroup. -/
noncomputable def ccmRationalIntegralPiAddEquivIntegralFiniteAdeles :
    ((v : HeightOneSpectrum ℤ) → CCMRationalLocalIntegers v) ≃+
      ccmRationalIntegralFiniteAdelesAddSubgroup where
  toFun x := ⟨RestrictedProduct.structureMap
    (fun v : HeightOneSpectrum ℤ ↦ CCMRationalLocalField v)
    (fun v : HeightOneSpectrum ℤ ↦
      (CCMRationalLocalIntegers v : Set (CCMRationalLocalField v)))
    Filter.cofinite x, fun v ↦ (x v).2⟩
  invFun x := fun v ↦ ⟨x.1 v, x.2 v⟩
  left_inv _ := rfl
  right_inv x := by
    apply Subtype.ext
    apply RestrictedProduct.ext
    intro v
    rfl
  map_add' x y := by
    apply Subtype.ext
    apply RestrictedProduct.ext
    intro v
    rfl

/-- Multiplication by nonzero `n` has exact index `n` in the integral finite-adele subgroup. -/
theorem ccmRationalIntegralFiniteAdelesNSMul_index
    {n : ℕ} (hn : n ≠ 0) :
    (nsmulAddMonoidHom
      (α := ccmRationalIntegralFiniteAdelesAddSubgroup) n).range.index = n := by
  have hindex := AddSubgroup.index_map_equiv
    (nsmulAddMonoidHom
      (α := (v : HeightOneSpectrum ℤ) → CCMRationalLocalIntegers v) n).range
    ccmRationalIntegralPiAddEquivIntegralFiniteAdeles
  have hmap :
      AddSubgroup.map
        ccmRationalIntegralPiAddEquivIntegralFiniteAdeles.toAddMonoidHom
        (nsmulAddMonoidHom
          (α := (v : HeightOneSpectrum ℤ) → CCMRationalLocalIntegers v) n).range =
      (nsmulAddMonoidHom
        (α := ccmRationalIntegralFiniteAdelesAddSubgroup) n).range :=
    ccmRationalIntegralPiAddEquivIntegralFiniteAdeles.map_range_nsmulAddMonoidHom n
  change (AddSubgroup.map
      ccmRationalIntegralPiAddEquivIntegralFiniteAdeles.toAddMonoidHom
      (nsmulAddMonoidHom
        (α := (v : HeightOneSpectrum ℤ) → CCMRationalLocalIntegers v) n).range).index = _
    at hindex
  rw [hmap] at hindex
  exact hindex.trans (ccmRationalIntegralPiNSMulRange_index hn)

noncomputable instance ccmRationalIntegralFiniteAdelesCompactSpace :
    CompactSpace ccmRationalIntegralFiniteAdelesAddSubgroup :=
  isCompact_iff_compactSpace.mp ccmRationalIntegralFiniteAdeles_isCompact

/-- Ambient normalized Haar measure pulled back to the integral finite-adele subgroup. -/
noncomputable def ccmRationalIntegralFiniteAdelesHaar :
    Measure ccmRationalIntegralFiniteAdelesAddSubgroup :=
  ccmRationalFiniteAdeleHaar.comap
    ccmRationalIntegralFiniteAdelesAddSubgroup.subtype

noncomputable instance ccmRationalIntegralFiniteAdelesHaarIsAddLeftInvariant :
    ccmRationalIntegralFiniteAdelesHaar.IsAddLeftInvariant := by
  unfold ccmRationalIntegralFiniteAdelesHaar
  exact Measure.IsAddLeftInvariant.comap ccmRationalFiniteAdeleHaar
    (MeasurableEmbedding.subtype_coe
      ccmRationalIntegralFiniteAdeles_isOpen.measurableSet)

/-- The multiplication-by-`n` image is closed in the compact integral subgroup. -/
theorem ccmRationalIntegralFiniteAdelesNSMulRange_isClosed (n : ℕ) :
    IsClosed ((nsmulAddMonoidHom
      (α := ccmRationalIntegralFiniteAdelesAddSubgroup) n).range :
        Set ccmRationalIntegralFiniteAdelesAddSubgroup) := by
  apply IsCompact.isClosed
  change IsCompact (Set.range
    (fun x : ccmRationalIntegralFiniteAdelesAddSubgroup ↦ n • x))
  exact isCompact_range (continuous_const_smul n)

/-- The multiplication-by-`n` image is measurable in the integral subgroup. -/
theorem ccmRationalIntegralFiniteAdelesNSMulRange_measurableSet (n : ℕ) :
    MeasurableSet ((nsmulAddMonoidHom
      (α := ccmRationalIntegralFiniteAdelesAddSubgroup) n).range :
        Set ccmRationalIntegralFiniteAdelesAddSubgroup) :=
  (ccmRationalIntegralFiniteAdelesNSMulRange_isClosed n).measurableSet

@[simp]
theorem ccmRationalIntegralFiniteAdelesHaar_univ :
    ccmRationalIntegralFiniteAdelesHaar Set.univ = 1 := by
  calc
    ccmRationalIntegralFiniteAdelesHaar Set.univ =
        ccmRationalFiniteAdeleHaar
          (ccmRationalIntegralFiniteAdelesAddSubgroup.subtype '' Set.univ) := by
      exact Measure.comap_apply
        ccmRationalIntegralFiniteAdelesAddSubgroup.subtype Subtype.val_injective
        (fun s hs ↦
          (MeasurableEmbedding.subtype_coe
            ccmRationalIntegralFiniteAdeles_isOpen.measurableSet).measurableSet_image.mpr hs)
        ccmRationalFiniteAdeleHaar MeasurableSet.univ
    _ = ccmRationalFiniteAdeleHaar ccmRationalIntegralFiniteAdeles := by
      congr 1
      ext x
      constructor
      · rintro ⟨y, -, rfl⟩
        exact y.2
      · intro hx
        exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩
    _ = 1 := ccmRationalFiniteAdeleHaar_integral_subring

/-- Exact Haar mass inside the integral subgroup: the `n`-multiple lattice has mass `n⁻¹`. -/
theorem ccmRationalIntegralFiniteAdelesHaar_nsmulRange
    {n : ℕ} (hn : n ≠ 0) :
    ccmRationalIntegralFiniteAdelesHaar
        ((nsmulAddMonoidHom
          (α := ccmRationalIntegralFiniteAdelesAddSubgroup) n).range :
            Set ccmRationalIntegralFiniteAdelesAddSubgroup) =
      (n : ENNReal)⁻¹ := by
  letI : (nsmulAddMonoidHom
      (α := ccmRationalIntegralFiniteAdelesAddSubgroup) n).range.FiniteIndex :=
    ⟨by rw [ccmRationalIntegralFiniteAdelesNSMul_index hn]; exact hn⟩
  have hmeasure := AddSubgroup.index_mul_measure
    (nsmulAddMonoidHom
      (α := ccmRationalIntegralFiniteAdelesAddSubgroup) n).range
    (ccmRationalIntegralFiniteAdelesNSMulRange_measurableSet n)
    ccmRationalIntegralFiniteAdelesHaar
  rw [ccmRationalIntegralFiniteAdelesNSMul_index hn,
    ccmRationalIntegralFiniteAdelesHaar_univ] at hmeasure
  exact ENNReal.eq_inv_of_mul_eq_one_left (by simpa [mul_comm] using hmeasure)

/-- Ambient subset `n Ẑ̂` of rational finite adeles. -/
noncomputable def ccmRationalIntegralFiniteAdelesNSMulSet (n : ℕ) :
    Set CCMRationalFiniteAdele :=
  Set.range (fun x : ccmRationalIntegralFiniteAdelesAddSubgroup ↦
    n • (x.1 : CCMRationalFiniteAdele))

theorem ccmRationalIntegralFiniteAdelesSubtype_image_nsmulRange (n : ℕ) :
    ccmRationalIntegralFiniteAdelesAddSubgroup.subtype ''
        ((nsmulAddMonoidHom
          (α := ccmRationalIntegralFiniteAdelesAddSubgroup) n).range :
            Set ccmRationalIntegralFiniteAdelesAddSubgroup) =
      ccmRationalIntegralFiniteAdelesNSMulSet n := by
  ext y
  constructor
  · rintro ⟨x, ⟨z, hz⟩, rfl⟩
    refine ⟨z, ?_⟩
    rw [← hz]
    rfl
  · rintro ⟨z, rfl⟩
    refine ⟨n • z, ⟨z, ?_⟩, rfl⟩
    rfl

/-- Exact normalized ambient Haar mass of `n Ẑ̂ ⊂ ᵓ8_f`. -/
theorem ccmRationalFiniteAdeleHaar_integralSubring_nsmul
    {n : ℕ} (hn : n ≠ 0) :
    ccmRationalFiniteAdeleHaar
        (ccmRationalIntegralFiniteAdelesNSMulSet n) =
      (n : ENNReal)⁻¹ := by
  calc
    ccmRationalFiniteAdeleHaar
        (ccmRationalIntegralFiniteAdelesNSMulSet n) =
        ccmRationalFiniteAdeleHaar
          (ccmRationalIntegralFiniteAdelesAddSubgroup.subtype ''
            ((nsmulAddMonoidHom
              (α := ccmRationalIntegralFiniteAdelesAddSubgroup) n).range :
                Set ccmRationalIntegralFiniteAdelesAddSubgroup)) := by
      rw [ccmRationalIntegralFiniteAdelesSubtype_image_nsmulRange]
    _ = ccmRationalIntegralFiniteAdelesHaar
        ((nsmulAddMonoidHom
          (α := ccmRationalIntegralFiniteAdelesAddSubgroup) n).range :
            Set ccmRationalIntegralFiniteAdelesAddSubgroup) := by
      exact (Measure.comap_apply
        ccmRationalIntegralFiniteAdelesAddSubgroup.subtype Subtype.val_injective
        (fun s hs ↦
          (MeasurableEmbedding.subtype_coe
            ccmRationalIntegralFiniteAdeles_isOpen.measurableSet).measurableSet_image.mpr hs)
        ccmRationalFiniteAdeleHaar
        (ccmRationalIntegralFiniteAdelesNSMulRange_measurableSet n)).symm
    _ = (n : ENNReal)⁻¹ :=
      ccmRationalIntegralFiniteAdelesHaar_nsmulRange hn

end RHTower
end GaloisForLFunctions
