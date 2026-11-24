import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.OriginFormCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.OriginLocalParameters
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SelectedKoszulComponent
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.KoszulLatticeExact

/-! Over a reduced origin fibre point, the affine volume trivializes
the top form lattice. Consequently selected Koszul boundary values
for any generating set of the evaluation kernel are exactly the
forms with zero coefficient value. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.WH RingTheory.Sequence
open scoped GlobalTheory.CechDR

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [CharZero k] [Field F] [Field E]
  [Algebra k F] [Algebra k E] [Algebra F E] [IsScalarTower k F E]
  {d : ℕ} {x : Fin (d + 1) → F}

local notation "B" => rB k E x {0}
variable (h : IsFinCover k E x)
  [IsReduced ((rB k E x {0}) ⧸ originIdeal k E x)] (e : OriginFibrePoint k E x)

local notation "R" => loc B (Subtype.val e)
local notation "M" => chartFormLattice R d

private def localAffineVolume : M :=
  ⟨originAffineVolume k E x, omB_mono (le_loc B e.1) d originAffineVolume_mem⟩

/-- Scalar multiplication of affine volume identifies the top local
form lattice with the local ring. -/
def IsFinCover.localAffineVolumeEquiv : R ≃ₗ[R] M := by
  let f := LinearMap.toSpanSingleton R M (localAffineVolume e)
  apply LinearEquiv.ofBijective f
  constructor
  · intro a b hab
    apply Subtype.ext
    apply smul_left_injective E h.originAffineVolume_ne_zero
    exact congrArg Subtype.val hab
  · intro w
    obtain ⟨c, hc⟩ := h.exists_localOriginVolumeCoefficient e w w.property
    exact ⟨c, Subtype.ext hc.symm⟩

theorem IsFinCover.localAffineVolumeEquiv_coe (a : R) :
    (h.localAffineVolumeEquiv e a : DR k E) = (a : E) • originAffineVolume k E x := rfl

include h in
/-- Any weight ideal containing the origin ideal gives exactness up
to the dimension in the top-form Koszul complex. -/
theorem IsFinCover.localOriginKoszul_exact {ι : Type} [LinearOrder ι] (r : ι → R)
    (hr : Ideal.span (Set.range (localOriginCoordinate e)) ≤ Ideal.span (Set.range r))
    (m : ℤ) (hm : m < (d : ℤ)) :
    let C := acx (fun _ => omB k E R d) (fun l => Algebra.lsmul k k (DR k E) (r l : E))
    C.Z m ≤ C.B m := by
  let l := (List.finRange d).map (localOriginCoordinate e)
  have hreg : IsWeaklyRegular M l :=
    ((h.localAffineVolumeEquiv e).isWeaklyRegular_congr l).mp
      (h.weaklyRegular_localOriginCoordinates e)
  have hmem (a : R) (ha : a ∈ l) : a ∈ Ideal.span (Set.range r) := by
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp ha
    exact hr (Ideal.subset_span (Set.mem_range_self j))
  have hlen : m < (l.length : ℤ) := by simpa [l] using hm
  exact acx_lattice_exact_of_weaklyRegular (k := k) M r l hmem hreg m hlen

private theorem mem_iSup_map_smul_of_mem_span {ι : Type} (r : ι → R) {a : R}
    (ha : a ∈ Ideal.span (Set.range r)) (u : DR k E) (hu : u ∈ omB k E R d) :
    (a : E) • u ∈ ⨆ j, (omB k E R d).map (Algebra.lsmul k k (DR k E) (r j : E)) := by
  induction ha using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨j, rfl⟩ := hv
    exact le_iSup (fun j => (omB k E R d).map (Algebra.lsmul k k (DR k E) (r j : E))) j
      (Submodule.mem_map_of_mem hu)
  | zero => simp
  | add a b _ _ ha hb =>
    rw [Subalgebra.coe_add, add_smul]
    exact add_mem ha hb
  | smul b a _ ha =>
    rw [smul_eq_mul, Subalgebra.coe_mul, mul_smul]
    have hstable : (⨆ j, (omB k E R d).map
          (Algebra.lsmul k k (DR k E) (r j : E))) ≤
        (⨆ j, (omB k E R d).map (Algebra.lsmul k k (DR k E) (r j : E))).comap
          (Algebra.lsmul k k (DR k E) (b : E)) := by
      refine iSup_le fun j _ h => ?_
      obtain ⟨v, hv, rfl⟩ := h
      apply le_iSup (fun j => (omB k E R d).map (Algebra.lsmul k k (DR k E) (r j : E))) j
      exact ⟨(b : E) • v, smul_mem_omB b.property hv, smul_comm (r j : E) (b : E) v⟩
    exact hstable ha

include h in
/-- For selected weights spanning the origin ideal, the selected
boundary values are detected by vanishing at the fibre point. -/
theorem IsFinCover.mem_selectedBoundaryValues_iff_residue {ι : Type} [LinearOrder ι]
    (r : ι → R) (sel : Fin d ↪o ι)
    (hr : Ideal.span (Set.range fun j => r (sel j)) = RingHom.ker (locEval B e.1).toRingHom)
    (a : R) :
    (a : E) • originAffineVolume k E x ∈
      selectedBoundaryValues (omB k E R d)
        (fun l => Algebra.lsmul k k (DR k E) (r l : E)) sel ↔ locEval B e.1 a = 0 := by
  rw [selectedBoundaryValues_eq_iSup]
  constructor
  · intro ha
    have hg (j : Fin d) : locEval B e.1 (r (sel j)) = 0 := by
      have hx := Ideal.subset_span (Set.mem_range_self (f := fun j => r (sel j)) j)
      rwa [hr] at hx
    have hv : ∀ v ∈ (⨆ j : Fin d, (omB k E R d).map
        (Algebra.lsmul k k (DR k E) (r (sel j) : E))), ∃ w : M, (w : DR k E) = v ∧
          locEval B e.1 ((h.localAffineVolumeEquiv e).symm w) = 0 := by
      let N : Submodule k M :=
        LinearMap.ker ((locEval B e.1).toLinearMap.comp
          ((h.localAffineVolumeEquiv e).symm.toLinearMap.restrictScalars k))
      let i : M →ₗ[k] DR k E := (M).subtype.restrictScalars k
      have hN : (⨆ j : Fin d, (omB k E R d).map
        (Algebra.lsmul k k (DR k E) (r (sel j) : E))) ≤ N.map i := by
        refine iSup_le fun j _ h => ?_
        obtain ⟨v, hv, rfl⟩ := h
        let w : M := ⟨v, hv⟩
        refine ⟨r (sel j) • w, LinearMap.mem_ker.mpr ?_, rfl⟩
        change locEval B e.1 ((h.localAffineVolumeEquiv e).symm (r (sel j) • w)) = 0
        rw [map_smul, smul_eq_mul, map_mul, hg j, zero_mul]
      exact fun v hv => by
        obtain ⟨w, hw, he⟩ := hN hv
        exact ⟨w, he, hw⟩
    obtain ⟨w, hw, hz⟩ := hv _ ha
    have hw' : w = h.localAffineVolumeEquiv e a := Subtype.ext
      (hw.trans (h.localAffineVolumeEquiv_coe e a).symm)
    rwa [hw', LinearEquiv.symm_apply_apply] at hz
  · intro ha
    have hm : a ∈ Ideal.span (Set.range fun j => r (sel j)) := hr.symm ▸ ha
    exact mem_iSup_map_smul_of_mem_span e (fun j => r (sel j)) hm _
      (localAffineVolume e).property

end GlobalTheory.PD
