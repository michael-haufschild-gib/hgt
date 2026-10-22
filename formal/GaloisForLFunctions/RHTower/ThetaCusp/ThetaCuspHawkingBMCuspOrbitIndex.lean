import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspPeriodization
import GaloisForLFunctions.HTGeometry.ModularStripUnfolding

/-! Exact translation and coprime-row coordinates for the full projective modular orbit sum. -/
open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped MatrixGroups
namespace RHTower.D4BMModularCore
noncomputable section

/-- The original compact translation window sums to one at every real coordinate. -/
theorem cuspWindow_partition_all (x : ℝ) : (∑' n : ℤ, cuspWindow (x+n)) = 1 := by
  let n : ℤ := -⌊x+(1/2:ℝ)⌋
  have hx : |x+(n:ℝ)| ≤ 1/2 := by
    dsimp [n]
    push_cast
    apply abs_le.mpr
    constructor <;> linarith [Int.floor_le (x+(1/2:ℝ)),Int.lt_floor_add_one (x+(1/2:ℝ))]
  have he : (∑' m : ℤ, cuspWindow ((x+(n:ℝ))+m)) = ∑' m : ℤ, cuspWindow (x+m) := by
    calc
      _ = ∑' m : ℤ, cuspWindow (x+((n+m:ℤ):ℝ)) := by
        apply tsum_congr
        intro m
        congr 1
        push_cast
        ring
      _ = _ := (Equiv.addLeft n).tsum_eq (fun m : ℤ => cuspWindow (x+m))
  rw [← he]
  exact cuspWindow_partition _ hx

private def translationIndex (n : ℤ) : translationSubgroup :=
  ⟨cuspTranslation n, by
    change (QuotientGroup.mk (T^n) : PSL2Z) ∈ Subgroup.zpowers psl2zT
    rw [QuotientGroup.mk_zpow]
    exact Subgroup.zpow_mem_zpowers _ _⟩

/-- Unique coordinates retain one coprime bottom row and every integer translation. -/
def cuspOrbitEquiv : (gammaSetHalf × ℤ) ≃ PSL2Z :=
  Equiv.ofBijective (fun p => cuspTranslation p.2 * halfRep p.1) (by
    constructor
    · intro p r he
      obtain ⟨hn,hv⟩ := translation_mul_halfRep_injective
        (translationIndex p.2) (translationIndex r.2) p.1 r.1 he
      exact Prod.ext hv (cuspTranslation_injective (congrArg Subtype.val hn))
    · intro g
      obtain ⟨h,v,hg⟩ := exists_translation_mul_halfRep g
      obtain ⟨n,hn⟩ := Subgroup.mem_zpowers_iff.mp h.2
      refine ⟨(v,n),?_⟩
      change cuspTranslation n * halfRep v = g
      rw [cuspTranslation,QuotientGroup.mk_zpow]
      change psl2zT^n * halfRep v = g
      rw [hn]
      exact hg)

/-- The exact projective matrix represented by a row and a translation. -/
theorem cuspOrbitEquiv_apply (v : gammaSetHalf) (n : ℤ) :
    cuspOrbitEquiv (v,n) = cuspTranslation n * halfRep v := rfl

/-- These coordinates act by the actual matrix followed by its literal integer translation. -/
theorem cuspOrbitEquiv_smul (v : gammaSetHalf) (n : ℤ) (z : UpperHalfPlane) :
    cuspOrbitEquiv (v,n) • z = T^n • (gammaSetMatrix v.1 • z) := by
  rw [cuspOrbitEquiv_apply,mul_smul]
  simp only [cuspTranslation,halfRep,PSL2Z_mk_smul]

end
end RHTower.D4BMModularCore
