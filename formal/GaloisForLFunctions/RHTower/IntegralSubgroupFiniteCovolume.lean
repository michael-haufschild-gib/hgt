import GaloisForLFunctions.RHTower.RealIwasawaMeasure
import GaloisForLFunctions.RHTower.IntegralSubgroupQuotientMeasure

/-!
# Finite covolume of actual integral congruence quotients

Modular reduction and finitely many integral cosets cover the real quotient by
right translates of the finite Iwasawa modular cell. Folding this cover proves
finite covolume without assuming that the subgroup is normal in SL(2,R).
The quotient measure has full support for every integral subgroup.
-/

open MeasureTheory Set UpperHalfPlane Topology
namespace GaloisForLFunctions.RHTower

noncomputable def integralQuotientCover (Γ : Subgroup SL2Z) : Set SL2R :=
  ⋃ a : SL2Z ⧸ Γ, (fun g : SL2R => g * (integralSL2ToReal a.out)⁻¹) ⁻¹'
    inverseModularCell

theorem integralQuotientCover_measurable (Γ : Subgroup SL2Z) :
    MeasurableSet (integralQuotientCover Γ) := by
  haveI : Countable SL2Z := inferInstanceAs (Countable (Subtype _))
  haveI : Countable (SL2Z ⧸ Γ) := by
    apply Set.countable_univ_iff.mp
    rw [← (QuotientGroup.mk_surjective (s := Γ)).range_eq]
    exact Set.countable_range _
  exact MeasurableSet.iUnion fun a => inverseModularCell_measurable.preimage
    (measurable_mul_const _)

theorem integralQuotientCover_projects (Γ : Subgroup SL2Z) :
    (QuotientGroup.mk : SL2R → SL2R ⧸ realImage Γ) '' integralQuotientCover Γ = univ := by
  apply eq_univ_iff_forall.mpr
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨A, hA⟩ := ModularGroup.exists_smul_mem_fd (g⁻¹ • UpperHalfPlane.I)
  change integralSL2ToReal A • (g⁻¹ • UpperHalfPlane.I) ∈ ModularGroup.fd at hA
  obtain ⟨γ, hγ⟩ := QuotientGroup.mk_out_eq_mul Γ A
  refine ⟨g * (integralSL2ToReal A)⁻¹ * integralSL2ToReal (QuotientGroup.mk A : SL2Z ⧸ Γ).out,
    mem_iUnion.mpr ⟨QuotientGroup.mk A, ?_⟩, ?_⟩
  · change ((g * (integralSL2ToReal A)⁻¹ *
      integralSL2ToReal (QuotientGroup.mk A : SL2Z ⧸ Γ).out) *
      (integralSL2ToReal (QuotientGroup.mk A : SL2Z ⧸ Γ).out)⁻¹)⁻¹ •
      UpperHalfPlane.I ∈ ModularGroup.fd
    simpa only [mul_inv_cancel_right, mul_inv_rev, inv_inv, mul_smul] using hA
  · rw [hγ, map_mul, ← mul_assoc, inv_mul_cancel_right]
    exact QuotientGroup.mk_mul_of_mem g ⟨γ, γ.2, rfl⟩

theorem integralQuotientCover_finite (Γ : Subgroup SL2Z) [Γ.FiniteIndex] :
    realSL2Haar (integralQuotientCover Γ) ≠ ⊤ := by
  have h := measure_biUnion_ne_top (μ := realSL2Haar)
    (s := (univ : Set (SL2Z ⧸ Γ))) (f := fun a =>
      (fun g : SL2R => g * (integralSL2ToReal a.out)⁻¹) ⁻¹' inverseModularCell)
    (Set.toFinite _) (fun a _ => by
      rw [measure_preimage_mul_right]
      exact inverseModularCell_haar_ne_top)
  simpa [integralQuotientCover] using h

instance integralSubgroupQuotientMeasure_finite (Γ : Subgroup SL2Z) [Γ.FiniteIndex] :
    IsFiniteMeasure (integralSubgroupQuotientMeasure Γ) := by
  constructor
  rw [← integralQuotientCover_projects Γ]
  exact (integralSubgroupQuotientMeasure_image_le Γ
    (integralQuotientCover_measurable Γ)).trans_lt (integralQuotientCover_finite Γ).lt_top

instance integralSubgroupQuotientMeasure_openPos (Γ : Subgroup SL2Z) :
    (integralSubgroupQuotientMeasure Γ).IsOpenPosMeasure where
  open_pos U hU hne := by
    intro hz
    have hFD := integralSubgroupFundamentalSet_isFundamentalDomain Γ
    have hpre := hFD.projection_respects_measure_apply (μ := integralSubgroupQuotientMeasure Γ) hU.measurableSet
    rw [hz] at hpre
    have hnull := hFD.measure_zero_of_invariant (QuotientGroup.mk ⁻¹' U)
        (fun γ => by
          have hγ : γ.1.unop ∈ realImage Γ := γ.2
          change (fun x : SL2R => x * γ.1.unop) '' (QuotientGroup.mk ⁻¹' U) =
            QuotientGroup.mk ⁻¹' U
          ext x
          simp only [mem_image, mem_preimage]
          constructor
          · rintro ⟨y, hy, rfl⟩
            simpa only [QuotientGroup.mk_mul_of_mem y hγ] using hy
          · intro hx
            refine ⟨x * γ.1.unop⁻¹, ?_, inv_mul_cancel_right x _⟩
            simpa only [QuotientGroup.mk_mul_of_mem x ((realImage Γ).inv_mem hγ)] using hx)
        hpre.symm
    exact (hU.preimage QuotientGroup.continuous_mk).measure_ne_zero realSL2Haar
      (hne.preimage QuotientGroup.mk_surjective) hnull

end GaloisForLFunctions.RHTower
