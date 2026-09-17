import GaloisForLFunctions.RHTower.MaassRationalHeckeIntegralIntersection
import GaloisForLFunctions.RHTower.MaassQuotientL2

namespace GaloisForLFunctions.RHTower

open MeasureTheory UpperHalfPlane Filter Topology
open Matrix SpecialLinearGroup GeneralLinearGroup
open scoped MatrixGroups

noncomputable section

/-- Projection between raw subgroup quotient spaces induced by an inclusion. -/
def subgroupQuotientProjection {G : Type*} [Group G]
    (K Γ : Subgroup G) (hKΓ : K ≤ Γ) :
    G ⧸ K → G ⧸ Γ :=
  Quotient.lift (fun x => QuotientGroup.mk x) (by
    intro x y hxy
    apply Quotient.sound'
    change QuotientGroup.leftRel K x y at hxy
    rw [QuotientGroup.leftRel_apply] at hxy ⊢
    exact hKΓ hxy)

@[simp] theorem subgroupQuotientProjection_mk {G : Type*} [Group G]
    (K Γ : Subgroup G) (hKΓ : K ≤ Γ) (x : G) :
    subgroupQuotientProjection K Γ hKΓ (QuotientGroup.mk x) = QuotientGroup.mk x :=
  rfl

theorem subgroupQuotientProjection_surjective {G : Type*} [Group G]
    (K Γ : Subgroup G) (hKΓ : K ≤ Γ) :
    Function.Surjective (subgroupQuotientProjection K Γ hKΓ) := by
  intro q
  induction q using Quotient.inductionOn with
  | h x => exact ⟨QuotientGroup.mk x, rfl⟩

/-- A subgroup quotient projection is measurable for quotient measurable spaces. -/
theorem subgroupQuotientProjection_measurable {G : Type*} [Group G] [MeasurableSpace G]
    (K Γ : Subgroup G) (hKΓ : K ≤ Γ) :
    Measurable (subgroupQuotientProjection K Γ hKΓ) := by
  rw [QuotientGroup.measurable_from_quotient]
  change Measurable (fun x : G => (QuotientGroup.mk x : G ⧸ Γ))
  exact QuotientGroup.measurable_coe

/-- The rational common cover is contained in the principal integral source. -/
theorem rationalHeckeIntegralIntersection_le_principal (N : ℕ) (g : GL (Fin 2) ℚ) :
    rationalHeckeIntegralIntersection N g ≤ CongruenceSubgroup.Gamma (N + 1) :=
  inf_le_left

/-- The real common cover is contained in the real principal source. -/
theorem realImage_rationalHeckeIntegralIntersection_le_principal
    (N : ℕ) (g : GL (Fin 2) ℚ) :
    realImage (rationalHeckeIntegralIntersection N g) ≤
      realImage (CongruenceSubgroup.Gamma (N + 1)) :=
  Subgroup.map_mono (rationalHeckeIntegralIntersection_le_principal N g)

/-- The quotient projection of the common finite deck onto the principal source quotient. -/
def rationalHeckeIntegralCoverProjection (N : ℕ) (g : GL (Fin 2) ℚ) :
    SL2R ⧸ realImage (rationalHeckeIntegralIntersection N g) →
      SL2R ⧸ realImage (CongruenceSubgroup.Gamma (N + 1)) :=
  subgroupQuotientProjection _ _
    (realImage_rationalHeckeIntegralIntersection_le_principal N g)

@[simp] theorem rationalHeckeIntegralCoverProjection_mk (N : ℕ) (g : GL (Fin 2) ℚ)
    (x : SL2R) :
    rationalHeckeIntegralCoverProjection N g (QuotientGroup.mk x) = QuotientGroup.mk x :=
  rfl

theorem rationalHeckeIntegralCoverProjection_surjective (N : ℕ) (g : GL (Fin 2) ℚ) :
    Function.Surjective (rationalHeckeIntegralCoverProjection N g) :=
  subgroupQuotientProjection_surjective _ _
    (realImage_rationalHeckeIntegralIntersection_le_principal N g)

/-- The common-cover projection is measurable. -/
theorem rationalHeckeIntegralCoverProjection_measurable (N : ℕ) (g : GL (Fin 2) ℚ) :
    Measurable (rationalHeckeIntegralCoverProjection N g) :=
  subgroupQuotientProjection_measurable _ _
    (realImage_rationalHeckeIntegralIntersection_le_principal N g)

/-- Restrict a principal Maass cusp eigenform to the rational common cover. -/
def rationalHeckeIntegralCoverMaassRestrict (N : ℕ) {lam : ℝ} (g : GL (Fin 2) ℚ)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    MaassCuspEigenform (realImage (rationalHeckeIntegralIntersection N g)) lam :=
  ⟨⟨f.1.1, by
      intro γ z
      exact f.1.2 ⟨γ.val, Subgroup.map_mono (inf_le_left :
        rationalHeckeIntegralIntersection N g ≤ CongruenceSubgroup.Gamma (N + 1)) γ.2⟩ z⟩,
    by
      intro hzero
      apply f.2.1
      apply Subtype.ext
      funext z
      exact congrFun (congrArg Subtype.val hzero) z,
    f.2.2.1, f.2.2.2⟩

/-- The original source, represented on its rational common-cover quotient. -/
def rationalHeckeIntegralCoverSourceFunction (N : ℕ) {lam : ℝ} (g : GL (Fin 2) ℚ)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    SL2R ⧸ realImage (rationalHeckeIntegralIntersection N g) → ℂ :=
  maassInvariantQuotientLift _ (rationalHeckeIntegralCoverMaassRestrict N g f).1

/-- The common-cover source is pointwise the pullback of the principal quotient source. -/
theorem rationalHeckeIntegralCoverSourceFunction_eq_comp_projection
    (N : ℕ) {lam : ℝ} (g : GL (Fin 2) ℚ)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    rationalHeckeIntegralCoverSourceFunction N g f =
      MaassQuotientL2.sourceFunction N f ∘ rationalHeckeIntegralCoverProjection N g := by
  funext q
  induction q using Quotient.inductionOn with
  | h x => rfl

/-- The source function on the common cover is square-integrable. -/
theorem rationalHeckeIntegralCoverSourceFunction_memLp (N : ℕ) {lam : ℝ} (g : GL (Fin 2) ℚ)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    MemLp (rationalHeckeIntegralCoverSourceFunction N g f) 2
      (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)) := by
  letI : (rationalHeckeIntegralIntersection N g).FiniteIndex :=
    rationalHeckeIntegralIntersection_finiteIndex N g
  obtain ⟨C, hC⟩ := MaassCongruenceL2.source_bounded N f
  apply MemLp.of_bound
    (maassInvariantQuotientLift_continuous (rationalHeckeIntegralCoverMaassRestrict N g f)).aestronglyMeasurable C
  apply ae_of_all
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  change ‖f.1.1 (x⁻¹ • UpperHalfPlane.I)‖ ≤ C
  exact hC _

/-- Hilbert-space source vector on the rational common-cover quotient. -/
def rationalHeckeIntegralCoverSourceLp (N : ℕ) {lam : ℝ} (g : GL (Fin 2) ℚ)
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam) :
    Lp ℂ 2 (integralSubgroupQuotientMeasure (rationalHeckeIntegralIntersection N g)) :=
  (rationalHeckeIntegralCoverSourceFunction_memLp N g f).toLp
    (rationalHeckeIntegralCoverSourceFunction N g f)

end

end GaloisForLFunctions.RHTower
