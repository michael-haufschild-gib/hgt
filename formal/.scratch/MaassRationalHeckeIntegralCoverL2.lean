import GaloisForLFunctions.RHTower.MaassRationalHeckeIntegralIntersection
import GaloisForLFunctions.RHTower.MaassQuotientL2

namespace GaloisForLFunctions.RHTower

open MeasureTheory UpperHalfPlane Filter Topology
open Matrix SpecialLinearGroup GeneralLinearGroup
open scoped MatrixGroups

noncomputable section

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
