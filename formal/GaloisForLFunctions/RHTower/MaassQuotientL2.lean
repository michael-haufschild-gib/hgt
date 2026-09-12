import GaloisForLFunctions.RHTower.IntegralSubgroupFiniteCovolume
import GaloisForLFunctions.RHTower.IntegralSubgroupUnitaryRepresentation
import GaloisForLFunctions.RHTower.MaassCongruenceL2

/-!
# The actual congruence Maass vector in the quotient Hilbert representation

The literal inverse lift descends to G/Gamma. Cusp decay gives global boundedness,
and the constructed finite quotient measure gives L2 admission. Full support
and continuity prove injectivity and nonvanishing. Actual unitary translations
act on this representative, and the actual stabilizer fixes the resulting vector.

This applies to every real eigenvalue and every positive principal congruence
level. All-order generator domains and identification with the completed model
remain separate analytic obligations. No spectral-gap estimate is asserted.
-/

open MeasureTheory UpperHalfPlane Filter Topology
namespace GaloisForLFunctions.RHTower
noncomputable section

/-- The actual inverse lift on the left-coset quotient. -/
def maassInvariantQuotientLift (Γ : Subgroup SL2R)
    (f : upperHalfPlaneInvariantFunctions Γ) : SL2R ⧸ Γ → ℂ :=
  Quotient.lift (fun g : SL2R => f.1 (g⁻¹ • UpperHalfPlane.I)) (by
    intro a b hab
    have h := f.2 ⟨a⁻¹ * b, QuotientGroup.leftRel_apply.mp hab⟩ (b⁻¹ • UpperHalfPlane.I)
    simpa only [← mul_smul, mul_inv_cancel_right] using h)

@[simp] theorem maassInvariantQuotientLift_mk (Γ : Subgroup SL2R)
    (f : upperHalfPlaneInvariantFunctions Γ) (g : SL2R) :
    maassInvariantQuotientLift Γ f (QuotientGroup.mk g) = f.1 (g⁻¹ • UpperHalfPlane.I) := rfl

@[simp] theorem maassInvariantQuotientLift_section (Γ : Subgroup SL2R)
    (f : upperHalfPlaneInvariantFunctions Γ) (z : ℍ) :
    maassInvariantQuotientLift Γ f (QuotientGroup.mk (UpperHalfPlane.toSL2R z)⁻¹) = f.1 z := by
  simp only [maassInvariantQuotientLift_mk, inv_inv, UpperHalfPlane.toSL2R_smul_I]

theorem maassInvariantQuotientLift_injective (Γ : Subgroup SL2R) :
    Function.Injective (maassInvariantQuotientLift Γ) := by
  intro f g h
  apply Subtype.ext
  funext z
  simpa only [maassInvariantQuotientLift_section] using
    congrFun h (QuotientGroup.mk (UpperHalfPlane.toSL2R z)⁻¹)

private theorem maass_source_continuous {Γ : Subgroup SL2R} {lam : ℝ}
    (f : MaassCuspEigenform Γ lam) : Continuous f.1.1 := by
  apply continuous_iff_continuousAt.mpr
  intro z
  have h := (f.2.2.1.1.continuousOn.continuousAt
    (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)).comp UpperHalfPlane.continuous_coe.continuousAt
  simpa only [Function.comp_def, ofComplex_apply] using h

theorem maassInvariantQuotientLift_continuous {Γ : Subgroup SL2R} {lam : ℝ}
    (f : MaassCuspEigenform Γ lam) : Continuous (maassInvariantQuotientLift Γ f.1) :=
  ((maass_source_continuous f).comp (continuous_inv.smul continuous_const)).quotient_lift _

namespace MaassQuotientL2
variable (N : ℕ) {lam : ℝ}
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

abbrev quotientMeasure := integralSubgroupQuotientMeasure (CongruenceSubgroup.Gamma (N + 1))

def sourceFunction := maassInvariantQuotientLift (realImage (CongruenceSubgroup.Gamma (N + 1))) f.1

theorem sourceFunction_continuous : Continuous (sourceFunction N f) :=
  maassInvariantQuotientLift_continuous f

/-- Square integrability follows from proved cusp bounds and actual finite covolume. -/
theorem sourceFunction_memLp : MemLp (sourceFunction N f) 2 (quotientMeasure N) := by
  obtain ⟨C, hC⟩ := MaassCongruenceL2.source_bounded N f
  apply MemLp.of_bound (sourceFunction_continuous N f).aestronglyMeasurable C
  apply ae_of_all
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  exact hC (g⁻¹ • UpperHalfPlane.I)

/-- The specified original Maass form, now an actual vector of L2(G/Gamma). -/
def sourceLp : Lp ℂ 2 (quotientMeasure N) :=
  (sourceFunction_memLp N f).toLp (sourceFunction N f)

theorem sourceLp_ae : sourceLp N f =ᵐ[quotientMeasure N] sourceFunction N f :=
  (sourceFunction_memLp N f).coeFn_toLp

/-- Passing to almost-everywhere classes loses no information about the Maass source. -/
theorem sourceLp_injective : Function.Injective (sourceLp N (lam := lam)) := by
  intro f g h
  have hae : sourceFunction N f =ᵐ[quotientMeasure N] sourceFunction N g := by
    exact (sourceLp_ae N f).symm.trans (h ▸ sourceLp_ae N g)
  have hfun := Measure.eq_of_ae_eq hae (sourceFunction_continuous N f) (sourceFunction_continuous N g)
  exact Subtype.ext (maassInvariantQuotientLift_injective _ hfun)

/-- Original pointwise nonvanishing survives in the actual quotient Hilbert space. -/
theorem sourceLp_ne_zero : sourceLp N f ≠ 0 := by
  intro hz
  have hae : sourceFunction N f =ᵐ[quotientMeasure N] 0 :=
    (sourceLp_ae N f).symm.trans (hz ▸ Lp.coeFn_zero ℂ 2 (quotientMeasure N))
  have hfun := Measure.eq_of_ae_eq hae (sourceFunction_continuous N f) continuous_const
  apply f.2.1
  apply Subtype.ext
  funext z
  change f.1.1 z = 0
  have h := congrFun hfun (QuotientGroup.mk (UpperHalfPlane.toSL2R z)⁻¹)
  simpa only [sourceFunction, maassInvariantQuotientLift_section, Pi.zero_apply] using h

/-- Literal translated source agrees with right translation before inversion. -/
theorem sourceFunction_translate_mk (g h : SL2R) :
    sourceFunction N f (g⁻¹ • (QuotientGroup.mk h)) =
      f.1.1 ((h⁻¹ * g) • UpperHalfPlane.I) := by
  change f.1.1 ((g⁻¹ * h)⁻¹ • UpperHalfPlane.I) = _
  simp only [mul_inv_rev, inv_inv]

/-- The actual unitary group operator acts on the actual Maass representative. -/
theorem sourceLp_translate_ae (g : SL2R) :
    integralSubgroupUnitary (CongruenceSubgroup.Gamma (N + 1)) g (sourceLp N f)
      =ᵐ[quotientMeasure N] fun q => sourceFunction N f (g⁻¹ • q) := by
  exact (integralSubgroupUnitary_ae_eq _ g (sourceLp N f)).trans
    ((integralSubgroupQuotientMeasure_translation _ g⁻¹).quasiMeasurePreserving.ae
      (sourceLp_ae N f))

/-- The Maass vector in the genuine quotient Hilbert space is spherical. -/
theorem sourceLp_stabilizer_fixed (k : upperHalfPlaneStabilizer) :
    integralSubgroupUnitary (CongruenceSubgroup.Gamma (N + 1)) k (sourceLp N f) =
      sourceLp N f := by
  have hk : (k : SL2R) • UpperHalfPlane.I = UpperHalfPlane.I :=
    MulAction.mem_stabilizer_iff.mp k.2
  apply Lp.ext
  filter_upwards [sourceLp_translate_ae N f k, sourceLp_ae N f] with q hq hsource
  rw [hq, hsource]
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
  rw [sourceFunction_translate_mk]
  change f.1.1 ((h⁻¹ * k) • UpperHalfPlane.I) = f.1.1 (h⁻¹ • UpperHalfPlane.I)
  rw [mul_smul, hk]

end MaassQuotientL2
end
end GaloisForLFunctions.RHTower
