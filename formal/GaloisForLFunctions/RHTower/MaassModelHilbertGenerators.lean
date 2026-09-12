import GaloisForLFunctions.RHTower.MaassModelQuotientL2
import GaloisForLFunctions.HTGeometry.L2DominatedDerivative

/-!
# Actual Hilbert generators of the Maass model map

The original quotient unitary action differentiates on every finite Maass
model vector to E+F, i(E-F), and iH. Global bounds on the actual model derivatives
supply the L2 majorant, and the one-parameter subgroup law propagates the proved
pointwise derivative to every time. Completion and full group intertwining
remain separate from these infinitesimal identities.
-/

open UpperHalfPlane MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.RHTower.MaassModelQuotientL2
open MaassSmooth
noncomputable section
variable (N : ℕ) (lam : SelbergExceptionalEigenvalue)
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam.1)

def translatedFunction (g : SL2R) (v : SphericalKFiniteModel)
    (q : SL2R ⧸ realImage (CongruenceSubgroup.Gamma (N+1))) : ℂ :=
  modelToBounded N lam f v (g⁻¹ • q)

theorem translatedFunction_mk (g h : SL2R) (v : SphericalKFiniteModel) :
    translatedFunction N lam f g v (QuotientGroup.mk h) = (modelToMaass lam f v).1 (h⁻¹*g) := by
  change modelToBounded N lam f v (QuotientGroup.mk (g⁻¹*h)) = _
  rw [modelToBounded_apply, mul_inv_rev, inv_inv]

theorem translatedFunction_memLp (g : SL2R) (v : SphericalKFiniteModel) :
    MemLp (translatedFunction N lam f g v) 2 (MaassQuotientL2.quotientMeasure N) :=
  MemLp.of_bound (((modelToBounded N lam f v).continuous).comp
    (continuous_const_smul g⁻¹)).aestronglyMeasurable ‖modelToBounded N lam f v‖
    (ae_of_all _ fun q => (modelToBounded N lam f v).norm_coe_le_norm (g⁻¹ • q))

theorem unitary_eq_translated_toLp (g : SL2R) (v : SphericalKFiniteModel) :
    integralSubgroupUnitary (CongruenceSubgroup.Gamma (N+1)) g (modelToLp N lam f v) =
      (translatedFunction_memLp N lam f g v).toLp (translatedFunction N lam f g v) := by
  apply Lp.ext
  have h := (integralSubgroupUnitary_ae_eq (CongruenceSubgroup.Gamma (N+1)) g
    (modelToLp N lam f v)).trans
    ((integralSubgroupQuotientMeasure_translation (CongruenceSubgroup.Gamma (N+1)) g⁻¹).quasiMeasurePreserving.ae (modelToLp_ae N lam f v))
  exact h.trans (translatedFunction_memLp N lam f g v).coeFn_toLp.symm

private theorem subgroup_derivative_all_times (p : ℝ → SL2R)
    (hp : ∀ t s, p (t+s) = p t*p s) (F D : SL2R → ℂ)
    (hD : ∀ g, HasDerivAt (fun t => F (g*p t)) (D g) 0) (g : SL2R) (t : ℝ) :
    HasDerivAt (fun s => F (g*p s)) (D (g*p t)) t := by
  have hh : HasDerivAt (fun r => F ((g*p t)*p r)) (D (g*p t)) (t-t) := by
    simpa only [sub_self] using hD (g*p t)
  have h := hh.scomp (h := fun s : ℝ => s-t) t ((hasDerivAt_id t).sub_const t)
  have he : (fun s => F ((g*p t)*p (s-t))) = fun s => F (g*p s) := by
    funext s
    rw [mul_assoc, ← hp, show t+(s-t) = s by rw [add_comm, sub_add_cancel]]
  simpa only [sub_self, one_smul, Function.comp_def, he] using h

private theorem modelToLp_curve_hasDerivAt (p : ℝ → SL2R) (hp0 : p 0 = 1)
    (hp : ∀ t s, p (t+s) = p t*p s) (D : Module.End ℂ SphericalKFiniteModel)
    (hD : ∀ v g, HasDerivAt (fun t => (modelToMaass lam f v).1 (g*p t))
      ((modelToMaass lam f (D v)).1 g) 0) (v : SphericalKFiniteModel) :
    HasDerivAt (fun t => integralSubgroupUnitary (CongruenceSubgroup.Gamma (N+1))
      (p t) (modelToLp N lam f v)) (modelToLp N lam f (D v)) 0 := by
  have h := HTGeometry.hasDerivAt_toLp_two_of_dominated (MaassQuotientL2.quotientMeasure N)
    (fun t => translatedFunction N lam f (p t) v)
    (fun t => translatedFunction N lam f (p t) (D v))
    (fun t => translatedFunction_memLp N lam f (p t) v)
    (fun t => translatedFunction_memLp N lam f (p t) (D v))
    (fun _ => ‖modelToBounded N lam f (D v)‖) (memLp_const _)
    (ae_of_all _ fun q => by
      obtain ⟨g,rfl⟩ := QuotientGroup.mk_surjective q
      intro t
      simp only [translatedFunction_mk]
      exact subgroup_derivative_all_times p hp _ _ (hD v) g⁻¹ t)
    (ae_of_all _ fun q t => (modelToBounded N lam f (D v)).norm_coe_le_norm _) 0
  simp_rw [← unitary_eq_translated_toLp] at h
  simpa only [hp0, integralSubgroupUnitary_one] using h

/-- The actual quotient-Hilbert diagonal generator is exactly the finite model operator E+F. -/
theorem modelToLp_diagonal_hasDerivAt (v : SphericalKFiniteModel) :
    HasDerivAt (fun t => integralSubgroupUnitary (CongruenceSubgroup.Gamma (N+1))
      (realPositiveDiagonalBorel (-t) : SL2R) (modelToLp N lam f v))
      (modelToLp N lam f
        ((sphericalPrincipalE ((2*lam.complementaryExponent : ℝ) : ℂ) +
          sphericalPrincipalF ((2*lam.complementaryExponent : ℝ) : ℂ)) v)) 0 := by
  apply modelToLp_curve_hasDerivAt N lam f
    (fun t => (realPositiveDiagonalBorel (-t) : SL2R))
    (by simp only [neg_zero, realPositiveDiagonalBorel_zero, OneMemClass.coe_one])
    (by intro t s; simp only [neg_add, realPositiveDiagonalBorel_add, Subgroup.coe_mul])
    _ (fun v g => modelToMaass_diagonal_hasDerivAt lam f v g) v

/-- The actual quotient-Hilbert compact generator is exactly iH on every finite model vector. -/
theorem modelToLp_rotation_hasDerivAt (v : SphericalKFiniteModel) :
    HasDerivAt (fun t => integralSubgroupUnitary (CongruenceSubgroup.Gamma (N+1))
      (realSphericalRotation t : SL2R) (modelToLp N lam f v))
      (modelToLp N lam f ((Complex.I • sphericalPrincipalH) v)) 0 := by
  apply modelToLp_curve_hasDerivAt N lam f
    (fun t => (realSphericalRotation t : SL2R))
    (by simp only [realSphericalRotation_zero, OneMemClass.coe_one])
    (by intro t s; exact congrArg Subtype.val (realSphericalRotation_add t s))
    (Complex.I • sphericalPrincipalH) ?_ v
  intro w g
  simpa only [LinearMap.smul_apply, map_smul, SetLike.val_smul, Pi.smul_apply, smul_eq_mul] using
    modelToMaass_rotation_hasDerivAt lam f w g

/-- The conjugated diagonal generator is exactly i(E-F) in the actual quotient Hilbert space. -/
theorem modelToLp_quarterDiagonal_hasDerivAt (v : SphericalKFiniteModel) :
    HasDerivAt (fun t => integralSubgroupUnitary (CongruenceSubgroup.Gamma (N+1))
      ((realSphericalRotation (Real.pi/4) : SL2R) * (realPositiveDiagonalBorel (-t) : SL2R) *
        (realSphericalRotation (Real.pi/4) : SL2R)⁻¹) (modelToLp N lam f v))
      (modelToLp N lam f ((Complex.I •
        (sphericalPrincipalE ((2*lam.complementaryExponent : ℝ) : ℂ) -
          sphericalPrincipalF ((2*lam.complementaryExponent : ℝ) : ℂ))) v)) 0 := by
  apply modelToLp_curve_hasDerivAt N lam f
    (fun t => (realSphericalRotation (Real.pi/4) : SL2R) *
      (realPositiveDiagonalBorel (-t) : SL2R) * (realSphericalRotation (Real.pi/4) : SL2R)⁻¹)
    (by simp only [neg_zero, realPositiveDiagonalBorel_zero, OneMemClass.coe_one,
      mul_one, mul_inv_cancel])
    (by
      intro t s
      simp only [neg_add, realPositiveDiagonalBorel_add, Subgroup.coe_mul]
      group)
    (Complex.I • (sphericalPrincipalE ((2*lam.complementaryExponent : ℝ) : ℂ) -
      sphericalPrincipalF ((2*lam.complementaryExponent : ℝ) : ℂ))) ?_ v
  intro w g
  simpa only [LinearMap.smul_apply, map_smul, SetLike.val_smul, Pi.smul_apply, smul_eq_mul] using
    modelToMaass_quarterDiagonal_hasDerivAt lam f w g

end
end GaloisForLFunctions.RHTower.MaassModelQuotientL2
