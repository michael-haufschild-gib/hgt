import GaloisForLFunctions.RHTower.FokasLenellsCausalRationalEigenvectors
import GaloisForLFunctions.RHTower.FokasLenellsCauchyExtension

/-! Actual scalar Cauchy pairings for lower Hardy data and arbitrary bounded operators.
Literal L2 conjugation supplies the density of the holomorphic Cauchy transform;
no vector-valued analytic-family assumption is needed. -/
open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
local instance causalCauchyPairingLowerComplete : CompleteSpace (hardyL2ᗮ) :=
  hardyL2.isClosed_orthogonal.completeSpace_coe

/-- The globally defined Cauchy transform of literal conjugate L2 data, with the
normalization that makes upper-pole values exact rational-vector pairings. -/
def causalCauchyPairing (f : hardyL2ᗮ) (w : ℂ) : ℂ :=
  (2 * (Real.pi : ℂ) * I) * cauchyExtension (star f.val) w

/-- Upper-pole values of the scalar transform are exactly inner products with the
actual rational Cauchy eigenvectors in the original L2 space. -/
theorem causalCauchyPairing_eq_inner (f : hardyL2ᗮ) (w : {z : ℂ // 0 < z.im}) :
    causalCauchyPairing f w.val = inner ℂ f (causalCauchyEigenvector w) := by
  obtain ⟨u, rfl⟩ := causalHardyConjugation_surjective f
  change (2 * (Real.pi : ℂ) * I) * cauchyExtension (star (star u.val)) w.val =
    inner ℂ (causalHardyConjugation u)
      (causalHardyConjugation (lowerCauchyFeatureAt w.val w.property))
  rw [star_star, causalHardyConjugation_inner]
  have hs : 2 * (Real.pi : ℂ) * I ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
  calc
    (2 * (Real.pi : ℂ) * I) * cauchyExtension u.val w.val =
        ∫ x : ℝ, (u.val : ℝ → ℂ) x / ((x : ℂ) - w.val) := by
      unfold cauchyExtension
      rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]
    _ = inner ℂ (lowerCauchyFeatureAt w.val w.property) u :=
      (inner_lowerCauchyFeatureAt w.property u).symm
    _ = (starRingEnd ℂ) (inner ℂ u (lowerCauchyFeatureAt w.val w.property)) :=
      (inner_conj_symm (lowerCauchyFeatureAt w.val w.property) u).symm

/-- Every genuine lower Hardy L2 datum has a holomorphic scalar pairing off the real axis. -/
theorem analyticOnNhd_causalCauchyPairing (f : hardyL2ᗮ) :
    AnalyticOnNhd ℂ (causalCauchyPairing f) {w : ℂ | w.im ≠ 0} :=
  analyticOnNhd_const.mul (analyticOnNhd_cauchyExtension (star f.val))

/-- The same holomorphic scalar construction describes matrix elements of every
bounded L2 operator on the actual rational eigenvectors. -/
theorem causalCauchyPairing_adjoint (T : hardyL2ᗮ →L[ℂ] hardyL2ᗮ)
    (f : hardyL2ᗮ) (w : {z : ℂ // 0 < z.im}) :
    causalCauchyPairing (T.adjoint f) w.val = inner ℂ f (T (causalCauchyEigenvector w)) :=
  (causalCauchyPairing_eq_inner (T.adjoint f) w).trans
    (ContinuousLinearMap.adjoint_inner_left T (causalCauchyEigenvector w) f)

/-- The scalar Cauchy transform retains all original lower Hardy L2 data. -/
theorem causalCauchyPairing_injective : Function.Injective causalCauchyPairing := by
  intro f g h
  have hz : f - g = 0 := by
    apply (RHTower.topologicalClosure_span_eq_top_iff _).mp
      topologicalClosure_span_causalCauchyEigenvector_eq_top
    rintro v ⟨w, rfl⟩
    rw [inner_sub_left]
    apply sub_eq_zero.mpr
    exact (causalCauchyPairing_eq_inner f w).symm.trans
      ((congrFun h w.val).trans (causalCauchyPairing_eq_inner g w))
  exact sub_eq_zero.mp hz

end
end RHTower.FokasLenells
