import GaloisForLFunctions.HTGeometry.AnalyticPowerCoordinate
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Analysis.Analytic.Polynomial

open Polynomial Filter Topology Set
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- The reciprocal polynomial germ at infinity, written in the inverse source coordinate. -/
def polynomialReciprocalGerm (P : ℂ[X]) (w : ℂ) : ℂ :=
  w ^ P.natDegree * (P.reverse.eval w)⁻¹

/-- Monicity makes the reciprocal denominator an analytic unit at zero. -/
theorem analyticAt_polynomialReciprocalGerm {P : ℂ[X]} (hP : P.Monic) :
    AnalyticAt ℂ (polynomialReciprocalGerm P) 0 := by
  have hQ : AnalyticAt ℂ (fun w : ℂ => P.reverse.eval w) 0 := by
    simpa using (analyticAt_id : AnalyticAt ℂ (fun w : ℂ => w) 0).aeval_polynomial P.reverse
  have hQ0 : P.reverse.eval 0 = 1 := by
    rw [← coeff_zero_eq_eval_zero, coeff_zero_reverse, hP.leadingCoeff]
  exact (analyticAt_id.pow P.natDegree).mul (hQ.inv (by rw [hQ0]; exact one_ne_zero))

/-- The analytic ramification order at infinity is the exact polynomial degree. -/
theorem analyticOrderAt_polynomialReciprocalGerm {P : ℂ[X]} (hP : P.Monic) :
    analyticOrderAt (polynomialReciprocalGerm P) 0 = P.natDegree := by
  have hQ : AnalyticAt ℂ (fun w : ℂ => P.reverse.eval w) 0 := by
    simpa using (analyticAt_id : AnalyticAt ℂ (fun w : ℂ => w) 0).aeval_polynomial P.reverse
  have hQ0 : P.reverse.eval 0 = 1 := by
    rw [← coeff_zero_eq_eval_zero, coeff_zero_reverse, hP.leadingCoeff]
  apply (analyticAt_polynomialReciprocalGerm hP).analyticOrderAt_eq_natCast.mpr
  refine ⟨fun w => (P.reverse.eval w)⁻¹, hQ.inv (by rw [hQ0]; exact one_ne_zero), ?_, ?_⟩
  · simp only [hQ0, inv_one, ne_eq, one_ne_zero, not_false_eq_true]
  · exact Eventually.of_forall fun w => by simp [polynomialReciprocalGerm, smul_eq_mul]

/-- Exact reciprocal identity, requiring only a nonzero inverse source coordinate. -/
theorem polynomialReciprocalGerm_eq_inv_eval (P : ℂ[X]) {w : ℂ} (hw : w ≠ 0) :
    polynomialReciprocalGerm P w = (P.eval w⁻¹)⁻¹ := by
  letI : Invertible w⁻¹ := invertibleOfNonzero (inv_ne_zero hw)
  have he : P.reverse.eval w * (w ^ P.natDegree)⁻¹ = P.eval w⁻¹ := by
    simpa only [invOf_eq_inv, inv_inv, eval₂_id, inv_pow] using
      (Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) w⁻¹ P)
  rw [polynomialReciprocalGerm, ← he, mul_inv_rev, inv_inv]

/-- An actual monic polynomial has an analytic power coordinate at infinity. -/
theorem exists_polynomial_reciprocal_power_coordinate {P : ℂ[X]} (hP : P.Monic)
    (hd : 0 < P.natDegree) {U : Set ℂ} (hU : U ∈ 𝓝 (0 : ℂ)) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ,
      (0 : ℂ) ∈ e.source ∧ e.source ⊆ U ∧ e 0 = 0 ∧
      AnalyticOnNhd ℂ e e.source ∧ AnalyticOnNhd ℂ e.symm e.target ∧
      (∀ w ∈ e.source, deriv e w ≠ 0) ∧
      ∀ w ∈ e.source, w ≠ 0 → (e w) ^ P.natDegree = (P.eval w⁻¹)⁻¹ := by
  obtain ⟨e, he, heU, he0, hean, heinv, hed, hpow⟩ :=
    exists_analytic_power_coordinate (analyticAt_polynomialReciprocalGerm hP) hd
      (analyticOrderAt_polynomialReciprocalGerm hP) hU
  refine ⟨e, he, heU, he0, hean, heinv, hed, ?_⟩
  intro w hw hw0
  exact (hpow w hw).symm.trans (polynomialReciprocalGerm_eq_inv_eval P hw0)

end
end GaloisForLFunctions.HTGeometry
