import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCuspPacketDerivatives

/-!
Exact native Hilbert norms of actual modular cusp packets and their residuals.
-/

open MeasureTheory Set Filter Topology
open scoped ContDiff ComplexConjugate
namespace RHTower.D4BMModularCore
noncomputable section

/-- Native squared norm of every admitted cusp profile, over the whole flat line. -/
theorem CuspLogTest.operatorVector_norm_sq (f : CuspLogTest) :
    ‖(f.operatorVector : Space)‖^(2 : ℕ) = ∫ t : ℝ, ‖f.field t‖^(2 : ℕ) := by
  have he := f.operatorVector_inner f
  rw [inner_self_eq_norm_sq_to_K] at he
  have hi : (∫ t in Ioi (Real.log 2), conj (f.field t)*f.field t) =
      ((∫ t : ℝ, ‖f.field t‖^(2 : ℕ) : ℝ):ℂ) := by
    simp_rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]
    rw [integral_complex_ofReal]
    congr 1
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro t ht
    have hz : f.field t = 0 := image_eq_zero_of_notMem_tsupport
      (fun hs => ht (f.support hs))
    simp only [hz,norm_zero,zero_pow (by norm_num : 2 ≠ 0)]
  rw [hi,← RCLike.ofReal_pow] at he
  exact Complex.ofReal_injective he

private theorem scaledWindow_sq_integrable (j : ℕ) {L : ℝ} (hL : 0 < L) :
    Integrable (fun t : ℝ => cuspWindowDerivative j (cuspPacketCoordinate L t)^(2 : ℕ)) := by
  exact ((cuspWindowDerivative_sq_integrable j).comp_div hL.ne').comp_sub_right
    (cuspPacketCenter L)

/-- Translation and dilation of the original cutoff retain its exact derivative moments. -/
theorem cuspPacketWindow_integral (j : ℕ) {L : ℝ} (hL : 0 < L) :
    (∫ t : ℝ, cuspWindowDerivative j (cuspPacketCoordinate L t)^(2 : ℕ)) = L*cuspWindowMoment j := by
  change (∫ t : ℝ, (fun x : ℝ => cuspWindowDerivative j (x/L)^(2 : ℕ))
    (t-cuspPacketCenter L)) = _
  rw [integral_sub_right_eq_self (fun x : ℝ => cuspWindowDerivative j (x/L)^(2 : ℕ))
    (cuspPacketCenter L)]
  rw [Measure.integral_comp_div (fun x : ℝ => cuspWindowDerivative j x^(2 : ℕ)),abs_of_pos hL]
  rfl

/-- Exact squared norm of the actual modular packet, with its positive mass constant. -/
theorem cuspPacketVector_norm_sq (tau : ℝ) {L : ℝ} (hL : 0 < L) :
    ‖((cuspPacketTest tau L hL).operatorVector : Space)‖^(2 : ℕ) = L*cuspWindowMoment 0 := by
  rw [CuspLogTest.operatorVector_norm_sq]
  change (∫ t : ℝ, ‖cuspPacketField tau L t‖^(2 : ℕ)) = _
  simp_rw [cuspPacketField_norm_sq]
  exact cuspPacketWindow_integral 0 hL

/-- Exact residual norm of the original unbounded modular operator on an actual packet. -/
theorem cuspPacketVector_residual_norm_sq (tau : ℝ) {L : ℝ} (hL : 0 < L) :
    ‖energyOperator (cuspPacketTest tau L hL).operatorVector-
      ((5/4:ℂ)+(tau:ℂ)^(2 : ℕ)) • ((cuspPacketTest tau L hL).operatorVector : Space)‖^(2 : ℕ) =
      4*tau^(2 : ℕ)/L*cuspWindowMoment 1+L⁻¹^(3 : ℕ)*cuspWindowMoment 2 := by
  rw [CuspLogTest.shifted_operator,CuspLogTest.operatorVector_norm_sq]
  change (∫ t : ℝ, ‖(5/4-((5/4:ℂ)+(tau:ℂ)^(2 : ℕ)))*cuspPacketField tau L t-
    deriv (deriv (cuspPacketField tau L)) t‖^(2 : ℕ)) = _
  simp_rw [cuspPacketField_residual_norm_sq]
  change (∫ t : ℝ, 4*tau^(2 : ℕ)/L^(2 : ℕ)*cuspWindowDerivative 1 (cuspPacketCoordinate L t)^(2 : ℕ)+
    L⁻¹^(4 : ℕ)*cuspWindowDerivative 2 (cuspPacketCoordinate L t)^(2 : ℕ)) = _
  rw [integral_add ((scaledWindow_sq_integrable 1 hL).const_mul _)
    ((scaledWindow_sq_integrable 2 hL).const_mul _),integral_const_mul,integral_const_mul,
    cuspPacketWindow_integral 1 hL,cuspPacketWindow_integral 2 hL]
  field_simp

end
end RHTower.D4BMModularCore
