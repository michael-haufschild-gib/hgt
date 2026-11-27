import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.CutEcho
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.SelectedOverlap

/-! # Projective fitting error controls a normalized Heisenberg trace -/
open Matrix RHTower GaloisForLFunctions.RHTower
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity
open private conjugate_dist from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.CutEcho
noncomputable section
private abbrev Reg (N : ℕ) := Matrix (Fin N→Bool) (Fin N→Bool) ℂ

/-- A trace which vanishes on a circuit can have magnitude at most twice
the projective fitting error on the physical evolution, for contraction probes. -/
theorem missing_trace_bound {N : ℕ} (U V : Reg N) (hU : U∈unitary _) (hV : V∈unitary _)
    (P B : Reg N) (hP : ‖P‖≤1) (hB : ‖B‖≤1) (z : ℂ) (hz : ‖z‖=1)
    (hzero : (star V*P*V*B).trace=0) :
    ‖(star U*P*U*B).trace/(Fintype.card (Fin N→Bool):ℂ)‖≤2*‖U-z • V‖ := by
  let W := z • V
  have hW : ‖W‖≤1 := by simp only [W,norm_smul,hz,one_mul,CStarRing.norm_of_mem_unitary hV,le_refl]
  have hphase : star W*P*W=star V*P*V := by
    simp only [W,star_smul,Matrix.mul_smul,Matrix.smul_mul,smul_smul]
    rw [show z*star z=1 by simp [Complex.mul_conj',hz],one_smul]
  have he := conjugate_dist U W P (CStarRing.norm_of_mem_unitary hU).le hW hP
  rw [hphase] at he
  let X := star U*P*U
  let Y := star V*P*V
  have ht := norm_normalizedTrace_sub_le_l2OpNorm (X*B) (Y*B)
  change (Y*B).trace=0 at hzero
  rw [hzero,mul_zero,sub_zero,←sub_mul] at ht
  rw [div_eq_mul_inv,mul_comm (star U*P*U*B).trace]
  exact ht.trans ((norm_mul_le _ _).trans ((mul_le_mul_of_nonneg_left hB (norm_nonneg _)).trans
    ((mul_one _).le.trans he)))

#print axioms missing_trace_bound
end
end GaloisForLFunctions.HTGeometry.SpanningDensity
