import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.TraceResponse
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.InteractionCrossFibre
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.PauliSectorRotations

/-! # Unit bond response at a calibrated coupling, for every exterior -/
open Matrix Real NormedSpace
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

/-- An exterior commuting with both probes cancels from the signal.
A quarter turn about the bond rotates the reporter into its paired input. -/
theorem calibrated_fieldTrace {n : ℕ} (E : selfAdjoint (Reg n)) (P Y : Reg n)
    (hEP : Commute E.val P) (hEY : Commute E.val Y)
    (hP : P*P=1) (hY : Y*Y=1) (ha : P*Y=-(Y*P))
    (t : ℝ) (ht : t≠0) :
    fieldTrace E.val P Y (Complex.I • (P*Y)) t (π/(4*t) : ℝ) = 1 := by
  let a := π/(4*t)
  let J : Reg n := (a:ℂ) • P
  have hat : a*t=π/4 := by dsimp only [a]; field_simp
  have hJ : Commute E.val J := hEP.smul_right (a:ℂ)
  have he : unitaryEvolution E.val (-t)*Y*unitaryEvolution E.val t=Y := by
    have h := unitaryEvolution_sub_mul E 0 t
    simp only [zero_sub,unitaryEvolution,zero_smul,exp_zero] at h
    have heY : Commute (unitaryEvolution E.val (-t)) Y :=
      ((hEY.smul_left (-Complex.I)).smul_left (-t)).exp_left
    rw [heY.eq,mul_assoc,h,mul_one]
  have hrot (s : ℝ) :
      unitaryEvolution J s = exp (((-Complex.I)*(a*s:ℝ)) • P) := by
    unfold unitaryEvolution
    change exp ((s:ℂ) • ((-Complex.I) • ((a:ℂ) • P))) = _
    simp only [smul_smul,Complex.ofReal_mul]
    congr 2
    ring
  have hspin := _root_.HTGeometry.ConstraintRelativity.conjugation_of_involution_anticommute
    P Y hP ha (π/4)
  rw [show 2*(π/4)=π/2 by ring,cos_pi_div_two,sin_pi_div_two] at hspin
  simp only [Complex.ofReal_zero,Complex.ofReal_one,zero_smul,zero_add,mul_one] at hspin
  have hsig : unitaryEvolution (E.val+J) (-t)*Y*unitaryEvolution (E.val+J) t =
      Complex.I • (P*Y) := by
    conv_lhs => lhs; lhs; rw [add_comm,unitaryEvolution_add_of_commuting hJ.symm]
    rw [unitaryEvolution_add_of_commuting hJ t]
    rw [show unitaryEvolution J (-t)*unitaryEvolution E.val (-t)*Y*
        (unitaryEvolution E.val t*unitaryEvolution J t) =
        unitaryEvolution J (-t)*(unitaryEvolution E.val (-t)*Y*unitaryEvolution E.val t)*
        unitaryEvolution J t by simp only [mul_assoc],he,hrot,hrot,mul_neg,hat]
    simpa only [Complex.ofReal_neg,mul_neg,neg_mul,neg_neg] using hspin
  have hsq : (Complex.I • (P*Y))*(Complex.I • (P*Y))=(1 : Reg n) := by
    have hyP : Y*P=-(P*Y) := by rw [ha,neg_neg]
    have hpyp : (P*Y)*(P*Y) = -1 := by
      rw [←mul_assoc, mul_assoc P Y P, hyP, mul_neg, ←mul_assoc, hP, one_mul, neg_mul, hY]
    rw [smul_mul_smul_comm,Complex.I_mul_I,hpyp,neg_one_smul,neg_neg]
  change (Fintype.card (Fin n → Bool) : ℂ)⁻¹ *
    (unitaryEvolution (E.val+J) (-t)*Y*unitaryEvolution (E.val+J) t*(Complex.I • (P*Y))).trace=1
  rw [hsig,hsq,Matrix.trace_one]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
