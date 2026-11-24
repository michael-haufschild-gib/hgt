import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.Arc
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.ClockSpectrum.AngularMetric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.RingTheory.Coprime.Lemmas

/-! # Resolved spectral phases at rational fractions of a circuit return -/

open Real Set
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.Subperiods
open ClockSpectrum
noncomputable section

private theorem separated_integer {u v : ℤ} {d j : ℕ} (hc : d.Coprime j)
    (h : u%(d:ℤ) ≠ v%(d:ℤ)) (k : ℤ) :
    1 ≤ |(((j:ℤ)*(u-v)+(d:ℤ)*k:ℤ):ℝ)| := by
  let m : ℤ := (j:ℤ)*(u-v)+(d:ℤ)*k
  have hm : m ≠ 0 := by
    intro he
    have hdiv : (d:ℤ) ∣ (j:ℤ)*(u-v) := ⟨-k,by dsimp only [m] at he; linarith only [he]⟩
    exact h (Int.modEq_iff_dvd.mpr (hc.isCoprime.dvd_of_dvd_mul_left hdiv)).symm
  have hpos := abs_pos.mpr hm
  change 1≤|(m:ℝ)|
  exact_mod_cast (show (1:ℤ)≤|m| by omega)

/-- Distinct winding residues give a pair of eigenphases separated at
every coprime subdivision. The winding errors in the original common arc
contribute only their difference to the loss of separation. -/
theorem divided_phase_separation {I : Type*} {w : I → ℝ} {t R : ℝ} {b : I} {z : I → ℤ}
    (hz : Anchored w t R b z) {d j : ℕ} (hd : 0<d) (hj : d.Coprime j)
    {i l : I} (hneq : z i%(d:ℤ) ≠ z l%(d:ℤ)) :
    4*(1-(j:ℝ)*R)/d ≤
      ‖expTurns ((j:ℝ)/d*t*w i)-expTurns ((j:ℝ)/d*t*w l)‖ := by
  let s := (j:ℝ)/d*t
  let A := 2*π*(s*w i)
  let B := 2*π*(s*w l)
  let e := t*(w i-w l)-((z i:ℝ)-(z l:ℝ))
  have he : |e|≤R := abs_le.mpr ⟨by dsimp only [e]; linarith only [(hz i).1,(hz l).2],
    by dsimp only [e]; linarith only [(hz i).2,(hz l).1]⟩
  obtain ⟨k,hk⟩ := exists_int_phaseGap A B
  let m : ℤ := (j:ℤ)*(z i-z l)+(d:ℤ)*k
  have hm : 1≤|(m:ℝ)| := separated_integer hj hneq k
  have hd' := Nat.cast_pos (α:=ℝ).mpr hd
  have hj' := Nat.cast_nonneg (α:=ℝ) j
  have heq : phaseGap A B=(2*π/(d:ℝ))*((m:ℝ)+(j:ℝ)*e) := by
    rw [hk]
    dsimp only [A,B,s,m,e]; push_cast; field_simp [hd'.ne']; ring
  have hdiff : 1-(j:ℝ)*R ≤ |(m:ℝ)+(j:ℝ)*e| := by
    have hh := abs_sub ((m:ℝ)+(j:ℝ)*e) ((j:ℝ)*e)
    rw [add_sub_cancel_right,abs_mul,abs_of_nonneg hj'] at hh
    linarith only [hh,hm,mul_le_mul_of_nonneg_left he hj']
  have hdist : circDist A B=(2*π/(d:ℝ))*|(m:ℝ)+(j:ℝ)*e| := by
    rw [circDist,heq,abs_mul,abs_of_nonneg (div_nonneg two_pi_pos.le hd'.le)]
  have hangle := mul_le_sin (x:=circDist A B/2) (div_nonneg (circDist_nonneg ..) zero_le_two)
    (div_le_div_of_nonneg_right (circDist_le_pi ..) zero_le_two)
  change _ ≤ ‖Complex.exp ((A:ℂ)*Complex.I)-Complex.exp ((B:ℂ)*Complex.I)‖
  rw [norm_expI_sub_eq_sin_circDist]
  apply le_trans _ (mul_le_mul_of_nonneg_left hangle zero_le_two)
  rw [hdist]
  calc 4*(1-(j:ℝ)*R)/d ≤ 4*|(m:ℝ)+(j:ℝ)*e|/d :=
         div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdiff (by norm_num)) hd'.le
       _ = _ := by field_simp [hd'.ne',pi_ne_zero]; ring

#print axioms divided_phase_separation
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.Subperiods
