import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Window
import GaloisForLFunctions.RHTower.StationaryPhaseWithCubicError

/-! # Angular resolution of a short terminal energy window -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn

open Real Finset Filter
open scoped Topology

/-- Unit-amplitude phase at a continuous cutoff. -/
def center (t x : ℝ) := (Circle.exp (-(t*log x)) : ℂ)

theorem center_norm (t x : ℝ) : ‖center t x‖=1 := Circle.norm_coe _

/-- Multiplying the upper label by a fixed factor switches the measured
phase to its antipode. Both cutoffs grow without bound. -/
theorem center_antipode {t x : ℝ} (ht : t≠0) (hx : 0<x) :
    center t (exp (π/t)*x) = -center t x := by
  rw [center,center,log_mul (exp_pos _).ne' hx.ne',log_exp,Circle.coe_exp,Circle.coe_exp]
  have turn : -(t*(π/t+log x)) = -π + -(t*log x) := by field_simp [ht]; ring
  rw [turn,Complex.ofReal_add,add_mul,Complex.exp_add,Complex.ofReal_neg,neg_mul,
    Complex.exp_neg,Complex.exp_pi_mul_I]
  simp

/-- Phases in a fixed multiplicative window differ from its endpoint
by at most the angular width of that window. -/
theorem phase_dist_center {c x : ℝ} (hc : 0<c) (hx : 2≤x) (hcx : 2≤c*x)
    (t : ℝ) {p : ℕ} (hp : p ∈ window c x) :
    ‖(phase t p : ℂ) - center t x‖ ≤ |t| * (-log c) := by
  obtain ⟨prime,lo,hi⟩ := (mem_window hx hcx).mp hp
  have pp := (Nat.cast_pos.mpr prime.pos : 0<(p:ℝ))
  have xp : 0<x := by linarith only [hx]
  have hu := log_le_log pp hi
  have hl := log_le_log (mul_pos hc xp) lo.le
  rw [log_mul hc.ne' xp.ne'] at hl
  have dist := _root_.RHTower.norm_cexp_mul_I_sub_le (-(t*log p)) (-(t*log x))
  rw [show -(t*log p) - -(t*log x) = t*(log x-log p) by ring,
    abs_mul,abs_of_nonneg (sub_nonneg.mpr hu)] at dist
  exact dist.trans (mul_le_mul_of_nonneg_left (by linarith only [hl]) (abs_nonneg t))

def packetSum (a t x : ℝ) := ∑ p ∈ primes (cutoff x), ((p : ℝ)^(a-1) : ℝ) • (phase t p : ℂ)

def windowSum (a t c x : ℝ) := ∑ p ∈ window c x, ((p : ℝ)^(a-1) : ℝ) • (phase t p : ℂ)

theorem windowSum_sub {c x : ℝ} (h : c*x ≤ x) (a t : ℝ) :
    windowSum a t c x = packetSum a t x - packetSum a t (c*x) :=
  sum_sdiff_eq_sub (cutoff_mono h)

/-- Finite angular localization survives the weighted average. -/
theorem window_dist_center {c x : ℝ} (hc : 0<c) (hx : 2≤x) (hcx : 2≤c*x) (a t : ℝ) :
    ‖windowSum a t c x - windowMass a c x • center t x‖ ≤
      windowMass a c x*(|t| * (-log c)) := by
  rw [windowSum,windowMass,sum_smul,←sum_sub_distrib,sum_mul]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro p hp
  rw [←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg (rpow_nonneg (Nat.cast_nonneg p) _)]
  exact mul_le_mul_of_nonneg_left (phase_dist_center hc hx hcx t hp)
    (rpow_nonneg (Nat.cast_nonneg p) _)

#print axioms center_norm
#print axioms center_antipode
#print axioms phase_dist_center
#print axioms windowSum_sub
#print axioms window_dist_center

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn
