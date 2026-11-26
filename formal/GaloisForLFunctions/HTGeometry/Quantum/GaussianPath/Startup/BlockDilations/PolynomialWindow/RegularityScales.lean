import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! # Logarithmic pattern cost and a positive fraction of forced wires -/

open Real Filter
namespace GaloisForLFunctions.HTGeometry.BlockDilations

/-- The logarithmic cost separates the Gaussian Jacobian, the permitted
number of costly bits, and the gain per regular packet. -/
theorem log_of_packet_count {p a : ℝ} (hp : 0<p) (ha : 0≤a)
    (b d k g : ℕ) (hk : k≤b) (hg : g≤b)
    (h : p*(2:ℝ)^b≤(1+a)^d*((3^g*4^(b-g):ℕ):ℝ)/(2:ℝ)^(b-k)) :
    log p≤(d:ℝ)*a+k*log 2-g*log (4/3) := by
  push_cast at h
  have hlog := log_le_log (mul_pos hp (by positivity)) h
  have hx : 0<1+a := by positivity
  have h4 : log 4=2*log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,log_pow]; norm_num
  have hratio : log (4/3)=2*log 2-log 3 := by rw [log_div (by norm_num) (by norm_num),h4]
  rw [log_mul hp.ne' (by positivity),log_div (by positivity) (by positivity),
    log_mul (by positivity) (by positivity),log_mul (by positivity) (by positivity)] at hlog
  simp only [log_pow,Nat.cast_sub hg,Nat.cast_sub hk,h4] at hlog
  have hx' : log (1+a)≤a := by simpa only [add_sub_cancel_left] using log_le_sub_one_of_pos hx
  rw [hratio]
  linarith only [hlog,mul_le_mul_of_nonneg_left hx' (Nat.cast_nonneg d)]

/-- A single positive fraction of the packet wires works for all large
packet lengths when the coupling norm is at most C times the square root
of the length and the local time shift is A divided by the length. -/
theorem exists_wire_fraction {A C : ℝ} (hA : 0<A) (hC : 0<C) :
    ∃ α>0, ∃ L₀>0, ∀ {L r : ℝ}, L₀≤L → r≤α*L →
      2*(5/16+1/32)+(A/L)*(C*sqrt L)*(sqrt 21+2+2*sqrt (21*(2*r)))<1 := by
  let P := A*C
  let d := sqrt 21+2
  let v := sqrt 42
  let z := 1/(32*P*v)
  have hP : 0<P := mul_pos hA hC
  have hd : 0<d := add_pos_of_nonneg_of_pos (sqrt_nonneg _) two_pos
  have hv : 0<v := sqrt_pos.mpr (by norm_num)
  have hz : 0<z := by dsimp only [z]; positivity
  have hbase : 0<16*P*d+1 := by positivity
  refine ⟨z^2,sq_pos_of_pos hz,(16*P*d+1)^2,sq_pos_of_pos hbase,?_⟩
  intro L r hL hr
  have hLp := (sq_pos_of_pos hbase).trans_le hL
  have hs := sqrt_pos.mpr hLp
  have hlarge : 16*P*d+1≤sqrt L := by
    simpa only [sqrt_sq hbase.le] using sqrt_le_sqrt hL
  have hroot : sqrt (21*(2*r))≤v*z*sqrt L := calc
    _ ≤ sqrt (42*(z^2*L)) := sqrt_le_sqrt (by linarith only [hr])
    _ = _ := by rw [sqrt_mul (by norm_num : (0:ℝ)≤42),sqrt_mul (sq_nonneg _),sqrt_sq hz.le,mul_assoc]
  have hscale : (A/L)*(C*sqrt L)=P/sqrt L := by
    dsimp only [P]
    field_simp [hLp.ne',hs.ne']
    nlinarith only [sq_sqrt hLp.le,
      congrArg (fun y : ℝ => A*C*y) (sq_sqrt hLp.le)]
  have hmain : P*d/sqrt L≤1/16 := (div_le_iff₀ hs).mpr (by linarith only [hlarge])
  have hzid : 2*P*v*z=1/16 := by dsimp only [z]; field_simp [hP.ne',hv.ne']; ring
  rw [hscale]
  change 2*(5/16+1/32)+(P/sqrt L)*(d+2*sqrt (21*(2*r)))<1
  calc
    _ ≤ 2*(5/16+1/32)+(P/sqrt L)*(d+2*(v*z*sqrt L)) := add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (add_le_add le_rfl (mul_le_mul_of_nonneg_left hroot zero_le_two))
        (div_nonneg hP.le hs.le))
    _ = 2*(5/16+1/32)+P*d/sqrt L+2*P*v*z := by field_simp [hs.ne']; ring
    _ < 1 := by rw [hzid]; linarith only [hmain]

#print axioms log_of_packet_count
#print axioms exists_wire_fraction
end GaloisForLFunctions.HTGeometry.BlockDilations
