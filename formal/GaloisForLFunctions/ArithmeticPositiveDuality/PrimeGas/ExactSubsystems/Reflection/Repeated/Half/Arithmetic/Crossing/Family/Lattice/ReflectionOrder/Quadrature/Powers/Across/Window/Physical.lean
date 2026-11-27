import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across.Window.Grid
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Channel

/-! # Finite-height minima of the two elementary divisor-channel readings -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across.Window

open Real
open PrimeCalibration (log_pos_prime)

/-- A prime's fraction of the sum of the two elementary energies. -/
def share (p q : Nat.Primes) := log p.val/(log p.val+log q.val)

/-- Successive candidate heights are separated by half a turn of the
sum of the two elementary phases. -/
def spacing (p q : Nat.Primes) := π/(log p.val+log q.val)

private theorem share_bounds (p q : Nat.Primes) : 0 < share p q ∧ share p q < 1 := by
  have hp := log_pos_prime p
  have hq := log_pos_prime q
  exact ⟨div_pos hp (add_pos hp hq),(div_lt_one (add_pos hp hq)).mpr (lt_add_of_pos_right _ hq)⟩

private theorem spacing_pos (p q : Nat.Primes) : 0 < spacing p q :=
  div_pos pi_pos (add_pos (log_pos_prime p) (log_pos_prime q))

private def normalized (p : Nat.Primes) (σ t : ℝ) :=
  |reading p 1 ⟨σ,t⟩| / (2*|sinh (radial p σ)|)

def observed (p q : Nat.Primes) (σ t : ℝ) := max (normalized p σ t) (normalized q σ t)

private theorem elementary (p : Nat.Primes) (σ t : ℝ) (off : σ≠1/2) :
    normalized p σ t=|cos (t*log p.val)| := by
  have hx : radial p σ ≠ 0 := mul_ne_zero (sub_ne_zero.mpr off) (log_pos_prime p).ne'
  have scale : 2*|sinh (radial p σ)| ≠ 0 :=
    mul_ne_zero (by norm_num) (abs_ne_zero.mpr (sinh_ne_zero.mpr hx))
  unfold normalized
  rw [reading_formula,abs_neg,abs_mul,abs_mul]
  simpa only [PNat.one_coe,Nat.cast_one,one_mul,abs_of_pos (by norm_num : (0 : ℝ)<2)]
    using mul_div_cancel_left₀ |cos (t*log p.val)| scale

private theorem phase_form (p q : Nat.Primes) (σ t : ℝ) (off : σ≠1/2) :
    observed p q σ t=signal (share p q) (t/spacing p q) := by
  have pos := (add_pos (log_pos_prime p) (log_pos_prime q)).ne'
  have a : π*(share p q*(t/spacing p q))=t*log p.val := by
    unfold share spacing
    field_simp [pos,pi_ne_zero]
  have b : π*((1-share p q)*(t/spacing p q))=t*log q.val := by
    unfold share spacing
    field_simp [pos,pi_ne_zero]
    ring
  rw [observed,elementary p σ t off,elementary q σ t off,signal,a,b]

/-- The least reading on the physical interval is attained and equals
the minimum of the first N+1 samples of a single rotation. -/
theorem physical_minimum (p q : Nat.Primes) (σ : ℝ) (off : σ≠1/2) (N : ℕ) :
    IsLeast (observed p q σ '' Set.Icc 0 ((N : ℝ)*spacing p q))
      (floorValue (share p q) N) := by
  have ds := spacing_pos p q
  obtain ⟨ha,hb⟩ := share_bounds p q
  constructor
  · obtain ⟨j,hit⟩ := attained (share p q) N
    refine ⟨(j.val : ℝ)*spacing p q,⟨mul_nonneg (Nat.cast_nonneg _) ds.le,?_⟩,?_⟩
    · exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (Nat.lt_succ_iff.mp j.isLt)) ds.le
    · rw [phase_form p q σ _ off,mul_div_cancel_right₀ _ ds.ne',at_integer,hit]
  · rintro _ ⟨t,⟨lo,hi⟩,rfl⟩
    rw [phase_form p q σ t off]
    exact lower ha hb N _ (div_nonneg lo ds.le) ((div_le_iff₀ ds).mpr hi)

/-- Every minimizing physical height lies on the sum-frequency grid;
the grid indices are precisely the minimizers of the finite rotation. -/
theorem physical_minimizers (p q : Nat.Primes) (σ t : ℝ) (off : σ≠1/2) (N : ℕ)
    (lo : 0 ≤ t) (hi : t ≤ (N : ℝ)*spacing p q) :
    observed p q σ t=floorValue (share p q) N ↔ ∃ j : Fin (N+1),
      t=(j.val : ℝ)*spacing p q ∧ sample (share p q) j.val=floorValue (share p q) N := by
  have ds := spacing_pos p q
  obtain ⟨ha,hb⟩ := share_bounds p q
  rw [phase_form p q σ t off,minimizers ha hb N _ (div_nonneg lo ds.le) ((div_le_iff₀ ds).mpr hi)]
  exact exists_congr fun j => and_congr_left fun _ => div_eq_iff ds.ne'

#print axioms physical_minimum
#print axioms physical_minimizers

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.ReflectionOrder.Quadrature.Powers.Across.Window
