import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Ordinary.Dilution

/-! # Convergent moving prime packets on the original integer labels -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Collisions

open Finset Filter Real
open scoped Topology

/-- Elementary mass of one natural label, zero outside the finite prime packet. -/
def packetTerm (b : ℝ) (N n : ℕ) :=
  if n∈primes (cutoff N) then (n:ℝ)^(b-1) else 0

def totalTerm (b : ℝ) (n : ℕ) := if n.Prime then (n:ℝ)^(b-1) else 0

theorem packet_nonneg (b : ℝ) (N n : ℕ) : 0 ≤ packetTerm b N n := by
  unfold packetTerm
  split_ifs <;> positivity

theorem packet_sum (b : ℝ) (N : ℕ) : ∑' n, packetTerm b N n=powerMass b N := by
  have off (n : ℕ) (hn : n∉primes (cutoff N)) : packetTerm b N n=0 := if_neg hn
  rw [tsum_eq_sum off]
  exact sum_congr rfl fun _ hn => if_pos hn

theorem point {b : ℕ → ℝ} {a : ℝ} (hb : Tendsto b atTop (𝓝 a)) (n : ℕ) :
    Tendsto (fun N => packetTerm (b N) N n) atTop (𝓝 (totalTerm a n)) := by
  by_cases hp : n.Prime
  · have p := (Nat.cast_pos.mpr hp.pos : 0<(n:ℝ))
    have lim := continuous_exp.continuousAt.tendsto.comp ((hb.sub_const 1).const_mul (log n))
    rw [totalTerm,if_pos hp,rpow_def_of_pos p]
    apply lim.congr'
    filter_upwards [eventually_ge_atTop 2,eventually_ge_atTop n] with N hN hn
    change exp (log n*(b N-1))=packetTerm (b N) N n
    rw [packetTerm,if_pos ((mem_cutoff (by exact_mod_cast hN)).mpr ⟨hp,by exact_mod_cast hn⟩),rpow_def_of_pos p]
  · rw [totalTerm,if_neg hp]
    apply tendsto_const_nhds.congr
    intro N
    exact (if_neg (fun h => hp (Nat.mem_primesBelow.mp h).2) : packetTerm (b N) N n=0).symm

theorem dominate {b B : ℝ} (hb : b≤B) (N n : ℕ) :
    |packetTerm b N n| ≤ (n:ℝ)^(B-1) := by
  rw [abs_of_nonneg (packet_nonneg _ _ _)]
  by_cases h : n∈primes (cutoff N)
  · rw [packetTerm,if_pos h]
    exact rpow_le_rpow_of_exponent_le (by exact_mod_cast (Nat.mem_primesBelow.mp h).2.one_lt.le)
      (sub_le_sub_right hb 1)
  · rw [packetTerm,if_neg h]
    exact rpow_nonneg (Nat.cast_nonneg _) _

/-- The moving finite prime masses converge throughout the summable range. -/
theorem moving_mass {b : ℕ → ℝ} {a : ℝ} (ha : a<0) (hb : Tendsto b atTop (𝓝 a)) :
    Tendsto (fun N : ℕ => powerMass (b N) N) atTop (𝓝 (primeTotal a)) := by
  have hs : Summable (fun n : ℕ => (n:ℝ)^(a/2-1)) := summable_nat_rpow.mpr (by linarith only [ha])
  have dom : ∀ᶠ N in atTop, ∀ n, ‖packetTerm (b N) N n‖ ≤ (n:ℝ)^(a/2-1) := by
    filter_upwards [hb.eventually_le_const (show a<a/2 by linarith only [ha])] with N hN n
    exact dominate hN N n
  have h := tendsto_tsum_of_dominated_convergence hs (point hb) dom
  simpa only [packet_sum,totalTerm,primeTotal] using h

#print axioms packet_sum
#print axioms moving_mass

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Collisions
