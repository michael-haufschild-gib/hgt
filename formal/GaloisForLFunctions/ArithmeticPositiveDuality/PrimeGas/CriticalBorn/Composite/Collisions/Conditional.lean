import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Collisions.MovingMass

/-! # Total variation for normalized convergent prime packets -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Collisions

open Filter Real
open scoped Topology

def finiteProbability (b : ℝ) (N n : ℕ) := packetTerm b N n/powerMass b N

def infiniteProbability (a : ℝ) (n : ℕ) := totalTerm a n/primeTotal a

theorem finite_sum (b : ℝ) (N : ℕ) : ∑' n, finiteProbability b N n=1 := by
  simp only [finiteProbability,tsum_div_const,packet_sum,div_self (powerMass_pos _ _).ne']

theorem infinite_sum {a : ℝ} (ha : a<0) : ∑' n, infiniteProbability a n=1 := by
  rw [show (fun n => infiniteProbability a n)=(fun n => totalTerm a n/primeTotal a) from rfl,tsum_div_const]
  exact div_self (primeTotal_pos ha).ne'

private theorem static_bound {a B : ℝ} (ha : a≤B) (n : ℕ) :
    |totalTerm a n| ≤ (n:ℝ)^(B-1) := by
  by_cases hp : n.Prime
  · rw [totalTerm,if_pos hp,abs_of_nonneg (rpow_nonneg (Nat.cast_nonneg _) _)]
    exact rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_lt.le) (sub_le_sub_right ha 1)
  · rw [totalTerm,if_neg hp,abs_zero]
    exact rpow_nonneg (Nat.cast_nonneg _) _

/-- Uniform convergence of all bounded label tests follows from total
variation convergence for any moving temperature in the summable range. -/
theorem normalized_l1 {b : ℕ → ℝ} {a : ℝ} (ha : a<0) (hb : Tendsto b atTop (𝓝 a)) :
    Tendsto (fun N => ∑' n, |finiteProbability (b N) N n-infiniteProbability a n|) atTop (𝓝 0) := by
  let T := primeTotal a
  have hT : 0<T := primeTotal_pos ha
  let w := fun n : ℕ => (n:ℝ)^(a/2-1)
  have sw : Summable w := summable_nat_rpow.mpr (by linarith only [ha])
  have sum := (sw.div_const (T/2)).add (sw.div_const T)
  have mass := moving_mass ha hb
  have each (n : ℕ) : Tendsto (fun N => |finiteProbability (b N) N n-infiniteProbability a n|)
      atTop (𝓝 0) := by
    have h := (((point hb n).div mass hT.ne').sub_const (infiniteProbability a n)).abs
    simpa only [Pi.div_apply,finiteProbability,infiniteProbability,sub_self,abs_zero] using h
  have dom : ∀ᶠ N in atTop, ∀ n, ‖|finiteProbability (b N) N n-infiniteProbability a n|‖ ≤
      w n/(T/2)+w n/T := by
    filter_upwards [hb.eventually_le_const (show a<a/2 by linarith only [ha]),
      Tendsto.eventually_const_le (show T/2<T by linarith only [hT]) mass] with N hN hD n
    rw [Real.norm_eq_abs,abs_abs]
    refine (abs_sub _ _).trans (add_le_add ?_ ?_)
    · rw [finiteProbability,abs_div,abs_of_pos (powerMass_pos _ _)]
      exact (div_le_div_of_nonneg_right (dominate hN N n) (powerMass_pos _ _).le).trans
        (div_le_div_of_nonneg_left (rpow_nonneg (Nat.cast_nonneg _) _) (half_pos hT) hD)
    · rw [infiniteProbability,abs_div,abs_of_pos hT]
      exact div_le_div_of_nonneg_right (static_bound (show a≤a/2 by linarith only [ha]) n) hT.le
  simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence sum each dom

#print axioms finite_sum
#print axioms infinite_sum
#print axioms normalized_l1

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Composite.Collisions
