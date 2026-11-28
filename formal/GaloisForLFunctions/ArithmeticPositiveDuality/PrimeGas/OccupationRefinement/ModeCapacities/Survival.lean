import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities.Channels
import GaloisForLFunctions.RHTower.SmoothNumberLogSeries

/-! # Independent survival of prime particles gives logarithmic heat evolution -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities

open Finset Real

def survive (t : ℝ) (p : ℕ) := exp (-t*log p)

def emit (t : ℝ) : ℕ → ℝ := 1-survive t

theorem survive_pos (t : ℝ) : positive (survive t) := fun _ => exp_pos _

theorem emit_pos {t : ℝ} (ht : 0<t) : positive (emit t) := by
  intro p
  have prime : 1<(p.val:ℝ) := Nat.one_lt_cast.mpr p.property.one_lt
  exact sub_pos.mpr (exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_neg_of_pos ht) (log_pos prime)))

theorem capacities_sum (t : ℝ) : emit t+survive t=1 := sub_add_cancel _ _

theorem survive_mul (t r : ℝ) : survive t*survive r=survive (t+r) := by
  funext p
  rw [Pi.mul_apply,survive,survive,survive,←exp_add]
  congr 1
  ring

theorem one_time (p : Nat.Primes) : survive 1 p.val=1/(p.val:ℝ) := by
  rw [survive,neg_one_mul,exp_neg,exp_log (Nat.cast_pos.mpr p.property.pos),one_div]

/-- Unit-time elementary survival is the vacuum Born probability of
the uniform-residue order channel at the same prime. -/
theorem residue_anchor (p : Nat.Primes) :
    survive 1 p.val=‖channel (1/2) (⟨p.val,p.property.pos⟩ : ℕ+) 1‖^2 := by
  rw [survive,channel_norm_sq,Nat.totient_one,Nat.cast_one,one_mul,norm_heat,sq,←exp_add,
    Complex.div_ofNat_re,Complex.one_re]
  congr 1
  rw [show energy (⟨p.val,p.property.pos⟩ : ℕ+) = log (p.val:ℝ) from rfl]
  ring

/-- Requiring every particle to survive multiplies the elementary survival probabilities. -/
theorem survive_all (t : ℝ) (n : ℕ+) : twistFactor (survive t) n=exp (-t*energy n) := by
  calc
    _ = ∏ p ∈ n.val.primeFactors, exp (-t*((n.val.factorization p:ℝ)*log p)) := by
      apply prod_congr rfl
      intro p _
      rw [survive,←exp_nat_mul]
      congr 1
      ring
    _ = exp (-t*energy n) := by
      change _ = exp (-t*log n.val)
      rw [←exp_sum,←Finset.mul_sum,←RHTower.SmoothNumbers.log_eq_sum_factorization (Subset.rfl : n.val.primeFactors ⊆ _)]

theorem vacuum_probability (t : ℝ) (n : ℕ+) : branch (emit t) (survive t) 1 n.val=exp (-t*energy n) := by
  have pos : positive (1 : ℕ → ℝ) := fun _ => zero_lt_one
  have h := twist_profile (survive t) 1 n
  rw [mul_one] at h
  rw [branch,profile_one,one_mul,one_mul,capacities_sum,h,
    mul_div_cancel_right₀ _ (profile_pos pos n).ne',survive_all]

/-- The no-emission amplitude is the full complex heat multiplier. -/
theorem vacuum_heat (s : ℂ) (t : ℝ) (n : ℕ+) :
    kernel s (emit t) (survive t) 1 n=heat ((t:ℂ)*s) n := by
  rw [kernel,show (1:ℕ+).val=1 from rfl,vacuum_probability,log_exp,heat]
  congr 1
  push_cast
  ring

/-- The emitted-vacuum slice agrees with cyclic-order heat propagation,
including its phase on every composite and every input wave. -/
theorem cyclic_vacuum (s : ℂ) (t : ℝ) (f : Gas) (n : ℕ+) :
    CoassociativeSplitting.wave (kernel s (emit t) (survive t)) f (1,n) =
      split ((t:ℂ)*s) f (1,n) := by
  simp only [CoassociativeSplitting.wave,split,one_mul,vacuum_heat,channel,
    show (1:ℕ+).val=1 from rfl,Nat.totient_one,
    Nat.cast_one,Real.sqrt_one,Complex.ofReal_one]

#print axioms one_time
#print axioms residue_anchor
#print axioms survive_all
#print axioms vacuum_probability
#print axioms vacuum_heat
#print axioms cyclic_vacuum

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities
