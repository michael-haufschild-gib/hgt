import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay.TwoShells.Rigidity
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay.Sharpness
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.ModeCapacities.Survival

/-! # When a single species needs the third occupation in the residue experiment -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay.TwoShells

open ModeCapacities
open scoped ComplexConjugate

def ambiguous (u v : ℕ → ℝ) (p : Nat.Primes) :=
  ∃ w s : ℂ, double w s u v p ∧ w≠1-conj s

theorem ambiguous_iff {u v : ℕ → ℝ} (hu : positive u) (hv : positive v) (p : Nat.Primes) :
    ambiguous u v p ↔ share u v p=1/2 := by
  constructor
  · rintro ⟨w,s,test,ne⟩
    exact (((double_iff w s hu hv p).mp test).resolve_left ne).1
  · intro half
    have pos : positive (1 : ℕ → ℝ) := fun _ => zero_lt_one
    obtain ⟨w,s,h1,h2,_,ne⟩ := two_shells_insufficient p
    have period := (((double_iff w s pos pos p).mp ⟨h1,h2⟩).resolve_left ne).2
    exact ⟨w,s,(double_iff w s hu hv p).mpr (Or.inr ⟨half,period⟩),ne⟩

private theorem emit_share (t : ℝ) (p : Nat.Primes) : share (emit t) (survive t) p=emit t p.val := by
  change (1-survive t p.val)/(1-survive t p.val+survive t p.val)=1-survive t p.val
  rw [sub_add_cancel,div_one]

/-- There is exactly one duration at which these two occupations leave
a phase ambiguity for the specified physical prime. -/
theorem exceptional_time {t : ℝ} (ht : 0<t) (p : Nat.Primes) :
    ambiguous (emit t) (survive t) p ↔ t=Real.log 2/Real.log p.val := by
  rw [ambiguous_iff (emit_pos ht) (survive_pos t) p,emit_share]
  change 1-Real.exp (-t*Real.log p.val)=1/2 ↔ _
  have pos := Real.log_pos (Nat.one_lt_cast.mpr p.property.one_lt : (1:ℝ)<p.val)
  rw [eq_div_iff pos.ne']
  constructor
  · intro h
    have e : Real.exp (-t*Real.log p.val)=1/2 := by linarith only [h]
    have L := congrArg Real.log e
    rw [Real.log_exp,one_div,Real.log_inv] at L
    linarith only [L]
  · intro h
    rw [neg_mul,h,Real.exp_neg,Real.exp_log (by norm_num : 0<(2:ℝ))]
    norm_num

theorem exceptional_prime (p : Nat.Primes) : ambiguous (emit 1) (survive 1) p ↔ p.val=2 := by
  rw [ambiguous_iff (emit_pos zero_lt_one) (survive_pos 1) p,emit_share]
  change 1-survive 1 p.val=1/2 ↔ _
  rw [one_time]
  constructor
  · intro h
    have nz : (p.val:ℝ)≠0 := Nat.cast_ne_zero.mpr p.property.ne_zero
    field_simp [nz] at h
    exact_mod_cast (show (p.val:ℝ)=2 by linarith only [h])
  · intro h
    rw [h]
    norm_num

#print axioms ambiguous_iff
#print axioms exceptional_time
#print axioms exceptional_prime

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.OccupationRefinement.CoherentRay.TwoShells
