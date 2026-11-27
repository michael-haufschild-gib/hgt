import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Optimal.Packing
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ExactSubsystems.Reflection.Repeated.Half.Arithmetic.Crossing.Family.LevelCount
import Mathlib.Analysis.SpecialFunctions.Arcosh

/-! # Sharp level cost of prescribed positive prime-coordinate ties -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Optimal

open Finset Real

private theorem log_prime (p : Nat.Primes) : 0<log (p.val : ℝ) :=
  log_pos (Nat.one_lt_cast.mpr p.property.one_lt)

/-- Positive inverse of the prime coordinate above two. -/
def temperature (p : Nat.Primes) (x : ℝ) := arcosh (x/2)/log p.val

private theorem temperature_pos (p : Nat.Primes) {x : ℝ} (hx : 2<x) : 0<temperature p x :=
  div_pos (arcosh_pos (by linarith)) (log_prime p)

private theorem measured (p : Nat.Primes) {x : ℝ} (hx : 2<x) :
    coordinate (temperature p x*log p.val)=x := by
  rw [temperature,div_mul_cancel₀ _ (log_prime p).ne']
  have eq (t : ℝ) : coordinate t=2*cosh t := by rw [coordinate,cosh_eq]; ring
  rw [eq,cosh_arcosh (by linarith)]; ring

private theorem profile_zero (T : Finset ℚ) {u : ℝ} (hu : 0<u) :
    profile T u=0 ↔ ∃ q ∈ T, coordinate u=(q : ℝ) := by
  have factor_zero (q : ℚ) : factor q (coordinate u)=0 ↔ coordinate u=(q : ℝ) := by
    rw [factor,sub_eq_zero,Rat.cast_def,eq_div_iff (Nat.cast_ne_zero.mpr q.den_pos.ne')]
    rw [mul_comm]
  simp only [profile,mul_eq_zero,(base_pos hu).ne',false_or,prod_eq_zero_iff,factor_zero]

/-- Each distinct rational coordinate above two supplies a distinct positive
tie. This lower bound applies to arbitrary real energies and degeneracies. -/
theorem level_lower_bound {I : Type*} [Fintype I] (E : I → ℝ) (p : Nat.Primes) (T : Finset ℚ)
    (above : ∀ q ∈ T, 2<q) (asym : ¬Reflects E)
    (ties : ∀ q ∈ T, agrees E (temperature p q)) : T.card+2≤(univ.image E).card := by
  classical
  let fin := finite_blind E
  have size : T.card≤fin.toFinset.card := by
    apply card_le_card_of_injOn (fun q : ℚ => temperature p q)
    · intro q hq
      exact fin.mem_toFinset.mpr ⟨temperature_pos p (by exact_mod_cast above q hq),ties q hq,asym⟩
    · intro q hq v hv eq
      have read := congrArg (fun t => coordinate (t*log p.val)) eq
      have qg : (2 : ℝ)<q := by exact_mod_cast above q hq
      have vg : (2 : ℝ)<v := by exact_mod_cast above v hv
      change coordinate (temperature p q*log p.val)=coordinate (temperature p v*log p.val) at read
      rw [measured p qg,measured p vg] at read
      exact_mod_cast read
  have bound := blind_distinct_levels E asym
  rw [Set.ncard_eq_toFinset_card _ fin] at bound
  omega

/-- Exactly r+2 distinct energies realize any r distinct rational thresholds
above two on one prime. The positive tie set has no other members. -/
theorem optimal_prime_schedule (p : Nat.Primes) (T : Finset ℚ) (above : ∀ q ∈ T, 2<q) :
    ∃ (n : ℕ) (a : Fin n → ℕ), (univ.image (primeModes p a)).card=T.card+2 ∧
      ¬Reflects (primeModes p a) ∧ ∀ t : ℝ, 0<t →
        (agrees (primeModes p a) t ↔ ∃ q ∈ T, coordinate (t*log p.val)=(q : ℝ)) := by
  classical
  obtain ⟨n,a,upper,traceEq⟩ := packed_response p T
  let E := primeModes p a
  have test (t : ℝ) (ht : 0<t) : agrees E t ↔ ∃ q ∈ T, coordinate (t*log p.val)=(q : ℝ) := by
    rw [agrees_odd,traceEq,profile_zero T (mul_pos ht (log_prime p))]
  obtain ⟨b,bounds⟩ := (T.image (fun q : ℚ => (q : ℝ))).finite_toSet.bddAbove
  let x := max 2 b+1
  have xg : 2<x := lt_of_le_of_lt (le_max_left _ _) (lt_add_one _)
  have xb : b<x := lt_of_le_of_lt (le_max_right _ _) (lt_add_one _)
  have asym : ¬Reflects E := by
    intro h
    obtain ⟨q,hq,eq⟩ := (test _ (temperature_pos p xg)).mp (reflection_agrees h _)
    rw [measured p xg] at eq
    have le : (q : ℝ)≤b := bounds (mem_image_of_mem (fun r : ℚ => (r : ℝ)) hq)
    exact xb.not_ge (eq.trans_le le)
  have lower := level_lower_bound E p T above asym (by
    intro q hq
    have gx : (2 : ℝ)<q := by exact_mod_cast above q hq
    exact (test _ (temperature_pos p gx)).mpr ⟨q,hq,measured p gx⟩)
  exact ⟨n,a,le_antisymm upper lower,asym,test⟩

#print axioms level_lower_bound
#print axioms optimal_prime_schedule

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.Repeated.Half.Arithmetic.Crossing.Family.Lattice.Optimal
