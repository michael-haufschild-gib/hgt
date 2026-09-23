import GaloisForLFunctions.RHTower.EulerDeletionCoprimeWordPeriodicity
import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# Polynomial moments of literal coprime deletion polygons

For actual moduli `P=p+1` and `Q=q+1`, join the successive prefix endpoints
`(n mod P,n mod Q)` by straight segments. Their velocities are exactly the existing
Euler-deletion coefficients, and one common period is a closed polygon.

CRT factors every polynomial segment density into two explicit one-coordinate phase sums.
All coefficient-degree-at-most-three polynomial one-forms have zero circulation. The
higher moment `integral x*y^(3 : ℕ) dx` is exactly `P*(P-1)*Q*(Q-1)*(Q-2)/120` for coprime
`P,Q`. In particular the literal moduli-2-and-3 path gives the closed value `1/10`.

This is a finite unweighted arithmetic statement. It supplies no assertion about a weighted
infinite product, no vanishing at a zeta zero, and no RH implication. Polynomial-moment
and path-signature methods have published ancestry; no global novelty claim is made here.
-/

open scoped BigOperators
namespace RHTower.DeletionJointPolygon
noncomputable section

/-- Velocity of the literal modulus `p+1` deletion path. -/
def velocity (p n : ℕ) : ℝ := blockDeletionCoefficient (p+1) (n+1)

/-- Straight interpolation of the exact residue-valued prefix. -/
def position (p n : ℕ) (t : ℝ) : ℝ := (n % (p+1) : ℕ) + t * velocity p n

/-- Polynomial one-form integrated along one full common period. -/
def circulation (p q a b : ℕ) : ℝ :=
  ∫ t in (0:ℝ)..1, ∑ n ∈ Finset.range ((p+1)*(q+1)),
    position p n t ^ a * position q n t ^ b * velocity p n

/-- Position moments across one coordinate's phases. -/
def phaseMoment (p k : ℕ) (t : ℝ) : ℝ :=
  (∑ j ∈ Finset.range p, ((j:ℝ)+t)^k) + ((p:ℝ)*(1-t))^k

/-- Velocity-weighted position moments across one coordinate's phases. -/
def velocityMoment (p k : ℕ) (t : ℝ) : ℝ :=
  (∑ j ∈ Finset.range p, ((j:ℝ)+t)^k) - (p:ℝ)*((p:ℝ)*(1-t))^k

theorem velocity_of_lt {p n : ℕ} (hn : n < p) : velocity p n = 1 := by
  have hd : ¬ p+1 ∣ n+1 := Nat.not_dvd_of_pos_of_lt (Nat.succ_pos n)
    (Nat.succ_lt_succ hn)
  simp [velocity, blockDeletionCoefficient, hd]

theorem velocity_last (p : ℕ) : velocity p p = -(p:ℝ) := by
  simp [velocity, blockDeletionCoefficient]

theorem position_of_lt {p n : ℕ} (hn : n < p) (t : ℝ) :
    position p n t = (n:ℝ)+t := by
  simp [position, Nat.mod_eq_of_lt (Nat.lt_succ_of_lt hn), velocity_of_lt hn]

theorem position_last (p : ℕ) (t : ℝ) : position p p t = (p:ℝ)*(1-t) := by
  simp only [position, Nat.mod_eq_of_lt (Nat.lt_succ_self p), velocity_last]
  ring

theorem velocity_periodic (p : ℕ) : Function.Periodic (velocity p) (p+1) := by
  intro n
  exact congrArg (fun z : ℤ => (z:ℝ))
    (DeletionCoprimeWords.shifted_deletion_periodic (p+1) n)

theorem position_periodic (p : ℕ) (t : ℝ) :
    Function.Periodic (fun n => position p n t) (p+1) := by
  intro n
  simp only [position, Nat.add_mod_right, velocity_periodic p n]

theorem sum_position_pow (p k : ℕ) (t : ℝ) :
    (∑ n ∈ Finset.range (p+1), position p n t ^ k) = phaseMoment p k t := by
  rw [Finset.sum_range_succ, position_last]
  unfold phaseMoment
  congr 1
  exact Finset.sum_congr rfl (fun n hn => by rw [position_of_lt (Finset.mem_range.mp hn)])

theorem sum_position_pow_velocity (p k : ℕ) (t : ℝ) :
    (∑ n ∈ Finset.range (p+1), position p n t ^ k * velocity p n) =
      velocityMoment p k t := by
  rw [Finset.sum_range_succ, position_last, velocity_last]
  unfold velocityMoment
  have hs : (∑ n ∈ Finset.range p, position p n t ^ k * velocity p n) =
      ∑ n ∈ Finset.range p, ((n:ℝ)+t)^k := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [position_of_lt (Finset.mem_range.mp hn), velocity_of_lt (Finset.mem_range.mp hn), mul_one]
  rw [hs]
  ring

/-- The starting coordinate is the actual sum of previous deletion jumps. -/
theorem position_zero_eq_prefix (p n : ℕ) :
    position p n 0 = (deletionCoeffPartialSum (p+1) n : ℝ) := by
  simp only [position, zero_mul, add_zero, deletionCoeffPartialSum_eq_mod, Int.cast_natCast]

/-- Consecutive straight segments meet at their endpoints. -/
theorem segment_endpoint (p n : ℕ) : position p n 1 = position p (n+1) 0 := by
  have h : deletionCoeffPartialSum (p+1) n + blockDeletionCoefficient (p+1) (n+1) =
      deletionCoeffPartialSum (p+1) (n+1) := by
    exact (Finset.sum_range_succ _ _).symm
  rw [deletionCoeffPartialSum_eq_mod, deletionCoeffPartialSum_eq_mod] at h
  have hr := congrArg (fun z : ℤ => (z:ℝ)) h
  simpa only [position, velocity, one_mul, zero_mul, add_zero, Int.cast_add, Int.cast_natCast] using hr

/-- A common period returns both literal coordinates to the origin. -/
theorem common_period_closed (p q : ℕ) :
    position p ((p+1)*(q+1)) 0 = 0 ∧ position q ((p+1)*(q+1)) 0 = 0 := by
  simp [position]

/-- CRT factors the actual segment integrand; no averaging approximation is used. -/
theorem integrand_factorization {p q : ℕ} (hpq : (p+1).Coprime (q+1))
    (a b : ℕ) (t : ℝ) :
    (∑ n ∈ Finset.range ((p+1)*(q+1)),
      position p n t ^ a * position q n t ^ b * velocity p n) =
    velocityMoment p a t * phaseMoment q b t := by
  have hf : Function.Periodic (fun n => position p n t ^ a * velocity p n) (p+1) :=
    by
      intro n
      dsimp only
      exact congrArg₂ (fun x y : ℝ => x^a*y) (position_periodic p t n)
        (velocity_periodic p n)
  have hg : Function.Periodic (fun n => position q n t ^ b) (q+1) := by
    intro n
    dsimp only
    exact congrArg (fun x : ℝ => x^b) (position_periodic q t n)
  have h := DeletionCoprimeWords.coprime_period_sum_mul (Nat.succ_pos p) (Nat.succ_pos q)
    hpq hf hg
  rw [sum_position_pow_velocity, sum_position_pow] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro n hn
  ring

theorem sum_shift_pow_one (p : ℕ) (t : ℝ) :
    (∑ j ∈ Finset.range p, ((j:ℝ)+t)) = (p:ℝ)*t + (p:ℝ)*(p-1)/2 := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem sum_shift_pow_two (p : ℕ) (t : ℝ) :
    (∑ j ∈ Finset.range p, ((j:ℝ)+t)^(2 : ℕ)) =
      (p:ℝ)*t^(2 : ℕ) + (p:ℝ)*(p-1)*t + (p:ℝ)*(p-1)*(2*p-1)/6 := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem sum_shift_pow_three (p : ℕ) (t : ℝ) :
    (∑ j ∈ Finset.range p, ((j:ℝ)+t)^(3 : ℕ)) =
      (p:ℝ)*t^(3 : ℕ) + 3*(p:ℝ)*(p-1)*t^(2 : ℕ)/2 + (p:ℝ)*(p-1)*(2*p-1)*t/2 +
        (p:ℝ)^(2 : ℕ)*(p-1)^(2 : ℕ)/4 := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

theorem phaseMoment_zero (p : ℕ) (t : ℝ) : phaseMoment p 0 t = (p:ℝ)+1 := by
  simp [phaseMoment]

theorem phaseMoment_one (p : ℕ) (t : ℝ) :
    phaseMoment p 1 t = (p:ℝ)*(p+1)/2 := by
  simp only [phaseMoment, pow_one, sum_shift_pow_one]
  ring

theorem phaseMoment_two (p : ℕ) (t : ℝ) :
    phaseMoment p 2 t = (p:ℝ)*(p+1)*(2*p+1)/6 - (p:ℝ)*(p+1)*t +
      (p:ℝ)*(p+1)*t^(2 : ℕ) := by
  rw [phaseMoment, sum_shift_pow_two]
  ring

theorem phaseMoment_three (p : ℕ) (t : ℝ) :
    phaseMoment p 3 t = (p:ℝ)^(2 : ℕ)*(p+1)^(2 : ℕ)/4 - (p:ℝ)*(p+1)*(4*p-1)*t/2 +
      3*(p:ℝ)*(p+1)*(2*p-1)*t^(2 : ℕ)/2 - (p:ℝ)*(p+1)*(p-1)*t^(3 : ℕ) := by
  rw [phaseMoment, sum_shift_pow_three]
  ring

theorem velocityMoment_zero (p : ℕ) (t : ℝ) : velocityMoment p 0 t = 0 := by
  simp [velocityMoment]

theorem velocityMoment_one (p : ℕ) (t : ℝ) :
    velocityMoment p 1 t = (p:ℝ)*(p+1)*(2*t-1)/2 := by
  simp only [velocityMoment, pow_one, sum_shift_pow_one]
  ring

private theorem integral_linear (a : ℝ) :
    (∫ t in (0:ℝ)..1, a*t) = a/2 := by
  rw [intervalIntegral.integral_const_mul, integral_id]
  norm_num
  ring

private theorem integral_quartic (a b c d e : ℝ) :
    (∫ t in (0:ℝ)..1, a + b*t + c*t^(2 : ℕ) + d*t^(3 : ℕ) + e*t^(4 : ℕ)) =
      a + b/2 + c/3 + d/4 + e/5 := by
  simp (disch := exact Continuous.intervalIntegrable (by fun_prop) _ _) only
    [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, integral_pow]
  rw [intervalIntegral.integral_const_mul, integral_id]
  norm_num
  ring

/-- An exact mixed moment of the literal coprime deletion polygon. -/
theorem circulation_one_three {p q : ℕ} (hpq : (p+1).Coprime (q+1)) :
    circulation p q 1 3 = (p:ℝ)*(p+1)*(q:ℝ)*(q+1)*(q-1)/120 := by
  unfold circulation
  simp_rw [integrand_factorization hpq, velocityMoment_one, phaseMoment_three]
  let A : ℝ := (p:ℝ)*(p+1)/2
  let B : ℝ := (q:ℝ)^(2 : ℕ)*(q+1)^(2 : ℕ)/4
  let C : ℝ := -(q:ℝ)*(q+1)*(4*q-1)/2
  let D : ℝ := 3*(q:ℝ)*(q+1)*(2*q-1)/2
  let E : ℝ := -(q:ℝ)*(q+1)*(q-1)
  have hpoly (t : ℝ) :
      (p:ℝ)*(p+1)*(2*t-1)/2 * ((q:ℝ)^(2 : ℕ)*(q+1)^(2 : ℕ)/4 -
      (q:ℝ)*(q+1)*(4*q-1)*t/2 + 3*(q:ℝ)*(q+1)*(2*q-1)*t^(2 : ℕ)/2 -
      (q:ℝ)*(q+1)*(q-1)*t^(3 : ℕ)) =
      -A*B + A*(2*B-C)*t + A*(2*C-D)*t^(2 : ℕ) + A*(2*D-E)*t^(3 : ℕ) + 2*A*E*t^(4 : ℕ) := by
    dsimp [A, B, C, D, E]
    ring
  simp_rw [hpoly]
  rw [integral_quartic]
  dsimp [A, B, C, D, E]
  ring

/-- Closed concrete arithmetic witness, with no hypotheses. -/
theorem moduli_two_three_moment : circulation 1 2 1 3 = (1:ℝ)/10 := by
  have hc : (1+1:ℕ).Coprime (2+1) := by norm_num
  rw [circulation_one_three hc]
  norm_num

/-- Every polynomial moment through coefficient degree three vanishes. -/
theorem circulation_low_degree {p q : ℕ} (hpq : (p+1).Coprime (q+1))
    (a b : ℕ) (hab : a+b ≤ 3) : circulation p q a b = 0 := by
  unfold circulation
  simp_rw [integrand_factorization hpq]
  have ha : a ≤ 3 := by omega
  have hb : b ≤ 3 := by omega
  interval_cases a <;> interval_cases b <;> try omega
  all_goals try simp only [velocityMoment_zero, zero_mul, intervalIntegral.integral_zero]
  all_goals simp only [phaseMoment_zero, phaseMoment_one,
    phaseMoment_two, velocityMoment, pow_one, sum_shift_pow_one, sum_shift_pow_two, sum_shift_pow_three]
  all_goals
    conv_lhs =>
      congr
      ext t
      ring_nf
    simp (disch := exact Continuous.intervalIntegrable (by fun_prop) _ _) only
      [intervalIntegral.integral_add, intervalIntegral.integral_sub,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_mul_const,
        intervalIntegral.integral_const, integral_pow]
    simp only [integral_linear]
    norm_num
    ring

/-- The integral of the summed segment densities is the sum of the line integrals. -/
theorem circulation_eq_segment_sum (p q a b : ℕ) :
    circulation p q a b = ∑ n ∈ Finset.range ((p+1)*(q+1)),
      ∫ t in (0:ℝ)..1, position p n t ^ a * position q n t ^ b * velocity p n := by
  exact intervalIntegral.integral_finsetSum (fun n _ =>
    Continuous.intervalIntegrable (by unfold position; fun_prop) _ _)

/-- Both coordinate families close and pass every degree-three polynomial test,
while a specified mixed polynomial one-form has nonzero integral. No hypotheses. -/
theorem moduli_two_three_closed_low_degree_nonzero :
    (position 1 6 0 = 0 ∧ position 2 6 0 = 0) ∧
    (∀ a b : ℕ, a+b ≤ 3 → circulation 1 2 a b = 0 ∧ circulation 2 1 a b = 0) ∧
    circulation 1 2 1 3 = (1:ℝ)/10 ∧ circulation 1 2 1 3 ≠ 0 := by
  refine ⟨common_period_closed 1 2, ?_, moduli_two_three_moment, ?_⟩
  · intro a b hab
    exact ⟨circulation_low_degree (by norm_num) a b hab,
      circulation_low_degree (by norm_num) a b hab⟩
  · rw [moduli_two_three_moment]
    norm_num

end
end RHTower.DeletionJointPolygon
