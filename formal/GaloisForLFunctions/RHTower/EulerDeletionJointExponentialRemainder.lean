import GaloisForLFunctions.RHTower.EulerDeletionJointPolygonMoment
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Tactic

/-!
# Actual Euler-deletion exponential block: fifth-order remainder

The chronological moduli-2-and-3 block has the literal velocities
`X+Y, -X+Y, X-2Y, -X+Y, X+Y, -X-2Y`. The source-list identity is proved from
`blockDeletionCoefficient`; no closure or zeta-zero premise is supplied.

Integer-normalized exponential coefficients obey the ordinary Leibniz convolution. Their
first four positive degrees vanish as universal noncommutative ring identities. Identifying
these coefficients with derivatives of the actual Banach-algebra exponential word proves
`B(z)-1 = O(norm(z)^5)` at zero, directly, without a path-signature axiom or theorem.

This is a local analytic statement about one complete arithmetic block. The infinite product
with varying Dirichlet weights, its convergence region, and its sharpness require additional
estimates. No RH implication or novelty certificate is claimed.
-/

open scoped BigOperators
open NormedSpace
namespace RHTower.DeletionJointExponential
noncomputable section

section Algebra
variable {A : Type*} [Ring A]

/-- Integer-normalized coefficients of a chronological exponential word. -/
def jet : List A → ℕ → A
  | [], n => if n=0 then 1 else 0
  | v::vs, n => ∑ i ∈ Finset.range (n+1), (n.choose i : A) * v^i * jet vs (n-i)

/-- The six actual deletion velocities for moduli two and three. -/
def twoThreeVelocities (X Y : A) : List A :=
  [X+Y, -X+Y, X-2*Y, -X+Y, X+Y, -X-2*Y]

theorem jet_zero (vs : List A) : jet vs 0 = 1 := by
  induction vs with
  | nil => simp [jet]
  | cons v vs ih => simp [jet, ih]

set_option maxHeartbeats 4000000 in
theorem twoThree_jet_first_four (X Y : A) (n : ℕ) (hn : 1 ≤ n) (hn' : n ≤ 4) :
    jet (twoThreeVelocities X Y) n = 0 := by
  interval_cases n
  all_goals norm_num [twoThreeVelocities, jet, Finset.sum_range_succ, Nat.choose]
  all_goals noncomm_ring

end Algebra

section Analysis
variable {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A]

def exponentialWord (vs : List A) (z : ℂ) : A :=
  (vs.map (fun v => exp (z • v))).prod

theorem iteratedDeriv_exp_smul (v : A) (n : ℕ) :
    iteratedDeriv n (fun z : ℂ => exp (z • v)) = fun z => v^n * exp (z • v) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    have h := (hasDerivAt_exp_smul_const' v z).const_mul (v^n)
    simpa only [pow_succ, mul_assoc] using h.deriv

omit [CompleteSpace A] in
theorem exponentialWord_nil : exponentialWord ([] : List A) = fun _ => 1 := by
  funext z
  simp [exponentialWord]

omit [CompleteSpace A] in
theorem exponentialWord_cons (v : A) (vs : List A) :
    exponentialWord (v::vs) = (fun z : ℂ => exp (z • v)) * exponentialWord vs := by
  funext z
  simp [exponentialWord]

theorem analytic_exp_smul (v : A) (z : ℂ) :
    AnalyticAt ℂ (fun u : ℂ => exp (u • v)) z := by
  have hlin : AnalyticAt ℂ (fun u : ℂ => u • v) z := by fun_prop
  exact (exp_analytic (𝕂 := ℂ) (z • v)).comp (f := fun u : ℂ => u • v) hlin

theorem analytic_exponentialWord (vs : List A) (z : ℂ) :
    AnalyticAt ℂ (exponentialWord vs) z := by
  induction vs with
  | nil => rw [exponentialWord_nil]; exact analyticAt_const
  | cons v vs ih =>
    rw [exponentialWord_cons]
    exact (analytic_exp_smul v z).mul ih

theorem iteratedDeriv_exponentialWord_zero (vs : List A) (n : ℕ) :
    iteratedDeriv n (exponentialWord vs) 0 = jet vs n := by
  induction vs generalizing n with
  | nil => rw [exponentialWord_nil]; simp [jet, iteratedDeriv_const]
  | cons v vs ih =>
    have heq : exponentialWord (v::vs) =
        fun z : ℂ => exp (z • v) * exponentialWord vs z := by
      funext z
      simp [exponentialWord]
    rw [heq, iteratedDeriv_fun_mul]
    · simp only [jet, iteratedDeriv_exp_smul, zero_smul, exp_zero, mul_one, ih]
    · exact (analytic_exp_smul v 0).contDiffAt
    · exact (analytic_exponentialWord vs 0).contDiffAt

/-- Genuine derivatives of the actual six-exponential word, for arbitrary noncommuting inputs. -/
theorem twoThree_exponentialWord_first_four (X Y : A) (n : ℕ) (hn : 1 ≤ n) (hn' : n ≤ 4) :
    iteratedDeriv n (exponentialWord (twoThreeVelocities X Y)) 0 = 0 := by
  rw [iteratedDeriv_exponentialWord_zero]
  exact twoThree_jet_first_four X Y n hn hn'

/-- One literal two-channel coefficient, with no zero or closure input. -/
def sourceVelocity (P Q n : ℕ) (X Y : A) : A :=
  (blockDeletionCoefficient P (n+1) : ℂ) • X + (blockDeletionCoefficient Q (n+1) : ℂ) • Y

omit [CompleteSpace A] in
theorem twoThreeVelocities_eq_source (X Y : A) :
    (List.range 6).map (fun n => sourceVelocity 2 3 n X Y) = twoThreeVelocities X Y := by
  norm_num [List.range_succ, sourceVelocity, blockDeletionCoefficient, twoThreeVelocities,
    sub_smul, add_smul, two_mul]
  and_intros <;> module

/-- The actual common block, retaining chronological order. -/
def twoThreeSourceBlock (X Y : A) : ℂ → A :=
  exponentialWord ((List.range 6).map (fun n => sourceVelocity 2 3 n X Y))

omit [CompleteSpace A] in
theorem exponentialWord_zero (vs : List A) : exponentialWord vs 0 = 1 := by
  simp [exponentialWord]

/-- The analytic remainder has order at least five, without importing any signature theorem. -/
theorem twoThreeSourceBlock_remainder (X Y : A) :
    (fun z : ℂ => twoThreeSourceBlock X Y z - 1) =O[nhds 0]
      (fun z : ℂ => ‖z‖^5) := by
  have heq : twoThreeSourceBlock X Y = exponentialWord (twoThreeVelocities X Y) := by
    unfold twoThreeSourceBlock
    rw [twoThreeVelocities_eq_source]
  rw [heq]
  obtain ⟨p, hp⟩ := analytic_exponentialWord (twoThreeVelocities X Y) 0
  obtain ⟨r, hr⟩ := hp
  have hp : HasFPowerSeriesAt (exponentialWord (twoThreeVelocities X Y)) p 0 := ⟨r, hr⟩
  have hterm (n : ℕ) (hn : 1 ≤ n) (hn' : n ≤ 4) (z : ℂ) : p n (fun _ => z) = 0 := by
    have h := hr.factorial_smul z n
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
      twoThree_exponentialWord_first_four X Y n hn hn', smul_zero] at h
    have hc : (n.factorial : ℂ) • p n (fun _ => z) = 0 := by
      simpa only [Nat.cast_smul_eq_nsmul] using h
    exact (smul_eq_zero.mp hc).resolve_left (by exact_mod_cast n.factorial_ne_zero)
  have hpartial (z : ℂ) : p.partialSum 5 z = 1 := by
    unfold FormalMultilinearSeries.partialSum
    rw [Finset.sum_eq_single 0]
    · simpa only [exponentialWord_zero] using hp.coeff_zero (fun _ => z)
    · intro n hn hn0
      exact hterm n (by omega) (by have := Finset.mem_range.mp hn; omega) z
    · simp
  have h := hp.isBigO_sub_partialSum_pow 5
  simpa only [zero_add, hpartial] using h

end Analysis
end
end RHTower.DeletionJointExponential
