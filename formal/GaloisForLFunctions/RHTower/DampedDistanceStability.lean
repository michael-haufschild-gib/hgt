import GaloisForLFunctions.RHTower.Sieve.DistanceLocalChanges
import GaloisForLFunctions.RHTower.Sieve.DampedLocalFactor
import GaloisForLFunctions.RHTower.DampedPretentiousGap

/-!
# Two-sided pretentious bounds for Möbius damping

The finite-prime estimate in Lemma 12.1 of *Ordinary two-point correlations of
multiplicative functions* identifies the exact distance of `dampedOmegaMoebius`
and bounds its difference from the Möbius distance for every real damping
parameter. The cost is `|a - 1|` times the selected harmonic mass.
-/

open Finset
namespace RHTower
open Sieve
noncomputable section

/-- The damped cosine sum is exactly the distance of the altered prime data. -/
theorem dampedCosPlusSum_eq_mulDistSq_patch (S : Finset ℕ) (a t x : ℝ) :
    dampedCosPlusSum S a t x =
      mulDistSq (finiteValuePatch S (fun _ => (-1 : ℂ)) (fun _ => -(a : ℂ))) t
        (Nat.primesLE ⌊x⌋₊) := by
  unfold dampedCosPlusSum mulDistSq
  refine sum_congr rfl fun p _ => ?_
  have heq : finiteValuePatch S (fun _ => (-1 : ℂ)) (fun _ => -(a : ℂ)) p =
      -((if p ∈ S then a else 1 : ℝ) : ℂ) := by
    by_cases hp : p ∈ S <;> simp [finiteValuePatch, hp]
  rw [heq, neg_mul, Complex.neg_re, Complex.re_ofReal_mul,
    Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  ring

/-- The undamped cosine sum is the distance of the Liouville prime values. -/
theorem primeCosPlusSum_eq_mulDistSq (t x : ℝ) :
    primeCosPlusSum t x = mulDistSq (fun _ => (-1 : ℂ)) t (Nat.primesLE ⌊x⌋₊) := by
  rw [mulDistSq_eq_pair]
  exact (pretentiousDistSq_neg_one_eq t x).symm

/-- Arbitrary real damping changes the distance by at most its amplitude times harmonic mass. -/
theorem abs_dampedCosPlusSum_sub_le (S : Finset ℕ) (a t x : ℝ) :
    |dampedCosPlusSum S a t x - primeCosPlusSum t x| ≤
      |a - 1| * ∑ p ∈ S, (1 : ℝ) / p := by
  rw [dampedCosPlusSum_eq_mulDistSq_patch, primeCosPlusSum_eq_mulDistSq]
  refine (abs_mulDistSq_patch_sub_le _ _ t _ S).trans_eq ?_
  rw [mul_sum]
  refine sum_congr rfl fun p _ => ?_
  have heq : (-1 : ℂ) - -(a : ℂ) = ((a - 1 : ℝ) : ℂ) := by push_cast; ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs]
  ring

/-- The arithmetic damped Möbius function realizes the cosine distance exactly. -/
theorem mulDistSq_dampedOmegaMoebius_eq (S : Finset ℕ) (a t : ℝ) (N : ℕ) :
    mulDistSq (dampedOmegaMoebius (S.filter Nat.Prime) a) t (Nat.primesLE N) =
      dampedCosPlusSum S a t N := by
  unfold mulDistSq dampedCosPlusSum
  rw [Nat.floor_natCast]
  refine sum_congr rfl fun p hp => ?_
  have hpprime := Nat.prime_of_mem_primesLE hp
  rw [dampedOmegaMoebius_prime (fun q hq => (mem_filter.mp hq).2) a hpprime]
  simp only [mem_filter, hpprime, and_true]
  rw [neg_mul, Complex.neg_re, Complex.re_ofReal_mul,
    Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  ring

/-- The local-change bound applies to the existing arithmetic Möbius damping construction. -/
theorem abs_mulDistSq_dampedOmegaMoebius_sub_moebius_le (S : Finset ℕ)
    (a t : ℝ) (N : ℕ) :
    |mulDistSq (dampedOmegaMoebius (S.filter Nat.Prime) a) t (Nat.primesLE N) -
      mulDistSq moebiusC t (Nat.primesLE N)| ≤
        |a - 1| * ∑ p ∈ S, (1 : ℝ) / p := by
  rw [mulDistSq_dampedOmegaMoebius_eq,
    mulDistSq_moebiusC t (fun _ hp => Nat.prime_of_mem_primesLE hp)]
  simpa only [primeCosPlusSum, Nat.floor_natCast] using abs_dampedCosPlusSum_sub_le S a t N

end
end RHTower
