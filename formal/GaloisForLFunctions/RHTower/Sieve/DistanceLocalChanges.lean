import GaloisForLFunctions.RHTower.Sieve.DistanceTriangle

/-!
# Exact local changes of the multiplicative distance

The finite-prime stability argument of Lemmas 12.1 and 18.1 in
*Ordinary two-point correlations of multiplicative functions* extends to arbitrary
complex sequences when the error records their actual local amplitudes. The signed
identity precedes the absolute-value estimate. Neither multiplicativity nor unit
bounds are needed for these finite identities.
-/

open Finset
namespace RHTower.Sieve
noncomputable section

/-- Replacing finitely many values of a sequence. -/
def finiteValuePatch (S : Finset ℕ) (f b : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n ∈ S then b n else f n

/-- The exact signed change in squared multiplicative distance. -/
theorem mulDistSqPair_sub_eq (f b g : ℕ → ℂ) (P : Finset ℕ) :
    mulDistSqPair b g P - mulDistSqPair f g P =
      ∑ p ∈ P, ((f p - b p) * (starRingEnd ℂ) (g p)).re / (p : ℝ) := by
  rw [mulDistSqPair, mulDistSqPair, ← sum_sub_distrib]
  refine sum_congr rfl fun p _ => ?_
  simp only [sub_mul, Complex.sub_re]
  ring

/-- Real-part cancellation is retained before bounding the local perturbation. -/
theorem abs_sum_re_div_le (z : ℕ → ℂ) (P : Finset ℕ) :
    |∑ p ∈ P, (z p).re / (p : ℝ)| ≤ ∑ p ∈ P, ‖z p‖ / (p : ℝ) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p _ => ?_)
  rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (p : ℝ) from Nat.cast_nonneg p)]
  exact div_le_div_of_nonneg_right (Complex.abs_re_le_norm _) (Nat.cast_nonneg p)

/-- An unconditional Lipschitz bound, including zero in the finite index set. -/
theorem abs_mulDistSqPair_sub_le (f b g : ℕ → ℂ) (P : Finset ℕ) :
    |mulDistSqPair b g P - mulDistSqPair f g P| ≤
      ∑ p ∈ P, ‖f p - b p‖ * ‖g p‖ / (p : ℝ) := by
  rw [mulDistSqPair_sub_eq]
  simpa only [norm_mul, RCLike.norm_conj] using
    abs_sum_re_div_le (fun p => (f p - b p) * (starRingEnd ℂ) (g p)) P

/-- Only the changed coordinates contribute to the signed distance error. -/
theorem mulDistSqPair_patch_sub_eq (f b g : ℕ → ℂ) (P S : Finset ℕ) :
    mulDistSqPair (finiteValuePatch S f b) g P - mulDistSqPair f g P =
      ∑ p ∈ P.filter (· ∈ S), ((f p - b p) * (starRingEnd ℂ) (g p)).re / (p : ℝ) := by
  rw [mulDistSqPair_sub_eq, sum_filter]
  refine sum_congr rfl fun p _ => ?_
  by_cases hp : p ∈ S <;> simp [finiteValuePatch, hp]

/-- The local-change budget uses the actual amplitudes, without boundedness premises. -/
theorem abs_mulDistSqPair_patch_sub_le (f b g : ℕ → ℂ) (P S : Finset ℕ) :
    |mulDistSqPair (finiteValuePatch S f b) g P - mulDistSqPair f g P| ≤
      ∑ p ∈ P.filter (· ∈ S), ‖f p - b p‖ * ‖g p‖ / (p : ℝ) := by
  rw [mulDistSqPair_patch_sub_eq]
  simpa only [norm_mul, RCLike.norm_conj] using
    abs_sum_re_div_le (fun p => (f p - b p) * (starRingEnd ℂ) (g p))
      (P.filter (· ∈ S))

/-- The comparison with an archimedean character has a cutoff-independent budget. -/
theorem abs_mulDistSq_patch_sub_le (f b : ℕ → ℂ) (t : ℝ) (P S : Finset ℕ) :
    |mulDistSq (finiteValuePatch S f b) t P - mulDistSq f t P| ≤
      ∑ p ∈ S, ‖f p - b p‖ / (p : ℝ) := by
  rw [mulDistSq_eq_pair, mulDistSq_eq_pair]
  have h := abs_mulDistSqPair_patch_sub_le f b (charFn t) P S
  simp only [norm_charFn, mul_one] at h
  refine h.trans (sum_le_sum_of_subset_of_nonneg ?_ fun p _ _ => ?_)
  · intro p hp
    exact (mem_filter.mp hp).2
  · exact div_nonneg (norm_nonneg _) (Nat.cast_nonneg _)

/-- Finite local changes preserve every lower bound up to their explicit harmonic cost. -/
theorem mulDistSq_sub_local_cost_le (f b : ℕ → ℂ) (t : ℝ) (P S : Finset ℕ) :
    mulDistSq f t P - (∑ p ∈ S, ‖f p - b p‖ / (p : ℝ)) ≤
      mulDistSq (finiteValuePatch S f b) t P := by
  have h := (abs_le.mp (abs_mulDistSq_patch_sub_le f b t P S)).1
  linarith

/-- Conjugation can be moved from one argument of the distance to the other. -/
theorem mulDistSqPair_conj_left (f g : ℕ → ℂ) (P : Finset ℕ) :
    mulDistSqPair (fun n => (starRingEnd ℂ) (f n)) g P =
      mulDistSqPair f (fun n => (starRingEnd ℂ) (g n)) P := by
  unfold mulDistSqPair
  refine sum_congr rfl fun p _ => ?_
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Twisting one factor transports the conjugate twist to the comparison sequence. -/
theorem mulDistSqPair_mul_left (f g u : ℕ → ℂ) (P : Finset ℕ) :
    mulDistSqPair (fun n => f n * u n) g P =
      mulDistSqPair f (fun n => g n * (starRingEnd ℂ) (u n)) P := by
  unfold mulDistSqPair
  refine sum_congr rfl fun p _ => ?_
  simp only [map_mul, starRingEnd_self_apply]
  rw [mul_right_comm, mul_assoc]

/-- Simultaneous conjugation leaves the distance unchanged. -/
theorem mulDistSqPair_conj (f g : ℕ → ℂ) (P : Finset ℕ) :
    mulDistSqPair (fun n => (starRingEnd ℂ) (f n))
      (fun n => (starRingEnd ℂ) (g n)) P = mulDistSqPair f g P := by
  rw [mulDistSqPair_conj_left]
  simp only [starRingEnd_self_apply]

end
end RHTower.Sieve
