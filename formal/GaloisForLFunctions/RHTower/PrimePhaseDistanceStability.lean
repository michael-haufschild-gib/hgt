import GaloisForLFunctions.RHTower.CCM.CCMCoherentSquareExclusion
import GaloisForLFunctions.RHTower.Sieve.DistanceLocalChanges
import GaloisForLFunctions.RHTower.LiouvillePrimeBandAlgebra

/-!
# Pretentious stability of finite prime-phase deformations

The finite-prime argument in Lemma 12.1 of *Ordinary two-point correlations of
multiplicative functions* applies to the completely multiplicative `phaseChar`
and to `LiouvillePrimeBand.character`. The resulting Lipschitz bound is uniform in
the prime cutoff and frequency. Hence every fixed band deformation preserves
divergence along arbitrary moving frequency and cutoff schedules.
-/

open Finset Filter
open GaloisForLFunctions.HTGeometry
namespace RHTower
open Sieve
noncomputable section

/-- A completely multiplicative extension has exactly the distance of its prime data. -/
theorem mulDistSq_phaseChar (v : ℕ → ℂ) (t : ℝ) (N : ℕ) :
    mulDistSq (phaseChar v) t (Nat.primesLE N) = mulDistSq v t (Nat.primesLE N) := by
  unfold mulDistSq
  exact sum_congr rfl fun p hp => by rw [phaseChar_prime v (Nat.prime_of_mem_primesLE hp)]

/-- Finite changes to actual completely multiplicative functions have a uniform local budget. -/
theorem abs_mulDistSq_phaseChar_patch_sub_le (v b : ℕ → ℂ) (S : Finset ℕ)
    (t : ℝ) (N : ℕ) :
    |mulDistSq (phaseChar (finiteValuePatch S v b)) t (Nat.primesLE N) -
      mulDistSq (phaseChar v) t (Nat.primesLE N)| ≤
        ∑ p ∈ S, ‖v p - b p‖ / (p : ℝ) := by
  rw [mulDistSq_phaseChar, mulDistSq_phaseChar]
  exact abs_mulDistSq_patch_sub_le v b t _ S

/-- Arbitrary local phase rotations of Liouville cost at most twice their harmonic mass. -/
theorem abs_mulDistSq_liouville_phase_patch_sub_le (S : Finset ℕ) (θ : ℕ → ℝ)
    (t : ℝ) (N : ℕ) :
    |mulDistSq (phaseChar (finiteValuePatch S (fun _ => (-1 : ℂ))
        (fun p => -Complex.exp ((θ p : ℂ) * Complex.I)))) t (Nat.primesLE N) -
      mulDistSq (phaseChar (fun _ => (-1 : ℂ))) t (Nat.primesLE N)| ≤
        2 * ∑ p ∈ S, (1 : ℝ) / p := by
  refine (abs_mulDistSq_phaseChar_patch_sub_le _ _ S t N).trans ?_
  rw [mul_sum]
  refine sum_le_sum fun p _ => ?_
  have hnorm : ‖(-1 : ℂ) - -Complex.exp ((θ p : ℂ) * Complex.I)‖ ≤ 2 := by
    calc
      _ ≤ ‖(-1 : ℂ)‖ + ‖-Complex.exp ((θ p : ℂ) * Complex.I)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_neg, norm_one, norm_neg, Complex.norm_exp_ofReal_mul_I]; ring
  simpa only [← mul_div_assoc, mul_one] using
    div_le_div_of_nonneg_right hnorm (Nat.cast_nonneg p)

/-- The prime-band parameter is Lipschitz in pretentious distance, uniformly in frequency. -/
theorem LiouvillePrimeBand.abs_mulDistSq_character_sub_le (S : Finset ℕ)
    (β : ℕ → ℂ) (z w : ℂ) (t : ℝ) (N : ℕ) :
    |mulDistSq (LiouvillePrimeBand.character S β z) t (Nat.primesLE N) -
      mulDistSq (LiouvillePrimeBand.character S β w) t (Nat.primesLE N)| ≤
        ‖z - w‖ * ∑ p ∈ S, ‖β p‖ / (p : ℝ) := by
  let v : ℕ → ℂ := fun p =>
    if p ∈ S then w * β p else LiouvilleTwistedDensity.primePhase p
  have hpatch : finiteValuePatch S v (fun p => z * β p) =
      fun p => if p ∈ S then z * β p else LiouvilleTwistedDensity.primePhase p := by
    funext p
    by_cases hp : p ∈ S <;> simp [finiteValuePatch, v, hp]
  have h := abs_mulDistSq_phaseChar_patch_sub_le v (fun p => z * β p) S t N
  rw [hpatch] at h
  change |mulDistSq (LiouvillePrimeBand.character S β z) t (Nat.primesLE N) -
      mulDistSq (LiouvillePrimeBand.character S β w) t (Nat.primesLE N)| ≤ _ at h
  refine h.trans_eq ?_
  rw [mul_sum]
  refine sum_congr rfl fun p hp => ?_
  simp only [v, if_pos hp, ← sub_mul, norm_mul, norm_sub_rev w z]
  ring

/-- Even along a moving frequency schedule, a fixed prime-band deformation preserves divergence. -/
theorem LiouvillePrimeBand.tendsto_mulDistSq_character_iff (S : Finset ℕ)
    (β : ℕ → ℂ) (z w : ℂ) (t : ℕ → ℝ) (N : ℕ → ℕ) :
    Tendsto (fun k => mulDistSq (LiouvillePrimeBand.character S β z) (t k)
        (Nat.primesLE (N k))) atTop atTop ↔
      Tendsto (fun k => mulDistSq (LiouvillePrimeBand.character S β w) (t k)
        (Nat.primesLE (N k))) atTop atTop := by
  have transfer : ∀ z w : ℂ,
      Tendsto (fun k => mulDistSq (LiouvillePrimeBand.character S β z) (t k)
          (Nat.primesLE (N k))) atTop atTop →
        Tendsto (fun k => mulDistSq (LiouvillePrimeBand.character S β w) (t k)
          (Nat.primesLE (N k))) atTop atTop := by
    intro z w hz
    refine tendsto_atTop.2 fun B => ?_
    filter_upwards [hz.eventually_ge_atTop
      (B + ‖z - w‖ * ∑ p ∈ S, ‖β p‖ / (p : ℝ))] with k hk
    have h := (abs_le.mp (LiouvillePrimeBand.abs_mulDistSq_character_sub_le
      S β z w (t k) (N k))).2
    linarith
  exact ⟨transfer z w, transfer w z⟩

/-- Every finite prime modification of Liouville remains distant from the constant reference. -/
theorem tendsto_mulDistSq_liouville_patch_zero (S : Finset ℕ) (b : ℕ → ℂ) :
    Tendsto (fun N => mulDistSq (phaseChar (finiteValuePatch S (fun _ => -1) b)) 0
      (Nat.primesLE N)) atTop atTop := by
  have hdiv := GaloisForLFunctions.RHTower.tendsto_primeReciprocalSum_atTop.comp
    (tendsto_add_atTop_nat 1)
  have hbase (N : ℕ) :
      mulDistSq (fun _ => (-1 : ℂ)) 0 (Nat.primesLE N) =
        2 * GaloisForLFunctions.RHTower.primeReciprocalSum (N + 1) := by
    norm_num [mulDistSq_eq_pair, mulDistSqPair, charFn, Nat.primesLE_eq_filter_range,
      GaloisForLFunctions.RHTower.primeReciprocalSum, mul_sum, div_eq_mul_inv]
  refine tendsto_atTop.2 fun B => ?_
  filter_upwards [hdiv.eventually_ge_atTop
    ((B + ∑ p ∈ S, ‖(-1 : ℂ) - b p‖ / (p : ℝ)) / 2)] with N hN
  rw [mulDistSq_phaseChar]
  have hlocal := mulDistSq_sub_local_cost_le (fun _ => (-1 : ℂ)) b 0
    (Nat.primesLE N) S
  rw [hbase] at hlocal
  dsimp only [Function.comp_apply] at hN
  linarith

/-- The corpus's complete prime-band family has unconditional zero-frequency divergence. -/
theorem LiouvillePrimeBand.tendsto_mulDistSq_character_zero (S : Finset ℕ)
    (β : ℕ → ℂ) (z : ℂ) :
    Tendsto (fun N => mulDistSq (LiouvillePrimeBand.character S β z) 0
      (Nat.primesLE N)) atTop atTop := by
  have hchar : LiouvillePrimeBand.character S β z =
      phaseChar (finiteValuePatch (insert 2 S) (fun _ => -1)
        (fun p => if p ∈ S then z * β p else Complex.I)) := by
    apply congrArg phaseChar
    funext p
    by_cases hp : p ∈ S <;> by_cases hp2 : p = 2 <;>
      simp [finiteValuePatch, LiouvilleTwistedDensity.primePhase, hp, hp2]
  rw [hchar]
  exact tendsto_mulDistSq_liouville_patch_zero _ _

end
end RHTower
