import GaloisForLFunctions.RHTower.PrimeFirstTraceEssentialEdgeSchattenThreshold
import GaloisForLFunctions.RHTower.EulerActivationSquarefreeDisintegration

/-!
# Reflected trace-ideal grade of the actual essential edge

The retained second coordinate of the literal strict-preclosure essential edge is

`c_p = 1 / p - p / (farPrime p)^2`.

This module proves that its far-prime correction is absolutely summable and classifies every real
modular twist `p^t c_p` exactly: it is summable if and only if `t < 0`.  The reflected twists have
the same trace-class status exactly at `t = 0`, where neither is trace class.  Thus the actual edge,
not merely the model prime harmonic sequence, carries an exact reflected ideal-valued fracture.

No Xi zero, divisor specialization, numerical computation, or extra postulate is used.
-/

open Filter Topology
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

def primeFirstTraceEssentialHarmonicCoordinate (p : Nat.Primes) : ℝ :=
  primeFirstTraceEssentialSourceDeviation p 2

def primeFirstTraceEssentialHarmonicTwist (t : ℝ) (p : Nat.Primes) : ℝ :=
  (p.1 : ℝ) ^ t * primeFirstTraceEssentialHarmonicCoordinate p

theorem primeFirstTraceEssentialHarmonicCoordinate_eq (p : Nat.Primes) :
    primeFirstTraceEssentialHarmonicCoordinate p =
      1 / (p.1 : ℝ) - (p.1 : ℝ) / ((farPrime p).1 : ℝ) ^ 2 := by
  exact primeFirstTraceEssentialSourceDeviation_apply_two p

theorem primeFirstTraceEssentialHarmonicCoordinate_bounds (p : Nat.Primes) :
    3 / (4 * (p.1 : ℝ)) ≤ primeFirstTraceEssentialHarmonicCoordinate p ∧
      primeFirstTraceEssentialHarmonicCoordinate p ≤ 1 / (p.1 : ℝ) := by
  let P : ℝ := p.1
  let R : ℝ := (farPrime p).1
  have hP0 : 0 < P := by dsimp [P]; exact_mod_cast p.2.pos
  have hR0 : 0 < R := by dsimp [R]; exact_mod_cast (farPrime p).2.pos
  have hP2 : 2 ≤ P := by dsimp [P]; exact_mod_cast p.2.two_le
  have hsq : P ^ 2 ≤ R := by
    dsimp [P, R]
    exact_mod_cast (farPrime_sq_lt p).le
  have hR2 : 4 * P ^ 2 ≤ R ^ 2 := by
    nlinarith [sq_nonneg (P ^ 2 - 4)]
  have hsmall : P / R ^ 2 ≤ 1 / (4 * P) := by
    calc
      P / R ^ 2 ≤ P / (4 * P ^ 2) :=
        div_le_div_of_nonneg_left hP0.le (by positivity) hR2
      _ = 1 / (4 * P) := by field_simp [hP0.ne']
  rw [primeFirstTraceEssentialHarmonicCoordinate_eq]
  change 3 / (4 * P) ≤ 1 / P - P / R ^ 2 ∧
    1 / P - P / R ^ 2 ≤ 1 / P
  constructor
  · calc
      3 / (4 * P) = 1 / P - 1 / (4 * P) := by
        field_simp [hP0.ne']
        ring
      _ ≤ 1 / P - P / R ^ 2 := sub_le_sub_left hsmall _
  · exact sub_le_self _ (by positivity)

theorem primeFirstTraceEssentialHarmonicCoordinate_nonneg (p : Nat.Primes) :
    0 ≤ primeFirstTraceEssentialHarmonicCoordinate p := by
  have hp : 0 < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  exact (by positivity : 0 ≤ 3 / (4 * (p.1 : ℝ))).trans
    (primeFirstTraceEssentialHarmonicCoordinate_bounds p).1

theorem summable_primeFirstTraceEssentialHarmonicCorrection :
    Summable (fun p : Nat.Primes =>
      1 / (p.1 : ℝ) - primeFirstTraceEssentialHarmonicCoordinate p) := by
  have hprime : Summable (fun p : Nat.Primes => ((p : ℝ) ^ 3)⁻¹) :=
    (Real.summable_nat_pow_inv.mpr (by norm_num)).comp_injective
      Subtype.val_injective
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hprime
  · rw [primeFirstTraceEssentialHarmonicCoordinate_eq]
    ring_nf
    positivity
  · let P : ℝ := p.1
    let R : ℝ := (farPrime p).1
    have hP0 : 0 < P := by dsimp [P]; exact_mod_cast p.2.pos
    have hR0 : 0 < R := by dsimp [R]; exact_mod_cast (farPrime p).2.pos
    have hsq : P ^ 2 ≤ R := by
      dsimp [P, R]
      exact_mod_cast (farPrime_sq_lt p).le
    have hR2' : (P ^ 2) ^ 2 ≤ R ^ 2 :=
      (sq_le_sq₀ (sq_nonneg P) hR0.le).2 hsq
    have hR2 : P ^ 4 ≤ R ^ 2 := by nlinarith
    rw [primeFirstTraceEssentialHarmonicCoordinate_eq]
    change 1 / P - (1 / P - P / R ^ 2) ≤ (P ^ 3)⁻¹
    calc
      1 / P - (1 / P - P / R ^ 2) = P / R ^ 2 := by ring
      _ ≤ P / P ^ 4 :=
        div_le_div_of_nonneg_left hP0.le (by positivity) hR2
      _ = (P ^ 3)⁻¹ := by field_simp [hP0.ne']

private theorem primeFirstTraceEssentialHarmonicTwist_nonneg
    (t : ℝ) (p : Nat.Primes) :
    0 ≤ primeFirstTraceEssentialHarmonicTwist t p := by
  have hP0 : 0 ≤ (p.1 : ℝ) := by positivity
  exact mul_nonneg (Real.rpow_nonneg hP0 t)
    (primeFirstTraceEssentialHarmonicCoordinate_nonneg p)

private theorem primeFirstTraceEssentialHarmonicTwist_le_rpow
    (t : ℝ) (p : Nat.Primes) :
    primeFirstTraceEssentialHarmonicTwist t p ≤ (p.1 : ℝ) ^ (t - 1) := by
  have hP0 : 0 < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  calc
    primeFirstTraceEssentialHarmonicTwist t p ≤
        (p.1 : ℝ) ^ t * (1 / (p.1 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (primeFirstTraceEssentialHarmonicCoordinate_bounds p).2
        (Real.rpow_nonneg hP0.le t)
    _ = (p.1 : ℝ) ^ (t - 1) := by
      rw [one_div, ← Real.rpow_neg_one, ← Real.rpow_add hP0]
      congr 1

theorem summable_primeFirstTraceEssentialHarmonicTwist_of_neg
    {t : ℝ} (ht : t < 0) :
    Summable (primeFirstTraceEssentialHarmonicTwist t) := by
  have hmajor : Summable (fun p : Nat.Primes => (p.1 : ℝ) ^ (t - 1)) :=
    (Nat.Primes.summable_rpow).2 (by linarith)
  exact Summable.of_nonneg_of_le
    (primeFirstTraceEssentialHarmonicTwist_nonneg t)
    (primeFirstTraceEssentialHarmonicTwist_le_rpow t) hmajor

theorem not_summable_primeFirstTraceEssentialHarmonicTwist_of_nonneg
    {t : ℝ} (ht : 0 ≤ t) :
    ¬ Summable (primeFirstTraceEssentialHarmonicTwist t) := by
  intro hsum
  have hlower : ∀ p : Nat.Primes,
      (3 / 4 : ℝ) * (1 / (p.1 : ℝ)) ≤
        primeFirstTraceEssentialHarmonicTwist t p := by
    intro p
    have hpOne : (1 : ℝ) ≤ (p.1 : ℝ) := by
      exact_mod_cast p.2.one_lt.le
    have hpowOne : 1 ≤ (p.1 : ℝ) ^ t := Real.one_le_rpow hpOne ht
    calc
      (3 / 4 : ℝ) * (1 / (p.1 : ℝ)) = 3 / (4 * (p.1 : ℝ)) := by ring
      _ ≤ primeFirstTraceEssentialHarmonicCoordinate p :=
        (primeFirstTraceEssentialHarmonicCoordinate_bounds p).1
      _ = 1 * primeFirstTraceEssentialHarmonicCoordinate p := by ring
      _ ≤ (p.1 : ℝ) ^ t * primeFirstTraceEssentialHarmonicCoordinate p :=
        mul_le_mul_of_nonneg_right hpowOne
          (primeFirstTraceEssentialHarmonicCoordinate_nonneg p)
      _ = primeFirstTraceEssentialHarmonicTwist t p := rfl
  have hscaled : Summable (fun p : Nat.Primes =>
      (3 / 4 : ℝ) * (1 / (p.1 : ℝ))) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hlower hsum
  have hharmonic : Summable (fun p : Nat.Primes => 1 / (p.1 : ℝ)) :=
    (summable_mul_left_iff (by norm_num : (3 / 4 : ℝ) ≠ 0)).mp hscaled
  exact Nat.Primes.not_summable_one_div hharmonic

theorem summable_primeFirstTraceEssentialHarmonicTwist_iff (t : ℝ) :
    Summable (primeFirstTraceEssentialHarmonicTwist t) ↔ t < 0 := by
  constructor
  · intro hsum
    exact lt_of_not_ge (fun ht =>
      not_summable_primeFirstTraceEssentialHarmonicTwist_of_nonneg ht hsum)
  · exact summable_primeFirstTraceEssentialHarmonicTwist_of_neg

theorem summable_reflected_primeFirstTraceEssentialHarmonicTwist_iff (t : ℝ) :
    Summable (primeFirstTraceEssentialHarmonicTwist (-t)) ↔ 0 < t := by
  simpa using summable_primeFirstTraceEssentialHarmonicTwist_iff (-t)

theorem reflected_primeFirstTraceEssentialHarmonicTwist_status_eq_iff (t : ℝ) :
    (Summable (primeFirstTraceEssentialHarmonicTwist t) ↔
      Summable (primeFirstTraceEssentialHarmonicTwist (-t))) ↔ t = 0 := by
  rw [summable_primeFirstTraceEssentialHarmonicTwist_iff,
    summable_reflected_primeFirstTraceEssentialHarmonicTwist_iff]
  constructor
  · intro h
    by_contra ht
    rcases lt_or_gt_of_ne ht with htneg | htpos
    · exact (not_lt_of_ge (le_of_lt htneg)) (h.mp htneg)
    · exact (not_lt_of_ge (le_of_lt htpos)) (h.mpr htpos)
  · rintro rfl
    simp

theorem not_both_summable_reflected_primeFirstTraceEssentialHarmonicTwist (t : ℝ) :
    ¬ (Summable (primeFirstTraceEssentialHarmonicTwist t) ∧
      Summable (primeFirstTraceEssentialHarmonicTwist (-t))) := by
  rw [summable_primeFirstTraceEssentialHarmonicTwist_iff,
    summable_reflected_primeFirstTraceEssentialHarmonicTwist_iff]
  rintro ⟨htn, htp⟩
  linarith

end


end RHTower
