import GaloisForLFunctions.RHTower.PrimeFirstTraceEssentialNormalBoundary

/-!
# Exact Schatten threshold of the all-prime essential first-trace edge

The anisotropically normalized actual-prime first-trace graph has a canonical edge
`e₁ ↦ e₂` at infinity.  This module globalizes its correction over all ordinary primes.

Both the source and response corrections have summable squared norms.  The source correction is
not absolutely summable: its second Hardy coordinate is exactly

`1 / p - p / (farPrime p)^(2 : ℕ) ≥ 3 / (4p)`.

Thus the literal all-prime strict-preclosure correction is Hilbert--Schmidt but not trace class.
No Xi zero, divisor specialization, numerical computation, or extra postulate is used.
-/

open Filter Topology
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-- Source component of the normalized essential-edge correction at an ordinary prime. -/
def primeFirstTraceEssentialSourceDeviation (p : Nat.Primes) : PrimeHardy :=
  Real.log (p.1 : ℝ) •
      primeHardyKernelMap (primeFirstTraceWitness p (farPrime p)) -
    lp.single 2 1 1

/-- Response component of the normalized essential-edge correction at an ordinary prime. -/
def primeFirstTraceEssentialResponseDeviation (p : Nat.Primes) : PrimeHardy :=
  (p.1 : ℝ) • primeFirstTraceEssentialResponse p - lp.single 2 2 1

/-- The retained second source coordinate is the prime harmonic term minus a prime-cubic-size
far-prime correction. -/
theorem primeFirstTraceEssentialSourceDeviation_apply_two (p : Nat.Primes) :
    primeFirstTraceEssentialSourceDeviation p 2 =
      1 / (p.1 : ℝ) - (p.1 : ℝ) / ((farPrime p).1 : ℝ) ^ 2 := by
  have hp0 : (p.1 : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hr0 : ((farPrime p).1 : ℝ) ≠ 0 := by
    exact_mod_cast (farPrime p).2.ne_zero
  have hlogp : Real.log (p.1 : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast p.2.one_lt))
  rw [primeFirstTraceEssentialSourceDeviation, primeHardyKernelMap_witness]
  simp only [smul_sub, smul_smul]
  simp [primeHardyTail, primeReciprocal, hardyFirstTail_apply_succ,
    lp.single_apply]
  field_simp [hp0, hr0, hlogp]

/-- The harmonic coordinate survives uniformly: the normalized source correction is at least
`3 / (4p)` in norm. -/
theorem three_div_four_prime_le_norm_primeFirstTraceEssentialSourceDeviation
    (p : Nat.Primes) :
    3 / (4 * (p.1 : ℝ)) ≤ ‖primeFirstTraceEssentialSourceDeviation p‖ := by
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
  have hcoord : 3 / (4 * P) ≤ 1 / P - P / R ^ 2 := by
    calc
      3 / (4 * P) = 1 / P - 1 / (4 * P) := by
        field_simp [hP0.ne']
        ring
      _ ≤ 1 / P - P / R ^ 2 := sub_le_sub_left hsmall _
  have hcoord0 : 0 ≤ 1 / P - P / R ^ 2 :=
    le_trans (by positivity : 0 ≤ 3 / (4 * P)) hcoord
  have happ := lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0)
    (primeFirstTraceEssentialSourceDeviation p) 2
  rw [primeFirstTraceEssentialSourceDeviation_apply_two] at happ
  change |1 / P - P / R ^ 2| ≤
    ‖primeFirstTraceEssentialSourceDeviation p‖ at happ
  rw [abs_of_nonneg hcoord0] at happ
  exact hcoord.trans happ

/-- Existing local source control is uniform over all actual primes. -/
theorem norm_primeFirstTraceEssentialSourceDeviation_le (p : Nat.Primes) :
    ‖primeFirstTraceEssentialSourceDeviation p‖ ≤ 4 / (p.1 : ℝ) := by
  simpa [primeFirstTraceEssentialSourceDeviation] using
    norm_log_smul_primeHardyKernelMap_farWitness_sub_basisOne_le p

/-- Existing local response control improves to the uniform all-prime bound `5 / p`. -/
theorem norm_primeFirstTraceEssentialResponseDeviation_le (p : Nat.Primes) :
    ‖primeFirstTraceEssentialResponseDeviation p‖ ≤ 5 / (p.1 : ℝ) := by
  let P : ℝ := p.1
  have hP0 : 0 < P := by dsimp [P]; exact_mod_cast p.2.pos
  have hP2 : 2 ≤ P := by dsimp [P]; exact_mod_cast p.2.two_le
  have h := norm_primeFirstTraceEssentialResponse_blowup_sub_basisTwo_le p
  change ‖primeFirstTraceEssentialResponseDeviation p‖ ≤ 5 / P
  change ‖primeFirstTraceEssentialResponseDeviation p‖ ≤ 2 / P + 6 / P ^ 2 at h
  refine h.trans ?_
  have htail : 6 / P ^ 2 ≤ 3 / P := by
    apply (div_le_iff₀ (sq_pos_of_pos hP0)).2
    rw [show 3 / P * P ^ 2 = 3 * P by field_simp [hP0.ne']]
    nlinarith
  calc
    2 / P + 6 / P ^ 2 ≤ 2 / P + 3 / P :=
      add_le_add (le_refl _) htail
    _ = 5 / P := by ring

/-- The full ordinary-prime source correction has finite square energy. -/
theorem summable_norm_sq_primeFirstTraceEssentialSourceDeviation :
    Summable (fun p : Nat.Primes =>
      ‖primeFirstTraceEssentialSourceDeviation p‖ ^ 2) := by
  have hprime : Summable (fun p : Nat.Primes => ((p : ℝ) ^ 2)⁻¹) :=
    (Real.summable_nat_pow_inv.mpr (by norm_num)).comp_injective
      Subtype.val_injective
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun p => ?_)
    (hprime.mul_left 16)
  have hP0 : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have h := norm_primeFirstTraceEssentialSourceDeviation_le p
  have hsquare := (sq_le_sq₀ (norm_nonneg _)
    (by positivity : 0 ≤ 4 / (p : ℝ))).2 h
  calc
    ‖primeFirstTraceEssentialSourceDeviation p‖ ^ 2 ≤
        (4 / (p : ℝ)) ^ 2 := hsquare
    _ = 16 * ((p : ℝ) ^ 2)⁻¹ := by
      field_simp [hP0.ne']
      ring

/-- The full ordinary-prime response correction has finite square energy. -/
theorem summable_norm_sq_primeFirstTraceEssentialResponseDeviation :
    Summable (fun p : Nat.Primes =>
      ‖primeFirstTraceEssentialResponseDeviation p‖ ^ 2) := by
  have hprime : Summable (fun p : Nat.Primes => ((p : ℝ) ^ 2)⁻¹) :=
    (Real.summable_nat_pow_inv.mpr (by norm_num)).comp_injective
      Subtype.val_injective
  refine Summable.of_nonneg_of_le (fun _ => sq_nonneg _) (fun p => ?_)
    (hprime.mul_left 25)
  have hP0 : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have h := norm_primeFirstTraceEssentialResponseDeviation_le p
  have hsquare := (sq_le_sq₀ (norm_nonneg _)
    (by positivity : 0 ≤ 5 / (p : ℝ))).2 h
  calc
    ‖primeFirstTraceEssentialResponseDeviation p‖ ^ 2 ≤
        (5 / (p : ℝ)) ^ 2 := hsquare
    _ = 25 * ((p : ℝ) ^ 2)⁻¹ := by
      field_simp [hP0.ne']
      ring

/-- The source correction is not trace class: its absolute prime norm sum diverges. -/
theorem not_summable_norm_primeFirstTraceEssentialSourceDeviation :
    ¬ Summable (fun p : Nat.Primes =>
      ‖primeFirstTraceEssentialSourceDeviation p‖) := by
  intro hsum
  have hlower : ∀ p : Nat.Primes,
      (3 / 4 : ℝ) * (1 / (p : ℝ)) ≤
        ‖primeFirstTraceEssentialSourceDeviation p‖ := by
    intro p
    convert
      three_div_four_prime_le_norm_primeFirstTraceEssentialSourceDeviation p using 1
    ring
  have hscaled : Summable (fun p : Nat.Primes =>
      (3 / 4 : ℝ) * (1 / (p : ℝ))) :=
    Summable.of_nonneg_of_le (fun _ => by positivity) hlower hsum
  have hharmonic : Summable (fun p : Nat.Primes => 1 / (p : ℝ)) :=
    (summable_mul_left_iff (by norm_num : (3 / 4 : ℝ) ≠ 0)).mp hscaled
  exact Nat.Primes.not_summable_one_div hharmonic

/-- The source correction is a genuine all-prime `ell^(2 : ℕ)` vector. -/
theorem primeFirstTraceEssentialSourceDeviation_memℓp_two :
    Memℓp primeFirstTraceEssentialSourceDeviation 2 := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
  simpa [ENNReal.toReal_ofNat, Real.rpow_two] using
    summable_norm_sq_primeFirstTraceEssentialSourceDeviation

/-- The response correction is a genuine all-prime `ell^(2 : ℕ)` vector. -/
theorem primeFirstTraceEssentialResponseDeviation_memℓp_two :
    Memℓp primeFirstTraceEssentialResponseDeviation 2 := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
  simpa [ENNReal.toReal_ofNat, Real.rpow_two] using
    summable_norm_sq_primeFirstTraceEssentialResponseDeviation

/-- The source correction does not belong to `ell^(1 : ℕ)`. -/
theorem primeFirstTraceEssentialSourceDeviation_not_memℓp_one :
    ¬ Memℓp primeFirstTraceEssentialSourceDeviation 1 := by
  intro h
  have hs := (memℓp_gen_iff
    (by norm_num : (0 : ℝ) < (1 : ENNReal).toReal)).mp h
  apply not_summable_norm_primeFirstTraceEssentialSourceDeviation
  simpa [ENNReal.toReal_ofNat, Real.rpow_one] using hs

/-- Canonical all-prime Hilbert source correction to the essential edge. -/
def primeFirstTraceEssentialSourceCorrection :
    lp (fun _ : Nat.Primes => PrimeHardy) 2 :=
  ⟨primeFirstTraceEssentialSourceDeviation,
    primeFirstTraceEssentialSourceDeviation_memℓp_two⟩

/-- Canonical all-prime Hilbert response correction to the essential edge. -/
def primeFirstTraceEssentialResponseCorrection :
    lp (fun _ : Nat.Primes => PrimeHardy) 2 :=
  ⟨primeFirstTraceEssentialResponseDeviation,
    primeFirstTraceEssentialResponseDeviation_memℓp_two⟩

/-- The source and response corrections form the canonical global normalized essential edge. -/
def primeFirstTraceEssentialEdgeCorrection :
    lp (fun _ : Nat.Primes => PrimeHardy) 2 ×
      lp (fun _ : Nat.Primes => PrimeHardy) 2 :=
  (primeFirstTraceEssentialSourceCorrection,
    primeFirstTraceEssentialResponseCorrection)

end

end RHTower
