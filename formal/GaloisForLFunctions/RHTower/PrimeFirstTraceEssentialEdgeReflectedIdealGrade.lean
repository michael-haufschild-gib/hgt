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

/-! ## Literal activation-Fisher provenance -/

/-- Ordinary-prime occupancy Fisher density selected by diagonal Euler activation. -/
def primeActivationOccupancyFisherDensity (p : Nat.Primes) : ℝ :=
  diagonalActivationOccupancyFisher
    (xiTransversePrimeApertureDiskNode 1 p)

/-- Modular transport of the source-selected occupancy Fisher density. -/
def primeActivationOccupancyFisherTwist (t : ℝ) (p : Nat.Primes) : ℝ :=
  (p.1 : ℝ) ^ t * primeActivationOccupancyFisherDensity p

/-- Occupancy Fisher is exactly the square of the Möbius-to-Gamma damping. -/
theorem primeActivationOccupancyFisherDensity_eq_damping_sq
    (p : Nat.Primes) :
    primeActivationOccupancyFisherDensity p =
      xiMobiusPrimeSchurValuationDamping p ^ 2 := by
  exact (xiMobiusPrimeSchurValuationDamping_sq_eq_activationOccupancyFisher p).symm

/-- Closed rational form of the ordinary-prime Fisher density. -/
theorem primeActivationOccupancyFisherDensity_eq (p : Nat.Primes) :
    primeActivationOccupancyFisherDensity p =
      (p.1 : ℝ) / ((p.1 : ℝ) + 1) ^ 2 := by
  have hp0 : (p.1 : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  rw [primeActivationOccupancyFisherDensity,
    diagonalActivationOccupancyFisher,
    xiTransversePrimeApertureDiskNode_one_eq_inv]
  field_simp [hp0]

/-- Occupancy Fisher differs from the prime harmonic density by a positive `O(p⁻²)` term. -/
theorem primeActivationOccupancyFisherDensity_harmonic_difference_bounds
    (p : Nat.Primes) :
    0 ≤ 1 / (p.1 : ℝ) - primeActivationOccupancyFisherDensity p ∧
      1 / (p.1 : ℝ) - primeActivationOccupancyFisherDensity p ≤
        3 / (p.1 : ℝ) ^ 2 := by
  let P : ℝ := p.1
  have hP0 : 0 < P := by dsimp [P]; exact_mod_cast p.2.pos
  have hP1 : 1 ≤ P := by dsimp [P]; exact_mod_cast p.2.one_lt.le
  rw [primeActivationOccupancyFisherDensity_eq]
  change 0 ≤ 1 / P - P / (P + 1) ^ 2 ∧
    1 / P - P / (P + 1) ^ 2 ≤ 3 / P ^ 2
  have hdiff :
      1 / P - P / (P + 1) ^ 2 =
        (2 * P + 1) / (P * (P + 1) ^ 2) := by
    field_simp [hP0.ne']
    ring
  rw [hdiff]
  constructor
  · positivity
  · rw [div_le_div_iff₀ (by positivity) (sq_pos_of_pos hP0)]
    have haux : 0 ≤ P * (P ^ 2 + 5 * P + 3) :=
      mul_nonneg hP0.le (by nlinarith [sq_nonneg P])
    nlinarith

/-- The literal essential edge and occupancy Fisher density differ by at most `4 / p²`. -/
theorem primeFirstTraceEssentialHarmonicCoordinate_sub_fisher_abs_le
    (p : Nat.Primes) :
    |primeFirstTraceEssentialHarmonicCoordinate p -
        primeActivationOccupancyFisherDensity p| ≤
      4 / (p.1 : ℝ) ^ 2 := by
  let P : ℝ := p.1
  let R : ℝ := (farPrime p).1
  have hP0 : 0 < P := by dsimp [P]; exact_mod_cast p.2.pos
  have hP1 : 1 ≤ P := by dsimp [P]; exact_mod_cast p.2.one_lt.le
  have hR0 : 0 < R := by dsimp [R]; exact_mod_cast (farPrime p).2.pos
  have hsq : P ^ 2 ≤ R := by
    dsimp [P, R]
    exact_mod_cast (farPrime_sq_lt p).le
  have hR2' : (P ^ 2) ^ 2 ≤ R ^ 2 :=
    (sq_le_sq₀ (sq_nonneg P) hR0.le).2 hsq
  have hR2 : P ^ 4 ≤ R ^ 2 := by nlinarith
  have hfar : P / R ^ 2 ≤ 1 / P ^ 3 := by
    calc
      P / R ^ 2 ≤ P / P ^ 4 :=
        div_le_div_of_nonneg_left hP0.le (by positivity) hR2
      _ = 1 / P ^ 3 := by field_simp [hP0.ne']
  have hfisher :=
    primeActivationOccupancyFisherDensity_harmonic_difference_bounds p
  rw [primeFirstTraceEssentialHarmonicCoordinate_eq]
  change |(1 / P - P / R ^ 2) - primeActivationOccupancyFisherDensity p| ≤
    4 / P ^ 2
  calc
    |(1 / P - P / R ^ 2) - primeActivationOccupancyFisherDensity p| =
        |(1 / P - primeActivationOccupancyFisherDensity p) - P / R ^ 2| := by
          congr 1
          ring
    _ ≤ |1 / P - primeActivationOccupancyFisherDensity p| + |P / R ^ 2| :=
      abs_sub _ _
    _ = (1 / P - primeActivationOccupancyFisherDensity p) + P / R ^ 2 := by
      rw [abs_of_nonneg hfisher.1, abs_of_nonneg (by positivity)]
    _ ≤ 3 / P ^ 2 + 1 / P ^ 3 := add_le_add hfisher.2 hfar
    _ ≤ 4 / P ^ 2 := by
      have htail : 1 / P ^ 3 ≤ 1 / P ^ 2 := by
        rw [div_le_div_iff₀ (pow_pos hP0 3) (pow_pos hP0 2)]
        nlinarith [mul_nonneg (sq_nonneg P) (sub_nonneg.mpr hP1)]
      calc
        3 / P ^ 2 + 1 / P ^ 3 ≤ 3 / P ^ 2 + 1 / P ^ 2 :=
          add_le_add_right htail _
        _ = 4 / P ^ 2 := by ring

/-- Below modular rate one, actual-edge and activation-Fisher twists define the same class modulo
`ell¹`. -/
theorem summable_primeFirstTraceEssentialHarmonicTwist_sub_fisherTwist_of_lt_one
    {t : ℝ} (ht : t < 1) :
    Summable (fun p : Nat.Primes =>
      primeFirstTraceEssentialHarmonicTwist t p -
        primeActivationOccupancyFisherTwist t p) := by
  have hpow : Summable (fun p : Nat.Primes =>
      4 * (p.1 : ℝ) ^ (t - 2)) :=
    ((Nat.Primes.summable_rpow).2 (by linarith)).mul_left 4
  have habs : Summable (fun p : Nat.Primes =>
      |primeFirstTraceEssentialHarmonicTwist t p -
        primeActivationOccupancyFisherTwist t p|) := by
    refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun p => ?_) hpow
    have hP0 : 0 < (p.1 : ℝ) := by exact_mod_cast p.2.pos
    rw [primeFirstTraceEssentialHarmonicTwist,
      primeActivationOccupancyFisherTwist, ← mul_sub, abs_mul,
      abs_of_nonneg (Real.rpow_nonneg hP0.le t)]
    calc
      (p.1 : ℝ) ^ t *
          |primeFirstTraceEssentialHarmonicCoordinate p -
            primeActivationOccupancyFisherDensity p| ≤
          (p.1 : ℝ) ^ t * (4 / (p.1 : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left
          (primeFirstTraceEssentialHarmonicCoordinate_sub_fisher_abs_le p)
          (Real.rpow_nonneg hP0.le t)
      _ = 4 * (p.1 : ℝ) ^ (t - 2) := by
        calc
          (p.1 : ℝ) ^ t * (4 / (p.1 : ℝ) ^ 2) =
              4 * ((p.1 : ℝ) ^ t / (p.1 : ℝ) ^ 2) := by ring
          _ = 4 * (p.1 : ℝ) ^ (t - 2) := by
            rw [← Real.rpow_natCast (p.1 : ℝ) 2,
              ← Real.rpow_sub hP0]
            norm_num
  exact summable_norm_iff.mp (by simpa [Real.norm_eq_abs] using habs)

/-- In the moderate strip `t < 1`, source Fisher has the same exact trace-ideal grade as the
literal essential edge. -/
theorem summable_primeActivationOccupancyFisherTwist_iff_of_lt_one
    {t : ℝ} (ht : t < 1) :
    Summable (primeActivationOccupancyFisherTwist t) ↔ t < 0 := by
  have hdiff :=
    summable_primeFirstTraceEssentialHarmonicTwist_sub_fisherTwist_of_lt_one ht
  rw [← summable_primeFirstTraceEssentialHarmonicTwist_iff t]
  constructor
  · intro hfisher
    have hadd := hdiff.add hfisher
    exact hadd.congr (fun p => by
      ring)
  · intro hedge
    have hsub := hedge.sub hdiff
    exact hsub.congr (fun p => by
      ring)

/-- Every actual Xi-divisor centered modular rate lies in `(-1,1)`. -/
theorem xiCenteredPrimeIdealRate_abs_lt_one (rho : XiDivisorSupport) :
    |2 * (rho : ℂ).re - 1| < 1 := by
  have hstrip := xi_divisor_support_re_mem_open_unit rho
  rw [abs_lt]
  constructor <;> linarith

/-- Forward actual edge and forward activation Fisher represent the same critical-strip relative
ideal class at every Xi divisor. -/
theorem xi_actualEdge_forward_sub_activationFisher_summable
    (rho : XiDivisorSupport) :
    Summable (fun p : Nat.Primes =>
      primeFirstTraceEssentialHarmonicTwist (2 * (rho : ℂ).re - 1) p -
        primeActivationOccupancyFisherTwist (2 * (rho : ℂ).re - 1) p) := by
  apply summable_primeFirstTraceEssentialHarmonicTwist_sub_fisherTwist_of_lt_one
  exact (abs_lt.mp (xiCenteredPrimeIdealRate_abs_lt_one rho)).2

/-- Reflected actual edge and reflected activation Fisher represent the same critical-strip
relative ideal class at every Xi divisor. -/
theorem xi_actualEdge_reflected_sub_activationFisher_summable
    (rho : XiDivisorSupport) :
    Summable (fun p : Nat.Primes =>
      primeFirstTraceEssentialHarmonicTwist (-(2 * (rho : ℂ).re - 1)) p -
        primeActivationOccupancyFisherTwist (-(2 * (rho : ℂ).re - 1)) p) := by
  apply summable_primeFirstTraceEssentialHarmonicTwist_sub_fisherTwist_of_lt_one
  linarith [(abs_lt.mp (xiCenteredPrimeIdealRate_abs_lt_one rho)).1]

/-! ## Exact common-Hilbert threshold of the source Fisher endpoints -/

/-- The source-selected Fisher density is uniformly comparable to the prime harmonic density.
The lower constant is deliberately uniform: it is what makes the converse square-summability
classification coefficient-faithful. -/
theorem primeActivationOccupancyFisherDensity_bounds (p : Nat.Primes) :
    1 / (4 * (p.1 : ℝ)) ≤ primeActivationOccupancyFisherDensity p ∧
      primeActivationOccupancyFisherDensity p ≤ 1 / (p.1 : ℝ) := by
  let P : ℝ := p.1
  have hP0 : 0 < P := by dsimp [P]; exact_mod_cast p.2.pos
  have hP1 : 1 ≤ P := by dsimp [P]; exact_mod_cast p.2.one_lt.le
  rw [primeActivationOccupancyFisherDensity_eq]
  change 1 / (4 * P) ≤ P / (P + 1) ^ 2 ∧
    P / (P + 1) ^ 2 ≤ 1 / P
  constructor
  · rw [div_le_div_iff₀ (by positivity : 0 < 4 * P)
      (sq_pos_of_pos (by linarith : 0 < P + 1))]
    nlinarith [sq_nonneg (P - 1)]
  · rw [div_le_div_iff₀ (sq_pos_of_pos (by linarith : 0 < P + 1)) hP0]
    nlinarith

/-- Every modular Fisher twist remains between two fixed multiples of its prime-power model. -/
theorem primeActivationOccupancyFisherTwist_bounds (t : ℝ) (p : Nat.Primes) :
    (1 / 4 : ℝ) * (p.1 : ℝ) ^ (t - 1) ≤
        primeActivationOccupancyFisherTwist t p ∧
      primeActivationOccupancyFisherTwist t p ≤
        (p.1 : ℝ) ^ (t - 1) := by
  have hP0 : 0 < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  have hpow : 0 ≤ (p.1 : ℝ) ^ t := Real.rpow_nonneg hP0.le t
  constructor
  · calc
      (1 / 4 : ℝ) * (p.1 : ℝ) ^ (t - 1) =
          (p.1 : ℝ) ^ t * (1 / (4 * (p.1 : ℝ))) := by
            rw [show t - 1 = t + (-1) by ring,
              Real.rpow_add hP0, Real.rpow_neg_one]
            ring
      _ ≤ (p.1 : ℝ) ^ t * primeActivationOccupancyFisherDensity p :=
        mul_le_mul_of_nonneg_left
          (primeActivationOccupancyFisherDensity_bounds p).1 hpow
      _ = primeActivationOccupancyFisherTwist t p := rfl
  · calc
      primeActivationOccupancyFisherTwist t p ≤
          (p.1 : ℝ) ^ t * (1 / (p.1 : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (primeActivationOccupancyFisherDensity_bounds p).2 hpow
      _ = (p.1 : ℝ) ^ (t - 1) := by
        rw [show t - 1 = t + (-1) by ring,
          Real.rpow_add hP0, Real.rpow_neg_one]
        ring

private theorem primeActivationOccupancyFisherTwist_nonneg
    (t : ℝ) (p : Nat.Primes) :
    0 ≤ primeActivationOccupancyFisherTwist t p := by
  have hP0 : 0 < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  have hf : 0 ≤ primeActivationOccupancyFisherDensity p :=
    (by positivity : 0 ≤ 1 / (4 * (p.1 : ℝ))).trans
      (primeActivationOccupancyFisherDensity_bounds p).1
  exact mul_nonneg (Real.rpow_nonneg hP0.le t) hf

private theorem primeActivationOccupancyFisherTwist_sq_upper
    (t : ℝ) (p : Nat.Primes) :
    (primeActivationOccupancyFisherTwist t p) ^ 2 ≤
      (p.1 : ℝ) ^ (2 * (t - 1)) := by
  have hP0 : 0 < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  calc
    (primeActivationOccupancyFisherTwist t p) ^ 2 ≤
        ((p.1 : ℝ) ^ (t - 1)) ^ 2 :=
      (sq_le_sq₀ (primeActivationOccupancyFisherTwist_nonneg t p)
        (Real.rpow_nonneg hP0.le (t - 1))).2
          (primeActivationOccupancyFisherTwist_bounds t p).2
    _ = (p.1 : ℝ) ^ (2 * (t - 1)) := by
      rw [← Real.rpow_natCast ((p.1 : ℝ) ^ (t - 1)) 2,
        ← Real.rpow_mul hP0.le]
      congr 1
      ring

private theorem primeActivationOccupancyFisherTwist_sq_lower
    (t : ℝ) (p : Nat.Primes) :
    (1 / 16 : ℝ) * (p.1 : ℝ) ^ (2 * (t - 1)) ≤
      (primeActivationOccupancyFisherTwist t p) ^ 2 := by
  have hP0 : 0 < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  have hsq : ((p.1 : ℝ) ^ (t - 1)) ^ 2 =
      (p.1 : ℝ) ^ (2 * (t - 1)) := by
    rw [← Real.rpow_natCast ((p.1 : ℝ) ^ (t - 1)) 2,
      ← Real.rpow_mul hP0.le]
    congr 1
    ring
  calc
    (1 / 16 : ℝ) * (p.1 : ℝ) ^ (2 * (t - 1)) =
        ((1 / 4 : ℝ) * (p.1 : ℝ) ^ (t - 1)) ^ 2 := by
      rw [mul_pow, hsq]
      norm_num
    _ ≤ (primeActivationOccupancyFisherTwist t p) ^ 2 :=
      (sq_le_sq₀ (mul_nonneg (by positivity)
          (Real.rpow_nonneg hP0.le (t - 1)))
        (primeActivationOccupancyFisherTwist_nonneg t p)).2
          (primeActivationOccupancyFisherTwist_bounds t p).1

/-- Exact Hilbert threshold of the literal source-selected Fisher twist.  In particular, the
critical-strip condition `t < 1` is not enough to place this class in `ell²`: the sharp wall is
`t = 1/2`. -/
theorem summable_sq_primeActivationOccupancyFisherTwist_iff (t : ℝ) :
    Summable (fun p : Nat.Primes =>
      (primeActivationOccupancyFisherTwist t p) ^ 2) ↔
      t < 1 / 2 := by
  constructor
  · intro hsum
    have hscaled : Summable (fun p : Nat.Primes =>
        (1 / 16 : ℝ) * (p.1 : ℝ) ^ (2 * (t - 1))) :=
      Summable.of_nonneg_of_le (fun _ => by positivity)
        (primeActivationOccupancyFisherTwist_sq_lower t) hsum
    have hpow : Summable (fun p : Nat.Primes =>
        (p.1 : ℝ) ^ (2 * (t - 1))) :=
      (summable_mul_left_iff (by norm_num : (1 / 16 : ℝ) ≠ 0)).mp hscaled
    have hexp := (Nat.Primes.summable_rpow).mp hpow
    linarith
  · intro ht
    have hmajor : Summable (fun p : Nat.Primes =>
        (p.1 : ℝ) ^ (2 * (t - 1))) :=
      (Nat.Primes.summable_rpow).2 (by linarith)
    exact Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
      (primeActivationOccupancyFisherTwist_sq_upper t) hmajor

/-- The two reflected source Fisher endpoints inhabit one common prime `ell²` carrier exactly in
the strict central half-strip.  This is the sharp obstruction to treating all Xi-divisor twists
as classes of one fixed `ell²/ell¹` completion. -/
theorem summable_sq_reflected_primeActivationOccupancyFisherTwist_iff
    (t : ℝ) :
    (Summable (fun p : Nat.Primes =>
        (primeActivationOccupancyFisherTwist t p) ^ 2) ∧
      Summable (fun p : Nat.Primes =>
        (primeActivationOccupancyFisherTwist (-t) p) ^ 2)) ↔
      |t| < 1 / 2 := by
  rw [summable_sq_primeActivationOccupancyFisherTwist_iff,
    summable_sq_primeActivationOccupancyFisherTwist_iff, abs_lt]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

end


end RHTower
