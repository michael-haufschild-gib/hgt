import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovIncludedMinLogForms
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovIncludedEnergy
import GaloisForLFunctions.RHTower.Sieve.GcdSumTotient
import GaloisForLFunctions.RHTower.Sieve.DivisorSquareMoment

/-!
# Reciprocal-scale cancellation and Gram positivity for the included detector boundary

The included differentiated Barban--Vehov boundary initially contains six moving minimum-log
Selberg monomials.  This module classifies their exact quadratic combination.  Every lower channel
is divisible by `1 - lam * ell`; at reciprocal tuning `lam * ell = 1`, only one cubic remainder
survives.

The survivor is not merely pointwise positive.  Its Möbius/gcd form is exactly an interval integral
of totient-weighted squares.  Gauss's gcd factorization therefore absorbs all Möbius signs and proves
unconditional nonnegativity.  This replaces the signed six-channel T1 boundary problem by one
explicit positive Gram remainder.
-/

open ArithmeticFunction Finset MeasureTheory intervalIntegral
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section


/-- Linear tent feature whose Gram kernel is the tuned cubic minimum-log remainder. -/
def linearCutoffFeature (A t : ℝ) : ℝ := A * max (A - t) 0

theorem continuous_linearCutoffFeature (A : ℝ) : Continuous (linearCutoffFeature A) := by
  unfold linearCutoffFeature
  fun_prop

theorem integral_linearGramKernel (A B u : ℝ) :
    (∫ t in (0 : ℝ)..u, A * B * (A - t) * (B - t)) =
      A * B * (u * A * B - u ^ 2 / 2 * (A + B) + u ^ 3 / 3) := by
  let F : ℝ → ℝ := fun t =>
    A * B * ((A * B) * t - ((A + B) / 2) * t ^ 2 + (1 / 3) * t ^ 3)
  have hderiv : ∀ t : ℝ, HasDerivAt F (A * B * (A - t) * (B - t)) t := by
    intro t
    have hraw := (((hasDerivAt_id t).const_mul (A * B)).sub
      (((hasDerivAt_id t).pow 2).const_mul ((A + B) / 2))).add
        (((hasDerivAt_id t).pow 3).const_mul (1 / 3)) |>.const_mul (A * B)
    have hder : HasDerivAt
        (fun y => A * B * (((A * B) * y - ((A + B) / 2) * y ^ 2) +
          (1 / 3) * y ^ 3))
        (A * B * (A - t) * (B - t)) t :=
      hraw.congr_deriv (by norm_num; ring)
    simpa only [F, id_eq] using hder
  have hint : IntervalIntegrable (fun t : ℝ => A * B * (A - t) * (B - t)) volume 0 u :=
    (show Continuous (fun t : ℝ => A * B * (A - t) * (B - t)) by fun_prop).intervalIntegrable 0 u
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t) hint]
  dsimp [F]
  ring

theorem integral_linearCutoffFeature_mul
    {A B H : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hAH : A ≤ H) (hBH : B ≤ H) :
    (∫ t in (0 : ℝ)..H, linearCutoffFeature A t * linearCutoffFeature B t) =
      A * B *
        (min A B * A * B - min A B ^ 2 / 2 * (A + B) + min A B ^ 3 / 3) := by
  have hcont : Continuous (fun t : ℝ =>
      linearCutoffFeature A t * linearCutoffFeature B t) :=
    (continuous_linearCutoffFeature A).mul (continuous_linearCutoffFeature B)
  rcases le_total A B with hAB | hBA
  · have hcore : (∫ t in (0 : ℝ)..A,
        linearCutoffFeature A t * linearCutoffFeature B t) =
        ∫ t in (0 : ℝ)..A, A * B * (A - t) * (B - t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hA0] at ht
      simp only [linearCutoffFeature]
      rw [max_eq_left (sub_nonneg.mpr ht.2),
        max_eq_left (sub_nonneg.mpr (ht.2.trans hAB))]
      ring
    have htail : (∫ t in A..H,
        linearCutoffFeature A t * linearCutoffFeature B t) = 0 := by
      rw [← intervalIntegral.integral_zero]
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hAH] at ht
      simp only [linearCutoffFeature]
      rw [max_eq_right (sub_nonpos.mpr ht.1)]
      ring
    have hcont0A : IntervalIntegrable
        (fun t : ℝ => linearCutoffFeature A t * linearCutoffFeature B t)
        volume 0 A := hcont.intervalIntegrable 0 A
    have hcontAH : IntervalIntegrable
        (fun t : ℝ => linearCutoffFeature A t * linearCutoffFeature B t)
        volume A H := hcont.intervalIntegrable A H
    have hadd := intervalIntegral.integral_add_adjacent_intervals hcont0A hcontAH
    rw [hcore, htail, add_zero, integral_linearGramKernel] at hadd
    rw [min_eq_left hAB]
    exact hadd.symm

  · have hcore : (∫ t in (0 : ℝ)..B,
        linearCutoffFeature A t * linearCutoffFeature B t) =
        ∫ t in (0 : ℝ)..B, A * B * (A - t) * (B - t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hB0] at ht
      simp only [linearCutoffFeature]
      rw [max_eq_left (sub_nonneg.mpr (ht.2.trans hBA)),
        max_eq_left (sub_nonneg.mpr ht.2)]
      ring
    have htail : (∫ t in B..H,
        linearCutoffFeature A t * linearCutoffFeature B t) = 0 := by
      rw [← intervalIntegral.integral_zero]
      apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hBH] at ht
      simp only [linearCutoffFeature]
      rw [max_eq_right (sub_nonpos.mpr ht.1)]
      ring
    have hcont0B : IntervalIntegrable
        (fun t : ℝ => linearCutoffFeature A t * linearCutoffFeature B t)
        volume 0 B := hcont.intervalIntegrable 0 B
    have hcontBH : IntervalIntegrable
        (fun t : ℝ => linearCutoffFeature A t * linearCutoffFeature B t)
        volume B H := hcont.intervalIntegrable B H
    have hadd := intervalIntegral.integral_add_adjacent_intervals hcont0B hcontBH
    rw [hcore, htail, add_zero, integral_linearGramKernel] at hadd
    rw [min_eq_right hBA]
    exact hadd.symm

/-- Weighted Gauss factorization: the gcd kernel remains positive after arbitrary real weights. -/
theorem sum_gcd_mul_weight_eq_sum_totient_mul_sq
    {S : Finset ℕ} {M : ℕ} (f : ℕ → ℝ)
    (hpos : ∀ d ∈ S, 0 < d) (hM : ∀ d ∈ S, d ≤ M) :
    (∑ p ∈ S ×ˢ S, (Nat.gcd p.1 p.2 : ℝ) * f p.1 * f p.2) =
      ∑ g ∈ Finset.Icc 1 M, (Nat.totient g : ℝ) *
        (∑ d ∈ S.filter (fun d => g ∣ d), f d) ^ 2 := by
  classical
  have hpair : ∀ p ∈ S ×ˢ S,
      (Nat.gcd p.1 p.2 : ℝ) * f p.1 * f p.2 =
        ∑ g ∈ Finset.Icc 1 M,
          (Nat.totient g : ℝ) *
            (if g ∣ p.1 then f p.1 else 0) *
              (if g ∣ p.2 then f p.2 else 0) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    rw [gcd_eq_sum_totient_indicator (Nat.one_le_iff_ne_zero.mpr
      (hpos p.1 hp1).ne') (hM p.1 hp1)
      (Nat.one_le_iff_ne_zero.mpr (hpos p.2 hp2).ne')]
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro g hg
    by_cases h1 : g ∣ p.1 <;> by_cases h2 : g ∣ p.2 <;>
      simp [h1, h2]
  rw [Finset.sum_congr rfl hpair, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g hg
  rw [Finset.sum_product]
  have hfac :
      (∑ m ∈ S, ∑ n ∈ S,
        (Nat.totient g : ℝ) * (if g ∣ m then f m else 0) *
          (if g ∣ n then f n else 0)) =
        (Nat.totient g : ℝ) *
          ((∑ m ∈ S, if g ∣ m then f m else 0) *
            (∑ n ∈ S, if g ∣ n then f n else 0)) := by
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [hfac, ← Finset.sum_filter]
  ring

/-- The sole minimum-log channel surviving the reciprocal-scale detector tuning. -/
def selbergOriginalTunedMinLogRemainder (M : ℕ) : ℝ :=
  (1 / 3 : ℝ) * selbergOriginalMinLogMonomial 1 1 3 M -
    selbergOriginalMinLogMonomial 2 1 2 M +
      selbergOriginalMinLogMonomial 2 2 1 M

theorem selbergOriginalTunedMinLogRemainder_eq_kernel (M : ℕ) :
    selbergOriginalTunedMinLogRemainder M =
      ∑ p ∈ (Finset.Icc 1 M) ×ˢ (Finset.Icc 1 M),
        let A := Real.log ((M : ℝ) / (p.1 : ℝ))
        let B := Real.log ((M : ℝ) / (p.2 : ℝ))
        let u := min A B
        selbergOriginalCoeff p.1 p.2 *
          (A * B * (u * A * B - u ^ 2 / 2 * (A + B) + u ^ 3 / 3)) := by
  unfold selbergOriginalTunedMinLogRemainder
  have hsym : -selbergOriginalMinLogMonomial 2 1 2 M =
      -(1 / 2 : ℝ) * selbergOriginalMinLogMonomial 2 1 2 M -
        (1 / 2 : ℝ) * selbergOriginalMinLogMonomial 1 2 2 M := by
    rw [selbergOriginalMinLogMonomial_comm 1 2 2 M]
    ring
  rw [sub_eq_add_neg, hsym]
  simp only [selbergOriginalMinLogMonomial]
  simp_rw [Finset.mul_sum]
  repeat
    first
    | rw [← Finset.sum_add_distrib]
    | rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  ring

/-- Exact totient-weighted square integral for the tuned minimum-log remainder. -/
theorem selbergOriginalTunedMinLogRemainder_eq_integral_totient_sq
    {M : ℕ} (hM : 0 < M) :
    selbergOriginalTunedMinLogRemainder M =
      ∫ t in (0 : ℝ)..Real.log M,
        ∑ g ∈ Finset.Icc 1 M, (Nat.totient g : ℝ) *
          (∑ m ∈ (Finset.Icc 1 M).filter (fun m => g ∣ m),
            (((ArithmeticFunction.moebius m : ℤ) : ℝ) / (m : ℝ)) *
              linearCutoffFeature (Real.log ((M : ℝ) / (m : ℝ))) t) ^ 2 := by
  let S : Finset ℕ := Finset.Icc 1 M
  let H : ℝ := Real.log M
  let A : ℕ → ℝ := fun m => Real.log ((M : ℝ) / (m : ℝ))
  let f : ℝ → ℕ → ℝ := fun t m =>
    (((ArithmeticFunction.moebius m : ℤ) : ℝ) / (m : ℝ)) *
      linearCutoffFeature (A m) t
  have hpos : ∀ m ∈ S, 0 < m := by
    intro m hm
    exact (Finset.mem_Icc.mp hm).1
  have hle : ∀ m ∈ S, m ≤ M := by
    intro m hm
    exact (Finset.mem_Icc.mp hm).2
  have hA0 : ∀ m ∈ S, 0 ≤ A m := by
    intro m hm
    have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hpos m hm
    apply Real.log_nonneg
    rw [le_div_iff₀ hmR]
    norm_num
    exact_mod_cast hle m hm
  have hAH : ∀ m ∈ S, A m ≤ H := by
    intro m hm
    have hm1R : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hpos m hm
    have hmR : (0 : ℝ) < (m : ℝ) := by positivity
    have hMR : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
    have hratio : (M : ℝ) / (m : ℝ) ≤ (M : ℝ) := by
      rw [div_le_iff₀ hmR]
      nlinarith
    exact Real.log_le_log (by positivity) hratio
  rw [selbergOriginalTunedMinLogRemainder_eq_kernel]
  have hterm : ∀ p ∈ S ×ˢ S,
      selbergOriginalCoeff p.1 p.2 *
          (A p.1 * A p.2 *
            (min (A p.1) (A p.2) * A p.1 * A p.2 -
              min (A p.1) (A p.2) ^ 2 / 2 * (A p.1 + A p.2) +
                min (A p.1) (A p.2) ^ 3 / 3)) =
        ∫ t in (0 : ℝ)..H,
          selbergOriginalCoeff p.1 p.2 *
            (linearCutoffFeature (A p.1) t * linearCutoffFeature (A p.2) t) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
    rw [← integral_linearCutoffFeature_mul (hA0 p.1 hp1) (hA0 p.2 hp2)
      (hAH p.1 hp1) (hAH p.2 hp2)]
    rw [intervalIntegral.integral_const_mul]
  change (∑ p ∈ S ×ˢ S,
      selbergOriginalCoeff p.1 p.2 *
        (A p.1 * A p.2 *
          (min (A p.1) (A p.2) * A p.1 * A p.2 -
            min (A p.1) (A p.2) ^ 2 / 2 * (A p.1 + A p.2) +
              min (A p.1) (A p.2) ^ 3 / 3))) = _
  rw [Finset.sum_congr rfl hterm]
  have hintegrable : ∀ p ∈ S ×ˢ S, IntervalIntegrable
      (fun t : ℝ => selbergOriginalCoeff p.1 p.2 *
        (linearCutoffFeature (A p.1) t * linearCutoffFeature (A p.2) t))
      volume 0 H := by
    intro p hp
    exact (continuous_const.mul ((continuous_linearCutoffFeature (A p.1)).mul
      (continuous_linearCutoffFeature (A p.2)))).intervalIntegrable 0 H
  rw [← intervalIntegral.integral_finsetSum hintegrable]
  apply intervalIntegral.integral_congr
  intro t ht
  change (∑ p ∈ S ×ˢ S, selbergOriginalCoeff p.1 p.2 *
      (linearCutoffFeature (A p.1) t * linearCutoffFeature (A p.2) t)) =
    ∑ g ∈ Finset.Icc 1 M, (Nat.totient g : ℝ) *
      (∑ m ∈ S.filter (fun m => g ∣ m), f t m) ^ 2
  have hinner :
      (∑ p ∈ S ×ˢ S, selbergOriginalCoeff p.1 p.2 *
        (linearCutoffFeature (A p.1) t * linearCutoffFeature (A p.2) t)) =
        ∑ p ∈ S ×ˢ S, (Nat.gcd p.1 p.2 : ℝ) * f t p.1 * f t p.2 := by
    apply Finset.sum_congr rfl
    intro p hp
    simp only [selbergOriginalCoeff, f]
    ring
  rw [hinner, sum_gcd_mul_weight_eq_sum_totient_mul_sq (f t) hpos hle]

/-- The tuned minimum-log survivor is nonnegative for every positive cutoff. -/
theorem selbergOriginalTunedMinLogRemainder_nonneg
    {M : ℕ} (hM : 0 < M) :
    0 ≤ selbergOriginalTunedMinLogRemainder M := by
  rw [selbergOriginalTunedMinLogRemainder_eq_integral_totient_sq hM]
  have hlog : 0 ≤ Real.log M :=
    Real.log_nonneg (by exact_mod_cast hM)
  apply intervalIntegral.integral_nonneg hlog
  intro t ht
  exact Finset.sum_nonneg fun g hg =>
    mul_nonneg (by positivity) (sq_nonneg _)

/-- Minimum-log sector of the included detector boundary quadratic. -/
def selbergOriginalIncludedMinLogEnergy (lam ell : ℝ) (M : ℕ) : ℝ :=
  selbergOriginalMinLogMonomial 1 1 1 M +
    2 * lam *
      (-ell * selbergOriginalMinLogMonomial 1 1 1 M -
        (1 / 2 : ℝ) * selbergOriginalMinLogMonomial 1 1 2 M +
          selbergOriginalMinLogMonomial 2 1 1 M) +
    lam ^ 2 *
      (ell ^ 2 * selbergOriginalMinLogMonomial 1 1 1 M +
        ell * selbergOriginalMinLogMonomial 1 1 2 M +
        (1 / 3 : ℝ) * selbergOriginalMinLogMonomial 1 1 3 M -
        2 * ell * selbergOriginalMinLogMonomial 2 1 1 M -
        selbergOriginalMinLogMonomial 2 1 2 M +
        selbergOriginalMinLogMonomial 2 2 1 M)

/-- Exact hostile classification: away from reciprocal tuning, only three lower channels survive,
each carrying an explicit factor of `1 - lam * ell`. -/
theorem selbergOriginalIncludedMinLogEnergy_eq_tunedRemainder_add_mismatch
    (lam ell : ℝ) (M : ℕ) :
    selbergOriginalIncludedMinLogEnergy lam ell M =
      lam ^ 2 * selbergOriginalTunedMinLogRemainder M +
        (1 - lam * ell) ^ 2 * selbergOriginalMinLogMonomial 1 1 1 M -
        lam * (1 - lam * ell) * selbergOriginalMinLogMonomial 1 1 2 M +
        2 * lam * (1 - lam * ell) * selbergOriginalMinLogMonomial 2 1 1 M := by
  unfold selbergOriginalIncludedMinLogEnergy
  unfold selbergOriginalTunedMinLogRemainder
  ring

/-- Reciprocal detector tuning cancels every lower minimum-log channel exactly. -/
theorem selbergOriginalIncludedMinLogEnergy_eq_tunedRemainder
    {lam ell : ℝ} (M : ℕ) (htune : lam * ell = 1) :
    selbergOriginalIncludedMinLogEnergy lam ell M =
      lam ^ 2 * selbergOriginalTunedMinLogRemainder M := by
  rw [selbergOriginalIncludedMinLogEnergy_eq_tunedRemainder_add_mismatch]
  rw [htune]
  ring

/-- At reciprocal tuning the complete minimum-log sector is nonnegative. -/
theorem selbergOriginalIncludedMinLogEnergy_nonneg_of_tuned
    {lam ell : ℝ} {M : ℕ} (hM : 0 < M) (htune : lam * ell = 1) :
    0 ≤ selbergOriginalIncludedMinLogEnergy lam ell M := by
  rw [selbergOriginalIncludedMinLogEnergy_eq_tunedRemainder M htune]
  exact mul_nonneg (sq_nonneg lam) (selbergOriginalTunedMinLogRemainder_nonneg hM)

/-- Ordinary-log sector complementary to the minimum-log boundary. -/
def selbergOriginalIncludedOrdinaryEnergy (lam ell : ℝ) (M : ℕ) : ℝ :=
  (Real.log M * selbergOriginalLogMonomial 1 1 M -
      2 * selbergOriginalLogMonomial 1 2 M) +
    2 * lam *
      (-(ell * Real.log M - Real.log M ^ 2 / 2) *
          selbergOriginalLogMonomial 1 1 M +
        (2 * ell - Real.log M) * selbergOriginalLogMonomial 1 2 M) +
    lam ^ 2 *
      ((Real.log M * ell ^ 2 - ell * Real.log M ^ 2 + Real.log M ^ 3 / 3) *
          selbergOriginalLogMonomial 1 1 M -
        2 * (ell ^ 2 - ell * Real.log M + Real.log M ^ 2 / 2) *
          selbergOriginalLogMonomial 1 2 M +
        (1 / 3 : ℝ) * selbergOriginalLogMonomial 1 4 M -
        selbergOriginalLogMonomial 2 3 M +
        Real.log M * selbergOriginalLogMonomial 2 2 M)

/-- Exact signed split of the three included boundaries into ordinary and minimum-log sectors. -/
theorem selbergOriginalIncludedBoundaryEnergy_eq_ordinary_add_minLog
    (lam ell : ℝ) (M : ℕ) :
    selbergOriginalIncludedBaseBoundary M +
        2 * lam * selbergOriginalIncludedCrossBoundary ell M +
        lam ^ 2 * selbergOriginalIncludedDerivativeBoundary ell M =
      selbergOriginalIncludedOrdinaryEnergy lam ell M +
        selbergOriginalIncludedMinLogEnergy lam ell M := by
  rw [selbergOriginalIncludedBaseBoundary_eq_logMonomials,
    selbergOriginalIncludedCrossBoundary_eq_logMonomials,
    selbergOriginalIncludedDerivativeBoundary_eq_logMonomials]
  unfold selbergOriginalIncludedOrdinaryEnergy
  unfold selbergOriginalIncludedMinLogEnergy
  ring

/-- At reciprocal tuning the whole included boundary has one and only one minimum-log survivor. -/
theorem selbergOriginalIncludedBoundaryEnergy_eq_ordinary_add_tunedRemainder
    {lam ell : ℝ} (M : ℕ) (htune : lam * ell = 1) :
    selbergOriginalIncludedBaseBoundary M +
        2 * lam * selbergOriginalIncludedCrossBoundary ell M +
        lam ^ 2 * selbergOriginalIncludedDerivativeBoundary ell M =
      selbergOriginalIncludedOrdinaryEnergy lam ell M +
        lam ^ 2 * selbergOriginalTunedMinLogRemainder M := by
  rw [selbergOriginalIncludedBoundaryEnergy_eq_ordinary_add_minLog,
    selbergOriginalIncludedMinLogEnergy_eq_tunedRemainder M htune]

/-- Detector-facing tuned polynomial identity: six moving minimum-log asymptotics are replaced by
one explicit nonnegative Gram remainder. -/
theorem barbanVehovIncludedLongEnergyPolynomialMain_eq_ordinary_add_tunedRemainder
    {lam ell : ℝ} {M : ℕ} (hM : 0 < M) (htune : lam * ell = 1) :
    barbanVehovIncludedLongEnergyPolynomialMain lam ell M =
      (selbergOriginalIncludedOrdinaryEnergy lam ell M +
        lam ^ 2 * selbergOriginalTunedMinLogRemainder M) / Real.log M ^ 2 := by
  rw [barbanVehovIncludedLongEnergyPolynomialMain,
    barbanVehovIncludedLongBasePolynomialMain_eq_originalBoundary hM,
    barbanVehovIncludedLongCrossPolynomialMain_eq_originalBoundary ell hM,
    barbanVehovIncludedLongDerivativePolynomialMain_eq_originalBoundary ell hM,
    selbergOriginalIncludedBoundaryEnergy_eq_ordinary_add_tunedRemainder M htune]

/-- Coercive detector form: reciprocal tuning leaves the ordinary sector below the exact included
polynomial by one nonnegative Gram remainder. -/
theorem selbergOriginalIncludedOrdinaryEnergy_div_log_sq_le_polynomialMain_of_tuned
    {lam ell : ℝ} {M : ℕ} (hM : 1 < M) (htune : lam * ell = 1) :
    selbergOriginalIncludedOrdinaryEnergy lam ell M / Real.log M ^ 2 ≤
      barbanVehovIncludedLongEnergyPolynomialMain lam ell M := by
  rw [barbanVehovIncludedLongEnergyPolynomialMain_eq_ordinary_add_tunedRemainder
    (Nat.zero_lt_of_lt hM) htune]
  apply div_le_div_of_nonneg_right _ (sq_nonneg (Real.log M))
  exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg lam)
    (selbergOriginalTunedMinLogRemainder_nonneg (Nat.zero_lt_of_lt hM)))

end

end RHTower.Sieve
