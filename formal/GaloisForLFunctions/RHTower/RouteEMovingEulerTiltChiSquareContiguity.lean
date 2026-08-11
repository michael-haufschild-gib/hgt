import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.BernoulliBooleanGibbs
import GaloisForLFunctions.HTGeometry.InfiniteProductNearOne
import GaloisForLFunctions.RHTower.EulerActivationSquarefreeProbability
import GaloisForLFunctions.RHTower.PrimeClockFiniteScaling
import GaloisForLFunctions.RHTower.Sieve.PrimeCosineSum

/-!
# Route E moving Euler-tilt chi-square contiguity

The source-faithful squarefree Gibbs representation uses Bernoulli occupations
`q_{p,sigma} = p^{-sigma} / (1 + p^{-sigma})`.  This module proves the exact finite likelihood and
chi-square product laws, then compares the local chi-square defect between `sigma = 1 + delta`
and `sigma = 1` with the existing reflected prime-clock energy:

`chiSq(nu_{1+delta,N} || nu_{1,N}) <= exp(E_N(delta/2)) - 1`.

Consequently every nonnegative supercritical tilt with `delta_N log N -> 0` is chi-square
contiguous to the critical finite Bernoulli source.  A finite Cauchy--Schwarz theorem transfers
every observable, not only events.  This removes the moving-Euler-source mismatch from Route E's
unit-shell incidence problem; it does not assert or assume that missing incidence theorem.
-/

open scoped BigOperators

namespace RHTower

open HTGeometry.ConstraintFrameRelativity

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def bernoulliLikelihood (q r : ι → ℝ) (S : Finset ι) : ℝ :=
  (∏ p ∈ S, q p / r p) * ∏ p ∈ Sᶜ, (1 - q p) / (1 - r p)

lemma bernoulliWeight_mul_likelihood
    (q r : ι → ℝ) (hr0 : ∀ p, r p ≠ 0) (hr1 : ∀ p, 1 - r p ≠ 0)
    (S : Finset ι) :
    bernoulliWeight r S * bernoulliLikelihood q r S = bernoulliWeight q S := by
  rw [bernoulliWeight, bernoulliWeight, bernoulliLikelihood,
    Finset.prod_div_distrib, Finset.prod_div_distrib]
  have hS0 : ∏ p ∈ S, r p ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p _ => hr0 p
  have hSc0 : ∏ p ∈ Sᶜ, (1 - r p) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p _ => hr1 p
  field_simp [hS0, hSc0]

def bernoulliChiSquare (q r : ι → ℝ) : ℝ :=
  bernoulliExp r (fun S => (bernoulliLikelihood q r S - 1) ^ 2)

lemma bernoulliLikelihoodSecondMoment_eq_prod
    (q r : ι → ℝ) :
    bernoulliExp r (fun S => bernoulliLikelihood q r S ^ 2) =
      ∏ p, (r p * (q p / r p) ^ 2 +
        (1 - r p) * ((1 - q p) / (1 - r p)) ^ 2) := by
  have h := bernoulliExp_prod r (fun p => (q p / r p) ^ 2)
    (fun p => ((1 - q p) / (1 - r p)) ^ 2)
  rw [← h]
  unfold bernoulliExp
  apply Finset.sum_congr rfl
  intro S hS
  congr 1
  simp only [bernoulliLikelihood, mul_pow, Finset.prod_pow]

lemma bernoulliChiSquare_eq_secondMoment_sub_one
    (q r : ι → ℝ) (hr0 : ∀ p, r p ≠ 0) (hr1 : ∀ p, 1 - r p ≠ 0) :
    bernoulliChiSquare q r =
      bernoulliExp r (fun S => bernoulliLikelihood q r S ^ 2) - 1 := by
  rw [bernoulliChiSquare, bernoulliExp]
  have hmean : ∑ S : Finset ι,
      bernoulliWeight r S * bernoulliLikelihood q r S = 1 := by
    calc
      _ = ∑ S : Finset ι, bernoulliWeight q S := by
        apply Finset.sum_congr rfl
        intro S hS
        exact bernoulliWeight_mul_likelihood q r hr0 hr1 S
      _ = 1 := by
        simpa [bernoulliExp] using bernoulliExp_one q
  have hmass : ∑ S : Finset ι, bernoulliWeight r S = 1 := by
    simpa [bernoulliExp] using bernoulliExp_one r
  have hexpand : (∑ S : Finset ι,
      bernoulliWeight r S * (bernoulliLikelihood q r S - 1) ^ 2) =
      (∑ S : Finset ι, bernoulliWeight r S * bernoulliLikelihood q r S ^ 2) -
        2 * (∑ S : Finset ι, bernoulliWeight r S * bernoulliLikelihood q r S) +
        ∑ S : Finset ι, bernoulliWeight r S := by
    calc
      _ = ∑ S : Finset ι,
          (bernoulliWeight r S * bernoulliLikelihood q r S ^ 2 -
            2 * (bernoulliWeight r S * bernoulliLikelihood q r S) +
            bernoulliWeight r S) := by
              apply Finset.sum_congr rfl
              intro S hS
              ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hexpand]
  rw [hmean, hmass]
  simp only [bernoulliExp]
  ring

lemma localBernoulliSecondMoment_eq
    {q r : ℝ} (hr0 : r ≠ 0) (hr1 : 1 - r ≠ 0) :
    r * (q / r) ^ 2 + (1 - r) * ((1 - q) / (1 - r)) ^ 2 =
      1 + (q - r) ^ 2 / (r * (1 - r)) := by
  field_simp [hr0, hr1]
  ring

lemma bernoulliChiSquare_eq_prod_local
    (q r : ι → ℝ) (hr0 : ∀ p, r p ≠ 0) (hr1 : ∀ p, 1 - r p ≠ 0) :
    bernoulliChiSquare q r =
      (∏ p, (1 + (q p - r p) ^ 2 / (r p * (1 - r p)))) - 1 := by
  rw [bernoulliChiSquare_eq_secondMoment_sub_one q r hr0 hr1,
    bernoulliLikelihoodSecondMoment_eq_prod]
  congr 2
  funext p
  exact localBernoulliSecondMoment_eq (hr0 p) (hr1 p)

lemma bernoulliWeight_nonneg
    (r : ι → ℝ) (hr0 : ∀ p, 0 ≤ r p) (hr1 : ∀ p, r p ≤ 1)
    (S : Finset ι) : 0 ≤ bernoulliWeight r S := by
  unfold bernoulliWeight
  exact mul_nonneg
    (Finset.prod_nonneg fun p hp => hr0 p)
    (Finset.prod_nonneg fun p hp => sub_nonneg.mpr (hr1 p))

lemma bernoulliExp_changeOfMeasure
    (q r : ι → ℝ) (hr0 : ∀ p, r p ≠ 0) (hr1 : ∀ p, 1 - r p ≠ 0)
    (f : Finset ι → ℝ) :
    bernoulliExp q f =
      bernoulliExp r (fun S => bernoulliLikelihood q r S * f S) := by
  unfold bernoulliExp
  apply Finset.sum_congr rfl
  intro S hS
  rw [← bernoulliWeight_mul_likelihood q r hr0 hr1 S]
  ring

lemma bernoulliExp_sq_nonneg
    (r : ι → ℝ) (hr0 : ∀ p, 0 ≤ r p) (hr1 : ∀ p, r p ≤ 1)
    (f : Finset ι → ℝ) : 0 ≤ bernoulliExp r (fun S => f S ^ 2) := by
  unfold bernoulliExp
  exact Finset.sum_nonneg fun S hS => mul_nonneg
    (bernoulliWeight_nonneg r hr0 hr1 S) (sq_nonneg _)

/-- Finite chi-square transfer for every observable, not only events. -/
theorem bernoulliExp_sub_sq_le_chiSquare_mul_secondMoment
    (q r : ι → ℝ) (hr0 : ∀ p, 0 < r p) (hr1 : ∀ p, r p < 1)
    (f : Finset ι → ℝ) :
    (bernoulliExp q f - bernoulliExp r f) ^ 2 ≤
      bernoulliChiSquare q r * bernoulliExp r (fun S => f S ^ 2) := by
  have hchange := bernoulliExp_changeOfMeasure q r
    (fun p => (hr0 p).ne') (fun p => (sub_pos.mpr (hr1 p)).ne') f
  have hdiff : bernoulliExp q f - bernoulliExp r f =
      ∑ S : Finset ι, bernoulliWeight r S *
        ((bernoulliLikelihood q r S - 1) * f S) := by
    rw [hchange]
    unfold bernoulliExp
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro S hS
    ring
  have hw0 : ∀ S : Finset ι, 0 ≤ bernoulliWeight r S :=
    bernoulliWeight_nonneg r (fun p => (hr0 p).le) (fun p => (hr1 p).le)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset (Finset ι))
    (fun S => Real.sqrt (bernoulliWeight r S) *
      (bernoulliLikelihood q r S - 1))
    (fun S => Real.sqrt (bernoulliWeight r S) * f S)
  rw [hdiff]
  calc
    (∑ S : Finset ι, bernoulliWeight r S *
        ((bernoulliLikelihood q r S - 1) * f S)) ^ 2 =
      (∑ S : Finset ι,
        (Real.sqrt (bernoulliWeight r S) *
          (bernoulliLikelihood q r S - 1)) *
        (Real.sqrt (bernoulliWeight r S) * f S)) ^ 2 := by
          congr 1
          apply Finset.sum_congr rfl
          intro S hS
          calc
            bernoulliWeight r S *
                ((bernoulliLikelihood q r S - 1) * f S) =
              Real.sqrt (bernoulliWeight r S) ^ 2 *
                ((bernoulliLikelihood q r S - 1) * f S) := by
                  rw [Real.sq_sqrt (hw0 S)]
            _ = (Real.sqrt (bernoulliWeight r S) *
                  (bernoulliLikelihood q r S - 1)) *
                (Real.sqrt (bernoulliWeight r S) * f S) := by ring
    _ ≤ (∑ S : Finset ι,
          (Real.sqrt (bernoulliWeight r S) *
            (bernoulliLikelihood q r S - 1)) ^ 2) *
        ∑ S : Finset ι,
          (Real.sqrt (bernoulliWeight r S) * f S) ^ 2 := hcs
    _ = bernoulliChiSquare q r * bernoulliExp r (fun S => f S ^ 2) := by
      unfold bernoulliChiSquare bernoulliExp
      congr 1
      · apply Finset.sum_congr rfl
        intro S hS
        have hsqrt := Real.sq_sqrt (hw0 S)
        rw [mul_pow, hsqrt]
      · apply Finset.sum_congr rfl
        intro S hS
        have hsqrt := Real.sq_sqrt (hw0 S)
        rw [mul_pow, hsqrt]

def routeEEulerBernoulliProb (sigma : ℝ) (p : Nat.Primes) : ℝ :=
  (p : ℝ) ^ (-sigma) / (1 + (p : ℝ) ^ (-sigma))

theorem routeEEulerBernoulliProb_eq_activation (sigma : ℝ) (p : Nat.Primes) :
    routeEEulerBernoulliProb sigma p =
      diagonalActivationOccupancyProbability ((p : ℝ) ^ (-sigma)) := rfl

lemma routeEEulerBernoulliProb_pos (sigma : ℝ) (p : Nat.Primes) :
    0 < routeEEulerBernoulliProb sigma p := by
  unfold routeEEulerBernoulliProb
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
  have ha := Real.rpow_pos_of_pos hp (-sigma)
  positivity

lemma routeEEulerBernoulliProb_lt_one (sigma : ℝ) (p : Nat.Primes) :
    routeEEulerBernoulliProb sigma p < 1 := by
  unfold routeEEulerBernoulliProb
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
  have ha := Real.rpow_pos_of_pos hp (-sigma)
  exact (div_lt_one (by linarith)).mpr (by linarith)

lemma routeEEulerBernoulli_localChi_eq
    (sigma tau : ℝ) (p : Nat.Primes) :
    (routeEEulerBernoulliProb sigma p - routeEEulerBernoulliProb tau p) ^ 2 /
        (routeEEulerBernoulliProb tau p * (1 - routeEEulerBernoulliProb tau p)) =
      (((p : ℝ) ^ (-sigma) - (p : ℝ) ^ (-tau)) ^ 2) /
        ((p : ℝ) ^ (-tau) * (1 + (p : ℝ) ^ (-sigma)) ^ 2) := by
  unfold routeEEulerBernoulliProb
  have hp : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
  have ha := Real.rpow_pos_of_pos hp (-sigma)
  have hb := Real.rpow_pos_of_pos hp (-tau)
  field_simp [ha.ne', hb.ne', (by linarith : 1 + (p : ℝ) ^ (-sigma) ≠ 0),
    (by linarith : 1 + (p : ℝ) ^ (-tau) ≠ 0)]
  ring

lemma eulerLocalChi_raw_le_reflected
    {x delta : ℝ} (hx : 0 < x) (hx1 : 1 ≤ x) (hdelta : 0 ≤ delta) :
    (x ^ (-(1 + delta)) - x ^ (-1 : ℝ)) ^ 2 /
        (x ^ (-1 : ℝ) * (1 + x ^ (-(1 + delta))) ^ 2) ≤
      (x ^ (-(1 / 2 + delta / 2)) -
        x ^ (-(1 / 2 - delta / 2))) ^ 2 := by
  let b : ℝ := x ^ (-1 : ℝ)
  let y : ℝ := x ^ (-delta)
  let z : ℝ := x ^ delta
  have hb : 0 < b := Real.rpow_pos_of_pos hx _
  have hy : 0 < y := Real.rpow_pos_of_pos hx _
  have hz : 0 < z := Real.rpow_pos_of_pos hx _
  have hz1 : 1 ≤ z := Real.one_le_rpow hx1 hdelta
  have ha : x ^ (-(1 + delta)) = b * y := by
    dsimp [b, y]
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have hc :
      x ^ (-(1 / 2 + delta / 2)) =
        x ^ (-(1 / 2 - delta / 2)) * y := by
    dsimp [y]
    rw [← Real.rpow_add hx]
    congr 1
    ring
  have hcSq : (x ^ (-(1 / 2 - delta / 2))) ^ 2 = b * z := by
    dsimp [b, z]
    rw [pow_two, ← Real.rpow_add hx, ← Real.rpow_add hx]
    congr 1
    ring
  have hden : b ≤ b * (1 + b * y) ^ 2 := by
    apply le_mul_of_one_le_right hb.le
    nlinarith [mul_pos hb hy]
  calc
    (x ^ (-(1 + delta)) - x ^ (-1 : ℝ)) ^ 2 /
        (x ^ (-1 : ℝ) * (1 + x ^ (-(1 + delta))) ^ 2) =
      (b * y - b) ^ 2 / (b * (1 + b * y) ^ 2) := by rw [ha]
    _ ≤ (b * y - b) ^ 2 / b :=
      div_le_div_of_nonneg_left (sq_nonneg _) hb hden
    _ = b * (y - 1) ^ 2 := by field_simp [hb.ne']
    _ ≤ b * z * (y - 1) ^ 2 := by
      have hbz : b ≤ b * z := by
        simpa using mul_le_mul_of_nonneg_left hz1 hb.le
      exact mul_le_mul_of_nonneg_right hbz (sq_nonneg _)
    _ = (x ^ (-(1 / 2 + delta / 2)) -
        x ^ (-(1 / 2 - delta / 2))) ^ 2 := by
      rw [hc, ← hcSq]
      ring

lemma routeEEulerBernoulli_localChi_le_primeClock
    (delta : ℝ) (hdelta : 0 ≤ delta) (p : Nat.Primes) :
    (routeEEulerBernoulliProb (1 + delta) p - routeEEulerBernoulliProb 1 p) ^ 2 /
        (routeEEulerBernoulliProb 1 p * (1 - routeEEulerBernoulliProb 1 p)) ≤
      ((p : ℝ) ^ (-(1 / 2 + delta / 2)) -
        (p : ℝ) ^ (-(1 / 2 - delta / 2))) ^ 2 := by
  rw [routeEEulerBernoulli_localChi_eq]
  simpa using eulerLocalChi_raw_le_reflected
    (x := (p : ℝ)) (delta := delta)
    (by exact_mod_cast p.2.pos) (by exact_mod_cast p.2.one_le) hdelta

def routeEEulerTiltChiSquareBelow (delta : ℝ) (N : ℕ) : ℝ :=
  let P := Sieve.primeSubtypeLE N
  bernoulliChiSquare
    (fun p : ↥P => routeEEulerBernoulliProb (1 + delta) p.1)
    (fun p : ↥P => routeEEulerBernoulliProb 1 p.1)

def routeEEulerBernoulliExpBelow (sigma : ℝ) (N : ℕ)
    (f : Finset ↥(Sieve.primeSubtypeLE N) → ℝ) : ℝ :=
  bernoulliExp
    (fun p : ↥(Sieve.primeSubtypeLE N) => routeEEulerBernoulliProb sigma p.1) f

theorem routeEEulerTiltChiSquareBelow_eq_prod (delta : ℝ) (N : ℕ) :
    routeEEulerTiltChiSquareBelow delta N =
      (∏ p : ↥(Sieve.primeSubtypeLE N),
        (1 +
          (routeEEulerBernoulliProb (1 + delta) p.1 -
            routeEEulerBernoulliProb 1 p.1) ^ 2 /
            (routeEEulerBernoulliProb 1 p.1 *
              (1 - routeEEulerBernoulliProb 1 p.1)))) - 1 := by
  unfold routeEEulerTiltChiSquareBelow
  exact bernoulliChiSquare_eq_prod_local _ _
    (fun p => (routeEEulerBernoulliProb_pos 1 p.1).ne')
    (fun p => (sub_pos.mpr (routeEEulerBernoulliProb_lt_one 1 p.1)).ne')

theorem routeEEulerTiltChiSquareBelow_le_primeClock
    (delta : ℝ) (hdelta : 0 ≤ delta) (N : ℕ) :
    routeEEulerTiltChiSquareBelow delta N ≤
      Real.exp (primeClockCutoffEnergy N (delta / 2)) - 1 := by
  rw [routeEEulerTiltChiSquareBelow_eq_prod]
  let P := Sieve.primeSubtypeLE N
  let e : ↥P → ℝ := fun p =>
    (routeEEulerBernoulliProb (1 + delta) p.1 -
      routeEEulerBernoulliProb 1 p.1) ^ 2 /
      (routeEEulerBernoulliProb 1 p.1 *
        (1 - routeEEulerBernoulliProb 1 p.1))
  let clock : ↥P → ℝ := fun p =>
    ((p.1 : ℝ) ^ (-(1 / 2 + delta / 2)) -
      (p.1 : ℝ) ^ (-(1 / 2 - delta / 2))) ^ 2
  have he0 : ∀ p : ↥P, 0 ≤ e p := by
    intro p
    dsimp [e]
    exact div_nonneg (sq_nonneg _)
      (mul_nonneg (routeEEulerBernoulliProb_pos 1 p.1).le
        (sub_pos.mpr (routeEEulerBernoulliProb_lt_one 1 p.1)).le)
  have heClock : ∀ p : ↥P, e p ≤ clock p := by
    intro p
    exact routeEEulerBernoulli_localChi_le_primeClock delta hdelta p.1
  have hprod := GaloisForLFunctions.HTGeometry.prod_one_add_le_exp_sum
    (Finset.univ : Finset ↥P) e (fun p hp => he0 p)
  have hsum : (∑ p : ↥P, e p) ≤ primeClockCutoffEnergy N (delta / 2) := by
    calc
      (∑ p : ↥P, e p) ≤ ∑ p : ↥P, clock p :=
        Finset.sum_le_sum fun p hp => heClock p
      _ = ∑ p ∈ P,
          (((p : ℝ) ^ (-(1 / 2 + delta / 2)) -
            (p : ℝ) ^ (-(1 / 2 - delta / 2))) ^ 2) := by
        rw [Finset.sum_subtype P (fun _ => Iff.rfl)]
      _ = ∑ n ∈ Nat.primesLE N,
          (((n : ℝ) ^ (-(1 / 2 + delta / 2)) -
            (n : ℝ) ^ (-(1 / 2 - delta / 2))) ^ 2) := by
        simpa [P] using Sieve.sum_primeSubtypeLE N
          (fun n : ℕ => (((n : ℝ) ^ (-(1 / 2 + delta / 2)) -
            (n : ℝ) ^ (-(1 / 2 - delta / 2))) ^ 2))
      _ = primeClockCutoffEnergy N (delta / 2) := by
        unfold primeClockCutoffEnergy
        congr 1
  calc
    (∏ p : ↥P, (1 + e p)) - 1 ≤ Real.exp (∑ p : ↥P, e p) - 1 :=
      sub_le_sub_right hprod 1
    _ ≤ Real.exp (primeClockCutoffEnergy N (delta / 2)) - 1 :=
      sub_le_sub_right (Real.exp_le_exp.mpr hsum) 1

theorem routeEEulerTiltChiSquareBelow_nonneg (delta : ℝ) (N : ℕ) :
    0 ≤ routeEEulerTiltChiSquareBelow delta N := by
  rw [routeEEulerTiltChiSquareBelow_eq_prod]
  apply sub_nonneg.mpr
  apply Finset.one_le_prod
  intro p hp
  have hden : 0 < routeEEulerBernoulliProb 1 p.1 *
      (1 - routeEEulerBernoulliProb 1 p.1) :=
    mul_pos (routeEEulerBernoulliProb_pos 1 p.1)
      (sub_pos.mpr (routeEEulerBernoulliProb_lt_one 1 p.1))
  exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _) hden.le)

/-- Exact finite observable transfer from the critical Bernoulli source to the moving Euler tilt. -/
theorem routeEEulerBernoulliExpBelow_sub_sq_le
    (delta : ℝ) (N : ℕ)
    (f : Finset ↥(Sieve.primeSubtypeLE N) → ℝ) :
    (routeEEulerBernoulliExpBelow (1 + delta) N f -
        routeEEulerBernoulliExpBelow 1 N f) ^ 2 ≤
      routeEEulerTiltChiSquareBelow delta N *
        routeEEulerBernoulliExpBelow 1 N (fun S => f S ^ 2) := by
  exact bernoulliExp_sub_sq_le_chiSquare_mul_secondMoment
    (fun p : ↥(Sieve.primeSubtypeLE N) =>
      routeEEulerBernoulliProb (1 + delta) p.1)
    (fun p : ↥(Sieve.primeSubtypeLE N) => routeEEulerBernoulliProb 1 p.1)
    (fun p => routeEEulerBernoulliProb_pos 1 p.1)
    (fun p => routeEEulerBernoulliProb_lt_one 1 p.1) f

open Filter Topology

/-- Any supercritical Euler tilt narrower than the prime-clock scale `1 / log N` is chi-square
contiguous to the critical finite Bernoulli source. -/
theorem tendsto_routeEEulerTiltChiSquareBelow_zero
    (delta : ℕ → ℝ)
    (hdelta : ∀ᶠ N : ℕ in atTop, 0 ≤ delta N)
    (hscaled : Tendsto (fun N : ℕ => delta N * Real.log N) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => routeEEulerTiltChiSquareBelow (delta N) N)
      atTop (𝓝 0) := by
  have hscaledHalf :
      Tendsto (fun N : ℕ => (delta N / 2) * Real.log N) atTop (𝓝 0) := by
    have hfun : (fun N : ℕ => (delta N / 2) * Real.log N) =
        fun N : ℕ => (1 / 2 : ℝ) * (delta N * Real.log N) := by
      funext N
      ring
    rw [hfun]
    simpa using hscaled.const_mul (1 / 2 : ℝ)
  have henergy :=
    tendsto_primeClockCutoffEnergy_zero_of_scaled_tendsto_zero
      (fun N : ℕ => delta N / 2) hscaledHalf
  have hupper :
      Tendsto (fun N : ℕ =>
        Real.exp (primeClockCutoffEnergy N (delta N / 2)) - 1)
        atTop (𝓝 0) := by
    have hexp : Tendsto (fun N : ℕ =>
        Real.exp (primeClockCutoffEnergy N (delta N / 2)))
        atTop (𝓝 (Real.exp 0)) :=
      Real.continuous_exp.continuousAt.tendsto.comp henergy
    simpa using hexp.sub_const 1
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun N =>
      routeEEulerTiltChiSquareBelow_nonneg (delta N) N)
    (show ∀ᶠ N : ℕ in atTop,
      routeEEulerTiltChiSquareBelow (delta N) N ≤
        Real.exp (primeClockCutoffEnergy N (delta N / 2)) - 1 by
      filter_upwards [hdelta] with N hN
      exact routeEEulerTiltChiSquareBelow_le_primeClock (delta N) hN N)
  exact hupper

end

end RHTower
