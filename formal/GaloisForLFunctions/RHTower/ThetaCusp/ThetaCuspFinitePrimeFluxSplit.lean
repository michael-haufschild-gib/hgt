import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFinitePrimeDerivatives
import GaloisForLFunctions.RHTower.ThetaTiltFluxCarrier

open Filter Topology Set
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Exponential tilt of the logarithmic theta-cusp seed. -/
def thetaCuspLogSeedTilt (a x : ℝ) : ℝ :=
  Real.exp (a * x) * thetaCuspLogSeed x

/-- Smooth-monoid resolvent series at an arbitrary real parameter. -/
def finitePrimeThetaCuspResolventSeriesAt
    (N : ℕ) (sigma : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' n : (N + 1).smoothNumbers,
    (n : ℝ) ^ (-sigma) * logTranslate (Real.log n) f x

/-- Equation (21): exponential tilting shifts the resolvent parameter. -/
theorem exp_mul_resolventTerm_eq_resolventTerm_tilt
    (a sigma x : ℝ) {n : ℕ} (hn : 0 < n) (f : ℝ → ℝ) :
    Real.exp (a * x) *
        ((n : ℝ) ^ (-sigma) * logTranslate (Real.log n) f x) =
      (n : ℝ) ^ (-(sigma + a)) *
        logTranslate (Real.log n) (fun y => Real.exp (a * y) * f y) x := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.rpow_def_of_pos hnR, Real.rpow_def_of_pos hnR]
  unfold logTranslate
  change Real.exp (a * x) *
      (Real.exp (Real.log (n : ℝ) * -sigma) * f (x + Real.log n)) =
    Real.exp (Real.log (n : ℝ) * -(sigma + a)) *
      (Real.exp (a * (x + Real.log n)) * f (x + Real.log n))
  have hcoeff :
      Real.exp (a * x) * Real.exp (Real.log (n : ℝ) * -sigma) =
        Real.exp (Real.log (n : ℝ) * -(sigma + a)) *
          Real.exp (a * (x + Real.log n)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    Real.exp (a * x) *
        (Real.exp (Real.log (n : ℝ) * -sigma) * f (x + Real.log n)) =
      (Real.exp (a * x) * Real.exp (Real.log (n : ℝ) * -sigma)) *
        f (x + Real.log n) := by ring
    _ = (Real.exp (Real.log (n : ℝ) * -(sigma + a)) *
          Real.exp (a * (x + Real.log n))) * f (x + Real.log n) := by
      rw [hcoeff]
    _ = Real.exp (Real.log (n : ℝ) * -(sigma + a)) *
        (Real.exp (a * (x + Real.log n)) * f (x + Real.log n)) := by ring

/-- Equation (22): the tilted finite-prime source is the shifted-parameter Euler resolvent of
the tilted seed. -/
theorem exp_mul_finitePrimeThetaCuspSource_eq_resolventSeriesAt
    (N : ℕ) (a x : ℝ) :
    Real.exp (a * x) * finitePrimeThetaCuspSource N x =
      finitePrimeThetaCuspResolventSeriesAt N (1 / 2 + a)
        (thetaCuspLogSeedTilt a) x := by
  rw [finitePrimeThetaCuspSource, finitePrimeThetaCuspResolventSeriesAt,
    ← tsum_mul_left]
  apply tsum_congr
  intro n
  have hn : 0 < (n : ℕ) :=
    Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers n.property)
  calc
    Real.exp (a * x) * thetaCuspSourceTerm x n =
        Real.exp (a * x) *
          ((n : ℝ) ^ (-(1 / 2 : ℝ)) *
            logTranslate (Real.log n) thetaCuspLogSeed x) := by
      rw [invSqrt_mul_logTranslate_thetaCuspLogSeed hn]
      rfl
    _ = (n : ℝ) ^ (-((1 / 2 : ℝ) + a)) *
          logTranslate (Real.log n)
            (fun y => Real.exp (a * y) * thetaCuspLogSeed y) x :=
      exp_mul_resolventTerm_eq_resolventTerm_tilt a (1 / 2) x hn thetaCuspLogSeed
    _ = (n : ℝ) ^ (-((1 / 2 : ℝ) + a)) *
          logTranslate (Real.log n) (thetaCuspLogSeedTilt a) x := by
      rfl

/-- The shifted-parameter resolvent in equation (22) is absolutely summable for every real tilt;
Gaussian source decay supplies convergence without a half-plane premise. -/
theorem summable_finitePrimeThetaCuspResolventSeriesAt_tilt
    (N : ℕ) (a x : ℝ) :
    Summable (fun n : (N + 1).smoothNumbers =>
      (n : ℝ) ^ (-((1 / 2 : ℝ) + a)) *
        logTranslate (Real.log n) (thetaCuspLogSeedTilt a) x) := by
  have hsource := (summable_thetaCuspSourceTerm x).subtype ((N + 1).smoothNumbers)
  refine (hsource.mul_left (Real.exp (a * x))).congr fun n => ?_
  have hn : 0 < (n : ℕ) :=
    Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers n.property)
  calc
    Real.exp (a * x) * thetaCuspSourceTerm x n =
        Real.exp (a * x) *
          ((n : ℝ) ^ (-(1 / 2 : ℝ)) *
            logTranslate (Real.log n) thetaCuspLogSeed x) := by
      rw [invSqrt_mul_logTranslate_thetaCuspLogSeed hn]
      rfl
    _ = (n : ℝ) ^ (-((1 / 2 : ℝ) + a)) *
          logTranslate (Real.log n)
            (fun y => Real.exp (a * y) * thetaCuspLogSeed y) x :=
      exp_mul_resolventTerm_eq_resolventTerm_tilt a (1 / 2) x hn thetaCuspLogSeed
    _ = (n : ℝ) ^ (-((1 / 2 : ℝ) + a)) *
          logTranslate (Real.log n) (thetaCuspLogSeedTilt a) x := by
      rfl

/-- Logarithmically weighted finite-prime source. -/
def finitePrimeThetaCuspLogMoment (N : ℕ) (x : ℝ) : ℝ :=
  ∑' n : (N + 1).smoothNumbers,
    Real.log (n : ℕ) * thetaCuspSourceTerm x n

/-- Resolvent of the archimedean moment of the seed. -/
def finitePrimeThetaCuspArchMoment (N : ℕ) (x : ℝ) : ℝ :=
  finitePrimeThetaCuspResolventSeries N
    (fun y => y * thetaCuspLogSeed y) x

/-- The logarithmic moment series is absolutely summable at every point. -/
theorem summable_finitePrimeThetaCuspLogMoment (N : ℕ) (x : ℝ) :
    Summable (fun n : (N + 1).smoothNumbers =>
      Real.log (n : ℕ) * thetaCuspSourceTerm x n) := by
  let sigma : ℝ := Real.pi * Real.exp x ^ 2
  let A5 : ℝ := Real.exp (x / 2) * 4 * Real.pi ^ 2 * Real.exp x ^ 4
  let A3 : ℝ := Real.exp (x / 2) * 6 * Real.pi * Real.exp x ^ 2
  have hsigma : 0 < sigma := by
    dsimp [sigma]
    positivity
  have h5 := (summable_pow_mul_exp_neg_nat_sq 5 hsigma).mul_left A5
  have h3 := (summable_pow_mul_exp_neg_nat_sq 3 hsigma).mul_left A3
  refine Summable.of_norm_bounded ((h5.add h3).subtype ((N + 1).smoothNumbers)) ?_
  intro n
  have hn : 0 < (n : ℕ) :=
    Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers n.property)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog0 : 0 ≤ Real.log (n : ℕ) := Real.log_nonneg (by exact_mod_cast hn)
  have hlog : Real.log (n : ℕ) ≤ (n : ℝ) := by
    calc
      Real.log (n : ℕ) ≤ (n : ℝ) - 1 := Real.log_le_sub_one_of_pos hnR
      _ ≤ (n : ℝ) := by linarith
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hlog0,
    thetaCuspSourceTerm, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hseed := abs_thetaCuspSeed_le ((n : ℝ) * Real.exp x)
  calc
    Real.log (n : ℕ) *
        (Real.exp (x / 2) * |thetaCuspSeed ((n : ℝ) * Real.exp x)|) ≤
      (n : ℝ) *
        (Real.exp (x / 2) *
          (2 * Real.pi *
            (2 * Real.pi * ((n : ℝ) * Real.exp x) ^ 4 +
              3 * ((n : ℝ) * Real.exp x) ^ 2) *
            Real.exp (-Real.pi * ((n : ℝ) * Real.exp x) ^ 2))) := by
      gcongr
    _ = A5 * ((n : ℝ) ^ 5 * Real.exp (-sigma * (n : ℝ) ^ 2)) +
        A3 * ((n : ℝ) ^ 3 * Real.exp (-sigma * (n : ℝ) ^ 2)) := by
      dsimp [A5, A3, sigma]
      ring_nf

/-- Smooth divisors remain in the same finite-prime monoid. -/
theorem divisor_mem_smoothNumbers
    {N n d : ℕ} (hn : n ∈ N.smoothNumbers) (hd : d ∣ n) :
    d ∈ N.smoothNumbers := by
  rw [Nat.mem_smoothNumbers'] at hn ⊢
  intro p hp hpd
  exact hn p hp (dvd_trans hpd hd)

/-- Multiplication internal to a smooth-number monoid. -/
def smoothNumbersMul (N : ℕ)
    (q : N.smoothNumbers × N.smoothNumbers) : N.smoothNumbers :=
  ⟨(q.1 : ℕ) * (q.2 : ℕ), Nat.mul_mem_smoothNumbers q.1.property q.2.property⟩

/-- A smooth product fibre is exactly the finite divisor packet of its output. -/
def smoothNumbersMulFiberEquivDivisors (N : ℕ) (n : N.smoothNumbers) :
    {q : N.smoothNumbers × N.smoothNumbers // smoothNumbersMul N q = n} ≃
      {d : ℕ // d ∈ (n : ℕ).divisors} where
  toFun q := ⟨(q.1.1 : ℕ), by
    rw [Nat.mem_divisors]
    constructor
    · use (q.1.2 : ℕ)
      exact (congrArg Subtype.val q.2).symm
    · exact Nat.ne_zero_of_mem_smoothNumbers n.property⟩
  invFun d :=
    let hd : (d : ℕ) ∣ (n : ℕ) := (Nat.mem_divisors.mp d.property).1
    ⟨(⟨(d : ℕ), divisor_mem_smoothNumbers n.property hd⟩,
        ⟨(n : ℕ) / (d : ℕ),
          divisor_mem_smoothNumbers n.property (Nat.div_dvd_of_dvd hd)⟩),
      Subtype.ext (Nat.mul_div_cancel' hd)⟩
  left_inv q := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change (n : ℕ) / (q.1.1 : ℕ) = (q.1.2 : ℕ)
      have hd : (q.1.1 : ℕ) ∣ (n : ℕ) := by
        use (q.1.2 : ℕ)
        exact (congrArg Subtype.val q.2).symm
      apply Nat.eq_of_mul_eq_mul_left
        (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers q.1.1.property))
      rw [Nat.mul_div_cancel' hd]
      exact (congrArg Subtype.val q.2).symm
  right_inv d := by
    apply Subtype.ext
    rfl

/-- Critical translation terms multiply their integer labels exactly. -/
theorem invSqrt_mul_thetaCuspSourceTerm_shift
    {q : ℕ} (hq : 0 < q) (m : ℕ) (x : ℝ) :
    (q : ℝ) ^ (-(1 / 2 : ℝ)) *
        thetaCuspSourceTerm (x + Real.log q) m =
      thetaCuspSourceTerm x (q * m) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hpow :
      (q : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (Real.log q / 2) = 1 := by
    rw [Real.rpow_def_of_pos hqR]
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  rw [thetaCuspSourceTerm, thetaCuspSourceTerm, Real.exp_add,
    Real.exp_log hqR]
  have hhalf : Real.exp ((x + Real.log q) / 2) =
      Real.exp (x / 2) * Real.exp (Real.log q / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hhalf]
  calc
    (q : ℝ) ^ (-(1 / 2 : ℝ)) *
        ((Real.exp (x / 2) * Real.exp (Real.log q / 2)) *
          thetaCuspSeed ((m : ℝ) * (Real.exp x * q))) =
      Real.exp (x / 2) *
        (((q : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (Real.log q / 2)) *
          thetaCuspSeed ((m : ℝ) * (Real.exp x * q))) := by ring
    _ = Real.exp (x / 2) *
        thetaCuspSeed (((q * m : ℕ) : ℝ) * Real.exp x) := by
      rw [hpow, one_mul]
      congr 2
      push_cast
      ring

/-- Two-term Gaussian majorant retaining the exact polynomial degrees of a theta-cusp atom. -/
theorem abs_thetaCuspSourceTerm_le_gaussianPolynomial (x : ℝ) (n : ℕ) :
    |thetaCuspSourceTerm x n| ≤
      (Real.exp (x / 2) * 4 * Real.pi ^ 2 * Real.exp x ^ 4) *
          (n : ℝ) ^ 4 *
          Real.exp (-(Real.pi * Real.exp x ^ 2) * (n : ℝ) ^ 2) +
        (Real.exp (x / 2) * 6 * Real.pi * Real.exp x ^ 2) *
          (n : ℝ) ^ 2 *
          Real.exp (-(Real.pi * Real.exp x ^ 2) * (n : ℝ) ^ 2) := by
  rw [thetaCuspSourceTerm, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (x / 2) * |thetaCuspSeed ((n : ℝ) * Real.exp x)| ≤
      Real.exp (x / 2) *
        (2 * Real.pi *
          (2 * Real.pi * ((n : ℝ) * Real.exp x) ^ 4 +
            3 * ((n : ℝ) * Real.exp x) ^ 2) *
          Real.exp (-Real.pi * ((n : ℝ) * Real.exp x) ^ 2)) := by
      gcongr
      exact abs_thetaCuspSeed_le _
    _ = _ := by ring_nf

/-- Gaussian decay at a product index separates into Gaussian decay in each positive factor. -/
theorem thetaCusp_product_gaussian_le
    {sigma : ℝ} (hsigma : 0 < sigma) {q m : ℕ} (hq : 0 < q) (hm : 0 < m) :
    Real.exp (-sigma * ((q * m : ℕ) : ℝ) ^ 2) ≤
      Real.exp (-(sigma / 2) * (q : ℝ) ^ 2) *
        Real.exp (-(sigma / 2) * (m : ℝ) ^ 2) := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  push_cast
  have hq0 : 0 ≤ (q : ℝ) ^ 2 := sq_nonneg _
  have hm0 : 0 ≤ (m : ℝ) ^ 2 := sq_nonneg _
  have hqterm : (q : ℝ) ^ 2 ≤ ((q : ℝ) * (m : ℝ)) ^ 2 := by
    have hmSq : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
    have hnonneg : 0 ≤ (q : ℝ) ^ 2 * ((m : ℝ) ^ 2 - 1) :=
      mul_nonneg hq0 (sub_nonneg.mpr hmSq)
    nlinarith
  have hmterm : (m : ℝ) ^ 2 ≤ ((q : ℝ) * (m : ℝ)) ^ 2 := by
    have hqSq : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
    have hnonneg : 0 ≤ (m : ℝ) ^ 2 * ((q : ℝ) ^ 2 - 1) :=
      mul_nonneg hm0 (sub_nonneg.mpr hqSq)
    nlinarith
  have hqm : (q : ℝ) ^ 2 + (m : ℝ) ^ 2 ≤
      2 * ((q : ℝ) * (m : ℝ)) ^ 2 := by linarith
  nlinarith

/-- Absolutely summable pair expansion of the critical generator acting on the theta-cusp
resolvent. -/
theorem summable_finitePrimeThetaCuspGeneratorPairs (N : ℕ) (x : ℝ) :
    Summable (fun q : (N + 1).smoothNumbers × (N + 1).smoothNumbers =>
      ArithmeticFunction.vonMangoldt (q.1 : ℕ) *
        thetaCuspSourceTerm x ((q.1 : ℕ) * (q.2 : ℕ))) := by
  let sigma : ℝ := Real.pi * Real.exp x ^ 2
  let tau : ℝ := sigma / 2
  let A4 : ℝ := Real.exp (x / 2) * 4 * Real.pi ^ 2 * Real.exp x ^ 4
  let A2 : ℝ := Real.exp (x / 2) * 6 * Real.pi * Real.exp x ^ 2
  have hsigma : 0 < sigma := by dsimp [sigma]; positivity
  have htau : 0 < tau := by dsimp [tau]; positivity
  let f5 : (N + 1).smoothNumbers → ℝ := fun q =>
    (q : ℝ) ^ 5 * Real.exp (-tau * (q : ℝ) ^ 2)
  let f3 : (N + 1).smoothNumbers → ℝ := fun q =>
    (q : ℝ) ^ 3 * Real.exp (-tau * (q : ℝ) ^ 2)
  let g4 : (N + 1).smoothNumbers → ℝ := fun m =>
    (m : ℝ) ^ 4 * Real.exp (-tau * (m : ℝ) ^ 2)
  let g2 : (N + 1).smoothNumbers → ℝ := fun m =>
    (m : ℝ) ^ 2 * Real.exp (-tau * (m : ℝ) ^ 2)
  have hf5 : Summable f5 :=
    (summable_pow_mul_exp_neg_nat_sq 5 htau).subtype ((N + 1).smoothNumbers)
  have hf3 : Summable f3 :=
    (summable_pow_mul_exp_neg_nat_sq 3 htau).subtype ((N + 1).smoothNumbers)
  have hg4 : Summable g4 :=
    (summable_pow_mul_exp_neg_nat_sq 4 htau).subtype ((N + 1).smoothNumbers)
  have hg2 : Summable g2 :=
    (summable_pow_mul_exp_neg_nat_sq 2 htau).subtype ((N + 1).smoothNumbers)
  have h54 : Summable (fun q : (N + 1).smoothNumbers × (N + 1).smoothNumbers =>
      f5 q.1 * g4 q.2) := by
    rw [summable_prod_of_nonneg (fun q => by dsimp [f5, g4]; positivity)]
    constructor
    · intro q
      exact hg4.mul_left (f5 q)
    · simpa only [tsum_mul_left] using hf5.mul_right (∑' m, g4 m)
  have h32 : Summable (fun q : (N + 1).smoothNumbers × (N + 1).smoothNumbers =>
      f3 q.1 * g2 q.2) := by
    rw [summable_prod_of_nonneg (fun q => by dsimp [f3, g2]; positivity)]
    constructor
    · intro q
      exact hg2.mul_left (f3 q)
    · simpa only [tsum_mul_left] using hf3.mul_right (∑' m, g2 m)
  refine Summable.of_norm_bounded ((h54.mul_left A4).add (h32.mul_left A2)) ?_
  intro q
  have hq : 0 < (q.1 : ℕ) :=
    Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers q.1.property)
  have hm : 0 < (q.2 : ℕ) :=
    Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers q.2.property)
  have hqR : (0 : ℝ) ≤ q.1 := by positivity
  have hLambda0 := ArithmeticFunction.vonMangoldt_nonneg (n := (q.1 : ℕ))
  have hLambda : ArithmeticFunction.vonMangoldt (q.1 : ℕ) ≤ (q.1 : ℝ) := by
    calc
      ArithmeticFunction.vonMangoldt (q.1 : ℕ) ≤ Real.log (q.1 : ℕ) :=
        ArithmeticFunction.vonMangoldt_le_log
      _ ≤ (q.1 : ℝ) - 1 := Real.log_le_sub_one_of_pos (by exact_mod_cast hq)
      _ ≤ (q.1 : ℝ) := by linarith
  have hsource := abs_thetaCuspSourceTerm_le_gaussianPolynomial x
    ((q.1 : ℕ) * (q.2 : ℕ))
  have hdecay := thetaCusp_product_gaussian_le hsigma hq hm
  dsimp [sigma] at hdecay
  have hdecay' :
      Real.exp (-(Real.pi * Real.exp x ^ 2) *
          ((q.1 : ℝ) * (q.2 : ℝ)) ^ 2) ≤
        Real.exp (-(Real.pi * Real.exp x ^ 2 / 2) * (q.1 : ℝ) ^ 2) *
          Real.exp (-(Real.pi * Real.exp x ^ 2 / 2) * (q.2 : ℝ) ^ 2) := by
    simpa only [Nat.cast_mul] using hdecay
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hLambda0]
  dsimp [f5, f3, g4, g2, A4, A2, tau, sigma]
  calc
    ArithmeticFunction.vonMangoldt (q.1 : ℕ) *
        |thetaCuspSourceTerm x ((q.1 : ℕ) * (q.2 : ℕ))| ≤
      (q.1 : ℝ) *
        ((Real.exp (x / 2) * 4 * Real.pi ^ 2 * Real.exp x ^ 4) *
            (((q.1 : ℕ) * (q.2 : ℕ) : ℕ) : ℝ) ^ 4 *
            Real.exp (-(Real.pi * Real.exp x ^ 2) *
              (((q.1 : ℕ) * (q.2 : ℕ) : ℕ) : ℝ) ^ 2) +
          (Real.exp (x / 2) * 6 * Real.pi * Real.exp x ^ 2) *
            (((q.1 : ℕ) * (q.2 : ℕ) : ℕ) : ℝ) ^ 2 *
            Real.exp (-(Real.pi * Real.exp x ^ 2) *
              (((q.1 : ℕ) * (q.2 : ℕ) : ℕ) : ℝ) ^ 2)) := by
      gcongr
    _ ≤ (Real.exp (x / 2) * 4 * Real.pi ^ 2 * Real.exp x ^ 4) *
          ((q.1 : ℝ) ^ 5 *
            Real.exp (-(Real.pi * Real.exp x ^ 2 / 2) * (q.1 : ℝ) ^ 2)) *
          ((q.2 : ℝ) ^ 4 *
            Real.exp (-(Real.pi * Real.exp x ^ 2 / 2) * (q.2 : ℝ) ^ 2)) +
        (Real.exp (x / 2) * 6 * Real.pi * Real.exp x ^ 2) *
          ((q.1 : ℝ) ^ 3 *
            Real.exp (-(Real.pi * Real.exp x ^ 2 / 2) * (q.1 : ℝ) ^ 2)) *
          ((q.2 : ℝ) ^ 2 *
            Real.exp (-(Real.pi * Real.exp x ^ 2 / 2) * (q.2 : ℝ) ^ 2)) := by
      push_cast
      let B4 : ℝ := Real.exp (x / 2) * 4 * Real.pi ^ 2 * Real.exp x ^ 4
      let B2 : ℝ := Real.exp (x / 2) * 6 * Real.pi * Real.exp x ^ 2
      have hB4 : 0 ≤ B4 := by dsimp [B4]; positivity
      have hB2 : 0 ≤ B2 := by dsimp [B2]; positivity
      have hterm4 :
          (q.1 : ℝ) *
              (B4 * ((q.1 : ℝ) * (q.2 : ℝ)) ^ 4 *
                Real.exp (-(Real.pi * Real.exp x ^ 2) *
                  ((q.1 : ℝ) * (q.2 : ℝ)) ^ 2)) ≤
            B4 *
              ((q.1 : ℝ) ^ 5 *
                Real.exp (-(Real.pi * Real.exp x ^ 2 / 2) * (q.1 : ℝ) ^ 2)) *
              ((q.2 : ℝ) ^ 4 *
                Real.exp (-(Real.pi * Real.exp x ^ 2 / 2) * (q.2 : ℝ) ^ 2)) := by
        calc
          (q.1 : ℝ) *
              (B4 * ((q.1 : ℝ) * (q.2 : ℝ)) ^ 4 *
                Real.exp (-(Real.pi * Real.exp x ^ 2) *
                  ((q.1 : ℝ) * (q.2 : ℝ)) ^ 2)) ≤
            (q.1 : ℝ) *
              (B4 * ((q.1 : ℝ) * (q.2 : ℝ)) ^ 4 *
                (Real.exp (-(Real.pi * Real.exp x ^ 2 / 2) * (q.1 : ℝ) ^ 2) *
                  Real.exp (-(Real.pi * Real.exp x ^ 2 / 2) * (q.2 : ℝ) ^ 2))) := by
              gcongr
          _ = _ := by ring
      have hterm2 :
          (q.1 : ℝ) *
              (B2 * ((q.1 : ℝ) * (q.2 : ℝ)) ^ 2 *
                Real.exp (-(Real.pi * Real.exp x ^ 2) *
                  ((q.1 : ℝ) * (q.2 : ℝ)) ^ 2)) ≤
            B2 *
              ((q.1 : ℝ) ^ 3 *
                Real.exp (-(Real.pi * Real.exp x ^ 2 / 2) * (q.1 : ℝ) ^ 2)) *
              ((q.2 : ℝ) ^ 2 *
                Real.exp (-(Real.pi * Real.exp x ^ 2 / 2) * (q.2 : ℝ) ^ 2)) := by
        calc
          (q.1 : ℝ) *
              (B2 * ((q.1 : ℝ) * (q.2 : ℝ)) ^ 2 *
                Real.exp (-(Real.pi * Real.exp x ^ 2) *
                  ((q.1 : ℝ) * (q.2 : ℝ)) ^ 2)) ≤
            (q.1 : ℝ) *
              (B2 * ((q.1 : ℝ) * (q.2 : ℝ)) ^ 2 *
                (Real.exp (-(Real.pi * Real.exp x ^ 2 / 2) * (q.1 : ℝ) ^ 2) *
                  Real.exp (-(Real.pi * Real.exp x ^ 2 / 2) * (q.2 : ℝ) ^ 2))) := by
              gcongr
          _ = _ := by ring
      dsimp [B4, B2] at hterm4 hterm2
      linarith
    _ = _ := by ring

/-- Pair term obtained after expanding the generator and the critical resolvent. -/
def finitePrimeThetaCuspGeneratorPairTerm
    (N : ℕ) (x : ℝ)
    (q : (N + 1).smoothNumbers × (N + 1).smoothNumbers) : ℝ :=
  ArithmeticFunction.vonMangoldt (q.1 : ℕ) *
    thetaCuspSourceTerm x ((q.1 : ℕ) * (q.2 : ℕ))

/-- Coefficient expansion of `Q_N(1/2) R_N(1/2) f`: every smooth output index carries the
von Mangoldt mass of all its divisors. -/
def finitePrimeVonMangoldtResolventResponse
    (N : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' n : (N + 1).smoothNumbers,
    (∑ d ∈ (n : ℕ).divisors, ArithmeticFunction.vonMangoldt d) *
      ((n : ℝ) ^ (-(1 / 2 : ℝ)) *
        logTranslate (Real.log n) f x)

/-- Product-fibre regrouping turns the expanded generator-resolvent action into its divisor
convolution response. -/
theorem tsum_finitePrimeThetaCuspGeneratorPairTerm_eq_response (N : ℕ) (x : ℝ) :
    (∑' q : (N + 1).smoothNumbers × (N + 1).smoothNumbers,
        finitePrimeThetaCuspGeneratorPairTerm N x q) =
      finitePrimeVonMangoldtResolventResponse N thetaCuspLogSeed x := by
  have hsum : Summable (finitePrimeThetaCuspGeneratorPairTerm N x) :=
    summable_finitePrimeThetaCuspGeneratorPairs N x
  have hgroup := hsum.hasSum.tsum_fiberwise (smoothNumbersMul (N + 1))
  rw [← hgroup.tsum_eq]
  unfold finitePrimeVonMangoldtResolventResponse
  apply tsum_congr
  intro n
  let e := smoothNumbersMulFiberEquivDivisors (N + 1) n
  calc
    (∑' q : {(q : (N + 1).smoothNumbers × (N + 1).smoothNumbers) |
          smoothNumbersMul (N + 1) q ∈ ({n} : Set (N + 1).smoothNumbers)},
        finitePrimeThetaCuspGeneratorPairTerm N x q) =
      ∑' q : {q : (N + 1).smoothNumbers × (N + 1).smoothNumbers //
          smoothNumbersMul (N + 1) q = n},
        finitePrimeThetaCuspGeneratorPairTerm N x q := by
      apply tsum_congr
      intro q
      rfl
    _ = ∑' d : {d : ℕ // d ∈ (n : ℕ).divisors},
        ArithmeticFunction.vonMangoldt (d : ℕ) * thetaCuspSourceTerm x n := by
      rw [← e.symm.tsum_eq]
      apply tsum_congr
      intro d
      unfold finitePrimeThetaCuspGeneratorPairTerm
      change ArithmeticFunction.vonMangoldt (d : ℕ) *
          thetaCuspSourceTerm x ((d : ℕ) * ((n : ℕ) / (d : ℕ))) = _
      rw [Nat.mul_div_cancel' (Nat.mem_divisors.mp d.property).1]
    _ = (∑ d ∈ (n : ℕ).divisors, ArithmeticFunction.vonMangoldt d) *
        thetaCuspSourceTerm x n := by
      rw [tsum_fintype]
      calc
        (∑ d : {d : ℕ // d ∈ (n : ℕ).divisors},
            ArithmeticFunction.vonMangoldt (d : ℕ) * thetaCuspSourceTerm x n) =
          ∑ d ∈ (n : ℕ).divisors,
            ArithmeticFunction.vonMangoldt d * thetaCuspSourceTerm x n :=
          Finset.sum_coe_sort (n : ℕ).divisors
            (fun d : ℕ => ArithmeticFunction.vonMangoldt d * thetaCuspSourceTerm x n)
        _ = _ := by rw [Finset.sum_mul]
    _ = (∑ d ∈ (n : ℕ).divisors, ArithmeticFunction.vonMangoldt d) *
        ((n : ℝ) ^ (-(1 / 2 : ℝ)) *
          logTranslate (Real.log n) thetaCuspLogSeed x) := by
      have hn : 0 < (n : ℕ) :=
        Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers n.property)
      rw [invSqrt_mul_logTranslate_thetaCuspLogSeed hn]
      rfl
    _ = _ := by ring

/-- Equation (23): finite von Mangoldt shift generator.  Since `vonMangoldt` is supported exactly
on positive prime powers, this natural-number series is literally the stated prime-power sum. -/
def finitePrimeVonMangoldtShiftGenerator
    (N : ℕ) (sigma : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' q : (N + 1).smoothNumbers,
    ArithmeticFunction.vonMangoldt (q : ℕ) *
      ((q : ℝ) ^ (-sigma) * logTranslate (Real.log q) f x)

/-- Non-prime-power coordinates of the finite generator vanish identically. -/
theorem finitePrimeVonMangoldtShiftGenerator_term_eq_zero_of_not_primePow
    (N : ℕ) (sigma x : ℝ) (f : ℝ → ℝ)
    (q : (N + 1).smoothNumbers) (hq : ¬IsPrimePow (q : ℕ)) :
    ArithmeticFunction.vonMangoldt (q : ℕ) *
        ((q : ℝ) ^ (-sigma) * logTranslate (Real.log q) f x) = 0 := by
  rw [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hq, zero_mul]

/-- The generator in equation (23), applied to the critical finite-prime resolvent source, is
exactly the divisor-convolution response. -/
theorem finitePrimeVonMangoldtShiftGenerator_source_eq_response (N : ℕ) (x : ℝ) :
    finitePrimeVonMangoldtShiftGenerator N (1 / 2)
        (finitePrimeThetaCuspSource N) x =
      finitePrimeVonMangoldtResolventResponse N thetaCuspLogSeed x := by
  unfold finitePrimeVonMangoldtShiftGenerator
  rw [show finitePrimeThetaCuspSource N = fun y =>
      ∑' m : (N + 1).smoothNumbers, thetaCuspSourceTerm y m by
    funext y
    rfl]
  calc
    (∑' q : (N + 1).smoothNumbers,
        ArithmeticFunction.vonMangoldt (q : ℕ) *
          ((q : ℝ) ^ (-(1 / 2 : ℝ)) *
            (∑' m : (N + 1).smoothNumbers,
              thetaCuspSourceTerm (x + Real.log q) m))) =
      ∑' q : (N + 1).smoothNumbers,
        ∑' m : (N + 1).smoothNumbers,
          ArithmeticFunction.vonMangoldt (q : ℕ) *
            ((q : ℝ) ^ (-(1 / 2 : ℝ)) *
              thetaCuspSourceTerm (x + Real.log q) m) := by
      apply tsum_congr
      intro q
      rw [← tsum_mul_left, ← tsum_mul_left]
    _ = ∑' q : (N + 1).smoothNumbers,
        ∑' m : (N + 1).smoothNumbers,
          finitePrimeThetaCuspGeneratorPairTerm N x (q, m) := by
      apply tsum_congr
      intro q
      apply tsum_congr
      intro m
      unfold finitePrimeThetaCuspGeneratorPairTerm
      have hq : 0 < (q : ℕ) :=
        Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers q.property)
      rw [invSqrt_mul_thetaCuspSourceTerm_shift hq]
    _ = ∑' q : (N + 1).smoothNumbers × (N + 1).smoothNumbers,
        finitePrimeThetaCuspGeneratorPairTerm N x q := by
      exact (summable_finitePrimeThetaCuspGeneratorPairs N x).tsum_prod.symm
    _ = finitePrimeVonMangoldtResolventResponse N thetaCuspLogSeed x :=
      tsum_finitePrimeThetaCuspGeneratorPairTerm_eq_response N x

/-- Equation (23) at coefficient level: the full finite prime-power response collapses to the
logarithmic weight. -/
theorem finitePrimeVonMangoldtResolventResponse_eq_logMoment (N : ℕ) (x : ℝ) :
    finitePrimeVonMangoldtResolventResponse N thetaCuspLogSeed x =
      finitePrimeThetaCuspLogMoment N x := by
  unfold finitePrimeVonMangoldtResolventResponse finitePrimeThetaCuspLogMoment
  apply tsum_congr
  intro n
  have hn : 0 < (n : ℕ) :=
    Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers n.property)
  rw [ArithmeticFunction.vonMangoldt_sum,
    invSqrt_mul_logTranslate_thetaCuspLogSeed hn]
  rfl

/-- Moving the linear coordinate through one critical resolvent term creates its logarithmic
shift. -/
theorem finitePrimeThetaCuspArchMoment_term
    {n : ℕ} (hn : 0 < n) (x : ℝ) :
    (n : ℝ) ^ (-(1 / 2 : ℝ)) *
        logTranslate (Real.log n) (fun y => y * thetaCuspLogSeed y) x =
      (x + Real.log n) * thetaCuspSourceTerm x n := by
  calc
    (n : ℝ) ^ (-(1 / 2 : ℝ)) *
        logTranslate (Real.log n) (fun y => y * thetaCuspLogSeed y) x =
      (x + Real.log n) *
        ((n : ℝ) ^ (-(1 / 2 : ℝ)) *
          logTranslate (Real.log n) thetaCuspLogSeed x) := by
      unfold logTranslate
      ring
    _ = (x + Real.log n) * thetaCuspSourceTerm x n := by
      rw [invSqrt_mul_logTranslate_thetaCuspLogSeed hn]
      rfl

/-- The archimedean-moment resolvent series is absolutely summable. -/
theorem summable_finitePrimeThetaCuspArchMoment (N : ℕ) (x : ℝ) :
    Summable (fun n : (N + 1).smoothNumbers =>
      (n : ℝ) ^ (-(1 / 2 : ℝ)) *
        logTranslate (Real.log n) (fun y => y * thetaCuspLogSeed y) x) := by
  have hsource := (summable_thetaCuspSourceTerm x).subtype ((N + 1).smoothNumbers)
  have hxsource := hsource.mul_left x
  have hlog := summable_finitePrimeThetaCuspLogMoment N x
  refine (hxsource.add hlog).congr fun n => ?_
  have hn : 0 < (n : ℕ) :=
    Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers n.property)
  rw [finitePrimeThetaCuspArchMoment_term hn]
  change x * thetaCuspSourceTerm x n +
      Real.log (n : ℕ) * thetaCuspSourceTerm x n =
    (x + Real.log (n : ℕ)) * thetaCuspSourceTerm x n
  ring

/-- Equation (24): exact archimedean-minus-prime-power splitting of the first source moment. -/
theorem finitePrimeThetaCusp_moment_split (N : ℕ) (x : ℝ) :
    x * finitePrimeThetaCuspSource N x =
      finitePrimeThetaCuspArchMoment N x -
        finitePrimeVonMangoldtResolventResponse N thetaCuspLogSeed x := by
  rw [finitePrimeVonMangoldtResolventResponse_eq_logMoment]
  unfold finitePrimeThetaCuspArchMoment finitePrimeThetaCuspResolventSeries
  unfold finitePrimeThetaCuspLogMoment finitePrimeThetaCuspSource
  rw [← tsum_mul_left,
    ← Summable.tsum_sub (summable_finitePrimeThetaCuspArchMoment N x)
      (summable_finitePrimeThetaCuspLogMoment N x)]
  · apply tsum_congr
    intro n
    have hn : 0 < (n : ℕ) :=
      Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers n.property)
    rw [finitePrimeThetaCuspArchMoment_term hn]
    ring

/-- Equation (24) in its literal generator form. -/
theorem finitePrimeThetaCusp_moment_split_generator (N : ℕ) (x : ℝ) :
    x * finitePrimeThetaCuspSource N x =
      finitePrimeThetaCuspArchMoment N x -
        finitePrimeVonMangoldtShiftGenerator N (1 / 2)
          (finitePrimeThetaCuspSource N) x := by
  rw [finitePrimeVonMangoldtShiftGenerator_source_eq_response]
  exact finitePrimeThetaCusp_moment_split N x

/-! ## Linear source windows and the exact flux split -/

/-- Equation (25): source window against an arbitrary packet function. -/
def sourcePacketIntegralWindow
    (f : ℝ → ℝ) (Phi : ℝ → ℂ) (s : ℝ) : ℂ :=
  ∫ x : ℝ, (f (x + s) : ℂ) * Phi x

theorem sourcePacketIntegralWindow_eq
    (f : ℝ → ℝ) (Phi : ℝ → ℂ) (s : ℝ) :
    sourcePacketIntegralWindow f Phi s =
      ∫ x : ℝ, (f (x + s) : ℂ) * Phi x := rfl

/-- First-variation source entering the finite-prime critical flux. -/
def finitePrimeThetaCuspMomentSource (N : ℕ) (x : ℝ) : ℝ :=
  x * finitePrimeThetaCuspSource N x

/-- The pointwise source split underlying equation (26). -/
theorem finitePrimeThetaCuspMomentSource_eq_arch_sub_prime (N : ℕ) :
    finitePrimeThetaCuspMomentSource N =
      finitePrimeThetaCuspArchMoment N -
        finitePrimeVonMangoldtResolventResponse N thetaCuspLogSeed := by
  funext x
  exact finitePrimeThetaCusp_moment_split N x

/-- Critical first variation after applying any real-linear source window.  For fixed `Phi,s`,
equation (25) is such a window on every common integrable source domain. -/
def finitePrimeThetaCuspCriticalFlux
    (N : ℕ) (W : (ℝ → ℝ) →ₗ[ℝ] ℂ) : ℝ :=
  2 * (W (finitePrimeThetaCuspMomentSource N) *
    starRingEnd ℂ (W (finitePrimeThetaCuspSource N))).re

/-- Finite-degree archimedean response in equation (26). -/
def finitePrimeThetaCuspArchFlux
    (N : ℕ) (W : (ℝ → ℝ) →ₗ[ℝ] ℂ) : ℝ :=
  2 * (W (finitePrimeThetaCuspArchMoment N) *
    starRingEnd ℂ (W (finitePrimeThetaCuspSource N))).re

/-- Complete finite von Mangoldt prime-power response in equation (26). -/
def finitePrimeThetaCuspPrimePowerFlux
    (N : ℕ) (W : (ℝ → ℝ) →ₗ[ℝ] ℂ) : ℝ :=
  2 * (W (finitePrimeVonMangoldtResolventResponse N thetaCuspLogSeed) *
    starRingEnd ℂ (W (finitePrimeThetaCuspSource N))).re

/-- Literal `Q_N(1/2) k_N` response source. -/
def finitePrimeThetaCuspGeneratorSource (N : ℕ) : ℝ → ℝ :=
  finitePrimeVonMangoldtShiftGenerator N (1 / 2)
    (finitePrimeThetaCuspSource N)

theorem finitePrimeThetaCuspGeneratorSource_eq_response (N : ℕ) :
    finitePrimeThetaCuspGeneratorSource N =
      finitePrimeVonMangoldtResolventResponse N thetaCuspLogSeed := by
  funext x
  exact finitePrimeVonMangoldtShiftGenerator_source_eq_response N x

/-- Prime-power term in equation (26), written literally as the generator applied to `k_N`. -/
def finitePrimeThetaCuspGeneratorFlux
    (N : ℕ) (W : (ℝ → ℝ) →ₗ[ℝ] ℂ) : ℝ :=
  2 * (W (finitePrimeThetaCuspGeneratorSource N) *
    starRingEnd ℂ (W (finitePrimeThetaCuspSource N))).re

theorem finitePrimeThetaCuspGeneratorFlux_eq_primePowerFlux
    (N : ℕ) (W : (ℝ → ℝ) →ₗ[ℝ] ℂ) :
    finitePrimeThetaCuspGeneratorFlux N W =
      finitePrimeThetaCuspPrimePowerFlux N W := by
  rw [finitePrimeThetaCuspGeneratorFlux, finitePrimeThetaCuspPrimePowerFlux,
    finitePrimeThetaCuspGeneratorSource_eq_response]

/-- Equation (26): exact archimedean-minus-prime-power decomposition of finite-prime critical
flux.  It holds for every linear window, hence in particular on every common integral domain of
the source window (25). -/
theorem finitePrimeThetaCuspCriticalFlux_eq_arch_sub_primePower
    (N : ℕ) (W : (ℝ → ℝ) →ₗ[ℝ] ℂ) :
    finitePrimeThetaCuspCriticalFlux N W =
      finitePrimeThetaCuspArchFlux N W -
        finitePrimeThetaCuspPrimePowerFlux N W := by
  rw [finitePrimeThetaCuspCriticalFlux, finitePrimeThetaCuspArchFlux,
    finitePrimeThetaCuspPrimePowerFlux,
    finitePrimeThetaCuspMomentSource_eq_arch_sub_prime, map_sub]
  simp only [sub_mul, Complex.sub_re]
  ring

/-- Equation (26) with its prime term written exactly as `W_(Q_N(1/2) k_N)`. -/
theorem finitePrimeThetaCuspCriticalFlux_eq_arch_sub_generator
    (N : ℕ) (W : (ℝ → ℝ) →ₗ[ℝ] ℂ) :
    finitePrimeThetaCuspCriticalFlux N W =
      finitePrimeThetaCuspArchFlux N W -
        finitePrimeThetaCuspGeneratorFlux N W := by
  rw [finitePrimeThetaCuspGeneratorFlux_eq_primePowerFlux]
  exact finitePrimeThetaCuspCriticalFlux_eq_arch_sub_primePower N W

/-! The same identity on an arbitrary complex Hilbert target.  Taking the target to be the
half-line `L²` space and `W` to be equation (25) is exactly the pairing in equation (26). -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def finitePrimeThetaCuspHilbertCriticalFlux
    (N : ℕ) (W : (ℝ → ℝ) →ₗ[ℝ] H) : ℝ :=
  2 * (inner ℂ (W (finitePrimeThetaCuspMomentSource N))
    (W (finitePrimeThetaCuspSource N))).re

def finitePrimeThetaCuspHilbertArchFlux
    (N : ℕ) (W : (ℝ → ℝ) →ₗ[ℝ] H) : ℝ :=
  2 * (inner ℂ (W (finitePrimeThetaCuspArchMoment N))
    (W (finitePrimeThetaCuspSource N))).re

def finitePrimeThetaCuspHilbertGeneratorFlux
    (N : ℕ) (W : (ℝ → ℝ) →ₗ[ℝ] H) : ℝ :=
  2 * (inner ℂ (W (finitePrimeThetaCuspGeneratorSource N))
    (W (finitePrimeThetaCuspSource N))).re

/-- Equation (26) on every complex Hilbert source-window target, including the half-line `L²`
window of equation (25). -/
theorem finitePrimeThetaCuspHilbertCriticalFlux_eq_arch_sub_generator
    (N : ℕ) (W : (ℝ → ℝ) →ₗ[ℝ] H) :
    finitePrimeThetaCuspHilbertCriticalFlux N W =
      finitePrimeThetaCuspHilbertArchFlux N W -
        finitePrimeThetaCuspHilbertGeneratorFlux N W := by
  rw [finitePrimeThetaCuspHilbertCriticalFlux, finitePrimeThetaCuspHilbertArchFlux,
    finitePrimeThetaCuspHilbertGeneratorFlux,
    finitePrimeThetaCuspMomentSource_eq_arch_sub_prime,
    finitePrimeThetaCuspGeneratorSource_eq_response, map_sub]
  simp only [inner_sub_left, Complex.sub_re]
  ring

end RHTower
