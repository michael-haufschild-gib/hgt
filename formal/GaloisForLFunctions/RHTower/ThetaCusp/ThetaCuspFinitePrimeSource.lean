import GaloisForLFunctions.RHTower.ThetaHalfPlaneBound
import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# Finite-prime theta-cusp source

This module starts the direct formalization of the pointed theta-cusp screen card.  It fixes the
normalized polynomial-Gaussian seed, proves its exact scaling-generator identity, realizes physical
dilation as normalized logarithmic translation, and defines the unscreened finite-prime state as a
sum over smooth integers.  The finite-prime states converge pointwise to the all-integer state.

All statements are unconditional.  The later smooth compact-local convergence, cofinal screen,
entire Fourier transform, and zero-fibre energy estimate are not asserted here.
-/

open Filter Topology

noncomputable section

namespace RHTower

/-- The Gaussian scaling seed in the pointed theta-cusp construction. -/
def thetaCuspGaussian (t : ℝ) : ℝ := Real.exp (-Real.pi * t ^ 2)

/-- The correctly normalized Hedenmalm theta-cusp seed. -/
def thetaCuspSeed (t : ℝ) : ℝ :=
  2 * Real.pi * (2 * Real.pi * t ^ 4 - 3 * t ^ 2) *
    Real.exp (-Real.pi * t ^ 2)

/-- The normalized seed is positive past its unique positive sign threshold. -/
theorem thetaCuspSeed_pos {t : ℝ} (ht : 3 < 2 * Real.pi * t ^ 2) :
    0 < thetaCuspSeed t := by
  have ht2 : 0 < t ^ 2 := by
    nlinarith [Real.pi_pos]
  have hpoly : 0 < 2 * Real.pi * t ^ 4 - 3 * t ^ 2 := by
    calc
      2 * Real.pi * t ^ 4 - 3 * t ^ 2 = t ^ 2 * (2 * Real.pi * t ^ 2 - 3) := by
        ring
      _ > 0 := mul_pos ht2 (sub_pos.mpr ht)
  unfold thetaCuspSeed
  positivity

/-- A polynomial-Gaussian majorant for the normalized seed. -/
theorem abs_thetaCuspSeed_le (t : ℝ) :
    |thetaCuspSeed t| ≤
      2 * Real.pi * (2 * Real.pi * t ^ 4 + 3 * t ^ 2) *
        Real.exp (-Real.pi * t ^ 2) := by
  rw [thetaCuspSeed, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
  have hdiff : |2 * Real.pi * t ^ 4 - 3 * t ^ 2| ≤
      2 * Real.pi * t ^ 4 + 3 * t ^ 2 := by
    calc
      |2 * Real.pi * t ^ 4 - 3 * t ^ 2| ≤
          |2 * Real.pi * t ^ 4| + |3 * t ^ 2| := abs_sub _ _
      _ = 2 * Real.pi * t ^ 4 + 3 * t ^ 2 := by
        rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  gcongr

/-- Multiplicative differentiation `t ∂_t`. -/
def multiplicativeDeriv (f : ℝ → ℝ) (t : ℝ) : ℝ := t * deriv f t

theorem hasDerivAt_thetaCuspGaussian (t : ℝ) :
    HasDerivAt thetaCuspGaussian
      (-2 * Real.pi * t * Real.exp (-Real.pi * t ^ 2)) t := by
  unfold thetaCuspGaussian
  have hinner : HasDerivAt (fun x : ℝ => -Real.pi * x ^ 2) (-2 * Real.pi * t) t := by
    have hraw := (hasDerivAt_const t (-Real.pi)).mul (hasDerivAt_pow 2 t)
    have hfun :
        (fun x : ℝ => -Real.pi * x ^ 2) =
          (fun _ : ℝ => -Real.pi) * fun x : ℝ => x ^ 2 := by
      funext x
      rfl
    rw [hfun]
    exact hraw.congr_deriv (by norm_num; ring)
  have hcomp := (Real.hasDerivAt_exp (-Real.pi * t ^ 2)).comp t hinner
  have hfun :
      (fun x : ℝ => Real.exp (-Real.pi * x ^ 2)) =
        Real.exp ∘ fun x : ℝ => -Real.pi * x ^ 2 := by
    funext x
    rfl
  rw [hfun]
  exact hcomp.congr_deriv (by ring)

theorem multiplicativeDeriv_thetaCuspGaussian (t : ℝ) :
    multiplicativeDeriv thetaCuspGaussian t =
      -2 * Real.pi * t ^ 2 * Real.exp (-Real.pi * t ^ 2) := by
  rw [multiplicativeDeriv, (hasDerivAt_thetaCuspGaussian t).deriv]
  ring

theorem hasDerivAt_multiplicativeDeriv_thetaCuspGaussian (t : ℝ) :
    HasDerivAt (multiplicativeDeriv thetaCuspGaussian)
      ((-4 * Real.pi * t + 4 * Real.pi ^ 2 * t ^ 3) *
        Real.exp (-Real.pi * t ^ 2)) t := by
  have heq : multiplicativeDeriv thetaCuspGaussian = fun x : ℝ =>
      -2 * Real.pi * x ^ 2 * Real.exp (-Real.pi * x ^ 2) := by
    funext x
    exact multiplicativeDeriv_thetaCuspGaussian x
  rw [heq]
  have hpoly : HasDerivAt (fun x : ℝ => -2 * Real.pi * x ^ 2) (-4 * Real.pi * t) t := by
    exact ((hasDerivAt_pow 2 t).const_mul (-2 * Real.pi)).congr_deriv (by norm_num; ring)
  have hprod := hpoly.mul (hasDerivAt_thetaCuspGaussian t)
  have hfun :
      (fun x : ℝ => -2 * Real.pi * x ^ 2 * Real.exp (-Real.pi * x ^ 2)) =
        (fun x : ℝ => -2 * Real.pi * x ^ 2) * thetaCuspGaussian := by
    funext x
    rfl
  rw [hfun]
  apply hprod.congr_deriv
  unfold thetaCuspGaussian
  ring

/-- Exact scaling-Hamiltonian seed identity `h = (D² + D)g₀`. -/
theorem multiplicativeDeriv_sq_add_apply_thetaCuspGaussian (t : ℝ) :
    multiplicativeDeriv (multiplicativeDeriv thetaCuspGaussian) t +
      multiplicativeDeriv thetaCuspGaussian t = thetaCuspSeed t := by
  rw [multiplicativeDeriv,
    (hasDerivAt_multiplicativeDeriv_thetaCuspGaussian t).deriv,
    multiplicativeDeriv_thetaCuspGaussian]
  unfold thetaCuspSeed
  ring

/-- The logarithmic theta-cusp seed before the finite-prime resolvent. -/
def thetaCuspLogSeed (x : ℝ) : ℝ :=
  Real.exp (x / 2) * thetaCuspSeed (Real.exp x)

/-- Additive translation in logarithmic coordinates. -/
def logTranslate (ell : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ := f (x + ell)

/-- A normalized logarithmic translation is exactly physical dilation of the seed. -/
theorem invSqrt_mul_logTranslate_thetaCuspLogSeed
    {n : ℕ} (hn : 0 < n) (x : ℝ) :
    (n : ℝ) ^ (-(1 / 2 : ℝ)) *
        logTranslate (Real.log n) thetaCuspLogSeed x =
      Real.exp (x / 2) * thetaCuspSeed (n * Real.exp x) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [logTranslate, thetaCuspLogSeed, Real.exp_add, Real.exp_log hnR]
  have hpow : (n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (Real.log n / 2) = 1 := by
    rw [Real.rpow_def_of_pos hnR]
    calc
      Real.exp (Real.log n * (-(1 / 2 : ℝ))) * Real.exp (Real.log n / 2) =
          Real.exp (Real.log n * (-(1 / 2 : ℝ)) + Real.log n / 2) :=
        (Real.exp_add _ _).symm
      _ = Real.exp 0 := by
        congr 1
        ring
      _ = 1 := Real.exp_zero
  have hexp : Real.exp ((x + Real.log n) / 2) =
      Real.exp (x / 2) * Real.exp (Real.log n / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  calc
    (n : ℝ) ^ (-(1 / 2 : ℝ)) *
          ((Real.exp (x / 2) * Real.exp (Real.log n / 2)) *
            thetaCuspSeed (Real.exp x * n)) =
        Real.exp (x / 2) *
          (((n : ℝ) ^ (-(1 / 2 : ℝ)) * Real.exp (Real.log n / 2)) *
            thetaCuspSeed (Real.exp x * n)) := by ring
    _ = Real.exp (x / 2) * thetaCuspSeed (n * Real.exp x) := by
      rw [hpow, one_mul]
      congr 2
      ring

/-- Polynomially weighted Gaussians are summable over the natural numbers. -/
theorem summable_pow_mul_exp_neg_nat_sq (A : ℕ) {sigma : ℝ} (hsigma : 0 < sigma) :
    Summable (fun n : ℕ => (n : ℝ) ^ A * Real.exp (-sigma * (n : ℝ) ^ 2)) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_pow_mul_exp_neg A hsigma)
  have hnn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    cases n with
    | zero => norm_num
    | succ n =>
        have h1 : (1 : ℝ) ≤ (n.succ : ℕ) := by exact_mod_cast n.succ_pos
        nlinarith
  have hexp : Real.exp (-sigma * (n : ℝ) ^ 2) ≤
      Real.exp (-((n : ℝ) * sigma)) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  exact mul_le_mul_of_nonneg_left hexp (by positivity)

/-- The `n`-th all-integer theta-cusp source term in logarithmic coordinates. -/
def thetaCuspSourceTerm (x : ℝ) (n : ℕ) : ℝ :=
  Real.exp (x / 2) * thetaCuspSeed (n * Real.exp x)

/-- Absolute convergence of the all-integer theta-cusp state at every logarithmic point. -/
theorem summable_thetaCuspSourceTerm (x : ℝ) : Summable (thetaCuspSourceTerm x) := by
  let sigma : ℝ := Real.pi * Real.exp x ^ 2
  have hsigma : 0 < sigma := mul_pos Real.pi_pos (sq_pos_of_pos (Real.exp_pos x))
  have h4 := (summable_pow_mul_exp_neg_nat_sq 4 hsigma).mul_left
    (Real.exp (x / 2) * 4 * Real.pi ^ 2 * Real.exp x ^ 4)
  have h2 := (summable_pow_mul_exp_neg_nat_sq 2 hsigma).mul_left
    (Real.exp (x / 2) * 6 * Real.pi * Real.exp x ^ 2)
  refine (h4.sub h2).congr (fun n => ?_)
  unfold thetaCuspSourceTerm thetaCuspSeed
  dsimp [sigma]
  ring_nf

/-- A single summable envelope for the source terms on the logarithmic interval `[-R,R]`. -/
def thetaCuspSourceMajorant (R : ℝ) (n : ℕ) : ℝ :=
  Real.exp (R / 2) * 2 * Real.pi *
    (2 * Real.pi * ((n : ℝ) * Real.exp R) ^ 4 +
      3 * ((n : ℝ) * Real.exp R) ^ 2) *
    Real.exp (-(Real.pi * Real.exp (-2 * R)) * n)

theorem summable_thetaCuspSourceMajorant (R : ℝ) :
    Summable (thetaCuspSourceMajorant R) := by
  have hsigma : 0 < Real.pi * Real.exp (-2 * R) :=
    mul_pos Real.pi_pos (Real.exp_pos _)
  have h4 := (summable_pow_mul_exp_neg 4 hsigma).mul_left
    (Real.exp (R / 2) * 4 * Real.pi ^ 2 * Real.exp R ^ 4)
  have h2 := (summable_pow_mul_exp_neg 2 hsigma).mul_left
    (Real.exp (R / 2) * 6 * Real.pi * Real.exp R ^ 2)
  refine (h4.add h2).congr (fun n => ?_)
  unfold thetaCuspSourceMajorant
  ring_nf

theorem thetaCuspSourceMajorant_nonneg (R : ℝ) (n : ℕ) :
    0 ≤ thetaCuspSourceMajorant R n := by
  unfold thetaCuspSourceMajorant
  positivity

/-- The majorant controls every source term uniformly on `[-R,R]`. -/
theorem abs_thetaCuspSourceTerm_le_majorant
    {R x : ℝ} (hx : x ∈ Set.Icc (-R) R) (n : ℕ) :
    |thetaCuspSourceTerm x n| ≤ thetaCuspSourceMajorant R n := by
  have hexpUpper : Real.exp x ≤ Real.exp R := Real.exp_le_exp.mpr hx.2
  have hexpHalf : Real.exp (x / 2) ≤ Real.exp (R / 2) :=
    Real.exp_le_exp.mpr (by linarith [hx.2])
  have hexpLower : Real.exp (-R) ≤ Real.exp x :=
    Real.exp_le_exp.mpr hx.1
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have hn2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    cases n with
    | zero => norm_num
    | succ n =>
        have h1 : (1 : ℝ) ≤ (n.succ : ℕ) := by exact_mod_cast n.succ_pos
        nlinarith
  have hexpSq : Real.exp (-2 * R) ≤ Real.exp x ^ 2 := by
    rw [show Real.exp (-2 * R) = Real.exp (-R) ^ 2 by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring]
    exact (sq_le_sq₀ (Real.exp_pos _).le (Real.exp_pos _).le).2 hexpLower
  have hscale : (n : ℝ) * Real.exp (-2 * R) ≤
      (n : ℝ) ^ 2 * Real.exp x ^ 2 := by
    calc
      (n : ℝ) * Real.exp (-2 * R) ≤ (n : ℝ) ^ 2 * Real.exp (-2 * R) := by
        gcongr
      _ ≤ (n : ℝ) ^ 2 * Real.exp x ^ 2 := by gcongr
  have hdecay : Real.exp (-Real.pi * ((n : ℝ) * Real.exp x) ^ 2) ≤
      Real.exp (-(Real.pi * Real.exp (-2 * R)) * n) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hscale Real.pi_pos.le
    nlinarith
  rw [thetaCuspSourceTerm, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (x / 2) * |thetaCuspSeed (↑n * Real.exp x)| ≤
        Real.exp (x / 2) *
          (2 * Real.pi *
            (2 * Real.pi * (↑n * Real.exp x) ^ 4 +
              3 * (↑n * Real.exp x) ^ 2) *
            Real.exp (-Real.pi * (↑n * Real.exp x) ^ 2)) := by
      gcongr
      exact abs_thetaCuspSeed_le _
    _ ≤ thetaCuspSourceMajorant R n := by
      unfold thetaCuspSourceMajorant
      have hpow2 : ((n : ℝ) * Real.exp x) ^ 2 ≤
          ((n : ℝ) * Real.exp R) ^ 2 := by gcongr
      have hpow4 : ((n : ℝ) * Real.exp x) ^ 4 ≤
          ((n : ℝ) * Real.exp R) ^ 4 := by gcongr
      have hpoly :
          2 * Real.pi * ((n : ℝ) * Real.exp x) ^ 4 +
              3 * ((n : ℝ) * Real.exp x) ^ 2 ≤
            2 * Real.pi * ((n : ℝ) * Real.exp R) ^ 4 +
              3 * ((n : ℝ) * Real.exp R) ^ 2 := by
        gcongr
      calc
        Real.exp (x / 2) *
              (2 * Real.pi *
                (2 * Real.pi * (↑n * Real.exp x) ^ 4 +
                  3 * (↑n * Real.exp x) ^ 2) *
                Real.exp (-Real.pi * (↑n * Real.exp x) ^ 2)) ≤
            Real.exp (R / 2) *
              (2 * Real.pi *
                (2 * Real.pi * (↑n * Real.exp R) ^ 4 +
                  3 * (↑n * Real.exp R) ^ 2) *
                Real.exp (-Real.pi * (↑n * Real.exp x) ^ 2)) := by
          gcongr
        _ ≤ Real.exp (R / 2) * 2 * Real.pi *
              (2 * Real.pi * (↑n * Real.exp R) ^ 4 +
                3 * (↑n * Real.exp R) ^ 2) *
              Real.exp (-(Real.pi * Real.exp (-2 * R)) * ↑n) := by
          let A : ℝ := Real.exp (R / 2) * 2 * Real.pi *
            (2 * Real.pi * (↑n * Real.exp R) ^ 4 +
              3 * (↑n * Real.exp R) ^ 2)
          have hA : 0 ≤ A := by dsimp [A]; positivity
          calc
            Real.exp (R / 2) *
                (2 * Real.pi *
                  (2 * Real.pi * (↑n * Real.exp R) ^ 4 +
                    3 * (↑n * Real.exp R) ^ 2) *
                  Real.exp (-Real.pi * (↑n * Real.exp x) ^ 2)) =
              A * Real.exp (-Real.pi * (↑n * Real.exp x) ^ 2) := by
                dsimp [A]
                ring
            _ ≤ A * Real.exp (-(Real.pi * Real.exp (-2 * R)) * ↑n) :=
              mul_le_mul_of_nonneg_left hdecay hA
            _ = Real.exp (R / 2) * 2 * Real.pi *
                  (2 * Real.pi * (↑n * Real.exp R) ^ 4 +
                    3 * (↑n * Real.exp R) ^ 2) *
                  Real.exp (-(Real.pi * Real.exp (-2 * R)) * ↑n) := by
              dsimp [A]

/-- The all-integer theta-cusp state. -/
def thetaCuspFullSource (x : ℝ) : ℝ :=
  ∑' n : ℕ, thetaCuspSourceTerm x n

/-- The finite-prime theta source: sum over positive integers with all prime factors below `N+1`. -/
def finitePrimeThetaCuspSource (N : ℕ) (x : ℝ) : ℝ :=
  ∑' n : (N + 1).smoothNumbers, thetaCuspSourceTerm x n

/-- The smooth-integer Neumann-series action of the finite-prime resolvent in logarithmic
coordinates.  On the theta-cusp seed the series is absolutely convergent, as proved below. -/
def finitePrimeThetaCuspResolventSeries (N : ℕ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑' n : (N + 1).smoothNumbers,
    (n : ℝ) ^ (-(1 / 2 : ℝ)) * logTranslate (Real.log n) f x

/-- Absolute convergence of the finite-prime resolvent series on the actual seed. -/
theorem summable_finitePrimeThetaCuspResolventSeries_seed (N : ℕ) (x : ℝ) :
    Summable (fun n : (N + 1).smoothNumbers =>
      (n : ℝ) ^ (-(1 / 2 : ℝ)) *
        logTranslate (Real.log n) thetaCuspLogSeed x) := by
  have hsource : Summable (fun n : (N + 1).smoothNumbers => thetaCuspSourceTerm x n) :=
    (summable_thetaCuspSourceTerm x).subtype _
  refine hsource.congr fun n => ?_
  exact (invSqrt_mul_logTranslate_thetaCuspLogSeed
    (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers n.property)) x).symm

/-- Exact source identity `k_N = R_N(1/2)a` in its norm-convergent smooth-integer series form. -/
theorem finitePrimeThetaCuspResolventSeries_seed_eq_source (N : ℕ) (x : ℝ) :
    finitePrimeThetaCuspResolventSeries N thetaCuspLogSeed x =
      finitePrimeThetaCuspSource N x := by
  unfold finitePrimeThetaCuspResolventSeries finitePrimeThetaCuspSource
  apply tsum_congr
  intro n
  exact invSqrt_mul_logTranslate_thetaCuspLogSeed
    (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers n.property)) x

/-- The unscreened finite-prime sources converge pointwise to the all-integer theta-cusp state. -/
theorem finitePrimeThetaCuspSource_tendsto (x : ℝ) :
    Tendsto (fun N : ℕ => finitePrimeThetaCuspSource N x) atTop
      (𝓝 (thetaCuspFullSource x)) := by
  rw [Metric.tendsto_atTop]
  intro epsilon hepsilon
  obtain ⟨N0, hN0⟩ := EulerProduct.norm_tsum_smoothNumbers_sub_tsum_lt
    (summable_thetaCuspSourceTerm x) (by simp [thetaCuspSourceTerm, thetaCuspSeed]) hepsilon
  refine ⟨N0, fun N hN => ?_⟩
  rw [Real.dist_eq, abs_sub_comm]
  simpa [finitePrimeThetaCuspSource, thetaCuspFullSource] using hN0 (N + 1) (by omega)

/-- The finite-prime sources converge uniformly to the all-integer source on every compact
logarithmic interval.  This is the derivative-order-zero case of equation (9) in the card. -/
theorem finitePrimeThetaCuspSource_tendstoUniformlyOn_Icc (R : ℝ) :
    TendstoUniformlyOn finitePrimeThetaCuspSource thetaCuspFullSource atTop
      (Set.Icc (-R) R) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  obtain ⟨N0, hN0⟩ := EulerProduct.norm_tsum_smoothNumbers_sub_tsum_lt
    (summable_thetaCuspSourceMajorant R)
    (by simp [thetaCuspSourceMajorant]) hepsilon
  filter_upwards [eventually_ge_atTop N0] with N hN x hx
  let S : Set ℕ := (N + 1).smoothNumbers
  have hf := summable_thetaCuspSourceTerm x
  have hfSplit := hf.tsum_subtype_add_tsum_subtype_compl S
  have hdiff : thetaCuspFullSource x - finitePrimeThetaCuspSource N x =
      ∑' n : ↥(Sᶜ), thetaCuspSourceTerm x n := by
    rw [thetaCuspFullSource, finitePrimeThetaCuspSource]
    change (∑' n : ℕ, thetaCuspSourceTerm x n) -
        (∑' n : S, thetaCuspSourceTerm x n) = _
    rw [← hfSplit]
    ring
  have hnorm : |∑' n : ↥(Sᶜ), thetaCuspSourceTerm x n| ≤
      ∑' n : ↥(Sᶜ), thetaCuspSourceMajorant R n := by
    calc
      |∑' n : ↥(Sᶜ), thetaCuspSourceTerm x n| ≤
          ∑' n : ↥(Sᶜ), |thetaCuspSourceTerm x n| :=
        norm_tsum_le_tsum_norm (hf.norm.subtype _)
      _ ≤ ∑' n : ↥(Sᶜ), thetaCuspSourceMajorant R n :=
        (hf.norm.subtype _).tsum_le_tsum
          (fun n => abs_thetaCuspSourceTerm_le_majorant hx n)
          ((summable_thetaCuspSourceMajorant R).subtype _)
  have hM := summable_thetaCuspSourceMajorant R
  have hMSplit := hM.tsum_subtype_add_tsum_subtype_compl S
  have hMdiff : (∑' n : ℕ, thetaCuspSourceMajorant R n) -
      (∑' n : S, thetaCuspSourceMajorant R n) =
        ∑' n : ↥(Sᶜ), thetaCuspSourceMajorant R n := by
    rw [← hMSplit]
    ring
  have htailNonneg : 0 ≤ ∑' n : ↥(Sᶜ), thetaCuspSourceMajorant R n :=
    tsum_nonneg fun n => thetaCuspSourceMajorant_nonneg R n
  have htail : (∑' n : ↥(Sᶜ), thetaCuspSourceMajorant R n) < epsilon := by
    have hNtail := hN0 (N + 1) (by omega)
    change |(∑' n : ℕ, thetaCuspSourceMajorant R n) -
      (∑' n : S, thetaCuspSourceMajorant R n)| < epsilon at hNtail
    rw [hMdiff, abs_of_nonneg htailNonneg] at hNtail
    exact hNtail
  rw [Real.dist_eq, hdiff]
  exact hnorm.trans_lt htail

end RHTower
