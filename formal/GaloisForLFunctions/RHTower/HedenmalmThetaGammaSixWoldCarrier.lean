import GaloisForLFunctions.RHTower.HedenmalmThetaMovingHorizonWardCarrier
import GaloisForLFunctions.RHTower.SourceHorizontalGammaSixTameReaderTransgression
import GaloisForLFunctions.RHTower.EulerHellingerDyadicSignSeries
import GaloisForLFunctions.RHTower.DeningerGammaSixShellPrincipalIdeal
import GaloisForLFunctions.RHTower.TraceNorm

/-!
# Theta / Gamma-six / Wold nonlinear horizontal carrier

The finite Gamma-six shell source has a coefficient-faithful reflection base-change defect.
It is the nonlinear character readout of a regulator-null harmonic source boundary; its first
nonblind cutoff is exactly the negative dyadic Hellinger sewing atom.  Multiplying that defect by
the literal moving-horizon theta boundary atom produces one source carrier retaining

* every ordinary-prime label;
* every multiplicity-labelled Xi copy;
* both functional-equation orientations; and
* the full nonlinear horizontal grade before bounded scalarization.

The same flat theta boundary mode, sampled on the doubled Gamma-six shell clock, is the principal
Green eigenvalue `6^-m`, with exact Wold scaling and constant replicated trace mass five.  Its
prime-clock limit has square exactly

`4 * F(a(q))^2 / p`.

Euler divergence therefore puts it in the prime `ell^2` domain exactly at neutral grade.  This
is an unconditional cross-route identification and a strict source-domain wall.  It does not
assert the still-missing theorem that the completed Green comparison lands in this domain.
-/

open Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ### Sharp finite-shell selector -/

/-- The one-shell cutoff is blind: its only clock is `1`, so every normalized moment is one. -/
@[simp] theorem sourceHorizontalGammaSixShellNormalizedMoment_one (r : ℕ) :
    sourceHorizontalGammaSixShellNormalizedMoment 1 r = 1 := by
  rw [sourceHorizontalGammaSixShellNormalizedMoment_eq_uniform]
  simp

/-- Consequently the complete one-shell odd response vanishes at every horizontal grade. -/
@[simp] theorem sourceHorizontalGammaSixShellPrimeClockProfileSeries_one (u : ℝ) :
    sourceHorizontalGammaSixShellPrimeClockProfileSeries 1 u = 0 := by
  unfold sourceHorizontalGammaSixShellPrimeClockProfileSeries
  simp

/-- The first nonblind shell profile is an explicit dyadic hyperbolic difference. -/
theorem sourceHorizontalGammaSixShellPrimeClockProfileSeries_two (u : ℝ) :
    sourceHorizontalGammaSixShellPrimeClockProfileSeries 2 u =
      Real.sinh (u / 2) - Real.sinh u / 2 := by
  rw [sourceHorizontalGammaSixShellPrimeClockProfileSeries_eq_finiteTrace
    (N := 2) (by norm_num)]
  norm_num [sourceHorizontalGammaSixShellClock, Finset.sum_range_succ]
  ring

/-- Exact L/N/P seam: the first nonblind Gamma-six base-change defect is the negative dyadic
Hellinger sewing atom. -/
theorem sourceHorizontalGammaSixShellReflectionBaseChangeDefect_two_eq_dyadic
    (u : ℝ) :
    sourceHorizontalGammaSixShellReflectionBaseChangeDefect 2 u =
      -(Real.sinh u - 2 * Real.sinh (u / 2)) := by
  rw [sourceHorizontalGammaSixShellReflectionBaseChangeDefect_eq,
    sourceHorizontalGammaSixShellPrimeClockProfileSeries_two]
  ring

/-- Factorization of the two-shell defect into an oriented character and a nonnegative dyadic
polarization.  The odd factor retains reflection orientation; the even factor is the Hellinger
square-type loss. -/
theorem sourceHorizontalGammaSixShellReflectionBaseChangeDefect_two_factor
    (u : ℝ) :
    sourceHorizontalGammaSixShellReflectionBaseChangeDefect 2 u =
      -2 * Real.sinh (u / 2) * (Real.cosh (u / 2) - 1) := by
  rw [sourceHorizontalGammaSixShellReflectionBaseChangeDefect_two_eq_dyadic]
  have h := sinh_two_mul_sub_two_sinh (u / 2)
  convert congrArg Neg.neg h using 1 <;> ring

/-- The first interior shell clock makes the quadratic normalized moment strictly smaller than
one.  This is the first finite cutoff at which the shell source can detect horizontal grade. -/
theorem sourceHorizontalGammaSixShellNormalizedMoment_two_lt_one
    {N : ℕ} (hN : 2 ≤ N) :
    sourceHorizontalGammaSixShellNormalizedMoment N 2 < 1 := by
  rw [sourceHorizontalGammaSixShellNormalizedMoment_eq_uniform]
  have h1mem : 1 ∈ Finset.range N := Finset.mem_range.mpr (by omega)
  have hsum :
      (∑ k ∈ Finset.range N,
          sourceHorizontalGammaSixShellClock N k ^ 2) <
        ∑ _k ∈ Finset.range N, (1 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro k hk
      exact pow_le_one₀
        (sourceHorizontalGammaSixShellClock_nonneg hk)
        (sourceHorizontalGammaSixShellClock_le_one N k)
    · refine ⟨1, h1mem, ?_⟩
      have hclock0 : 0 ≤ sourceHorizontalGammaSixShellClock N 1 :=
        sourceHorizontalGammaSixShellClock_nonneg h1mem
      have hclocklt : sourceHorizontalGammaSixShellClock N 1 < 1 := by
        rw [sourceHorizontalGammaSixShellClock]
        have hinvpos : (0 : ℝ) < (1 : ℝ) / N := by positivity
        linarith
      exact pow_lt_one₀ hclock0 hclocklt (by norm_num)
  calc
    (1 / (N : ℝ)) *
          ∑ k ∈ Finset.range N,
            (1 - (k : ℝ) / N) ^ 2
        < (1 / (N : ℝ)) *
            ∑ _k ∈ Finset.range N, (1 : ℝ) :=
      mul_lt_mul_of_pos_left hsum (by positivity)
    _ = 1 := by
      simp
      apply inv_mul_cancel₀
      positivity

private theorem summable_sourceHorizontalGammaSixShellPrimeClockProfileDeficit
    (N : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    Summable (fun k : ℕ =>
      u ^ (2 * k + 1) / (2 * k + 1).factorial *
        (1 - sourceHorizontalGammaSixShellNormalizedMoment N (2 * k))) := by
  refine Summable.of_norm_bounded (Real.hasSum_sinh u).summable ?_
  intro k
  have hm0 : 0 ≤ sourceHorizontalGammaSixShellNormalizedMoment N (2 * k) :=
    sourceHorizontalGammaSixShellNormalizedMoment_nonneg N (2 * k)
  have hm1 : sourceHorizontalGammaSixShellNormalizedMoment N (2 * k) ≤ 1 :=
    sourceHorizontalGammaSixShellNormalizedMoment_le_one N (2 * k)
  have hcoeff0 :
      0 ≤ 1 - sourceHorizontalGammaSixShellNormalizedMoment N (2 * k) := by
    linarith
  have hcoeff1 :
      1 - sourceHorizontalGammaSixShellNormalizedMoment N (2 * k) ≤ 1 := by
    linarith
  have hbase0 : 0 ≤ u ^ (2 * k + 1) / (2 * k + 1).factorial := by
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hbase0 hcoeff0)]
  exact mul_le_of_le_one_right hbase0 hcoeff1

/-- Every finite cutoff containing an interior clock already orients positive horizontal grade.
No cofinal limit is needed for strictness. -/
theorem sourceHorizontalGammaSixShellPrimeClockProfileSeries_neg_of_pos
    {N : ℕ} (hN : 2 ≤ N) {u : ℝ} (hu : 0 < u) :
    sourceHorizontalGammaSixShellPrimeClockProfileSeries N u < 0 := by
  let g : ℕ → ℝ := fun k =>
    u ^ (2 * k + 1) / (2 * k + 1).factorial *
      (1 - sourceHorizontalGammaSixShellNormalizedMoment N (2 * k))
  have hsum : Summable g :=
    summable_sourceHorizontalGammaSixShellPrimeClockProfileDeficit N hu.le
  have hg0 : ∀ k : ℕ, 0 ≤ g k := by
    intro k
    dsimp only [g]
    exact mul_nonneg (by positivity)
      (sub_nonneg.mpr
        (sourceHorizontalGammaSixShellNormalizedMoment_le_one N (2 * k)))
  have hg1 : 0 < g 1 := by
    dsimp only [g]
    exact mul_pos (by positivity)
      (sub_pos.mpr (sourceHorizontalGammaSixShellNormalizedMoment_two_lt_one hN))
  have hpositive : 0 < ∑' k : ℕ, g k := hsum.tsum_pos hg0 1 hg1
  have heq : sourceHorizontalGammaSixShellPrimeClockProfileSeries N u =
      -(∑' k : ℕ, g k) := by
    unfold sourceHorizontalGammaSixShellPrimeClockProfileSeries
    rw [← tsum_neg]
    apply tsum_congr
    intro k
    dsimp only [g]
    ring
  rw [heq]
  exact neg_lt_zero.mpr hpositive

theorem sourceHorizontalGammaSixShellPrimeClockProfileSeries_pos_of_neg
    {N : ℕ} (hN : 2 ≤ N) {u : ℝ} (hu : u < 0) :
    0 < sourceHorizontalGammaSixShellPrimeClockProfileSeries N u := by
  have h := sourceHorizontalGammaSixShellPrimeClockProfileSeries_neg_of_pos
    hN (u := -u) (neg_pos.mpr hu)
  rw [sourceHorizontalGammaSixShellPrimeClockProfileSeries_neg] at h
  linarith

/-- Sharp finite-cutoff classification: `N = 1` is blind, whereas every `N ≥ 2` has exactly
one profile zero. -/
theorem sourceHorizontalGammaSixShellPrimeClockProfileSeries_eq_zero_iff
    {N : ℕ} (hN : 2 ≤ N) (u : ℝ) :
    sourceHorizontalGammaSixShellPrimeClockProfileSeries N u = 0 ↔ u = 0 := by
  constructor
  · intro hzero
    by_contra hu
    rcases lt_or_gt_of_ne hu with huNeg | huPos
    · linarith [sourceHorizontalGammaSixShellPrimeClockProfileSeries_pos_of_neg hN huNeg]
    · linarith [sourceHorizontalGammaSixShellPrimeClockProfileSeries_neg_of_pos hN huPos]
  · intro hu
    subst u
    simp [sourceHorizontalGammaSixShellPrimeClockProfileSeries]

theorem sourceHorizontalGammaSixShellReflectionBaseChangeDefect_eq_zero_iff
    {N : ℕ} (hN : 2 ≤ N) (u : ℝ) :
    sourceHorizontalGammaSixShellReflectionBaseChangeDefect N u = 0 ↔ u = 0 := by
  rw [sourceHorizontalGammaSixShellReflectionBaseChangeDefect_eq, mul_eq_zero]
  norm_num
  exact sourceHorizontalGammaSixShellPrimeClockProfileSeries_eq_zero_iff hN u

end

end RHTower

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-! ### One flat theta mode on the Gamma-six and prime clocks -/

/-- At doubled Gamma-six logarithmic aperture, the normalized physical theta flat boundary mode
is exactly the principal Green eigenvalue.  Thus Route L's weak-trace diagonal and Route P's
moving-horizon boundary are the same source mode sampled on different clocks. -/
theorem thetaMovingHorizonBoundaryMode_gammaSixShellGreenEigenvalue (m : ℕ) :
    thetaMovingHorizonBoundaryMode (2 * (m : ℝ) * Real.log 6) / thetaSource.k 0 =
      sourceHorizontalGammaSixShellGreenEigenvalue m := by
  rw [thetaMovingHorizonBoundaryMode,
    sourceHorizontalGammaSixShellGreenEigenvalue]
  have hk0 : thetaSource.k 0 ≠ 0 := (thetaSource.pos_k 0).ne'
  field_simp [hk0]
  rw [show -((m : ℝ) * Real.log 6) =
      (m : ℕ) * (-Real.log 6) by ring,
    Real.exp_nat_mul, Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

/-- Wold compression of the Gamma-six principal class is literal translation of the same theta
flat mode by one doubled shell aperture. -/
theorem thetaMovingHorizonBoundaryMode_gammaSixShell_succ (m : ℕ) :
    thetaMovingHorizonBoundaryMode (2 * ((m + 1 : ℕ) : ℝ) * Real.log 6) /
        thetaSource.k 0 =
      (1 / 6 : ℝ) *
        (thetaMovingHorizonBoundaryMode (2 * (m : ℝ) * Real.log 6) /
          thetaSource.k 0) := by
  rw [thetaMovingHorizonBoundaryMode_gammaSixShellGreenEigenvalue,
    thetaMovingHorizonBoundaryMode_gammaSixShellGreenEigenvalue,
    sourceHorizontalGammaSixShellGreenEigenvalue,
    sourceHorizontalGammaSixShellGreenEigenvalue, pow_succ]
  ring

/-- Replicating the physical theta flat mode over the literal Gamma-six integer shell gives exact
trace mass five at every depth.  This realizes the weak-trace principal obstruction physically. -/
theorem thetaMovingHorizonBoundaryMode_gammaSixShellTraceMass (m : ℕ) :
    sourceHorizontalGammaSixShellMultiplicity m *
        (thetaMovingHorizonBoundaryMode (2 * (m : ℝ) * Real.log 6) /
          thetaSource.k 0) = 5 := by
  rw [thetaMovingHorizonBoundaryMode_gammaSixShellGreenEigenvalue]
  exact sourceHorizontalGammaSixShellGreenTraceMass_eq_five m

/-- Finite Gamma-six reflected shell defect carried by the literal theta half-density atom. -/
def thetaGammaSixShellHorizontalCarrier
    (N : ℕ) (p : Nat.Primes) (q : XiZeroCopy) : ℝ :=
  thetaMovingHorizonUniversalAmplitude p *
    sourceHorizontalGammaSixShellReflectionBaseChangeDefect N
      (primeDepthBVWoldXiCenteredRate q.1)

/-- The finite carrier is not a fitted product: it is the literal nonlinear character readout of
the regulator-null Gamma-six harmonic boundary class, carried by the physical theta prime atom. -/
theorem thetaGammaSixShellHorizontalCarrier_eq_sourceReadout
    {N : ℕ} (hN : 0 < N) (p : Nat.Primes) (q : XiZeroCopy) :
    thetaGammaSixShellHorizontalCarrier N p q =
      thetaMovingHorizonUniversalAmplitude p *
        sourceHorizontalGammaSixExponentCharacterReadout
          (primeDepthBVWoldXiCenteredRate q.1 / N)
          (sourceHorizontalGammaSixHarmonicBoundaryClass N) := by
  rw [thetaGammaSixShellHorizontalCarrier,
    sourceHorizontalGammaSixShellReflectionBaseChangeDefect_eq,
    ← sourceHorizontalGammaSixExponentCharacterReadout_harmonicBoundaryClass_eq_profile hN]

/-- Its source class is unconditionally Kummer-regulator null before Xi specialization. -/
theorem thetaGammaSixShellHorizontalCarrier_sourceClass_regulatorNull
    {N : ℕ} (hN : 0 < N) :
    sourceHorizontalGammaSixKummerExponentMoment
        (sourceHorizontalGammaSixHarmonicBoundaryClass N) = 0 :=
  sourceHorizontalGammaSixKummerExponentMoment_harmonicBoundaryClass hN

/-- At the first nonblind cutoff, the source-derived physical carrier is exactly the negative
dyadic Hellinger sewing atom times the theta prime half-density. -/
theorem thetaGammaSixShellHorizontalCarrier_two_eq_dyadic
    (p : Nat.Primes) (q : XiZeroCopy) :
    thetaGammaSixShellHorizontalCarrier 2 p q =
      -thetaMovingHorizonUniversalAmplitude p *
        (Real.sinh (primeDepthBVWoldXiCenteredRate q.1) -
          2 * Real.sinh (primeDepthBVWoldXiCenteredRate q.1 / 2)) := by
  rw [thetaGammaSixShellHorizontalCarrier,
    sourceHorizontalGammaSixShellReflectionBaseChangeDefect_two_eq_dyadic]
  ring

/-! ### Operator-ideal form of the same carrier -/

/-- The actual Gamma-six weak-trace principal operator with the same finite nonlinear source
coefficient.  The two-clock theorem above identifies its diagonal with the physical theta flat
boundary mode on every complete shell. -/
def thetaGammaSixShellHorizontalPrincipalOperator
    (N : ℕ) (q : XiZeroCopy) : EllTwo →L[ℂ] EllTwo :=
  ((sourceHorizontalGammaSixShellReflectionBaseChangeDefect N
    (primeDepthBVWoldXiCenteredRate q.1) : ℝ) : ℂ) •
      deningerGammaSixShellPrincipalOperator

/-- A nonzero scalar cannot make the Gamma-six principal weak-trace class trace class. -/
theorem memSchattenClass_one_smul_deningerGammaSixShellPrincipalOperator_iff
    (c : ℂ) :
    MemSchattenClass 1 (c • deningerGammaSixShellPrincipalOperator) ↔ c = 0 := by
  constructor
  · intro hmem
    by_contra hc
    apply deningerGammaSixShellPrincipalOperator_not_traceClass
    have hscaled := memSchattenClass_one_smul hmem c⁻¹
    convert hscaled using 1
    rw [smul_smul]
    simp [hc]
  · rintro rfl
    simp [MemSchattenClass, approxNumber_zero_op]

/-- The finite horizontal principal operator always remains in weak Schatten one. -/
theorem thetaGammaSixShellHorizontalPrincipalOperator_weak
    (N : ℕ) (q : XiZeroCopy) :
    MemWeakSchattenClass 1
      (thetaGammaSixShellHorizontalPrincipalOperator N q) := by
  let c : ℂ :=
    (sourceHorizontalGammaSixShellReflectionBaseChangeDefect N
      (primeDepthBVWoldXiCenteredRate q.1) : ℝ)
  obtain ⟨C, hC, hbound⟩ := deningerGammaSixShellPrincipalOperator_weak
  refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg c) hC, fun n => ?_⟩
  rw [thetaGammaSixShellHorizontalPrincipalOperator,
    approxNumber_smul, Real.rpow_one]
  change ‖c‖ * approxNumber deningerGammaSixShellPrincipalOperator n ≤
    ‖c‖ * C / ((n : ℝ) + 1)
  have hb : approxNumber deningerGammaSixShellPrincipalOperator n ≤
      C / ((n : ℝ) + 1) := by simpa using hbound n
  calc
    ‖c‖ * approxNumber deningerGammaSixShellPrincipalOperator n
        ≤ ‖c‖ * (C / ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg c)
    _ = ‖c‖ * C / ((n : ℝ) + 1) := by ring

/-- **Strict ideal-drop wall.**  At every nonblind finite cutoff, the actual source-weighted
Gamma-six principal operator drops from weak trace class to ordinary trace class exactly at
neutral horizontal grade. -/
theorem thetaGammaSixShellHorizontalPrincipalOperator_traceClass_iff
    {N : ℕ} (hN : 2 ≤ N) (q : XiZeroCopy) :
    MemSchattenClass 1 (thetaGammaSixShellHorizontalPrincipalOperator N q) ↔
      primeDepthBVWoldXiCenteredRate q.1 = 0 := by
  rw [thetaGammaSixShellHorizontalPrincipalOperator,
    memSchattenClass_one_smul_deningerGammaSixShellPrincipalOperator_iff,
    Complex.ofReal_eq_zero,
    sourceHorizontalGammaSixShellReflectionBaseChangeDefect_eq_zero_iff hN]

/-- Cofinal nonlinear carrier obtained from the complete Gamma-six shell source. -/
def thetaGammaSixWoldHorizontalCarrier
    (p : Nat.Primes) (q : XiZeroCopy) : ℝ :=
  thetaMovingHorizonUniversalAmplitude p *
    (2 * sourceHorizontalWoldPrimeClockUniversalProfile
      (primeDepthBVWoldXiCenteredRate q.1))

/-- The finite coefficient-faithful shell carriers converge labelwise to the nonlinear
theta/Wold carrier. -/
theorem tendsto_thetaGammaSixShellHorizontalCarrier
    (p : Nat.Primes) (q : XiZeroCopy) :
    Tendsto (fun N : ℕ => thetaGammaSixShellHorizontalCarrier N p q) atTop
      (nhds (thetaGammaSixWoldHorizontalCarrier p q)) := by
  have hconst : Tendsto
      (fun _N : ℕ => thetaMovingHorizonUniversalAmplitude p) atTop
      (nhds (thetaMovingHorizonUniversalAmplitude p)) := tendsto_const_nhds
  have h := hconst.mul
    (tendsto_sourceHorizontalGammaSixShellReflectionBaseChangeDefect
      (primeDepthBVWoldXiCenteredRate q.1))
  simpa [thetaGammaSixShellHorizontalCarrier,
    thetaGammaSixWoldHorizontalCarrier] using h

/-- Functional-equation reflection reverses every finite shell carrier without changing its
prime label or cutoff. -/
theorem thetaGammaSixShellHorizontalCarrier_copyReflect
    (N : ℕ) (p : Nat.Primes) (q : XiZeroCopy) :
    thetaGammaSixShellHorizontalCarrier N p (xiZeroCopyReflectEquiv q) =
      -thetaGammaSixShellHorizontalCarrier N p q := by
  rw [thetaGammaSixShellHorizontalCarrier,
    thetaGammaSixShellHorizontalCarrier,
    primeDepthBVWoldXiCenteredRate_copyReflect]
  unfold sourceHorizontalGammaSixShellReflectionBaseChangeDefect
  rw [sourceHorizontalGammaSixShellPrimeClockProfileSeries_neg]
  ring

/-- The one-shell theta carrier is identically zero: this cutoff has no interior clock and cannot
detect any off-line class. -/
@[simp] theorem thetaGammaSixShellHorizontalCarrier_one
    (p : Nat.Primes) (q : XiZeroCopy) :
    thetaGammaSixShellHorizontalCarrier 1 p q = 0 := by
  rw [thetaGammaSixShellHorizontalCarrier,
    sourceHorizontalGammaSixShellReflectionBaseChangeDefect_eq]
  simp

/-- Exact reciprocal-prime square law already holds at every finite shell cutoff. -/
theorem thetaGammaSixShellHorizontalCarrier_sq
    (N : ℕ) (p : Nat.Primes) (q : XiZeroCopy) :
    thetaGammaSixShellHorizontalCarrier N p q ^ 2 =
      sourceHorizontalGammaSixShellReflectionBaseChangeDefect N
          (primeDepthBVWoldXiCenteredRate q.1) ^ 2 / (p : ℝ) := by
  rw [thetaGammaSixShellHorizontalCarrier, mul_pow,
    thetaMovingHorizonUniversalAmplitude_sq]
  ring

/-- At every nonblind finite cutoff, one retained prime label detects neutral grade exactly. -/
theorem thetaGammaSixShellHorizontalCarrier_eq_zero_iff
    {N : ℕ} (hN : 2 ≤ N) (p : Nat.Primes) (q : XiZeroCopy) :
    thetaGammaSixShellHorizontalCarrier N p q = 0 ↔
      primeDepthBVWoldXiCenteredRate q.1 = 0 := by
  have hamp : thetaMovingHorizonUniversalAmplitude p ≠ 0 := by
    rw [thetaMovingHorizonUniversalAmplitude_eq_routeN,
      routeNGammaSewnUniversalCriticalChannelAmplitude]
    exact (Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _).ne'
  rw [thetaGammaSixShellHorizontalCarrier, mul_eq_zero]
  simp only [hamp, false_or]
  exact sourceHorizontalGammaSixShellReflectionBaseChangeDefect_eq_zero_iff hN _

/-- **Finite Frankenstein domain wall.**  Every fixed cutoff `N ≥ 2` already turns the
coefficient-faithful shell response into a prime `ell^2` selector.  Cofinal passage is unnecessary
for the equivalence. -/
theorem summable_sq_thetaGammaSixShellHorizontalCarrier_iff
    {N : ℕ} (hN : 2 ≤ N) (q : XiZeroCopy) :
    Summable (fun p : Nat.Primes =>
      thetaGammaSixShellHorizontalCarrier N p q ^ 2) ↔
      primeDepthBVWoldXiCenteredRate q.1 = 0 := by
  let D : ℝ := sourceHorizontalGammaSixShellReflectionBaseChangeDefect N
    (primeDepthBVWoldXiCenteredRate q.1)
  constructor
  · intro hsum
    by_contra hrate
    have hD : D ≠ 0 := by
      dsimp only [D]
      intro hzero
      exact hrate
        ((sourceHorizontalGammaSixShellReflectionBaseChangeDefect_eq_zero_iff
          hN _).1 hzero)
    let c : ℝ := D ^ 2
    have hc : c ≠ 0 := by
      dsimp only [c]
      exact pow_ne_zero 2 hD
    have hscaled := hsum.mul_left c⁻¹
    apply burnolNotSummable_prime_one_div
    refine hscaled.congr (fun p => ?_)
    rw [thetaGammaSixShellHorizontalCarrier_sq]
    change c⁻¹ * (D ^ 2 / (p : ℝ)) = 1 / (p : ℝ)
    dsimp only [c] at hc ⊢
    field_simp [hc]
  · intro hrate
    have hzero : ∀ p : Nat.Primes,
        thetaGammaSixShellHorizontalCarrier N p q = 0 := fun p =>
      (thetaGammaSixShellHorizontalCarrier_eq_zero_iff hN p q).2 hrate
    exact (summable_zero : Summable (fun _p : Nat.Primes => (0 : ℝ))).congr
      (fun p => by simp [hzero p])

/-- Every nonblind finite cutoff yields RH from global prime-domain admission.  The theorem is an
unconditional equivalence, not an assertion of admission. -/
theorem all_summable_sq_thetaGammaSixShellHorizontalCarrier_iff_riemannHypothesis
    {N : ℕ} (hN : 2 ≤ N) :
    (∀ q : XiZeroCopy, Summable (fun p : Nat.Primes =>
      thetaGammaSixShellHorizontalCarrier N p q ^ 2)) ↔
      RiemannHypothesis := by
  rw [← thetaGreenBoundaryNeutral_iff_riemannHypothesis]
  refine forall_congr' fun q => ?_
  rw [summable_sq_thetaGammaSixShellHorizontalCarrier_iff hN,
    thetaXiRankTwoBoundaryFlux_eq_neg_massEnergy_mul_centeredRate]
  have hcoefficient :
      -(thetaSource.mass * thetaXiRootEnergy q) ≠ 0 :=
    neg_ne_zero.mpr
      (mul_pos thetaSource.mass_pos (thetaXiRootEnergy_pos q)).ne'
  constructor
  · intro hrate
    rw [hrate, mul_zero]
  · intro hflux
    exact (mul_eq_zero.mp hflux).resolve_left hcoefficient

/-- Global ordinary trace-class admission of the literal finite Gamma-six/theta principal
operator is exactly RH.  A successful strict source lift must prove this admission rather than
postulate it as a target domain. -/
theorem all_thetaGammaSixShellHorizontalPrincipalOperator_traceClass_iff_riemannHypothesis
    {N : ℕ} (hN : 2 ≤ N) :
    (∀ q : XiZeroCopy,
      MemSchattenClass 1 (thetaGammaSixShellHorizontalPrincipalOperator N q)) ↔
      RiemannHypothesis := by
  constructor
  · intro hall
    apply (all_summable_sq_thetaGammaSixShellHorizontalCarrier_iff_riemannHypothesis hN).1
    intro q
    exact (summable_sq_thetaGammaSixShellHorizontalCarrier_iff hN q).2
      ((thetaGammaSixShellHorizontalPrincipalOperator_traceClass_iff hN q).1 (hall q))
  · intro hRH q
    apply (thetaGammaSixShellHorizontalPrincipalOperator_traceClass_iff hN q).2
    exact (summable_sq_thetaGammaSixShellHorizontalCarrier_iff hN q).1
      ((all_summable_sq_thetaGammaSixShellHorizontalCarrier_iff_riemannHypothesis hN).2
        hRH q)

/-- Reflection reverses the limiting carrier as well. -/
theorem thetaGammaSixWoldHorizontalCarrier_copyReflect
    (p : Nat.Primes) (q : XiZeroCopy) :
    thetaGammaSixWoldHorizontalCarrier p (xiZeroCopyReflectEquiv q) =
      -thetaGammaSixWoldHorizontalCarrier p q := by
  rw [thetaGammaSixWoldHorizontalCarrier,
    thetaGammaSixWoldHorizontalCarrier,
    primeDepthBVWoldXiCenteredRate_copyReflect,
    sourceHorizontalWoldPrimeClockUniversalProfile_neg]
  ring

/-- Exact nonlinear reciprocal-prime square law.  The Gamma-six anomaly supplies the coefficient
and the physical theta endpoint supplies the unavoidable `1 / p` mass. -/
theorem thetaGammaSixWoldHorizontalCarrier_sq
    (p : Nat.Primes) (q : XiZeroCopy) :
    thetaGammaSixWoldHorizontalCarrier p q ^ 2 =
      4 * sourceHorizontalWoldPrimeClockUniversalProfile
          (primeDepthBVWoldXiCenteredRate q.1) ^ 2 / (p : ℝ) := by
  rw [thetaGammaSixWoldHorizontalCarrier, mul_pow,
    thetaMovingHorizonUniversalAmplitude_sq]
  ring

/-- At every retained prime label the nonlinear carrier vanishes exactly at neutral horizontal
grade. -/
theorem thetaGammaSixWoldHorizontalCarrier_eq_zero_iff
    (p : Nat.Primes) (q : XiZeroCopy) :
    thetaGammaSixWoldHorizontalCarrier p q = 0 ↔
      primeDepthBVWoldXiCenteredRate q.1 = 0 := by
  have hamp : thetaMovingHorizonUniversalAmplitude p ≠ 0 := by
    rw [thetaMovingHorizonUniversalAmplitude_eq_routeN,
      routeNGammaSewnUniversalCriticalChannelAmplitude]
    exact (Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _).ne'
  rw [thetaGammaSixWoldHorizontalCarrier, mul_eq_zero]
  simp only [hamp, false_or]
  exact sourceHorizontalGammaSixShellReflectionBaseChangeLimit_eq_zero_iff _

/-- **Strict Frankenstein domain wall.**  The complete nonlinear L/T/P carrier is square
summable over its literal prime labels exactly at neutral horizontal grade. -/
theorem summable_sq_thetaGammaSixWoldHorizontalCarrier_iff
    (q : XiZeroCopy) :
    Summable (fun p : Nat.Primes =>
      thetaGammaSixWoldHorizontalCarrier p q ^ 2) ↔
      primeDepthBVWoldXiCenteredRate q.1 = 0 := by
  let F : ℝ := sourceHorizontalWoldPrimeClockUniversalProfile
    (primeDepthBVWoldXiCenteredRate q.1)
  constructor
  · intro hsum
    by_contra hrate
    have hF : F ≠ 0 := by
      dsimp only [F]
      intro hzero
      exact hrate
        ((sourceHorizontalWoldPrimeClockUniversalProfile_eq_zero_iff _).1 hzero)
    let c : ℝ := 4 * F ^ 2
    have hc : c ≠ 0 := by
      dsimp only [c]
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hF)
    have hscaled := hsum.mul_left c⁻¹
    apply burnolNotSummable_prime_one_div
    refine hscaled.congr (fun p => ?_)
    rw [thetaGammaSixWoldHorizontalCarrier_sq]
    change c⁻¹ * (4 * F ^ 2 / (p : ℝ)) = 1 / (p : ℝ)
    dsimp only [c] at hc ⊢
    field_simp [hc]
  · intro hrate
    have hF : sourceHorizontalWoldPrimeClockUniversalProfile
        (primeDepthBVWoldXiCenteredRate q.1) = 0 :=
      (sourceHorizontalWoldPrimeClockUniversalProfile_eq_zero_iff _).2 hrate
    exact (summable_zero : Summable (fun _p : Nat.Primes => (0 : ℝ))).congr
      (fun p => by simp [thetaGammaSixWoldHorizontalCarrier, hF])

/-- The strict domain wall is the same literal theta Green boundary, now reached through the
Gamma-six shell anomaly rather than through quadratic Ward scalarization. -/
theorem summable_sq_thetaGammaSixWoldHorizontalCarrier_iff_boundaryFlux_zero
    (q : XiZeroCopy) :
    Summable (fun p : Nat.Primes =>
      thetaGammaSixWoldHorizontalCarrier p q ^ 2) ↔
      thetaXiRankTwoBoundaryFlux q = 0 := by
  rw [summable_sq_thetaGammaSixWoldHorizontalCarrier_iff,
    thetaXiRankTwoBoundaryFlux_eq_neg_massEnergy_mul_centeredRate]
  have hcoefficient :
      -(thetaSource.mass * thetaXiRootEnergy q) ≠ 0 :=
    neg_ne_zero.mpr
      (mul_pos thetaSource.mass_pos (thetaXiRootEnergy_pos q)).ne'
  constructor
  · intro hrate
    rw [hrate, mul_zero]
  · intro hflux
    exact (mul_eq_zero.mp hflux).resolve_left hcoefficient

/-- Global prime-domain admission of the finite-shell-derived nonlinear carrier is exactly RH.
The equivalence is a receiver statement; no global admission premise is assumed. -/
theorem all_summable_sq_thetaGammaSixWoldHorizontalCarrier_iff_riemannHypothesis :
    (∀ q : XiZeroCopy, Summable (fun p : Nat.Primes =>
      thetaGammaSixWoldHorizontalCarrier p q ^ 2)) ↔
      RiemannHypothesis := by
  rw [← thetaGreenBoundaryNeutral_iff_riemannHypothesis]
  exact forall_congr'
    summable_sq_thetaGammaSixWoldHorizontalCarrier_iff_boundaryFlux_zero

end

end RHTower.HedenmalmThetaSource
