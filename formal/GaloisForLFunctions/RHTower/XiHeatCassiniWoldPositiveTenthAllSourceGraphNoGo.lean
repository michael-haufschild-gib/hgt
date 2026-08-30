import GaloisForLFunctions.RHTower.XiHeatCassiniWoldPositiveTenthBohrTerminalNoGo
import GaloisForLFunctions.RHTower.XiHeatCassiniWoldHolonomyLogSmooth

/-!
# T2 all-source graph-to-terminal reconstruction no-go

The positive-height T2 current is Bohr-Cauchy, while the genuine Wold primitive is smooth for
every power of the prime-log generator in three concrete Hilbert sources.  This module tests the
strongest reconstruction principle assembled from those already proved facts.

It still fails.  The literal-prime-clock witness `r_N = exp(-h_N/20)` belongs to every polynomial
graph domain for the harmonic, activation-Fisher, and literal essential-edge densities; its
height-`1/10` Abel increments remain square summable, but its terminal diverges.  Thus no argument
using all finite source graph norms plus the fixed-height Bohr limit can supply T2's terminal.

The positive survivor is sharp at Hilbert-source level: exponential graph radius `t` controls
terminal height `c` once `t ≥ c + 1/2`.  Consequently a height-cofinal T2 proof through graph
regularity needs source-specific analytic radii approaching `1`, or an arithmetic identity that
bypasses Hilbert point evaluation.
-/

open Complex Filter Topology Set MeasureTheory
open scoped BigOperators

namespace RHTower

noncomputable section

private theorem t2BohrTerminalCounterResidual_sq_eq_rpow (N : ℕ) :
    t2BohrTerminalCounterResidual N ^ 2 =
      (nthPrimeSubtype N : ℝ) ^ (-(1 / 10 : ℝ)) := by
  rw [t2BohrTerminalCounterResidual, pow_two, ← Real.exp_add,
    Real.rpow_def_of_pos (nthPrimeSubtype_pos N)]
  unfold xiMassNthPrimeLogHeight
  congr 1
  ring_nf

/-- Every strictly positive polynomial prime-log graph energy of the counterexample is finite. -/
theorem summable_t2BohrTerminalCounterResidual_positiveLogGraphEnergy (k : ℕ) :
    Summable (fun N : ℕ =>
      Real.log (nthPrimeSubtype N : ℝ) ^ (2 * (k + 1)) /
          (nthPrimeSubtype N : ℝ) *
        t2BohrTerminalCounterResidual N ^ 2) := by
  have hraw := summable_primeLogPowWeight_rpow (2 * (k + 1) - 1)
    (by norm_num : (0 : ℝ) < 1 / 10)
  have hinj : Function.Injective (fun N : ℕ => (nthPrimeSubtype N : ℕ)) :=
    fun _ _ h => nthPrimeSubtype_strictMono.injective h
  have h := hraw.comp_injective hinj
  refine h.congr (fun N => ?_)
  change
    primeLogPowWeight ((2 * (k + 1) - 1) + 1)
          (nthPrimeSubtype N : ℕ) *
        (nthPrimeSubtype N : ℝ) ^ (-(1 / 10 : ℝ)) =
      Real.log (nthPrimeSubtype N : ℝ) ^ (2 * (k + 1)) /
          (nthPrimeSubtype N : ℝ) *
        t2BohrTerminalCounterResidual N ^ 2
  have hk : (2 * (k + 1) - 1) + 1 = 2 * (k + 1) := by omega
  rw [hk, primeLogPowWeight, if_pos (nthPrimeSubtype N).prop,
    t2BohrTerminalCounterResidual_sq_eq_rpow]

private theorem summable_t2BohrTerminalCounterResidual_zeroLogGraphEnergy :
    Summable (fun N : ℕ =>
      (1 / (nthPrimeSubtype N : ℝ)) *
        t2BohrTerminalCounterResidual N ^ 2) := by
  have hscaled :=
    (summable_t2BohrTerminalCounterResidual_positiveLogGraphEnergy 0).mul_left
      (1 / Real.log 2 ^ 2)
  refine Summable.of_nonneg_of_le
    (fun N => mul_nonneg (by positivity) (sq_nonneg _)) (fun N => ?_) hscaled
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hp0 : (0 : ℝ) < (nthPrimeSubtype N : ℝ) := nthPrimeSubtype_pos N
  have hlogle : Real.log 2 ≤ Real.log (nthPrimeSubtype N : ℝ) :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hp0
      (by exact_mod_cast (nthPrimeSubtype N).prop.two_le)
  have hfactor : 1 ≤
      (1 / Real.log 2 ^ 2) *
        Real.log (nthPrimeSubtype N : ℝ) ^ 2 := by
    have hsquare := pow_le_pow_left₀ hlog2.le hlogle 2
    calc
      1 = (1 / Real.log 2 ^ 2) * Real.log 2 ^ 2 := by
        field_simp [hlog2.ne']
      _ ≤ (1 / Real.log 2 ^ 2) *
          Real.log (nthPrimeSubtype N : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hsquare (by positivity)
  calc
    (1 / (nthPrimeSubtype N : ℝ)) *
        t2BohrTerminalCounterResidual N ^ 2 =
      1 * ((1 / (nthPrimeSubtype N : ℝ)) *
        t2BohrTerminalCounterResidual N ^ 2) := by ring
    _ ≤ ((1 / Real.log 2 ^ 2) *
          Real.log (nthPrimeSubtype N : ℝ) ^ 2) *
        ((1 / (nthPrimeSubtype N : ℝ)) *
          t2BohrTerminalCounterResidual N ^ 2) :=
      mul_le_mul_of_nonneg_right hfactor
        (mul_nonneg (by positivity) (sq_nonneg _))
    _ = (1 / Real.log 2 ^ 2) *
        (Real.log (nthPrimeSubtype N : ℝ) ^ (2 * (0 + 1)) /
          (nthPrimeSubtype N : ℝ) *
          t2BohrTerminalCounterResidual N ^ 2) := by ring

/-- The counterexample belongs to every polynomial graph domain of the prime-harmonic source. -/
theorem summable_t2BohrTerminalCounterResidual_allLogGraphEnergy (k : ℕ) :
    Summable (fun N : ℕ =>
      Real.log (nthPrimeSubtype N : ℝ) ^ (2 * k) /
          (nthPrimeSubtype N : ℝ) *
        t2BohrTerminalCounterResidual N ^ 2) := by
  cases k with
  | zero => simpa using summable_t2BohrTerminalCounterResidual_zeroLogGraphEnergy
  | succ k => simpa [Nat.succ_eq_add_one] using
      summable_t2BohrTerminalCounterResidual_positiveLogGraphEnergy k

/-- The counterexample also belongs to every activation-Fisher polynomial graph domain. -/
theorem summable_t2BohrTerminalCounterResidual_activationFisherAllLogGraphEnergy (k : ℕ) :
    Summable (fun N : ℕ =>
      Real.log (nthPrimeSubtype N : ℝ) ^ (2 * k) *
          primeActivationOccupancyFisherDensity (nthPrimeSubtype N) *
        t2BohrTerminalCounterResidual N ^ 2) := by
  refine Summable.of_nonneg_of_le
    (fun N => mul_nonneg
      (mul_nonneg (by positivity)
        (by
          exact (show 0 ≤ 1 / (4 * (nthPrimeSubtype N : ℝ)) by positivity).trans
            (primeActivationOccupancyFisherDensity_bounds (nthPrimeSubtype N)).1))
      (sq_nonneg _))
    (fun N => ?_) (summable_t2BohrTerminalCounterResidual_allLogGraphEnergy k)
  calc
    Real.log (nthPrimeSubtype N : ℝ) ^ (2 * k) *
          primeActivationOccupancyFisherDensity (nthPrimeSubtype N) *
        t2BohrTerminalCounterResidual N ^ 2 ≤
      Real.log (nthPrimeSubtype N : ℝ) ^ (2 * k) *
          (1 / (nthPrimeSubtype N : ℝ)) *
        t2BohrTerminalCounterResidual N ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (primeActivationOccupancyFisherDensity_bounds (nthPrimeSubtype N)).2
          (by positivity)) (sq_nonneg _)
    _ = Real.log (nthPrimeSubtype N : ℝ) ^ (2 * k) /
          (nthPrimeSubtype N : ℝ) *
        t2BohrTerminalCounterResidual N ^ 2 := by ring

/-- The counterexample also belongs to every literal essential-edge polynomial graph domain. -/
theorem summable_t2BohrTerminalCounterResidual_actualEssentialEdgeAllLogGraphEnergy (k : ℕ) :
    Summable (fun N : ℕ =>
      Real.log (nthPrimeSubtype N : ℝ) ^ (2 * k) *
          primeFirstTraceEssentialHarmonicCoordinate (nthPrimeSubtype N) *
        t2BohrTerminalCounterResidual N ^ 2) := by
  refine Summable.of_nonneg_of_le
    (fun N => mul_nonneg
      (mul_nonneg (by positivity)
        (primeFirstTraceEssentialHarmonicCoordinate_nonneg (nthPrimeSubtype N)))
      (sq_nonneg _))
    (fun N => ?_) (summable_t2BohrTerminalCounterResidual_allLogGraphEnergy k)
  calc
    Real.log (nthPrimeSubtype N : ℝ) ^ (2 * k) *
          primeFirstTraceEssentialHarmonicCoordinate (nthPrimeSubtype N) *
        t2BohrTerminalCounterResidual N ^ 2 ≤
      Real.log (nthPrimeSubtype N : ℝ) ^ (2 * k) *
          (1 / (nthPrimeSubtype N : ℝ)) *
        t2BohrTerminalCounterResidual N ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (primeFirstTraceEssentialHarmonicCoordinate_bounds (nthPrimeSubtype N)).2
          (by positivity)) (sq_nonneg _)
    _ = Real.log (nthPrimeSubtype N : ℝ) ^ (2 * k) /
          (nthPrimeSubtype N : ℝ) *
        t2BohrTerminalCounterResidual N ^ 2 := by ring

/-- Reconstruction principle obtained by combining every currently proved source graph domain
with the fixed-height Abel/Bohr datum. -/
def T2PrimeClockBohrAllSourceGraphTerminalLandingPrinciple : Prop :=
  ∀ r : ℕ → ℝ,
    Tendsto r atTop (𝓝 0) →
    (∀ k : ℕ, Summable (fun N : ℕ =>
      Real.log (nthPrimeSubtype N : ℝ) ^ (2 * k) /
          (nthPrimeSubtype N : ℝ) * r N ^ 2)) →
    (∀ k : ℕ, Summable (fun N : ℕ =>
      Real.log (nthPrimeSubtype N : ℝ) ^ (2 * k) *
          primeActivationOccupancyFisherDensity (nthPrimeSubtype N) * r N ^ 2)) →
    (∀ k : ℕ, Summable (fun N : ℕ =>
      Real.log (nthPrimeSubtype N : ℝ) ^ (2 * k) *
          primeFirstTraceEssentialHarmonicCoordinate (nthPrimeSubtype N) * r N ^ 2)) →
    Summable (fun N : ℕ =>
      ‖(((r (N + 1) - r N : ℝ) : ℂ) *
        (Real.exp (xiMassNthPrimeLogHeight (N + 1) / 10) : ℂ))‖ ^ 2) →
    Tendsto (fun N : ℕ =>
      |r N| * Real.exp (xiMassNthPrimeLogHeight N / 10)) atTop (𝓝 0)

/-- **T2 all-source graph-to-terminal no-go.** Primitive vanishing, every polynomial graph
energy in all three current source Hilbert structures, and the height-`1/10` Bohr datum still do
not force terminal disappearance. -/
theorem not_T2PrimeClockBohrAllSourceGraphTerminalLandingPrinciple :
    ¬ T2PrimeClockBohrAllSourceGraphTerminalLandingPrinciple := by
  intro hlanding
  have hzero := hlanding t2BohrTerminalCounterResidual
    t2BohrTerminalCounterResidual_tendsto_zero
    summable_t2BohrTerminalCounterResidual_allLogGraphEnergy
    summable_t2BohrTerminalCounterResidual_activationFisherAllLogGraphEnergy
    summable_t2BohrTerminalCounterResidual_actualEssentialEdgeAllLogGraphEnergy
    summable_norm_sq_t2BohrTerminalCounterCoefficient
  have hsmall : ∀ᶠ N : ℕ in atTop,
      |t2BohrTerminalCounterResidual N| *
        Real.exp (xiMassNthPrimeLogHeight N / 10) < 1 :=
    hzero (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  have hlarge : ∀ᶠ N : ℕ in atTop,
      1 < |t2BohrTerminalCounterResidual N| *
        Real.exp (xiMassNthPrimeLogHeight N / 10) :=
    t2BohrTerminalCounterAbsTerminal_tendsto_atTop (eventually_gt_atTop 1)
  obtain ⟨N, hs, hl⟩ := (hsmall.and hlarge).exists
  linarith

/-- **Exact surviving terminal-control threshold.** In the prime-harmonic Hilbert source,
exponential graph radius `t` controls terminal height `c` as soon as `t ≥ c + 1/2`. -/
theorem tendsto_primeClockTerminal_of_exponentialGraphEnergy
    (r : ℕ → ℝ) {c t : ℝ} (hct : c + 1 / 2 ≤ t)
    (hsum : Summable (fun N : ℕ =>
      Real.exp (2 * t * xiMassNthPrimeLogHeight N) *
        (1 / (nthPrimeSubtype N : ℝ)) * r N ^ 2)) :
    Tendsto (fun N : ℕ =>
      |r N| * Real.exp (c * xiMassNthPrimeLogHeight N)) atTop (𝓝 0) := by
  have henergy := hsum.tendsto_atTop_zero
  have hsq : Tendsto (fun N : ℕ =>
      (|r N| * Real.exp (c * xiMassNthPrimeLogHeight N)) ^ 2)
      atTop (𝓝 0) := by
    refine squeeze_zero' (Filter.Eventually.of_forall (fun N => sq_nonneg _))
      (Filter.Eventually.of_forall (fun N => ?_)) henergy
    have hh0 : 0 ≤ xiMassNthPrimeLogHeight N :=
      (xiMassNthPrimeLogHeight_pos N).le
    have hexple :
        Real.exp (2 * c * xiMassNthPrimeLogHeight N) ≤
          Real.exp ((2 * t - 1) * xiMassNthPrimeLogHeight N) := by
      apply Real.exp_le_exp.mpr
      have hrate : 2 * c ≤ 2 * t - 1 := by linarith
      exact mul_le_mul_of_nonneg_right hrate hh0
    calc
      (|r N| * Real.exp (c * xiMassNthPrimeLogHeight N)) ^ 2 =
          r N ^ 2 * Real.exp (2 * c * xiMassNthPrimeLogHeight N) := by
        rw [mul_pow, sq_abs, ← Real.exp_nat_mul]
        congr 1
        ring_nf
      _ ≤ r N ^ 2 * Real.exp ((2 * t - 1) *
          xiMassNthPrimeLogHeight N) :=
        mul_le_mul_of_nonneg_left hexple (sq_nonneg _)
      _ = Real.exp (2 * t * xiMassNthPrimeLogHeight N) *
          (1 / (nthPrimeSubtype N : ℝ)) * r N ^ 2 := by
        have hprimeInv : 1 / (nthPrimeSubtype N : ℝ) =
            Real.exp (-xiMassNthPrimeLogHeight N) := by
          rw [xiMassNthPrimeLogHeight, Real.exp_neg,
            Real.exp_log (nthPrimeSubtype_pos N)]
          simp only [one_div]
        rw [hprimeInv, ← Real.exp_add]
        have heq : 2 * t * xiMassNthPrimeLogHeight N +
            -xiMassNthPrimeLogHeight N =
          (2 * t - 1) * xiMassNthPrimeLogHeight N := by ring
        rw [heq]
        ring_nf
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [Real.sqrt_zero] at hsqrt
  convert hsqrt using 1
  funext N
  change |r N| * Real.exp (c * xiMassNthPrimeLogHeight N) =
    Real.sqrt ((|r N| * Real.exp (c * xiMassNthPrimeLogHeight N)) ^ 2)
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg
    (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le)]

end

end RHTower
