import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDampedMobiusCriticalEnergy
import GaloisForLFunctions.RHTower.MoebiusFloorSummatory
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheEscapeIsAnInteriorBump
import GaloisForLFunctions.TransHorizonIncidenceMechanics.ParityPairAtHalfDamping

/-!
# The escape is a tail phenomenon

The classical identity `Σ_{d ≤ n} μ(d) ⌊n/d⌋ = 1` says the *undamped* source is exactly the constant
one.  Writing the damped source against it gives an explicit, unconditional head bound: since
`1 − d^{-ε} ≤ ε log d`,

`|A_ε(n) − 1| ≤ ε Σ_{d ≤ n} (log d) ⌊n/d⌋ + n m₀(ε)`
(`abs_pmPowerDampedCenteredDivisorPrefix_sub_one_le`),

and both terms vanish with the damping at a fixed horizon.  So at small damping the source is close
to the constant one on any fixed head of horizons, and the escape of the critical energy — which is
what the Riemann hypothesis forbids — can only come from horizons beyond that head: for every
horizon and every tolerance there is a damping below which the head of the energy stays within the
tolerance of the pronic mass (`exists_damping_head_energy_le`).

Together with the interior-bump reframing this pins the obstruction in both parameters at once: it
lives at small damping *and* at large horizon, in the region where `ε Σ_{d ≤ n}(log d)⌊n/d⌋` is no
longer small.
-/

open Finset Filter Topology RHTower GaloisForLFunctions.TransHorizonIncidenceMechanics

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. The source against the undamped identity -/

/-- The centred prefix in floor coordinates. -/
theorem pmPowerDampedCenteredDivisorPrefix_eq_floor_sum (ε : ℝ) (n : ℕ) :
    pmPowerDampedCenteredDivisorPrefix ε n =
      (∑ d ∈ Icc 1 n, (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-ε) *
          ((n / d : ℕ) : ℝ)) -
        (pmPowerDampedDivisorDensity ε).re * n := by
  rw [pmPowerDampedCenteredDivisorPrefix_eq]
  congr 1
  have hcoeff : ∀ k : ℕ, pmPowerDampedDivisorCoeff ε k =
      ∑ d ∈ k.divisors, (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-ε) := fun k => rfl
  rw [Finset.sum_congr rfl fun k _ => hcoeff k]
  exact sum_Icc_sum_divisors_eq_floor
    (fun d => (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-ε)) n

/-- **The explicit head bound.**  The damped source differs from the constant one by at most the
damping times a logarithmic divisor sum, plus the pole term. -/
theorem abs_pmPowerDampedCenteredDivisorPrefix_sub_one_le {ε : ℝ} (hε : 0 ≤ ε) {n : ℕ}
    (hn : 1 ≤ n) :
    |pmPowerDampedCenteredDivisorPrefix ε n - 1| ≤
      ε * (∑ d ∈ Icc 1 n, Real.log d * ((n / d : ℕ) : ℝ)) +
        (n : ℝ) * |(pmPowerDampedDivisorDensity ε).re| := by
  have hundamped := moebius_floor_summatory n hn
  rw [pmPowerDampedCenteredDivisorPrefix_eq_floor_sum]
  have hdiff : (∑ d ∈ Icc 1 n, (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-ε) *
        ((n / d : ℕ) : ℝ)) - 1 =
      ∑ d ∈ Icc 1 n, (ArithmeticFunction.moebius d : ℝ) * ((d : ℝ) ^ (-ε) - 1) *
        ((n / d : ℕ) : ℝ) := by
    have hexpand : (∑ d ∈ Icc 1 n, (ArithmeticFunction.moebius d : ℝ) *
        ((d : ℝ) ^ (-ε) - 1) * ((n / d : ℕ) : ℝ)) =
        (∑ d ∈ Icc 1 n, (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-ε) *
          ((n / d : ℕ) : ℝ)) -
          ∑ d ∈ Icc 1 n, (ArithmeticFunction.moebius d : ℝ) * ((n / d : ℕ) : ℝ) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun d _ => by ring
    rw [hexpand, hundamped]
  have hcell : ∀ d ∈ Icc 1 n,
      |(ArithmeticFunction.moebius d : ℝ) * ((d : ℝ) ^ (-ε) - 1) * ((n / d : ℕ) : ℝ)| ≤
        ε * (Real.log d * ((n / d : ℕ) : ℝ)) := by
    intro d hd
    have hd1 : 1 ≤ d := (mem_Icc.mp hd).1
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    have hlog : 0 ≤ Real.log d := Real.log_natCast_nonneg d
    have hpow1 : (d : ℝ) ^ (-ε) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd1) (by linarith)
    have hpowlow : 1 - ε * Real.log d ≤ (d : ℝ) ^ (-ε) := by
      have hexp : Real.exp (-(ε * Real.log d)) ≥ 1 - ε * Real.log d := by
        have := Real.add_one_le_exp (-(ε * Real.log d))
        linarith
      have hrw : (d : ℝ) ^ (-ε) = Real.exp (-(ε * Real.log d)) := by
        rw [Real.rpow_def_of_pos hd0]
        congr 1
        ring
      rw [hrw]
      linarith
    have habs : |(d : ℝ) ^ (-ε) - 1| ≤ ε * Real.log d := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - (d : ℝ) ^ (-ε))]
      linarith
    have hμ : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    have hfloor : (0 : ℝ) ≤ ((n / d : ℕ) : ℝ) := Nat.cast_nonneg _
    rw [abs_mul, abs_mul, abs_of_nonneg hfloor]
    have hεlog : 0 ≤ ε * Real.log d := mul_nonneg hε hlog
    calc |((ArithmeticFunction.moebius d : ℤ) : ℝ)| * |(d : ℝ) ^ (-ε) - 1| *
          ((n / d : ℕ) : ℝ)
        ≤ 1 * (ε * Real.log d) * ((n / d : ℕ) : ℝ) := by
          have h1 := mul_le_mul hμ habs (abs_nonneg _) zero_le_one
          exact mul_le_mul_of_nonneg_right h1 hfloor
      _ = ε * (Real.log d * ((n / d : ℕ) : ℝ)) := by ring
  have hsum : |(∑ d ∈ Icc 1 n, (ArithmeticFunction.moebius d : ℝ) * ((d : ℝ) ^ (-ε) - 1) *
      ((n / d : ℕ) : ℝ))| ≤ ε * ∑ d ∈ Icc 1 n, Real.log d * ((n / d : ℕ) : ℝ) := by
    calc |(∑ d ∈ Icc 1 n, (ArithmeticFunction.moebius d : ℝ) * ((d : ℝ) ^ (-ε) - 1) *
        ((n / d : ℕ) : ℝ))|
        ≤ ∑ d ∈ Icc 1 n, |(ArithmeticFunction.moebius d : ℝ) * ((d : ℝ) ^ (-ε) - 1) *
            ((n / d : ℕ) : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Icc 1 n, ε * (Real.log d * ((n / d : ℕ) : ℝ)) := Finset.sum_le_sum hcell
      _ = ε * ∑ d ∈ Icc 1 n, Real.log d * ((n / d : ℕ) : ℝ) := by rw [Finset.mul_sum]
  have hpole : |(pmPowerDampedDivisorDensity ε).re * (n : ℝ)| =
      (n : ℝ) * |(pmPowerDampedDivisorDensity ε).re| := by
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    ring
  set S : ℝ := ∑ d ∈ Icc 1 n, (ArithmeticFunction.moebius d : ℝ) * (d : ℝ) ^ (-ε) *
    ((n / d : ℕ) : ℝ) with hS
  set D : ℝ := ∑ d ∈ Icc 1 n, (ArithmeticFunction.moebius d : ℝ) * ((d : ℝ) ^ (-ε) - 1) *
    ((n / d : ℕ) : ℝ) with hD
  set P : ℝ := (pmPowerDampedDivisorDensity ε).re * (n : ℝ) with hP
  have heq : S - (pmPowerDampedDivisorDensity ε).re * n - 1 = D - P := by
    rw [hP, ← hdiff]
    ring
  have htri : |D - P| ≤ |D| + |P| := by
    calc |D - P| = |D + -P| := by ring_nf
      _ ≤ |D| + |-P| := abs_add_le _ _
      _ = |D| + |P| := by rw [abs_neg]
  rw [heq]
  have hPabs : |P| = (n : ℝ) * |(pmPowerDampedDivisorDensity ε).re| := by
    rw [hP, abs_mul, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    ring
  rw [hPabs] at htri
  linarith [hsum, htri]

/-! ## §2. The head of the energy stays near the pronic mass -/

/-- **The escape is a tail phenomenon.**  At every fixed horizon the head of the critical energy
returns to the pronic mass as the damping tends to zero, so the escape lives beyond every fixed
horizon. -/
theorem exists_damping_head_energy_le (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → dampedMobiusEnergy ε N ≤ 1 + δ := by
  have hlim := tendsto_dampedMobiusEnergy_nhdsGT_zero N
  have hmass := pronicMass_le_one N
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), dampedMobiusEnergy ε N < 1 + δ :=
    hlim.eventually (gt_mem_nhds (by linarith))
  obtain ⟨ε₀, hε₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  exact ⟨ε₀, hε₀, fun ε hε hεlt => le_of_lt (hsub ⟨hε, hεlt⟩)⟩

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
