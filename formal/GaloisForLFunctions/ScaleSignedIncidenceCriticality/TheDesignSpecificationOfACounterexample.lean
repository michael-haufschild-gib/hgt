import GaloisForLFunctions.ScaleSignedIncidenceCriticality.TheHidingLaws
import GaloisForLFunctions.ScaleSignedIncidenceCriticality.ThreeBandsDefeatTheMass
import GaloisForLFunctions.SquareRootThreshold.CrystalRigidityAtTheSquareRootThreshold
import GaloisForLFunctions.SquareRootThreshold.ProfileRigidityAtTheSquareRootThreshold
import GaloisForLFunctions.SquareRootThreshold.ClusterTotalVariationBlindness
import GaloisForLFunctions.SquareRootThreshold.LagFamilyMeetsTheCrystalAtTheThreshold
import GaloisForLFunctions.SquareRootThreshold.PoleFreeDyadicWindowsDecideTheCriticalLine
import GaloisForLFunctions.SquareRootThreshold.ZoneHorizonLawAndTwistedPrimeWindows
import GaloisForLFunctions.SquareRootThreshold.WindowCertificatesAndThePrimeWeight
import GaloisForLFunctions.SquareRootThreshold.ZetaZeroCountRemainderIsUnbounded

/-!
# The design specification of a counterexample

The hiding laws (`TheHidingLaws`) prescribe the architecture of any off-line configuration that
remains invisible up to aperture `a`: an off-line sub-lattice of spacing parameter `ℓ`, an on-line
background of mass parameter `L` obeying `bandEnergy ℓ δ ⌈2a/ℓ⌉₊ ≤ 2L`, and a depth profile free
of total-variation edges above `1/(a sinh(2δa))`. This module solves the two problems posed by that
specification: it computes the exact resolution law and hiding reach of the structured family, and
it determines its compatibility with the prime-side explicit formula across dyadic windows.

1. **Hyperbolic decomposition and strict monotonicity of the band energy**
   (`centredSum_eq_sum_cosh`, `bandEnergy_eq_sum_cosh_sub_one`, `bandEnergy_strictMono_depth`).
   Symmetrising the centred sum under `Fin.revPerm` writes the `n`-th band energy as
   `bandEnergy ℓ δ n = ℓ ∑_{j < n} (cosh(δℓ(2j − n + 1)) − 1)`. Consequently `bandEnergy ℓ δ n` is
   strictly increasing in `δ > 0` for every aliasing index `n ≥ 2`, and satisfies the two-step
   recurrence `bandEnergy ℓ δ (n + 1) − bandEnergy ℓ δ (n − 1) = 2ℓ(cosh(nδℓ) − 1)`
   (`bandEnergy_succ_sub_pred`).

2. **Exact resolution limit, floor, and reach law of `dilutedReading`**
   (`dilutedReading_iff_bandEnergy_le`, `resolutionFloor_depth_dilutedReading`,
   `resolutionLimit_depth_dilutedReading_subNyquist`,
   `resolutionLimit_depth_dilutedReading_secondBand`,
   `resolutionLimit_depth_dilutedReading_brackets`).
   On `DepthDatum`, `dilutedReading hℓ hL a` has resolution floor `0` at every aperture `0 < a ≤ L/2`.
   Its exact resolution limit is `1/2` in the sub-Nyquist regime `a ≤ ℓ/2`, drops to
   `min (1/2) (arcosh(1 + L/ℓ)/ℓ)` across the second aliasing band `ℓ/2 < a ≤ min ℓ (L/2)`, and for
   arbitrary `a ∈ (ℓ/2, L/2]` is bracketed between explicit hyperbolic and logarithmic functions of
   `2L/ℓ` and `⌈2a/ℓ⌉₊`.

3. **Dyadic two-bump comb law on a diluted counterexample**
   (`W_dilutedLattice_eq_offLineLattice_add`, `W_dilutedLattice_lag_nat_mul`,
   `W_dilutedLattice_lag_eq_of_gap`, `re_W_dilutedLattice_lag_nat_mul_nonneg_iff`).
   Below the background Nyquist aperture `L/2`, the Weil form of `dilutedLatticeConfig` splits as
   `W_diluted(f, f) = W_offLine(f, f) + 2L k(0)`. On the two-bump difference family
   `twoBump (modScaledBump w 0) v (-1)` — which for `2w < log 2` reads the primes of a single
   dyadic window `lagPrimeWindow v w` — every gap `|v − nℓ| > 2w` evaluates to the positive constant
   `4(L + ℓ)‖κ_w‖²`, while the `n`-th resonant tooth `v = nℓ` evaluates to
   `4(L − ℓ(cosh(nδℓ) − 1))‖κ_w‖²`. Thus a diluted configuration is compatible with the dyadic
   difference tests up to lag `V ≤ L − 2w` if and only if every resonant tooth `nℓ ≤ V` satisfies
   `ℓ(cosh(nδℓ) − 1) ≤ L`, and the first two teeth `v = ℓ, 2ℓ` read `-2 bandDeficit ℓ δ L 2` and
   `-2 bandDeficit ℓ δ L 3` directly.

4. **Incompatibility with the prime-side explicit formula of `ζ`**
   (`counterexample_primeSide_obstructions`).
   No off-line configuration of `ζ` can sustain the counterexample specification across the dyadic
   prime windows:
   * below `(log 2)/2`, the aperture-`3/10` certificate holds unconditionally for every prime weight
     (`re_weilFullFunctional_ge_of_aperture_le_threeTenths`), forcing any hiding structure past
     `3/10` to pay exponential mass or wide spacing;
   * at growing scale, hiding up to the threshold forces uniform depth and crystalline spacing
     (`uniform_crystal_of_hiding`, `profile_hides_frequently_iff_uniform`), while finite clusters are
     bounded by total variation (`re_W_clusterConfig_ge`);
   * the prime-torus oscillation of `windowPrime` forces `rvmRemainder` to be unbounded
     (`rvmRemainder_unbounded`), ruling out any configuration with a bounded counting remainder;
   * any off-line zero of `ζ` violates dyadic prime-window positivity at unbounded lags at the rate
     of its depth (`zeta_exists_primeWindow_lt`, `onLine_iff_polarFree_primeWindow_le_arch`), and any
     near-top zero is exposed by a single dyadic prime window within the polylogarithmic lag
     `nearTopLag` (`zeta_near_top_primeWindow_neg`).
-/

open Set MeasureTheory Complex Filter Topology
open scoped Real ComplexConjugate
open GaloisForLFunctions.SquareRootThreshold
open Zeta23 _root_.RHTower

namespace GaloisForLFunctions.ScaleSignedIncidenceCriticality

set_option autoImplicit false

/-! ### 1. Hyperbolic decomposition and strict monotonicity of the band energy -/

/-- Reversing the summation index in `centredSum` negates the exponent. -/
theorem centredSum_eq_sum_neg (u : ℝ) (n : ℕ) :
    centredSum u n = ∑ j : Fin n, Real.exp (-(u * (2 * (j : ℝ) - n + 1))) := by
  rw [centredSum, ← Equiv.sum_comp Fin.revPerm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fin.revPerm_apply, Fin.val_rev]
  congr 1
  have hj : (j : ℕ) + 1 ≤ n := j.isLt
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

/-- **Hyperbolic decomposition of the centred sum.** Symmetrising `centredSum` under `Fin.revPerm`
writes it as a sum of hyperbolic cosines. -/
theorem centredSum_eq_sum_cosh (u : ℝ) (n : ℕ) :
    centredSum u n = ∑ j : Fin n, Real.cosh (u * (2 * (j : ℝ) - n + 1)) := by
  have hdef : centredSum u n = ∑ j : Fin n, Real.exp (u * (2 * (j : ℝ) - n + 1)) := rfl
  have hneg := centredSum_eq_sum_neg u n
  have h1 : centredSum u n + centredSum u n =
      ∑ j : Fin n, (Real.exp (u * (2 * (j : ℝ) - n + 1)) +
        Real.exp (-(u * (2 * (j : ℝ) - n + 1)))) := by
    rw [Finset.sum_add_distrib, ← hdef, ← hneg]
  have h2 : ∑ j : Fin n, (Real.exp (u * (2 * (j : ℝ) - n + 1)) +
        Real.exp (-(u * (2 * (j : ℝ) - n + 1)))) =
      2 * ∑ j : Fin n, Real.cosh (u * (2 * (j : ℝ) - n + 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Real.cosh_eq]
    ring
  linarith

/-- **Closed cosh formula for `latticeFloor` without positivity hypotheses.** -/
theorem latticeFloor_eq_sum_one_sub_cosh (ℓ δ : ℝ) (n : ℕ) :
    latticeFloor ℓ δ n = ∑ j : Fin n, (1 - Real.cosh ((δ * ℓ) * (2 * (j : ℝ) - n + 1))) := by
  rw [latticeFloor, sqrt_latticeSums_eq, centredSum_eq_sum_cosh, Finset.sum_sub_distrib]
  simp

/-- **Hyperbolic decomposition of `bandEnergy`.** Every aliasing band energy is a nonnegative sum of
`cosh − 1` modes. -/
theorem bandEnergy_eq_sum_cosh_sub_one (ℓ δ : ℝ) (n : ℕ) :
    bandEnergy ℓ δ n = ℓ * ∑ j : Fin n, (Real.cosh ((δ * ℓ) * (2 * (j : ℝ) - n + 1)) - 1) := by
  rw [bandEnergy, latticeFloor_eq_sum_one_sub_cosh, ← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun j _ => by ring

@[simp] theorem bandEnergy_zero (ℓ δ : ℝ) : bandEnergy ℓ δ 0 = 0 := by
  simp [bandEnergy_eq_sum_cosh_sub_one]

@[simp] theorem bandEnergy_one (ℓ δ : ℝ) : bandEnergy ℓ δ 1 = 0 := by
  rw [bandEnergy, latticeFloor_one, mul_zero, neg_zero]

theorem bandEnergy_nonneg {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (δ : ℝ) (n : ℕ) :
    0 ≤ bandEnergy ℓ δ n := by
  rw [bandEnergy_eq_sum_cosh_sub_one]
  refine mul_nonneg hℓ (Finset.sum_nonneg fun j _ => ?_)
  linarith [Real.one_le_cosh ((δ * ℓ) * (2 * (j : ℝ) - n + 1))]

/-- **Two-step recurrence for `bandEnergy`.** The difference `bandEnergy ℓ δ (n + 1) − bandEnergy ℓ δ (n − 1)`
isolates the outer mode `2ℓ(cosh(nδℓ) − 1)`. -/
theorem bandEnergy_succ_sub_pred {ℓ δ : ℝ} (hδℓ : 0 < δ * ℓ) {n : ℕ} (hn : 1 ≤ n) :
    bandEnergy ℓ δ (n + 1) - bandEnergy ℓ δ (n - 1) =
      2 * ℓ * (Real.cosh ((n : ℝ) * (δ * ℓ)) - 1) := by
  have hs : Real.sinh (δ * ℓ) ≠ 0 := (Real.sinh_pos_iff.mpr hδℓ).ne'
  rw [bandEnergy_eq hδℓ (n + 1), bandEnergy_eq hδℓ (n - 1)]
  have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn, Nat.cast_one]
  have hnp : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [hn1, hnp]
  have hdiff : Real.sinh (((n : ℝ) + 1) * (δ * ℓ)) - Real.sinh (((n : ℝ) - 1) * (δ * ℓ)) =
      2 * Real.cosh ((n : ℝ) * (δ * ℓ)) * Real.sinh (δ * ℓ) := by
    rw [show ((n : ℝ) + 1) * (δ * ℓ) = (n : ℝ) * (δ * ℓ) + δ * ℓ by ring,
      show ((n : ℝ) - 1) * (δ * ℓ) = (n : ℝ) * (δ * ℓ) - δ * ℓ by ring,
      Real.sinh_add, Real.sinh_sub]
    ring
  calc ℓ * (Real.sinh (((n : ℝ) + 1) * (δ * ℓ)) / Real.sinh (δ * ℓ) - ((n : ℝ) + 1)) -
        ℓ * (Real.sinh (((n : ℝ) - 1) * (δ * ℓ)) / Real.sinh (δ * ℓ) - ((n : ℝ) - 1))
      = ℓ * ((Real.sinh (((n : ℝ) + 1) * (δ * ℓ)) - Real.sinh (((n : ℝ) - 1) * (δ * ℓ))) /
          Real.sinh (δ * ℓ) - 2) := by ring
    _ = 2 * ℓ * (Real.cosh ((n : ℝ) * (δ * ℓ)) - 1) := by
        rw [hdiff, mul_div_cancel_right₀ _ hs]
        ring

/-- **Strict monotonicity in the aliasing index.** -/
theorem bandEnergy_lt_succ {ℓ δ : ℝ} (hℓ : 0 < ℓ) (hδ : 0 < δ) {n : ℕ} (hn : 1 ≤ n) :
    bandEnergy ℓ δ n < bandEnergy ℓ δ (n + 1) := by
  rw [bandEnergy, bandEnergy]
  have := latticeFloor_succ_lt (mul_pos hδ hℓ) hn
  nlinarith

/-- **Monotonicity in the depth.** -/
theorem bandEnergy_mono_depth {ℓ : ℝ} (hℓ : 0 ≤ ℓ) {δ₁ δ₂ : ℝ} (hδ₁ : 0 ≤ δ₁) (hδ : δ₁ ≤ δ₂)
    (n : ℕ) : bandEnergy ℓ δ₁ n ≤ bandEnergy ℓ δ₂ n := by
  rw [bandEnergy_eq_sum_cosh_sub_one, bandEnergy_eq_sum_cosh_sub_one]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) hℓ
  have hle : |(δ₁ * ℓ) * (2 * (j : ℝ) - n + 1)| ≤ |(δ₂ * ℓ) * (2 * (j : ℝ) - n + 1)| := by
    rw [abs_mul (δ₁ * ℓ), abs_mul (δ₂ * ℓ), abs_of_nonneg (mul_nonneg hδ₁ hℓ),
      abs_of_nonneg (mul_nonneg (hδ₁.trans hδ) hℓ)]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hδ hℓ) (abs_nonneg _)
  linarith [Real.cosh_le_cosh.mpr hle]

/-- **Strict monotonicity in the depth above index one.** -/
theorem bandEnergy_strictMono_depth {ℓ : ℝ} (hℓ : 0 < ℓ) {δ₁ δ₂ : ℝ} (hδ₁ : 0 ≤ δ₁)
    (hδ : δ₁ < δ₂) {n : ℕ} (hn : 2 ≤ n) :
    bandEnergy ℓ δ₁ n < bandEnergy ℓ δ₂ n := by
  rw [bandEnergy_eq_sum_cosh_sub_one, bandEnergy_eq_sum_cosh_sub_one]
  refine mul_lt_mul_of_pos_left (Finset.sum_lt_sum (fun j _ => ?_) ?_) hℓ
  · have hle : |(δ₁ * ℓ) * (2 * (j : ℝ) - n + 1)| ≤ |(δ₂ * ℓ) * (2 * (j : ℝ) - n + 1)| := by
      rw [abs_mul (δ₁ * ℓ), abs_mul (δ₂ * ℓ), abs_of_nonneg (mul_nonneg hδ₁ hℓ.le),
        abs_of_nonneg (mul_nonneg (hδ₁.trans hδ.le) hℓ.le)]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hδ.le hℓ.le) (abs_nonneg _)
    linarith [Real.cosh_le_cosh.mpr hle]
  · refine ⟨⟨0, by omega⟩, Finset.mem_univ _, ?_⟩
    have hc : (0 : ℝ) < |2 * (((⟨0, by omega⟩ : Fin n) : ℕ) : ℝ) - n + 1| := by
      simp only [Nat.cast_zero, mul_zero, zero_sub]
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
      rw [abs_of_neg (by linarith)]
      linarith
    have hlt : |(δ₁ * ℓ) * (2 * (((⟨0, by omega⟩ : Fin n) : ℕ) : ℝ) - n + 1)| <
        |(δ₂ * ℓ) * (2 * (((⟨0, by omega⟩ : Fin n) : ℕ) : ℝ) - n + 1)| := by
      rw [abs_mul (δ₁ * ℓ), abs_mul (δ₂ * ℓ), abs_of_nonneg (mul_nonneg hδ₁ hℓ.le),
        abs_of_nonneg (mul_nonneg (hδ₁.trans hδ.le) hℓ.le)]
      exact mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hδ hℓ) hc
    linarith [Real.cosh_lt_cosh.mpr hlt]

/-- Explicit upper bound on `bandEnergy ℓ δ n` by `ℓ n (cosh(δ n ℓ) − 1)`. -/
theorem bandEnergy_le_mul_cosh {ℓ δ : ℝ} (hℓ : 0 ≤ ℓ) (hδ : 0 ≤ δ) (n : ℕ) :
    bandEnergy ℓ δ n ≤ ℓ * n * (Real.cosh (δ * (n * ℓ)) - 1) := by
  rw [bandEnergy_eq_sum_cosh_sub_one, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hℓ
  calc ∑ j : Fin n, (Real.cosh ((δ * ℓ) * (2 * (j : ℝ) - n + 1)) - 1)
      ≤ ∑ _j : Fin n, (Real.cosh (δ * (n * ℓ)) - 1) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hj : (j : ℝ) + 1 ≤ n := by exact_mod_cast j.isLt
        have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
        have habs : |2 * (j : ℝ) - n + 1| ≤ n := abs_le.mpr ⟨by linarith, by linarith⟩
        have hle : |(δ * ℓ) * (2 * (j : ℝ) - n + 1)| ≤ |δ * (n * ℓ)| := by
          rw [abs_mul (δ * ℓ), abs_of_nonneg (mul_nonneg hδ hℓ),
            abs_of_nonneg (mul_nonneg hδ (mul_nonneg (Nat.cast_nonneg n) hℓ)),
            show δ * (n * ℓ) = (δ * ℓ) * n by ring]
          exact mul_le_mul_of_nonneg_left habs (mul_nonneg hδ hℓ)
        linarith [Real.cosh_le_cosh.mpr hle]
    _ = n * (Real.cosh (δ * (n * ℓ)) - 1) := by simp [mul_sub]

/-! ### 2. Exact resolution limit and floor of `dilutedReading` -/

/-- **Characterization of `dilutedReading` by the band energy.** Below the background Nyquist
aperture `L/2`, a diluted configuration of depth `d` is Weil-nonnegative at aperture `a` iff its
`⌈2a/ℓ⌉₊`-th band energy is at most `2L`. -/
theorem dilutedReading_iff_bandEnergy_le {ℓ L a : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (ha : 0 < a)
    (haL : a ≤ L / 2) (d : DepthDatum) :
    dilutedReading hℓ hL a d ↔ bandEnergy ℓ (depth d) ⌈2 * a / ℓ⌉₊ ≤ 2 * L :=
  dilutedLattice_weil_nonneg_iff hℓ hL d.2.1 d.2.2 ha haL

/-- `dilutedReading` is downward-closed in the depth. -/
theorem dilutedReading_of_depth_le {ℓ L a : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (ha : 0 < a)
    (haL : a ≤ L / 2) {d₁ d₂ : DepthDatum} (hle : depth d₁ ≤ depth d₂)
    (hd₂ : dilutedReading hℓ hL a d₂) : dilutedReading hℓ hL a d₁ := by
  rw [dilutedReading_iff_bandEnergy_le hℓ hL ha haL] at hd₂ ⊢
  exact (bandEnergy_mono_depth hℓ.le d₁.2.1.le hle _).trans hd₂

/-- Every positive aperture `a ≤ L/2` admits small positive depths in `dilutedReading hℓ hL a`. -/
theorem exists_dilutedReading_lt {ℓ L a ε : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (ha : 0 < a)
    (haL : a ≤ L / 2) (hε : 0 < ε) :
    ∃ d : DepthDatum, depth d ≤ ε ∧ dilutedReading hℓ hL a d := by
  set n := ⌈2 * a / ℓ⌉₊ with hn
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
  set δ₀ := min (min ε (1 / 2)) (Real.arcosh (1 + 2 * L / (ℓ * n)) / (n * ℓ)) with hδ₀
  have hquot_pos : 0 < 2 * L / (ℓ * n) := by positivity
  have harc : 0 < Real.arcosh (1 + 2 * L / (ℓ * n)) := Real.arcosh_pos (by linarith)
  have hδ₀_pos : 0 < δ₀ := lt_min (lt_min hε (by norm_num)) (div_pos harc (by positivity))
  have hδ₀_half : δ₀ ≤ 1 / 2 := (min_le_left _ _).trans (min_le_right _ _)
  refine ⟨⟨δ₀, hδ₀_pos, hδ₀_half⟩, (min_le_left _ _).trans (min_le_left _ _), ?_⟩
  rw [dilutedReading_iff_bandEnergy_le hℓ hL ha haL]
  have hle : δ₀ * (n * ℓ) ≤ Real.arcosh (1 + 2 * L / (ℓ * n)) := by
    rw [← le_div_iff₀ (by positivity)]
    exact min_le_right _ _
  have h1 : (1 : ℝ) ≤ 1 + 2 * L / (ℓ * n) := by linarith
  have hcosh : Real.cosh (δ₀ * (n * ℓ)) - 1 ≤ 2 * L / (ℓ * n) := by
    have hc : Real.cosh (δ₀ * (n * ℓ)) ≤ Real.cosh (Real.arcosh (1 + 2 * L / (ℓ * n))) :=
      Real.cosh_le_cosh.mpr (by
        rw [abs_of_pos (by positivity), abs_of_pos harc]
        exact hle)
    rw [Real.cosh_arcosh h1] at hc
    linarith
  calc bandEnergy ℓ δ₀ n ≤ ℓ * n * (Real.cosh (δ₀ * (n * ℓ)) - 1) :=
        bandEnergy_le_mul_cosh hℓ.le hδ₀_pos.le n
    _ ≤ ℓ * n * (2 * L / (ℓ * n)) := mul_le_mul_of_nonneg_left hcosh (by positivity)
    _ = 2 * L := mul_div_cancel₀ _ (by positivity)

theorem bddBelow_depth_shadow {O : Type*} (R : DepthDatum → O) (d₀ : DepthDatum) :
    BddBelow (depth '' shadow R d₀) := by
  refine ⟨0, fun x hx => ?_⟩
  obtain ⟨d, -, rfl⟩ := hx
  exact d.2.1.le

theorem bddAbove_depth_shadow {O : Type*} (R : DepthDatum → O) (d₀ : DepthDatum) :
    BddAbove (depth '' shadow R d₀) := by
  refine ⟨1 / 2, fun x hx => ?_⟩
  obtain ⟨d, -, rfl⟩ := hx
  exact d.2.2

/-- **The resolution floor of `dilutedReading` is zero at every aperture.** Arbitrarily shallow
off-line sub-lattices pass the aperture-`a` certificate inside any on-line background. -/
theorem resolutionFloor_depth_dilutedReading {ℓ L a : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (ha : 0 < a)
    (haL : a ≤ L / 2) {d₀ : DepthDatum} (hd₀ : dilutedReading hℓ hL a d₀) :
    resolutionFloor depth (dilutedReading hℓ hL a) d₀ = 0 := by
  refine le_antisymm ?_ (le_csInf (shadow_image_nonempty depth _ d₀) fun x hx => by
    obtain ⟨d, -, rfl⟩ := hx; exact d.2.1.le)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  rw [zero_add]
  obtain ⟨d, hdε, hd⟩ := exists_dilutedReading_lt hℓ hL ha haL hε
  have hmem : d ∈ shadow (dilutedReading hℓ hL a) d₀ := propext (iff_of_true hd hd₀)
  exact (csInf_le (bddBelow_depth_shadow _ d₀) ⟨d, hmem, rfl⟩).trans hdε

/-- **Sub-Nyquist resolution law (`a ≤ ℓ/2`).** Below the sub-lattice's own Nyquist aperture,
aliasing is free and `dilutedReading` has resolution limit `1/2`, floor `0`, and resolution
interval `[0, 1/2]`. -/
theorem resolutionLimit_depth_dilutedReading_subNyquist {ℓ L a : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L)
    (ha : 0 < a) (haℓ : a ≤ ℓ / 2) (haL : a ≤ L / 2) (d₀ : DepthDatum) :
    resolutionLimit depth (dilutedReading hℓ hL a) d₀ = 1 / 2 ∧
      resolutionFloor depth (dilutedReading hℓ hL a) d₀ = 0 ∧
      resolutionInterval depth (dilutedReading hℓ hL a) d₀ = Icc 0 (1 / 2) := by
  have hd₀ : dilutedReading hℓ hL a d₀ := fun f hf hfs =>
    dilutedLattice_hides_below_own_nyquist hℓ hL d₀.2.1 d₀.2.2 ha haℓ haL hf hfs
  set dmax : DepthDatum := ⟨1 / 2, by norm_num, le_rfl⟩
  have hdmax : dilutedReading hℓ hL a dmax := fun f hf hfs =>
    dilutedLattice_hides_below_own_nyquist hℓ hL dmax.2.1 dmax.2.2 ha haℓ haL hf hfs
  have hlim : resolutionLimit depth (dilutedReading hℓ hL a) d₀ = 1 / 2 :=
    resolutionLimit_eq_of_mem_shadow_of_max (fun d => d.2.2)
      (propext (iff_of_true hdmax hd₀)) rfl
  have hfl : resolutionFloor depth (dilutedReading hℓ hL a) d₀ = 0 :=
    resolutionFloor_depth_dilutedReading hℓ hL ha haL hd₀
  refine ⟨hlim, hfl, ?_⟩
  rw [resolutionInterval, hfl, hlim]

/-- **Second-band characterization (`ℓ/2 < a ≤ ℓ`).** Across the second aliasing band,
`dilutedReading hℓ hL a d` holds iff `depth d ≤ depthResolution ℓ (2 * L) = arcosh(1 + L/ℓ)/ℓ`. -/
theorem dilutedReading_secondBand_iff {ℓ L a : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (ha : ℓ / 2 < a)
    (haℓ : a ≤ ℓ) (haL : a ≤ L / 2) (d : DepthDatum) :
    dilutedReading hℓ hL a d ↔ depth d ≤ depthResolution ℓ (2 * L) := by
  have ha0 : 0 < a := lt_trans (by positivity) ha
  have hdpos : 0 < depth d := d.2.1
  rw [dilutedReading_iff_bandEnergy_le hℓ hL ha0 haL, ceil_two_mul_div_eq_two hℓ ha haℓ,
    bandEnergy, groundEnergy_index_two (mul_pos hdpos hℓ), ← weilFloorThreshold,
    weilFloorThreshold_le_iff hℓ hdpos (by positivity)]

/-- **Exact resolution limit and interval on the second aliasing band.** For `ℓ/2 < a ≤ min ℓ (L/2)`,
the resolution limit of `depth` under `dilutedReading hℓ hL a` is
`min (1/2) (arcosh(1 + L/ℓ)/ℓ)`. -/
theorem resolutionLimit_depth_dilutedReading_secondBand {ℓ L a : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L)
    (ha : ℓ / 2 < a) (haℓ : a ≤ ℓ) (haL : a ≤ L / 2) {d₀ : DepthDatum}
    (hd₀ : dilutedReading hℓ hL a d₀) :
    resolutionLimit depth (dilutedReading hℓ hL a) d₀ = min (1 / 2) (depthResolution ℓ (2 * L)) ∧
      resolutionFloor depth (dilutedReading hℓ hL a) d₀ = 0 ∧
      resolutionInterval depth (dilutedReading hℓ hL a) d₀ =
        Icc 0 (min (1 / 2) (depthResolution ℓ (2 * L))) := by
  have ha0 : 0 < a := lt_trans (by positivity) ha
  have hD : 0 < depthResolution ℓ (2 * L) := depthResolution_pos hℓ (by positivity)
  have hm0 : 0 < min (1 / 2 : ℝ) (depthResolution ℓ (2 * L)) := lt_min (by norm_num) hD
  have hmle : min (1 / 2 : ℝ) (depthResolution ℓ (2 * L)) ≤ 1 / 2 := min_le_left _ _
  have hlim : resolutionLimit depth (dilutedReading hℓ hL a) d₀ =
      min (1 / 2) (depthResolution ℓ (2 * L)) := by
    refine le_antisymm (csSup_le (shadow_image_nonempty depth _ d₀) ?_) ?_
    · rintro x ⟨d, hd, rfl⟩
      have hread : dilutedReading hℓ hL a d := (mem_shadow_iff.mp hd) ▸ hd₀
      exact le_min d.2.2 ((dilutedReading_secondBand_iff hℓ hL ha haℓ haL d).mp hread)
    · set d₁ : DepthDatum := ⟨min (1 / 2) (depthResolution ℓ (2 * L)), hm0, hmle⟩
      have hread₁ : dilutedReading hℓ hL a d₁ :=
        (dilutedReading_secondBand_iff hℓ hL ha haℓ haL d₁).mpr (min_le_right _ _)
      have hmem : d₁ ∈ shadow (dilutedReading hℓ hL a) d₀ := propext (iff_of_true hread₁ hd₀)
      exact le_csSup (bddAbove_depth_shadow _ d₀) ⟨d₁, hmem, rfl⟩
  have hfl : resolutionFloor depth (dilutedReading hℓ hL a) d₀ = 0 :=
    resolutionFloor_depth_dilutedReading hℓ hL ha0 haL hd₀
  refine ⟨hlim, hfl, ?_⟩
  rw [resolutionInterval, hfl, hlim]

/-- **General trans-Nyquist resolution brackets (`ℓ/2 < a ≤ L/2`).** For every aperture above the
sub-lattice Nyquist threshold, the resolution limit of `dilutedReading` is bracketed from below by
the explicit hyperbolic bound of index `n = ⌈2a/ℓ⌉₊` and from above by the logarithmic mass-exchange
bound. -/
theorem resolutionLimit_depth_dilutedReading_brackets {ℓ L a : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L)
    (ha : ℓ / 2 < a) (haL : a ≤ L / 2) {d₀ : DepthDatum} (hd₀ : dilutedReading hℓ hL a d₀) :
    min (1 / 2) (Real.arcosh (1 + 2 * L / (ℓ * ⌈2 * a / ℓ⌉₊)) / (⌈2 * a / ℓ⌉₊ * ℓ)) ≤
        resolutionLimit depth (dilutedReading hℓ hL a) d₀ ∧
      resolutionLimit depth (dilutedReading hℓ hL a) d₀ ≤
        min (1 / 2) (Real.log ((2 * L + 2 * a + ℓ) / ℓ) / (2 * a - ℓ)) := by
  have ha0 : 0 < a := lt_trans (by positivity) ha
  set n := ⌈2 * a / ℓ⌉₊ with hn
  have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by positivity)).ne'
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn1
  constructor
  · set δ₁ := min (1 / 2) (Real.arcosh (1 + 2 * L / (ℓ * n)) / (n * ℓ)) with hδ₁
    have hquot_pos : 0 < 2 * L / (ℓ * n) := by positivity
    have harc : 0 < Real.arcosh (1 + 2 * L / (ℓ * n)) := Real.arcosh_pos (by linarith)
    have hδ₁_pos : 0 < δ₁ := lt_min (by norm_num) (div_pos harc (by positivity))
    have hδ₁_half : δ₁ ≤ 1 / 2 := min_le_left _ _
    set d₁ : DepthDatum := ⟨δ₁, hδ₁_pos, hδ₁_half⟩
    have hd₁ : dilutedReading hℓ hL a d₁ := by
      rw [dilutedReading_iff_bandEnergy_le hℓ hL ha0 haL]
      have hle : δ₁ * (n * ℓ) ≤ Real.arcosh (1 + 2 * L / (ℓ * n)) := by
        rw [← le_div_iff₀ (by positivity)]
        exact min_le_right _ _
      have h1 : (1 : ℝ) ≤ 1 + 2 * L / (ℓ * n) := by linarith
      have hcosh : Real.cosh (δ₁ * (n * ℓ)) - 1 ≤ 2 * L / (ℓ * n) := by
        have hc : Real.cosh (δ₁ * (n * ℓ)) ≤ Real.cosh (Real.arcosh (1 + 2 * L / (ℓ * n))) :=
          Real.cosh_le_cosh.mpr (by
            rw [abs_of_pos (by positivity), abs_of_pos harc]
            exact hle)
        rw [Real.cosh_arcosh h1] at hc
        linarith
      calc bandEnergy ℓ δ₁ n ≤ ℓ * n * (Real.cosh (δ₁ * (n * ℓ)) - 1) :=
            bandEnergy_le_mul_cosh hℓ.le hδ₁_pos.le n
        _ ≤ ℓ * n * (2 * L / (ℓ * n)) := mul_le_mul_of_nonneg_left hcosh (by positivity)
        _ = 2 * L := mul_div_cancel₀ _ (by positivity)
    have hmem : d₁ ∈ shadow (dilutedReading hℓ hL a) d₀ := propext (iff_of_true hd₁ hd₀)
    exact le_csSup (bddAbove_depth_shadow _ d₀) ⟨d₁, hmem, rfl⟩
  · refine csSup_le (shadow_image_nonempty depth _ d₀) ?_
    rintro x ⟨d, hd, rfl⟩
    exact le_min d.2.2 (certifies_depth_dilutedReading hℓ hL ha0 haL (by linarith) hd₀ d hd)

/-! ### 3. Dyadic two-bump comb law on a diluted counterexample -/

/-- **Splitting of the diluted Weil form below the background Nyquist aperture.** For any test `f`
supported in `[−L/2, L/2]`, the Weil form of `dilutedLatticeConfig` equals that of the off-line
sub-lattice plus the on-line diagonal `2L k(0)`. -/
theorem W_dilutedLattice_eq_offLineLattice_add {ℓ L δ : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-(L / 2)) (L / 2)) :
    (dilutedLatticeConfig hℓ hL hδ hδ').W f f =
      (offLineLatticeConfig hℓ hδ hδ').W f f + 2 * (L : ℂ) * EF.weilTest f f 0 := by
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  rw [W_dilutedLatticeConfig hℓ hL hδ hδ' hf hfs, offLineLattice_weil_floor_symbol hℓ hδ hδ' f hf hfc,
    lagSum_shiftSymbol hℓ hfc, ← SquareRootThreshold.weilTest_self_zero]
  have hℓc : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  push_cast
  have hℓL : (ℓ : ℂ) * (2 * (L : ℂ) / (ℓ : ℂ)) = 2 * L := by field_simp
  linear_combination (EF.weilTest f f 0) * hℓL

/-- At any lag `v > 2w`, the self-correlation of `twoBump (modScaledBump w 0) v (-1)` at `0` is
`2 ‖κ_w‖²`. -/
theorem weilTest_twoBump_modScaledBump_zero_of_lt {w v : ℝ} (hw : 0 < w) (hv : 2 * w < v) :
    EF.weilTest (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1)) 0 =
      2 * ((∫ t, ‖modScaledBump w 0 t‖ ^ 2 : ℝ) : ℂ) := by
  have hbs := modScaledBump_support hw 0
  have hb : ContDiff ℝ 2 (modScaledBump w 0) := contDiff_modScaledBump_two w 0
  have hbc : HasCompactSupport (modScaledBump w 0) := hasCompactSupport_of_support_subset_abs hbs
  have hv0 : 0 < v := by linarith
  have hKv : EF.weilTest (modScaledBump w 0) (modScaledBump w 0) v = 0 :=
    weilTest_self_eq_zero_of_lt hbs (by rw [abs_of_pos hv0]; exact hv)
  have hKmv : EF.weilTest (modScaledBump w 0) (modScaledBump w 0) (-v) = 0 :=
    weilTest_self_eq_zero_of_lt hbs (by rw [abs_neg, abs_of_pos hv0]; exact hv)
  rw [weilTest_twoBump_neg_one hb.continuous hbc v 0, zero_add, zero_sub, hKv, hKmv,
    sub_zero, sub_zero, SquareRootThreshold.weilTest_self_zero]

/-- **Teeth of the comb on a diluted counterexample.** For `4w < ℓ`, `n ≥ 1`, and `nℓ + 2w ≤ L`,
the two-bump difference test at the `n`-th sub-lattice tooth `v = nℓ` evaluates to
`4(L − ℓ(cosh(nδℓ) − 1))‖κ_w‖²`. -/
theorem W_dilutedLattice_lag_nat_mul {ℓ L δ : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) {w : ℝ} (hw : 0 < w) (hwℓ : 4 * w < ℓ) {n : ℕ} (hn : 1 ≤ n)
    (hnL : (n : ℝ) * ℓ + 2 * w ≤ L) :
    (dilutedLatticeConfig hℓ hL hδ hδ').W (twoBump (modScaledBump w 0) (n * ℓ) (-1))
        (twoBump (modScaledBump w 0) (n * ℓ) (-1)) =
      ((4 * (L - ℓ * (Real.cosh (n * δ * ℓ) - 1)) *
        ∫ t, ‖modScaledBump w 0 t‖ ^ 2 : ℝ) : ℂ) := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hv0 : 0 ≤ (n : ℝ) * ℓ := by positivity
  have hv2w : 2 * w < (n : ℝ) * ℓ := by nlinarith
  have hsupp : tsupport (twoBump (modScaledBump w 0) (n * ℓ) (-1)) ⊆ Icc (-(L / 2)) (L / 2) :=
    (tsupport_twoBump_modScaledBump_subset hw hv0).trans (Icc_subset_Icc (by linarith) (by linarith))
  rw [W_dilutedLattice_eq_offLineLattice_add hℓ hL hδ hδ'
      (f := twoBump (modScaledBump w 0) (n * ℓ) (-1))
      (contDiff_bumpTest (contDiff_modScaledBump_two w 0) (n * ℓ) ![1, -1]) hsupp,
    W_offLineLattice_lag_nat_mul hℓ hδ hδ' hw hwℓ hn,
    weilTest_twoBump_modScaledBump_zero_of_lt hw hv2w]
  push_cast
  ring

/-- **Gaps of the comb on a diluted counterexample.** Between the teeth `nℓ` (`|v − nℓ| > 2w`),
every two-bump difference test with `2w < v` and `v + 2w ≤ L` sees only the positive mean mode
`4(L + ℓ)‖κ_w‖²`. -/
theorem W_dilutedLattice_lag_eq_of_gap {ℓ L δ : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) {w : ℝ} (hw : 0 < w) (hwℓ : 4 * w < ℓ) {v : ℝ} (hv : 2 * w < v)
    (hvL : v + 2 * w ≤ L) (hgap : ∀ n : ℕ, 1 ≤ n → 2 * w < |v - n * ℓ|) :
    (dilutedLatticeConfig hℓ hL hδ hδ').W (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1)) =
      ((4 * (L + ℓ) * ∫ t, ‖modScaledBump w 0 t‖ ^ 2 : ℝ) : ℂ) := by
  have hv0 : 0 ≤ v := by linarith
  have hsupp : tsupport (twoBump (modScaledBump w 0) v (-1)) ⊆ Icc (-(L / 2)) (L / 2) :=
    (tsupport_twoBump_modScaledBump_subset hw hv0).trans (Icc_subset_Icc (by linarith) (by linarith))
  rw [W_dilutedLattice_eq_offLineLattice_add hℓ hL hδ hδ'
      (f := twoBump (modScaledBump w 0) v (-1))
      (contDiff_bumpTest (contDiff_modScaledBump_two w 0) v ![1, -1]) hsupp,
    W_offLineLattice_lag_eq_of_gap hℓ hδ hδ' hw hwℓ hv hgap,
    weilTest_twoBump_modScaledBump_zero_of_lt hw hv]
  push_cast
  ring

/-- **Sign criterion at the `n`-th dyadic tooth.** The `n`-th resonant two-bump difference test
`twoBump (modScaledBump w 0) (nℓ) (-1)` is Weil-nonnegative on `dilutedLatticeConfig` iff
`ℓ(cosh(nδℓ) − 1) ≤ L`, equivalently `nℓ ≤ arcosh(1 + L/ℓ)/δ`. -/
theorem re_W_dilutedLattice_lag_nat_mul_nonneg_iff {ℓ L δ : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) {w : ℝ} (hw : 0 < w) (hwℓ : 4 * w < ℓ) {n : ℕ} (hn : 1 ≤ n)
    (hnL : (n : ℝ) * ℓ + 2 * w ≤ L) :
    0 ≤ ((dilutedLatticeConfig hℓ hL hδ hδ').W (twoBump (modScaledBump w 0) (n * ℓ) (-1))
        (twoBump (modScaledBump w 0) (n * ℓ) (-1))).re ↔
      ℓ * (Real.cosh (n * δ * ℓ) - 1) ≤ L := by
  rw [W_dilutedLattice_lag_nat_mul hℓ hL hδ hδ' hw hwℓ hn hnL, Complex.ofReal_re]
  have hK := integral_norm_sq_modScaledBump_pos hw
  constructor
  · intro h
    have h1 : 0 ≤ 4 * (L - ℓ * (Real.cosh (n * δ * ℓ) - 1)) :=
       nonneg_of_mul_nonneg_left h hK
    linarith
  · intro h
    exact mul_nonneg (by linarith) hK.le

/-- **The first two teeth read the second and third band deficits directly.** At `n = 1` and `n = 2`,
the two-bump difference tests evaluate to `-2 bandDeficit ℓ δ L 2 ‖κ_w‖²` and
`-2 bandDeficit ℓ δ L 3 ‖κ_w‖²`. -/
theorem re_W_dilutedLattice_first_two_teeth_eq_bandDeficit {ℓ L δ : ℝ} (hℓ : 0 < ℓ) (hL : 0 < L)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) {w : ℝ} (hw : 0 < w) (hwℓ : 4 * w < ℓ)
    (h2L : 2 * ℓ + 2 * w ≤ L) :
    ((dilutedLatticeConfig hℓ hL hδ hδ').W (twoBump (modScaledBump w 0) ℓ (-1))
        (twoBump (modScaledBump w 0) ℓ (-1))).re =
      -2 * bandDeficit ℓ δ L 2 * (∫ t, ‖modScaledBump w 0 t‖ ^ 2) ∧
    ((dilutedLatticeConfig hℓ hL hδ hδ').W (twoBump (modScaledBump w 0) (2 * ℓ) (-1))
        (twoBump (modScaledBump w 0) (2 * ℓ) (-1))).re =
      -2 * bandDeficit ℓ δ L 3 * (∫ t, ‖modScaledBump w 0 t‖ ^ 2) := by
  have hδℓ : 0 < δ * ℓ := mul_pos hδ hℓ
  constructor
  · have h1 := W_dilutedLattice_lag_nat_mul hℓ hL hδ hδ' hw hwℓ (n := 1) le_rfl
      (by push_cast; linarith)
    simp only [Nat.cast_one, one_mul] at h1
    rw [h1, Complex.ofReal_re, bandDeficit_two hδℓ]
    ring
  · have h2 := W_dilutedLattice_lag_nat_mul hℓ hL hδ hδ' hw hwℓ (n := 2) (by norm_num)
      (by push_cast; linarith)
    simp only [Nat.cast_ofNat] at h2
    have hcosh2 : Real.cosh (2 * δ * ℓ) - 1 = 2 * (Real.cosh (δ * ℓ) ^ 2 - 1) := by
      rw [show 2 * δ * ℓ = 2 * (δ * ℓ) by ring, Real.cosh_two_mul]
      linarith [Real.cosh_sq (δ * ℓ)]
    rw [h2, Complex.ofReal_re, hcosh2, bandDeficit_three hδℓ]
    ring

/-! ### 4. Incompatibility with the prime-side explicit formula of `ζ` -/

/-- **Prime-side obstructions to a hiding counterexample for `ζ`.**
1. *Prime-free barrier (`a ≤ 3/10`)*: the explicit-formula functional is coercive (`≥ (1/5000)‖f‖²`)
   for every prime weight on `[−3/10, 3/10]`, so `ζ` is unconditionally positive up to `3/10`.
2. *Unbounded remainder*: the zero-count remainder `rvmRemainder` is unbounded, excluding any
   periodic or diluted-lattice model with bounded remainder.
3. *Dyadic prime-window negativity*: any off-line zero of `ζ` of depth `> σ ≥ 0` drives the dyadic
   window functional `lagPrimeWindowRHS v w` below `-K e^{σv}` at lags `v ≥ V` for every `K, V`.
4. *Polylogarithmic near-top visibility*: any `1/V`-near-top zero of `ζ` at height `γ₀ ≥ T_w` makes
   a single dyadic prime window negative at a lag `v ∈ [0, V]` once `V ≥ nearTopLag w γ₀ δ₀`. -/
theorem counterexample_primeSide_obstructions :
    (∀ (w : ℕ → ℝ) (f : ℝ → ℂ), ContDiff ℝ 2 f → tsupport f ⊆ Icc (-(3 / 10)) (3 / 10) →
      1 / 5000 * ∫ x, ‖f x‖ ^ 2 ≤ (weilFullFunctional w (EF.weilTest f f)).re) ∧
    (∀ B T₀ : ℝ, ∃ T, T₀ ≤ T ∧ B < |rvmRemainder T|) ∧
    (∀ (w : ℝ), 0 < w → 2 * w < Real.log 2 → ∀ (ρ : ℂ), ρ ∈ zetaZeroConfig.carrier →
      ∀ (σ : ℝ), 0 ≤ σ → σ < |ρ.re - 1 / 2| → ∀ K V : ℝ,
        ∃ (γ v : ℝ) (τ : ℂ), V ≤ v ∧ ‖τ‖ = 1 ∧
          (lagPrimeWindowRHS v w (EF.weilTest (twoBump (modScaledBump w γ) v τ)
            (twoBump (modScaledBump w γ) v τ))).re < -(K * Real.exp (σ * v))) ∧
    (∀ (w : ℝ), 0 < w → 2 * w < Real.log 2 → ∀ (z₀ : ℂ),
      (1 / 2 + z₀) ∈ zetaZeroConfig.carrier → 0 < z₀.re → nearTopHeight w ≤ z₀.im →
      1280 * Real.log (180 * recordHeightEnvelope w z₀.im) *
          (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 ≤
        centerAmplitude w ^ 2 / (2 * Real.exp 1) * (1 + z₀.im) ^ 4 →
      ∀ (V : ℝ), nearTopLag w z₀.im z₀.re ≤ V →
      (∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + 1 / V) →
        ∃ v ∈ Icc (0 : ℝ) V, (lagPrimeWindowRHS v w (EF.weilTest
          (twoBump (modScaledBump w z₀.im) v (-1))
          (twoBump (modScaledBump w z₀.im) v (-1)))).re < 0) :=
  ⟨fun w _ hf hfs => re_weilFullFunctional_ge_of_aperture_le_threeTenths w hf hfs,
    rvmRemainder_unbounded,
    fun _ hw hw2 _ hρ _ hσ0 hσ K V => zeta_exists_primeWindow_lt hw hw2 hρ hσ0 hσ K V,
    fun _ hw hw2 _ hz₀ hre₀ hTw hγ _ hV htop =>
      zeta_near_top_primeWindow_neg hw hw2 hz₀ hre₀ hTw hγ hV htop⟩

end GaloisForLFunctions.ScaleSignedIncidenceCriticality
