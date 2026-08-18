import GaloisForLFunctions.RHTower.Sieve.OmegaWeightTransfer
import GaloisForLFunctions.RHTower.Sieve.ScaledFibreBridge
import GaloisForLFunctions.RHTower.Sieve.OmegaWeightedFactorisation
import GaloisForLFunctions.RHTower.Sieve.LogWindowPlancherel
import GaloisForLFunctions.RHTower.Sieve.PairFibreMeanSquare

/-!
# The Möbius fibre mean square against the weighted spectral side

Chaining the Turán--Kubilius transfer, the rescaled fibre bridge and Plancherel puts the whole
short-interval input of the Route E cards on the `ω_P`-weighted Dirichlet polynomial — the object
that factors exactly into a prime polynomial times a cofactor polynomial.

Everything below is an inequality between explicit quantities; no asymptotic notation and no
hypothesis on the designated range beyond `z₀ ≤ z`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory Filter Topology
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- The weighted Möbius polynomial is the Gallagher polynomial of the weighted coefficients. -/
theorem logPoly_omegaWeighted_eq (P S : Finset ℕ) (w : ℝ) :
    logPoly (fun n => ((((ArithmeticFunction.moebius n : ℤ) : ℝ)
        * ((primeFactorsIn P n).card : ℝ) : ℝ) : ℂ)) S w
      = omegaWeightedMoebiusPoly P S w := by
  rw [logPoly, omegaWeightedMoebiusPoly]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [moebiusPhase, unitLogPhase]
  push_cast
  ring

/-- The designated prime count never exceeds the size of the designated set. -/
theorem card_primeFactorsIn_le (P : Finset ℕ) (n : ℕ) :
    ((primeFactorsIn P n).card : ℝ) ≤ (P.card : ℝ) := by
  have := Finset.card_le_card (Finset.filter_subset (fun p => p ∣ n) P)
  exact_mod_cast this

/-- **The Möbius fibre mean square against the weighted spectral side.**  The harmonic mass of the
designated range multiplies the fibre mean square; the cost is the rounding term of the bridge and
the Turán--Kubilius variance. -/
theorem sum_sq_fibreSum_moebius_le_omegaSpectral {x h : ℝ} (hx : 4 ≤ x) (hh0 : 0 ≤ h)
    (hhx : h ≤ Real.sqrt x) {z₀ z : ℕ} (hz : z₀ ≤ z) :
    (mertensS z - mertensS z₀) ^ 2
        * ∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, ((ArithmeticFunction.moebius b : ℤ) : ℝ)) ^ 2
      ≤ 16 * Real.sqrt x
            * (∫ w : ℝ, ‖logWindowKernel (fibreWidth x h) w‖ ^ 2
                * ‖omegaWeightedMoebiusPoly (primesRange z₀ z) (fibreIndex x h) w‖ ^ 2)
        + 204 * (((primesRange z₀ z).card : ℝ) + 1) ^ 2 * (Real.sqrt x + 1)
        + 2 * (h + 1) * (2 * h + 1)
            * (4 * (Real.sqrt x / 2 + h + 1) * mertensS z + 4 * ((Nat.primesLE z).card : ℝ)
              + 8 * ((Nat.primesLE z).card : ℝ) ^ 2) := by
  classical
  set P : Finset ℕ := primesRange z₀ z with hP
  set B : ℝ := ((P.card : ℝ) + 1) with hB
  have hB0 : (0 : ℝ) < B := by
    have : (0 : ℝ) ≤ (P.card : ℝ) := Nat.cast_nonneg _
    rw [hB]
    linarith
  set F : ℕ → ℝ := fun n =>
    ((ArithmeticFunction.moebius n : ℤ) : ℝ) * ((primeFactorsIn P n).card : ℝ) with hF
  have hFbd : ∀ n, |F n| ≤ B := by
    intro n
    rw [hF, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((primeFactorsIn P n).card : ℝ))]
    have h1 := abs_moebius_real_le_one n
    have h2 := card_primeFactorsIn_le P n
    have h3 : (0 : ℝ) ≤ ((primeFactorsIn P n).card : ℝ) := Nat.cast_nonneg _
    have h4 : (0 : ℝ) ≤ |((ArithmeticFunction.moebius n : ℤ) : ℝ)| := abs_nonneg _
    rw [hB]
    nlinarith [h1, h2, h3, h4]
  -- the Turán--Kubilius transfer
  have hTK := sum_sq_fibreSum_le_omegaWeighted
    (f := fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) abs_moebius_real_le_one hx hh0 hz
  -- the rescaled bridge
  have hbridge := sum_fibreSum_sq_le_integral_scaled (f := F) hB0 hFbd hx hh0 hhx
  -- Plancherel
  have hplanch : (∫ u : ℝ, ‖logWindowSum (fun n => ((F n : ℝ) : ℂ))
        (fibreIndex x h) (fibreWidth x h) u‖ ^ 2)
      = ∫ w : ℝ, ‖logWindowKernel (fibreWidth x h) w‖ ^ 2
          * ‖omegaWeightedMoebiusPoly P (fibreIndex x h) w‖ ^ 2 := by
    rw [integral_normSq_logWindowSum_eq _ _ (fibreWidth_nonneg hx hh0)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [hF, logPoly_omegaWeighted_eq]
  rw [hplanch] at hbridge
  have hsx : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hstep : 2 * ∑ a ∈ outerBlock x h, (∑ b ∈ innerFibre x h a, F b) ^ 2
      ≤ 16 * Real.sqrt x
            * (∫ w : ℝ, ‖logWindowKernel (fibreWidth x h) w‖ ^ 2
                * ‖omegaWeightedMoebiusPoly P (fibreIndex x h) w‖ ^ 2)
        + 204 * B ^ 2 * (Real.sqrt x + 1) := by
    linarith [hbridge]
  linarith [hTK, hstep]

/-! ## The gate, at the level of the limit -/

/-- The whole explicit cost of the weighted arrangement at one scale. -/
def omegaBudget (x h : ℝ) (z₀ z : ℕ) : ℝ :=
  16 * Real.sqrt x
      * (∫ w : ℝ, ‖logWindowKernel (fibreWidth x h) w‖ ^ 2
          * ‖omegaWeightedMoebiusPoly (primesRange z₀ z) (fibreIndex x h) w‖ ^ 2)
    + 204 * (((primesRange z₀ z).card : ℝ) + 1) ^ 2 * (Real.sqrt x + 1)
    + 2 * (h + 1) * (2 * h + 1)
        * (4 * (Real.sqrt x / 2 + h + 1) * mertensS z + 4 * ((Nat.primesLE z).card : ℝ)
          + 8 * ((Nat.primesLE z).card : ℝ) ^ 2)

/-- **The Route E gate on the weighted polynomial.**  If the explicit budget of the weighted
arrangement is `o` of the harmonic mass squared times the trivial size, the Möbius fibre mean square
vanishes. -/
theorem averagedMeanSquare_moebius_of_omegaBudget {hh : ℝ → ℝ} {zlo zhi : ℝ → ℕ}
    (hhx : ∀ᶠ x in atTop, hh x ≤ Real.sqrt x)
    (hh0 : ∀ᶠ x in atTop, 0 < hh x)
    (hz : ∀ᶠ x in atTop, zlo x ≤ zhi x)
    (hW : ∀ᶠ x in atTop, 0 < mertensS (zhi x) - mertensS (zlo x))
    (hlim : Tendsto (fun x => omegaBudget x (hh x) (zlo x) (zhi x)
        / ((mertensS (zhi x) - mertensS (zlo x)) ^ 2 * hh x ^ 2 * Real.sqrt x)) atTop (𝓝 0)) :
    AveragedMeanSquare (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) hh := by
  rw [AveragedMeanSquare]
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hhx, hh0, hz, hW, Filter.eventually_ge_atTop (4 : ℝ)] with x hx1 hx2 hx3 hx4 hx5
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hden : (0 : ℝ) < (mertensS (zhi x) - mertensS (zlo x)) ^ 2 * hh x ^ 2 * Real.sqrt x := by
    have : (0 : ℝ) < (mertensS (zhi x) - mertensS (zlo x)) ^ 2 := by positivity
    positivity
  have hnum0 : (0 : ℝ)
      ≤ ∑ a ∈ outerBlock x (hh x),
          (∑ b ∈ innerFibre x (hh x) a, ((ArithmeticFunction.moebius b : ℤ) : ℝ)) ^ 2 :=
    Finset.sum_nonneg fun a _ => sq_nonneg _
  have hkey := sum_sq_fibreSum_moebius_le_omegaSpectral hx5 hx2.le hx1 hx3
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [div_le_div_iff₀ (by positivity) hden]
  have hval : (∑ a ∈ outerBlock x (hh x),
        (∑ b ∈ innerFibre x (hh x) a, ((ArithmeticFunction.moebius b : ℤ) : ℝ)) ^ 2)
      * ((mertensS (zhi x) - mertensS (zlo x)) ^ 2 * hh x ^ 2 * Real.sqrt x)
      = ((mertensS (zhi x) - mertensS (zlo x)) ^ 2
          * ∑ a ∈ outerBlock x (hh x),
            (∑ b ∈ innerFibre x (hh x) a, ((ArithmeticFunction.moebius b : ℤ) : ℝ)) ^ 2)
        * (hh x ^ 2 * Real.sqrt x) := by ring
  rw [hval]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [omegaBudget]
  exact hkey

/-- **The Möbius capstone on the weighted polynomial.** -/
theorem averagedShortInterval_moebius_of_omegaBudget {hh : ℝ → ℝ} {zlo zhi : ℝ → ℕ}
    (hgrow : Tendsto hh atTop atTop)
    (hhx : ∀ᶠ x in atTop, hh x ≤ Real.sqrt x)
    (hz : ∀ᶠ x in atTop, zlo x ≤ zhi x)
    (hW : ∀ᶠ x in atTop, 0 < mertensS (zhi x) - mertensS (zlo x))
    (hlim : Tendsto (fun x => omegaBudget x (hh x) (zlo x) (zhi x)
        / ((mertensS (zhi x) - mertensS (zlo x)) ^ 2 * hh x ^ 2 * Real.sqrt x)) atTop (𝓝 0)) :
    AveragedShortInterval (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) hh :=
  averagedShortInterval_of_meanSquare hgrow
    (averagedMeanSquare_moebius_of_omegaBudget hhx
      (hgrow.eventually_gt_atTop 0) hz hW hlim)

end

end RHTower.Sieve
