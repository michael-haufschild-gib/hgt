import GaloisForLFunctions.RHTower.Sieve.JointFibreTransfer
import GaloisForLFunctions.RHTower.Sieve.ScaledFibreBridge
import GaloisForLFunctions.RHTower.Sieve.OmegaWeightedFactorisation
import GaloisForLFunctions.RHTower.Sieve.LogWindowPlancherel
import GaloisForLFunctions.RHTower.Sieve.PairFibreMeanSquare

/-!
# The Möbius fibre mean square against the jointly weighted spectral side

The §4 arrangement of Soundararajan's exposé weights the Möbius function by `ω_P(n)·ω_Q(n)`, the
product of the designated-prime counts over two disjoint ranges.  This module carries that weight
through the same three steps as the single-weight `Sieve/OmegaSpectralFibre`: the joint
Turán–Kubilius transfer, the rescaled fibre bridge, and Plancherel.

Everything below is an inequality between explicit quantities; no asymptotic notation.
-/

namespace RHTower.Sieve

open Finset MeasureTheory Filter Topology
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- The jointly weighted Möbius polynomial. -/
def jointOmegaPoly (P Q S : Finset ℕ) (w : ℝ) : ℂ :=
  ∑ n ∈ S, (((primeFactorsIn P n).card : ℂ) * ((primeFactorsIn Q n).card : ℂ))
    * moebiusPhase w n

/-- The joint coefficient sequence, as a real function. -/
def jointOmegaWeight (P Q : Finset ℕ) (n : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius n : ℤ) : ℝ)
    * (((primeFactorsIn P n).card : ℝ) * ((primeFactorsIn Q n).card : ℝ))

/-- The jointly weighted polynomial is the Gallagher polynomial of the joint coefficients. -/
theorem logPoly_jointOmegaWeight_eq (P Q S : Finset ℕ) (w : ℝ) :
    logPoly (fun n => ((jointOmegaWeight P Q n : ℝ) : ℂ)) S w = jointOmegaPoly P Q S w := by
  rw [logPoly, jointOmegaPoly]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [jointOmegaWeight, moebiusPhase, unitLogPhase]
  push_cast
  ring

/-- The designated prime count never exceeds the size of the designated set. -/
theorem card_primeFactorsIn_le_card (P : Finset ℕ) (n : ℕ) :
    ((primeFactorsIn P n).card : ℝ) ≤ (P.card : ℝ) := by
  have := Finset.card_le_card (Finset.filter_subset (fun p => p ∣ n) P)
  exact_mod_cast this

/-- The joint weight is bounded by the product of the two range sizes. -/
theorem abs_jointOmegaWeight_le (P Q : Finset ℕ) (n : ℕ) :
    |jointOmegaWeight P Q n| ≤ ((P.card : ℝ) + 1) * ((Q.card : ℝ) + 1) := by
  have h1 := abs_moebius_real_le_one n
  have h2 := card_primeFactorsIn_le_card P n
  have h3 := card_primeFactorsIn_le_card Q n
  have h4 : (0 : ℝ) ≤ ((primeFactorsIn P n).card : ℝ) := Nat.cast_nonneg _
  have h5 : (0 : ℝ) ≤ ((primeFactorsIn Q n).card : ℝ) := Nat.cast_nonneg _
  have h6 : (0 : ℝ) ≤ |((ArithmeticFunction.moebius n : ℤ) : ℝ)| := abs_nonneg _
  have hPc : (0 : ℝ) ≤ (P.card : ℝ) := Nat.cast_nonneg _
  have hQc : (0 : ℝ) ≤ (Q.card : ℝ) := Nat.cast_nonneg _
  have hprod : ((primeFactorsIn P n).card : ℝ) * ((primeFactorsIn Q n).card : ℝ)
      ≤ (P.card : ℝ) * (Q.card : ℝ) := mul_le_mul h2 h3 h5 hPc
  have hpp : (0 : ℝ) ≤ ((primeFactorsIn P n).card : ℝ) * ((primeFactorsIn Q n).card : ℝ) :=
    mul_nonneg h4 h5
  rw [jointOmegaWeight, abs_mul, abs_mul, abs_of_nonneg h4, abs_of_nonneg h5]
  calc |((ArithmeticFunction.moebius n : ℤ) : ℝ)|
        * (((primeFactorsIn P n).card : ℝ) * ((primeFactorsIn Q n).card : ℝ))
      ≤ 1 * (((primeFactorsIn P n).card : ℝ) * ((primeFactorsIn Q n).card : ℝ)) :=
        mul_le_mul_of_nonneg_right h1 hpp
    _ ≤ 1 * ((P.card : ℝ) * (Q.card : ℝ)) := by linarith
    _ ≤ ((P.card : ℝ) + 1) * ((Q.card : ℝ) + 1) := by nlinarith [hPc, hQc]

/-- **The Möbius fibre mean square against the jointly weighted spectral side.** -/
theorem sum_sq_fibreSum_moebius_le_jointSpectral {x h : ℝ} (hx : 4 ≤ x) (hh0 : 0 ≤ h)
    (hhx : h ≤ Real.sqrt x) {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (hPQ : Disjoint P Q) :
    ((∑ p ∈ P, (1 : ℝ) / (p : ℝ)) * (∑ q ∈ Q, (1 : ℝ) / (q : ℝ))) ^ 2
        * ∑ a ∈ outerBlock x h,
            (∑ b ∈ innerFibre x h a, ((ArithmeticFunction.moebius b : ℤ) : ℝ)) ^ 2
      ≤ 16 * Real.sqrt x
            * (∫ w : ℝ, ‖logWindowKernel (fibreWidth x h) w‖ ^ 2
                * ‖jointOmegaPoly P Q (fibreIndex x h) w‖ ^ 2)
        + 204 * (((P.card : ℝ) + 1) * ((Q.card : ℝ) + 1)) ^ 2 * (Real.sqrt x + 1)
        + 2 * (h + 1) * (2 * h + 1)
            * (((⌊Real.sqrt x + h⌋₊ : ℕ) : ℝ)
                  * ((∑ p ∈ P, (1 : ℝ) / (p : ℝ)) * (∑ q ∈ Q, (1 : ℝ) / (q : ℝ)))
                  * ((∑ p ∈ P, (1 : ℝ) / (p : ℝ)) + (∑ q ∈ Q, (1 : ℝ) / (q : ℝ)) + 1)
              + 2 * ((∑ p ∈ P, (1 : ℝ) / (p : ℝ)) * (∑ q ∈ Q, (1 : ℝ) / (q : ℝ)))
                  * (P.card : ℝ) * (Q.card : ℝ)) := by
  classical
  set B : ℝ := ((P.card : ℝ) + 1) * ((Q.card : ℝ) + 1) with hB
  have hB0 : (0 : ℝ) < B := by
    have h1 : (0 : ℝ) ≤ (P.card : ℝ) := Nat.cast_nonneg _
    have h2 : (0 : ℝ) ≤ (Q.card : ℝ) := Nat.cast_nonneg _
    rw [hB]
    positivity
  have hTK := sum_sq_fibreSum_le_jointWeighted
    (f := fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) abs_moebius_real_le_one hx hh0
    hP hQ hPQ
  have hbridge := sum_fibreSum_sq_le_integral_scaled (f := jointOmegaWeight P Q) hB0
    (abs_jointOmegaWeight_le P Q) hx hh0 hhx
  have hplanch : (∫ u : ℝ, ‖logWindowSum (fun n => ((jointOmegaWeight P Q n : ℝ) : ℂ))
        (fibreIndex x h) (fibreWidth x h) u‖ ^ 2)
      = ∫ w : ℝ, ‖logWindowKernel (fibreWidth x h) w‖ ^ 2
          * ‖jointOmegaPoly P Q (fibreIndex x h) w‖ ^ 2 := by
    rw [integral_normSq_logWindowSum_eq _ _ (fibreWidth_nonneg hx hh0)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [logPoly_jointOmegaWeight_eq]
  rw [hplanch] at hbridge
  have hsx : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  simp only [jointOmegaWeight] at hbridge
  linarith [hTK, hbridge]


/-! ## The gate, at the level of the limit -/

namespace Joint

open Filter Topology MeasureTheory

/-- The harmonic mass of a finite prime set. -/
def mass (P : Finset ℕ) : ℝ := ∑ p ∈ P, (1 : ℝ) / (p : ℝ)

end Joint

/-- The whole explicit cost of the jointly weighted arrangement at one scale. -/
def jointOmegaBudget (x h : ℝ) (P Q : Finset ℕ) : ℝ :=
  16 * Real.sqrt x
      * (∫ w : ℝ, ‖logWindowKernel (fibreWidth x h) w‖ ^ 2
          * ‖jointOmegaPoly P Q (fibreIndex x h) w‖ ^ 2)
    + 204 * (((P.card : ℝ) + 1) * ((Q.card : ℝ) + 1)) ^ 2 * (Real.sqrt x + 1)
    + 2 * (h + 1) * (2 * h + 1)
        * (((⌊Real.sqrt x + h⌋₊ : ℕ) : ℝ) * (Joint.mass P * Joint.mass Q)
              * (Joint.mass P + Joint.mass Q + 1)
          + 2 * (Joint.mass P * Joint.mass Q) * (P.card : ℝ) * (Q.card : ℝ))

/-- **The Route E gate on the jointly weighted polynomial.** -/
theorem averagedMeanSquare_moebius_of_jointOmegaBudget {hh : ℝ → ℝ} {Pf Qf : ℝ → Finset ℕ}
    (hhx : ∀ᶠ x in atTop, hh x ≤ Real.sqrt x)
    (hh0 : ∀ᶠ x in atTop, 0 < hh x)
    (hP : ∀ᶠ x in atTop, ∀ p ∈ Pf x, p.Prime)
    (hQ : ∀ᶠ x in atTop, ∀ q ∈ Qf x, q.Prime)
    (hPQ : ∀ᶠ x in atTop, Disjoint (Pf x) (Qf x))
    (hW : ∀ᶠ x in atTop, 0 < Joint.mass (Pf x) * Joint.mass (Qf x))
    (hlim : Tendsto (fun x => jointOmegaBudget x (hh x) (Pf x) (Qf x)
        / ((Joint.mass (Pf x) * Joint.mass (Qf x)) ^ 2 * hh x ^ 2 * Real.sqrt x))
      atTop (𝓝 0)) :
    AveragedMeanSquare (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) hh := by
  rw [AveragedMeanSquare]
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hhx, hh0, hP, hQ, hPQ, hW, Filter.eventually_ge_atTop (4 : ℝ)]
    with x hx1 hx2 hxP hxQ hxPQ hxW hx5
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hden : (0 : ℝ)
      < (Joint.mass (Pf x) * Joint.mass (Qf x)) ^ 2 * hh x ^ 2 * Real.sqrt x := by
    have h1 : (0 : ℝ) < (Joint.mass (Pf x) * Joint.mass (Qf x)) ^ 2 := by positivity
    positivity
  have hnum0 : (0 : ℝ)
      ≤ ∑ a ∈ outerBlock x (hh x),
          (∑ b ∈ innerFibre x (hh x) a, ((ArithmeticFunction.moebius b : ℤ) : ℝ)) ^ 2 :=
    Finset.sum_nonneg fun a _ => sq_nonneg _
  have hkey := sum_sq_fibreSum_moebius_le_jointSpectral hx5 hx2.le hx1 hxP hxQ hxPQ
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [div_le_div_iff₀ (by positivity) hden]
  have hval : (∑ a ∈ outerBlock x (hh x),
        (∑ b ∈ innerFibre x (hh x) a, ((ArithmeticFunction.moebius b : ℤ) : ℝ)) ^ 2)
      * ((Joint.mass (Pf x) * Joint.mass (Qf x)) ^ 2 * hh x ^ 2 * Real.sqrt x)
      = ((Joint.mass (Pf x) * Joint.mass (Qf x)) ^ 2
          * ∑ a ∈ outerBlock x (hh x),
            (∑ b ∈ innerFibre x (hh x) a, ((ArithmeticFunction.moebius b : ℤ) : ℝ)) ^ 2)
        * (hh x ^ 2 * Real.sqrt x) := by ring
  rw [hval]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [jointOmegaBudget, Joint.mass, Joint.mass]
  exact hkey

end

end RHTower.Sieve
