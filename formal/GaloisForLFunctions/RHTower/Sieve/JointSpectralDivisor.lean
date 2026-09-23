import GaloisForLFunctions.RHTower.Sieve.JointBudgetMaster
import GaloisForLFunctions.RHTower.Sieve.JointLadderDefectDivisor

/-!
# The joint spectral reduction at the divisor bound

`Sieve/JointOmegaSpectral` pays the sup bound `(#P+1)(#Q+1)` for the joint weight in the fibre
bridge's rounding error `204·B²·(√x+1)`.  That is fatal once the long range is as high as §4 needs
it: `#Q ≍ exp((log x)^b)/(log x)^b`, so `B²/h² ≍ exp(2(log x)^b)/polylog → ∞` and the term does not
vanish.

The repair is the same divisor bound that fixed the short ladder's defect.  The fibre sums and the
window sums only ever touch indices in `[1, B₀]`, and there

```text
   |μ(n)·ω_P(n)·ω_Q(n)|  ≤  (log B₀/log R_P)·(log B₀/log R_Q) ,
```

which at `log R_P ≍ (log x)^{β/2}` and `log R_Q ≍ (log x)^a` is `≍ (log x)^{2−β/2−a}` — a *power of
the logarithm*.  This module carries the whole reduction with that bound as a parameter.
-/

namespace RHTower.Sieve

open Finset MeasureTheory Filter Topology

noncomputable section

/-- The joint weight, cut off outside the fibre index. -/
def jointOmegaWeightR (P Q : Finset ℕ) (N : ℕ) (n : ℕ) : ℝ :=
  if n ∈ Finset.Icc 1 N then jointOmegaWeight P Q n else 0

theorem jointOmegaWeightR_eq {P Q : Finset ℕ} {N n : ℕ} (hn : n ∈ Finset.Icc 1 N) :
    jointOmegaWeightR P Q N n = jointOmegaWeight P Q n := by
  rw [jointOmegaWeightR, if_pos hn]

/-- **The divisor bound for the joint weight.** -/
theorem abs_jointOmegaWeightR_le {P Q : Finset ℕ} {RP RQ : ℝ} (hRP : 1 < RP) (hRQ : 1 < RQ)
    (hPprime : ∀ p ∈ P, p.Prime) (hPge : ∀ p ∈ P, RP ≤ (p : ℝ))
    (hQprime : ∀ q ∈ Q, q.Prime) (hQge : ∀ q ∈ Q, RQ ≤ (q : ℝ)) (N n : ℕ) :
    |jointOmegaWeightR P Q N n|
      ≤ (Real.log N / Real.log RP) * (Real.log N / Real.log RQ) := by
  classical
  have hlogP : 0 < Real.log RP := Real.log_pos hRP
  have hlogQ : 0 < Real.log RQ := Real.log_pos hRQ
  have hPd : (0 : ℝ) ≤ Real.log N / Real.log RP :=
    div_nonneg (Real.log_natCast_nonneg N) hlogP.le
  have hQd : (0 : ℝ) ≤ Real.log N / Real.log RQ :=
    div_nonneg (Real.log_natCast_nonneg N) hlogQ.le
  rw [jointOmegaWeightR]
  by_cases hn : n ∈ Finset.Icc 1 N
  · rw [if_pos hn]
    rw [Finset.mem_Icc] at hn
    have hP := card_designatedPrimes_dvd_le hRP hPprime hPge hn.1 hn.2
    have hQ := card_designatedPrimes_dvd_le hRQ hQprime hQge hn.1 hn.2
    have hpfP : primeFactorsIn P n = P.filter (fun p => p ∣ n) := rfl
    have hpfQ : primeFactorsIn Q n = Q.filter (fun p => p ∣ n) := rfl
    have hP0 : (0 : ℝ) ≤ ((primeFactorsIn P n).card : ℝ) := Nat.cast_nonneg _
    have hQ0 : (0 : ℝ) ≤ ((primeFactorsIn Q n).card : ℝ) := Nat.cast_nonneg _
    have h1 := abs_moebius_real_le_one n
    rw [jointOmegaWeight, abs_mul, abs_mul, abs_of_nonneg hP0, abs_of_nonneg hQ0]
    rw [← hpfP] at hP
    rw [← hpfQ] at hQ
    have hprod : ((primeFactorsIn P n).card : ℝ) * ((primeFactorsIn Q n).card : ℝ)
        ≤ (Real.log N / Real.log RP) * (Real.log N / Real.log RQ) :=
      mul_le_mul hP hQ hQ0 hPd
    nlinarith [h1, hprod, mul_nonneg hP0 hQ0,
      abs_nonneg ((ArithmeticFunction.moebius n : ℤ) : ℝ)]
  · rw [if_neg hn, abs_zero]
    positivity

/-- The window sum is unchanged by the cut-off. -/
theorem logWindowSum_jointOmegaWeightR (P Q : Finset ℕ) (N : ℕ) (δ u : ℝ) :
    logWindowSum (fun n => ((jointOmegaWeightR P Q N n : ℝ) : ℂ)) (Finset.Icc 1 N) δ u
      = logWindowSum (fun n => ((jointOmegaWeight P Q n : ℝ) : ℂ)) (Finset.Icc 1 N) δ u := by
  rw [logWindowSum, logWindowSum]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [jointOmegaWeightR_eq hn]

/-- **The Möbius fibre mean square against the jointly weighted spectral side, at the divisor
bound.** -/
theorem sum_sq_fibreSum_moebius_le_jointSpectralD {x h : ℝ} (hx : 4 ≤ x) (hh0 : 0 ≤ h)
    (hhx : h ≤ Real.sqrt x) {P Q : Finset ℕ}
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (hPQ : Disjoint P Q)
    {Bd : ℝ} (hBd0 : 0 < Bd)
    (hBd : ∀ n, |jointOmegaWeightR P Q ⌊Real.sqrt x + h⌋₊ n| ≤ Bd) :
    (Joint.mass P * Joint.mass Q) ^ (2 : ℕ)
        * ∑ a ∈ outerBlock x h,
            (∑ b ∈ innerFibre x h a, ((ArithmeticFunction.moebius b : ℤ) : ℝ)) ^ (2 : ℕ)
      ≤ 16 * Real.sqrt x
            * (∫ w : ℝ, ‖logWindowKernel (fibreWidth x h) w‖ ^ (2 : ℕ)
                * ‖jointOmegaPoly P Q (fibreIndex x h) w‖ ^ (2 : ℕ))
        + 204 * Bd ^ (2 : ℕ) * (Real.sqrt x + 1)
        + 2 * (h + 1) * (2 * h + 1)
            * (((⌊Real.sqrt x + h⌋₊ : ℕ) : ℝ) * (Joint.mass P * Joint.mass Q)
                  * (Joint.mass P + Joint.mass Q + 1)
              + 2 * (Joint.mass P * Joint.mass Q) * (P.card : ℝ) * (Q.card : ℝ)) := by
  classical
  set N : ℕ := ⌊Real.sqrt x + h⌋₊ with hN
  have hTK := sum_sq_fibreSum_le_jointWeighted
    (f := fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) abs_moebius_real_le_one hx hh0
    hP hQ hPQ
  have hbridge := sum_fibreSum_sq_le_integral_scaled (f := jointOmegaWeightR P Q N) hBd0 hBd
    hx hh0 hhx
  have hplanch : (∫ u : ℝ, ‖logWindowSum (fun n => ((jointOmegaWeightR P Q N n : ℝ) : ℂ))
        (fibreIndex x h) (fibreWidth x h) u‖ ^ (2 : ℕ))
      = ∫ w : ℝ, ‖logWindowKernel (fibreWidth x h) w‖ ^ (2 : ℕ)
          * ‖jointOmegaPoly P Q (fibreIndex x h) w‖ ^ (2 : ℕ) := by
    have hidx : fibreIndex x h = Finset.Icc 1 N := rfl
    rw [hidx]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => by
      rw [logWindowSum_jointOmegaWeightR P Q N (fibreWidth x h) u])]
    rw [integral_normSq_logWindowSum_eq _ _ (fibreWidth_nonneg hx hh0)]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [logPoly_jointOmegaWeight_eq]
  rw [hplanch] at hbridge
  have hfib : ∀ a ∈ outerBlock x h,
      (∑ b ∈ innerFibre x h a, jointOmegaWeightR P Q N b)
        = ∑ b ∈ innerFibre x h a,
            ((ArithmeticFunction.moebius b : ℤ) : ℝ)
              * (((primeFactorsIn P b).card : ℝ) * ((primeFactorsIn Q b).card : ℝ)) := by
    intro a ha
    refine Finset.sum_congr rfl fun b hb => ?_
    have hbn : b ∈ Finset.Icc 1 N := innerFibre_subset_fibreIndex hx ha hb
    rw [jointOmegaWeightR_eq hbn, jointOmegaWeight]
  rw [Finset.sum_congr rfl fun a ha => by rw [hfib a ha]] at hbridge
  have hsx : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  simp only [Joint.mass]
  linarith [hTK, hbridge]

/-! ## The budget at the divisor bound -/

/-- The joint budget with the fibre bridge's rounding error carried by a parameter. -/
def jointOmegaBudgetD (x h : ℝ) (P Q : Finset ℕ) (Bd : ℝ) : ℝ :=
  16 * Real.sqrt x
      * (∫ w : ℝ, ‖logWindowKernel (fibreWidth x h) w‖ ^ (2 : ℕ)
          * ‖jointOmegaPoly P Q (fibreIndex x h) w‖ ^ (2 : ℕ))
    + 204 * Bd ^ (2 : ℕ) * (Real.sqrt x + 1)
    + 2 * (h + 1) * (2 * h + 1)
        * (((⌊Real.sqrt x + h⌋₊ : ℕ) : ℝ) * (Joint.mass P * Joint.mass Q)
              * (Joint.mass P + Joint.mass Q + 1)
          + 2 * (Joint.mass P * Joint.mass Q) * (P.card : ℝ) * (Q.card : ℝ))

/-- **The Route E gate at the divisor bound.** -/
theorem averagedMeanSquare_moebius_of_jointOmegaBudgetD {hh : ℝ → ℝ} {Pf Qf : ℝ → Finset ℕ}
    {Bdf : ℝ → ℝ}
    (hhx : ∀ᶠ x in atTop, hh x ≤ Real.sqrt x)
    (hh0 : ∀ᶠ x in atTop, 0 < hh x)
    (hP : ∀ᶠ x in atTop, ∀ p ∈ Pf x, p.Prime)
    (hQ : ∀ᶠ x in atTop, ∀ q ∈ Qf x, q.Prime)
    (hPQ : ∀ᶠ x in atTop, Disjoint (Pf x) (Qf x))
    (hW : ∀ᶠ x in atTop, 0 < Joint.mass (Pf x) * Joint.mass (Qf x))
    (hBd0 : ∀ᶠ x in atTop, 0 < Bdf x)
    (hBd : ∀ᶠ x in atTop,
      ∀ n, |jointOmegaWeightR (Pf x) (Qf x) ⌊Real.sqrt x + hh x⌋₊ n| ≤ Bdf x)
    (hlim : Tendsto (fun x => jointOmegaBudgetD x (hh x) (Pf x) (Qf x) (Bdf x)
        / ((Joint.mass (Pf x) * Joint.mass (Qf x)) ^ (2 : ℕ) * hh x ^ (2 : ℕ) * Real.sqrt x))
      atTop (𝓝 0)) :
    AveragedMeanSquare (fun n => ((ArithmeticFunction.moebius n : ℤ) : ℝ)) hh := by
  rw [AveragedMeanSquare]
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hhx, hh0, hP, hQ, hPQ, hW, hBd0, hBd, Filter.eventually_ge_atTop (4 : ℝ)]
    with x hx1 hx2 hxP hxQ hxPQ hxW hxB0 hxB hx5
  have hsx : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hden : (0 : ℝ)
      < (Joint.mass (Pf x) * Joint.mass (Qf x)) ^ (2 : ℕ) * hh x ^ (2 : ℕ) * Real.sqrt x := by
    have h1 : (0 : ℝ) < (Joint.mass (Pf x) * Joint.mass (Qf x)) ^ (2 : ℕ) := by positivity
    positivity
  have hnum0 : (0 : ℝ)
      ≤ ∑ a ∈ outerBlock x (hh x),
          (∑ b ∈ innerFibre x (hh x) a, ((ArithmeticFunction.moebius b : ℤ) : ℝ)) ^ (2 : ℕ) :=
    Finset.sum_nonneg fun a _ => sq_nonneg _
  have hkey := sum_sq_fibreSum_moebius_le_jointSpectralD hx5 hx2.le hx1 hxP hxQ hxPQ hxB0 hxB
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [div_le_div_iff₀ (by positivity) hden]
  have hval : (∑ a ∈ outerBlock x (hh x),
        (∑ b ∈ innerFibre x (hh x) a, ((ArithmeticFunction.moebius b : ℤ) : ℝ)) ^ (2 : ℕ))
      * ((Joint.mass (Pf x) * Joint.mass (Qf x)) ^ (2 : ℕ) * hh x ^ (2 : ℕ) * Real.sqrt x)
      = ((Joint.mass (Pf x) * Joint.mass (Qf x)) ^ (2 : ℕ)
          * ∑ a ∈ outerBlock x (hh x),
            (∑ b ∈ innerFibre x (hh x) a, ((ArithmeticFunction.moebius b : ℤ) : ℝ)) ^ (2 : ℕ))
        * (hh x ^ (2 : ℕ) * Real.sqrt x) := by ring
  rw [hval]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  rw [jointOmegaBudgetD]
  exact hkey

/-- **The joint budget at the divisor bound, with the spectral part replaced.** -/
theorem jointOmegaBudgetD_le {x h : ℝ} {P Q : Finset ℕ} {Bd : ℝ}
    {δ Wc T₀ β₀ : ℝ} (hδ : δ = fibreWidth x h) (hδ0 : 0 < δ)
    (hWc : 1 ≤ Wc) (hT₀ : 0 < T₀) (hδWc : δ * Wc ≤ 1)
    (hbound : (∫ w in Set.Icc (-T₀) T₀,
        ‖jointOmegaPoly P Q (fibreIndex x h) w‖ ^ (2 : ℕ)) ≤ β₀) :
    jointOmegaBudgetD x h P Q Bd
      ≤ 16 * Real.sqrt x
          * (3 * ((5 * Real.pi / 2
                + 5 * Real.exp 1 / 2 * ((⌊Real.sqrt x + h⌋₊ : ℕ) : ℝ) / T₀)
              * ∑ n ∈ fibreIndex x h, ‖jointOmegaCoeff P Q n‖ ^ (2 : ℕ)) / Wc
            + 3 * β₀ / Wc ^ (2 : ℕ))
        + 204 * Bd ^ (2 : ℕ) * (Real.sqrt x + 1)
        + 2 * (h + 1) * (2 * h + 1)
            * (((⌊Real.sqrt x + h⌋₊ : ℕ) : ℝ) * (Joint.mass P * Joint.mass Q)
                  * (Joint.mass P + Joint.mass Q + 1)
              + 2 * (Joint.mass P * Joint.mass Q) * (P.card : ℝ) * (Q.card : ℝ)) := by
  classical
  have hidx : fibreIndex x h = Finset.Icc 1 ⌊Real.sqrt x + h⌋₊ := rfl
  have hbound' : (∫ w in Set.Icc (-T₀) T₀,
      ‖jointOmegaPoly P Q (Finset.Icc 1 ⌊Real.sqrt x + h⌋₊) w‖ ^ (2 : ℕ)) ≤ β₀ := by
    rw [← hidx]; exact hbound
  have hspec := integral_kernel_normSq_jointOmega_le' (P := P) (Q := Q) (A₀ := 1)
    (B₀ := ⌊Real.sqrt x + h⌋₊) (by omega) (δ := δ) hδ0 hWc hT₀ hδWc hbound'
  rw [← hidx] at hspec
  have hsx : (0 : ℝ) ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hmul := mul_le_mul_of_nonneg_left hspec (by positivity : (0 : ℝ) ≤ 16 * Real.sqrt x)
  rw [jointOmegaBudgetD, ← hδ]
  have hcast : (5 * Real.pi / 2
        + 5 * Real.exp 1 / 2 * (((⌊Real.sqrt x + h⌋₊ : ℕ) : ℝ) / T₀))
      = 5 * Real.pi / 2 + 5 * Real.exp 1 / 2 * ((⌊Real.sqrt x + h⌋₊ : ℕ) : ℝ) / T₀ := by
    ring
  rw [hcast] at hmul
  linarith [hmul]

end

end RHTower.Sieve
