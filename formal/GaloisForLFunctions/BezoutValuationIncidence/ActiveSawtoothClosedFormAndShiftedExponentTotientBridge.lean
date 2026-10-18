import GaloisForLFunctions.BezoutValuationIncidence.SawtoothMidpointAnnihilationAndActiveDivisorSquareInvariance

/-!
# Pillar XVIII: Closed-Form Active Sawtooth Evaluation & Shifted-Exponent Totient Bridge (`ε ↦ 1 + ε`)

In Pillar XVII (`SawtoothMidpointAnnihilationAndActiveDivisorSquareInvariance`), we partitioned
`weightedCenteredSawtoothSum N c k` across each step `n ↦ n + 1` into its **active divisor component**
`activeCenteredSawtoothSum N c (n + 1) k` (`d ∣ (n + 1)`) and **inactive drifting component**
`inactiveCenteredSawtoothSum N c (n + 1) k` (`d ∤ (n + 1)`), proving that the active component flips
sign (`A(n + 1) = -A(n)`) and its square cancels identically in `W(n + 1)² - W(n)²`.

In this eighteenth pillar of **Bézout–Valuation Incidence Mechanics**, we evaluate both the active
component at `n` and `n + 1` and the inactive forward drift across `n ↦ n + 1` in **exact closed
form** in terms of the BVI sieve operator `sieveSeq` and the **shifted-exponent power-damped weight**
`pmPowerDampedRealWeight (1 + ε)` (which lives at exponent `1 + ε > 1` in the absolutely convergent
Euler product region, reducing at `ε = 0` to the Euler totient ratio `φ(m) / m = ∏_{p ∣ m} (1 - p⁻¹)`).

## Core Main Theorems (100% Unconditional)

1. **Exact Sieve Closed Form for `activeCenteredSawtoothSum` & `inactiveCenteredSawtoothSum` Drift
   (`activeCenteredSawtoothSum_at_pred_eq_half_sieveSeq_sub`,
   `activeCenteredSawtoothSum_at_self_eq_half_sieveSeq_sub`,
   `inactiveCenteredSawtoothSum_succ_sub_eq`)**:
   For **every** cutoff `N : ℕ`, weight `c : ℕ → ℝ`, and `n : ℕ`:
   - At the predecessor `n`:
     $$\operatorname{activeCenteredSawtoothSum}\,N\,c\,(n + 1)\,n =
       -\frac{1}{2}\left(\operatorname{sieveSeq}\,N\,c\,(n + 1) -
         \operatorname{sieveSeq}\,N\,\left(\text{fun } d \Rightarrow \frac{c(d)}{d}\right)\,(n + 1)\right).$$
   - At the step `n + 1`:
     $$\operatorname{activeCenteredSawtoothSum}\,N\,c\,(n + 1)\,(n + 1) =
       +\frac{1}{2}\left(\operatorname{sieveSeq}\,N\,c\,(n + 1) -
         \operatorname{sieveSeq}\,N\,\left(\text{fun } d \Rightarrow \frac{c(d)}{d}\right)\,(n + 1)\right).$$
   - Across `n ↦ n + 1`, the inactive component drifts purely by the harmonic complement:
     $$\operatorname{inactiveCenteredSawtoothSum}\,N\,c\,(n + 1)\,(n + 1) -
       \operatorname{inactiveCenteredSawtoothSum}\,N\,c\,(n + 1)\,n =
       \operatorname{sieveSeq}\,N\,\left(\text{fun } d \Rightarrow \frac{c(d)}{d}\right)\,(n + 1) -
       \operatorname{selbergMultiplesCoord}\,N\,c\,1.$$

2. **Shifted-Exponent Totient Law (`pmPowerDampedRealWeight_div_eq_add_one`) & Sub-Horizon Closed Form
   (`activeCenteredSawtoothSum_pmPowerDampedRealWeight_pred_eq`,
   `activeCenteredSawtoothSum_pmPowerDampedRealWeight_self_eq`,
   `inactiveCenteredSawtoothSum_pmPowerDampedRealWeight_succ_sub_eq`)**:
   For every `ε : ℝ` and `d : ℕ`:
   $$\frac{\operatorname{pmPowerDampedRealWeight}\,\varepsilon\,d}{d} =
     \operatorname{pmPowerDampedRealWeight}\,(1 + \varepsilon)\,d.$$
   Consequently, for every sub-horizon step `n + 1 ≤ N`:
   - $\operatorname{activeCenteredSawtoothSum}\,N\,c_\varepsilon\,(n + 1)\,n =
       -\frac{1}{2}\bigl(\tau_\varepsilon(n + 1) - \tau_{1+\varepsilon}(n + 1)\bigr)$,
   - $\operatorname{activeCenteredSawtoothSum}\,N\,c_\varepsilon\,(n + 1)\,(n + 1) =
       +\frac{1}{2}\bigl(\tau_\varepsilon(n + 1) - \tau_{1+\varepsilon}(n + 1)\bigr)$,
   - $\operatorname{inactiveCenteredSawtoothSum}\,N\,c_\varepsilon\,(n + 1)\,(n + 1) -
       \operatorname{inactiveCenteredSawtoothSum}\,N\,c_\varepsilon\,(n + 1)\,n =
       \tau_{1+\varepsilon}(n + 1) - \operatorname{selbergMultiplesCoord}\,N\,c_\varepsilon\,1$.

3. **Zero-Damping Euler Totient Ratio Evaluation (`pmPowerDampedDivisorCoeff_one_prime_pow`,
   `pmPowerDampedDivisorCoeff_one_four_and_six`)**:
   At exponent `1` (`ε = 0` in `1 + ε`), `pmPowerDampedDivisorCoeff 1 m = ∏_{p ∈ m.primeFactors} (1 - 1 / p)`
   is the exact Euler totient ratio `φ(m) / m`, satisfying `τ₁(p^k) = 1 - 1/p`, `τ₁(4) = 1/2`,
   `τ₁(6) = 1/3`, and `τ₁(4) - τ₁(6) = 1/6`.
-/

open Complex MeasureTheory Set Filter Topology Finset ArithmeticFunction
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.NymanMellin RHTower RHTower.Sieve
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ## §1. Exact Sieve Closed Form for `activeCenteredSawtoothSum` & `inactiveCenteredSawtoothSum` -/

/-- **Closed-Form Sieve Evaluation of `activeCenteredSawtoothSum` at Predecessor `n`
(`activeCenteredSawtoothSum_at_pred_eq_half_sieveSeq_sub`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `n : ℕ`:
`activeCenteredSawtoothSum N c (n + 1) n = -(1 / 2) * (sieveSeq N c (n + 1) - sieveSeq N (fun d => c d / d) (n + 1))`. -/
theorem activeCenteredSawtoothSum_at_pred_eq_half_sieveSeq_sub
    (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    activeCenteredSawtoothSum N c (n + 1) n =
      -(1 / 2 : ℝ) *
        (sieveSeq N c (n + 1) - sieveSeq N (fun d => c d / (d : ℝ)) (n + 1)) := by
  unfold activeCenteredSawtoothSum sieveSeq
  have hterm : ∀ d ∈ (Finset.Icc 1 N).filter (fun d => d ∣ (n + 1)),
      c d * centeredDiscreteSawtooth d n =
        (1 / 2 : ℝ) * (c d - c d / (d : ℝ)) := by
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_Icc] at hd
    have hd_pos : 0 < d := hd.1.1
    have hdR : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd_pos.ne'
    rw [centeredDiscreteSawtooth_of_dvd_succ hd_pos hd.2]
    field_simp [hdR]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_sub_distrib]
  ring

/-- **Closed-Form Sieve Evaluation of `activeCenteredSawtoothSum` at Step `n + 1`
(`activeCenteredSawtoothSum_at_self_eq_half_sieveSeq_sub`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `n : ℕ`:
`activeCenteredSawtoothSum N c (n + 1) (n + 1) = (1 / 2) * (sieveSeq N c (n + 1) - sieveSeq N (fun d => c d / d) (n + 1))`. -/
theorem activeCenteredSawtoothSum_at_self_eq_half_sieveSeq_sub
    (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    activeCenteredSawtoothSum N c (n + 1) (n + 1) =
      (1 / 2 : ℝ) *
        (sieveSeq N c (n + 1) - sieveSeq N (fun d => c d / (d : ℝ)) (n + 1)) := by
  rw [activeCenteredSawtoothSum_succ_eq_neg,
    activeCenteredSawtoothSum_at_pred_eq_half_sieveSeq_sub]
  ring

/-- **Exact Forward Drift of `inactiveCenteredSawtoothSum` Across `n ↦ n + 1`
(`inactiveCenteredSawtoothSum_succ_sub_eq`):**
For every `N : ℕ`, `c : ℕ → ℝ`, and `n : ℕ`:
`inactiveCenteredSawtoothSum N c (n + 1) (n + 1) - inactiveCenteredSawtoothSum N c (n + 1) n = sieveSeq N (fun d => c d / d) (n + 1) - selbergMultiplesCoord N c 1`. -/
theorem inactiveCenteredSawtoothSum_succ_sub_eq (N : ℕ) (c : ℕ → ℝ) (n : ℕ) :
    inactiveCenteredSawtoothSum N c (n + 1) (n + 1) -
      inactiveCenteredSawtoothSum N c (n + 1) n =
      sieveSeq N (fun d => c d / (d : ℝ)) (n + 1) -
        selbergMultiplesCoord N c 1 := by
  have h1 := weightedCenteredSawtoothSum_eq_active_add_inactive N c (n + 1) n
  have h2 := weightedCenteredSawtoothSum_eq_active_add_inactive N c (n + 1) (n + 1)
  have hw := weightedCenteredSawtoothSum_succ_sub_eq N c n
  have ha1 := activeCenteredSawtoothSum_at_pred_eq_half_sieveSeq_sub N c n
  have ha2 := activeCenteredSawtoothSum_at_self_eq_half_sieveSeq_sub N c n
  linarith

/-! ## §2. Shifted-Exponent Totient Law (`ε ↦ 1 + ε`) & Sub-Horizon Closed Forms -/

/-- **Shifted-Exponent Weight Identity (`pmPowerDampedRealWeight_div_eq_add_one`):**
For every `ε : ℝ` and `d : ℕ`, dividing `pmPowerDampedRealWeight ε d` by `d` shifts the damping
exponent from `ε` to `1 + ε`:
`pmPowerDampedRealWeight ε d / d = pmPowerDampedRealWeight (1 + ε) d`. -/
theorem pmPowerDampedRealWeight_div_eq_add_one (ε : ℝ) (d : ℕ) :
    pmPowerDampedRealWeight ε d / (d : ℝ) =
      pmPowerDampedRealWeight (1 + ε) d := by
  by_cases hd : d = 0
  · subst hd
    unfold pmPowerDampedRealWeight moebiusReal
    simp
  · have hd_pos : (0 : ℝ) < (d : ℝ) := by positivity
    unfold pmPowerDampedRealWeight
    rw [mul_div_assoc, ← Real.rpow_sub_one hd_pos.ne']
    congr 2
    ring

/-- For every `ε : ℝ` and `1 ≤ m ≤ N`:
`sieveSeq N (fun d => pmPowerDampedRealWeight ε d / d) m = pmPowerDampedDivisorCoeff (1 + ε) m`. -/
theorem sieveSeq_pmPowerDampedRealWeight_div_eq_divisorCoeff_add_one
    (ε : ℝ) {N m : ℕ} (hm1 : 1 ≤ m) (hmN : m ≤ N) :
    sieveSeq N (fun d => pmPowerDampedRealWeight ε d / (d : ℝ)) m =
      pmPowerDampedDivisorCoeff (1 + ε) m := by
  have hfun : (fun d : ℕ => pmPowerDampedRealWeight ε d / (d : ℝ)) =
      pmPowerDampedRealWeight (1 + ε) := by
    ext d
    exact pmPowerDampedRealWeight_div_eq_add_one ε d
  rw [hfun]
  exact sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff hm1 hmN

/-- **Sub-Horizon Closed Form for `activeCenteredSawtoothSum` at Predecessor `n`
(`activeCenteredSawtoothSum_pmPowerDampedRealWeight_pred_eq`):**
For every `ε : ℝ` and `n + 1 ≤ N`:
`activeCenteredSawtoothSum N (pmPowerDampedRealWeight ε) (n + 1) n = -(1 / 2) * (pmPowerDampedDivisorCoeff ε (n + 1) - pmPowerDampedDivisorCoeff (1 + ε) (n + 1))`. -/
theorem activeCenteredSawtoothSum_pmPowerDampedRealWeight_pred_eq
    (ε : ℝ) {N n : ℕ} (hnN : n + 1 ≤ N) :
    activeCenteredSawtoothSum N (pmPowerDampedRealWeight ε) (n + 1) n =
      -(1 / 2 : ℝ) *
        (pmPowerDampedDivisorCoeff ε (n + 1) -
          pmPowerDampedDivisorCoeff (1 + ε) (n + 1)) := by
  rw [activeCenteredSawtoothSum_at_pred_eq_half_sieveSeq_sub,
    sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff (by omega : 1 ≤ n + 1) hnN,
    sieveSeq_pmPowerDampedRealWeight_div_eq_divisorCoeff_add_one ε (by omega : 1 ≤ n + 1) hnN]

/-- **Sub-Horizon Closed Form for `activeCenteredSawtoothSum` at Step `n + 1`
(`activeCenteredSawtoothSum_pmPowerDampedRealWeight_self_eq`):**
For every `ε : ℝ` and `n + 1 ≤ N`:
`activeCenteredSawtoothSum N (pmPowerDampedRealWeight ε) (n + 1) (n + 1) = (1 / 2) * (pmPowerDampedDivisorCoeff ε (n + 1) - pmPowerDampedDivisorCoeff (1 + ε) (n + 1))`. -/
theorem activeCenteredSawtoothSum_pmPowerDampedRealWeight_self_eq
    (ε : ℝ) {N n : ℕ} (hnN : n + 1 ≤ N) :
    activeCenteredSawtoothSum N (pmPowerDampedRealWeight ε) (n + 1) (n + 1) =
      (1 / 2 : ℝ) *
        (pmPowerDampedDivisorCoeff ε (n + 1) -
          pmPowerDampedDivisorCoeff (1 + ε) (n + 1)) := by
  rw [activeCenteredSawtoothSum_at_self_eq_half_sieveSeq_sub,
    sieveSeq_pmPowerDampedRealWeight_eq_pmPowerDampedDivisorCoeff (by omega : 1 ≤ n + 1) hnN,
    sieveSeq_pmPowerDampedRealWeight_div_eq_divisorCoeff_add_one ε (by omega : 1 ≤ n + 1) hnN]

/-- **Sub-Horizon Closed Form for the Inactive Sawtooth Drift
(`inactiveCenteredSawtoothSum_pmPowerDampedRealWeight_succ_sub_eq`):**
For every `ε : ℝ` and `n + 1 ≤ N`:
`inactiveCenteredSawtoothSum N (pmPowerDampedRealWeight ε) (n + 1) (n + 1) - inactiveCenteredSawtoothSum N (pmPowerDampedRealWeight ε) (n + 1) n = pmPowerDampedDivisorCoeff (1 + ε) (n + 1) - selbergMultiplesCoord N (pmPowerDampedRealWeight ε) 1`. -/
theorem inactiveCenteredSawtoothSum_pmPowerDampedRealWeight_succ_sub_eq
    (ε : ℝ) {N n : ℕ} (hnN : n + 1 ≤ N) :
    inactiveCenteredSawtoothSum N (pmPowerDampedRealWeight ε) (n + 1) (n + 1) -
      inactiveCenteredSawtoothSum N (pmPowerDampedRealWeight ε) (n + 1) n =
      pmPowerDampedDivisorCoeff (1 + ε) (n + 1) -
        selbergMultiplesCoord N (pmPowerDampedRealWeight ε) 1 := by
  rw [inactiveCenteredSawtoothSum_succ_sub_eq,
    sieveSeq_pmPowerDampedRealWeight_div_eq_divisorCoeff_add_one ε (by omega : 1 ≤ n + 1) hnN]

/-! ## §3. Euler Totient Ratio Evaluation at Exponent `1` (`ε = 0` in `1 + ε`) -/

/-- At exponent `1`, `pmPowerDampedDivisorCoeff 1 (p ^ k) = 1 - 1 / p` for every prime power `p ^ k`
(`k ≠ 0`). -/
theorem pmPowerDampedDivisorCoeff_one_prime_pow {p k : ℕ} (hp : Nat.Prime p) (hk : k ≠ 0) :
    pmPowerDampedDivisorCoeff 1 (p ^ k) = 1 - 1 / (p : ℝ) := by
  rw [pmPowerDampedDivisorCoeff_prime_pow 1 hp hk, Real.rpow_neg_one, one_div]

/-- **Wall 11 Euler Totient Ratio Evaluation at `4 = 2²` vs. `6 = 2 · 3`
(`pmPowerDampedDivisorCoeff_one_four_and_six`):**
At exponent `1`:
1. `pmPowerDampedDivisorCoeff 1 4 = 1 / 2 = φ(4) / 4`,
2. `pmPowerDampedDivisorCoeff 1 6 = 1 / 3 = φ(6) / 6`,
3. `pmPowerDampedDivisorCoeff 1 4 - pmPowerDampedDivisorCoeff 1 6 = 1 / 6`. -/
theorem pmPowerDampedDivisorCoeff_one_four_and_six :
    pmPowerDampedDivisorCoeff 1 4 = 1 / 2 ∧
    pmPowerDampedDivisorCoeff 1 6 = 1 / 3 ∧
    pmPowerDampedDivisorCoeff 1 4 - pmPowerDampedDivisorCoeff 1 6 = 1 / 6 := by
  obtain ⟨h4, h6, _⟩ := pmPowerDampedDivisorCoeff_four_and_six 1
  rw [Real.rpow_neg_one] at h4 h6
  rw [Real.rpow_neg_one] at h6
  refine ⟨by linarith, by linarith, by linarith⟩

end
end GaloisForLFunctions.BezoutValuationIncidence
