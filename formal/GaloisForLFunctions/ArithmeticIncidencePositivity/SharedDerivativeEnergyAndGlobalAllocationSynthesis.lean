import GaloisForLFunctions.ArithmeticIncidencePositivity.ReflectedPrimePolarAllocation
import GaloisForLFunctions.ArithmeticIncidencePositivity.PrimeDefectCoordinate
import GaloisForLFunctions.ArithmeticIncidencePositivity.PrimeCombEnergyReduction
import GaloisForLFunctions.ArithmeticIncidencePositivity.FirstPrimeOddPartPaymentWall
import GaloisForLFunctions.ArithmeticIncidencePositivity.EdgeTentSharingObstruction
import GaloisForLFunctions.SignedArithmeticEnergyIncidence.ArithmeticCanonicalPathCalibration

/-!
# Shared Derivative-Energy Payment, Bipartite High-Lag Halving, and Global Incidence Allocation Synthesis

This module establishes the definitive all-aperture synthesis for `GlobalIncidenceAllocation` on
real odd compactly supported `C²` tests `F` on `[−r, r]`:

1. **Four-Way Equivalence of `GlobalIncidenceAllocation` (`globalIncidenceAllocation_iff_...`)**:
   For every `0 < r < R` and every real odd `F ∈ C²_c[−r, r]`, `GlobalIncidenceAllocation r R F` is
   unconditionally equivalent to bounding any of the four exact readings of the joint prime–polar
   cost `C_F(r) = reflectedPrimePolarCost F r` by the single archimedean budget
   `incidenceBudget r R F = surplusPool + crossingPotentialTerm + gaugeRemainder`:
   - the reflected-prime/polar cost `Σ_n oddStripCost − Σ_n evenStripGain + poleCharge` (retaining
     favorable prime mass `evenStripGain ≥ 0` and the negative `sinh`-pole square
     `−poleCharge = −2(∫ F sinh(x/2))² ≤ 0`),
   - the first-order joint Chebyshev-defect integral
     `∫_0^{2r} E(s) · 2e^{−s/2}(A_F'(s) − ½ A_F(s)) ds`,
   - the second-order critical-scale prefix integral
     `∫_0^{2r} (D(s) + s²/2 − s) · 2e^{−s/2}(A_{F'}(s) + A_{F,F'}(s) − ¼ A_F(s)) ds`,
   - the spectral symbol integral
     `2 ∫_ℝ (primeSymbol N ξ − 2 coshCosKernel (2r) (2πξ)) spectralDensity F ξ dξ`.

2. **Exact Cauchy–Schwarz Pole-Charge Bound and Bipartite High-Lag Halving Law
   (`poleCharge_le_two_sinh_sub_two_r_mul_sq`, `abs_autoCorrelation_le_half_of_le`,
   `exists_abs_reflectedPrimePolarCost_le_three_add_eps_mul_exp`)**:
   - Directly applying Cauchy–Schwarz to `poleCharge F = 2(∫_{−r}^r F(x) sinh(x/2) dx)²` yields the
     sharp, attained bound `0 ≤ poleCharge F ≤ (2 sinh r − 2r) ∫ F² ≤ (e^r − 2r) ∫ F²`, improving
     the previous `8 sinh r ≤ 4 e^r` bound by a factor of `4`.
   - For every lag `t ≥ r`, the support of `F(x) F(x + t)` is bipartite (`x ≤ 0 ≤ x + t`), so
     `|A_F(t)| ≤ ½ ∫ F²` (`abs_autoCorrelation_le_half_of_le`), halving the high-lag prime charge on
     `r ≤ log n < 2r` and upgrading the chord-cascade `1/4` shift defect to `1/2` on odd tests.
   - Combining both cuts the explicit Chebyshev pure-mass bound from `72 e^r` to
     `(35 e^r + 34 e^{r/2} − 2r) ∫ F²` (`GradedIncidenceAllocation (1 / 2) 75`) and lowers the
     asymptotic Prime Number Theorem pure-mass prefactor from `(8 + ε) e^r + C` to
     `((3 + ε) e^r + C) ∫ F²`.

3. **Second-Order Pole-Tilted de la Vallée Poussin Allocation
   (`exists_abs_reflectedPrimePolarCost_le_exp_sub_sqrt_mul_poleTiltedSobolev`,
   `exists_globalIncidenceAllocation_with_poleTilted_deLaValleePoussin_deficit`)**:
   Dominating `2e^{−s/2}|D(s) + s²/2 − s|` by the first-order Chebyshev-defect `L¹(0, 2r]` integral
   yields the unconditional second-order de la Vallée Poussin bound
   `|C_F(r)| ≤ K e^r exp(−c√r) (¼ ∫ F² + ∫ (F')²)` with the sharp pole-tilted mass weight `1/4`.

4. **Shared Derivative-Energy Payment Law, Plancherel Spectral Band-Split Payment, and
   High-Frequency Derivative Unboundedness (`exists_shared_derivative_payment_sub_envelope`,
   `integral_deriv_sq_eq_spectral`, `reflectedPrimePolarCost_le_spectral_band_split`,
   `integral_deriv_sq_compressTest`)**:
   - Sharing a single derivative-energy reserve `α ∫ (F')²` with `α ≥ ½ K e^r exp(−c√r)` across the
     aperture absorbs the Sobolev derivative bill and reduces the all-test deficit to the pure-mass
     sub-envelope rate `K e^r exp(−c√r) ∫ F² = o(e^r) ∫ F²`.
   - On the exponentially growing bandwidth cone `∫ (F')² ≤ 2 exp((c/2)√r) ∫ F²`, half of the
     de la Vallée Poussin saving pays the derivative energy automatically, giving the pure-mass
     sub-envelope bound `|C_F(r)| ≤ 2 K e^r exp(−(c/2)√r) ∫ F²`.
   - In frequency space, `spectralDensity (deriv F) ξ = 4π²ξ² spectralDensity F ξ` and
     `∫ (F')² = ∫ 4π²ξ² spectralDensity F ξ dξ`, so a shared derivative budget pays the entire
     high-frequency tail `|ξ| > Ω` while `[−Ω, Ω]` is controlled by pure mass.
   - Without shared derivative payment, compressing any nonzero test via `F_λ(x) = F(λx)` (`λ ≥ 1`)
     keeps support inside `[−r, r]` while scaling `∫ (F_λ')² / ∫ F_λ²` by `λ²`, proving that
     finite-horizon integrability of `E(s)` alone cannot eliminate `∫ (F')²`.

5. **Structural Synthesis of Tower, Comb, Defect, and Canonical-Path Reductions**:
   Unifies the tower diagonal bill, the Euler comb ratio–product off-diagonal decomposition, the
   sharp `1/2` high-lag defect law, and the source-faithful `weilLedgerKernel 1 1` canonical-path
   supersolutions (`primeTriangleCanonicalPathCertificate`, `packedPrimeCanonicalPathCertificate`,
   `packed_shared_step_gauge_lower_bound`).
-/

open MeasureTheory Set Filter Topology intervalIntegral
open RHTower RHTower.CHMDPolar RHTower.WeilLevyPoleGauss
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.SignedArithmeticEnergyIncidence

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

/-! ## §1. Four-Way Equivalence of `GlobalIncidenceAllocation` -/

/-- The single archimedean incidence budget on `[−r, r]` with plateau radius `R > r`:
`surplusPool + crossingPotentialTerm + gaugeRemainder` evaluated at `aperturePlateau r R`. -/
def incidenceBudget (r R : ℝ) (F : ℝ → ℝ) : ℝ :=
  surplusPool (aperturePlateau r R) F +
    crossingPotentialTerm (aperturePlateau r R) F +
    gaugeRemainder (aperturePlateau r R) F

/-- The full zero form equals `incidenceBudget r R F − reflectedPrimePolarCost F r`. -/
theorem fullZeroForm_eq_incidenceBudget_sub_reflectedPrimePolarCost {F : ℝ → ℝ} {r R : ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hr : 0 < r) (hsupp : ∀ x, r < |x| → F x = 0) (hrR : r < R) :
    fullZeroForm F = incidenceBudget r R F - reflectedPrimePolarCost F r := by
  rw [fullZeroForm_eq_reflectedPrimePolarLedger hF hFc hodd hr hsupp hrR, incidenceBudget]

/-- `GlobalIncidenceAllocation r R F` holds iff `reflectedPrimePolarCost F r ≤ incidenceBudget r R F`. -/
theorem globalIncidenceAllocation_iff_reflectedPrimePolarCost_le_incidenceBudget
    {F : ℝ → ℝ} {r R : ℝ} :
    GlobalIncidenceAllocation r R F ↔ reflectedPrimePolarCost F r ≤ incidenceBudget r R F := by
  rw [globalIncidenceAllocation_iff_reflectedPrimePolarCost, incidenceBudget]

/-- **First-Order Chebyshev-Defect Characterization of `GlobalIncidenceAllocation`.**
For every `0 < r < R` and every real odd `F ∈ C²_c[−r, r]`, `GlobalIncidenceAllocation r R F` holds
iff the joint two-pole Chebyshev-defect integral `C_F(r)` on `(0, 2r]` is bounded by the single
archimedean budget `incidenceBudget r R F`. -/
theorem globalIncidenceAllocation_iff_chebyshevTwoPoleDefect_Ioc_le_incidenceBudget
    {F : ℝ → ℝ} {r R : ℝ} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    (hodd : ∀ x, F (-x) = -F x) (hr : 0 < r) (hsupp : ∀ x, r < |x| → F x = 0) :
    GlobalIncidenceAllocation r R F ↔
      (∫ s in Ioc (0 : ℝ) (2 * r), chebyshevTwoPoleDefect s *
          (2 * Real.exp (-s / 2) * (crossCorrelation F s - autoCorrelation F s / 2))) ≤
        incidenceBudget r R F := by
  rw [globalIncidenceAllocation_iff_reflectedPrimePolarCost_le_incidenceBudget,
    reflectedPrimePolarCost_eq_chebyshevTwoPoleDefect_Ioc hF hFc hodd hr hsupp]

/-- **Second-Order Critical-Scale Prefix Characterization of `GlobalIncidenceAllocation`.**
For every `0 < r < R` and every real odd `F ∈ C²_c[−r, r]`, `GlobalIncidenceAllocation r R F` holds
iff the critical-scale prefix integral on `(0, 2r]` is bounded by `incidenceBudget r R F`. -/
theorem globalIncidenceAllocation_iff_criticalScalePrefix_Ioc_le_incidenceBudget
    {F : ℝ → ℝ} {r R : ℝ} (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F)
    (hodd : ∀ x, F (-x) = -F x) (hr : 0 < r) (hsupp : ∀ x, r < |x| → F x = 0) :
    GlobalIncidenceAllocation r R F ↔
      (∫ s in Ioc (0 : ℝ) (2 * r),
          (criticalScalePrefix s + s ^ 2 / 2 - s) *
            (2 * Real.exp (-s / 2) *
              (autoCorrelation (deriv F) s + crossCorrelation F s -
                autoCorrelation F s / 4))) ≤
        incidenceBudget r R F := by
  rw [globalIncidenceAllocation_iff_reflectedPrimePolarCost_le_incidenceBudget,
    reflectedPrimePolarCost_eq_criticalScalePrefix_autoCorrelation_deriv_Ioc hF hFc hodd hr hsupp]

/-- **Spectral Symbol Identity for `reflectedPrimePolarCost`.**
For every real odd `F ∈ C¹_c[−r, r]` and every `N ≥ e^{2r}`, the joint reflected-prime/polar cost
equals the frequency pairing of `primeSymbol N ξ − 2 coshCosKernel (2r) (2πξ)` against
`2 spectralDensity F ξ`. -/
theorem reflectedPrimePolarCost_eq_spectralSymbol_integral
    {F : ℝ → ℝ} {r : ℝ} {N : ℕ} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    (hodd : ∀ x, F (-x) = -F x) (hr : 0 < r) (hsupp : ∀ x, r < |x| → F x = 0)
    (hN : Real.exp (2 * r) ≤ N) :
    reflectedPrimePolarCost F r =
      2 * ∫ ξ : ℝ, (primeSymbol N ξ - 2 * coshCosKernel (2 * r) (2 * Real.pi * ξ)) *
        spectralDensity F ξ := by
  rw [reflectedPrimePolarCost_eq_chebyshevTwoPoleDefect hF hFc hodd hr hsupp,
    chebyshev_pairing_eq_spectral hF hFc hr hsupp hN]

/-- **Spectral Symbol Characterization of `GlobalIncidenceAllocation`.**
For every `0 < r < R`, every `N ≥ e^{2r}`, and every real odd `F ∈ C²_c[−r, r]`,
`GlobalIncidenceAllocation r R F` holds iff the spectral symbol pairing is bounded by
`incidenceBudget r R F`. -/
theorem globalIncidenceAllocation_iff_spectralSymbol_le_incidenceBudget
    {F : ℝ → ℝ} {r R : ℝ} {N : ℕ} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F)
    (hodd : ∀ x, F (-x) = -F x) (hr : 0 < r) (hsupp : ∀ x, r < |x| → F x = 0)
    (hN : Real.exp (2 * r) ≤ N) :
    GlobalIncidenceAllocation r R F ↔
      2 * (∫ ξ : ℝ, (primeSymbol N ξ - 2 * coshCosKernel (2 * r) (2 * Real.pi * ξ)) *
          spectralDensity F ξ) ≤
        incidenceBudget r R F := by
  rw [globalIncidenceAllocation_iff_reflectedPrimePolarCost_le_incidenceBudget,
    reflectedPrimePolarCost_eq_spectralSymbol_integral hF hFc hodd hr hsupp hN]

/-! ## §2. Exact Cauchy–Schwarz Pole-Charge Bound and Bipartite High-Lag Halving Law -/

/-- Exact value of the polar variance integral on `[−r, r]`:
`∫_{−r}^r 2 sinh²(x/2) dx = 2 sinh r − 2r`. -/
theorem integral_two_mul_sinh_half_sq (r : ℝ) :
    (∫ x in (-r)..r, 2 * Real.sinh (x / 2) ^ 2) = 2 * Real.sinh r - 2 * r := by
  have hderiv : ∀ x ∈ uIcc (-r) r,
      HasDerivAt (fun u => Real.sinh u - u) (2 * Real.sinh (x / 2) ^ 2) x := fun x _ => by
    have h1 := (Real.hasDerivAt_sinh x).sub (hasDerivAt_id x)
    have h2 : Real.cosh x - 1 = 2 * Real.sinh (x / 2) ^ 2 := by
      have h := cosh_half_sub_one (2 * x)
      rwa [show 2 * x / 2 = x by ring, show 2 * x / 4 = x / 2 by ring] at h
    exact h1.congr_deriv h2
  have hint : IntervalIntegrable (fun x => 2 * Real.sinh (x / 2) ^ 2) volume (-r) r :=
    (continuous_const.mul ((Real.continuous_sinh.comp (continuous_id.div_const 2)).pow 2)).intervalIntegrable
      (-r) r
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [Real.sinh_neg]
  ring

/-- For every `r ≥ 0`, `0 ≤ 2 sinh r − 2r ≤ e^r − 2r`. -/
theorem two_sinh_sub_two_r_bounds {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ 2 * Real.sinh r - 2 * r ∧ 2 * Real.sinh r - 2 * r ≤ Real.exp r - 2 * r := by
  constructor
  · rw [← integral_two_mul_sinh_half_sq r]
    exact intervalIntegral.integral_nonneg (by linarith) fun x _ => by positivity
  · rw [Real.sinh_eq]
    have := Real.exp_pos (-r)
    linarith

/-- **Sharp Cauchy–Schwarz Bound on `poleCharge F`.**
For every continuous test `F` supported in `[−r, r]` (`r > 0`),
`poleCharge F = 2 (∫ F(x) sinh(x/2) dx)² ≤ (2 sinh r − 2r) ∫ F² ≤ (e^r − 2r) ∫ F²`.
This improves `poleCharge_le_eight_mul_sinh_mul_sq` (`8 sinh r ≤ 4 e^r`) by a factor of `4`. -/
theorem poleCharge_le_two_sinh_sub_two_r_mul_sq {F : ℝ → ℝ} {r : ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) (hr : 0 < r)
    (hsupp : ∀ x, r < |x| → F x = 0) :
    poleCharge F ≤ (2 * Real.sinh r - 2 * r) * ∫ x, F x ^ 2 := by
  have hsinh_cont : Continuous fun x => Real.sinh (x / 2) :=
    Real.continuous_sinh.comp (continuous_id.div_const 2)
  have hI_eq : (∫ x, F x * Real.sinh (x / 2)) = ∫ x in (-r)..r, F x * Real.sinh (x / 2) := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    symm
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have hxr : r < |x| := by
      by_contra hle
      exact hx ⟨by linarith [(abs_le.mp (not_lt.mp hle)).1], (abs_le.mp (not_lt.mp hle)).2⟩
    rw [hsupp x hxr, zero_mul]
  have hF2_eq : (∫ x, F x ^ 2) = ∫ x in (-r)..r, F x ^ 2 := by
    rw [intervalIntegral.integral_of_le (by linarith)]
    symm
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have hxr : r < |x| := by
      by_contra hle
      exact hx ⟨by linarith [(abs_le.mp (not_lt.mp hle)).1], (abs_le.mp (not_lt.mp hle)).2⟩
    simp [hsupp x hxr]
  set I := ∫ x in (-r)..r, F x * Real.sinh (x / 2)
  set G := ∫ x in (-r)..r, Real.sinh (x / 2) ^ 2
  have h2G : 2 * G = 2 * Real.sinh r - 2 * r := by
    rw [← integral_two_mul_sinh_half_sq r, ← intervalIntegral.integral_const_mul]
  have hG0 : 0 ≤ G := intervalIntegral.integral_nonneg (by linarith) fun x _ => sq_nonneg _
  rcases eq_or_lt_of_le hG0 with hG_zero | hG_pos
  · have h2G0 : 2 * Real.sinh r - 2 * r = 0 := by linarith
    have hsinh0 : ∀ x ∈ Icc (-r) r, Real.sinh (x / 2) ^ 2 = 0 := by
      have hint_s : IntegrableOn (fun x => Real.sinh (x / 2) ^ 2) (Ioc (-r) r) :=
        (hsinh_cont.pow 2).integrableOn_Icc.mono_set Ioc_subset_Icc_self
      have h := (integral_eq_zero_iff_of_nonneg_ae
        (Eventually.of_forall fun x => sq_nonneg (Real.sinh (x / 2))) hint_s).mp
        (by rw [← intervalIntegral.integral_of_le (by linarith)]; exact hG_zero.symm)
      intro x hx
      have h0 : r = 0 := by
        have h1 := Real.sinh_pos_iff.mpr hr
        linarith
      linarith
    exfalso
    have := hsinh0 r ⟨by linarith, le_rfl⟩
    have hpos : 0 < Real.sinh (r / 2) := Real.sinh_pos_iff.mpr (by linarith)
    nlinarith
  · have hint_F2 : IntervalIntegrable (fun x => F x ^ 2) volume (-r) r :=
      (hF.pow 2).intervalIntegrable (-r) r
    have hint_FG : IntervalIntegrable (fun x => F x * Real.sinh (x / 2)) volume (-r) r :=
      (hF.mul hsinh_cont).intervalIntegrable (-r) r
    have hint_G2 : IntervalIntegrable (fun x => Real.sinh (x / 2) ^ 2) volume (-r) r :=
      (hsinh_cont.pow 2).intervalIntegrable (-r) r
    have hsq_nonneg : 0 ≤ ∫ x in (-r)..r, (G * F x - I * Real.sinh (x / 2)) ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) fun x _ => sq_nonneg _
    have hexp : (fun x => (G * F x - I * Real.sinh (x / 2)) ^ 2) =
        fun x => G ^ 2 * F x ^ 2 - 2 * G * I * (F x * Real.sinh (x / 2)) +
          I ^ 2 * Real.sinh (x / 2) ^ 2 := by
      funext x; ring
    rw [hexp,
      intervalIntegral.integral_add
        ((hint_F2.const_mul (G ^ 2)).sub (hint_FG.const_mul (2 * G * I)))
        (hint_G2.const_mul (I ^ 2)),
      intervalIntegral.integral_sub (hint_F2.const_mul (G ^ 2)) (hint_FG.const_mul (2 * G * I)),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at hsq_nonneg
    have hcs : I ^ 2 ≤ G * ∫ x in (-r)..r, F x ^ 2 := by
      have hprod : 0 ≤ G * (G * (∫ x in (-r)..r, F x ^ 2) - I ^ 2) := by
        change 0 ≤ G ^ 2 * (∫ x in (-r)..r, F x ^ 2) - 2 * G * I * I + I ^ 2 * G at hsq_nonneg
        linarith
      have hnonneg := nonneg_of_mul_nonneg_right hprod hG_pos
      linarith
    unfold poleCharge
    rw [hI_eq, hF2_eq, ← h2G]
    nlinarith

theorem poleCharge_le_exp_sub_two_r_mul_sq {F : ℝ → ℝ} {r : ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) (hr : 0 < r)
    (hsupp : ∀ x, r < |x| → F x = 0) :
    poleCharge F ≤ (Real.exp r - 2 * r) * ∫ x, F x ^ 2 := by
  have h1 := poleCharge_le_two_sinh_sub_two_r_mul_sq hF hFc hr hsupp
  have h2 := (two_sinh_sub_two_r_bounds hr.le).2
  have hI0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  exact h1.trans (mul_le_mul_of_nonneg_right h2 hI0)

/-- For an odd function `F`, `F 0 = 0`. -/
theorem odd_apply_zero {F : ℝ → ℝ} (hodd : ∀ x, F (-x) = -F x) : F 0 = 0 := by
  have h := hodd 0
  rw [neg_zero] at h
  linarith

/-- For an odd test `F` supported in `[−r, r]` and every lag `t ≥ r`, the product
`F x * F (x + t)` factors through `leftPart F x * rightPart F (x + t)` at every `x ∈ ℝ`. -/
theorem mul_shift_eq_leftPart_mul_rightPart_of_odd_of_le {F : ℝ → ℝ} {r t : ℝ}
    (hodd : ∀ x, F (-x) = -F x) (hsupp : ∀ y, r < |y| → F y = 0) (ht : r ≤ t) (x : ℝ) :
    F x * F (x + t) = leftPart F x * rightPart F (x + t) := by
  by_cases hz : F x * F (x + t) = 0
  · rw [hz]
    rcases mul_eq_zero.mp hz with h | h
    · rw [leftPart, h]; split_ifs <;> ring
    · rw [rightPart, h]; split_ifs <;> ring
  · have h1 : F x ≠ 0 := fun h => hz (by rw [h, zero_mul])
    have h2 : F (x + t) ≠ 0 := fun h => hz (by rw [h, mul_zero])
    have hx : |x| ≤ r := not_lt.mp fun h => h1 (hsupp x h)
    have hxt : |x + t| ≤ r := not_lt.mp fun h => h2 (hsupp (x + t) h)
    have hx0 : x ≠ 0 := fun h0 => h1 (by rw [h0, odd_apply_zero hodd])
    have hxle : x ≤ 0 := by
      have := (abs_le.mp hxt).2; linarith
    have hxneg : x < 0 := lt_of_le_of_ne hxle hx0
    have hxtpos : 0 ≤ x + t := by
      have := (abs_le.mp hx).1; linarith
    rw [leftPart, rightPart, if_pos hxneg, if_pos hxtpos]

/-- **Bipartite High-Lag Halving Law (`abs_autoCorrelation_le_half_of_le`).**
For every continuous odd test `F` supported in `[−r, r]` and every lag `t ≥ r`,
`|autoCorrelation F t| ≤ (1 / 2) * ∫ F²`. -/
theorem abs_autoCorrelation_le_half_of_le {F : ℝ → ℝ} {r t : ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hsupp : ∀ y, r < |y| → F y = 0) (ht : r ≤ t) :
    |autoCorrelation F t| ≤ (1 / 2) * ∫ x, F x ^ 2 := by
  have hsqF : Integrable fun x => F x ^ 2 :=
    (hF.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hFc)
  have hil : Integrable fun x => leftPart F x ^ 2 := integrable_leftPart_sq hF hFc
  have hir : Integrable fun x => rightPart F x ^ 2 := integrable_rightPart_sq hF hFc
  have hirt : Integrable fun x => rightPart F (x + t) ^ 2 := by
    simpa using hir.comp_add_right t
  have hprod : Integrable fun x => F x * F (x + t) :=
    (hF.mul (hF.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hFc.mul_right
  have htrans : (∫ x, rightPart F (x + t) ^ 2) = ∫ x, rightPart F x ^ 2 := by
    simpa using MeasureTheory.integral_add_right_eq_self (fun x => rightPart F x ^ 2) t
  have hsum : (∫ x, leftPart F x ^ 2) + ∫ x, rightPart F x ^ 2 = ∫ x, F x ^ 2 := by
    rw [integral_halves_add hF hFc, autoCorrelation_zero_eq]
  have hRHS : (∫ x, (leftPart F x ^ 2 + rightPart F (x + t) ^ 2)) = ∫ x, F x ^ 2 := by
    rw [MeasureTheory.integral_add hil hirt, htrans, hsum]
  have hpt : ∀ x, 2 * |F x * F (x + t)| ≤ leftPart F x ^ 2 + rightPart F (x + t) ^ 2 := by
    intro x
    rw [mul_shift_eq_leftPart_mul_rightPart_of_odd_of_le hodd hsupp ht x, abs_mul]
    have h1 := sq_nonneg (|leftPart F x| - |rightPart F (x + t)|)
    have h2 := sq_abs (leftPart F x)
    have h3 := sq_abs (rightPart F (x + t))
    nlinarith
  have hmono := MeasureTheory.integral_mono (hprod.norm.const_mul 2) (hil.add hirt) hpt
  rw [MeasureTheory.integral_const_mul, hRHS] at hmono
  have habs : |autoCorrelation F t| ≤ ∫ x, |F x * F (x + t)| := by
    unfold autoCorrelation
    simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => F x * F (x + t))
  linarith

/-- For `r > 0`, `relevantShifts (r / 2) ⊆ relevantShifts r`. -/
theorem relevantShifts_half_subset {r : ℝ} (hr : 0 < r) :
    relevantShifts (r / 2) ⊆ relevantShifts r := by
  intro n hn
  rw [mem_relevantShifts] at hn ⊢
  exact ⟨hn.1, by linarith [hn.2]⟩

/-- **Bipartite Split of the Prime Shift Sum.**
For every continuous odd test `F` supported in `[−r, r]` (`r > 0`), splitting `relevantShifts r` at
`r` bounds the prime shift sum by `(Σ_{n ∈ relevantShifts r} Λ(n)/√n + Σ_{n ∈ relevantShifts (r/2)} Λ(n)/√n) ∫ F²`,
halving the coefficient on the high-lag range `r ≤ log n < 2r`. -/
theorem abs_sum_relevantShifts_autoCorrelation_le_bipartite {F : ℝ → ℝ} {r : ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hr : 0 < r) (hsupp : ∀ x, r < |x| → F x = 0) :
    |∑ n ∈ relevantShifts r, 2 * vonMangoldtAtom n * autoCorrelation F (Real.log n)| ≤
      ((∑ n ∈ relevantShifts r, vonMangoldtAtom n) +
        ∑ n ∈ relevantShifts (r / 2), vonMangoldtAtom n) * ∫ x, F x ^ 2 := by
  have hsub := relevantShifts_half_subset hr
  have hterm : ∀ n ∈ relevantShifts r,
      |2 * vonMangoldtAtom n * autoCorrelation F (Real.log n)| ≤
        (vonMangoldtAtom n +
          if n ∈ relevantShifts (r / 2) then vonMangoldtAtom n else 0) * ∫ x, F x ^ 2 := by
    intro n hn
    have h2 : 2 ≤ n := (mem_relevantShifts.mp hn).1
    have hw0 : 0 ≤ vonMangoldtAtom n := vonMangoldtAtom_nonneg n
    by_cases hmem : n ∈ relevantShifts (r / 2)
    · rw [if_pos hmem, abs_mul, abs_mul, abs_of_pos two_pos, abs_of_nonneg hw0]
      have hA : |autoCorrelation F (Real.log n)| ≤ ∫ x, F x ^ 2 := by
        rw [← autoCorr_eq_autoCorrelation]
        exact abs_autoCorr_le_integral_sq hF hFc (Real.log n)
      calc 2 * vonMangoldtAtom n * |autoCorrelation F (Real.log n)|
          ≤ 2 * vonMangoldtAtom n * ∫ x, F x ^ 2 :=
            mul_le_mul_of_nonneg_left hA (by positivity)
        _ = (vonMangoldtAtom n + vonMangoldtAtom n) * ∫ x, F x ^ 2 := by ring
    · rw [if_neg hmem, add_zero, abs_mul, abs_mul, abs_of_pos two_pos, abs_of_nonneg hw0]
      have hge : r ≤ Real.log n := by
        by_contra hlt
        exact hmem (mem_relevantShifts.mpr ⟨h2, by linarith⟩)
      have hA := abs_autoCorrelation_le_half_of_le hF hFc hodd hsupp hge
      calc 2 * vonMangoldtAtom n * |autoCorrelation F (Real.log n)|
          ≤ 2 * vonMangoldtAtom n * ((1 / 2) * ∫ x, F x ^ 2) :=
            mul_le_mul_of_nonneg_left hA (by positivity)
        _ = vonMangoldtAtom n * ∫ x, F x ^ 2 := by ring
  calc |∑ n ∈ relevantShifts r, 2 * vonMangoldtAtom n * autoCorrelation F (Real.log n)|
      ≤ ∑ n ∈ relevantShifts r, |2 * vonMangoldtAtom n * autoCorrelation F (Real.log n)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ relevantShifts r,
          (vonMangoldtAtom n +
            if n ∈ relevantShifts (r / 2) then vonMangoldtAtom n else 0) * ∫ x, F x ^ 2 :=
        Finset.sum_le_sum hterm
    _ = ((∑ n ∈ relevantShifts r, vonMangoldtAtom n) +
          ∑ n ∈ relevantShifts r,
            if n ∈ relevantShifts (r / 2) then vonMangoldtAtom n else 0) * ∫ x, F x ^ 2 := by
        rw [← Finset.sum_mul, Finset.sum_add_distrib]
    _ = ((∑ n ∈ relevantShifts r, vonMangoldtAtom n) +
          ∑ n ∈ relevantShifts (r / 2), vonMangoldtAtom n) * ∫ x, F x ^ 2 := by
        rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub]

/-- **Sharp Bipartite + Cauchy–Schwarz Bound on `|reflectedPrimePolarCost F r|`.**
For every aperture `r > 0` and every real odd `F ∈ C⁰_c[−r, r]`,
`|reflectedPrimePolarCost F r| ≤ (Σ_{n ∈ relevantShifts r} Λ(n)/√n + Σ_{n ∈ relevantShifts (r/2)} Λ(n)/√n + 2 sinh r − 2r) ∫ F²`. -/
theorem abs_reflectedPrimePolarCost_le_bipartite_add_sinh {F : ℝ → ℝ} {r : ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hr : 0 < r) (hsupp : ∀ x, r < |x| → F x = 0) :
    |reflectedPrimePolarCost F r| ≤
      ((∑ n ∈ relevantShifts r, vonMangoldtAtom n) +
        (∑ n ∈ relevantShifts (r / 2), vonMangoldtAtom n) +
        (2 * Real.sinh r - 2 * r)) * ∫ x, F x ^ 2 := by
  have heq := reflectedPrimePolarCost_eq_sum_autoCorrelation_add_poleCharge hF hodd hr.le hsupp
  have hprime := abs_sum_relevantShifts_autoCorrelation_le_bipartite hF hFc hodd hr hsupp
  have hpole0 : 0 ≤ poleCharge F := poleCharge_nonneg F
  have hpole := poleCharge_le_two_sinh_sub_two_r_mul_sq hF hFc hr hsupp
  rw [heq]
  have habs := (abs_add_le
    (∑ n ∈ relevantShifts r, 2 * vonMangoldtAtom n * autoCorrelation F (Real.log n))
    (poleCharge F)).trans (by rw [abs_of_nonneg hpole0]; linarith)
  linarith

/-- **Explicit `(35 e^r + 34 e^{r/2} − 2r) ∫ F²` Bound on `|reflectedPrimePolarCost F r|`.**
For every `r > 0` and every real odd `F ∈ C⁰_c[−r, r]`,
`|reflectedPrimePolarCost F r| ≤ (35 e^r + 34 e^{r/2} − 2r) ∫ F² ≤ 69 e^r ∫ F²`. -/
theorem abs_reflectedPrimePolarCost_le_thirtyFive_exp_add_thirtyFour_exp_half {F : ℝ → ℝ} {r : ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hr : 0 < r) (hsupp : ∀ x, r < |x| → F x = 0) :
    |reflectedPrimePolarCost F r| ≤
      (35 * Real.exp r + 34 * Real.exp (r / 2) - 2 * r) * ∫ x, F x ^ 2 := by
  have h1 := abs_reflectedPrimePolarCost_le_bipartite_add_sinh hF hFc hodd hr hsupp
  have h2 := sum_relevantShifts_vonMangoldtAtom_le_thirty_four_mul_exp r
  have h3 := sum_relevantShifts_vonMangoldtAtom_le_thirty_four_mul_exp (r / 2)
  have h4 := (two_sinh_sub_two_r_bounds hr.le).2
  have hI0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  exact h1.trans (mul_le_mul_of_nonneg_right (by linarith) hI0)

theorem abs_reflectedPrimePolarCost_le_sixtyNine_mul_exp_mul_sq {F : ℝ → ℝ} {r : ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hr : 0 < r) (hsupp : ∀ x, r < |x| → F x = 0) :
    |reflectedPrimePolarCost F r| ≤ 69 * Real.exp r * ∫ x, F x ^ 2 := by
  have h1 := abs_reflectedPrimePolarCost_le_thirtyFive_exp_add_thirtyFour_exp_half
    hF hFc hodd hr hsupp
  have hexp : Real.exp (r / 2) ≤ Real.exp r := Real.exp_le_exp.mpr (by linarith)
  have hI0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  exact h1.trans (mul_le_mul_of_nonneg_right (by linarith) hI0)

/-- **Improved Unconditional `GradedIncidenceAllocation (1 / 2) 75`.**
Lowering `72 e^r` to `69 e^r` improves the global rate-`1/2` constant from `78` to `75`. -/
theorem gradedIncidenceAllocation_half_seventyFive :
    GaloisForLFunctions.SquareRootThreshold.GradedIncidenceAllocation (1 / 2) 75 := by
  intro r R F hr hrR hF hFc hodd hsupp
  have hP0 : ∀ y, 0 ≤ aperturePlateau r R y :=
    fun y => plateauGauge_nonneg R (R - r) y
  have hpool := surplusPool_nonneg (F := F) hP0
  have hcross := crossingPotentialTerm_nonneg (F := F) hP0
  have hrem := gaugeRemainder_ge_neg_const_mul_sq hF hFc hsupp hrR
  have hcost := (le_abs_self _).trans
    (abs_reflectedPrimePolarCost_le_sixtyNine_mul_exp_mul_sq hF.continuous hFc hodd hr hsupp)
  have hexp1 : 1 ≤ Real.exp r := Real.one_le_exp hr.le
  have hI0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hrem' : -(6 * Real.exp r * ∫ x, F x ^ 2) ≤ gaugeRemainder (aperturePlateau r R) F := by
    have h6 : 27 / 5 * ∫ x, F x ^ 2 ≤ 6 * Real.exp r * ∫ x, F x ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) hI0
    linarith
  have hrate : 2 * (1 / 2 : ℝ) * r = r := by ring
  rw [hrate]
  unfold reflectedPrimePolarCost at hcost
  linarith

/-- **Sharp PNT `(3 + ε) e^r + C` Pure-Mass Bound on `|reflectedPrimePolarCost F r|`.**
Combining the bipartite high-lag halving law (`2 e^r` from the prime shifts) with the sharp
Cauchy–Schwarz pole-charge bound (`e^r − 2r` from `poleCharge`) lowers the asymptotic PNT pure-mass
prefactor from `(8 + ε) e^r + C` (`exists_reflectedPrimePolarCost_le_eight_add_eps_mul_exp`) to
`(3 + ε) e^r + C` across all apertures `r > 0` and all real odd tests `F ∈ C⁰_c[−r, r]`. -/
theorem exists_abs_reflectedPrimePolarCost_le_three_add_eps_mul_exp {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ) (F : ℝ → ℝ), 0 < r → Continuous F → HasCompactSupport F →
      (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
      |reflectedPrimePolarCost F r| ≤ ((3 + ε) * Real.exp r + C) * ∫ x, F x ^ 2 := by
  obtain ⟨C₀, hC₀0, hC₀⟩ :=
    GaloisForLFunctions.SquareRootThreshold.exists_aperturePrimeSum_le_two_add_eps_mul_exp
      (half_pos hε)
  refine ⟨C₀ + 578 / ε, by positivity, fun r F hr hF hFc hodd hsupp => ?_⟩
  have h1 := abs_reflectedPrimePolarCost_le_bipartite_add_sinh hF hFc hodd hr hsupp
  have h2 := (sum_relevantShifts_vonMangoldtAtom_le_aperturePrimeSum r).trans (hC₀ r)
  have h3 := sum_relevantShifts_vonMangoldtAtom_le_thirty_four_mul_exp (r / 2)
  have h4 := (two_sinh_sub_two_r_bounds hr.le).2
  have hhalf_sq : 34 * Real.exp (r / 2) ≤ (ε / 2) * Real.exp r + 578 / ε := by
    have hsq : 0 ≤ (ε / 34 * Real.exp (r / 2) - 1) ^ 2 := sq_nonneg _
    have hexp_sq : Real.exp (r / 2) ^ 2 = Real.exp r := by
      rw [← Real.exp_nat_mul, show (2 : ℕ) * (r / 2) = r by push_cast; ring]
    have hmul := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 578 / ε)
    have hident : 578 / ε * (ε / 34 * Real.exp (r / 2) - 1) ^ 2 =
        (ε / 2) * Real.exp (r / 2) ^ 2 - 34 * Real.exp (r / 2) + 578 / ε := by
      field_simp
      ring
    rw [hident, hexp_sq] at hmul
    linarith
  have hI0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  exact h1.trans (mul_le_mul_of_nonneg_right (by linarith) hI0)

/-! ## §3. Second-Order Pole-Tilted de la Vallée Poussin Allocation -/

/-- Pointwise domination of the damped critical-scale prefix `2e^{−s/2}|D(s) + s²/2 − s|` on
`(0, 2r]` by the `L¹(0, 2r]` norm of `2e^{−u/2}|E(u)|`. -/
theorem two_mul_exp_neg_half_mul_abs_criticalScalePrefix_le {r s : ℝ}
    (hs0 : 0 ≤ s) (hsr : s ≤ 2 * r) :
    2 * Real.exp (-s / 2) * |criticalScalePrefix s + s ^ 2 / 2 - s| ≤
      ∫ u in Ioc (0 : ℝ) (2 * r), 2 * Real.exp (-u / 2) * |chebyshevTwoPoleDefect u| := by
  rw [criticalScalePrefix_eq_integral_chebyshevTwoPoleDefect hs0]
  have hint_2r := integrableOn_Ioc_exp_mul_abs_chebyshevTwoPoleDefect (by linarith : 0 ≤ 2 * r)
  have hint_s : IntegrableOn (fun u => 2 * Real.exp (-u / 2) * |chebyshevTwoPoleDefect u|)
      (Ioc (0 : ℝ) s) :=
    hint_2r.mono_set (Ioc_subset_Ioc_right hsr)
  calc 2 * Real.exp (-s / 2) * |∫ u in Ioc (0 : ℝ) s, chebyshevTwoPoleDefect u|
      ≤ 2 * Real.exp (-s / 2) * ∫ u in Ioc (0 : ℝ) s, |chebyshevTwoPoleDefect u| := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (f := chebyshevTwoPoleDefect)
            (μ := volume.restrict (Ioc 0 s))
    _ = ∫ u in Ioc (0 : ℝ) s, 2 * Real.exp (-s / 2) * |chebyshevTwoPoleDefect u| := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ ∫ u in Ioc (0 : ℝ) s, 2 * Real.exp (-u / 2) * |chebyshevTwoPoleDefect u| := by
        refine setIntegral_mono_on
          (((integrableOn_Ioc_chebyshevTwoPoleDefect hs0).norm).const_mul (2 * Real.exp (-s / 2)))
          hint_s measurableSet_Ioc fun u hu => ?_
        have hexp : Real.exp (-s / 2) ≤ Real.exp (-u / 2) :=
          Real.exp_le_exp.mpr (by linarith [hu.2])
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp zero_le_two)
          (abs_nonneg _)
    _ ≤ ∫ u in Ioc (0 : ℝ) (2 * r), 2 * Real.exp (-u / 2) * |chebyshevTwoPoleDefect u| := by
        refine setIntegral_mono_set hint_2r
          (Eventually.of_forall fun u => by positivity)
          (Eventually.of_forall fun u hu => ⟨hu.1, hu.2.trans hsr⟩)

/-- **Second-Order Critical-Scale `L¹` Domination by the First-Order Chebyshev-Defect `L¹` Norm.**
For every `r ≥ 0`,
`∫_0^{2r} 2e^{−s/2}|D(s) + s²/2 − s| ds ≤ 2r ∫_0^{2r} 2e^{−u/2}|E(u)| du`. -/
theorem integral_Ioc_exp_mul_abs_criticalScalePrefix_le_two_mul_r {r : ℝ} (hr : 0 ≤ r) :
    (∫ s in Ioc (0 : ℝ) (2 * r),
        2 * Real.exp (-s / 2) * |criticalScalePrefix s + s ^ 2 / 2 - s|) ≤
      2 * r * ∫ u in Ioc (0 : ℝ) (2 * r), 2 * Real.exp (-u / 2) * |chebyshevTwoPoleDefect u| := by
  set M := ∫ u in Ioc (0 : ℝ) (2 * r), 2 * Real.exp (-u / 2) * |chebyshevTwoPoleDefect u|
  have hcont : Continuous fun s : ℝ =>
      2 * Real.exp (-s / 2) * |criticalScalePrefix s + s ^ 2 / 2 - s| :=
    (continuous_const.mul (Real.continuous_exp.comp (continuous_id.neg.div_const 2))).mul
      ((continuous_criticalScalePrefix.add (continuous_id.pow 2 |>.div_const 2)).sub
        continuous_id).abs
  have hint : IntegrableOn
      (fun s => 2 * Real.exp (-s / 2) * |criticalScalePrefix s + s ^ 2 / 2 - s|)
      (Ioc (0 : ℝ) (2 * r)) :=
    hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hmono : (∫ s in Ioc (0 : ℝ) (2 * r),
        2 * Real.exp (-s / 2) * |criticalScalePrefix s + s ^ 2 / 2 - s|) ≤
      ∫ _ in Ioc (0 : ℝ) (2 * r), M := by
    refine setIntegral_mono_on hint (integrableOn_const (by simp)) measurableSet_Ioc fun s hs => ?_
    exact two_mul_exp_neg_half_mul_abs_criticalScalePrefix_le hs.1.le hs.2
  have hconst : (∫ _ in Ioc (0 : ℝ) (2 * r), M) = 2 * r * M := by
    rw [setIntegral_const, Measure.real, Real.volume_Ioc, sub_zero,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
  exact hmono.trans hconst.le

/-- **De la Vallée Poussin Bound on the Second-Order Critical-Scale `L¹` Norm.**
With universal constants `c > 0` and `K > 0`, for every `r > 0`,
`∫_0^{2r} 2e^{−s/2}|criticalScalePrefix s + s²/2 − s| ds ≤ K e^r exp(−c√r)`. -/
theorem exists_integral_Ioc_exp_mul_abs_criticalScalePrefix_le :
    ∃ c > 0, ∃ K > 0, ∀ r : ℝ, 0 < r →
      (∫ s in Ioc (0 : ℝ) (2 * r),
          2 * Real.exp (-s / 2) * |criticalScalePrefix s + s ^ 2 / 2 - s|) ≤
        K * Real.exp r * Real.exp (-c * Real.sqrt r) := by
  obtain ⟨c₀, hc₀, K₀, hK₀, hL1⟩ := exists_integral_Ioc_exp_mul_abs_chebyshevTwoPoleDefect_le
  set c := c₀ / 2
  have hc : 0 < c := half_pos hc₀
  set K := 4 * K₀ / c ^ 2
  have hK : 0 < K := by positivity
  refine ⟨c, hc, K, hK, fun r hr => ?_⟩
  have hdom := integral_Ioc_exp_mul_abs_criticalScalePrefix_le_two_mul_r hr.le
  have h1 := hL1 r hr
  have hexp_split : Real.exp (-c₀ * Real.sqrt r) =
      Real.exp (-c * Real.sqrt r) * Real.exp (-c * Real.sqrt r) := by
    rw [← Real.exp_add]
    congr 1
    simp only [c]
    ring
  have hquad : r * Real.exp (-c * Real.sqrt r) ≤ 2 / c ^ 2 := by
    have hq := Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ c * Real.sqrt r)
    have hsq : (c * Real.sqrt r) ^ 2 = c ^ 2 * r := by rw [mul_pow, Real.sq_sqrt hr.le]
    have hle : c ^ 2 / 2 * r ≤ Real.exp (c * Real.sqrt r) := by rw [hsq] at hq; linarith
    have hmul := mul_le_mul_of_nonneg_right hle
      (by positivity : 0 ≤ 2 / c ^ 2 * Real.exp (-c * Real.sqrt r))
    have hlhs : c ^ 2 / 2 * r * (2 / c ^ 2 * Real.exp (-c * Real.sqrt r)) =
        r * Real.exp (-c * Real.sqrt r) := by field_simp
    have hrhs : Real.exp (c * Real.sqrt r) * (2 / c ^ 2 * Real.exp (-c * Real.sqrt r)) =
        2 / c ^ 2 := by
      rw [mul_left_comm, ← Real.exp_add, show c * Real.sqrt r + -c * Real.sqrt r = 0 by ring,
        Real.exp_zero, mul_one]
    linarith
  calc (∫ s in Ioc (0 : ℝ) (2 * r),
          2 * Real.exp (-s / 2) * |criticalScalePrefix s + s ^ 2 / 2 - s|)
      ≤ 2 * r * (K₀ * Real.exp r * Real.exp (-c₀ * Real.sqrt r)) :=
        hdom.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
    _ = 2 * K₀ * (r * Real.exp (-c * Real.sqrt r)) * (Real.exp r * Real.exp (-c * Real.sqrt r)) := by
        rw [hexp_split]; ring
    _ ≤ 2 * K₀ * (2 / c ^ 2) * (Real.exp r * Real.exp (-c * Real.sqrt r)) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hquad (by positivity))
          (by positivity)
    _ = K * Real.exp r * Real.exp (-c * Real.sqrt r) := by simp only [K]; ring

/-- **Second-Order Pole-Tilted de la Vallée Poussin Bound on `|reflectedPrimePolarCost F r|`.**
With universal constants `c > 0` and `K > 0`, for every aperture `r > 0` and every real odd
`F ∈ C²_c[−r, r]`,
`|reflectedPrimePolarCost F r| ≤ K e^r exp(−c√r) ((1/4) ∫ F² + ∫ (deriv F)²)`. -/
theorem exists_abs_reflectedPrimePolarCost_le_exp_sub_sqrt_mul_poleTiltedSobolev :
    ∃ c > 0, ∃ K > 0, ∀ (r : ℝ) (F : ℝ → ℝ), 0 < r → ContDiff ℝ 2 F → HasCompactSupport F →
      (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
      |reflectedPrimePolarCost F r| ≤
        K * Real.exp r * Real.exp (-c * Real.sqrt r) *
          ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2) := by
  obtain ⟨c, hc, K, hK, hL1⟩ := exists_integral_Ioc_exp_mul_abs_criticalScalePrefix_le
  refine ⟨c, hc, K, hK, fun r F hr hF hFc hodd hsupp => ?_⟩
  have h1 := abs_reflectedPrimePolarCost_le_criticalScalePrefix_L1_mul_sobolev hF hFc hodd hr hsupp
  have h2 := hL1 r hr
  have hsob : 0 ≤ (1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2 :=
    add_nonneg (mul_nonneg (by norm_num) (integral_nonneg fun _ => sq_nonneg _))
      (integral_nonneg fun _ => sq_nonneg _)
  exact h1.trans (mul_le_mul_of_nonneg_right h2 hsob)

/-- **Second-Order Pole-Tilted de la Vallée Poussin Global Incidence Allocation.**
With universal constants `c > 0` and `K > 0`, for every `0 < r < R` and every real odd
`F ∈ C²_c[−r, r]`, `GlobalIncidenceAllocation` holds up to the pole-tilted Sobolev deficit
`K e^r exp(−c√r) ((1/4) ∫ F² + ∫ (deriv F)²)`. -/
theorem exists_globalIncidenceAllocation_with_poleTilted_deLaValleePoussin_deficit :
    ∃ c > 0, ∃ K > 0, ∀ (r R : ℝ) (F : ℝ → ℝ), 0 < r → r < R →
      ContDiff ℝ 2 F → HasCompactSupport F →
      (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
      (∑ n ∈ relevantShifts r, oddStripCost F r n) + poleCharge F ≤
        surplusPool (aperturePlateau r R) F +
          crossingPotentialTerm (aperturePlateau r R) F +
          (∑ n ∈ relevantShifts r, evenStripGain F r n) +
          gaugeRemainder (aperturePlateau r R) F +
          K * Real.exp r * Real.exp (-c * Real.sqrt r) *
            ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2) := by
  obtain ⟨c, hc, K₀, hK₀, hcost⟩ :=
    exists_abs_reflectedPrimePolarCost_le_exp_sub_sqrt_mul_poleTiltedSobolev
  set K := K₀ + 108 / 5 * Real.exp (c ^ 2 / 4)
  have hK : 0 < K := by positivity
  refine ⟨c, hc, K, hK, fun r R F hr hrR hF hFc hodd hsupp => ?_⟩
  have hc1 := (le_abs_self _).trans (hcost r F hr hF hFc hodd hsupp)
  unfold reflectedPrimePolarCost at hc1
  have hP0 : ∀ y, 0 ≤ aperturePlateau r R y :=
    fun y => plateauGauge_nonneg R (R - r) y
  have hpool := surplusPool_nonneg (F := F) hP0
  have hcross := crossingPotentialTerm_nonneg (F := F) hP0
  have hrem := gaugeRemainder_ge_neg_const_mul_sq hF hFc hsupp hrR
  have hsq_r : Real.sqrt r ^ 2 = r := Real.sq_sqrt hr.le
  have hcomplete : 0 ≤ c ^ 2 / 4 + r - c * Real.sqrt r := by
    have := sq_nonneg (Real.sqrt r - c / 2)
    linarith
  have hexp_floor : 1 ≤ Real.exp (c ^ 2 / 4) * (Real.exp r * Real.exp (-c * Real.sqrt r)) := by
    rw [← Real.exp_add, ← Real.exp_add,
      show c ^ 2 / 4 + (r + -c * Real.sqrt r) = c ^ 2 / 4 + r - c * Real.sqrt r by ring]
    exact Real.one_le_exp hcomplete
  have hI0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hd0 : 0 ≤ ∫ x, deriv F x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hrem' : 27 / 5 * ∫ x, F x ^ 2 ≤
      (108 / 5 * Real.exp (c ^ 2 / 4)) * Real.exp r * Real.exp (-c * Real.sqrt r) *
        ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2) := by
    calc 27 / 5 * ∫ x, F x ^ 2
        = 108 / 5 * 1 * ((1 / 4) * ∫ x, F x ^ 2) := by ring
      _ ≤ 108 / 5 * (Real.exp (c ^ 2 / 4) * (Real.exp r * Real.exp (-c * Real.sqrt r))) *
            ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hexp_floor (by norm_num))
            (by linarith) (by positivity) (by positivity)
      _ = (108 / 5 * Real.exp (c ^ 2 / 4)) * Real.exp r * Real.exp (-c * Real.sqrt r) *
            ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2) := by ring
  have hsum_K : K * Real.exp r * Real.exp (-c * Real.sqrt r) *
        ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2) =
      K₀ * Real.exp r * Real.exp (-c * Real.sqrt r) *
        ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2) +
      (108 / 5 * Real.exp (c ^ 2 / 4)) * Real.exp r * Real.exp (-c * Real.sqrt r) *
        ((1 / 4) * (∫ x, F x ^ 2) + ∫ x, deriv F x ^ 2) := by
    simp only [K]; ring
  linarith

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
