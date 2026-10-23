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

1. **Three-Way Equivalence of `GlobalIncidenceAllocation` (`globalIncidenceAllocation_iff_...`)**:
   For every `0 < r < R` and every real odd `F ∈ C²_c[−r, r]`, `GlobalIncidenceAllocation r R F` is
   unconditionally equivalent to bounding any of the three exact readings of the joint prime–polar
   cost `C_F(r) = reflectedPrimePolarCost F r` by the single archimedean budget
   `incidenceBudget r R F = surplusPool + crossingPotentialTerm + gaugeRemainder`:
   - the reflected-prime/polar cost `Σ_n oddStripCost − Σ_n evenStripGain + poleCharge` (retaining
     favorable prime mass `evenStripGain ≥ 0` and the negative `sinh`-pole square
     `−poleCharge = −2(∫ F sinh(x/2))² ≤ 0`),
   - the first-order joint Chebyshev-defect integral
     `∫_0^{2r} E(s) · 2e^{−s/2}(A_F'(s) − ½ A_F(s)) ds`,
   - the second-order critical-scale prefix integral
     `∫_0^{2r} (D(s) + s²/2 − s) · 2e^{−s/2}(A_{F'}(s) + A_{F,F'}(s) − ¼ A_F(s)) ds`.

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

4. **Shared Derivative-Energy Payment Law, Exponential Bandwidth Sub-Envelope Cone, and
   High-Frequency Derivative Unboundedness (`exists_shared_derivative_payment_sub_envelope`,
   `exists_abs_reflectedPrimePolarCost_le_sub_envelope_of_dirichlet_le`,
   `integral_deriv_sq_compressTest`)**:
   - Sharing a single derivative-energy reserve `α ∫ (F')²` with `α ≥ ½ K e^r exp(−c√r)` across the
     aperture absorbs the Sobolev derivative bill and reduces the all-test deficit to the pure-mass
     sub-envelope rate `K e^r exp(−c√r) ∫ F² = o(e^r) ∫ F²`.
   - On the exponentially growing bandwidth cone `∫ (F')² ≤ 2 exp((c/2)√r) ∫ F²`, half of the
     de la Vallée Poussin saving pays the derivative energy automatically, giving the pure-mass
     sub-envelope bound `|C_F(r)| ≤ 2 K e^r exp(−(c/2)√r) ∫ F²`.
   - Without shared derivative payment, compressing any test via `F_λ(x) = F(λx)` (`λ ≥ 1`) keeps
     support inside `[−r, r]` while scaling `∫ (F_λ')²` by `λ` and `∫ F_λ²` by `λ⁻¹`, proving that
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

/-! ## §1. Equivalent Characterizations of `GlobalIncidenceAllocation` -/

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
  unfold GlobalIncidenceAllocation reflectedPrimePolarCost incidenceBudget
  constructor <;> intro h <;> linarith

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
    reflectedPrimePolarCost_eq_criticalScalePrefix_Ioc hF hFc hodd hr hsupp]

/-! ## §2. Exact Cauchy–Schwarz Pole-Charge Bound and Bipartite High-Lag Halving Law -/

/-- Exact value of the polar variance integral on `[−r, r]`:
`∫_{−r}^r 2 sinh²(x/2) dx = 2 sinh r − 2r`. -/
theorem integral_two_mul_sinh_half_sq (r : ℝ) :
    (∫ x in (-r)..r, 2 * Real.sinh (x / 2) ^ 2) = 2 * Real.sinh r - 2 * r := by
  have hderiv : ∀ x ∈ uIcc (-r) r,
      HasDerivAt (fun u => Real.sinh u - u) (2 * Real.sinh (x / 2) ^ 2) x := fun x _ => by
    have h1 := (Real.hasDerivAt_sinh x).sub (hasDerivAt_id x)
    have h2 : Real.cosh x - 1 = 2 * Real.sinh (x / 2) ^ 2 := by
      have hpos : Real.exp (x / 2) * Real.exp (-(x / 2)) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      have hexp1 : Real.exp x = Real.exp (x / 2) * Real.exp (x / 2) := by
        rw [← Real.exp_add, add_halves]
      have hexp2 : Real.exp (-x) = Real.exp (-(x / 2)) * Real.exp (-(x / 2)) := by
        rw [← Real.exp_add, show -(x / 2) + -(x / 2) = -x by ring]
      calc Real.cosh x - 1
          = (Real.exp x + Real.exp (-x)) / 2 - 1 := by rw [Real.cosh_eq]
        _ = (Real.exp (x / 2) * Real.exp (x / 2) +
              Real.exp (-(x / 2)) * Real.exp (-(x / 2))) / 2 -
              Real.exp (x / 2) * Real.exp (-(x / 2)) := by rw [hexp1, hexp2, hpos]
        _ = 2 * ((Real.exp (x / 2) - Real.exp (-(x / 2))) / 2) ^ 2 := by ring
        _ = 2 * Real.sinh (x / 2) ^ 2 := by rw [Real.sinh_eq]
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
    rw [intervalIntegral.integral_of_le (by linarith), ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    symm
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have hxr : r < |x| := by
      rw [lt_abs]
      by_contra! hle
      exact hx ⟨by linarith [hle.2], hle.1⟩
    rw [hsupp x hxr, zero_mul]
  have hF2_eq : (∫ x, F x ^ 2) = ∫ x in (-r)..r, F x ^ 2 := by
    rw [intervalIntegral.integral_of_le (by linarith), ← MeasureTheory.integral_Icc_eq_integral_Ioc]
    symm
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have hxr : r < |x| := by
      rw [lt_abs]
      by_contra! hle
      exact hx ⟨by linarith [hle.2], hle.1⟩
    simp [hsupp x hxr]
  set I := ∫ x in (-r)..r, F x * Real.sinh (x / 2)
  set G := ∫ x in (-r)..r, Real.sinh (x / 2) ^ 2
  set A := ∫ x in (-r)..r, F x ^ 2
  have h2G : 2 * G = 2 * Real.sinh r - 2 * r := by
    rw [← integral_two_mul_sinh_half_sq r, ← intervalIntegral.integral_const_mul]
  have hint_F2 : IntervalIntegrable (fun x => F x ^ 2) volume (-r) r :=
    (hF.pow 2).intervalIntegrable (-r) r
  have hint_FG : IntervalIntegrable (fun x => F x * Real.sinh (x / 2)) volume (-r) r :=
    (hF.mul hsinh_cont).intervalIntegrable (-r) r
  have hint_G2 : IntervalIntegrable (fun x => Real.sinh (x / 2) ^ 2) volume (-r) r :=
    (hsinh_cont.pow 2).intervalIntegrable (-r) r
  have hquad : ∀ θ : ℝ, 0 ≤ G * (θ * θ) + (2 * I) * θ + A := fun θ => by
    have hsq : 0 ≤ ∫ x in (-r)..r, (F x + θ * Real.sinh (x / 2)) ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) fun x _ => sq_nonneg _
    have hexp : (fun x => (F x + θ * Real.sinh (x / 2)) ^ 2) =
        fun x => (F x ^ 2 + 2 * θ * (F x * Real.sinh (x / 2))) +
          (θ * θ) * Real.sinh (x / 2) ^ 2 := by
      funext x; ring
    rw [hexp,
      intervalIntegral.integral_add
        (hint_F2.add (hint_FG.const_mul (2 * θ)))
        (hint_G2.const_mul (θ * θ)),
      intervalIntegral.integral_add hint_F2 (hint_FG.const_mul (2 * θ)),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul] at hsq
    change 0 ≤ A + 2 * θ * I + (θ * θ) * G at hsq
    linarith
  have hdisc := discrim_le_zero hquad
  rw [discrim] at hdisc
  unfold poleCharge oddPoleMoment
  rw [hI_eq, hF2_eq]
  change 2 * I ^ 2 ≤ (2 * Real.sinh r - 2 * r) * A
  rw [← h2G]
  linarith

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
  have hbl : ∀ x, leftPart F x ^ 2 ≤ F x ^ 2 := fun x => by
    have := leftPart_sq_add_rightPart_sq F x; nlinarith [sq_nonneg (rightPart F x)]
  have hbr : ∀ x, rightPart F x ^ 2 ≤ F x ^ 2 := fun x => by
    have := leftPart_sq_add_rightPart_sq F x; nlinarith [sq_nonneg (leftPart F x)]
  have hil : Integrable fun x => leftPart F x ^ 2 := by
    refine hsqF.mono' ((measurable_leftPart hF).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbl x
  have hir : Integrable fun x => rightPart F x ^ 2 := by
    refine hsqF.mono' ((measurable_rightPart hF).pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hbr x
  have hirt : Integrable fun x => rightPart F (x + t) ^ 2 := by
    simpa using hir.comp_add_right t
  have hprod : Integrable fun x => F x * F (x + t) :=
    (hF.mul (hF.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hFc.mul_right
  have htrans : (∫ x, rightPart F (x + t) ^ 2) = ∫ x, rightPart F x ^ 2 := by
    simpa using MeasureTheory.integral_add_right_eq_self (fun x => rightPart F x ^ 2) t
  have hsum : (∫ x, leftPart F x ^ 2) + ∫ x, rightPart F x ^ 2 = ∫ x, F x ^ 2 := by
    rw [← MeasureTheory.integral_add hil hir]
    exact MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall fun x => leftPart_sq_add_rightPart_sq F x)
  have hpt : ∀ x, 2 * |F x * F (x + t)| ≤ leftPart F x ^ 2 + rightPart F (x + t) ^ 2 := by
    intro x
    rw [mul_shift_eq_leftPart_mul_rightPart_of_odd_of_le hodd hsupp ht x, abs_mul]
    have h1 := sq_nonneg (|leftPart F x| - |rightPart F (x + t)|)
    have h2 := sq_abs (leftPart F x)
    have h3 := sq_abs (rightPart F (x + t))
    nlinarith
  have hiadd : Integrable fun x => leftPart F x ^ 2 + rightPart F (x + t) ^ 2 := hil.add hirt
  have hmono := MeasureTheory.integral_mono (hprod.norm.const_mul 2) hiadd (fun x => hpt x)
  rw [MeasureTheory.integral_const_mul] at hmono
  have hRHS : (∫ x, (leftPart F x ^ 2 + rightPart F (x + t) ^ 2)) = ∫ x, F x ^ 2 := by
    rw [MeasureTheory.integral_add hil hirt, htrans, hsum]
  rw [hRHS] at hmono
  have habs : |autoCorrelation F t| ≤ ∫ x, ‖F x * F (x + t)‖ := by
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
  have hite_eq : (∑ n ∈ relevantShifts r,
      if n ∈ relevantShifts (r / 2) then vonMangoldtAtom n else 0) =
      ∑ n ∈ relevantShifts (r / 2), vonMangoldtAtom n := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub]
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
        rw [hite_eq]

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
  have habs := abs_add_le
    (∑ n ∈ relevantShifts r, 2 * vonMangoldtAtom n * autoCorrelation F (Real.log n))
    (poleCharge F)
  rw [abs_of_nonneg hpole0] at habs
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

theorem exists_reflectedPrimePolarCost_le_three_add_eps_mul_exp {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℝ) (F : ℝ → ℝ), 0 < r → Continuous F → HasCompactSupport F →
      (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
      reflectedPrimePolarCost F r ≤ ((3 + ε) * Real.exp r + C) * ∫ x, F x ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_reflectedPrimePolarCost_le_three_add_eps_mul_exp hε
  exact ⟨C, hC0, fun r F hr hF hFc hodd hsupp =>
    (le_abs_self _).trans (hC r F hr hF hFc hodd hsupp)⟩

/-! ## §3. Second-Order Pole-Tilted de la Vallée Poussin Allocation -/

/-- Exact integral representation of `criticalScalePrefix s + s²/2 − s` as the primitive of
`chebyshevTwoPoleDefect` on `(0, s]`. -/
theorem criticalScalePrefix_add_quad_eq_integral_chebyshevTwoPoleDefect {s : ℝ} (hs : 0 ≤ s) :
    criticalScalePrefix s + s ^ 2 / 2 - s =
      ∫ u in Ioc (0 : ℝ) s, chebyshevTwoPoleDefect u := by
  have hint1 : IntervalIntegrable (fun u => Real.exp u - lagChebyshev u) volume 0 s :=
    (Real.continuous_exp.intervalIntegrable 0 s).sub lagChebyshev_mono.intervalIntegrable
  have hint2 : IntervalIntegrable (fun u => u - 1) volume 0 s :=
    (continuous_id.sub continuous_const).intervalIntegrable 0 s
  have hlin : (∫ u in (0 : ℝ)..s, (u - 1)) = s ^ 2 / 2 - s := by
    have hd : ∀ u ∈ uIcc (0 : ℝ) s, HasDerivAt (fun t => t ^ 2 / 2 - t) (u - 1) u := fun u _ => by
      have h := ((hasDerivAt_pow 2 u).div_const 2).sub (hasDerivAt_id u)
      exact h.congr_deriv (by ring)
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint2]
    ring
  rw [criticalScalePrefix, add_sub_assoc, ← hlin, ← intervalIntegral.integral_add hint1 hint2,
    intervalIntegral.integral_of_le hs]
  refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
  rw [chebyshevTwoPoleDefect, twoPoleWeight]
  ring

theorem integrableOn_Ioc_chebyshevTwoPoleDefect {s : ℝ} (hs : 0 ≤ s) :
    IntegrableOn chebyshevTwoPoleDefect (Ioc 0 s) := by
  have hint1 : IntervalIntegrable (fun u => Real.exp u - lagChebyshev u) volume 0 s :=
    (Real.continuous_exp.intervalIntegrable 0 s).sub lagChebyshev_mono.intervalIntegrable
  have hint2 : IntervalIntegrable (fun u => u - 1) volume 0 s :=
    (continuous_id.sub continuous_const).intervalIntegrable 0 s
  have hint := (intervalIntegrable_iff_integrableOn_Ioc_of_le hs).mp (hint1.add hint2)
  refine hint.congr_fun (fun u _ => ?_) measurableSet_Ioc
  simp only [chebyshevTwoPoleDefect, twoPoleWeight]
  ring

/-- Pointwise domination of the damped critical-scale prefix `2e^{−s/2}|D(s) + s²/2 − s|` on
`(0, 2r]` by the `L¹(0, 2r]` norm of `2e^{−u/2}|E(u)|`. -/
theorem two_mul_exp_neg_half_mul_abs_criticalScalePrefix_le {r s : ℝ}
    (hs0 : 0 < s) (hsr : s ≤ 2 * r) :
    2 * Real.exp (-s / 2) * |criticalScalePrefix s + s ^ 2 / 2 - s| ≤
      ∫ u in Ioc (0 : ℝ) (2 * r), 2 * Real.exp (-u / 2) * |chebyshevTwoPoleDefect u| := by
  rw [criticalScalePrefix_add_quad_eq_integral_chebyshevTwoPoleDefect hs0.le]
  have h2r : 0 < 2 * r := lt_of_lt_of_le hs0 hsr
  have hint_2r := integrableOn_Ioc_exp_mul_abs_chebyshevTwoPoleDefect h2r
  have hint_s : IntegrableOn (fun u => 2 * Real.exp (-u / 2) * |chebyshevTwoPoleDefect u|)
      (Ioc (0 : ℝ) s) :=
    hint_2r.mono_set (Ioc_subset_Ioc_right hsr)
  calc 2 * Real.exp (-s / 2) * |∫ u in Ioc (0 : ℝ) s, chebyshevTwoPoleDefect u|
      ≤ 2 * Real.exp (-s / 2) * ∫ u in Ioc (0 : ℝ) s, |chebyshevTwoPoleDefect u| := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        simpa [Real.norm_eq_abs] using
          MeasureTheory.norm_integral_le_integral_norm (f := chebyshevTwoPoleDefect)
            (μ := volume.restrict (Ioc 0 s))
    _ = ∫ u in Ioc (0 : ℝ) s, 2 * Real.exp (-s / 2) * |chebyshevTwoPoleDefect u| := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ ∫ u in Ioc (0 : ℝ) s, 2 * Real.exp (-u / 2) * |chebyshevTwoPoleDefect u| := by
        refine setIntegral_mono_on
          (((integrableOn_Ioc_chebyshevTwoPoleDefect hs0.le).norm).const_mul (2 * Real.exp (-s / 2)))
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
  have hint := integrableOn_Ioc_exp_mul_abs_criticalScalePrefix (2 * r)
  have hint_const : IntegrableOn (fun _ : ℝ => M) (Ioc (0 : ℝ) (2 * r)) :=
    (continuous_const.integrableOn_Icc (a := 0) (b := 2 * r)).mono_set Ioc_subset_Icc_self
  have hmono : (∫ s in Ioc (0 : ℝ) (2 * r),
        2 * Real.exp (-s / 2) * |criticalScalePrefix s + s ^ 2 / 2 - s|) ≤
      ∫ _ in Ioc (0 : ℝ) (2 * r), M := by
    refine setIntegral_mono_on hint hint_const measurableSet_Ioc fun s hs => ?_
    exact two_mul_exp_neg_half_mul_abs_criticalScalePrefix_le hs.1 hs.2
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
    have hcr0 : 0 ≤ c * Real.sqrt r := by positivity
    have hle : c ^ 2 * r / 2 ≤ Real.exp (c * Real.sqrt r) := by
      rw [hsq] at hq
      linarith
    have hmul := mul_le_mul_of_nonneg_right hle
      (by positivity : 0 ≤ 2 / c ^ 2 * Real.exp (-c * Real.sqrt r))
    have hlhs : c ^ 2 * r / 2 * (2 / c ^ 2 * Real.exp (-c * Real.sqrt r)) =
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

/-! ## §4. Shared Derivative-Energy Payment Law, Bandwidth Cones, and Compression Unboundedness -/

/-- **Shared Derivative-Energy Payment Theorem (`exists_shared_derivative_payment_sub_envelope`).**
With universal constants `c > 0` and `K > 0`, for every aperture `r > 0`, every real odd
`F ∈ C¹_c[−r, r]`, and every shared derivative-energy rate `α ≥ (1/2) K e^r exp(−c√r)`, paying the
single derivative reserve `α ∫ (deriv F)²` reduces the prime–polar cost to the pure-mass
sub-envelope bound `K e^r exp(−c√r) ∫ F² = o(e^r) ∫ F²`. -/
theorem exists_shared_derivative_payment_sub_envelope :
    ∃ c > 0, ∃ K > 0, ∀ (r α : ℝ) (F : ℝ → ℝ), 0 < r →
      (1 / 2) * (K * Real.exp r * Real.exp (-c * Real.sqrt r)) ≤ α →
      ContDiff ℝ 1 F → HasCompactSupport F →
      (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
      reflectedPrimePolarCost F r - α * (∫ x, deriv F x ^ 2) ≤
        K * Real.exp r * Real.exp (-c * Real.sqrt r) * ∫ x, F x ^ 2 := by
  obtain ⟨c, hc, K, hK, hsob⟩ := exists_reflectedPrimePolarCost_le_exp_sub_sqrt_mul_sobolev
  refine ⟨c, hc, K, hK, fun r α F hr hα hF hFc hodd hsupp => ?_⟩
  have h1 := hsob r F hr hF hFc hodd hsupp
  have hd0 : 0 ≤ ∫ x, deriv F x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have h2 := mul_le_mul_of_nonneg_right hα hd0
  linarith

/-- **Simultaneous Bipartite Pure-Mass and de la Vallée Poussin Sobolev Envelope.**
Every real odd `F ∈ C¹_c[−r, r]` simultaneously obeys both the bipartite pure-mass bound
`(35 e^r + 34 e^{r/2} − 2r) ∫ F²` and the de la Vallée Poussin Sobolev bound
`K e^r exp(−c√r) (∫ F² + ½ ∫ (deriv F)²)`. -/
theorem exists_abs_reflectedPrimePolarCost_le_min_bipartite_and_sobolev :
    ∃ c > 0, ∃ K > 0, ∀ (r : ℝ) (F : ℝ → ℝ), 0 < r → ContDiff ℝ 1 F → HasCompactSupport F →
      (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
      |reflectedPrimePolarCost F r| ≤
        min ((35 * Real.exp r + 34 * Real.exp (r / 2) - 2 * r) * ∫ x, F x ^ 2)
          (K * Real.exp r * Real.exp (-c * Real.sqrt r) *
            ((∫ x, F x ^ 2) + (1 / 2) * ∫ x, deriv F x ^ 2)) := by
  obtain ⟨c, hc, K, hK, hsob⟩ := exists_abs_reflectedPrimePolarCost_le_exp_sub_sqrt_mul_sobolev
  refine ⟨c, hc, K, hK, fun r F hr hF hFc hodd hsupp => le_min ?_ ?_⟩
  · exact abs_reflectedPrimePolarCost_le_thirtyFive_exp_add_thirtyFour_exp_half
      hF.continuous hFc hodd hr hsupp
  · exact hsob r F hr hF hFc hodd hsupp

/-- **Automatic Pure-Mass Sub-Envelope Bound on Exponentially Growing Bandwidth Cones.**
With universal constants `c > 0` and `K > 0`, for every aperture `r > 0` and every real odd
`F ∈ C¹_c[−r, r]` whose Dirichlet energy satisfies `∫ (deriv F)² ≤ 2 exp(c√r) ∫ F²`, half of the
de la Vallée Poussin saving absorbs the derivative energy automatically, yielding the pure-mass
sub-envelope bound `|reflectedPrimePolarCost F r| ≤ K e^r exp(−c√r) ∫ F²`. -/
theorem exists_abs_reflectedPrimePolarCost_le_sub_envelope_of_dirichlet_le :
    ∃ c > 0, ∃ K > 0, ∀ (r : ℝ) (F : ℝ → ℝ), 0 < r → ContDiff ℝ 1 F → HasCompactSupport F →
      (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
      (∫ x, deriv F x ^ 2) ≤ 2 * Real.exp (c * Real.sqrt r) * (∫ x, F x ^ 2) →
      |reflectedPrimePolarCost F r| ≤
        K * Real.exp r * Real.exp (-c * Real.sqrt r) * ∫ x, F x ^ 2 := by
  obtain ⟨c₀, hc₀, K₀, hK₀, hsob⟩ := exists_abs_reflectedPrimePolarCost_le_exp_sub_sqrt_mul_sobolev
  set c := c₀ / 2
  have hc : 0 < c := half_pos hc₀
  set K := 2 * K₀
  have hK : 0 < K := by positivity
  refine ⟨c, hc, K, hK, fun r F hr hF hFc hodd hsupp hdir => ?_⟩
  have h1 := hsob r F hr hF hFc hodd hsupp
  have hexp_split : Real.exp (-c₀ * Real.sqrt r) =
      Real.exp (-c * Real.sqrt r) * Real.exp (-c * Real.sqrt r) := by
    rw [← Real.exp_add]
    congr 1
    simp only [c]
    ring
  have hexp_cancel : Real.exp (-c * Real.sqrt r) * Real.exp (c * Real.sqrt r) = 1 := by
    rw [← Real.exp_add, show -c * Real.sqrt r + c * Real.sqrt r = 0 by ring, Real.exp_zero]
  have hexp_le_one : Real.exp (-c * Real.sqrt r) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [hc, Real.sqrt_nonneg r])
  have hI0 : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  calc |reflectedPrimePolarCost F r|
      ≤ K₀ * Real.exp r * Real.exp (-c₀ * Real.sqrt r) *
          ((∫ x, F x ^ 2) + (1 / 2) * ∫ x, deriv F x ^ 2) := h1
    _ ≤ K₀ * Real.exp r * (Real.exp (-c * Real.sqrt r) * Real.exp (-c * Real.sqrt r)) *
          ((∫ x, F x ^ 2) + (1 / 2) * (2 * Real.exp (c * Real.sqrt r) * ∫ x, F x ^ 2)) := by
        rw [hexp_split]
        refine mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = K₀ * Real.exp r * Real.exp (-c * Real.sqrt r) *
          (Real.exp (-c * Real.sqrt r) +
            Real.exp (-c * Real.sqrt r) * Real.exp (c * Real.sqrt r)) *
          ∫ x, F x ^ 2 := by ring
    _ = K₀ * Real.exp r * Real.exp (-c * Real.sqrt r) *
          (Real.exp (-c * Real.sqrt r) + 1) * ∫ x, F x ^ 2 := by rw [hexp_cancel]
    _ ≤ K₀ * Real.exp r * Real.exp (-c * Real.sqrt r) * 2 * ∫ x, F x ^ 2 := by
        refine mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hI0
    _ = K * Real.exp r * Real.exp (-c * Real.sqrt r) * ∫ x, F x ^ 2 := by
        simp only [K]; ring

/-- Compression operator `compressTest a F x = F (a * x)`. For `a ≥ 1`, compressing a test
supported in `[−r, r]` keeps its support inside `[−r, r]` while scaling `∫ F²` by `a⁻¹` and
`∫ (deriv F)²` by `a`. -/
def compressTest (a : ℝ) (F : ℝ → ℝ) (x : ℝ) : ℝ := F (a * x)

theorem compressTest_odd {a : ℝ} {F : ℝ → ℝ} (hodd : ∀ x, F (-x) = -F x) (x : ℝ) :
    compressTest a F (-x) = -compressTest a F x := by
  unfold compressTest
  rw [mul_neg, hodd]

theorem compressTest_eq_zero_of_support {a r : ℝ} {F : ℝ → ℝ} (ha : 1 ≤ a)
    (hsupp : ∀ x, r < |x| → F x = 0) {x : ℝ} (hx : r < |x|) :
    compressTest a F x = 0 := by
  unfold compressTest
  refine hsupp (a * x) ?_
  have hx0 : 0 ≤ |x| := abs_nonneg x
  rw [abs_mul, abs_of_pos (by linarith : 0 < a)]
  nlinarith

theorem deriv_compressTest {a : ℝ} {F : ℝ → ℝ} (hF : Differentiable ℝ F) (x : ℝ) :
    deriv (compressTest a F) x = a * deriv F (a * x) := by
  unfold compressTest
  have h1 : HasDerivAt (fun y => a * y) a x := by
    simpa using (hasDerivAt_id x).const_mul a
  have h2 : HasDerivAt F (deriv F (a * x)) (a * x) := (hF (a * x)).hasDerivAt
  have h3 : HasDerivAt (fun y => F (a * y)) (deriv F (a * x) * a) x := h2.comp x h1
  rw [h3.deriv, mul_comm]

/-- **Exact Mass and Derivative-Energy Scaling of Compressed Tests.**
For every `a > 0` and `F ∈ C¹(ℝ)`, `∫ (compressTest a F)² = a⁻¹ ∫ F²` and
`∫ (deriv (compressTest a F))² = a ∫ (deriv F)²`, so the Dirichlet ratio `∫ (F')² / ∫ F²` scales
by `a²` at fixed aperture `[−r, r]` (`a ≥ 1`). -/
theorem integral_sq_and_deriv_sq_compressTest {a : ℝ} {F : ℝ → ℝ} (ha : 0 < a)
    (hF : Differentiable ℝ F) :
    (∫ x, compressTest a F x ^ 2) = a⁻¹ * (∫ x, F x ^ 2) ∧
    (∫ x, deriv (compressTest a F) x ^ 2) = a * ∫ x, deriv F x ^ 2 := by
  constructor
  · unfold compressTest
    simpa [abs_of_pos ha, smul_eq_mul] using
      MeasureTheory.Measure.integral_comp_mul_left (fun u => F u ^ 2) a
  · have hpt : (fun x => deriv (compressTest a F) x ^ 2) =
        fun x => a ^ 2 * deriv F (a * x) ^ 2 := by
      funext x
      rw [deriv_compressTest hF x]
      ring
    rw [hpt, MeasureTheory.integral_const_mul]
    have hcomp : (∫ x, deriv F (a * x) ^ 2) = a⁻¹ * ∫ u, deriv F u ^ 2 := by
      simpa [abs_of_pos ha, smul_eq_mul] using
        MeasureTheory.Measure.integral_comp_mul_left (fun u => deriv F u ^ 2) a
    rw [hcomp]
    field_simp

/-! ## §5. Structural Synthesis: High-Lag `1/2` Defect, Tower Bill, Comb Split, and Canonical Paths -/

/-- **Half-Mass Floor on the Shift Defect of an Odd Test Beyond the Aperture.**
For every continuous odd test `F` supported in `[−r, r]` and every lag `t ≥ r`,
`autoCorr F 0 / 2 ≤ shiftDefect F t`, doubling the chord-cascade `1/4` floor `quarter_le_shiftDefect`
of `PrimeDefectCoordinate` on odd tests. -/
theorem half_le_shiftDefect_of_odd {F : ℝ → ℝ} {r t : ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hsupp : ∀ y, r < |y| → F y = 0) (ht : r ≤ t) :
    autoCorr F 0 / 2 ≤ shiftDefect F t := by
  have h1 := (le_abs_self (autoCorrelation F t)).trans
    (abs_autoCorrelation_le_half_of_le hF hFc hodd hsupp ht)
  rw [← autoCorr_eq_autoCorrelation, ← autoCorr_zero_eq_integral_sq] at h1
  unfold shiftDefect
  linarith

/-- **The One-Half Law on the High Range for Odd Tests (`sum_atom_mul_autoCorr_le_half_of_odd`).**
For any set `s` of shifts with `r ≤ log n`, the prime charge of an odd test supported in `[−r, r]`
is at most `1/2` of the trivial `ℓ¹` bound (upgrading `sum_atom_mul_autoCorr_le_three_quarters`
from `3/4` to `1/2`). -/
theorem sum_atom_mul_autoCorr_le_half_of_odd {F : ℝ → ℝ} {r : ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) (hodd : ∀ x, F (-x) = -F x)
    (hsupp : ∀ y, r < |y| → F y = 0) (s : Finset ℕ) (hhigh : ∀ n ∈ s, r ≤ Real.log n) :
    ∑ n ∈ s, RHTower.vonMangoldtAtom n * autoCorr F (Real.log n) ≤
      (1 / 2) * (∑ n ∈ s, RHTower.vonMangoldtAtom n) * autoCorr F 0 := by
  have hdef : (autoCorr F 0 / 2) * (∑ n ∈ s, RHTower.vonMangoldtAtom n) ≤ primeDefect F s := by
    rw [Finset.mul_sum, primeDefect]
    refine Finset.sum_le_sum fun n hn => ?_
    have hd := half_le_shiftDefect_of_odd hF hFc hodd hsupp (hhigh n hn)
    have ha := vonMangoldtAtom_nonneg n
    calc autoCorr F 0 / 2 * RHTower.vonMangoldtAtom n
        = RHTower.vonMangoldtAtom n * (autoCorr F 0 / 2) := by ring
      _ ≤ RHTower.vonMangoldtAtom n * shiftDefect F (Real.log n) :=
          mul_le_mul_of_nonneg_left hd ha
  rw [sum_atom_mul_autoCorr_eq]
  linarith

/-- **Tower-Reduced Reflected Prime–Polar Bound (`reflectedPrimePolarCost_le_towerReduced_add_sinh`).**
Eliminating proper prime powers `p^k` (`k ≥ 2`) via `PrimeTowerLedgerReduction` bounds
`reflectedPrimePolarCost F r` by the first-power prime autocorrelation sum inflated by `p/(p − 1)`
plus the **tower diagonal bill** `(Σ_{p ∈ T} 2 log p/(p − 1)) ∫ F²` and the sharp polar variance
`(2 sinh r − 2r) ∫ F²`. -/
theorem reflectedPrimePolarCost_le_towerReduced_add_sinh {F : ℝ → ℝ} {r : ℝ}
    {T : Finset Nat.Primes} (hF : Continuous F) (hFc : HasCompactSupport F)
    (hodd : ∀ x, F (-x) = -F x) (hr : 0 < r) (hsupp : ∀ x, r < |x| → F x = 0)
    (hT : ∀ p : Nat.Primes, Real.log (p : ℕ) ≤ 2 * r → p ∈ T) :
    reflectedPrimePolarCost F r ≤
      (∑ p ∈ T, 2 * (Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1))) * (∫ x, F x ^ 2) +
        (∑ p ∈ T, 2 * (Real.sqrt (p : ℕ) * Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1)) *
          autoCorr F (Real.log (p : ℕ))) +
        (2 * Real.sinh r - 2 * r) * ∫ x, F x ^ 2 := by
  have heq := reflectedPrimePolarCost_eq_two_primeSide_add_poleCharge hF hodd hr.le hsupp
  have hbd := primeSideCharge_le_sum_primes hF hr.le hsupp hT
  have hpole := poleCharge_le_two_sinh_sub_two_r_mul_sq hF hFc hr hsupp
  have hsplit : 2 * (∑ p ∈ T, Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1) *
        (autoCorr F 0 + Real.sqrt (p : ℕ) * autoCorr F (Real.log (p : ℕ)))) =
      (∑ p ∈ T, 2 * (Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1))) * (∫ x, F x ^ 2) +
        ∑ p ∈ T, 2 * (Real.sqrt (p : ℕ) * Real.log (p : ℕ) / (((p : ℕ) : ℝ) - 1)) *
          autoCorr F (Real.log (p : ℕ)) := by
    rw [← autoCorr_zero_eq_integral_sq, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => by ring
  linarith

/-- **Exact Diagonal vs. Off-Diagonal Split of `combEnergy`.**
For every finite set `s` and weight `w : ℕ → ℝ`, the prime-comb energy `combEnergy F s w` splits
into the diagonal bill `(∑ p ∈ s, w p ^ 2) * autoCorr F 0` plus the full off-diagonal ratio-lag
sum `∑ p ∈ s, ∑ q ∈ s.erase p, w p * w q * autoCorr F (log q − log p)`. -/
theorem combEnergy_eq_diag_add_offDiag (F : ℝ → ℝ) (s : Finset ℕ) (w : ℕ → ℝ) :
    combEnergy F s w =
      (∑ p ∈ s, w p ^ 2) * autoCorr F 0 +
        ∑ p ∈ s, ∑ q ∈ s.erase p, w p * w q * autoCorr F (Real.log q - Real.log p) := by
  unfold combEnergy
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← Finset.add_sum_erase _ _ hp, sub_self, sq, mul_assoc]

/-- **Master Synthesis of Source-Faithful Canonical-Path Calibration and Global Incidence
Allocation.**
Unites the discrete source-faithful `weilLedgerKernel 1 1` canonical-path calibration with the
continuum incidence ledger:
1. Pairwise completeness fails on arithmetic log-grids (`not_isCompleteOverlap_oddFold_arithLogGrid`);
2. Source-blind prime-only local/path payment is empty on `{log 2, log 3, log 5}`
   (`isEmpty_pathCertificate_primeTriangle_primeKernel`);
3. Source-faithful full-form calibration (`weilLedgerKernel 1 1`) admits explicit positive
   supersolutions and packed canonical-path certificates (`primeTriangleCanonicalPathCertificate`,
   `packedPrimeCanonicalPathCertificate`), so `incidenceEnergy` is nonnegative for every test on
   both grids;
4. On the continuum side, `GlobalIncidenceAllocation` holds unconditionally on `(0, 181/500]`,
   satisfies `GradedIncidenceAllocation (1 / 2) 75` across all apertures, and achieves both the
   first-order (`∫ F² + ½ ∫ (F')²`) and second-order pole-tilted (`¼ ∫ F² + ∫ (F')²`)
   de la Vallée Poussin savings beyond the `e^r` envelope. -/
theorem sourceFaithful_canonicalPath_and_globalAllocation_synthesis :
    (∀ b : Fin 3 → ℝ, ¬ IsCompleteOverlap (oddFold arithLogGrid primeKernel b)) ∧
    (∀ b : Fin 3 → ℝ, IsEmpty (PathCertificate (oddFold primeTrianglePos primeKernel b))) ∧
    (∀ b : Fin 3 → ℝ, ¬ IsBalanced (oddFold primeTrianglePos (weilLedgerKernel 1 1) b)) ∧
    (∀ f : Fin 3 → ℝ,
      0 ≤ incidenceEnergy
        (oddFold primeTrianglePos (weilLedgerKernel 1 1) primeTriangleCanonicalBudget) f) ∧
    (∀ f : Fin 4 → ℝ,
      0 ≤ incidenceEnergy
        (oddFold packedPrimePos (weilLedgerKernel 1 1) packedPrimeCanonicalBudget) f) ∧
    GaloisForLFunctions.SquareRootThreshold.GradedIncidenceAllocation (1 / 2) 75 ∧
    (∀ (r R : ℝ) (F : ℝ → ℝ), 0 < r → r ≤ 181 / 500 → r < R →
      ContDiff ℝ 2 F → HasCompactSupport F →
      (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
      GlobalIncidenceAllocation r R F) :=
  ⟨not_isCompleteOverlap_oddFold_arithLogGrid,
    isEmpty_pathCertificate_primeTriangle_primeKernel,
    oddFold_primeTriangle_weilLedgerKernel_one_not_isBalanced,
    incidenceEnergy_oddFold_primeTriangleCanonical_nonneg,
    incidenceEnergy_oddFold_packedPrimeCanonical_nonneg,
    gradedIncidenceAllocation_half_seventyFive,
    fun _ _ _ hr hr0 hrR hF hFc hodd hsupp =>
      globalIncidenceAllocation_of_le_threeHundredSixtyTwoThousandths
        hF hFc hodd hr hr0 hsupp hrR⟩

end GaloisForLFunctions.ArithmeticIncidencePositivity

end
