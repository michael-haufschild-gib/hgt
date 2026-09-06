import GaloisForLFunctions.RHTower.WeilLagFunctionRecurrence
import GaloisForLFunctions.HTGeometry.BohrExponentialSeriesCoefficient
import GaloisForLFunctions.HTGeometry.BohrUniqueness
import GaloisForLFunctions.HTGeometry.BohrMeanMonotone
import GaloisForLFunctions.HTGeometry.BohrTrigPolynomial
import GaloisForLFunctions.HTGeometry.BohrProductUniformLimit

/-!
# The sign changes of the integer lags: an unconditional `Ω±(√n)` law

Under RH the lag function `Φ` is a Bohr almost-periodic exponential series with mean value zero
(no zero has ordinate `0`), so it cannot be eventually nonnegative: if it were, the vanishing lemma
would make it nonnegative everywhere, and a nonnegative almost-periodic function with mean zero
vanishes identically, contradicting `Φ(0) = 2 + γ − log 4π > 0`.  Hence `Φ ≤ −η` at arbitrarily
large lags for some `η > 0`.  A sharpened interval bound `|Φ(L) − a_{⌊e^L⌋}| ≤ 3(log n + 2)²/√n`
transfers this to the integer lags; without RH the integer lags are unbounded below anyway.

Together with the recurrence to the ceiling this gives, unconditionally, for the genus-kernel prime
error `E(n) = (n − ψ(n)) + n(Σ_{m≤n}Λ(m)/m − log n + γ) − log 2π + S(n)`:

`E(n) > (2 + γ − log 4π − ε)√n` infinitely often, and `E(n) ≤ −η√n` infinitely often.
-/

open Real Filter Topology
open GaloisForLFunctions GaloisForLFunctions.HTGeometry HTGeometry

namespace RHTower

noncomputable section

/-! ## The lag function as a Bohr exponential series -/

theorem summable_norm_cosWeight (h : RiemannHypothesis) :
    Summable fun q : XiZeroCopy => ‖(cosWeight q : ℂ)‖ := by
  refine (summable_cosWeight h).congr fun q => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (cosWeight_pos q)]

theorem weilLagFunction_eq_expSeriesCarrier (h : RiemannHypothesis) :
    weilLagFunction = expSeriesCarrier (fun q : XiZeroCopy => (cosWeight q : ℂ)) zeroOrdinate := by
  funext L
  unfold weilLagFunction expSeriesCarrier
  congr 1
  funext q
  rw [xiZeroCopy_eq_of_riemannHypothesis h q, half_add_mul_I_mul_one_sub]
  have e : (L : ℂ) * (1 / 2 + (zeroOrdinate q : ℂ) * Complex.I - 1 / 2)
      = ((zeroOrdinate q * L : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [e]
  unfold expChar cosWeight
  push_cast
  ring

theorem isBohrAlmostPeriodic_weilLagFunction (h : RiemannHypothesis) :
    IsBohrAlmostPeriodic weilLagFunction := by
  rw [weilLagFunction_eq_expSeriesCarrier h]
  exact isBohrAlmostPeriodic_expSeriesCarrier (summable_norm_cosWeight h) _

theorem continuous_weilLagFunction (h : RiemannHypothesis) : Continuous weilLagFunction := by
  rw [weilLagFunction_eq_expSeriesCarrier h]
  exact continuous_expSeriesCarrier (summable_norm_cosWeight h) _

/-- The Bohr coefficient of an absolutely convergent exponential series at a frequency that does
not occur is zero. -/
theorem bohrCoefficient_expSeriesCarrier_of_ne {ι : Type*} {a : ι → ℂ}
    (ha : Summable fun i => ‖a i‖) {omega : ι → ℝ} {lam : ℝ} (hne : ∀ i, omega i ≠ lam) :
    bohrCoefficient (expSeriesCarrier a omega) lam = 0 := by
  classical
  have hC := continuous_expSeriesCarrier ha omega
  have hA := isBohrAlmostPeriodic_expSeriesCarrier ha omega
  have key : ∀ ε : ℝ, 0 < ε → ‖bohrCoefficient (expSeriesCarrier a omega) lam‖ ≤ ε := by
    intro ε hε
    obtain ⟨S, hS⟩ := exists_finset_tsum_compl_lt ha hε
    set g : ℝ → ℂ := fun t => ∑ i ∈ S, a i * expChar (omega i) t with hg
    have hgC : Continuous g :=
      continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_expChar _)
    have hgA : IsBohrAlmostPeriodic g :=
      isBohrAlmostPeriodic_sum _ (fun i _ => continuous_const.mul (continuous_expChar _))
        (fun i _ => isBohrAlmostPeriodic_const_mul (a i) (isBohrAlmostPeriodic_expChar _))
    have hclose : ∀ t, ‖expSeriesCarrier a omega t - g t‖ ≤ ε := fun t =>
      (norm_expSeriesCarrier_sub_partial_le ha omega S t).trans (hS S le_rfl).le
    have h1 := norm_bohrCoefficient_sub_le hC hA hgC hgA hclose lam
    have h2 : bohrCoefficient g lam = 0 := by
      have : g = fun t => ∑ i ∈ S, a i * bohrExp (omega i) t := by
        funext t; simp only [hg, expChar_eq_bohrExp]
      rw [this, bohrCoefficient_trigPoly]
      exact Finset.sum_eq_zero fun i _ => by rw [if_neg (hne i)]
    rw [h2, sub_zero] at h1
    exact h1
  by_contra hne0
  have hpos : 0 < ‖bohrCoefficient (expSeriesCarrier a omega) lam‖ := norm_pos_iff.mpr hne0
  have := key _ (half_pos hpos)
  linarith

theorem bohrMean_eq_bohrCoefficient_zero (f : ℝ → ℂ) : bohrMean f = bohrCoefficient f 0 := by
  unfold bohrCoefficient
  congr 1
  funext t
  simp [bohrChar]

theorem zeroOrdinate_ne_zero (h : RiemannHypothesis) (q : XiZeroCopy) : zeroOrdinate q ≠ 0 := by
  intro h0
  apply xiZeroCopy_sub_half_ne_zero q
  rw [xiZeroCopy_eq_of_riemannHypothesis h q, h0]
  push_cast
  ring

/-- Under RH the lag function has Bohr mean zero. -/
theorem bohrMean_weilLagFunction (h : RiemannHypothesis) : bohrMean weilLagFunction = 0 := by
  rw [bohrMean_eq_bohrCoefficient_zero, weilLagFunction_eq_expSeriesCarrier h]
  exact bohrCoefficient_expSeriesCarrier_of_ne (summable_norm_cosWeight h)
    (fun q => zeroOrdinate_ne_zero h q)

theorem isBohrAlmostPeriodic_weilLagFunctionReal (h : RiemannHypothesis) :
    IsBohrAlmostPeriodic weilLagFunctionReal := by
  intro ε hε
  obtain ⟨L, hL, hτ⟩ := isBohrAlmostPeriodic_weilLagFunction h ε hε
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨τ, hτmem, hτx⟩ := hτ a
  refine ⟨τ, hτmem, fun x => ?_⟩
  have := hτx x
  rwa [weilLagFunction_eq_ofReal, weilLagFunction_eq_ofReal, ← Complex.ofReal_sub,
    Complex.norm_real] at this

/-- The negative part `max(−Φ, 0)`. -/
def lagNeg (L : ℝ) : ℝ := max (-(weilLagFunctionReal L)) 0

theorem isBohrAlmostPeriodic_lagNeg (h : RiemannHypothesis) : IsBohrAlmostPeriodic lagNeg := by
  intro ε hε
  obtain ⟨L, hL, hτ⟩ := isBohrAlmostPeriodic_weilLagFunctionReal h ε hε
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨τ, hτmem, hτx⟩ := hτ a
  refine ⟨τ, hτmem, fun x => ?_⟩
  have := hτx x
  rw [Real.norm_eq_abs] at this ⊢
  unfold lagNeg
  calc |max (-(weilLagFunctionReal (x + τ))) 0 - max (-(weilLagFunctionReal x)) 0|
      ≤ |(-(weilLagFunctionReal (x + τ))) - (-(weilLagFunctionReal x))| :=
        abs_max_sub_max_le_abs _ _ _
    _ = |weilLagFunctionReal (x + τ) - weilLagFunctionReal x| := by
        rw [show (-(weilLagFunctionReal (x + τ))) - (-(weilLagFunctionReal x))
          = -(weilLagFunctionReal (x + τ) - weilLagFunctionReal x) by ring, abs_neg]
    _ ≤ ε := this

/-- **The lag function is not eventually nonnegative (under RH).**  Some `η > 0` has
`Φ(L) ≤ −η` at arbitrarily large `L`. -/
theorem exists_weilLagFunctionReal_le_neg_of_riemannHypothesis (h : RiemannHypothesis) :
    ∃ η : ℝ, 0 < η ∧ ∀ L₀ : ℝ, ∃ L : ℝ, L₀ ≤ L ∧ weilLagFunctionReal L ≤ -η := by
  by_contra hcon
  push Not at hcon
  have h0 : Tendsto lagNeg atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨L₀, hL₀⟩ := hcon ε hε
    refine ⟨L₀, fun L hL => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (le_max_right _ _)]
    unfold lagNeg
    have := hL₀ L hL
    exact max_lt (by linarith) hε
  have hzero := eq_zero_of_isBohrAlmostPeriodic_of_tendsto_zero (isBohrAlmostPeriodic_lagNeg h) h0
  have hnn : ∀ L, 0 ≤ weilLagFunctionReal L := by
    intro L
    have h1 := hzero L
    unfold lagNeg at h1
    have h2 : -(weilLagFunctionReal L) ≤ 0 := by rw [← h1]; exact le_max_left _ _
    linarith
  have hΦ0 := eq_zero_of_bohrMean_eq_zero_of_nonneg (continuous_weilLagFunction h)
    (isBohrAlmostPeriodic_weilLagFunction h)
    (fun t => by rw [weilLagFunction_eq_ofReal, Complex.ofReal_re]; exact hnn t)
    (fun t => weilLagFunction_im_eq_zero t) (bohrMean_weilLagFunction h)
  have h1 := hΦ0 0
  rw [weilLagFunction_zero] at h1
  exact absurd (Complex.ofReal_eq_zero.mp h1) (ne_of_gt poleSharpConstant_pos)

/-! ## The sharpened interval bound -/

/-- The prime-side expression at `X ∈ [n, n+1)` differs from the one at `n` by at most
`3 (log n + 2)² / √n`. -/
theorem lag_interval_core_sharp {X L : ℝ} {n : ℕ} (hn2 : 2 ≤ n) (hnX : (n : ℝ) ≤ X)
    (hXn : X < n + 1) (hlogn : Real.log n ≤ L) (hLlog' : L ≤ Real.log n + 1 / n) :
    |(1 / Real.sqrt X) * ((X - Chebyshev.psi n) + X * (mertensSum n - L + eulerMascheroniConstant)
        - Real.log (2 * π) + trivialZeroSeriesReal X)
      - (1 / Real.sqrt n) * (((n : ℝ) - Chebyshev.psi n)
          + n * (mertensSum n - Real.log n + eulerMascheroniConstant)
          - Real.log (2 * π) + trivialZeroSeriesReal n)|
      ≤ 3 * (Real.log n + 2) ^ 2 / Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hinvn : (1 : ℝ) / n ≤ 1 := by rw [div_le_one hn0]; exact hn1
  have hLlog : L ≤ Real.log n + 1 := by linarith
  have hX0 : 0 < X := by linarith
  have hlog := log_le_two_sqrt hn0.le
  have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg hn1
  have hψn : Chebyshev.psi n ≤ 2 * n * Real.log n := psi_le_mul_log hn2
  have hψ0 : 0 ≤ Chebyshev.psi n := by
    rw [Chebyshev.psi_eq_sum_Icc]
    exact Finset.sum_nonneg fun _ _ => ArithmeticFunction.vonMangoldt_nonneg
  have hM0 := mertensSum_nonneg n
  have hMle := mertensSum_le hn2
  have hγ : eulerMascheroniConstant ≤ 1 := by
    have := Real.eulerMascheroniConstant_lt_two_thirds; linarith
  have hγ0 : 0 ≤ eulerMascheroniConstant := by have := eulerMascheroniConstant_gt; linarith
  have hS0 : 0 ≤ trivialZeroSeriesReal n := trivialZeroSeriesReal_nonneg hn1
  have hSX0 : 0 ≤ trivialZeroSeriesReal X := trivialZeroSeriesReal_nonneg (hn1.trans hnX)
  have hSle : trivialZeroSeriesReal X ≤ trivialZeroSeriesReal n := trivialZeroSeriesReal_anti hn1 hnX
  have hS1 : trivialZeroSeriesReal n ≤ 1 := trivialZeroSeriesReal_le_one hn1
  have hlog2π : Real.log (2 * π) ≤ 6 := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < 2 * π)
    have := Real.pi_lt_d2
    linarith
  have hlog2π0 : 0 ≤ Real.log (2 * π) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hgap := sqrt_succ_sub_sqrt_le hn1
  have hinv0 := inv_sqrt_sub_inv_sqrt_succ_le hn1
  have hsn_le : Real.sqrt n ≤ Real.sqrt X := Real.sqrt_le_sqrt hnX
  have hsX_lt : Real.sqrt X < Real.sqrt (n + 1) := Real.sqrt_lt_sqrt hX0.le hXn
  have hsXsq : Real.sqrt X * Real.sqrt X = X := Real.mul_self_sqrt hX0.le
  have hsnsq : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  have hsX0 : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hsn0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hsn1 : 1 ≤ Real.sqrt n := by
    have := Real.sqrt_le_sqrt hn1; rwa [Real.sqrt_one] at this
  set sX := Real.sqrt X with hsX
  set sn := Real.sqrt n with hsn
  set sn1 := Real.sqrt (n + 1) with hsn1'
  set ψ := Chebyshev.psi n with hψ
  set M := mertensSum n with hM
  set SX := trivialZeroSeriesReal X with hSX
  set Sn := trivialZeroSeriesReal n with hSn
  set l := Real.log (2 * π) with hl
  set γ := eulerMascheroniConstant with hγdef
  set ln := Real.log n with hln
  have hLln : L - ln ≤ 1 / (sn * sn) := by
    rw [hsnsq]; exact (by linarith : L - Real.log n ≤ 1 / n)
  clear_value sX sn sn1 ψ M SX Sn l γ ln
  have hexpand : (1 / sX) * ((X - ψ) + X * (M - L + γ) - l + SX)
      = sX - ψ / sX + sX * (M - L + γ) - l / sX + SX / sX := by
    rw [← hsXsq]; field_simp
  have hexpand' : (1 / sn) * (((n : ℝ) - ψ) + n * (M - ln + γ) - l + Sn)
      = sn - ψ / sn + sn * (M - ln + γ) - l / sn + Sn / sn := by
    rw [← hsnsq]; field_simp
  rw [hexpand, hexpand']
  set D := 1 / sn with hD
  have hD0 : 0 < D := by rw [hD]; positivity
  clear_value D
  have hgap' : sX - sn ≤ 1 / (2 * sn) := by linarith
  have hgapD : sX - sn ≤ (1 / 2) * D := by
    rw [hD]; have : 1 / (2 * sn) = (1 / 2) * (1 / sn) := by field_simp
    linarith
  have hinv : 1 / sn - 1 / sX ≤ 1 / (2 * (n * sn)) := by
    have : 1 / sn1 ≤ 1 / sX := one_div_le_one_div_of_le hsX0 hsX_lt.le
    linarith
  have hinv_nonneg : 0 ≤ 1 / sn - 1 / sX := by
    have := one_div_le_one_div_of_le hsn0 hsn_le; linarith
  have hinvD : 1 / sn - 1 / sX ≤ D := by
    rw [hD]; have : 0 < 1 / sX := by positivity
    linarith
  have hx2 : 2 ≤ ln + 2 := by linarith
  -- the six pieces, all in units of `D = 1/√n`
  have hP1 : sX - sn ≤ (1 / 2) * D := hgapD
  have hQ1 : 0 ≤ sX - sn := by linarith
  have hP2 : ψ * (1 / sn - 1 / sX) ≤ ln * D := by
    calc ψ * (1 / sn - 1 / sX) ≤ (2 * n * ln) * (1 / (2 * (n * sn))) :=
          mul_le_mul hψn hinv hinv_nonneg (by positivity)
      _ = ln * (1 / sn) := by field_simp
      _ = ln * D := by rw [hD]
  have hQ2 : 0 ≤ ψ * (1 / sn - 1 / sX) := mul_nonneg hψ0 hinv_nonneg
  have hb : |M - L + γ| ≤ (ln + 2) ^ 2 := by
    rw [abs_le]
    constructor
    · nlinarith only [hM0, hLlog, hγ0, hlogn0]
    · nlinarith only [hMle, hlogn, hγ, hlogn0]
  have hP3 : (sX - sn) * (M - L + γ) ≤ ((ln + 2) ^ 2 / 2) * D := by
    calc (sX - sn) * (M - L + γ) ≤ (sX - sn) * |M - L + γ| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) hQ1
      _ ≤ ((1 / 2) * D) * (ln + 2) ^ 2 := mul_le_mul hP1 hb (abs_nonneg _) (by positivity)
      _ = ((ln + 2) ^ 2 / 2) * D := by ring
  have hQ3 : -(((ln + 2) ^ 2 / 2) * D) ≤ (sX - sn) * (M - L + γ) := by
    have h1 : (sX - sn) * (-|M - L + γ|) ≤ (sX - sn) * (M - L + γ) :=
      mul_le_mul_of_nonneg_left (neg_abs_le _) hQ1
    have h2 : (sX - sn) * |M - L + γ| ≤ ((1 / 2) * D) * (ln + 2) ^ 2 :=
      mul_le_mul hP1 hb (abs_nonneg _) (by positivity)
    have h3 : (sX - sn) * (-|M - L + γ|) = -((sX - sn) * |M - L + γ|) := by ring
    have h4 : ((1 / 2) * D) * (ln + 2) ^ 2 = ((ln + 2) ^ 2 / 2) * D := by ring
    linarith only [h1, h2, h3, h4]
  have hP4 : l * (1 / sn - 1 / sX) ≤ 6 * D :=
    mul_le_mul hlog2π hinvD hinv_nonneg (by norm_num)
  have hQ4 : 0 ≤ l * (1 / sn - 1 / sX) := mul_nonneg hlog2π0 hinv_nonneg
  have hP5 : SX / sX - Sn / sn ≤ 0 := by
    have h1 : SX / sX ≤ Sn / sX := by gcongr
    have h2 : Sn / sX ≤ Sn / sn := by gcongr
    linarith
  have hQ5 : -D ≤ SX / sX - Sn / sn := by
    have h1 : 0 ≤ SX / sX := by positivity
    have h2 : Sn / sn ≤ 1 * D := by
      rw [hD, div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_right hS1 (by positivity)
    linarith
  have hP6 : sn * (ln - L) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hsn0.le (by linarith only [hlogn])
  have hQ6 : -D ≤ sn * (ln - L) := by
    have h1 : sn * (L - ln) ≤ sn * (1 / (sn * sn)) := mul_le_mul_of_nonneg_left hLln hsn0.le
    have h2 : sn * (1 / (sn * sn)) = 1 / sn := by field_simp
    have h4 : sn * (ln - L) = -(sn * (L - ln)) := by ring
    rw [hD]; linarith only [h1, h2, h4]
  -- assemble
  have key : (sX - ψ / sX + sX * (M - L + γ) - l / sX + SX / sX)
      - (sn - ψ / sn + sn * (M - ln + γ) - l / sn + Sn / sn)
      = (sX - sn) + ψ * (1 / sn - 1 / sX) + (sX - sn) * (M - L + γ) + sn * (ln - L)
        + l * (1 / sn - 1 / sX) + (SX / sX - Sn / sn) := by ring
  -- the polynomial comparisons
  have hpoly1 : (1 / 2) + ln + (ln + 2) ^ 2 / 2 + 6 ≤ 3 * (ln + 2) ^ 2 := by
    nlinarith only [hx2, hlogn0]
  have hpoly2 : (ln + 2) ^ 2 / 2 + 2 ≤ 3 * (ln + 2) ^ 2 := by
    nlinarith only [hx2, hlogn0]
  have hup : (sX - sn) + ψ * (1 / sn - 1 / sX) + (sX - sn) * (M - L + γ) + sn * (ln - L)
        + l * (1 / sn - 1 / sX) + (SX / sX - Sn / sn)
      ≤ (3 * (ln + 2) ^ 2) * D := by
    have h1 : (sX - sn) + ψ * (1 / sn - 1 / sX) + (sX - sn) * (M - L + γ) + sn * (ln - L)
        + l * (1 / sn - 1 / sX) + (SX / sX - Sn / sn)
        ≤ (1 / 2) * D + ln * D + ((ln + 2) ^ 2 / 2) * D + 0 + 6 * D + 0 :=
      add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hP1 hP2) hP3) hP6) hP4) hP5
    have h2 : (1 / 2) * D + ln * D + ((ln + 2) ^ 2 / 2) * D + 0 + 6 * D + 0
        = ((1 / 2) + ln + (ln + 2) ^ 2 / 2 + 6) * D := by ring
    have h3 : ((1 / 2) + ln + (ln + 2) ^ 2 / 2 + 6) * D ≤ (3 * (ln + 2) ^ 2) * D :=
      mul_le_mul_of_nonneg_right hpoly1 hD0.le
    linarith only [h1, h2, h3]
  have hlow : -((3 * (ln + 2) ^ 2) * D)
      ≤ (sX - sn) + ψ * (1 / sn - 1 / sX) + (sX - sn) * (M - L + γ) + sn * (ln - L)
        + l * (1 / sn - 1 / sX) + (SX / sX - Sn / sn) := by
    have h1 : 0 + 0 + (-(((ln + 2) ^ 2 / 2) * D)) + (-D) + 0 + (-D)
        ≤ (sX - sn) + ψ * (1 / sn - 1 / sX) + (sX - sn) * (M - L + γ) + sn * (ln - L)
          + l * (1 / sn - 1 / sX) + (SX / sX - Sn / sn) :=
      add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hQ1 hQ2) hQ3) hQ6) hQ4) hQ5
    have h2 : 0 + 0 + (-(((ln + 2) ^ 2 / 2) * D)) + (-D) + 0 + (-D)
        = -(((ln + 2) ^ 2 / 2 + 2) * D) := by ring
    have h3 : ((ln + 2) ^ 2 / 2 + 2) * D ≤ (3 * (ln + 2) ^ 2) * D :=
      mul_le_mul_of_nonneg_right hpoly2 hD0.le
    linarith only [h1, h2, h3]
  have hD' : 3 * (ln + 2) ^ 2 / sn = (3 * (ln + 2) ^ 2) * D := by rw [hD]; ring
  rw [hD', abs_le]
  constructor
  · linarith only [key, hlow]
  · linarith only [key, hup]

/-- For `L ≥ log 2` with `n = ⌊e^L⌋`: `|Φ(L) − a_n| ≤ 3 (log n + 2)² / √n`. -/
theorem abs_weilLagFunctionReal_sub_integerLag_le {L : ℝ} (hL : Real.log 2 ≤ L) :
    |weilLagFunctionReal L - integerLag ⌊Real.exp L⌋₊|
      ≤ 3 * (Real.log ⌊Real.exp L⌋₊ + 2) ^ 2 / Real.sqrt ⌊Real.exp L⌋₊ := by
  have hX2 : (2 : ℝ) ≤ Real.exp L := by
    rw [← Real.exp_log (by norm_num : (0:ℝ) < 2)]; exact Real.exp_le_exp.mpr hL
  have hX0 : 0 < Real.exp L := Real.exp_pos L
  have hnX : (⌊Real.exp L⌋₊ : ℝ) ≤ Real.exp L := Nat.floor_le hX0.le
  have hXn : Real.exp L < ⌊Real.exp L⌋₊ + 1 := Nat.lt_floor_add_one _
  have hn2 : 2 ≤ ⌊Real.exp L⌋₊ := Nat.le_floor (by exact_mod_cast hX2)
  have hn0 : (0 : ℝ) < ⌊Real.exp L⌋₊ := by exact_mod_cast (by omega : 0 < ⌊Real.exp L⌋₊)
  have hL0 : 0 < L := by
    have := Real.log_pos (by norm_num : (1:ℝ) < 2); linarith
  have hlogn : Real.log ⌊Real.exp L⌋₊ ≤ L := by
    have := Real.log_le_log hn0 hnX; rwa [Real.log_exp] at this
  have hLlog : L ≤ Real.log ⌊Real.exp L⌋₊ + 1 / ⌊Real.exp L⌋₊ := by
    have h2 : Real.log (Real.exp L) - Real.log ⌊Real.exp L⌋₊
        = Real.log (Real.exp L / ⌊Real.exp L⌋₊) := by
      rw [Real.log_div hX0.ne' hn0.ne']
    have h3 : Real.log (Real.exp L / ⌊Real.exp L⌋₊) ≤ Real.exp L / ⌊Real.exp L⌋₊ - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h4 : Real.exp L / ⌊Real.exp L⌋₊ - 1 < 1 / ⌊Real.exp L⌋₊ := by
      rw [div_sub_one hn0.ne', div_lt_div_iff_of_pos_right hn0]; linarith
    rw [Real.log_exp] at h2
    linarith
  have hψ : Chebyshev.psi (Real.exp L) = Chebyshev.psi ⌊Real.exp L⌋₊ := by
    rw [Chebyshev.psi_eq_sum_Icc, Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
  rw [weilLagFunctionReal_eq_prime_side hL0, hψ, integerLag_eq hn2,
    show Real.exp (-L / 2) = 1 / Real.sqrt (Real.exp L) by
      rw [neg_div, Real.exp_neg, Real.exp_half, one_div]]
  exact lag_interval_core_sharp hn2 hnX hXn hlogn hLlog

/-- The interval gap tends to zero. -/
theorem tendsto_lagGap :
    Tendsto (fun n : ℕ => 3 * (Real.log n + 2) ^ 2 / Real.sqrt n) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => 300 * ((n : ℝ) ^ (-(1 / 4 : ℝ)))) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 1 / 4)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa [Function.comp_def] using this.const_mul 300
  refine squeeze_zero' ?_ ?_ h1
  · filter_upwards with n; positivity
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0:ℝ) ≤ n := by linarith
    have hnpos : (0:ℝ) < n := by linarith
    have hlog : Real.log n ≤ 8 * (n:ℝ) ^ (1 / 8 : ℝ) := by
      have := Real.log_le_rpow_div hn0 (by norm_num : (0:ℝ) < 1 / 8); linarith
    have hr1 : (1:ℝ) ≤ (n:ℝ) ^ (1 / 8 : ℝ) := Real.one_le_rpow hn1 (by norm_num)
    have hsq : ((n:ℝ) ^ (1 / 8 : ℝ)) ^ 2 = (n:ℝ) ^ (1 / 4 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hn0]; norm_num
    have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
    have hbound : (Real.log n + 2) ^ 2 ≤ 100 * (n:ℝ) ^ (1 / 4 : ℝ) := by
      have : Real.log n + 2 ≤ 10 * (n:ℝ) ^ (1 / 8 : ℝ) := by linarith
      calc (Real.log n + 2) ^ 2 ≤ (10 * (n:ℝ) ^ (1 / 8 : ℝ)) ^ 2 :=
            pow_le_pow_left₀ (by linarith) this 2
        _ = 100 * ((n:ℝ) ^ (1 / 8 : ℝ)) ^ 2 := by ring
        _ = 100 * (n:ℝ) ^ (1 / 4 : ℝ) := by rw [hsq]
    have hsqrt : Real.sqrt n = (n:ℝ) ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow n
    have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hnpos
    rw [div_le_iff₀ hsqrt_pos]
    have hmul : (n:ℝ) ^ (-(1 / 4 : ℝ)) * Real.sqrt n = (n:ℝ) ^ (1 / 4 : ℝ) := by
      rw [hsqrt, ← Real.rpow_add hnpos]; norm_num
    calc 3 * (Real.log n + 2) ^ 2 ≤ 3 * (100 * (n:ℝ) ^ (1 / 4 : ℝ)) := by gcongr
      _ = 300 * ((n:ℝ) ^ (-(1 / 4 : ℝ)) * Real.sqrt n) := by rw [hmul]; ring
      _ = 300 * (n:ℝ) ^ (-(1 / 4 : ℝ)) * Real.sqrt n := by ring

/-! ## The sign changes of the integer lags -/

/-- Under RH some `η > 0` has `a_n ≤ −η` for infinitely many `n`. -/
theorem frequently_integerLag_le_neg_of_riemannHypothesis (h : RiemannHypothesis) :
    ∃ η : ℝ, 0 < η ∧ ∃ᶠ n : ℕ in atTop, integerLag n ≤ -η := by
  obtain ⟨η, hη, hL⟩ := exists_weilLagFunctionReal_le_neg_of_riemannHypothesis h
  refine ⟨η / 2, by linarith, ?_⟩
  rw [Filter.frequently_atTop]
  intro N
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    (tendsto_lagGap.eventually_lt_const (by linarith : (0:ℝ) < η / 2))
  have hK0 : (0 : ℝ) < ((N + N₁ + 1 : ℕ) : ℝ) := by positivity
  obtain ⟨L, hLge, hLle⟩ := hL (max (Real.log 2) (Real.log ((N + N₁ + 1 : ℕ) : ℝ)))
  have hL2 : Real.log 2 ≤ L := le_trans (le_max_left _ _) hLge
  have hnK : N + N₁ + 1 ≤ ⌊Real.exp L⌋₊ := by
    apply Nat.le_floor
    rw [← Real.exp_log hK0]
    exact Real.exp_le_exp.mpr (le_trans (le_max_right _ _) hLge)
  have hgap := abs_weilLagFunctionReal_sub_integerLag_le hL2
  have hsmall := hN₁ _ (by omega : N₁ ≤ ⌊Real.exp L⌋₊)
  refine ⟨⌊Real.exp L⌋₊, by omega, ?_⟩
  have := (abs_le.mp hgap).1
  linarith

/-- **The integer lags are `Ω₋`, unconditionally.**  Some `η > 0` has `a_n ≤ −η` for infinitely
many `n`: under RH by almost periodicity and the vanishing mean, otherwise by unboundedness. -/
theorem frequently_integerLag_le_neg :
    ∃ η : ℝ, 0 < η ∧ ∃ᶠ n : ℕ in atTop, integerLag n ≤ -η := by
  classical
  by_cases h : RiemannHypothesis
  · exact frequently_integerLag_le_neg_of_riemannHypothesis h
  · refine ⟨1, one_pos, ?_⟩
    rw [Filter.frequently_atTop]
    intro N
    rcases integerLag_dichotomy with hbd | ⟨-, hlow⟩
    · exact absurd (riemannHypothesis_iff_integerLag_le_sharp.mpr
        fun n _ => (le_abs_self _).trans (hbd n)) h
    · obtain ⟨B, hB⟩ := Finset.exists_le ((Finset.range N).image fun n => -integerLag n)
      obtain ⟨n, hn2, hn⟩ := hlow (min (-B) (-1))
      refine ⟨n, ?_, ?_⟩
      · by_contra hlt
        push Not at hlt
        have := hB _ (Finset.mem_image_of_mem (fun n => -integerLag n) (Finset.mem_range.mpr hlt))
        linarith [min_le_left (-B) (-1)]
      · linarith [min_le_right (-B) (-1)]

/-! ## RH as almost periodicity -/

/-- The lag function is continuous (unconditionally): the zero series converges uniformly on
bounded sets. -/
theorem continuous_weilLagFunction_unconditional : Continuous weilLagFunction := by
  rw [continuous_iff_continuousAt]
  intro L₀
  have hR : 0 < |L₀| + 1 := by positivity
  refine ContinuousOn.continuousAt (s := Metric.ball 0 (|L₀| + 1)) ?_
    (Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]; linarith))
  unfold weilLagFunction
  refine continuousOn_tsum (u := fun q => Real.exp ((|L₀| + 1) / 2) * ‖lagWeight q‖)
    (fun q => (by fun_prop : Continuous fun L : ℝ =>
      Complex.exp (L * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).continuousOn)
    (summable_norm_lagWeight.mul_left _) fun q L hL => ?_
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hL
  refine (norm_weilLagTerm_le L q).trans ?_
  unfold lagWeight
  gcongr

/-- **RH ⟺ the lag function is Bohr almost periodic.** -/
theorem riemannHypothesis_iff_isBohrAlmostPeriodic_weilLagFunction :
    RiemannHypothesis ↔ IsBohrAlmostPeriodic weilLagFunction := by
  refine ⟨isBohrAlmostPeriodic_weilLagFunction, fun hap => ?_⟩
  obtain ⟨C, hC⟩ := exists_bound_of_isBohrAlmostPeriodic continuous_weilLagFunction_unconditional hap
  exact riemannHypothesis_iff_weilLagFunction_bounded.mpr ⟨C, hC⟩

/-- The genus-kernel prime error `E(n)`. -/
def genusKernelError (n : ℕ) : ℝ :=
  ((n : ℝ) - Chebyshev.psi n) + n * (mertensSum n - Real.log n + eulerMascheroniConstant)
    - Real.log (2 * π) + trivialZeroSeriesReal n

theorem integerLag_eq_genusKernelError_div {n : ℕ} (hn : 2 ≤ n) :
    integerLag n = genusKernelError n / Real.sqrt n := by
  rw [integerLag_eq hn]; unfold genusKernelError; ring

/-- **The unconditional `Ω±(√n)` law for the genus-kernel prime error.**
`E(n) > (2 + γ − log 4π − ε)√n` for infinitely many `n`, for every `ε > 0`; and for some `η > 0`,
`E(n) ≤ −η√n` for infinitely many `n`. -/
theorem genusKernelError_omega_pm :
    (∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop,
        (poleSharpConstant - ε) * Real.sqrt n < genusKernelError n) ∧
      ∃ η : ℝ, 0 < η ∧ ∃ᶠ n : ℕ in atTop, genusKernelError n ≤ -η * Real.sqrt n := by
  constructor
  · intro ε hε
    have h1 := (frequently_integerLag_gt ε hε).and_eventually (eventually_ge_atTop 2)
    refine h1.mono fun n ⟨hn, hn2⟩ => ?_
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
    rw [integerLag_eq_genusKernelError_div hn2, lt_div_iff₀ hs] at hn
    exact hn
  · obtain ⟨η, hη, hfreq⟩ := frequently_integerLag_le_neg
    refine ⟨η, hη, ?_⟩
    have h1 := hfreq.and_eventually (eventually_ge_atTop 2)
    refine h1.mono fun n ⟨hn, hn2⟩ => ?_
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
    rw [integerLag_eq_genusKernelError_div hn2, div_le_iff₀ hs] at hn
    linarith

end

end RHTower
