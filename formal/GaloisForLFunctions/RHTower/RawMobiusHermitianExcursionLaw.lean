import GaloisForLFunctions.RHTower.TwistedOrderLawTheta
import GaloisForLFunctions.RHTower.MobiusEvenIndexPositiveRecurrence
import GaloisForLFunctions.RHTower.ZetaZeroAbscissa
import GaloisForLFunctions.RHTower.MixedConvolutionSubpowerAbelBound
import GaloisForLFunctions.HTGeometry.LogOrderLimsupBound

/-!
# The raw Hermitian positive-excursion law

The raw `2k`-fold Hermitian additive convolution of a reciprocal coefficient sequence has
logarithmic order pinned between the zero frontier and the composition count,

`2k Θ - 1 ≤ Ψ_k ≤ 2k - 1`,

for the Riemann zeta case (`rawOrder_moebius_bounds`) exactly as for a primitive twist.  The lower
edge is the radial Abel bound `‖A(e^{-x})‖ = O(x^{-(α+1)/(2k)})` extracted from a one-sided
coefficient bound, contradicted at any zero right of that exponent.

Because `Θ ≥ 1/2` the lower edge is positive from order two on, giving unconditional near-critical
positive excursions `R_k(N) ≥ (N+1)^{k-1-ε}` at infinitely many `N`
(`frequently_rpow_le_rawMixed_moebius`, `frequently_rpow_le_rawMixed_twisted`), and at the binary
endpoint integrality upgrades positivity to `∑_{a+b=N} μ(a) μ(b) ≥ 1`
(`frequently_one_le_moebiusBinaryCorrelation_raw`).
-/

open Complex Filter
open scoped ArithmeticFunction.Moebius LSeries.notation Topology BigOperators

namespace RHTower

noncomputable section

/-! ### The zeta case: the lower edge from a raw one-sided bound -/

/-- A global one-sided subpower bound on the raw Hermitian convolution powers of the Möbius
coefficients forces the decay exponent past the zeta zero abscissa. -/
theorem zetaZeroAbscissa_le_of_rawMixed_subpower {k : ℕ} {α C : ℝ} (hk : 0 < k)
    (hα : 0 ≤ α) (hC : 0 ≤ C)
    (hupper : ∀ N : ℕ, (mixedAdditiveConvolutionPower moebiusCoeffC k N).re
      ≤ C * ((N : ℝ) + 1) ^ α) :
    zetaZeroAbscissa ≤ (α + 1) / (2 * (k : ℝ)) := by
  by_contra hcon
  push Not at hcon
  have hkR : (0 : ℝ) < 2 * (k : ℝ) := by
    have : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
    linarith
  set b : ℝ := (α + 1) / (2 * (k : ℝ)) with hbdef
  have hb0 : 0 ≤ b := by rw [hbdef]; positivity
  have hAbel : 0 ≤ mixedSubpowerAbelConstant α := mixedSubpowerAbelConstant_nonneg hα
  have hconst : (0 : ℝ) ≤ C * mixedSubpowerAbelConstant α := mul_nonneg hC hAbel
  have hO : moebiusProfile =O[𝓝[>] (0 : ℝ)] fun x : ℝ => x ^ (-b) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨(C * mixedSubpowerAbelConstant α) ^ ((2 * (k : ℝ))⁻¹), ?_⟩
    have hev : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), x < 1 :=
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hev] with x hx hx1
    have hxpos : (0 : ℝ) < x := hx
    have hr0 : (0 : ℝ) ≤ Real.exp (-x) := (Real.exp_pos _).le
    have hr1 : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have hsum := GaloisForLFunctions.HTGeometry.summable_norm_coeff_mul_pow
      norm_moebiusCoeff_le_one hr0 hr1
    have hbound := norm_tsum_le_of_mixedAdditiveConvolutionPower_subpower
      hk hα hC hxpos hx1.le hsum hupper
    have hprofile : moebiusProfile x = ∑' N : ℕ, moebiusCoeffC N * ((Real.exp (-x) : ℝ) : ℂ) ^ N :=
      GaloisForLFunctions.HTGeometry.coeffLaplaceProfile_eq_tsum_pow _ x
    rw [hprofile, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hxpos _)]
    refine hbound.trans (le_of_eq ?_)
    congr 1
    rw [one_div, Real.inv_rpow hxpos.le, ← Real.rpow_neg hxpos.le]
  obtain ⟨ρ, hρz, hρ1, hbρ⟩ := exists_zetaZero_mem_openStrip_lt_re hcon
  exact not_isBigO_moebiusProfile_rpow hb0 hρz hρ1 hbρ hO

/-- The raw logarithmic order exponent `Ψ_k` of the Möbius Hermitian convolution powers. -/
def mobiusRawHermitianOrder (k : ℕ) : ℝ :=
  Filter.limsup
    (fun N : ℕ => Real.log (1 + max (mixedAdditiveConvolutionPower moebiusCoeffC k N).re 0)
      / Real.log ((N : ℝ) + 1)) Filter.atTop

/-- **The zeta lower edge of `(R3)`.**  `2k Θ - 1 ≤ Ψ_k`. -/
theorem le_mobiusRawHermitianOrder (j : ℕ) :
    2 * ((j : ℝ) + 1) * zetaZeroAbscissa - 1 ≤ mobiusRawHermitianOrder (j + 1) := by
  have hkR : (0 : ℝ) < 2 * (((j + 1 : ℕ) : ℝ)) := by
    have : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
    linarith
  refine le_limsup_of_no_subpower_below (D := 2 * j + 1) (fun M => ?_) fun α C hα hC hlt => ?_
  · exact (Complex.re_le_norm _).trans
      (norm_mixedAdditiveConvolutionPower_le_pow norm_moebiusCoeff_le_one j M)
  · intro hupper
    have hkey := zetaZeroAbscissa_le_of_rawMixed_subpower (k := j + 1) (Nat.succ_pos j)
      hα hC hupper
    rw [le_div_iff₀ hkR] at hkey
    push_cast at hlt hkey
    nlinarith [hlt, hkey]

/-- **The zeta upper edge of `(R3)`.**  `Ψ_k ≤ 2k - 1`. -/
theorem mobiusRawHermitianOrder_le (j : ℕ) :
    mobiusRawHermitianOrder (j + 1) ≤ 2 * ((j : ℝ) + 1) - 1 := by
  have h := limsup_log_mixedAdditiveConvolutionPower_re_le norm_moebiusCoeff_le_one j
  refine h.trans (le_of_eq ?_)
  push_cast
  ring

/-- **The zeta raw order law `(R3)`.** -/
theorem rawOrder_moebius_bounds (j : ℕ) :
    2 * ((j : ℝ) + 1) * zetaZeroAbscissa - 1 ≤ mobiusRawHermitianOrder (j + 1) ∧
      mobiusRawHermitianOrder (j + 1) ≤ 2 * ((j : ℝ) + 1) - 1 :=
  ⟨le_mobiusRawHermitianOrder j, mobiusRawHermitianOrder_le j⟩

/-! ### Unconditional positive excursions -/

/-- **`(R5)` for zeta.**  From order two on, the raw Hermitian convolution exceeds
`(N+1)^{k-1-ε}` at infinitely many `N`. -/
theorem frequently_rpow_le_rawMixed_moebius {j : ℕ} (hj : 1 ≤ j) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ N : ℕ in atTop,
      ((N : ℝ) + 1) ^ ((j : ℝ) + 1 - 1 - ε)
        ≤ (mixedAdditiveConvolutionPower moebiusCoeffC (j + 1) N).re := by
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  set α : ℝ := (j : ℝ) + 1 - 1 - ε with hαdef
  set lam : ℝ := max α 0 with hlamdef
  have hlam0 : 0 ≤ lam := le_max_right _ _
  have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hev : ∀ᶠ N : ℕ in atTop,
      (mixedAdditiveConvolutionPower moebiusCoeffC (j + 1) N).re ≤ ((N : ℝ) + 1) ^ lam := by
    filter_upwards [hcon] with N hN
    have hbase : (1 : ℝ) ≤ (N : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) N
      linarith
    refine le_trans (le_of_lt (not_le.mp hN)) ?_
    exact Real.rpow_le_rpow_of_exponent_le hbase (le_max_left _ _)
  obtain ⟨C, hC0, hCbound⟩ :=
    GaloisForLFunctions.HTGeometry.exists_global_subpower_of_eventually_le hlam0 hev
  have hkey := zetaZeroAbscissa_le_of_rawMixed_subpower (k := j + 1) (Nat.succ_pos j)
    hlam0 hC0 hCbound
  have hcast : ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
  rw [hcast, le_div_iff₀ (by linarith : (0 : ℝ) < 2 * ((j : ℝ) + 1))] at hkey
  have hΘ := half_le_zetaZeroAbscissa
  rcases le_or_gt α 0 with h | h
  · rw [hlamdef, max_eq_right h] at hkey
    nlinarith [hkey, hΘ]
  · rw [hlamdef, max_eq_left h.le, hαdef] at hkey
    nlinarith [hkey, hΘ]

/-- **`(R6)`.**  The binary additive Möbius self-convolution is at least `1` at infinitely many
totals. -/
theorem frequently_one_le_moebiusBinaryCorrelation_raw :
    ∃ᶠ N : ℕ in atTop, 1 ≤ moebiusBinaryCorrelation N := by
  have h := frequently_one_le_moebiusBinaryCorrelation
  rw [Filter.frequently_atTop] at h ⊢
  intro a
  obtain ⟨q, hq, hval⟩ := h a
  exact ⟨2 * q, by omega, hval⟩

/-! ### The twisted case -/

/-- **`(R3)` for a primitive twist.** -/
theorem rawOrder_twisted_bounds {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (j : ℕ) :
    2 * ((j : ℝ) + 1) * zeroAbscissa χ - 1 ≤ Filter.limsup
        (fun M => Real.log (1 + max (mixedAdditiveConvolutionPower (↗χ * ↗μ) (j + 1) M).re 0)
          / Real.log ((M : ℝ) + 1)) atTop ∧
      Filter.limsup
        (fun M => Real.log (1 + max (mixedAdditiveConvolutionPower (↗χ * ↗μ) (j + 1) M).re 0)
          / Real.log ((M : ℝ) + 1)) atTop ≤ 2 * ((j : ℝ) + 1) - 1 := by
  refine ⟨two_mul_zeroAbscissa_sub_one_le_limsup hχ hprim, ?_⟩
  refine (limsup_log_mixedAdditiveConvolutionPower_re_le
    (norm_twistedMobiusCoeff_le_one χ) j).trans (le_of_eq ?_)
  push_cast
  ring

/-- **`(R5)` for a primitive twist.** -/
theorem frequently_rpow_le_rawMixed_twisted {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) {j : ℕ} (hj : 1 ≤ j) {ε : ℝ} (hε : 0 < ε) :
    ∃ᶠ M : ℕ in atTop,
      ((M : ℝ) + 1) ^ ((j : ℝ) + 1 - 1 - ε)
        ≤ (mixedAdditiveConvolutionPower (↗χ * ↗μ) (j + 1) M).re := by
  by_contra hcon
  rw [Filter.not_frequently] at hcon
  set α : ℝ := (j : ℝ) + 1 - 1 - ε with hαdef
  set lam : ℝ := max α 0 with hlamdef
  have hlam0 : 0 ≤ lam := le_max_right _ _
  have hjR : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hkR : (0 : ℝ) < 2 * (((j + 1 : ℕ) : ℝ)) := by
    have : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
    linarith
  have hev : ∀ᶠ M : ℕ in atTop,
      (mixedAdditiveConvolutionPower (↗χ * ↗μ) (j + 1) M).re ≤ ((M : ℝ) + 1) ^ lam := by
    filter_upwards [hcon] with M hM
    have hbase : (1 : ℝ) ≤ (M : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) M
      linarith
    refine le_trans (le_of_lt (not_le.mp hM)) ?_
    exact Real.rpow_le_rpow_of_exponent_le hbase (le_max_left _ _)
  obtain ⟨C, hC0, hCbound⟩ :=
    GaloisForLFunctions.HTGeometry.exists_global_subpower_of_eventually_le hlam0 hev
  have hΘ := half_le_zeroAbscissa hχ hprim
  have hb : (lam + 1) / (2 * (((j + 1 : ℕ) : ℝ))) < zeroAbscissa χ := by
    rw [div_lt_iff₀ hkR]
    push_cast
    rcases le_or_gt α 0 with h | h
    · rw [hlamdef, max_eq_right h]
      nlinarith
    · rw [hlamdef, max_eq_left h.le, hαdef]
      nlinarith
  obtain ⟨ρ, hzero, hρre⟩ := exists_zero_lt_re hχ hprim hb
  exact not_twistedMixedSubpower_of_LFunction_eq_zero hχ (Nat.succ_pos j) hlam0 hC0 hzero hρre
    hCbound

end

end RHTower
