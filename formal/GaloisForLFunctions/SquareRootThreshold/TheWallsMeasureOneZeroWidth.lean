import GaloisForLFunctions.SquareRootThreshold.LagRateBoundsTheDeBruijnNewmanHeatTime
import GaloisForLFunctions.BiScaleUncertainty.BandSpectrumZeroWidthLaw
import GaloisForLFunctions.BiScaleUncertainty.PrimeWindowCeilingWidthLaw
import GaloisForLFunctions.RHTower.QuasiRHMeanSquareAbscissa
import GaloisForLFunctions.RHTower.CrossRouteReceiverBridges
import GaloisForLFunctions.RHTower.DeBruijnNewmanConstant
import GaloisForLFunctions.RHTower.PrimeBlindNodeCriticality
import GaloisForLFunctions.RHTower.BalazardSaiasYorZeroSum
import GaloisForLFunctions.ArithmeticCriticalityTheory.RestrictedWeilGroundEnergyCriticalAtInfinity

/-!
# The obstructions measure one zero width

The obstructions met by direct attacks on the Riemann hypothesis are stated in different
languages: a square-root error term for prime sums, the strip containing the zeros, the growth
of the Chebyshev mean square, the excess of the prime window ceiling over its polar value, the
negativity rate of the one-parameter lag family, the decay of the restricted Weil ground energy,
the de Bruijn–Newman heat time, the Balazard–Saias–Yor integral and the node-critical blind cone.
This module proves that they all read one number, the zero width
`zetaZeroWidth = sup |Re ρ − ½|`, and records the direction of every reading.

* **Three languages, one number.** `zetaZeroWidth = zetaZeroAbscissa − ½`
  (`zetaZeroWidth_eq_zetaZeroAbscissa_sub_half`); for `σ ≥ 0` the statements `zetaZeroWidth ≤ σ`,
  `zetaZeroAbscissa ≤ ½ + σ`, `XiZeroHalfPlaneBound σ` and
  `∀ ρ ∈ zetaZeroConfig.carrier, Re ρ ≤ ½ + σ` are equivalent
  (`zetaZeroWidth_le_iff_zetaZeroAbscissa_le`, `zetaZeroWidth_le_iff_xiZeroHalfPlaneBound`).
* **Prime side.** For `0 ≤ σ < ½`: `zetaZeroWidth ≤ σ` iff the integrated Chebyshev deficit
  `D(T) = ∫₀ᵀ (eᵗ − ψ(eᵗ)) dt` obeys the one-sided bound `D(T) ≤ B(1 + T)e^{(½ + β)T}` for every
  `β > σ` (`zetaZeroWidth_le_iff_forall_deficitPrimitive_le`, mirror
  `zetaZeroWidth_le_iff_forall_deficitPrimitive_ge`); iff the mean-square band, the Laplace
  energy and the spectral band grow at every rate above `σ`
  (`zetaZeroWidth_le_iff_forall_meanSquareBandRate`, `…_laplaceEnergyRate`,
  `…_spectralBandRate`); iff the completed Suzuki formation energy is subpower at exponent
  `1 + 2σ` (`zetaZeroWidth_le_iff_suzukiCompletedFormationEnergy_subpower`). The infimum of the
  cumulative Möbius–divisor Abel energy exponents is `1 + 2·zetaZeroWidth`
  (`one_add_two_mul_zetaZeroWidth_eq_sInf_mobiusDivisorAbelMeanSquareEnergy_exponents`), and the
  lag family turns negative at exactly the rate `zetaZeroWidth`
  (`zetaZeroWidth_le_iff_lag_primeWindow_ge_neg_exp`).
* **Window ceiling.** The excess exponent `θ*` of the prime window ceiling over `e^{L/2}` is
  pinched by the width: `zetaZeroWidth ≤ θ* ≤ zetaZeroWidth/2 + ¼`
  (`zetaZeroWidth_le_windowCeilingExcessExponent`,
  `windowCeilingExcessExponent_le_half_zetaZeroWidth_add_quarter`).
* **Operator side.** A ground-energy floor `μ(A) ≥ −Ce^{2σA}` at large apertures gives
  `zetaZeroWidth ≤ σ` (`zetaZeroWidth_le_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp`) and, by
  the Rayleigh bridge alone, the lag floor `−C'e^{σv}` at every width `2w < log 2`
  (`lag_primeWindow_ge_neg_exp_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp`). The converse floor
  on `μ` from the width is not proved here; it is the graded form of the no-crossing problem.
* **Heat side.** `newmanConstant ≤ zetaZeroWidth²/2` (`newmanConstant_le_half_sq_zetaZeroWidth`).
* **Jensen side.** Each zero right of the line contributes `2π m_ρ log|ρ/(1 − ρ)|` to the
  Balazard–Saias–Yor integral (`two_pi_mul_log_norm_div_le_integral_log_norm_zeta_criticalLine`),
  and the integral vanishes iff the width does
  (`integral_log_norm_zeta_criticalLine_eq_zero_iff_zetaZeroWidth_eq_zero`).
* **Positivity side.** Prime-blind positivity on a node set `S` is the existence of a full-cone
  Weil-positive weight vanishing off `S` (`primeBlindPositiveOn_iff_exists_weilPositiveFull_eq_zero_off`);
  since the cone is `{Λ}`, it is Weil positivity of `Λ` together with `supp Λ ⊆ S`
  (`primeBlindPositiveOn_iff_weilPositiveFull_vonMangoldt_and_support`).
* **Endpoint.** At width zero all readings are the Riemann hypothesis
  (`zetaZeroWidth_eq_zero_iff_newmanConstant_eq_zero`,
  `zetaZeroWidth_eq_zero_iff_tendsto_ccmRestrictedWeilGroundEnergy_zero`,
  `zetaZeroWidth_eq_zero_iff_primeBlindPositiveOn_primePowers`,
  `zetaZeroWidth_eq_zero_iff_deficitPrimitive_bound`).
-/

open Complex Set Filter Topology MeasureTheory
open scoped Real

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower _root_.RHTower.WeilOneSided _root_.RHTower.WeilSpectral
  _root_.RHTower.DeBruijn
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
open GaloisForLFunctions.ArithmeticCriticalityTheory GaloisForLFunctions.RHTower

/-! ### 1. Three languages, one number -/

/-- A zero of `ζ` with positive real part is a nontrivial zero in the open strip. -/
theorem mem_zetaZeroConfig_of_riemannZeta_eq_zero_of_re_pos {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) : ρ ∈ zetaZeroConfig.carrier := by
  have h1 : ρ.re < 1 := by
    by_contra h
    exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hρ
  exact show IsNontrivialZero ρ from ⟨hρ, h0, h1⟩

/-- `Θ ≤ ½ + σ` iff every nontrivial zero has `Re ρ ≤ ½ + σ`: the trivial zeros lie left of
`0` and never reach the abscissa. -/
theorem zetaZeroAbscissa_le_iff_zetaZeroConfig_re_le {σ : ℝ} (hσ : 0 ≤ σ) :
    zetaZeroAbscissa ≤ 1 / 2 + σ ↔ ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re ≤ 1 / 2 + σ := by
  constructor
  · intro h ρ hρ
    exact (re_le_zetaZeroAbscissa hρ.1).trans h
  · intro h
    refine csSup_le zetaZeroReSet_nonempty ?_
    rintro _ ⟨ρ, hρ, rfl⟩
    rcases le_or_gt ρ.re 0 with h0 | h0
    · linarith
    · exact h ρ (mem_zetaZeroConfig_of_riemannZeta_eq_zero_of_re_pos hρ h0)

/-- The zero width and the zero abscissa bound the same half-planes. -/
theorem zetaZeroWidth_le_iff_zetaZeroAbscissa_le {σ : ℝ} (hσ : 0 ≤ σ) :
    zetaZeroWidth ≤ σ ↔ zetaZeroAbscissa ≤ 1 / 2 + σ :=
  (zetaZeroWidth_le_iff_re_le hσ).trans (zetaZeroAbscissa_le_iff_zetaZeroConfig_re_le hσ).symm

/-- **The zero width is the zero abscissa measured from the critical line.** -/
theorem zetaZeroWidth_eq_zetaZeroAbscissa_sub_half : zetaZeroWidth = zetaZeroAbscissa - 1 / 2 := by
  have hΘ := half_le_zetaZeroAbscissa
  refine le_antisymm ?_ ?_
  · exact (zetaZeroWidth_le_iff_zetaZeroAbscissa_le (by linarith)).mpr (by linarith)
  · have h := (zetaZeroWidth_le_iff_zetaZeroAbscissa_le zetaZeroWidth_nonneg).mp le_rfl
    linarith

/-- The zero width and the Xi half-plane bounds agree. -/
theorem zetaZeroWidth_le_iff_xiZeroHalfPlaneBound {σ : ℝ} (hσ : 0 ≤ σ) :
    zetaZeroWidth ≤ σ ↔ XiZeroHalfPlaneBound σ :=
  (zetaZeroWidth_le_iff_re_le hσ).trans
    (RHTower.CrossRouteReceiverBridges.xiZeroHalfPlaneBound_iff_zetaZeroConfig_re_le σ).symm

/-- The width itself is a Xi half-plane bound. -/
theorem xiZeroHalfPlaneBound_zetaZeroWidth : XiZeroHalfPlaneBound zetaZeroWidth :=
  (zetaZeroWidth_le_iff_xiZeroHalfPlaneBound zetaZeroWidth_nonneg).mp le_rfl

/-- A width bound at every level strictly between `σ` and `½` is a width bound at `σ`. -/
private theorem zetaZeroWidth_le_of_forall_lt_half {σ : ℝ}
    (h : ∀ β : ℝ, σ < β → β < 1 / 2 → zetaZeroWidth ≤ β) : zetaZeroWidth ≤ σ := by
  by_contra hlt
  rw [not_le] at hlt
  have := h ((σ + zetaZeroWidth) / 2) (by linarith) (by linarith [zetaZeroWidth_le_half])
  linarith

/-! ### 2. The prime side: mean squares, the deficit primitive, energy exponents -/

/-- **The mean-square band spectrum is the zero width.** -/
theorem zetaZeroWidth_le_iff_forall_meanSquareBandRate {σ : ℝ} (hσ : 0 ≤ σ) (hσ' : σ < 1 / 2) :
    zetaZeroWidth ≤ σ ↔ ∀ β : ℝ, σ < β → MeanSquareBandRate β :=
  (zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ).trans
    (xiZeroHalfPlaneBound_iff_meanSquareBandRate hσ hσ')

/-- **The Laplace-energy spectrum is the zero width.** -/
theorem zetaZeroWidth_le_iff_forall_laplaceEnergyRate {σ : ℝ} (hσ : 0 ≤ σ) (hσ' : σ < 1 / 2) :
    zetaZeroWidth ≤ σ ↔ ∀ β : ℝ, σ < β → LaplaceEnergyRate β :=
  (zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ).trans
    (xiZeroHalfPlaneBound_iff_laplaceEnergyRate hσ hσ')

/-- **The spectral band spectrum is the zero width.** -/
theorem zetaZeroWidth_le_iff_forall_spectralBandRate {σ : ℝ} (hσ : 0 ≤ σ) (hσ' : σ < 1 / 2) :
    zetaZeroWidth ≤ σ ↔ ∀ β : ℝ, σ < β → SpectralBandRate β :=
  (zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ).trans
    (xiZeroHalfPlaneBound_iff_spectralBandRate hσ hσ')

/-- **Zero width ⟹ two-sided bound on the deficit primitive.** If `zetaZeroWidth ≤ σ < ½` and
`β > σ`, then `|D(T)| ≤ B(1 + T)e^{(½ + β)T}` for every `T ≥ 0`: the generalized von Koch bound
`|ψ(x) − x| ≤ K x^{½ + β}` integrated over `[0, T]` in the logarithmic variable. -/
theorem exists_abs_deficitPrimitive_le_of_zetaZeroWidth_le {σ β : ℝ} (hσ : 0 ≤ σ)
    (hσ' : σ < 1 / 2) (hw : zetaZeroWidth ≤ σ) (hβ : σ < β) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ T : ℝ, 0 ≤ T →
      |ccmLogChebyshevDeficitPrimitive T| ≤ B * (1 + T) * Real.exp ((1 / 2 + β) * T) := by
  obtain ⟨K, hK, hψ⟩ :=
    _root_.RHTower.Sieve.exists_chebyshevPsiReal_error_power_bound_of_xiZeroHalfPlaneBound hσ hσ'
      ((zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ).mp hw) (sub_pos.mpr hβ)
  refine ⟨K, hK.le, fun T hT => ?_⟩
  have hc : 0 ≤ 1 / 2 + β := by linarith
  have hpt : ∀ t ∈ Set.uIoc (0 : ℝ) T,
      ‖chebyshevLogDeficit t‖ ≤ K * Real.exp ((1 / 2 + β) * T) := by
    intro t ht
    rw [uIoc_of_le hT] at ht
    have h := hψ (Real.exp t) (Real.one_le_exp ht.1.le)
    rw [RHTower.FreeLagTrace.chebyshevPsiReal_eq_psi, ← Real.exp_mul] at h
    rw [chebyshevLogDeficit, Real.norm_eq_abs, abs_sub_comm]
    calc |Chebyshev.psi (Real.exp t) - Real.exp t|
        ≤ K * Real.exp (t * (1 / 2 + σ + (β - σ))) := h
      _ ≤ K * Real.exp ((1 / 2 + β) * T) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hK.le
          nlinarith [mul_le_mul_of_nonneg_right ht.2 hc]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const hpt
  rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hT] at hb
  rw [deficitPrimitive_eq]
  nlinarith [mul_nonneg hK.le (Real.exp_pos ((1 / 2 + β) * T)).le]

/-- **The one-sided upper rate of the deficit primitive is the zero width.** For `0 ≤ σ < ½`,
`zetaZeroWidth ≤ σ` iff `D(T) ≤ B(1 + T)e^{(½ + β)T}` on `T ≥ 0` for every `β > σ`. -/
theorem zetaZeroWidth_le_iff_forall_deficitPrimitive_le {σ : ℝ} (hσ : 0 ≤ σ) (hσ' : σ < 1 / 2) :
    zetaZeroWidth ≤ σ ↔ ∀ β : ℝ, σ < β → ∃ B : ℝ, ∀ T : ℝ, 0 ≤ T →
      ccmLogChebyshevDeficitPrimitive T ≤ B * (1 + T) * Real.exp ((1 / 2 + β) * T) := by
  constructor
  · intro hw β hβ
    obtain ⟨B, -, hB⟩ := exists_abs_deficitPrimitive_le_of_zetaZeroWidth_le hσ hσ' hw hβ
    exact ⟨B, fun T hT => (le_abs_self _).trans (hB T hT)⟩
  · intro h
    refine zetaZeroWidth_le_of_forall_lt_half fun β hβ hβ' => ?_
    obtain ⟨B, hB⟩ := h β hβ
    exact (zetaZeroWidth_le_iff_xiZeroHalfPlaneBound (by linarith)).mpr
      (xiZeroHalfPlaneBound_of_deficitPrimitive_le (by linarith) hβ' hB)

/-- **The one-sided lower rate of the deficit primitive is the zero width.** -/
theorem zetaZeroWidth_le_iff_forall_deficitPrimitive_ge {σ : ℝ} (hσ : 0 ≤ σ) (hσ' : σ < 1 / 2) :
    zetaZeroWidth ≤ σ ↔ ∀ β : ℝ, σ < β → ∃ B : ℝ, ∀ T : ℝ, 0 ≤ T →
      -(B * (1 + T) * Real.exp ((1 / 2 + β) * T)) ≤ ccmLogChebyshevDeficitPrimitive T := by
  constructor
  · intro hw β hβ
    obtain ⟨B, -, hB⟩ := exists_abs_deficitPrimitive_le_of_zetaZeroWidth_le hσ hσ' hw hβ
    exact ⟨B, fun T hT => (abs_le.mp (hB T hT)).1⟩
  · intro h
    refine zetaZeroWidth_le_of_forall_lt_half fun β hβ hβ' => ?_
    obtain ⟨B, hB⟩ := h β hβ
    exact (zetaZeroWidth_le_iff_xiZeroHalfPlaneBound (by linarith)).mpr
      (xiZeroHalfPlaneBound_of_deficitPrimitive_ge (by linarith) hβ' hB)

/-- **The cumulative Möbius–divisor Abel energy exponent is `1 + 2·zetaZeroWidth`.** -/
theorem one_add_two_mul_zetaZeroWidth_eq_sInf_mobiusDivisorAbelMeanSquareEnergy_exponents :
    1 + 2 * zetaZeroWidth = sInf {r : ℝ | 1 ≤ r ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ N : ℕ, 2 ≤ N → mobiusDivisorAbelMeanSquareEnergy N ≤ C * (N : ℝ) ^ r} := by
  rw [← two_mul_zetaZeroAbscissa_eq_sInf_mobiusDivisorAbelMeanSquareEnergy_exponents,
    zetaZeroWidth_eq_zetaZeroAbscissa_sub_half]
  ring

/-- **The completed Suzuki formation energy is subpower at exponent `1 + 2σ` iff the width is at
most `σ`.** -/
theorem zetaZeroWidth_le_iff_suzukiCompletedFormationEnergy_subpower {σ : ℝ} (hσ : 0 ≤ σ) :
    zetaZeroWidth ≤ σ ↔ ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧
      ∀ N : ℕ, 2 ≤ N → suzukiCompletedFormationEnergy N ≤ B * (N : ℝ) ^ (2 * (1 / 2 + σ) + ε) :=
  (zetaZeroWidth_le_iff_zetaZeroAbscissa_le hσ).trans
    (zetaZeroAbscissa_le_iff_suzukiCompletedFormationEnergy_subpower (by linarith))

/-! ### 3. The window ceiling excess exponent is pinched by the width -/

/-- Exponents `θ ≥ 0` for which every window deviation at large length `L` is at most
`e^{L/2} + B(1 + L)e^{θL}`. -/
def windowCeilingExcessExponents : Set ℝ :=
  {θ : ℝ | 0 ≤ θ ∧ ∃ B : ℝ, ∀ᶠ L in atTop, ∀ x ∈ windowDeviations L,
    x ≤ Real.exp (L / 2) + B * (1 + L) * Real.exp (θ * L)}

/-- The excess exponent `θ*` of the prime window ceiling over the polar value `e^{L/2}`. -/
noncomputable def windowCeilingExcessExponent : ℝ := sInf windowCeilingExcessExponents

/-- The exponent `½` is admissible: window deviations are `O(e^{L/2})`. -/
theorem half_mem_windowCeilingExcessExponents : (1 / 2 : ℝ) ∈ windowCeilingExcessExponents := by
  refine ⟨by norm_num, 1, ?_⟩
  filter_upwards [eventually_abs_windowDeviations_le (η := 1) one_pos,
    eventually_ge_atTop (0 : ℝ)] with L hL hL0 x hx
  have h := hL x hx
  have hE : Real.exp (1 / 2 * L) = Real.exp (L / 2) := by ring_nf
  rw [hE]
  nlinarith [le_abs_self x, mul_nonneg hL0 (Real.exp_pos (L / 2)).le]

theorem bddBelow_windowCeilingExcessExponents : BddBelow windowCeilingExcessExponents :=
  ⟨0, fun _ h => h.1⟩

/-- **The ceiling excess exponent is at least the zero width.** -/
theorem zetaZeroWidth_le_windowCeilingExcessExponent :
    zetaZeroWidth ≤ windowCeilingExcessExponent := by
  refine le_csInf ⟨_, half_mem_windowCeilingExcessExponents⟩ ?_
  rintro θ ⟨hθ, B, hB⟩
  rcases lt_or_ge θ (1 / 2) with hθ' | hθ'
  · exact (zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hθ).mpr
      (xiZeroHalfPlaneBound_of_windowDeviations_le hθ hθ' hB)
  · exact zetaZeroWidth_le_half.trans hθ'

/-- **The ceiling excess exponent is at most `zetaZeroWidth/2 + ¼`.** -/
theorem windowCeilingExcessExponent_le_half_zetaZeroWidth_add_quarter :
    windowCeilingExcessExponent ≤ zetaZeroWidth / 2 + 1 / 4 := by
  rcases eq_or_lt_of_le zetaZeroWidth_le_half with heq | hlt
  · calc windowCeilingExcessExponent ≤ 1 / 2 :=
          csInf_le bddBelow_windowCeilingExcessExponents half_mem_windowCeilingExcessExponents
      _ = zetaZeroWidth / 2 + 1 / 4 := by rw [heq]; norm_num
  · refine le_of_forall_pos_le_add fun ε hε => ?_
    have hε'0 : 0 < min ε (1 / 2 - zetaZeroWidth) := lt_min hε (by linarith)
    have hε'1 : min ε (1 / 2 - zetaZeroWidth) ≤ ε := min_le_left _ _
    have hε'2 : zetaZeroWidth + min ε (1 / 2 - zetaZeroWidth) ≤ 1 / 2 := by
      linarith [min_le_right ε (1 / 2 - zetaZeroWidth)]
    obtain ⟨C, hC⟩ := windowDeviations_le_of_xiZeroHalfPlaneBound zetaZeroWidth_nonneg hlt
      xiZeroHalfPlaneBound_zetaZeroWidth hε'0 hε'2
    have hmem : 1 / 4 + zetaZeroWidth / 2 + min ε (1 / 2 - zetaZeroWidth) ∈
        windowCeilingExcessExponents := by
      refine ⟨by linarith [zetaZeroWidth_nonneg], max C 0, ?_⟩
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL x hx
      have h := hC L hL x hx
      have hE := Real.exp_pos ((1 / 4 + zetaZeroWidth / 2 + min ε (1 / 2 - zetaZeroWidth)) * L)
      have hCm : C ≤ max C 0 * (1 + L) := by
        nlinarith [le_max_left C 0, le_max_right C 0]
      nlinarith [le_abs_self x]
    calc windowCeilingExcessExponent
        ≤ 1 / 4 + zetaZeroWidth / 2 + min ε (1 / 2 - zetaZeroWidth) :=
          csInf_le bddBelow_windowCeilingExcessExponents hmem
      _ ≤ zetaZeroWidth / 2 + 1 / 4 + ε := by linarith

/-! ### 4. The operator side: ground-energy floors read the width and feed the lag family -/

/-- **A ground-energy floor at rate `2σ` bounds the width by `σ`.** -/
theorem zetaZeroWidth_le_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp {σ C A₀ : ℝ} (hσ : 0 ≤ σ)
    (hμ : ∀ A : SuzukiPositiveAperture, A₀ ≤ A.1 →
      -(C * Real.exp (2 * σ * A.1)) ≤ ccmRestrictedWeilGroundEnergy A) :
    zetaZeroWidth ≤ σ :=
  (zetaZeroWidth_le_iff_re_le hσ).mpr (re_le_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp hσ hμ)

/-- **Ground-energy floor ⟹ lag floor, without passing through the zeros.** If
`μ(A) ≥ −Ce^{2σA}` for `A ≥ A₀`, then for every width `0 < w` with `2w < log 2` the dyadic prime
window functional of the difference test is `≥ −C'e^{σv}` for all large lags: the Rayleigh bridge
`2‖κ_w‖² μ(v/2 + w) ≤ Re P_{w,v}` with `e^{2σ(v/2 + w)} = e^{2σw} e^{σv}`. -/
theorem lag_primeWindow_ge_neg_exp_of_ccmRestrictedWeilGroundEnergy_ge_neg_exp {σ C A₀ w : ℝ}
    (hw : 0 < w) (hw2 : 2 * w < Real.log 2)
    (hμ : ∀ A : SuzukiPositiveAperture, A₀ ≤ A.1 →
      -(C * Real.exp (2 * σ * A.1)) ≤ ccmRestrictedWeilGroundEnergy A) :
    ∃ C' V : ℝ, 0 ≤ V ∧ ∀ v : ℝ, V ≤ v → -(C' * Real.exp (σ * v)) ≤
      (lagPrimeWindowRHS v w (EF.weilTest (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1)))).re := by
  set B := ∫ t, ‖modScaledBump w 0 t‖ ^ 2 with hB
  have hB0 : 0 ≤ B := integral_nonneg fun _ => sq_nonneg _
  refine ⟨2 * B * max C 0 * Real.exp (2 * σ * w), max (2 * w + 1) (2 * (A₀ - w)),
    le_trans (by linarith) (le_max_left _ _), fun v hv => ?_⟩
  have hv2w : 2 * w < v := by linarith [le_max_left (2 * w + 1) (2 * (A₀ - w))]
  have hvA₀ : A₀ ≤ v / 2 + w := by linarith [le_max_right (2 * w + 1) (2 * (A₀ - w))]
  have hray := two_mul_ccmRestrictedWeilGroundEnergy_le_re_lagPrimeWindowRHS hw hw2 hv2w
  rw [← hB] at hray
  have hfloor := hμ ⟨v / 2 + w, by linarith⟩ hvA₀
  have hC : C ≤ max C 0 := le_max_left _ _
  have hexp : Real.exp (2 * σ * (v / 2 + w)) = Real.exp (2 * σ * w) * Real.exp (σ * v) := by
    rw [← Real.exp_add]; congr 1; ring
  have h1 : -(2 * B * max C 0 * Real.exp (2 * σ * w) * Real.exp (σ * v)) ≤
      2 * B * ccmRestrictedWeilGroundEnergy ⟨v / 2 + w, by linarith⟩ := by
    calc -(2 * B * max C 0 * Real.exp (2 * σ * w) * Real.exp (σ * v))
        = 2 * B * (-(max C 0 * Real.exp (2 * σ * (v / 2 + w)))) := by rw [hexp]; ring
      _ ≤ 2 * B * (-(C * Real.exp (2 * σ * (v / 2 + w)))) := by
          refine mul_le_mul_of_nonneg_left (neg_le_neg ?_) (by linarith)
          exact mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le
      _ ≤ 2 * B * ccmRestrictedWeilGroundEnergy ⟨v / 2 + w, by linarith⟩ :=
          mul_le_mul_of_nonneg_left hfloor (by linarith)
  linarith

/-! ### 5. The heat side -/

/-- **The de Bruijn–Newman constant is at most half the square of the zero width.** -/
theorem newmanConstant_le_half_sq_zetaZeroWidth : newmanConstant ≤ zetaZeroWidth ^ 2 / 2 :=
  csInf_le realRootedTimes_bddBelow
    ⟨by positivity, fun _ hz => riemannHeat_zeros_real_of_half_sq_zetaZeroWidth_le le_rfl hz⟩

/-! ### 6. The Jensen side -/

/-- Right of the critical line, `|1 − ρ| < |ρ|`. -/
theorem norm_one_sub_lt_norm_of_half_lt_re {ρ : ℂ} (hre : 1 / 2 < ρ.re) : ‖1 - ρ‖ < ‖ρ‖ := by
  have h1 : ‖1 - ρ‖ ^ 2 < ‖ρ‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im]
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) h1

/-- The Blaschke depth `log|ρ/(1 − ρ)|` is nonnegative right of the critical line. -/
theorem log_norm_div_one_sub_nonneg_of_half_lt_re {ρ : ℂ} (hre : 1 / 2 < ρ.re) :
    0 ≤ Real.log ‖ρ / (1 - ρ)‖ := by
  rw [norm_div]
  by_cases h0 : ‖1 - ρ‖ = 0
  · rw [h0, div_zero, Real.log_zero]
  · have hpos : 0 < ‖1 - ρ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    exact Real.log_nonneg (by rw [one_le_div hpos]; exact (norm_one_sub_lt_norm_of_half_lt_re hre).le)

/-- **Each zero right of the line is seen by the Balazard–Saias–Yor integral** with weight
`2π m_ρ log|ρ/(1 − ρ)|`: every term of the convergent zero series is nonnegative. -/
theorem two_pi_mul_log_norm_div_le_integral_log_norm_zeta_criticalLine {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) (hre : 1 / 2 < ρ.re) :
    2 * Real.pi * ((analyticOrderNatAt riemannZeta ρ : ℝ) * Real.log ‖ρ / (1 - ρ)‖) ≤
      ∫ t : ℝ, Real.log ‖riemannZeta (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2) := by
  have h := le_hasSum hasSum_log_norm_rightZetaZeros ⟨ρ, hρ, hre⟩ fun q _ =>
    mul_nonneg (Nat.cast_nonneg _) (log_norm_div_one_sub_nonneg_of_half_lt_re q.2.2)
  exact (le_inv_mul_iff₀ (by positivity)).mp h

/-- **The Balazard–Saias–Yor integral vanishes iff the zero width does.** -/
theorem integral_log_norm_zeta_criticalLine_eq_zero_iff_zetaZeroWidth_eq_zero :
    (∫ t : ℝ, Real.log ‖riemannZeta (1 / 2 + t * I)‖ / (1 / 4 + t ^ 2)) = 0 ↔
      zetaZeroWidth = 0 := by
  rw [← riemannHypothesis_iff_zetaZeroWidth_eq_zero]
  refine ⟨fun h => riemannHypothesis_of_integral_log_norm_zeta_criticalLine_le_zero h.le,
    fun hRH => ?_⟩
  haveI : IsEmpty {ρ : ℂ // riemannZeta ρ = 0 ∧ 1 / 2 < ρ.re} :=
    ⟨fun q => (riemannHypothesis_iff_riemannZeta_ne_zero_of_half_lt_re.mp hRH) q q.2.2 q.2.1⟩
  rw [integral_log_norm_zeta_criticalLine_eq_tsum_rightZeros, tsum_empty, mul_zero]

/-! ### 7. The positivity side: node criticality is the support condition of the Weil cone -/

/-- **Prime-blind positivity on `S` is the existence of a full-cone Weil-positive weight vanishing
off `S`.** -/
theorem primeBlindPositiveOn_iff_exists_weilPositiveFull_eq_zero_off {S : Set ℕ} :
    PrimeBlindPositiveOn S ↔
      ∃ lam : ℕ → ℝ, WeilPositiveFull lam ∧ ∀ n, 2 ≤ n → n ∉ S → lam n = 0 :=
  ⟨exists_weilPositiveFull_of_primeBlindPositiveOn,
    fun ⟨_, hW, hS⟩ => primeBlindPositiveOn_of_weilPositiveFull hW hS⟩

/-- **Node criticality is Weil positivity of `Λ` plus `supp Λ ⊆ S`**: the only point of the Weil
cone is the von Mangoldt weight, so a weight supported in `S` is Weil-positive exactly when `Λ` is
and its support lies in `S`. -/
theorem primeBlindPositiveOn_iff_weilPositiveFull_vonMangoldt_and_support {S : Set ℕ} :
    PrimeBlindPositiveOn S ↔
      WeilPositiveFull (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) ∧
        ∀ n, 2 ≤ n → ArithmeticFunction.vonMangoldt n ≠ 0 → n ∈ S := by
  rw [primeBlindPositiveOn_iff, riemannHypothesis_iff_weilPositiveFull_vonMangoldt]

/-! ### 8. The endpoint: width zero in every language -/

/-- Width zero is the vanishing of the de Bruijn–Newman constant. -/
theorem zetaZeroWidth_eq_zero_iff_newmanConstant_eq_zero :
    zetaZeroWidth = 0 ↔ newmanConstant = 0 := by
  rw [← riemannHypothesis_iff_zetaZeroWidth_eq_zero, riemannHypothesis_iff_newmanConstant_eq_zero]

/-- Width zero is the decay of the restricted Weil ground energy at infinite aperture. -/
theorem zetaZeroWidth_eq_zero_iff_tendsto_ccmRestrictedWeilGroundEnergy_zero :
    zetaZeroWidth = 0 ↔ ∀ ε > 0, ∃ A₀ : ℝ, ∀ A : SuzukiPositiveAperture, A₀ ≤ A.1 →
      |ccmRestrictedWeilGroundEnergy A| < ε := by
  rw [← riemannHypothesis_iff_zetaZeroWidth_eq_zero,
    riemannHypothesis_iff_tendsto_ccmRestrictedWeilGroundEnergy_zero]

/-- Width zero is prime-blind positivity on the prime powers. -/
theorem zetaZeroWidth_eq_zero_iff_primeBlindPositiveOn_primePowers :
    zetaZeroWidth = 0 ↔ PrimeBlindPositiveOn {n | IsPrimePow n} := by
  rw [← riemannHypothesis_iff_zetaZeroWidth_eq_zero,
    riemannHypothesis_iff_primeBlindPositiveOn_primePowers]

/-- Width zero is the square-root bound on the deficit primitive. -/
theorem zetaZeroWidth_eq_zero_iff_deficitPrimitive_bound :
    zetaZeroWidth = 0 ↔ ∃ B : ℝ, 0 ≤ B ∧ ∀ t : ℝ, 0 ≤ t →
      |ccmLogChebyshevDeficitPrimitive t| ≤ B * Real.exp (t / 2) := by
  rw [← riemannHypothesis_iff_zetaZeroWidth_eq_zero]
  exact riemannHypothesis_iff_logChebyshevDeficitPrimitive_bound

end GaloisForLFunctions.SquareRootThreshold
