import GaloisForLFunctions.SquareRootThreshold.TheZeroWidthIsAnUnboundedApertureProperty
import GaloisForLFunctions.SquareRootThreshold.PolarGroundEnergyAndPoleFreeLagAbscissaBridge

/-!
# The zero width is a Landau exponent

Every graded reading of the zero width is the infimum of the admissible exponential rates of one
one-parameter family: the width is an *exponent*, the abscissa at which a one-sided bound of the
form `−Ce^{σ·parameter}` first holds, and exponents are tail invariants, determined by arbitrarily
late values of the parameter. This is the reason behind the aperture principle: a bounded range of
the parameter carries no information about an exponent.

* **Configurations.** For a tempered configuration and a good width the admissible rates of the
  lag family form the half-line `[configWidth Z, ∞)` (`lagRates_eq_Ici`), so
  `configWidth Z = inf lagRates` (`configWidth_eq_sInf_lagRates`).
* **`ζ`, three currencies.** `zetaZeroWidth` is the infimum of the admissible rates of the dyadic
  prime windows (`zetaZeroWidth_eq_sInf_zetaLagRates`), of the integrated Chebyshev deficit
  `|D(T)| ≤ B(1 + T)e^{(½+β)T}` (`zetaZeroWidth_eq_sInf_deficitAbsRates`), and of the mean-square
  band `∫₀ᴸ Ẽ² ≤ Ce^{2βL}` (`zetaZeroWidth_eq_sInf_bandRates`). At the trivial rate `½` every
  family is bounded unconditionally; the width is where the bounds stop.
* **The operator side.** The admissible rates of the polar restricted Weil ground energy,
  `μ₀(A) ≥ −Ce^{2σA}` at large apertures, define the exponent `polarGroundEnergyRate ∈ [0, ½]`;
  it dominates the width (`zetaZeroWidth_le_polarGroundEnergyRate`), its unconditional value is
  at most `½` by the floor `μ₀(A) ≥ −(10 + 68e^A)`, and it vanishes iff RH
  (`riemannHypothesis_iff_polarGroundEnergyRate_eq_zero`). The reverse inequality
  `polarGroundEnergyRate ≤ zetaZeroWidth` is the open arrow of the width dictionary in exponent
  form.

`zetaZeroWidth_exponent_law` collects the five statements.
-/

open Complex Set Filter Topology MeasureTheory
open scoped Real

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower
open GaloisForLFunctions.BiScaleUncertainty GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

/-! ### 1. The exponent of a configuration -/

/-- The admissible negativity rates `σ ≥ 0` of the lag family of width `w`: `Re W ≥ −Ce^{σv}` for
all large lags. -/
def lagRates (Z : ZeroConfig) (w : ℝ) : Set ℝ :=
  {σ : ℝ | 0 ≤ σ ∧ ∃ C V : ℝ, ∀ v : ℝ, V ≤ v → -(C * Real.exp (σ * v)) ≤
    (Z.W (twoBump (modScaledBump w 0) v (-1)) (twoBump (modScaledBump w 0) v (-1))).re}

/-- The admissible rates are exactly the half-line above the width. -/
theorem lagRates_eq_Ici {Z : ZeroConfig} (hZ : TemperedConfig Z)
    (hlt : ∀ ρ ∈ Z.carrier, ρ.re < 1) {w : ℝ} (hw : 0 < w)
    (hgood : ∀ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2 → paperFT (scaledBump w) (gammaOf ρ) ≠ 0) :
    lagRates Z w = Ici (configWidth Z) := by
  ext σ
  rw [mem_Ici]
  constructor
  · rintro ⟨hσ, h⟩
    exact (configWidth_le_iff_lag_twoBump_ge_neg_exp hZ hlt hw hgood hσ).mpr h
  · intro hσ
    have hσ0 : 0 ≤ σ := (configWidth_nonneg Z).trans hσ
    exact ⟨hσ0, (configWidth_le_iff_lag_twoBump_ge_neg_exp hZ hlt hw hgood hσ0).mp hσ⟩

/-- **The width of a configuration is the exponent of its lag family.** -/
theorem configWidth_eq_sInf_lagRates {Z : ZeroConfig} (hZ : TemperedConfig Z)
    (hlt : ∀ ρ ∈ Z.carrier, ρ.re < 1) {w : ℝ} (hw : 0 < w)
    (hgood : ∀ ρ ∈ Z.carrier, ρ.re ≠ 1 / 2 → paperFT (scaledBump w) (gammaOf ρ) ≠ 0) :
    configWidth Z = sInf (lagRates Z w) := by
  rw [lagRates_eq_Ici hZ hlt hw hgood, csInf_Ici]

/-! ### 2. `ζ`: the prime-window exponent -/

/-- The admissible rates of the dyadic prime windows of width `w`. -/
def zetaLagRates (w : ℝ) : Set ℝ :=
  {σ : ℝ | 0 ≤ σ ∧ ∃ C V : ℝ, 0 ≤ V ∧ ∀ v : ℝ, V ≤ v → -(C * Real.exp (σ * v)) ≤
    (lagPrimeWindowRHS v w (EF.weilTest (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1)))).re}

/-- **The zero width is the exponent of the dyadic prime windows**, for all but countably many
widths `w ∈ (0, ½ log 2)`. -/
theorem zetaZeroWidth_eq_sInf_zetaLagRates :
    ∃ E : Set ℝ, E.Countable ∧ ∀ w : ℝ, 0 < w → 2 * w < Real.log 2 → w ∉ E →
      zetaZeroWidth = sInf (zetaLagRates w) := by
  obtain ⟨E, hE, hlaw⟩ := zetaZeroWidth_le_iff_lag_primeWindow_ge_neg_exp
  refine ⟨E, hE, fun w hw hw2 hwE => ?_⟩
  have hset : zetaLagRates w = Ici zetaZeroWidth := by
    ext σ
    rw [mem_Ici]
    constructor
    · rintro ⟨hσ, h⟩
      exact (hlaw w hw hw2 hwE σ hσ).mpr h
    · intro hσ
      have hσ0 : 0 ≤ σ := zetaZeroWidth_nonneg.trans hσ
      exact ⟨hσ0, (hlaw w hw hw2 hwE σ hσ0).mp hσ⟩
  rw [hset, csInf_Ici]

/-! ### 3. `ζ`: the deficit-primitive exponent -/

/-- The admissible two-sided rates of the integrated Chebyshev deficit. -/
def deficitAbsRates : Set ℝ :=
  {β : ℝ | 0 ≤ β ∧ ∃ B : ℝ, ∀ T : ℝ, 0 ≤ T →
    |ccmLogChebyshevDeficitPrimitive T| ≤ B * (1 + T) * Real.exp ((1 / 2 + β) * T)}

theorem zetaZeroWidth_le_of_mem_deficitAbsRates {β : ℝ} (h : β ∈ deficitAbsRates) :
    zetaZeroWidth ≤ β := by
  obtain ⟨hβ, B, hB⟩ := h
  rcases lt_or_ge β (1 / 2) with hβ' | hβ'
  · exact (zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hβ).mpr
      (xiZeroHalfPlaneBound_of_deficitPrimitive_le hβ hβ' fun T hT =>
        (le_abs_self _).trans (hB T hT))
  · exact zetaZeroWidth_le_half.trans hβ'

/-- Every rate above the width is admissible; above `½` unconditionally, by the Chebyshev bound
`|D(T)| ≤ (log 4 + 5)e^T`. -/
theorem mem_deficitAbsRates_of_lt {β : ℝ} (hβ : zetaZeroWidth < β) : β ∈ deficitAbsRates := by
  have hβ0 : 0 ≤ β := zetaZeroWidth_nonneg.trans hβ.le
  rcases lt_or_ge zetaZeroWidth (1 / 2) with hw | hw
  · obtain ⟨B, -, hB⟩ :=
      exists_abs_deficitPrimitive_le_of_zetaZeroWidth_le zetaZeroWidth_nonneg hw le_rfl hβ
    exact ⟨hβ0, B, hB⟩
  · have hhalf : 1 / 2 ≤ β := hw.trans hβ.le
    refine ⟨hβ0, chebyshevDeficitConst, fun T hT => ?_⟩
    have h1 := abs_deficitPrimitive_le hT
    have hC := chebyshevDeficitConst_pos
    have hE := Real.exp_pos ((1 / 2 + β) * T)
    have h2 : Real.exp T ≤ Real.exp ((1 / 2 + β) * T) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hhalf) hT])
    calc |ccmLogChebyshevDeficitPrimitive T| ≤ chebyshevDeficitConst * Real.exp T := h1
      _ ≤ chebyshevDeficitConst * Real.exp ((1 / 2 + β) * T) :=
          mul_le_mul_of_nonneg_left h2 hC.le
      _ ≤ chebyshevDeficitConst * (1 + T) * Real.exp ((1 / 2 + β) * T) := by
          nlinarith [mul_nonneg (mul_nonneg hC.le hE.le) hT]

/-- **The zero width is the exponent of the integrated Chebyshev deficit.** -/
theorem zetaZeroWidth_eq_sInf_deficitAbsRates : zetaZeroWidth = sInf deficitAbsRates := by
  have hne : deficitAbsRates.Nonempty :=
    ⟨zetaZeroWidth + 1, mem_deficitAbsRates_of_lt (by linarith)⟩
  have hbdd : BddBelow deficitAbsRates := ⟨0, fun _ h => h.1⟩
  refine le_antisymm (le_csInf hne fun _ hβ => zetaZeroWidth_le_of_mem_deficitAbsRates hβ) ?_
  exact le_of_forall_pos_le_add fun ε hε =>
    csInf_le hbdd (mem_deficitAbsRates_of_lt (by linarith))

/-! ### 4. `ζ`: the mean-square band exponent -/

/-- The admissible rates of the mean-square band `∫₀ᴸ Ẽ² ≤ Ce^{2βL}`. -/
def bandRates : Set ℝ := {β : ℝ | 0 ≤ β ∧ MeanSquareBandRate β}

theorem zetaZeroWidth_le_of_mem_bandRates {β : ℝ} (h : β ∈ bandRates) : zetaZeroWidth ≤ β := by
  obtain ⟨hβ, hb⟩ := h
  rcases lt_or_ge β (1 / 2) with hβ' | hβ'
  · exact (zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hβ).mpr
      (xiZeroHalfPlaneBound_of_meanSquareBandRate hβ hβ' hb)
  · exact zetaZeroWidth_le_half.trans hβ'

theorem mem_bandRates_of_lt {β : ℝ} (hβ : zetaZeroWidth < β) : β ∈ bandRates :=
  ⟨zetaZeroWidth_nonneg.trans hβ.le,
    meanSquareBandRate_of_xiZeroHalfPlaneBound zetaZeroWidth_nonneg hβ
      xiZeroHalfPlaneBound_zetaZeroWidth⟩

/-- **The zero width is the exponent of the mean-square band.** -/
theorem zetaZeroWidth_eq_sInf_bandRates : zetaZeroWidth = sInf bandRates := by
  have hne : bandRates.Nonempty := ⟨zetaZeroWidth + 1, mem_bandRates_of_lt (by linarith)⟩
  have hbdd : BddBelow bandRates := ⟨0, fun _ h => h.1⟩
  refine le_antisymm (le_csInf hne fun _ hβ => zetaZeroWidth_le_of_mem_bandRates hβ) ?_
  exact le_of_forall_pos_le_add fun ε hε => csInf_le hbdd (mem_bandRates_of_lt (by linarith))

/-! ### 5. The operator side: the polar ground-energy exponent -/

/-- The admissible rates `σ ≥ 0` of the polar restricted Weil ground energy:
`μ₀(A) ≥ −Ce^{2σA}` at all large apertures. -/
def polarGroundEnergyRates : Set ℝ :=
  {σ : ℝ | 0 ≤ σ ∧ ∃ C A₀ : ℝ, ∀ A : SuzukiPositiveAperture, A₀ ≤ A.1 →
    -(C * Real.exp (2 * σ * A.1)) ≤ ccmRestrictedWeilPolarGroundEnergy A}

/-- The polar ground-energy exponent. -/
noncomputable def polarGroundEnergyRate : ℝ := sInf polarGroundEnergyRates

/-- The rate `½` is admissible unconditionally: `μ₀(A) ≥ −(10 + 68e^A) ≥ −78e^A`. -/
theorem half_mem_polarGroundEnergyRates : (1 / 2 : ℝ) ∈ polarGroundEnergyRates := by
  refine ⟨by norm_num, 78, 0, fun A _ => ?_⟩
  have h := neg_horizonExponent_le_ccmRestrictedWeilPolarGroundEnergy A
  have hA : 0 < A.1 := A.2
  rw [show (2 : ℝ) * (1 / 2) * A.1 = A.1 by ring]
  have h2 : 10 ≤ 10 * Real.exp A.1 := by nlinarith [Real.one_le_exp hA.le]
  linarith

theorem bddBelow_polarGroundEnergyRates : BddBelow polarGroundEnergyRates :=
  ⟨0, fun _ h => h.1⟩

theorem polarGroundEnergyRate_nonneg : 0 ≤ polarGroundEnergyRate :=
  le_csInf ⟨_, half_mem_polarGroundEnergyRates⟩ fun _ h => h.1

theorem polarGroundEnergyRate_le_half : polarGroundEnergyRate ≤ 1 / 2 :=
  csInf_le bddBelow_polarGroundEnergyRates half_mem_polarGroundEnergyRates

/-- Every admissible polar rate bounds the width. -/
theorem zetaZeroWidth_le_of_mem_polarGroundEnergyRates {σ : ℝ}
    (h : σ ∈ polarGroundEnergyRates) : zetaZeroWidth ≤ σ := by
  obtain ⟨hσ, C, A₀, hμ⟩ := h
  exact (zetaZeroWidth_le_iff_re_le hσ).mpr
    (re_le_of_ccmRestrictedWeilPolarGroundEnergy_ge_neg_exp hσ hμ)

/-- **The polar ground-energy exponent dominates the width.** -/
theorem zetaZeroWidth_le_polarGroundEnergyRate : zetaZeroWidth ≤ polarGroundEnergyRate :=
  le_csInf ⟨_, half_mem_polarGroundEnergyRates⟩ fun _ h =>
    zetaZeroWidth_le_of_mem_polarGroundEnergyRates h

/-- **RH is the vanishing of the polar ground-energy exponent.** -/
theorem riemannHypothesis_iff_polarGroundEnergyRate_eq_zero :
    RiemannHypothesis ↔ polarGroundEnergyRate = 0 := by
  constructor
  · intro hRH
    have h0 : (0 : ℝ) ∈ polarGroundEnergyRates := ⟨le_rfl, 0, 0, fun A _ => by
      simpa using riemannHypothesis_iff_ccmRestrictedWeilPolarGroundEnergy_nonneg.mp hRH A⟩
    exact le_antisymm (csInf_le bddBelow_polarGroundEnergyRates h0) polarGroundEnergyRate_nonneg
  · intro h
    rw [riemannHypothesis_iff_zetaZeroWidth_eq_zero]
    exact le_antisymm (zetaZeroWidth_le_polarGroundEnergyRate.trans h.le) zetaZeroWidth_nonneg

/-! ### 6. The exponent law -/

/-- **The zero width is one exponent.** It is the infimum of the admissible rates of the dyadic
prime windows, of the integrated Chebyshev deficit and of the mean-square band; the polar
ground-energy exponent dominates it and vanishes iff RH. -/
theorem zetaZeroWidth_exponent_law :
    (∃ E : Set ℝ, E.Countable ∧ ∀ w : ℝ, 0 < w → 2 * w < Real.log 2 → w ∉ E →
      zetaZeroWidth = sInf (zetaLagRates w)) ∧
    zetaZeroWidth = sInf deficitAbsRates ∧ zetaZeroWidth = sInf bandRates ∧
    zetaZeroWidth ≤ polarGroundEnergyRate ∧ (RiemannHypothesis ↔ polarGroundEnergyRate = 0) :=
  ⟨zetaZeroWidth_eq_sInf_zetaLagRates, zetaZeroWidth_eq_sInf_deficitAbsRates,
    zetaZeroWidth_eq_sInf_bandRates, zetaZeroWidth_le_polarGroundEnergyRate,
    riemannHypothesis_iff_polarGroundEnergyRate_eq_zero⟩

end GaloisForLFunctions.SquareRootThreshold
