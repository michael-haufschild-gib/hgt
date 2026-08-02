import GaloisForLFunctions.RHTower.SuzukiGammaStripCarrierIntegrability
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Gamma-wall Hardy boundary

The physical cutoff wall has two geometric block costs.  On the positive physical ray the
shifted source contributes `exp (-(1-σ)n)`; on the negative ray the Gamma canonical map costs
`exp n`, but the literal wall and shift contribute `exp (-(1+σ)n)`, leaving `exp (-σ n)`.
Both are summable exactly inside `0 < σ < 1`.

The same open strip is insufficient for one physical derivative.  The squared shifted Gamma
carrier is integrable, but multiplication by the real frequency has tail
`x^(1-2σ)` and is nonintegrable for every `σ < 1`.  This certifies the sharp distinction between
strip Hardy decay and the derivative-scattering cancellation.
-/

open Complex Filter Topology MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- Positive-physical-ray block majorant after shifting by `σ`. -/
def suzukiGammaWallPositiveBlock (σ : ℝ) (n : ℕ) : ℝ :=
  Real.exp (σ * n) * Real.exp (-n)

/-- Negative-physical-ray block majorant: canonical cost times wall and shift decay. -/
def suzukiGammaWallNegativeBlock (σ : ℝ) (n : ℕ) : ℝ :=
  Real.exp n * Real.exp (-(1 + σ) * n)

theorem suzukiGammaWallPositiveBlock_eq (σ : ℝ) (n : ℕ) :
    suzukiGammaWallPositiveBlock σ n = Real.exp (-(1 - σ) * n) := by
  rw [suzukiGammaWallPositiveBlock, ← Real.exp_add]
  congr 1
  ring

theorem suzukiGammaWallNegativeBlock_eq (σ : ℝ) (n : ℕ) :
    suzukiGammaWallNegativeBlock σ n = Real.exp (-σ * n) := by
  rw [suzukiGammaWallNegativeBlock, ← Real.exp_add]
  congr 1
  ring

/-- The positive physical Gamma wall is summable below the first Gamma pole. -/
theorem summable_suzukiGammaWallPositiveBlock {σ : ℝ} (hσ1 : σ < 1) :
    Summable (suzukiGammaWallPositiveBlock σ) := by
  rw [show suzukiGammaWallPositiveBlock σ =
      fun n : ℕ => Real.exp (n * (-(1 - σ))) by
    funext n
    rw [suzukiGammaWallPositiveBlock_eq]
    congr 1
    ring]
  exact Real.summable_exp_nat_mul_iff.mpr (by linarith)

/-- The negative physical Gamma wall remains summable after paying the canonical `exp n` cost. -/
theorem summable_suzukiGammaWallNegativeBlock {σ : ℝ} (hσ0 : 0 < σ) :
    Summable (suzukiGammaWallNegativeBlock σ) := by
  rw [show suzukiGammaWallNegativeBlock σ =
      fun n : ℕ => Real.exp (n * (-σ)) by
    funext n
    rw [suzukiGammaWallNegativeBlock_eq]
    congr 1
    ring]
  exact Real.summable_exp_nat_mul_iff.mpr (by linarith)

/-- Both literal Gamma-wall rays are summable throughout the open first-pole strip. -/
theorem summable_suzukiGammaWallBlocks {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Summable (suzukiGammaWallPositiveBlock σ) ∧
      Summable (suzukiGammaWallNegativeBlock σ) :=
  ⟨summable_suzukiGammaWallPositiveBlock hσ1,
    summable_suzukiGammaWallNegativeBlock hσ0⟩

/-- Squared norm density of the real-frequency derivative of the shifted scalar carrier. -/
def suzukiGammaStripDerivativeNormSq (σ x : ℝ) : ℝ :=
  x ^ 2 * suzukiGammaStripNormSq σ x

theorem continuous_suzukiGammaStripDerivativeNormSq
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    Continuous (suzukiGammaStripDerivativeNormSq σ) := by
  exact (continuous_id.pow 2).mul (continuous_suzukiGammaStripNormSq hσ0 hσ1)

theorem suzukiGammaStripDerivativeNormSq_nonneg (σ x : ℝ) :
    0 ≤ suzukiGammaStripDerivativeNormSq σ x := by
  unfold suzukiGammaStripDerivativeNormSq suzukiGammaStripNormSq
  positivity

/-- **Sharp derivative wall.**

Before the first Gamma pole, multiplying the shifted carrier by real frequency destroys
integrability.  Hence strip `L²` decay alone cannot imply one physical derivative. -/
theorem not_integrable_suzukiGammaStripDerivativeNormSq
    {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) :
    ¬ Integrable (suzukiGammaStripDerivativeNormSq σ) := by
  intro hderiv
  have htend :=
    suzukiGammaStripNormSq_rpow_tendsto (σ := σ) hσ0.le hσ1
  have hlower : ∀ᶠ x : ℝ in atTop,
      (1 / 2 : ℝ) <
        suzukiGammaStripNormSq σ x * x ^ (1 + 2 * σ) :=
    htend.eventually (Ioi_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  obtain ⟨A, hA⟩ := mem_atTop_sets.mp hlower
  let C : ℝ := max A 1
  have htail :
      IntegrableOn (suzukiGammaStripDerivativeNormSq σ) (Ici C) volume :=
    hderiv.integrableOn
  have hpower :
      IntegrableOn (fun x : ℝ => x ^ (1 - 2 * σ)) (Ici C) volume := by
    apply (htail.const_mul 2).mono'
    · exact (continuousOn_id.rpow_const (fun x hx => Or.inl (by
        have hx1 : 1 ≤ x := (le_max_right A 1).trans hx
        simp only [id_eq]
        linarith))).aestronglyMeasurable measurableSet_Ici
    · filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
      have hx1 : 1 ≤ x := by
        have hC1 : 1 ≤ C := le_max_right _ _
        exact hC1.trans hx
      have hx0 : 0 < x := zero_lt_one.trans_le hx1
      have hprod := hA x ((le_max_left A 1).trans hx)
      have hpowpos : 0 < x ^ (1 + 2 * σ) := Real.rpow_pos_of_pos hx0 _
      have hpow'pos : 0 < x ^ (1 - 2 * σ) := Real.rpow_pos_of_pos hx0 _
      have hpows :
          x ^ (1 - 2 * σ) * x ^ (1 + 2 * σ) = x ^ 2 := by
        rw [← Real.rpow_add hx0]
        norm_num
      have hdensity : 0 ≤ suzukiGammaStripNormSq σ x := by
        unfold suzukiGammaStripNormSq
        positivity
      have hscaled :
          x ^ (1 - 2 * σ) * (1 / 2 : ℝ) <
            suzukiGammaStripNormSq σ x * x ^ 2 := by
        calc
          x ^ (1 - 2 * σ) * (1 / 2 : ℝ) <
              x ^ (1 - 2 * σ) *
                (suzukiGammaStripNormSq σ x * x ^ (1 + 2 * σ)) :=
            mul_lt_mul_of_pos_left hprod hpow'pos
          _ = suzukiGammaStripNormSq σ x *
                (x ^ (1 - 2 * σ) * x ^ (1 + 2 * σ)) := by ring
          _ = suzukiGammaStripNormSq σ x * x ^ 2 := by rw [hpows]
      have hpoint :
          x ^ (1 - 2 * σ) ≤
            2 * suzukiGammaStripDerivativeNormSq σ x := by
        rw [suzukiGammaStripDerivativeNormSq]
        nlinarith [hscaled]
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
      exact hpoint
  have hatTop :
      IntegrableAtFilter (fun x : ℝ => x ^ (1 - 2 * σ)) atTop volume :=
    ⟨Ici C, Ici_mem_atTop C, hpower⟩
  have hexponent : 1 - 2 * σ < -1 :=
    integrableAtFilter_rpow_atTop_iff.mp hatTop
  linarith

end GaloisForLFunctions.RHTower
