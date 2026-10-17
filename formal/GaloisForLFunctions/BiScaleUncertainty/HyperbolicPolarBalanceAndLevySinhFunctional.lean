import GaloisForLFunctions.BiScaleUncertainty.MultiplicativeChainBesselAndOriginLeverage

/-!
# Pillar III: Hyperbolic Polar Balance & the Lévy–Sinh Bi-Scale Functional

This module develops the third pillar of **Bi-Scale / Logarithmic-Grid Uncertainty Theory**
(`GaloisForLFunctions.BiScaleUncertainty`): the interaction of the positive-definite correlation
cone `𝒫(ℝ)` with the hyperbolic polar hyperplane `∫ x in Ioi 0, h(x) cosh(x / 2) = 0` and the
singular archimedean Lévy–sinh increment functional
`𝒥_arch(h) = ∫ x in Ioi 0, (h(0) - h(x)) (e^{x/2} / sinh x)`.

## Main Results

1. **Exact Pole-Eliminated Weil–Lévy Identity & Bi-Scale Uncertainty Equivalence
   (`weilArchRe_eq_polar_levy_sinh_form`, `weilArchRe_nonneg_iff_levy_sinh_ge_abs_gammaBracket`):**
   When `∫ x in Ioi 0, h(x) cosh(x / 2) = 0`, the exact archimedean Weil functional reduces to
   `weilArchRe (weilTest F F) = Ω(0) h(0) + ∫ x in Ioi 0, (h(0) - h(x)) (e^{x/2} / sinh x)`,
   and its nonnegativity is equivalent to the physical-space Bi-Scale Uncertainty Inequality
   `|Ω(0)| h(0) ≤ ∫ x in Ioi 0, (h(0) - h(x)) (e^{x/2} / sinh x)`, where
   `|Ω(0)| = γ + π / 2 + log (8 π)`.
2. **Hyperbolic Positive/Negative Lobe Conservation
   (`autocorrPos_sub_autocorrNeg`, `autocorrPos_le_zero`, `integral_autocorrPos_cosh_eq_autocorrNeg_cosh`):**
   Decomposing `h(x) = h⁺(x) - h⁻(x)` into its nonnegative lobes `h⁺ = max(h, 0)` and
   `h⁻ = max(-h, 0)`, Cauchy–Schwarz forces `0 ≤ h⁺(x) ≤ h(0)` and
   `h(0) - h(x) = (h(0) - h⁺(x)) + h⁻(x) ≥ h⁻(x)` everywhere, while polar neutrality forces exact
   conservation of hyperbolic lobe mass:
   `∫ x in Ioi 0, h⁺(x) cosh(x / 2) = ∫ x in Ioi 0, h⁻(x) cosh(x / 2)`.
3. **Polar–Lévy Kernel Deformation & Crossover Floor (`polar_levy_deformation_identity`,
   `polar_levy_deformation_lower_bound`, `polar_levy_lobe_split_identity`):**
   For any Lagrange multiplier `μ ∈ ℝ` and any `x ∈ ℝ`,
   `(h(0) - h(x)) w(x) + μ h(x) cosh(x / 2)`
   `= (h(0) - h(x)) (w(x) - μ cosh(x / 2)) + μ h(0) cosh(x / 2)`.
   Whenever `μ cosh(x / 2) ≤ w(x)`, positive-definiteness `h(0) - h(x) ≥ 0` yields the pointwise
   floor `μ h(0) cosh(x / 2)` plus the residual non-local increment
   `(h(0) - h(x)) (w(x) - μ cosh(x / 2)) ≥ 0`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real
open Zeta23
open RHTower RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole

namespace GaloisForLFunctions.BiScaleUncertainty

noncomputable section

variable {f : ℝ → ℝ}

/-! ### 1. Exact Pole-Eliminated Weil–Lévy Functional on the Polar Hyperplane -/

/-- The archimedean Lévy–sinh weight `w_arch(x) = e^{x/2} / sinh x`. -/
def archLevySinhWeight (x : ℝ) : ℝ := Real.exp (x / 2) / Real.sinh x

/-- `0 < archLevySinhWeight x` for all `x > 0`. -/
theorem archLevySinhWeight_pos {x : ℝ} (hx : 0 < x) : 0 < archLevySinhWeight x :=
  div_pos (Real.exp_pos _) (Real.sinh_pos_iff.mpr hx)

/-- `0 ≤ archLevySinhWeight x` for all `x ≥ 0`. -/
theorem archLevySinhWeight_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ archLevySinhWeight x := by
  unfold archLevySinhWeight
  rcases eq_or_lt_of_le hx with rfl | hx_pos
  · simp
  · exact (archLevySinhWeight_pos hx_pos).le

/-- The physical-space Bi-Scale Uncertainty Functional:
`𝒥_arch(f) = ∫ x in Ioi 0, (h(0) - h(x)) * (e^{x/2} / sinh x)`. -/
def biScaleLevyEnergy (f : ℝ → ℝ) : ℝ :=
  ∫ x in Ioi 0, (autocorr f 0 - autocorr f x) * archLevySinhWeight x

/-- Integrability of the Bi-Scale Lévy integrand on `(0, ∞)` for `f ∈ C²_c(ℝ)`. -/
theorem integrableOn_biScaleLevyIntegrand (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    IntegrableOn (fun x => (autocorr f 0 - autocorr f x) * archLevySinhWeight x) (Ioi 0) := by
  have hc : Continuous (autocorr f) := continuous_autocorr hf hfc
  have hnn : ∀ x ∈ Ioi (0 : ℝ),
      0 ≤ (autocorr f 0 - autocorr f x) * archLevySinhWeight x := fun x hx =>
    mul_nonneg (autocorr_sub_nonneg hfc hf.continuous x) (archLevySinhWeight_pos hx).le
  have hlev : (∫⁻ x in Ioi 0, ENNReal.ofReal (archLevyDensity x * ∫ u, (f u - f (u + x)) ^ 2)) =
      ∫⁻ x in Ioi 0, ENNReal.ofReal ((autocorr f 0 - autocorr f x) * archLevySinhWeight x) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro x hx
    dsimp only [archLevySinhWeight]
    rw [integral_sub_shift_sq hfc hf.continuous x, exp_half_div_sinh_eq hx]
    congr 1
    ring
  have hfin := lintegral_levy_ne_top hf hfc
  rw [hlev] at hfin
  have hmeas : AEStronglyMeasurable
      (fun x => (autocorr f 0 - autocorr f x) * archLevySinhWeight x)
      (volume.restrict (Ioi 0)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine (continuousOn_const.sub hc.continuousOn).mul ?_
    exact (Real.continuous_exp.comp (continuous_id.div_const 2)).continuousOn.div
      Real.continuous_sinh.continuousOn fun x hx => (Real.sinh_pos_iff.mpr hx).ne'
  refine ⟨hmeas, ?_⟩
  rw [HasFiniteIntegral]
  refine lt_of_le_of_lt (le_of_eq ?_) hfin.lt_top
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro x hx
  dsimp only
  rw [Real.enorm_eq_ofReal (hnn x hx)]

/-- Nonnegativity of the Bi-Scale Lévy energy `0 ≤ biScaleLevyEnergy f`. -/
theorem biScaleLevyEnergy_nonneg (hfc : HasCompactSupport f) (hf : Continuous f) :
    0 ≤ biScaleLevyEnergy f := by
  unfold biScaleLevyEnergy
  refine setIntegral_nonneg measurableSet_Ioi fun x hx => ?_
  exact mul_nonneg (autocorr_sub_nonneg hfc hf x) (archLevySinhWeight_pos hx).le

/-- **Exact Pole-Eliminated Weil–Lévy Form:**
When `f ∈ C²_c(ℝ)` lies on the hyperbolic polar hyperplane
`∫ x in Ioi 0, autocorr f x * cosh (x / 2) = 0`, the archimedean Weil energy equals
`Ω(0) * h(0) + biScaleLevyEnergy f`. -/
theorem weilArchRe_eq_polar_levy_sinh_form (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hpolar : (∫ x in Ioi 0, autocorr f x * Real.cosh (x / 2)) = 0) :
    WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) =
      EF.gammaBracket 0 * autocorr f 0 + biScaleLevyEnergy f := by
  have hc : Continuous (autocorr f) := continuous_autocorr hf hfc
  have hcs : HasCompactSupport (autocorr f) := hasCompactSupport_autocorr hfc
  have hJ : IntegrableOn (fun x => (autocorr f 0 - autocorr f x) * archLevySinhWeight x) (Ioi 0) :=
    integrableOn_biScaleLevyIntegrand hf hfc
  have hP : IntegrableOn (fun x => 4 * autocorr f x * Real.cosh (x / 2)) (Ioi 0) := by
    refine Integrable.integrableOn ?_
    refine ((continuous_const.mul hc).mul (by fun_prop)).integrable_of_hasCompactSupport ?_
    exact (hcs.mul_left (f := fun _ => (4 : ℝ))).mul_right
  rw [weilArchRe_eq_exactForm hf hfc]
  have hsplit : (∫ x in Ioi 0, ((autocorr f 0 - autocorr f x) * (Real.exp (x / 2) / Real.sinh x) +
      4 * autocorr f x * Real.cosh (x / 2))) =
      biScaleLevyEnergy f + 4 * ∫ x in Ioi 0, autocorr f x * Real.cosh (x / 2) := by
    unfold archLevySinhWeight at hJ
    unfold biScaleLevyEnergy archLevySinhWeight
    rw [integral_add hJ hP]
    congr 1
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [hsplit, hpolar, mul_zero, add_zero]

/-- **Bi-Scale Uncertainty Equivalence on the Polar Hyperplane:**
For any `f ∈ C²_c(ℝ)` on the polar hyperplane `∫ x in Ioi 0, h(x) cosh(x / 2) = 0`,
`0 ≤ weilArchRe (weilTest F F) ↔ |Ω(0)| * h(0) ≤ biScaleLevyEnergy f`. -/
theorem weilArchRe_nonneg_iff_levy_sinh_ge_abs_gammaBracket
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hpolar : (∫ x in Ioi 0, autocorr f x * Real.cosh (x / 2)) = 0) :
    0 ≤ WeilOneSided.weilArchRe (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ))) ↔
      |EF.gammaBracket 0| * autocorr f 0 ≤ biScaleLevyEnergy f := by
  rw [weilArchRe_eq_polar_levy_sinh_form hf hfc hpolar, abs_gammaBracket_zero, gammaBracket_zero_eq]
  constructor <;> intro h <;> linarith

/-! ### 2. Positive/Negative Lobe Decomposition & Hyperbolic Lobe Conservation -/

/-- The positive lobe `h⁺(x) = max (h(x)) 0`. -/
def autocorrPos (f : ℝ → ℝ) (x : ℝ) : ℝ := max (autocorr f x) 0

/-- The negative lobe `h⁻(x) = max (-h(x)) 0`. -/
def autocorrNeg (f : ℝ → ℝ) (x : ℝ) : ℝ := max (-autocorr f x) 0

theorem autocorrPos_nonneg (f : ℝ → ℝ) (x : ℝ) : 0 ≤ autocorrPos f x := le_max_right _ _

theorem autocorrNeg_nonneg (f : ℝ → ℝ) (x : ℝ) : 0 ≤ autocorrNeg f x := le_max_right _ _

/-- Exact decomposition `h(x) = h⁺(x) - h⁻(x)`. -/
theorem autocorrPos_sub_autocorrNeg (f : ℝ → ℝ) (x : ℝ) :
    autocorrPos f x - autocorrNeg f x = autocorr f x :=
  max_zero_sub_max_neg_zero_eq_self (autocorr f x)

/-- Exact modulus decomposition `|h(x)| = h⁺(x) + h⁻(x)`. -/
theorem autocorrPos_add_autocorrNeg (f : ℝ → ℝ) (x : ℝ) :
    autocorrPos f x + autocorrNeg f x = |autocorr f x| := by
  unfold autocorrPos autocorrNeg
  rcases le_total 0 (autocorr f x) with h | h
  · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h, add_zero]
  · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h, zero_add]

/-- Cauchy–Schwarz upper bound on the positive lobe: `h⁺(x) ≤ h(0)` for all `x ∈ ℝ`. -/
theorem autocorrPos_le_zero (hfc : HasCompactSupport f) (hf : Continuous f) (x : ℝ) :
    autocorrPos f x ≤ autocorr f 0 := by
  unfold autocorrPos
  exact max_le (le_trans (le_abs_self _) (abs_autocorr_le_zero hfc hf x)) (autocorr_zero_nonneg f)

/-- **Lobe Decomposition of the Correlation Increment:**
`h(0) - h(x) = (h(0) - h⁺(x)) + h⁻(x)`, where both summands are nonnegative; in particular
`h⁻(x) ≤ h(0) - h(x)` for all `x ∈ ℝ`, and on the negative lobe (`h(x) ≤ 0`),
`h(0) - h(x) = h(0) + h⁻(x)`. -/
theorem autocorr_sub_eq_pos_defect_add_neg (f : ℝ → ℝ) (x : ℝ) :
    autocorr f 0 - autocorr f x = (autocorr f 0 - autocorrPos f x) + autocorrNeg f x := by
  have := autocorrPos_sub_autocorrNeg f x
  linarith

theorem autocorrNeg_le_autocorr_sub (hfc : HasCompactSupport f) (hf : Continuous f) (x : ℝ) :
    autocorrNeg f x ≤ autocorr f 0 - autocorr f x := by
  have h1 := autocorr_sub_eq_pos_defect_add_neg f x
  have h2 := autocorrPos_le_zero hfc hf x
  linarith

theorem autocorr_sub_eq_zero_add_neg_of_nonpos {x : ℝ} (hx : autocorr f x ≤ 0) :
    autocorr f 0 - autocorr f x = autocorr f 0 + autocorrNeg f x := by
  rw [autocorr_sub_eq_pos_defect_add_neg]
  have hpos0 : autocorrPos f x = 0 := max_eq_right hx
  rw [hpos0, sub_zero]

/-- **Exact Hyperbolic Lobe Conservation on the Polar Hyperplane:**
When `∫ x in Ioi 0, h(x) cosh(x / 2) = 0`, the positive-lobe hyperbolic mass equals the
negative-lobe hyperbolic mass:
`∫ x in Ioi 0, h⁺(x) cosh(x / 2) = ∫ x in Ioi 0, h⁻(x) cosh(x / 2)`. -/
theorem integral_autocorrPos_cosh_eq_autocorrNeg_cosh
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hpolar : (∫ x in Ioi 0, autocorr f x * Real.cosh (x / 2)) = 0) :
    (∫ x in Ioi 0, autocorrPos f x * Real.cosh (x / 2)) =
      ∫ x in Ioi 0, autocorrNeg f x * Real.cosh (x / 2) := by
  have hc : Continuous (autocorr f) := continuous_autocorr hf hfc
  have hcs : HasCompactSupport (autocorr f) := hasCompactSupport_autocorr hfc
  have hpos_c : Continuous (autocorrPos f) := hc.max continuous_const
  have hneg_c : Continuous (autocorrNeg f) := hc.neg.max continuous_const
  have hpos_cs : HasCompactSupport (autocorrPos f) :=
    hcs.comp_left (g := fun y : ℝ => max y 0) (max_self 0)
  have hneg_cs : HasCompactSupport (autocorrNeg f) :=
    hcs.comp_left (g := fun y : ℝ => max (-y) 0) (by simp)
  have hi_pos : IntegrableOn (fun x => autocorrPos f x * Real.cosh (x / 2)) (Ioi 0) :=
    ((hpos_c.mul (by fun_prop)).integrable_of_hasCompactSupport hpos_cs.mul_right).integrableOn
  have hi_neg : IntegrableOn (fun x => autocorrNeg f x * Real.cosh (x / 2)) (Ioi 0) :=
    ((hneg_c.mul (by fun_prop)).integrable_of_hasCompactSupport hneg_cs.mul_right).integrableOn
  have hdiff : (fun x => autocorr f x * Real.cosh (x / 2)) =
      fun x => autocorrPos f x * Real.cosh (x / 2) - autocorrNeg f x * Real.cosh (x / 2) := by
    funext x
    rw [← sub_mul, autocorrPos_sub_autocorrNeg]
  rw [hdiff, integral_sub hi_pos hi_neg] at hpolar
  linarith

/-! ### 3. Polar–Lévy Kernel Deformation & Crossover Lower Bounds -/

/-- **Polar–Lévy Kernel Deformation Identity:**
For any multiplier `μ : ℝ` and any `x ∈ ℝ`,
`(h(0) - h(x)) w(x) + μ h(x) cosh(x / 2)`
`= (h(0) - h(x)) (w(x) - μ cosh(x / 2)) + μ h(0) cosh(x / 2)`. -/
theorem polar_levy_deformation_identity (f : ℝ → ℝ) (w : ℝ → ℝ) (μ x : ℝ) :
    (autocorr f 0 - autocorr f x) * w x + μ * (autocorr f x * Real.cosh (x / 2)) =
      (autocorr f 0 - autocorr f x) * (w x - μ * Real.cosh (x / 2)) +
        μ * autocorr f 0 * Real.cosh (x / 2) := by
  ring

/-- **Polar–Lévy Lobe Split Identity:**
In terms of the positive and negative lobes `h⁺(x), h⁻(x)`, for any `μ, x ∈ ℝ`,
`(h(0) - h(x)) w(x) + μ h(x) cosh(x / 2)`
`= (h(0) - h⁺(x)) (w(x) - μ cosh(x / 2)) + h⁻(x) (w(x) - μ cosh(x / 2)) + μ h(0) cosh(x / 2)`. -/
theorem polar_levy_lobe_split_identity (f : ℝ → ℝ) (w : ℝ → ℝ) (μ x : ℝ) :
    (autocorr f 0 - autocorr f x) * w x + μ * (autocorr f x * Real.cosh (x / 2)) =
      (autocorr f 0 - autocorrPos f x) * (w x - μ * Real.cosh (x / 2)) +
        autocorrNeg f x * (w x - μ * Real.cosh (x / 2)) +
        μ * autocorr f 0 * Real.cosh (x / 2) := by
  rw [polar_levy_deformation_identity, autocorr_sub_eq_pos_defect_add_neg]
  ring

/-- **Pointwise Polar–Lévy Crossover Floor:**
Whenever `μ * cosh(x / 2) ≤ w(x)` at scale `x`, positive-definiteness `h(0) - h(x) ≥ 0` forces
`μ * h(0) * cosh(x / 2) + h⁻(x) * (w(x) - μ * cosh(x / 2))`
`≤ (h(0) - h(x)) * w(x) + μ * (h(x) * cosh(x / 2))`. -/
theorem polar_levy_deformation_lower_bound (hfc : HasCompactSupport f) (hf : Continuous f)
    (w : ℝ → ℝ) (μ x : ℝ) (hw : μ * Real.cosh (x / 2) ≤ w x) :
    μ * autocorr f 0 * Real.cosh (x / 2) +
      autocorrNeg f x * (w x - μ * Real.cosh (x / 2)) ≤
      (autocorr f 0 - autocorr f x) * w x + μ * (autocorr f x * Real.cosh (x / 2)) := by
  rw [polar_levy_deformation_identity]
  have h1 : autocorrNeg f x ≤ autocorr f 0 - autocorr f x :=
    autocorrNeg_le_autocorr_sub hfc hf x
  have h2 : 0 ≤ w x - μ * Real.cosh (x / 2) := by linarith
  have hmul : autocorrNeg f x * (w x - μ * Real.cosh (x / 2)) ≤
      (autocorr f 0 - autocorr f x) * (w x - μ * Real.cosh (x / 2)) :=
    mul_le_mul_of_nonneg_right h1 h2
  linarith

end

end GaloisForLFunctions.BiScaleUncertainty
