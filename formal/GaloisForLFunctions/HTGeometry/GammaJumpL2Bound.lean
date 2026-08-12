import GaloisForLFunctions.HTGeometry.GammaPairingMajorant
import GaloisForLFunctions.HTGeometry.YoungConvolutionL2

/-!
# The Gamma jump is `L²`-bounded on profiles with a linear translate modulus

The scale integral `J(x) = ∫_{s>0} D_σP(x,s) k(s) ds` of the conjugated second difference against
the Gamma kernel is square-integrable, with

`∫ J² ≤ (∫_{s>0} k(s) ν(s) ds)²`,

whenever the profile has energy at most `C₂²` and `L²` translate modulus at most `C₁ s` at scales
`s ≤ 1`.  Here `ν` is the `L²` scale majorant of the second difference — linear in `s` near zero
by the translate modulus, exponential of rate `σ` far out by the energy — and `k ν` is integrable
on the ray exactly when `σ < 1`.

The proof is Cauchy–Schwarz against the weight `k ν` followed by Tonelli, entirely in `ℝ≥0∞`, so
no joint integrability is assumed anywhere: the finiteness of the right-hand side is what *proves*
`J ∈ L²`.  This replaces the continuous Minkowski inequality, which mathlib does not have.
-/

open MeasureTheory Set ENNReal

namespace GaloisForLFunctions.HTGeometry

/-! ## Pointwise and integral square helpers -/

theorem sq_add_le_two (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

theorem aestronglyMeasurable_sq {q : ℝ → ℝ} (h : AEStronglyMeasurable q volume) :
    AEStronglyMeasurable (fun x => q x ^ 2) volume := by
  refine (h.mul h).congr ?_
  filter_upwards with x
  show q x * q x = q x ^ 2
  rw [pow_two]

/-- A linear combination of the profile and one translate has integrable square. -/
theorem integrable_sq_lin_translate {P : ℝ → ℝ}
    (hPm : AEStronglyMeasurable P volume) (hP2 : Integrable (fun x => P x ^ 2))
    (a b c : ℝ) :
    Integrable (fun x => (a * P x + b * P (x + c)) ^ 2) := by
  have hPt : AEStronglyMeasurable (fun x => P (x + c)) volume :=
    hPm.comp_measurePreserving (measurePreserving_add_right volume c)
  have hPt2 : Integrable (fun x => P (x + c) ^ 2) := integrable_sq_comp_add hP2 c
  have hlin : AEStronglyMeasurable (fun x => a * P x + b * P (x + c)) volume :=
    (hPm.const_mul a).add (hPt.const_mul b)
  have hmaj : Integrable (fun x => 2 * a ^ 2 * P x ^ 2 + 2 * b ^ 2 * P (x + c) ^ 2) :=
    (hP2.const_mul _).add (hPt2.const_mul _)
  refine Integrable.mono' hmaj (aestronglyMeasurable_sq hlin) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := sq_add_le_two (a * P x) (b * P (x + c))
  calc (a * P x + b * P (x + c)) ^ 2
      ≤ 2 * (a * P x) ^ 2 + 2 * (b * P (x + c)) ^ 2 := h
    _ = 2 * a ^ 2 * P x ^ 2 + 2 * b ^ 2 * P (x + c) ^ 2 := by ring

/-- `∫(f+g)² ≤ 2∫f² + 2∫g²`. -/
theorem integral_sq_add_le {f g : ℝ → ℝ}
    (hfm : AEStronglyMeasurable f volume) (hgm : AEStronglyMeasurable g volume)
    (hf2 : Integrable (fun x => f x ^ 2)) (hg2 : Integrable (fun x => g x ^ 2)) :
    (∫ x, (f x + g x) ^ 2) ≤ 2 * (∫ x, f x ^ 2) + 2 * ∫ x, g x ^ 2 := by
  have hsum : Integrable (fun x => 2 * f x ^ 2 + 2 * g x ^ 2) :=
    (hf2.const_mul 2).add (hg2.const_mul 2)
  have hint : Integrable (fun x => (f x + g x) ^ 2) := by
    refine Integrable.mono' hsum (aestronglyMeasurable_sq (hfm.add hgm)) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_add_le_two _ _
  have hmono := integral_mono hint hsum fun x => sq_add_le_two (f x) (g x)
  rwa [integral_add (hf2.const_mul 2) (hg2.const_mul 2), integral_const_mul,
    integral_const_mul] at hmono

/-! ## The `L²` scale majorant -/

/-- The `L²` scale majorant of the conjugated second difference: linear near zero, exponential of
rate `σ` far out. -/
noncomputable def gammaJumpL2Majorant (C₁ C₂ σ : ℝ) (s : ℝ) : ℝ :=
  if s ≤ 1 then 3 * (C₁ + C₂ * σ * Real.exp σ) * s else 5 * C₂ * Real.exp (σ * s)

theorem measurable_gammaJumpL2Majorant (C₁ C₂ σ : ℝ) :
    Measurable (gammaJumpL2Majorant C₁ C₂ σ) := by
  unfold gammaJumpL2Majorant
  exact Measurable.ite (measurableSet_le measurable_id measurable_const)
    (by fun_prop) (by fun_prop)

theorem gammaJumpL2Majorant_pos {C₁ C₂ σ : ℝ}
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hσ0 : 0 ≤ σ) {s : ℝ} (hs : 0 < s) :
    0 < gammaJumpL2Majorant C₁ C₂ σ s := by
  unfold gammaJumpL2Majorant
  by_cases hs1 : s ≤ 1
  · rw [if_pos hs1]
    have : 0 < C₁ + C₂ * σ * Real.exp σ := by positivity
    positivity
  · rw [if_neg hs1]
    positivity

/-- The second difference of an `L²` profile is square-integrable at every scale. -/
theorem integrable_sq_shiftedSecondDifference {P : ℝ → ℝ} (σ : ℝ)
    (hPm : AEStronglyMeasurable P volume) (hP2 : Integrable (fun x => P x ^ 2)) (s : ℝ) :
    Integrable (fun x => shiftedSecondDifference σ P x s ^ 2) := by
  have hX : Integrable (fun x => (1 * P x + (-Real.exp (-(σ * s))) * P (x + s)) ^ 2) :=
    integrable_sq_lin_translate hPm hP2 1 (-Real.exp (-(σ * s))) s
  have hY : Integrable (fun x => (1 * P x + (-Real.exp (σ * s)) * P (x + -s)) ^ 2) :=
    integrable_sq_lin_translate hPm hP2 1 (-Real.exp (σ * s)) (-s)
  have hXm : AEStronglyMeasurable (fun x => 1 * P x + (-Real.exp (-(σ * s))) * P (x + s))
      volume :=
    (hPm.const_mul 1).add
      ((hPm.comp_measurePreserving (measurePreserving_add_right volume s)).const_mul _)
  have hYm : AEStronglyMeasurable (fun x => 1 * P x + (-Real.exp (σ * s)) * P (x + -s))
      volume :=
    (hPm.const_mul 1).add
      ((hPm.comp_measurePreserving (measurePreserving_add_right volume (-s))).const_mul _)
  have hsum : Integrable (fun x =>
      2 * (1 * P x + (-Real.exp (-(σ * s))) * P (x + s)) ^ 2
        + 2 * (1 * P x + (-Real.exp (σ * s)) * P (x + -s)) ^ 2) :=
    (hX.const_mul 2).add (hY.const_mul 2)
  refine Integrable.mono' hsum ?_ ?_
  · have hD : AEStronglyMeasurable (fun x => shiftedSecondDifference σ P x s) volume := by
      have := hXm.add hYm
      refine this.congr ?_
      filter_upwards with x
      show 1 * P x + -Real.exp (-(σ * s)) * P (x + s)
          + (1 * P x + -Real.exp (σ * s) * P (x + -s)) = shiftedSecondDifference σ P x s
      rw [shiftedSecondDifference, show x + -s = x - s from by ring]
      ring
    exact aestronglyMeasurable_sq hD
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hDsplit : shiftedSecondDifference σ P x s
        = (1 * P x + (-Real.exp (-(σ * s))) * P (x + s))
          + (1 * P x + (-Real.exp (σ * s)) * P (x + -s)) := by
      rw [shiftedSecondDifference]
      have : x + -s = x - s := by ring
      rw [this]
      ring
    rw [hDsplit]
    exact sq_add_le_two _ _

/-- **The `L²` scale bound.**  The energy of the conjugated second difference at scale `s` is at
most `ν(s)²`: linear decay near zero from the translate modulus, exponential growth of rate `σ`
far out from the energy. -/
theorem integral_sq_shiftedSecondDifference_le {P : ℝ → ℝ} {C₁ C₂ σ : ℝ}
    (hPm : AEStronglyMeasurable P volume) (hP2 : Integrable (fun x => P x ^ 2))
    (htrans : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → (∫ x, (P (x + s) - P x) ^ 2) ≤ (C₁ * s) ^ 2)
    (hE : (∫ x, P x ^ 2) ≤ C₂ ^ 2)
    (hC₁0 : 0 ≤ C₁) (hC₂0 : 0 ≤ C₂) (hσ0 : 0 ≤ σ) {s : ℝ} (hs : 0 < s) :
    (∫ x, shiftedSecondDifference σ P x s ^ 2) ≤ gammaJumpL2Majorant C₁ C₂ σ s ^ 2 := by
  have hEnn : (0 : ℝ) ≤ ∫ x, P x ^ 2 := integral_nonneg fun x => sq_nonneg _
  set a : ℝ := Real.exp (-(σ * s)) with ha
  set b : ℝ := Real.exp (σ * s) with hb
  have hσs : 0 ≤ σ * s := mul_nonneg hσ0 hs.le
  have hb1 : 1 ≤ b := Real.one_le_exp hσs
  have ha1 : a ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have ha0 : 0 < a := Real.exp_pos _
  -- the two-arm split
  set X : ℝ → ℝ := fun x => P x - a * P (x + s) with hX
  set Y : ℝ → ℝ := fun x => P x - b * P (x - s) with hY
  have hPt : AEStronglyMeasurable (fun x => P (x + s)) volume :=
    hPm.comp_measurePreserving (measurePreserving_add_right volume s)
  have hPt' : AEStronglyMeasurable (fun x => P (x - s)) volume := by
    have := hPm.comp_measurePreserving (measurePreserving_add_right volume (-s))
    refine this.congr ?_
    filter_upwards with x
    show P (x + -s) = P (x - s)
    rw [show x + -s = x - s from by ring]
  have hXm : AEStronglyMeasurable X volume := hPm.sub (hPt.const_mul a)
  have hYm : AEStronglyMeasurable Y volume := hPm.sub (hPt'.const_mul b)
  have hX2 : Integrable (fun x => X x ^ 2) := by
    have := integrable_sq_lin_translate hPm hP2 1 (-a) s
    refine this.congr ?_
    filter_upwards with x
    show (1 * P x + -a * P (x + s)) ^ 2 = X x ^ 2
    rw [hX]
    ring
  have hY2 : Integrable (fun x => Y x ^ 2) := by
    have := integrable_sq_lin_translate hPm hP2 1 (-b) (-s)
    refine this.congr ?_
    filter_upwards with x
    show (1 * P x + -b * P (x + -s)) ^ 2 = Y x ^ 2
    rw [hY, show x + -s = x - s from by ring]
    ring
  have hDXY : ∀ x, shiftedSecondDifference σ P x s = X x + Y x := by
    intro x
    show shiftedSecondDifference σ P x s = (P x - a * P (x + s)) + (P x - b * P (x - s))
    rw [shiftedSecondDifference]
    ring
  have hstep1 : (∫ x, shiftedSecondDifference σ P x s ^ 2)
      ≤ 2 * (∫ x, X x ^ 2) + 2 * ∫ x, Y x ^ 2 := by
    have hcongr : (fun x => shiftedSecondDifference σ P x s ^ 2)
        = fun x => (X x + Y x) ^ 2 := by
      funext x
      rw [hDXY x]
    rw [hcongr]
    exact integral_sq_add_le hXm hYm hX2 hY2
  -- energies of the translates
  have hEt : (∫ x, P (x + s) ^ 2) = ∫ x, P x ^ 2 := integral_sq_comp_add s
  have hEt' : (∫ x, P (x - s) ^ 2) = ∫ x, P x ^ 2 := by
    have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
      (fun x => P (x - s) ^ 2) s
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show P (x + s - s) ^ 2 = P x ^ 2
    rw [show x + s - s = x from by ring]
  -- scalar-multiple energies
  have hsc : ∀ (c : ℝ) (Q : ℝ → ℝ), (∫ x, (c * Q x) ^ 2) = c ^ 2 * ∫ x, Q x ^ 2 := by
    intro c Q
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rcases le_or_gt s 1 with hs1 | hs1
  · -- near branch
    have habs_a : |1 - a| ≤ σ * s * Real.exp (σ * s) := by
      have := abs_one_sub_exp_le (-(σ * s))
      rwa [abs_neg, abs_of_nonneg hσs] at this
    have habs_b : |1 - b| ≤ σ * s * Real.exp (σ * s) := by
      have := abs_one_sub_exp_le (σ * s)
      rwa [abs_of_nonneg hσs] at this
    have htr : (∫ x, (P (x + s) - P x) ^ 2) ≤ (C₁ * s) ^ 2 := htrans s hs.le hs1
    -- X = (P − P(·+s)) + (1−a)·P(·+s)
    have hf2 : Integrable (fun x => (P x - P (x + s)) ^ 2) := by
      have := integrable_sq_lin_translate hPm hP2 1 (-1) s
      refine this.congr ?_
      filter_upwards with x
      show (1 * P x + -1 * P (x + s)) ^ 2 = (P x - P (x + s)) ^ 2
      ring
    have hg2a : Integrable (fun x => ((1 - a) * P (x + s)) ^ 2) := by
      have := integrable_sq_lin_translate hPm hP2 0 (1 - a) s
      refine this.congr ?_
      filter_upwards with x
      show (0 * P x + (1 - a) * P (x + s)) ^ 2 = ((1 - a) * P (x + s)) ^ 2
      ring
    have hfm : AEStronglyMeasurable (fun x => P x - P (x + s)) volume := hPm.sub hPt
    have hgma : AEStronglyMeasurable (fun x => (1 - a) * P (x + s)) volume :=
      hPt.const_mul _
    have hXsplit : (fun x => X x ^ 2)
        = fun x => ((P x - P (x + s)) + (1 - a) * P (x + s)) ^ 2 := by
      funext x
      show (P x - a * P (x + s)) ^ 2 = ((P x - P (x + s)) + (1 - a) * P (x + s)) ^ 2
      ring
    have hXbound : (∫ x, X x ^ 2)
        ≤ 2 * (C₁ * s) ^ 2 + 2 * (σ * s * Real.exp (σ * s)) ^ 2 * C₂ ^ 2 := by
      rw [hXsplit]
      have h1 := integral_sq_add_le hfm hgma hf2 hg2a
      have h2 : (∫ x, (P x - P (x + s)) ^ 2) ≤ (C₁ * s) ^ 2 := by
        have hcongr : (fun x => (P x - P (x + s)) ^ 2)
            = fun x => (P (x + s) - P x) ^ 2 := by
          funext x
          ring
        rw [hcongr]
        exact htr
      have h3 : (∫ x, ((1 - a) * P (x + s)) ^ 2)
          ≤ (σ * s * Real.exp (σ * s)) ^ 2 * C₂ ^ 2 := by
        rw [hsc (1 - a) (fun x => P (x + s)), hEt]
        have hsq : (1 - a) ^ 2 ≤ (σ * s * Real.exp (σ * s)) ^ 2 := by
          rw [← sq_abs (1 - a)]
          exact pow_le_pow_left₀ (abs_nonneg _) habs_a 2
        have hmul := mul_le_mul hsq hE hEnn (by positivity)
        exact hmul
      linarith
    -- Y = (P − P(·−s)) + (1−b)·P(·−s)
    have hf2' : Integrable (fun x => (P x - P (x - s)) ^ 2) := by
      have := integrable_sq_lin_translate hPm hP2 1 (-1) (-s)
      refine this.congr ?_
      filter_upwards with x
      show (1 * P x + -1 * P (x + -s)) ^ 2 = (P x - P (x - s)) ^ 2
      rw [show x + -s = x - s from by ring]
      ring
    have hg2b : Integrable (fun x => ((1 - b) * P (x - s)) ^ 2) := by
      have := integrable_sq_lin_translate hPm hP2 0 (1 - b) (-s)
      refine this.congr ?_
      filter_upwards with x
      show (0 * P x + (1 - b) * P (x + -s)) ^ 2 = ((1 - b) * P (x - s)) ^ 2
      rw [show x + -s = x - s from by ring]
      ring
    have hfm' : AEStronglyMeasurable (fun x => P x - P (x - s)) volume := hPm.sub hPt'
    have hgmb : AEStronglyMeasurable (fun x => (1 - b) * P (x - s)) volume :=
      hPt'.const_mul _
    have hYsplit : (fun x => Y x ^ 2)
        = fun x => ((P x - P (x - s)) + (1 - b) * P (x - s)) ^ 2 := by
      funext x
      show (P x - b * P (x - s)) ^ 2 = ((P x - P (x - s)) + (1 - b) * P (x - s)) ^ 2
      ring
    have hYbound : (∫ x, Y x ^ 2)
        ≤ 2 * (C₁ * s) ^ 2 + 2 * (σ * s * Real.exp (σ * s)) ^ 2 * C₂ ^ 2 := by
      rw [hYsplit]
      have h1 := integral_sq_add_le hfm' hgmb hf2' hg2b
      have h2 : (∫ x, (P x - P (x - s)) ^ 2) ≤ (C₁ * s) ^ 2 := by
        have hshift : (∫ x, (P x - P (x - s)) ^ 2)
            = ∫ x, (P (x + s) - P x) ^ 2 := by
          have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
            (fun x => (P x - P (x - s)) ^ 2) s
          rw [← h]
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          show (P (x + s) - P (x + s - s)) ^ 2 = (P (x + s) - P x) ^ 2
          rw [show x + s - s = x from by ring]
        rw [hshift]
        exact htr
      have h3 : (∫ x, ((1 - b) * P (x - s)) ^ 2)
          ≤ (σ * s * Real.exp (σ * s)) ^ 2 * C₂ ^ 2 := by
        rw [hsc (1 - b) (fun x => P (x - s)), hEt']
        have hsq : (1 - b) ^ 2 ≤ (σ * s * Real.exp (σ * s)) ^ 2 := by
          rw [← sq_abs (1 - b)]
          exact pow_le_pow_left₀ (abs_nonneg _) habs_b 2
        exact mul_le_mul hsq hE hEnn (by positivity)
      linarith
    -- assemble the near branch
    have hexp_mono : Real.exp (σ * s) ≤ Real.exp σ := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith
    rw [gammaJumpL2Majorant, if_pos hs1]
    have hfinal : 2 * (2 * (C₁ * s) ^ 2 + 2 * (σ * s * Real.exp (σ * s)) ^ 2 * C₂ ^ 2)
          + 2 * (2 * (C₁ * s) ^ 2 + 2 * (σ * s * Real.exp (σ * s)) ^ 2 * C₂ ^ 2)
        ≤ (3 * (C₁ + C₂ * σ * Real.exp σ) * s) ^ 2 := by
      have hEs0 : 0 < Real.exp (σ * s) := Real.exp_pos _
      have hE0 : 0 < Real.exp σ := Real.exp_pos _
      have hEsq : Real.exp (σ * s) ^ 2 ≤ Real.exp σ ^ 2 := by
        nlinarith [hexp_mono, hEs0.le, hE0.le]
      have hterm : (σ * s * Real.exp (σ * s)) ^ 2 * C₂ ^ 2
          ≤ (C₂ * σ * Real.exp σ) ^ 2 * s ^ 2 := by
        have h0 : (0 : ℝ) ≤ σ ^ 2 * s ^ 2 * C₂ ^ 2 := by positivity
        calc (σ * s * Real.exp (σ * s)) ^ 2 * C₂ ^ 2
            = σ ^ 2 * s ^ 2 * C₂ ^ 2 * Real.exp (σ * s) ^ 2 := by ring
          _ ≤ σ ^ 2 * s ^ 2 * C₂ ^ 2 * Real.exp σ ^ 2 :=
              mul_le_mul_of_nonneg_left hEsq h0
          _ = (C₂ * σ * Real.exp σ) ^ 2 * s ^ 2 := by ring
      have hcross : 0 ≤ C₁ * (C₂ * σ * Real.exp σ) * s ^ 2 := by positivity
      nlinarith [hterm, hcross, sq_nonneg (C₁ * s),
        mul_nonneg (sq_nonneg (C₂ * σ * Real.exp σ)) (sq_nonneg s)]
    calc (∫ x, shiftedSecondDifference σ P x s ^ 2)
        ≤ 2 * (∫ x, X x ^ 2) + 2 * ∫ x, Y x ^ 2 := hstep1
      _ ≤ 2 * (2 * (C₁ * s) ^ 2 + 2 * (σ * s * Real.exp (σ * s)) ^ 2 * C₂ ^ 2)
          + 2 * (2 * (C₁ * s) ^ 2 + 2 * (σ * s * Real.exp (σ * s)) ^ 2 * C₂ ^ 2) := by
          have hXnn : (0:ℝ) ≤ 2 := by norm_num
          nlinarith [hXbound, hYbound]
      _ ≤ (3 * (C₁ + C₂ * σ * Real.exp σ) * s) ^ 2 := hfinal
  · -- far branch
    have hfP : AEStronglyMeasurable (fun x => (-a) * P (x + s)) volume := hPt.const_mul _
    have hfP' : AEStronglyMeasurable (fun x => (-b) * P (x - s)) volume := hPt'.const_mul _
    have hf2a : Integrable (fun x => ((-a) * P (x + s)) ^ 2) := by
      have := integrable_sq_lin_translate hPm hP2 0 (-a) s
      refine this.congr ?_
      filter_upwards with x
      show (0 * P x + -a * P (x + s)) ^ 2 = ((-a) * P (x + s)) ^ 2
      ring
    have hf2b : Integrable (fun x => ((-b) * P (x - s)) ^ 2) := by
      have := integrable_sq_lin_translate hPm hP2 0 (-b) (-s)
      refine this.congr ?_
      filter_upwards with x
      show (0 * P x + -b * P (x + -s)) ^ 2 = ((-b) * P (x - s)) ^ 2
      rw [show x + -s = x - s from by ring]
      ring
    have hXsplit : (fun x => X x ^ 2) = fun x => (P x + (-a) * P (x + s)) ^ 2 := by
      funext x
      show (P x - a * P (x + s)) ^ 2 = (P x + (-a) * P (x + s)) ^ 2
      ring
    have hXbound : (∫ x, X x ^ 2) ≤ 2 * C₂ ^ 2 + 2 * a ^ 2 * C₂ ^ 2 := by
      rw [hXsplit]
      have h1 := integral_sq_add_le hPm hfP hP2 hf2a
      have h3 : (∫ x, ((-a) * P (x + s)) ^ 2) ≤ a ^ 2 * C₂ ^ 2 := by
        rw [hsc (-a) (fun x => P (x + s)), hEt]
        have : (-a) ^ 2 = a ^ 2 := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_left hE (sq_nonneg a)
      nlinarith [h1, hE]
    have hYsplit : (fun x => Y x ^ 2) = fun x => (P x + (-b) * P (x - s)) ^ 2 := by
      funext x
      show (P x - b * P (x - s)) ^ 2 = (P x + (-b) * P (x - s)) ^ 2
      ring
    have hYbound : (∫ x, Y x ^ 2) ≤ 2 * C₂ ^ 2 + 2 * b ^ 2 * C₂ ^ 2 := by
      rw [hYsplit]
      have h1 := integral_sq_add_le hPm hfP' hP2 hf2b
      have h3 : (∫ x, ((-b) * P (x - s)) ^ 2) ≤ b ^ 2 * C₂ ^ 2 := by
        rw [hsc (-b) (fun x => P (x - s)), hEt']
        have : (-b) ^ 2 = b ^ 2 := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_left hE (sq_nonneg b)
      nlinarith [h1, hE]
    rw [gammaJumpL2Majorant, if_neg (not_le.mpr hs1)]
    have hbsq : (1 : ℝ) ≤ b ^ 2 := by nlinarith
    have hasq : a ^ 2 ≤ 1 := by nlinarith
    calc (∫ x, shiftedSecondDifference σ P x s ^ 2)
        ≤ 2 * (∫ x, X x ^ 2) + 2 * ∫ x, Y x ^ 2 := hstep1
      _ ≤ 2 * (2 * C₂ ^ 2 + 2 * a ^ 2 * C₂ ^ 2) + 2 * (2 * C₂ ^ 2 + 2 * b ^ 2 * C₂ ^ 2) := by
          nlinarith [hXbound, hYbound]
      _ ≤ (5 * C₂ * Real.exp (σ * s)) ^ 2 := by
          have hC2sq : 0 ≤ C₂ ^ 2 := sq_nonneg _
          nlinarith [hbsq, hasq, mul_nonneg hC2sq (sq_nonneg b)]

/-! ## The scale weight and its integrability -/

/-- The scale weight `k ν`: the Gamma kernel times the `L²` majorant. -/
noncomputable def gammaJumpScaleWeight (C₁ C₂ σ : ℝ) (s : ℝ) : ℝ :=
  gammaTransportKernel s * gammaJumpL2Majorant C₁ C₂ σ s

theorem measurable_gammaJumpScaleWeight (C₁ C₂ σ : ℝ) :
    Measurable (gammaJumpScaleWeight C₁ C₂ σ) :=
  measurable_gammaTransportKernel.mul (measurable_gammaJumpL2Majorant C₁ C₂ σ)

theorem gammaJumpScaleWeight_nonneg {C₁ C₂ σ : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hσ0 : 0 ≤ σ) {s : ℝ} (hs : 0 < s) :
    0 ≤ gammaJumpScaleWeight C₁ C₂ σ s := by
  unfold gammaJumpScaleWeight gammaJumpL2Majorant
  have hk := gammaTransportKernel_pos hs
  by_cases hs1 : s ≤ 1
  · rw [if_pos hs1]
    have h1 : 0 ≤ C₁ + C₂ * σ * Real.exp σ := by positivity
    positivity
  · rw [if_neg hs1]
    positivity

/-- **Integrability of the scale weight**, exactly when `σ < 1`. -/
theorem integrableOn_gammaJumpScaleWeight {C₁ C₂ σ : ℝ}
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) :
    IntegrableOn (gammaJumpScaleWeight C₁ C₂ σ) (Ioi 0) := by
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := by
    rw [Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
  have hmeas : AEStronglyMeasurable (gammaJumpScaleWeight C₁ C₂ σ) volume :=
    (measurable_gammaJumpScaleWeight C₁ C₂ σ).aestronglyMeasurable
  have hnear : IntegrableOn (gammaJumpScaleWeight C₁ C₂ σ) (Ioc 0 1) := by
    have hconst : IntegrableOn (fun _ : ℝ => 3 * (C₁ + C₂ * σ * Real.exp σ)) (Ioc 0 1) := by
      have : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) 1)) := by
        constructor
        simp
      exact integrable_const _
    refine Integrable.mono' hconst hmeas.restrict ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with s hsmem
    have hs0 : 0 < s := hsmem.1
    have hs1 : s ≤ 1 := hsmem.2
    rw [Real.norm_eq_abs,
      abs_of_nonneg (gammaJumpScaleWeight_nonneg hC₁ hC₂ hσ0 hs0)]
    unfold gammaJumpScaleWeight gammaJumpL2Majorant
    rw [if_pos hs1]
    have hker : gammaTransportKernel s ≤ 1 / s := gammaTransportKernel_le_inv hs0
    have hkpos : 0 < gammaTransportKernel s := gammaTransportKernel_pos hs0
    have hcoef : 0 ≤ 3 * (C₁ + C₂ * σ * Real.exp σ) := by positivity
    calc gammaTransportKernel s * (3 * (C₁ + C₂ * σ * Real.exp σ) * s)
        ≤ (1 / s) * (3 * (C₁ + C₂ * σ * Real.exp σ) * s) := by
          refine mul_le_mul_of_nonneg_right hker ?_
          positivity
      _ = 3 * (C₁ + C₂ * σ * Real.exp σ) := by
          field_simp
  have hfar : IntegrableOn (gammaJumpScaleWeight C₁ C₂ σ) (Ioi 1) := by
    have hpos : 0 < 1 - σ := by linarith
    have hexp : IntegrableOn (fun s : ℝ => 10 * C₂ * Real.exp (-(1 - σ) * s)) (Ioi 1) := by
      have hbase : IntegrableOn (fun s : ℝ => Real.exp (-(1 - σ) * s)) (Ioi 1) :=
        exp_neg_integrableOn_Ioi (1 : ℝ) hpos
      have := hbase.const_mul (10 * C₂)
      refine this.congr ?_
      filter_upwards with s
      ring
    refine Integrable.mono' hexp hmeas.restrict ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hsmem
    have hs1 : (1 : ℝ) < s := hsmem
    have hs0 : 0 < s := by linarith
    rw [Real.norm_eq_abs,
      abs_of_nonneg (gammaJumpScaleWeight_nonneg hC₁ hC₂ hσ0 hs0)]
    unfold gammaJumpScaleWeight gammaJumpL2Majorant
    rw [if_neg (not_le.mpr hs1)]
    have hker : gammaTransportKernel s ≤ 2 * Real.exp (-s) :=
      gammaTransportKernel_le_two_mul_exp_neg hs1.le
    have hkpos : 0 < gammaTransportKernel s := gammaTransportKernel_pos hs0
    calc gammaTransportKernel s * (5 * C₂ * Real.exp (σ * s))
        ≤ (2 * Real.exp (-s)) * (5 * C₂ * Real.exp (σ * s)) := by
          refine mul_le_mul_of_nonneg_right hker ?_
          positivity
      _ = 10 * C₂ * (Real.exp (-s) * Real.exp (σ * s)) := by ring
      _ = 10 * C₂ * Real.exp (-(1 - σ) * s) := by
          rw [← Real.exp_add]
          congr 2
          ring
  rw [hsplit]
  exact hnear.union hfar

/-! ## The main `L²` bound for the Gamma scale integral -/

/-- The conjugated second difference is jointly measurable. -/
theorem measurable_uncurry_shiftedSecondDifference {P : ℝ → ℝ} (σ : ℝ) (hPm : Measurable P) :
    Measurable (Function.uncurry fun x s : ℝ => shiftedSecondDifference σ P x s) := by
  unfold shiftedSecondDifference
  fun_prop

/-- Measurability of the Gamma scale integral in the base point. -/
theorem measurable_gammaScaleIntegral {P : ℝ → ℝ} (σ : ℝ) (hPm : Measurable P) :
    Measurable fun x =>
      ∫ s in Ioi (0 : ℝ), shiftedSecondDifference σ P x s * gammaTransportKernel s := by
  have hDk : Measurable (Function.uncurry fun x s : ℝ =>
      shiftedSecondDifference σ P x s * gammaTransportKernel s) :=
    (measurable_uncurry_shiftedSecondDifference σ hPm).mul
      (measurable_gammaTransportKernel.comp measurable_snd)
  exact hDk.stronglyMeasurable.integral_prod_right'.measurable

/-- **The `ℝ≥0∞` master bound.**  The square `lintegral` of the Gamma scale integral is at most
the square of the scale weight's mass.  Cauchy–Schwarz against the weight `k ν`, then Tonelli;
no integrability is assumed. -/
theorem lintegral_sq_gammaScaleIntegral_le {P : ℝ → ℝ} {C₁ C₂ σ : ℝ}
    (hPm : Measurable P) (hP2 : Integrable (fun x => P x ^ 2))
    (htrans : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → (∫ x, (P (x + s) - P x) ^ 2) ≤ (C₁ * s) ^ 2)
    (hE : (∫ x, P x ^ 2) ≤ C₂ ^ 2)
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hσ0 : 0 ≤ σ) :
    (∫⁻ x, ‖∫ s in Ioi (0 : ℝ),
        shiftedSecondDifference σ P x s * gammaTransportKernel s‖ₑ ^ 2)
      ≤ (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (gammaJumpScaleWeight C₁ C₂ σ s)) ^ 2 := by
  set ν : ℝ → ℝ := gammaJumpL2Majorant C₁ C₂ σ with hν
  set w : ℝ → ℝ := gammaJumpScaleWeight C₁ C₂ σ with hw
  set μs : Measure ℝ := volume.restrict (Ioi 0) with hμs
  set W : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (w s) with hW
  set G : ℝ → ℝ → ℝ≥0∞ :=
    fun x s => ENNReal.ofReal (|shiftedSecondDifference σ P x s| / ν s) with hG
  have hWm : Measurable W := (measurable_gammaJumpScaleWeight C₁ C₂ σ).ennreal_ofReal
  have hDm := measurable_uncurry_shiftedSecondDifference σ hPm
  have hGm : ∀ x, Measurable (G x) := by
    intro x
    have hDx : Measurable fun s => shiftedSecondDifference σ P x s := by
      have : (fun s => shiftedSecondDifference σ P x s)
          = (Function.uncurry fun x s : ℝ => shiftedSecondDifference σ P x s) ∘
            fun s => (x, s) := rfl
      rw [this]
      exact hDm.comp (measurable_const.prodMk measurable_id)
    exact ((hDx.abs.div (measurable_gammaJumpL2Majorant C₁ C₂ σ))).ennreal_ofReal
  have hae : ∀ᵐ s ∂μs, 0 < s := by
    rw [hμs]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact hs
  -- the pointwise identity `‖D k‖ₑ = W · G x` on the ray
  have hker_eq : ∀ x, ∀ᵐ s ∂μs,
      ‖shiftedSecondDifference σ P x s * gammaTransportKernel s‖ₑ = W s * G x s := by
    intro x
    filter_upwards [hae] with s hs
    have hkpos : 0 < gammaTransportKernel s := gammaTransportKernel_pos hs
    have hνpos : 0 < ν s := gammaJumpL2Majorant_pos hC₁ hC₂ hσ0 hs
    have hνne : ν s ≠ 0 := hνpos.ne'
    have hwnn : (0 : ℝ) ≤ w s := gammaJumpScaleWeight_nonneg hC₁.le hC₂.le hσ0 hs
    have hwval : w s = gammaTransportKernel s * ν s := rfl
    show ‖shiftedSecondDifference σ P x s * gammaTransportKernel s‖ₑ
        = ENNReal.ofReal (w s)
          * ENNReal.ofReal (|shiftedSecondDifference σ P x s| / ν s)
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_mul hwnn]
    congr 1
    rw [abs_mul, abs_of_pos hkpos, hwval]
    field_simp
  -- pointwise Cauchy–Schwarz against the weight
  have hCS : ∀ x,
      ‖∫ s in Ioi (0 : ℝ), shiftedSecondDifference σ P x s * gammaTransportKernel s‖ₑ ^ 2
        ≤ (∫⁻ s, W s ∂μs) * ∫⁻ s, W s * G x s ^ 2 ∂μs := by
    intro x
    have h1 : ‖∫ s in Ioi (0 : ℝ),
        shiftedSecondDifference σ P x s * gammaTransportKernel s‖ₑ
        ≤ ∫⁻ s, W s * G x s ∂μs := by
      refine le_trans (enorm_integral_le_lintegral_enorm _) (le_of_eq ?_)
      exact lintegral_congr_ae (hker_eq x)
    calc ‖∫ s in Ioi (0 : ℝ),
          shiftedSecondDifference σ P x s * gammaTransportKernel s‖ₑ ^ 2
        ≤ (∫⁻ s, W s * G x s ∂μs) ^ 2 := pow_le_pow_left' h1 2
      _ ≤ (∫⁻ s, W s ∂μs) * ∫⁻ s, W s * G x s ^ 2 ∂μs :=
          lintegral_weighted_sq_le μs hWm (hGm x)
  -- integrate in the base point and exchange
  have hjoint : Measurable (Function.uncurry fun x s => W s * G x s ^ 2) := by
    have hDabs : Measurable fun p : ℝ × ℝ =>
        |Function.uncurry (fun x s : ℝ => shiftedSecondDifference σ P x s) p| := hDm.abs
    have hquot : Measurable fun p : ℝ × ℝ =>
        |shiftedSecondDifference σ P p.1 p.2| / ν p.2 :=
      hDabs.div ((measurable_gammaJumpL2Majorant C₁ C₂ σ).comp measurable_snd)
    exact ((hWm.comp measurable_snd)).mul (hquot.ennreal_ofReal.pow_const 2)
  have hswap : (∫⁻ x, ∫⁻ s, W s * G x s ^ 2 ∂μs)
      = ∫⁻ s, (∫⁻ x, W s * G x s ^ 2) ∂μs := by
    exact lintegral_lintegral_swap (μ := volume) (ν := μs) hjoint.aemeasurable
  have hinner : ∀ᵐ s ∂μs, (∫⁻ x, W s * G x s ^ 2) ≤ W s := by
    filter_upwards [hae] with s hs
    have hνpos : 0 < ν s := gammaJumpL2Majorant_pos hC₁ hC₂ hσ0 hs
    have hint := integrable_sq_shiftedSecondDifference σ hPm.aestronglyMeasurable hP2 s
    have hDbound := integral_sq_shiftedSecondDifference_le hPm.aestronglyMeasurable hP2
      htrans hE hC₁.le hC₂.le hσ0 hs
    have hGsq : ∀ x, G x s ^ 2
        = ENNReal.ofReal ((ν s ^ 2)⁻¹) * ENNReal.ofReal (shiftedSecondDifference σ P x s ^ 2) := by
      intro x
      rw [hG, ← ENNReal.ofReal_pow (by positivity), div_pow, sq_abs,
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    have hDxm : Measurable fun x => shiftedSecondDifference σ P x s := by
      have : (fun x => shiftedSecondDifference σ P x s)
          = (Function.uncurry fun x s : ℝ => shiftedSecondDifference σ P x s) ∘
            fun x => (x, s) := rfl
      rw [this]
      exact hDm.comp (measurable_id.prodMk measurable_const)
    have hGxm : Measurable fun x => G x s ^ 2 :=
      ((hDxm.abs.div_const (ν s)).ennreal_ofReal).pow_const 2
    calc (∫⁻ x, W s * G x s ^ 2)
        = W s * ∫⁻ x, G x s ^ 2 := lintegral_const_mul _ hGxm
      _ ≤ W s := by
          have hGint : (∫⁻ x, G x s ^ 2) ≤ 1 := by
            have hrw : (∫⁻ x, G x s ^ 2)
                = ENNReal.ofReal ((ν s ^ 2)⁻¹)
                  * ∫⁻ x, ENNReal.ofReal (shiftedSecondDifference σ P x s ^ 2) := by
              rw [← lintegral_const_mul _ (hDxm.pow_const 2).ennreal_ofReal]
              exact lintegral_congr fun x => hGsq x
            have hDint : (∫⁻ x, ENNReal.ofReal (shiftedSecondDifference σ P x s ^ 2))
                = ENNReal.ofReal (∫ x, shiftedSecondDifference σ P x s ^ 2) :=
              (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
                (Filter.Eventually.of_forall fun x => sq_nonneg _)).symm
            rw [hrw, hDint]
            calc ENNReal.ofReal ((ν s ^ 2)⁻¹)
                  * ENNReal.ofReal (∫ x, shiftedSecondDifference σ P x s ^ 2)
                ≤ ENNReal.ofReal ((ν s ^ 2)⁻¹) * ENNReal.ofReal (ν s ^ 2) := by
                  exact mul_le_mul_right (ENNReal.ofReal_le_ofReal hDbound) _
              _ = ENNReal.ofReal ((ν s ^ 2)⁻¹ * ν s ^ 2) := by
                  rw [ENNReal.ofReal_mul (by positivity)]
              _ = 1 := by
                  rw [inv_mul_cancel₀ (by positivity : (ν s ^ 2 : ℝ) ≠ 0)]
                  exact ENNReal.ofReal_one
          calc W s * ∫⁻ x, G x s ^ 2 ≤ W s * 1 := mul_le_mul_right hGint _
            _ = W s := mul_one _
  have hmeas_inner : Measurable fun x => ∫⁻ s, W s * G x s ^ 2 ∂μs :=
    Measurable.lintegral_prod_right' (f := Function.uncurry fun x s => W s * G x s ^ 2) hjoint
  calc (∫⁻ x, ‖∫ s in Ioi (0 : ℝ),
        shiftedSecondDifference σ P x s * gammaTransportKernel s‖ₑ ^ 2)
      ≤ ∫⁻ x, (∫⁻ s, W s ∂μs) * ∫⁻ s, W s * G x s ^ 2 ∂μs := lintegral_mono hCS
    _ = (∫⁻ s, W s ∂μs) * ∫⁻ x, ∫⁻ s, W s * G x s ^ 2 ∂μs :=
        lintegral_const_mul _ hmeas_inner
    _ = (∫⁻ s, W s ∂μs) * ∫⁻ s, (∫⁻ x, W s * G x s ^ 2) ∂μs := by rw [hswap]
    _ ≤ (∫⁻ s, W s ∂μs) * ∫⁻ s, W s ∂μs := by
        exact mul_le_mul_right (lintegral_mono_ae hinner) _
    _ = (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (gammaJumpScaleWeight C₁ C₂ σ s)) ^ 2 := by
        rw [sq]

/-- **The Gamma scale integral of an `L²`-modulus profile is square-integrable**, with explicit
`L²` bound: the two Bochner-level conclusions of the `ℝ≥0∞` master bound. -/
theorem integrable_sq_gammaScaleIntegral {P : ℝ → ℝ} {C₁ C₂ σ : ℝ}
    (hPm : Measurable P) (hP2 : Integrable (fun x => P x ^ 2))
    (htrans : ∀ s : ℝ, 0 ≤ s → s ≤ 1 → (∫ x, (P (x + s) - P x) ^ 2) ≤ (C₁ * s) ^ 2)
    (hE : (∫ x, P x ^ 2) ≤ C₂ ^ 2)
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hσ0 : 0 ≤ σ) (hσ1 : σ < 1) :
    Integrable (fun x => (∫ s in Ioi (0 : ℝ),
        shiftedSecondDifference σ P x s * gammaTransportKernel s) ^ 2)
      ∧ (∫ x, (∫ s in Ioi (0 : ℝ),
          shiftedSecondDifference σ P x s * gammaTransportKernel s) ^ 2)
        ≤ (∫ s in Ioi (0 : ℝ), gammaJumpScaleWeight C₁ C₂ σ s) ^ 2 := by
  set J : ℝ → ℝ := fun x =>
    ∫ s in Ioi (0 : ℝ), shiftedSecondDifference σ P x s * gammaTransportKernel s with hJ
  have hJm : Measurable J := measurable_gammaScaleIntegral σ hPm
  have hwi : IntegrableOn (gammaJumpScaleWeight C₁ C₂ σ) (Ioi 0) :=
    integrableOn_gammaJumpScaleWeight hC₁.le hC₂.le hσ0 hσ1
  have hwnn : ∀ᵐ s ∂(volume.restrict (Ioi (0 : ℝ))),
      0 ≤ gammaJumpScaleWeight C₁ C₂ σ s := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    exact gammaJumpScaleWeight_nonneg hC₁.le hC₂.le hσ0 hs
  have hWeq : (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (gammaJumpScaleWeight C₁ C₂ σ s))
      = ENNReal.ofReal (∫ s in Ioi (0 : ℝ), gammaJumpScaleWeight C₁ C₂ σ s) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hwi hwnn).symm
  have hmaster := lintegral_sq_gammaScaleIntegral_le hPm hP2 htrans hE hC₁ hC₂ hσ0
  rw [hWeq] at hmaster
  have hfin : (∫⁻ x, ‖J x‖ₑ ^ 2)
      ≤ ENNReal.ofReal (∫ s in Ioi (0 : ℝ), gammaJumpScaleWeight C₁ C₂ σ s) ^ 2 := hmaster
  have hnetop : (ENNReal.ofReal
      (∫ s in Ioi (0 : ℝ), gammaJumpScaleWeight C₁ C₂ σ s)) ^ 2 ≠ ⊤ :=
    ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hint : Integrable (fun x => J x ^ 2) := by
    refine ⟨((hJm.pow_const 2)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have heq : (∫⁻ x, ‖J x ^ 2‖ₑ) = ∫⁻ x, ‖J x‖ₑ ^ 2 :=
      lintegral_congr fun x => enorm_pow _ _
    rw [heq]
    exact lt_of_le_of_lt hfin hnetop.lt_top
  refine ⟨hint, ?_⟩
  have hsq : (∫⁻ x, ‖J x‖ₑ ^ 2).toReal = ∫ x, J x ^ 2 := by
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun x => sq_nonneg _)
      hint.aestronglyMeasurable]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  have hwint_nonneg : 0 ≤ ∫ s in Ioi (0 : ℝ), gammaJumpScaleWeight C₁ C₂ σ s :=
    integral_nonneg_of_ae hwnn
  have := ENNReal.toReal_mono hnetop hfin
  rw [hsq] at this
  calc (∫ x, J x ^ 2) ≤ ((ENNReal.ofReal
        (∫ s in Ioi (0 : ℝ), gammaJumpScaleWeight C₁ C₂ σ s)) ^ 2).toReal := this
    _ = (∫ s in Ioi (0 : ℝ), gammaJumpScaleWeight C₁ C₂ σ s) ^ 2 := by
        rw [ENNReal.toReal_pow, ENNReal.toReal_ofReal hwint_nonneg]

end GaloisForLFunctions.HTGeometry
