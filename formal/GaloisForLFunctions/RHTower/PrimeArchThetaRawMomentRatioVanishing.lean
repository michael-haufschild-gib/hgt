import GaloisForLFunctions.RHTower.PrimeArchThetaReflectedBudgetTailTransfer
import GaloisForLFunctions.RHTower.PrimeArchThetaScoreMomentRecurrence

/-!
# Vanishing odd-scaled theta moment ratios

The first theta atom has an arbitrarily coercive quadratic score after a finite
offset. Its exact Ward identity bounds adjacent moments, and likelihood order
transfers that bound to the complete theta source. Consequently the complete
adjacent raw-moment ratio divided by its odd degree tends to zero.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial
namespace RHTower
noncomputable section

private theorem first_score_quadratic {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 - 4 ≤ thetaCuspBornWittenSuperpotential 1 x := by
  let T : ℝ := thetaCuspMorseScale 1 x
  have he := Real.add_one_le_exp x
  have he0 := Real.exp_pos x
  have hT : T = Real.pi * Real.exp x ^ 2 := by
    simp [T, thetaCuspMorseScale]
  have hT3 : 3 < T := by
    rw [hT]
    nlinarith [Real.pi_gt_three, sq_nonneg (Real.exp x - 1)]
  have hden : 0 < T - 3 / 2 := by linarith
  have hfrac : T / (T - 3 / 2) ≤ 2 := by
    apply (div_le_iff₀ hden).2
    linarith
  have hW : thetaCuspBornWittenSuperpotential 1 x =
      T - 5 / 4 - T / (T - 3 / 2) := by
    rw [thetaCuspBornWittenSuperpotential, thetaCuspBornWittenWeight_eq]
    rfl
  rw [hW, hT] at *
  nlinarith [Real.pi_gt_three, sq_nonneg (Real.exp x - (x + 1)),
    mul_nonneg (sub_nonneg.mpr he) (show 0 ≤ Real.exp x + (x + 1) by positivity)]

/-- Every positive quadratic slope has a finite source-specific score offset. -/
theorem thetaCuspFirstBornWitten_arbitraryQuadraticScore
    {H : ℝ} (hH : 0 < H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x →
      H * x ^ 2 ≤ C + x * thetaCuspBornWittenSuperpotential 1 x := by
  let R : ℝ := H + 4
  let C : ℝ := H * R ^ 2 + R / 16
  have hR : 0 < R := by dsimp [R]; linarith
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro x hx
  by_cases hxR : x ≤ R
  · have hW := thetaCuspFirstBornWittenSuperpotential_affine_lower hx
    have hWx : -(1 / 16 : ℝ) * x ≤
        x * thetaCuspBornWittenSuperpotential 1 x := by
      nlinarith [mul_le_mul_of_nonneg_left hW hx, sq_nonneg x]
    have hs : x ^ 2 ≤ R ^ 2 := by nlinarith
    have hh := mul_le_mul_of_nonneg_left hs hH.le
    dsimp [C]
    linarith
  · have hRx : R ≤ x := (lt_of_not_ge hxR).le
    have hquad := first_score_quadratic hx
    have hW : H * x ≤ thetaCuspBornWittenSuperpotential 1 x := by
      dsimp [R] at hRx
      nlinarith [mul_nonneg hx (show 0 ≤ x - H - 4 by linarith)]
    have hm := mul_le_mul_of_nonneg_left hW hx
    nlinarith

/-- Ward turns arbitrary score coercivity into a sublinear adjacent-ratio fence. -/
theorem thetaCuspFirstAtomRawEvenMoment_arbitrarySlope
    {H : ℝ} (hH : 0 < H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ,
      H * thetaCuspAtomRawEvenMoment (j + 1) 1 ≤
        (((2 * j + 1 : ℕ) : ℝ) / 2 + C) * thetaCuspAtomRawEvenMoment j 1 := by
  obtain ⟨C, hC, hpoint⟩ := thetaCuspFirstBornWitten_arbitraryQuadraticScore hH
  refine ⟨C, hC, ?_⟩
  intro j
  let μ : Measure ℝ := volume.restrict (Ioi 0)
  let χ : ℝ → ℝ := fun x => thetaCuspBornWittenAmplitude 1 x ^ 2
  let W : ℝ → ℝ := thetaCuspBornWittenSuperpotential 1
  have h0 : Integrable (fun x : ℝ => x ^ (2 * j) * χ x) μ :=
    integrableOn_pow_mul_thetaCuspBornWittenAmplitude_sq (2 * j) (by norm_num)
  have h1 : Integrable (fun x : ℝ => x ^ (2 * (j + 1)) * χ x) μ :=
    integrableOn_pow_mul_thetaCuspBornWittenAmplitude_sq (2 * (j + 1)) (by norm_num)
  have hW : Integrable (fun x : ℝ => x ^ (2 * j + 1) * W x * χ x) μ :=
    integrableOn_pow_mul_thetaCuspBornWittenSuperpotential_mul_amplitude_sq
      (2 * j + 1) (by norm_num)
  have hi := integral_mono_ae (h1.const_mul H) ((h0.const_mul C).add hW) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hw : 0 ≤ x ^ (2 * j) * χ x := by
      exact mul_nonneg (pow_nonneg hx.le _) (sq_nonneg _)
    have hp := mul_le_mul_of_nonneg_right (hpoint x hx.le) hw
    convert hp using 1 <;>
      simp only [W, Pi.add_apply, show 2 * (j + 1) = 2 * j + 2 by omega, pow_add, pow_one] <;> ring)
  simp only [Pi.add_apply] at hi
  rw [integral_const_mul, integral_add (h0.const_mul C) hW, integral_const_mul] at hi
  change H * (∫ x : ℝ in Ioi 0, x ^ (2 * (j + 1)) *
      thetaCuspBornWittenAmplitude 1 x ^ 2) ≤
    C * (∫ x : ℝ in Ioi 0, x ^ (2 * j) * thetaCuspBornWittenAmplitude 1 x ^ 2) +
      (∫ x : ℝ in Ioi 0, x ^ (2 * j + 1) * thetaCuspBornWittenSuperpotential 1 x *
        thetaCuspBornWittenAmplitude 1 x ^ 2) at hi
  rw [← thetaCuspMorseBornMoment_eq_integral_bornWittenAmplitude_sq,
    ← thetaCuspMorseBornMoment_eq_integral_bornWittenAmplitude_sq,
    thetaCuspBornWitten_odd_superpotential_moment j (by norm_num)] at hi
  rw [thetaCuspAtomRawEvenMoment_eq_morseBornMoment,
    thetaCuspAtomRawEvenMoment_eq_morseBornMoment]
  have hs := mul_le_mul_of_nonneg_left hi (show 0 ≤ 2 * Real.pi by positivity)
  nlinarith

/-- Complete-source likelihood order retains every adjacent moment in the Ward fence. -/
theorem thetaCuspRawEvenMoment_arbitrarySlope
    {H : ℝ} (hH : 0 < H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ,
      H * thetaCuspRawEvenMoment (j + 1) ≤
        (((2 * j + 1 : ℕ) : ℝ) / 2 + C) * thetaCuspRawEvenMoment j := by
  obtain ⟨C, hC, hfirst⟩ := thetaCuspFirstAtomRawEvenMoment_arbitrarySlope hH
  refine ⟨C, hC, ?_⟩
  intro j
  have ha : 0 < thetaCuspAtomRawEvenMoment j 1 :=
    thetaCuspAtomRawEvenMoment_pos_of_nat_pos j (by norm_num)
  have hr := thetaCuspRawEvenMoment_pos j
  have hc := thetaCuspRawFirst_rawEvenMoment_cross_le j 1
  have hcH := mul_le_mul_of_nonneg_left hc hH.le
  have hstep := mul_le_mul_of_nonneg_right (hfirst j) hr.le
  nlinarith

/-- The literal adjacent raw-moment ratio, divided by its odd degree, tends to zero. -/
theorem tendsto_thetaCuspRawEvenMoment_oddScaledRatio_zero :
    Tendsto (fun j : ℕ => thetaCuspRawEvenMoment (j + 1) /
      (((2 * j + 1 : ℕ) : ℝ) * thetaCuspRawEvenMoment j)) atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    apply Filter.Eventually.of_forall
    intro j
    have hp := thetaCuspRawEvenMoment_pos (j + 1)
    have hq := thetaCuspRawEvenMoment_pos j
    exact ha.trans_le (by positivity)
  · intro ε hε
    obtain ⟨C, hC, hbound⟩ := thetaCuspRawEvenMoment_arbitrarySlope
      (show 0 < 2 / ε by positivity)
    have hev : ∀ᶠ j : ℕ in atTop, 2 * C ≤ (j : ℝ) :=
      (tendsto_natCast_atTop_atTop : Tendsto (fun j : ℕ => (j : ℝ)) atTop atTop).eventually
        (eventually_ge_atTop (2 * C))
    filter_upwards [hev] with j hj
    have hp := thetaCuspRawEvenMoment_pos (j + 1)
    have hq := thetaCuspRawEvenMoment_pos j
    have hd : 0 < ((2 * j + 1 : ℕ) : ℝ) := by positivity
    apply (div_lt_iff₀ (mul_pos hd hq)).2
    have hc : ((2 * j + 1 : ℕ) : ℝ) / 2 + C ≤ ((2 * j + 1 : ℕ) : ℝ) := by
      push_cast
      linarith
    have hh := (hbound j).trans (mul_le_mul_of_nonneg_right hc hq.le)
    have he := mul_le_mul_of_nonneg_left hh hε.le
    have hcancel : ε * (2 / ε) = 2 := by field_simp
    nlinarith

end
end RHTower
