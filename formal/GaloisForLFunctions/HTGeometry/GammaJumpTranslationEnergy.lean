import GaloisForLFunctions.HTGeometry.GammaTransportKernel

/-!
# The Gamma jump is a positive operator, in physical space

Pairing the second difference with the profile and integrating over the line turns it into a
squared translation increment:

`∫ [2F(L) − F(L+s) − F(L−s)] F(L) dL = ∫ [F(L+s) − F(L)]² dL`.

Translation invariance of Lebesgue measure is the only input — no Fourier transform, no Plancherel,
no spectral measure.  Integrating against the positive kernel `1/(e^s − 1)` therefore makes the
Gamma jump's quadratic form the weighted total translation energy, hence nonnegative, and gives the
exact identity that the coercive tail estimates consume.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

section Translation

variable {F : ℝ → ℝ}

theorem integrable_sq_comp_add (hF2 : Integrable (fun L => F L ^ (2 : ℕ))) (c : ℝ) :
    Integrable (fun L => F (L + c) ^ (2 : ℕ)) := by
  simpa using hF2.comp_add_right c

theorem integral_sq_comp_add (c : ℝ) :
    (∫ L, F (L + c) ^ (2 : ℕ)) = ∫ L, F L ^ (2 : ℕ) :=
  integral_add_right_eq_self (μ := (volume : Measure ℝ)) (fun L => F L ^ (2 : ℕ)) c

theorem integrable_translate_mul (hmeas : AEStronglyMeasurable F volume)
    (hF2 : Integrable (fun L => F L ^ (2 : ℕ))) (c : ℝ) :
    Integrable (fun L => F (L + c) * F L) := by
  have hmeas' : AEStronglyMeasurable (fun L => F (L + c) * F L) volume :=
    ((hmeas.comp_measurePreserving (measurePreserving_add_right volume c)).mul hmeas)
  refine Integrable.mono' (g := fun L => (F (L + c) ^ (2 : ℕ) + F L ^ (2 : ℕ)) / 2) ?_ hmeas' ?_
  · exact ((integrable_sq_comp_add hF2 c).add hF2).div_const 2
  · filter_upwards with L
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_nonneg (|F (L + c)| - |F L|), sq_abs (F (L + c)), sq_abs (F L)]

/-- Pairing a backward translate with the profile is pairing the profile with a forward
translate. -/
theorem integral_translate_neg_mul (s : ℝ) :
    (∫ L, F (L - s) * F L) = ∫ L, F (L + s) * F L := by
  have h := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (fun L => F (L - s) * F L) s
  rw [← h]
  refine integral_congr_ae ?_
  filter_upwards with L
  show F (L + s - s) * F (L + s) = F (L + s) * F L
  rw [add_sub_cancel_right, mul_comm]

/-- **The Gamma second difference pairs to a squared translation increment.** -/
theorem integral_secondDifference_mul_self (hmeas : AEStronglyMeasurable F volume)
    (hF2 : Integrable (fun L => F L ^ (2 : ℕ))) (s : ℝ) :
    (∫ L, secondDifference F L s * F L) = ∫ L, (F (L + s) - F L) ^ (2 : ℕ) := by
  have hp : Integrable (fun L => F (L + s) * F L) := integrable_translate_mul hmeas hF2 s
  have hm : Integrable (fun L => F (L - s) * F L) := by
    have := integrable_translate_mul hmeas hF2 (-s)
    simpa [sub_eq_add_neg] using this
  have hs2 : Integrable (fun L => F (L + s) ^ (2 : ℕ)) := integrable_sq_comp_add hF2 s
  have hlhs : (fun L => secondDifference F L s * F L)
      = fun L => 2 * F L ^ (2 : ℕ) - F (L + s) * F L - F (L - s) * F L := by
    funext L
    rw [secondDifference]
    ring
  have hrhs : (fun L => (F (L + s) - F L) ^ (2 : ℕ))
      = fun L => F (L + s) ^ (2 : ℕ) - 2 * (F (L + s) * F L) + F L ^ (2 : ℕ) := by
    funext L
    ring
  have i1 : (∫ L, 2 * F L ^ (2 : ℕ) - F (L + s) * F L - F (L - s) * F L)
      = (∫ L, 2 * F L ^ (2 : ℕ) - F (L + s) * F L) - ∫ L, F (L - s) * F L :=
    integral_sub ((hF2.const_mul 2).sub hp) hm
  have i2 : (∫ L, 2 * F L ^ (2 : ℕ) - F (L + s) * F L)
      = (∫ L, 2 * F L ^ (2 : ℕ)) - ∫ L, F (L + s) * F L :=
    integral_sub (hF2.const_mul 2) hp
  have i3 : (∫ L, 2 * F L ^ (2 : ℕ)) = 2 * ∫ L, F L ^ (2 : ℕ) := integral_const_mul 2 _
  have j1 : (∫ L, F (L + s) ^ (2 : ℕ) - 2 * (F (L + s) * F L) + F L ^ (2 : ℕ))
      = (∫ L, F (L + s) ^ (2 : ℕ) - 2 * (F (L + s) * F L)) + ∫ L, F L ^ (2 : ℕ) :=
    integral_add (hs2.sub (hp.const_mul 2)) hF2
  have j2 : (∫ L, F (L + s) ^ (2 : ℕ) - 2 * (F (L + s) * F L))
      = (∫ L, F (L + s) ^ (2 : ℕ)) - ∫ L, 2 * (F (L + s) * F L) :=
    integral_sub hs2 (hp.const_mul 2)
  have j3 : (∫ L, 2 * (F (L + s) * F L)) = 2 * ∫ L, F (L + s) * F L := integral_const_mul 2 _
  rw [hlhs, hrhs, i1, i2, i3, j1, j2, j3, integral_translate_neg_mul (F := F) s,
    integral_sq_comp_add (F := F) s]
  ring

/-- **The Gamma jump has nonnegative pairing at every scale.** -/
theorem integral_secondDifference_mul_self_nonneg (hmeas : AEStronglyMeasurable F volume)
    (hF2 : Integrable (fun L => F L ^ (2 : ℕ))) (s : ℝ) :
    0 ≤ ∫ L, secondDifference F L s * F L := by
  rw [integral_secondDifference_mul_self hmeas hF2 s]
  exact integral_nonneg fun L => sq_nonneg _

/-! ## The shifted jump and the exact numerical-range constant -/

/-- The exponentially conjugated second difference, `exp(sigma L) R exp(-sigma L)` at scale `s`. -/
noncomputable def shiftedSecondDifference (σ : ℝ) (F : ℝ → ℝ) (L s : ℝ) : ℝ :=
  2 * F L - Real.exp (-(σ * s)) * F (L + s) - Real.exp (σ * s) * F (L - s)

/-- The forward correlation never exceeds the energy. -/
theorem abs_integral_translate_mul_le (hmeas : AEStronglyMeasurable F volume)
    (hF2 : Integrable (fun L => F L ^ (2 : ℕ))) (s : ℝ) :
    |∫ L, F (L + s) * F L| ≤ ∫ L, F L ^ (2 : ℕ) := by
  have hp : Integrable (fun L => F (L + s) * F L) := integrable_translate_mul hmeas hF2 s
  have hs2 : Integrable (fun L => F (L + s) ^ (2 : ℕ)) := integrable_sq_comp_add hF2 s
  have hb : Integrable (fun L => (F (L + s) ^ (2 : ℕ) + F L ^ (2 : ℕ)) / 2) := (hs2.add hF2).div_const 2
  have hbn : Integrable (fun L => -((F (L + s) ^ (2 : ℕ) + F L ^ (2 : ℕ)) / 2)) := hb.neg
  have hI : (∫ L, (F (L + s) ^ (2 : ℕ) + F L ^ (2 : ℕ)) / 2) = ∫ L, F L ^ (2 : ℕ) := by
    have h1 : (∫ L, (F (L + s) ^ (2 : ℕ) + F L ^ (2 : ℕ)) / 2)
        = (∫ L, F (L + s) ^ (2 : ℕ) + F L ^ (2 : ℕ)) / 2 := integral_div (2 : ℝ) _
    have h2 : (∫ L, F (L + s) ^ (2 : ℕ) + F L ^ (2 : ℕ))
        = (∫ L, F (L + s) ^ (2 : ℕ)) + ∫ L, F L ^ (2 : ℕ) := integral_add hs2 hF2
    rw [h1, h2, integral_sq_comp_add (F := F) s]
    ring
  have hup : (∫ L, F (L + s) * F L) ≤ ∫ L, F L ^ (2 : ℕ) := by
    have hmono : (∫ L, F (L + s) * F L) ≤ ∫ L, (F (L + s) ^ (2 : ℕ) + F L ^ (2 : ℕ)) / 2 :=
      integral_mono hp hb (fun L => by nlinarith [sq_nonneg (F (L + s) - F L)])
    rwa [hI] at hmono
  have hlow : -(∫ L, F L ^ (2 : ℕ)) ≤ ∫ L, F (L + s) * F L := by
    have hmono : (∫ L, -((F (L + s) ^ (2 : ℕ) + F L ^ (2 : ℕ)) / 2)) ≤ ∫ L, F (L + s) * F L :=
      integral_mono hbn hp (fun L => by nlinarith [sq_nonneg (F (L + s) + F L)])
    have hneg : (∫ L, -((F (L + s) ^ (2 : ℕ) + F L ^ (2 : ℕ)) / 2)) = -∫ L, F L ^ (2 : ℕ) := by
      rw [integral_neg, hI]
    rwa [hneg] at hmono
  exact abs_le.mpr ⟨hlow, hup⟩

/-- **The shifted pairing in closed form.** -/
theorem integral_shiftedSecondDifference_mul_self (hmeas : AEStronglyMeasurable F volume)
    (hF2 : Integrable (fun L => F L ^ (2 : ℕ))) (σ s : ℝ) :
    (∫ L, shiftedSecondDifference σ F L s * F L)
      = (∫ L, (F (L + s) - F L) ^ (2 : ℕ))
        - 2 * (Real.cosh (σ * s) - 1) * ∫ L, F (L + s) * F L := by
  have hp : Integrable (fun L => F (L + s) * F L) := integrable_translate_mul hmeas hF2 s
  have hm : Integrable (fun L => F (L - s) * F L) := by
    have := integrable_translate_mul hmeas hF2 (-s)
    simpa [sub_eq_add_neg] using this
  have hbase := integral_secondDifference_mul_self hmeas hF2 s
  have hdiff : (fun L => shiftedSecondDifference σ F L s * F L)
      = fun L => secondDifference F L s * F L
        - ((Real.exp (-(σ * s)) - 1) * (F (L + s) * F L)
          + (Real.exp (σ * s) - 1) * (F (L - s) * F L)) := by
    funext L
    rw [shiftedSecondDifference, secondDifference]
    ring
  have hsd : Integrable (fun L => secondDifference F L s * F L) := by
    have hrw : (fun L => secondDifference F L s * F L)
        = fun L => 2 * F L ^ (2 : ℕ) - F (L + s) * F L - F (L - s) * F L := by
      funext L; rw [secondDifference]; ring
    rw [hrw]
    exact ((hF2.const_mul 2).sub hp).sub hm
  have hc1 : Integrable (fun L => (Real.exp (-(σ * s)) - 1) * (F (L + s) * F L)) := hp.const_mul _
  have hc2 : Integrable (fun L => (Real.exp (σ * s) - 1) * (F (L - s) * F L)) := hm.const_mul _
  have hcorr : Integrable (fun L => (Real.exp (-(σ * s)) - 1) * (F (L + s) * F L)
      + (Real.exp (σ * s) - 1) * (F (L - s) * F L)) := hc1.add hc2
  have hsplit : (∫ L, (Real.exp (-(σ * s)) - 1) * (F (L + s) * F L)
      + (Real.exp (σ * s) - 1) * (F (L - s) * F L))
      = (Real.exp (-(σ * s)) - 1) * (∫ L, F (L + s) * F L)
        + (Real.exp (σ * s) - 1) * (∫ L, F (L - s) * F L) := by
    rw [integral_add hc1 hc2, integral_const_mul, integral_const_mul]
  have hcosh : Real.exp (-(σ * s)) + Real.exp (σ * s) = 2 * Real.cosh (σ * s) := by
    rw [Real.cosh_eq]; ring
  rw [hdiff, integral_sub hsd hcorr, hbase, hsplit, integral_translate_neg_mul (F := F) s]
  linear_combination (-(∫ L, F (L + s) * F L)) * hcosh

/-- **The exact numerical-range bound `(11)` in physical space.**  The conjugated Gamma second
difference loses at most `2(cosh(sigma s) - 1)` times the energy, at every scale — with no Fourier
transform and no identification of the operator with a multiplier. -/
theorem neg_le_integral_shiftedSecondDifference (hmeas : AEStronglyMeasurable F volume)
    (hF2 : Integrable (fun L => F L ^ (2 : ℕ))) (σ s : ℝ) :
    -(2 * (Real.cosh (σ * s) - 1) * ∫ L, F L ^ (2 : ℕ))
      ≤ ∫ L, shiftedSecondDifference σ F L s * F L := by
  rw [integral_shiftedSecondDifference_mul_self hmeas hF2 σ s]
  have hsq : 0 ≤ ∫ L, (F (L + s) - F L) ^ (2 : ℕ) := integral_nonneg fun L => sq_nonneg _
  have hcorr : |∫ L, F (L + s) * F L| ≤ ∫ L, F L ^ (2 : ℕ) := abs_integral_translate_mul_le hmeas hF2 s
  have hcosh : 1 ≤ Real.cosh (σ * s) := Real.one_le_cosh _
  have hle : (∫ L, F (L + s) * F L) ≤ ∫ L, F L ^ (2 : ℕ) := le_of_abs_le hcorr
  nlinarith [hsq, hle, hcosh]


end Translation

end GaloisForLFunctions.HTGeometry
