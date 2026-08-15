import GaloisForLFunctions.HTGeometry.LSeriesPowerTwist

/-!
# High-line sign rigidity for ordinary Dirichlet series

A real ordinary Dirichlet series cannot acquire a fixed imaginary sign on every sufficiently
far-right vertical translate when it has a nonzero nonconstant coefficient.  The first surviving
coefficient after a finite prefix controls the sign: after a power twist, mathlib's
`LSeries.tendsto_cpow_mul_atTop` extracts its complex phase exactly.

This file packages the reusable coefficient-level mechanism.  No analytic continuation, divisor,
or zero-free hypothesis is used.
-/

namespace GaloisForLFunctions

open Complex Filter Topology LSeries

noncomputable section

/-- A fixed complex power twist preserves finiteness of the absolute-convergence abscissa. -/
theorem lseriesPowerTwistCoeff_abscissa_lt_top
    {f : ℕ → ℂ} (hf : LSeries.abscissaOfAbsConv f < ⊤) (a : ℂ) :
    LSeries.abscissaOfAbsConv (lseriesPowerTwistCoeff f a) < ⊤ := by
  obtain ⟨y, hfy, hyt⟩ := exists_between hf
  lift y to ℝ using ⟨hyt.ne, ((OrderBot.bot_le _).trans_lt hfy).ne'⟩
  have hs : LSeriesSummable f (y : ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (by simpa using hfy)
  have htwist : LSeriesSummable (lseriesPowerTwistCoeff f a) (a + (y : ℂ)) :=
    (LSeriesSummable_powerTwist f a (a + (y : ℂ))).2 (by simpa)
  exact htwist.abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _)

/-- Imaginary-part form of first-coefficient extraction for a peeled, power-twisted Dirichlet
series.  The positive real normalization is written as a real `rpow`. -/
theorem tendsto_rpow_mul_im_lseriesPeeledPowerTwist
    {f : ℕ → ℂ} (n : ℕ) (a : ℂ)
    (hf : LSeries.abscissaOfAbsConv f < ⊤) :
    Tendsto
      (fun x : ℝ => (((n + 1 : ℕ) : ℝ) ^ x) *
        (LSeries (lseriesPeeledCoeff (lseriesPowerTwistCoeff f a) n) (x : ℂ)).im)
      atTop (nhds ((f (n + 1) * ((n + 1 : ℕ) : ℂ) ^ a).im)) := by
  have hcomplex := tendsto_cpow_mul_LSeries_peeled (f := lseriesPowerTwistCoeff f a) n
    (lseriesPowerTwistCoeff_abscissa_lt_top hf a)
  have him := Complex.continuous_im.continuousAt.tendsto.comp hcomplex
  convert him using 1
  · funext x
    simp only [Function.comp_apply]
    have hpow : (((n + 1 : ℕ) : ℂ) ^ (x : ℂ)) =
        (((((n + 1 : ℕ) : ℝ) ^ x) : ℝ) : ℂ) := by
      symm
      simpa using Complex.ofReal_cpow (Nat.cast_nonneg (n + 1)) x
    rw [hpow]
    simp
  · rfl

/-- A positive first surviving twisted coefficient forces eventual positive imaginary part. -/
theorem eventually_lseriesPeeledPowerTwist_im_pos
    {f : ℕ → ℂ} (n : ℕ) (a : ℂ)
    (hf : LSeries.abscissaOfAbsConv f < ⊤)
    (hlimit : 0 < (f (n + 1) * ((n + 1 : ℕ) : ℂ) ^ a).im) :
    ∀ᶠ x : ℝ in atTop,
      0 < (LSeries (lseriesPeeledCoeff (lseriesPowerTwistCoeff f a) n) (x : ℂ)).im := by
  have hscaled := tendsto_rpow_mul_im_lseriesPeeledPowerTwist n a hf
  filter_upwards [hscaled.eventually (eventually_gt_nhds hlimit)] with x hx
  have hscale : 0 < (((n + 1 : ℕ) : ℝ) ^ x) := Real.rpow_pos_of_pos (by positivity) x
  exact pos_of_mul_pos_right hx hscale.le

/-- A negative first surviving twisted coefficient forces eventual negative imaginary part. -/
theorem eventually_lseriesPeeledPowerTwist_im_neg
    {f : ℕ → ℂ} (n : ℕ) (a : ℂ)
    (hf : LSeries.abscissaOfAbsConv f < ⊤)
    (hlimit : (f (n + 1) * ((n + 1 : ℕ) : ℂ) ^ a).im < 0) :
    ∀ᶠ x : ℝ in atTop,
      (LSeries (lseriesPeeledCoeff (lseriesPowerTwistCoeff f a) n) (x : ℂ)).im < 0 := by
  have hscaled := tendsto_rpow_mul_im_lseriesPeeledPowerTwist n a hf
  filter_upwards [hscaled.eventually (eventually_lt_nhds hlimit)] with x hx
  have hscale : 0 ≤ (((n + 1 : ℕ) : ℝ) ^ x) :=
    (Real.rpow_pos_of_pos (by positivity) x).le
  exact neg_of_mul_neg_right hx hscale

/-- A finite absolute-convergence abscissa gives eventual convergence on every fixed horizontal
translate of the far-right real ray. -/
theorem eventually_LSeriesSummable_sub_const
    {f : ℕ → ℂ} (hf : LSeries.abscissaOfAbsConv f < ⊤) (a : ℂ) :
    ∀ᶠ x : ℝ in atTop, LSeriesSummable f ((x : ℂ) - a) := by
  obtain ⟨y, hfy, hyt⟩ := exists_between hf
  lift y to ℝ using ⟨hyt.ne, ((OrderBot.bot_le _).trans_lt hfy).ne'⟩
  filter_upwards [eventually_gt_atTop (y + a.re)] with x hx
  apply LSeriesSummable_of_abscissaOfAbsConv_lt_re
  have hre : y < ((x : ℂ) - a).re := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  exact hfy.trans (by exact_mod_cast hre)

/-- If real coefficients `2,...,n` vanish, deleting the prefix through `n` does not change the
imaginary part.  Index `0` contributes no `LSeries` term and index `1` contributes a real constant. -/
theorem lseriesPeeledPowerTwist_im_eq_LSeries_sub
    (f : ℕ → ℝ) (n : ℕ) (a : ℂ) (x : ℝ)
    (hzero : ∀ m : ℕ, 2 ≤ m → m ≤ n → f m = 0)
    (hs : LSeriesSummable (fun m => ((f m : ℝ) : ℂ)) ((x : ℂ) - a)) :
    (LSeries
        (lseriesPeeledCoeff
          (lseriesPowerTwistCoeff (fun m => ((f m : ℝ) : ℂ)) a) n)
        (x : ℂ)).im =
      (LSeries (fun m => ((f m : ℝ) : ℂ)) ((x : ℂ) - a)).im := by
  have htwist : LSeriesSummable
      (lseriesPowerTwistCoeff (fun m => ((f m : ℝ) : ℂ)) a) (x : ℂ) :=
    (LSeriesSummable_powerTwist _ _ _).2 hs
  rw [LSeries_peeled_eq_sub_sum htwist n, LSeries_powerTwist]
  simp only [Complex.sub_im]
  suffices hsum :
      (∑ m ∈ Finset.range (n + 1),
        (LSeries.term (lseriesPowerTwistCoeff (fun j => ((f j : ℝ) : ℂ)) a)
          (x : ℂ) m).im) = 0 by
    rw [Complex.im_sum, hsum, sub_zero]
  apply Finset.sum_eq_zero
  intro m hm
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  rcases m.eq_zero_or_pos with rfl | hmpos
  · simp [LSeries.term_zero]
  rcases eq_or_ne m 1 with rfl | hmone
  · simp [LSeries.term_of_ne_zero, lseriesPowerTwistCoeff]
  have hm2 : 2 ≤ m := by omega
  rw [LSeries.term_of_ne_zero (Nat.ne_of_gt hmpos), lseriesPowerTwistCoeff,
    hzero m hm2 hmn]
  simp

/-- High-line sign rigidity, positive orientation.  If `n+1` is the first possible nonconstant
real coefficient and its twisted phase has positive imaginary part, the raw Dirichlet series has
positive imaginary part eventually on `x-a`. -/
theorem eventually_realLSeries_sub_im_pos
    {f : ℕ → ℝ} (n : ℕ) (a : ℂ)
    (hf : LSeries.abscissaOfAbsConv (fun m => ((f m : ℝ) : ℂ)) < ⊤)
    (hzero : ∀ m : ℕ, 2 ≤ m → m ≤ n → f m = 0)
    (hlimit : 0 < (((f (n + 1) : ℝ) : ℂ) * ((n + 1 : ℕ) : ℂ) ^ a).im) :
    ∀ᶠ x : ℝ in atTop,
      0 < (LSeries (fun m => ((f m : ℝ) : ℂ)) ((x : ℂ) - a)).im := by
  filter_upwards [eventually_lseriesPeeledPowerTwist_im_pos n a hf hlimit,
    eventually_LSeriesSummable_sub_const hf a] with x hsign hs
  rw [← lseriesPeeledPowerTwist_im_eq_LSeries_sub f n a x hzero hs]
  exact hsign

/-- High-line sign rigidity, negative orientation. -/
theorem eventually_realLSeries_sub_im_neg
    {f : ℕ → ℝ} (n : ℕ) (a : ℂ)
    (hf : LSeries.abscissaOfAbsConv (fun m => ((f m : ℝ) : ℂ)) < ⊤)
    (hzero : ∀ m : ℕ, 2 ≤ m → m ≤ n → f m = 0)
    (hlimit : (((f (n + 1) : ℝ) : ℂ) * ((n + 1 : ℕ) : ℂ) ^ a).im < 0) :
    ∀ᶠ x : ℝ in atTop,
      (LSeries (fun m => ((f m : ℝ) : ℂ)) ((x : ℂ) - a)).im < 0 := by
  filter_upwards [eventually_lseriesPeeledPowerTwist_im_neg n a hf hlimit,
    eventually_LSeriesSummable_sub_const hf a] with x hsign hs
  rw [← lseriesPeeledPowerTwist_im_eq_LSeries_sub f n a x hzero hs]
  exact hsign

/-- The raw impedance coordinate of a real ordinary Dirichlet series. -/
def realLSeriesRawImpedance (f : ℕ → ℝ) (z : ℂ) : ℂ :=
  LSeries (fun m => ((f m : ℝ) : ℂ)) (1 - Complex.I * z)

/-- A positive first twisted mode gives positive raw-impedance witnesses above every height. -/
theorem exists_high_realLSeriesRawImpedance_im_pos
    {f : ℕ → ℝ} (n : ℕ) (t Y : ℝ)
    (hf : LSeries.abscissaOfAbsConv (fun m => ((f m : ℝ) : ℂ)) < ⊤)
    (hzero : ∀ m : ℕ, 2 ≤ m → m ≤ n → f m = 0)
    (hlimit : 0 < (((f (n + 1) : ℝ) : ℂ) *
      ((n + 1 : ℕ) : ℂ) ^ ((t : ℂ) * Complex.I)).im) :
    ∃ z : ℂ, Y < z.im ∧ 0 < (realLSeriesRawImpedance f z).im := by
  have hevent := (eventually_realLSeries_sub_im_pos n ((t : ℂ) * Complex.I) hf hzero hlimit).and
    (eventually_gt_atTop (Y + 1))
  obtain ⟨x, hsign, hx⟩ := hevent.exists
  refine ⟨(t : ℂ) + ((x - 1 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero]
    linarith
  · rw [realLSeriesRawImpedance]
    have hcoord : (1 : ℂ) - Complex.I *
        ((t : ℂ) + ((x - 1 : ℝ) : ℂ) * Complex.I) =
        (x : ℂ) - (t : ℂ) * Complex.I := by
      calc
        (1 : ℂ) - Complex.I *
            ((t : ℂ) + ((x - 1 : ℝ) : ℂ) * Complex.I) =
            1 - Complex.I * (t : ℂ) - ((x - 1 : ℝ) : ℂ) *
              (Complex.I * Complex.I) := by ring
        _ = (x : ℂ) - (t : ℂ) * Complex.I := by
          rw [Complex.I_mul_I]
          push_cast
          ring
    rw [hcoord]
    exact hsign

/-- A negative first twisted mode gives negative raw-impedance witnesses above every height. -/
theorem exists_high_realLSeriesRawImpedance_im_neg
    {f : ℕ → ℝ} (n : ℕ) (t Y : ℝ)
    (hf : LSeries.abscissaOfAbsConv (fun m => ((f m : ℝ) : ℂ)) < ⊤)
    (hzero : ∀ m : ℕ, 2 ≤ m → m ≤ n → f m = 0)
    (hlimit : (((f (n + 1) : ℝ) : ℂ) *
      ((n + 1 : ℕ) : ℂ) ^ (-((t : ℂ) * Complex.I))).im < 0) :
    ∃ z : ℂ, Y < z.im ∧ (realLSeriesRawImpedance f z).im < 0 := by
  have hevent := (eventually_realLSeries_sub_im_neg n (-((t : ℂ) * Complex.I)) hf hzero hlimit).and
    (eventually_gt_atTop (Y + 1))
  obtain ⟨x, hsign, hx⟩ := hevent.exists
  refine ⟨(-t : ℂ) + ((x - 1 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.neg_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, zero_mul, add_zero, neg_zero]
    linarith
  · rw [realLSeriesRawImpedance]
    have hcoord : (1 : ℂ) - Complex.I *
        ((-t : ℂ) + ((x - 1 : ℝ) : ℂ) * Complex.I) =
        (x : ℂ) - (-((t : ℂ) * Complex.I)) := by
      calc
        (1 : ℂ) - Complex.I *
            ((-t : ℂ) + ((x - 1 : ℝ) : ℂ) * Complex.I) =
            1 - Complex.I * (-t : ℂ) - ((x - 1 : ℝ) : ℂ) *
              (Complex.I * Complex.I) := by ring
        _ = (x : ℂ) - (-((t : ℂ) * Complex.I)) := by
          rw [Complex.I_mul_I]
          push_cast
          ring
    rw [hcoord]
    exact hsign

/-- A negative first twisted mode excludes every upper-half-plane tail for the raw impedance. -/
theorem realLSeriesRawImpedance_not_upperHalfPlaneValued_above
    {f : ℕ → ℝ} (n : ℕ) (t Y : ℝ)
    (hf : LSeries.abscissaOfAbsConv (fun m => ((f m : ℝ) : ℂ)) < ⊤)
    (hzero : ∀ m : ℕ, 2 ≤ m → m ≤ n → f m = 0)
    (hlimit : (((f (n + 1) : ℝ) : ℂ) *
      ((n + 1 : ℕ) : ℂ) ^ (-((t : ℂ) * Complex.I))).im < 0) :
    ¬ (∀ z : ℂ, Y < z.im → 0 ≤ (realLSeriesRawImpedance f z).im) := by
  intro htail
  obtain ⟨z, hz, hneg⟩ :=
    exists_high_realLSeriesRawImpedance_im_neg n t Y hf hzero hlimit
  exact not_le_of_gt hneg (htail z hz)

/-- A positive first twisted mode excludes every lower-half-plane tail for the raw impedance. -/
theorem realLSeriesRawImpedance_not_lowerHalfPlaneValued_above
    {f : ℕ → ℝ} (n : ℕ) (t Y : ℝ)
    (hf : LSeries.abscissaOfAbsConv (fun m => ((f m : ℝ) : ℂ)) < ⊤)
    (hzero : ∀ m : ℕ, 2 ≤ m → m ≤ n → f m = 0)
    (hlimit : 0 < (((f (n + 1) : ℝ) : ℂ) *
      ((n + 1 : ℕ) : ℂ) ^ ((t : ℂ) * Complex.I)).im) :
    ¬ (∀ z : ℂ, Y < z.im → (realLSeriesRawImpedance f z).im ≤ 0) := by
  intro htail
  obtain ⟨z, hz, hpos⟩ :=
    exists_high_realLSeriesRawImpedance_im_pos n t Y hf hzero hlimit
  exact not_le_of_gt hpos (htail z hz)

end

end GaloisForLFunctions
