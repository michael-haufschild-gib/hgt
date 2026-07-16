import GaloisForLFunctions.RHTower.CCMCriticalMellinGrowingCumulative
import Mathlib.NumberTheory.Chebyshev
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Elementary finite-aperture bound for the growing critical Mellin cumulative

The Poisson-center cross term only sees the growing cumulative at a finite clipped height.  The
elementary Chebyshev bound `Psi(x) = O(x)` is therefore sufficient: no prime-number-theorem
remainder or zero-free region is required.
-/

open Real MeasureTheory

noncomputable section

namespace RHTower

/-- The project cumulative of the von Mangoldt coefficients is exactly Chebyshev's `psi`. -/
theorem criticalCumulative_vonMangoldt_eq_chebyshevPsi (x : ℝ) :
    criticalCumulative (fun k => ArithmeticFunction.vonMangoldt k) x = Chebyshev.psi x := by
  rw [criticalCumulative, Chebyshev.psi_eq_sum_Icc]

/-- Height-coordinate form of the growing cumulative. -/
def criticalMellinGrowingCumulativeAtHeight (h : ℝ) : ℝ :=
  criticalMellinGrowingCumulative (h / 2)

/-- At nonnegative height, the growing cumulative is the exponential main term plus height minus
the ordinary Chebyshev cumulative. -/
theorem criticalMellinGrowingCumulativeAtHeight_eq
    {h : ℝ} (hh : 0 ≤ h) :
    criticalMellinGrowingCumulativeAtHeight h =
      Real.exp h - 1 + h - Chebyshev.psi (Real.exp h) := by
  rw [criticalMellinGrowingCumulativeAtHeight,
    criticalMellinGrowingCumulative_eq (div_nonneg hh (by norm_num)),
    criticalCumulative_vonMangoldt_eq_chebyshevPsi]
  congr 2 <;> ring_nf

/-- **Elementary growing-cumulative bound.**  The finite-aperture center channel needs only
Chebyshev's linear upper bound.  The estimate is explicit and unconditional. -/
theorem abs_criticalMellinGrowingCumulativeAtHeight_le
    {h : ℝ} (hh : 0 ≤ h) :
    |criticalMellinGrowingCumulativeAtHeight h| ≤
      1 + h + (Real.log 4 + 5) * Real.exp h := by
  have hexp0 : 0 ≤ Real.exp h := (Real.exp_pos h).le
  have hpsi0 : 0 ≤ Chebyshev.psi (Real.exp h) := Chebyshev.psi_nonneg _
  have hpsi : Chebyshev.psi (Real.exp h) ≤
      (Real.log 4 + 4) * Real.exp h :=
    Chebyshev.psi_le_const_mul_self hexp0
  rw [criticalMellinGrowingCumulativeAtHeight_eq hh]
  calc
    |Real.exp h - 1 + h - Chebyshev.psi (Real.exp h)| ≤
        |Real.exp h| + |(1 : ℝ)| + |h| + |Chebyshev.psi (Real.exp h)| := by
      calc
        |Real.exp h - 1 + h - Chebyshev.psi (Real.exp h)| ≤
            |Real.exp h - 1 + h| + |Chebyshev.psi (Real.exp h)| := abs_sub _ _
        _ ≤ (|Real.exp h - 1| + |h|) + |Chebyshev.psi (Real.exp h)| := by
          gcongr
          exact abs_add_le _ _
        _ ≤ ((|Real.exp h| + |(1 : ℝ)|) + |h|) +
            |Chebyshev.psi (Real.exp h)| := by
          gcongr
          exact abs_sub _ _
        _ = |Real.exp h| + |(1 : ℝ)| + |h| +
            |Chebyshev.psi (Real.exp h)| := by ring
    _ = Real.exp h + 1 + h + Chebyshev.psi (Real.exp h) := by
      rw [abs_of_nonneg hexp0, abs_one, abs_of_nonneg hh, abs_of_nonneg hpsi0]
    _ ≤ Real.exp h + 1 + h + (Real.log 4 + 4) * Real.exp h := by gcongr
    _ = 1 + h + (Real.log 4 + 5) * Real.exp h := by ring

/-- The exponentially weighted growing cumulative is uniformly bounded on the whole nonnegative
ray.  This is the pointwise estimate consumed by the finite-aperture center pairing. -/
theorem exp_neg_mul_abs_criticalMellinGrowingCumulativeAtHeight_le
    {h : ℝ} (hh : 0 ≤ h) :
    Real.exp (-h) * |criticalMellinGrowingCumulativeAtHeight h| ≤ Real.log 4 + 7 := by
  have hraw := abs_criticalMellinGrowingCumulativeAtHeight_le hh
  have hexpNeg0 : 0 ≤ Real.exp (-h) := (Real.exp_pos _).le
  have hexpNegLe : Real.exp (-h) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hleexp : h ≤ Real.exp h :=
    (le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp h)
  have hmul : h * Real.exp (-h) ≤ 1 := by
    calc
      h * Real.exp (-h) ≤ Real.exp h * Real.exp (-h) :=
        mul_le_mul_of_nonneg_right hleexp hexpNeg0
      _ = 1 := by rw [← Real.exp_add]; simp
  calc
    Real.exp (-h) * |criticalMellinGrowingCumulativeAtHeight h| ≤
        Real.exp (-h) * (1 + h + (Real.log 4 + 5) * Real.exp h) :=
      mul_le_mul_of_nonneg_left hraw hexpNeg0
    _ = Real.exp (-h) + h * Real.exp (-h) +
        (Real.log 4 + 5) * (Real.exp (-h) * Real.exp h) := by ring
    _ = Real.exp (-h) + h * Real.exp (-h) + (Real.log 4 + 5) := by
      rw [← Real.exp_add]
      simp
    _ ≤ 1 + 1 + (Real.log 4 + 5) := by linarith
    _ = Real.log 4 + 7 := by ring

/-- The weighted absolute growing cumulative is genuinely interval-integrable on every finite
nonnegative aperture. -/
theorem intervalIntegrable_exp_neg_mul_abs_criticalMellinGrowingCumulativeAtHeight
    {H : ℝ} (hH : 0 ≤ H) :
    IntervalIntegrable
      (fun t : ℝ => Real.exp (-t) * |criticalMellinGrowingCumulativeAtHeight t|)
      (volume : MeasureTheory.Measure ℝ) 0 H := by
  let model : ℝ → ℝ := fun t => Real.exp t - 1 + t - Chebyshev.psi (Real.exp t)
  have hpsiMono : Monotone (fun t : ℝ => Chebyshev.psi (Real.exp t)) :=
    Chebyshev.psi_mono.comp Real.exp_monotone
  have hmodelInt : IntervalIntegrable model (volume : MeasureTheory.Measure ℝ) 0 H := by
    have hcont : Continuous (fun t : ℝ => Real.exp t - 1 + t) := by fun_prop
    have hcontInt : IntervalIntegrable (fun t : ℝ => Real.exp t - 1 + t)
        (volume : MeasureTheory.Measure ℝ) 0 H :=
      Continuous.intervalIntegrable (μ := (volume : MeasureTheory.Measure ℝ)) hcont 0 H
    have hpsiInt : IntervalIntegrable (fun t : ℝ => Chebyshev.psi (Real.exp t))
        (volume : MeasureTheory.Measure ℝ) 0 H :=
      Monotone.intervalIntegrable (μ := (volume : MeasureTheory.Measure ℝ)) hpsiMono
    exact hcontInt.sub hpsiInt
  have hJInt : IntervalIntegrable criticalMellinGrowingCumulativeAtHeight
      (volume : MeasureTheory.Measure ℝ) 0 H := by
    apply (hmodelInt.congr ?_)
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : ℝ) H := by
      have ht' : t ∈ Set.uIcc (0 : ℝ) H := Set.uIoc_subset_uIcc ht
      simpa only [Set.uIcc_of_le hH] using ht'
    exact (criticalMellinGrowingCumulativeAtHeight_eq htIcc.1).symm
  exact hJInt.abs.continuousOn_mul (by fun_prop)

/-- The exact scalar mass controlling a center cross term clipped at height `H`.  The first term
is the active aperture and the second is the exponentially weighted frozen tail. -/
def criticalMellinFiniteApertureCenterMass (H : ℝ) : ℝ :=
  (∫ t in 0..H,
      Real.exp (-t) * |criticalMellinGrowingCumulativeAtHeight t|) +
    Real.exp (-H) * |criticalMellinGrowingCumulativeAtHeight H|

/-- **Finite-aperture center bound.**  The clipped growing critical-Mellin channel costs only
linearly in the aperture.  This uses Chebyshev's elementary `Psi(x) = O(x)` bound and no PNT
remainder. -/
theorem criticalMellinFiniteApertureCenterMass_le
    {H : ℝ} (hH : 0 ≤ H) :
    criticalMellinFiniteApertureCenterMass H ≤
      (Real.log 4 + 7) * (H + 1) := by
  let C : ℝ := Real.log 4 + 7
  have hactive :
      ‖∫ t in 0..H,
          Real.exp (-t) * |criticalMellinGrowingCumulativeAtHeight t|‖ ≤ C * H := by
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const_ae
      (a := (0 : ℝ)) (b := H) (C := C)
      (f := fun t : ℝ => Real.exp (-t) *
        |criticalMellinGrowingCumulativeAtHeight t|) (by
        filter_upwards with t ht
        have htIcc : t ∈ Set.Icc (0 : ℝ) H := by
          have ht' : t ∈ Set.uIcc (0 : ℝ) H := Set.uIoc_subset_uIcc ht
          simpa only [Set.uIcc_of_le hH] using ht'
        have ht0 : 0 ≤ t := htIcc.1
        have hpoint := exp_neg_mul_abs_criticalMellinGrowingCumulativeAtHeight_le ht0
        have hnonneg : 0 ≤ Real.exp (-t) *
            |criticalMellinGrowingCumulativeAtHeight t| :=
          mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
        simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg, C] using hpoint)
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hH] using hnorm
  have htail :
      Real.exp (-H) * |criticalMellinGrowingCumulativeAtHeight H| ≤ C := by
    simpa only [C] using
      exp_neg_mul_abs_criticalMellinGrowingCumulativeAtHeight_le hH
  rw [criticalMellinFiniteApertureCenterMass]
  calc
      (∫ t in 0..H,
        Real.exp (-t) * |criticalMellinGrowingCumulativeAtHeight t|) +
        Real.exp (-H) * |criticalMellinGrowingCumulativeAtHeight H| ≤
      ‖∫ t in 0..H,
        Real.exp (-t) * |criticalMellinGrowingCumulativeAtHeight t|‖ +
        Real.exp (-H) * |criticalMellinGrowingCumulativeAtHeight H| := by
          gcongr
          simpa only [Real.norm_eq_abs] using
            (le_abs_self (∫ t in 0..H,
              Real.exp (-t) * |criticalMellinGrowingCumulativeAtHeight t|))
    _ ≤ C * H + C := add_le_add hactive htail
    _ = (Real.log 4 + 7) * (H + 1) := by simp only [C]; ring

end RHTower
