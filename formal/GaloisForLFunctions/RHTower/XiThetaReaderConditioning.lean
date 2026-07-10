import GaloisForLFunctions.RHTower.XiThetaLogTranslationSeam
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Superexponential conditioning of correct theta coefficient readers

The completed critical trace is Fourier in the logarithmic coordinate. This file measures the
actual positive-half atoms in that coordinate rather than importing a Laplace-variable reader.

The m-th atom has L1 norm and pointwise Fourier transform bounded by exp(-pi m squared). Therefore
every continuous L1 reader normalized on that atom has operator norm at least exp(pi m squared).
Every reader built from finitely many critical Fourier samples has total coefficient weight at
least the same amount.

This rules out uniformly stable finite-sample and L1-continuous coefficient extraction on the
physical positive source. It does not rule out a reader in a stronger analytic topology.
-/

open Complex Real MeasureTheory Set Filter Topology HurwitzZeta
open scoped ENNReal Topology FourierTransform

noncomputable section

namespace RHTower

/-- The m-th logarithmic theta atom after strict positive truncation. -/
def thetaPositiveSquareLogAtom (m : ℕ) (u : ℝ) : ℂ :=
  (positiveLogTruncation (thetaSquareLogAtom m) u : ℝ)

/-- An integrable exponential majorant with total mass exp(-pi m squared). -/
def thetaSquareL1Majorant (m : ℕ) (u : ℝ) : ℝ :=
  (Ioi (0 : ℝ)).indicator
    (fun v => 2 * Real.exp (-π * (m : ℝ) ^ 2) * Real.exp (-2 * v)) u

/-- The physical square atom has a uniform exponential tail beyond the positive boundary. -/
theorem thetaSquareLogAtom_le_exp_majorant {m : ℕ} (hm : 1 ≤ m)
    {u : ℝ} (hu : 0 ≤ u) :
    thetaSquareLogAtom m u ≤
      2 * Real.exp (-π * (m : ℝ) ^ 2) * Real.exp (-2 * u) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmSq : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  have hpi : (3 : ℝ) < π := Real.pi_gt_three
  have hexp : 1 + u ≤ Real.exp u := by
    nlinarith [Real.add_one_le_exp u]
  have hA : (9 : ℝ) / 4 ≤ π * (m : ℝ) ^ 2 := by
    have hpiSq : π ≤ π * (m : ℝ) ^ 2 := by
      simpa only [mul_one] using
        (mul_le_mul_of_nonneg_left hmSq Real.pi_nonneg)
    linarith
  have hexpdiff : u ≤ Real.exp u - 1 := by linarith
  have hprod : π * (m : ℝ) ^ 2 * u ≤
      π * (m : ℝ) ^ 2 * (Real.exp u - 1) :=
    mul_le_mul_of_nonneg_left hexpdiff
      (mul_nonneg Real.pi_nonneg (sq_nonneg (m : ℝ)))
  have hlinear : (9 : ℝ) / 4 * u ≤ π * (m : ℝ) ^ 2 * u :=
    mul_le_mul_of_nonneg_right hA hu
  have hexponent :
      u / 4 - π * (m : ℝ) ^ 2 * Real.exp u ≤
        -π * (m : ℝ) ^ 2 - 2 * u := by
    nlinarith
  rw [thetaSquareLogAtom]
  calc
    2 * Real.exp (u / 4) * Real.exp (-π * (m : ℝ) ^ 2 * Real.exp u) =
        2 * Real.exp (u / 4 - π * (m : ℝ) ^ 2 * Real.exp u) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring
    _ ≤ 2 * Real.exp (-π * (m : ℝ) ^ 2 - 2 * u) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by norm_num)
    _ = 2 * Real.exp (-π * (m : ℝ) ^ 2) * Real.exp (-2 * u) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 2
      ring

theorem thetaPositiveSquareLogAtom_norm_le_majorant {m : ℕ} (hm : 1 ≤ m) (u : ℝ) :
    ‖thetaPositiveSquareLogAtom m u‖ ≤ thetaSquareL1Majorant m u := by
  by_cases hu : 0 < u
  · rw [thetaPositiveSquareLogAtom, positiveLogTruncation,
      indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu),
      thetaSquareL1Majorant, indicator_of_mem (show u ∈ Ioi (0 : ℝ) from hu)]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    · exact thetaSquareLogAtom_le_exp_majorant hm hu.le
    · exact mul_nonneg (mul_nonneg (by norm_num) (Real.exp_pos _).le) (Real.exp_pos _).le
  · have hmem : u ∉ Ioi (0 : ℝ) := hu
    simp [thetaPositiveSquareLogAtom, positiveLogTruncation,
      thetaSquareL1Majorant, hmem]

theorem thetaSquareL1Majorant_integrable (m : ℕ) :
    Integrable (thetaSquareL1Majorant m) := by
  unfold thetaSquareL1Majorant
  rw [integrable_indicator_iff measurableSet_Ioi]
  exact (integrableOn_exp_mul_Ioi (a := (-2 : ℝ)) (by norm_num) 0).const_mul
    (2 * Real.exp (-π * (m : ℝ) ^ 2))

theorem integral_thetaSquareL1Majorant (m : ℕ) :
    ∫ u : ℝ, thetaSquareL1Majorant m u =
      Real.exp (-π * (m : ℝ) ^ 2) := by
  unfold thetaSquareL1Majorant
  rw [integral_indicator measurableSet_Ioi, integral_const_mul,
    integral_exp_mul_Ioi (a := (-2 : ℝ)) (by norm_num) 0]
  simp
  ring

theorem thetaPositiveSquareLogAtom_integrable {m : ℕ} (hm : 1 ≤ m) :
    Integrable (thetaPositiveSquareLogAtom m) := by
  refine (thetaSquareL1Majorant_integrable m).mono' ?_ ?_
  · have hcont : Continuous (thetaSquareLogAtom m) := by
      unfold thetaSquareLogAtom
      fun_prop
    unfold thetaPositiveSquareLogAtom positiveLogTruncation
    exact (hcont.measurable.indicator measurableSet_Ioi).complex_ofReal.aestronglyMeasurable
  · exact ae_of_all _ (thetaPositiveSquareLogAtom_norm_le_majorant hm)

/-- The correct positive-half atom has L1 mass at most exp(-pi m squared). -/
theorem integral_norm_thetaPositiveSquareLogAtom_le {m : ℕ} (hm : 1 ≤ m) :
    (∫ u : ℝ, ‖thetaPositiveSquareLogAtom m u‖) ≤
      Real.exp (-π * (m : ℝ) ^ 2) := by
  calc
    (∫ u : ℝ, ‖thetaPositiveSquareLogAtom m u‖) ≤
        ∫ u : ℝ, thetaSquareL1Majorant m u := by
      exact integral_mono_ae (thetaPositiveSquareLogAtom_integrable hm).norm
        (thetaSquareL1Majorant_integrable m)
        (ae_of_all _ (thetaPositiveSquareLogAtom_norm_le_majorant hm))
    _ = Real.exp (-π * (m : ℝ) ^ 2) := integral_thetaSquareL1Majorant m

/-- Every critical Fourier sample of the m-th physical atom is superexponentially small. -/
theorem norm_fourier_thetaPositiveSquareLogAtom_le {m : ℕ} (hm : 1 ≤ m) (w : ℝ) :
    ‖𝓕 (thetaPositiveSquareLogAtom m) w‖ ≤
      Real.exp (-π * (m : ℝ) ^ 2) := by
  exact le_trans
    (VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar
      (volume : Measure ℝ) (innerₗ ℝ) (thetaPositiveSquareLogAtom m) w)
    (integral_norm_thetaPositiveSquareLogAtom_le hm)

/-- A finite critical-trace sampler normalized on the m-th atom must have total weight at least
exp(pi m squared). -/
theorem thetaFiniteSample_reader_condition_number_lower
    {ι : Type*} {m : ℕ} (hm : 1 ≤ m) (s : Finset ι)
    (frequency : ι → ℝ) (weight : ι → ℂ)
    (hread : ∑ i ∈ s, weight i * 𝓕 (thetaPositiveSquareLogAtom m) (frequency i) = 1) :
    Real.exp (π * (m : ℝ) ^ 2) ≤ ∑ i ∈ s, ‖weight i‖ := by
  have hsum :
      1 ≤ (∑ i ∈ s, ‖weight i‖) * Real.exp (-π * (m : ℝ) ^ 2) := by
    calc
      1 = ‖∑ i ∈ s, weight i *
          𝓕 (thetaPositiveSquareLogAtom m) (frequency i)‖ := by rw [hread, norm_one]
      _ ≤ ∑ i ∈ s, ‖weight i *
          𝓕 (thetaPositiveSquareLogAtom m) (frequency i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ s, ‖weight i‖ * Real.exp (-π * (m : ℝ) ^ 2) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          (norm_fourier_thetaPositiveSquareLogAtom_le hm (frequency i)) (norm_nonneg _)
      _ = (∑ i ∈ s, ‖weight i‖) * Real.exp (-π * (m : ℝ) ^ 2) := by
        rw [Finset.sum_mul]
  have hpos : 0 < Real.exp (π * (m : ℝ) ^ 2) := Real.exp_pos _
  have hcancel : Real.exp (π * (m : ℝ) ^ 2) *
      Real.exp (-π * (m : ℝ) ^ 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring_nf
  calc
    Real.exp (π * (m : ℝ) ^ 2) =
        Real.exp (π * (m : ℝ) ^ 2) * 1 := by ring
    _ ≤ Real.exp (π * (m : ℝ) ^ 2) *
        ((∑ i ∈ s, ‖weight i‖) * Real.exp (-π * (m : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hsum hpos.le
    _ = (∑ i ∈ s, ‖weight i‖) *
        (Real.exp (π * (m : ℝ) ^ 2) *
          Real.exp (-π * (m : ℝ) ^ 2)) := by ring
    _ = ∑ i ∈ s, ‖weight i‖ := by rw [hcancel, mul_one]

def thetaPositiveSquareLogAtomL1 (m : ℕ) (hm : 1 ≤ m) :
    ℝ →₁[(volume : Measure ℝ)] ℂ :=
  (thetaPositiveSquareLogAtom_integrable hm).toL1 _

theorem norm_thetaPositiveSquareLogAtomL1_le {m : ℕ} (hm : 1 ≤ m) :
    ‖thetaPositiveSquareLogAtomL1 m hm‖ ≤ Real.exp (-π * (m : ℝ) ^ 2) := by
  rw [thetaPositiveSquareLogAtomL1,
    L1.norm_of_fun_eq_integral_norm (thetaPositiveSquareLogAtom_integrable hm)]
  exact integral_norm_thetaPositiveSquareLogAtom_le hm

/-- Every L1-continuous reader normalized on the m-th physical atom has norm at least
exp(pi m squared). -/
theorem thetaL1_reader_condition_number_lower {m : ℕ} (hm : 1 ≤ m)
    (reader : (ℝ →₁[(volume : Measure ℝ)] ℂ) →L[ℂ] ℂ)
    (hread : reader (thetaPositiveSquareLogAtomL1 m hm) = 1) :
    Real.exp (π * (m : ℝ) ^ 2) ≤ ‖reader‖ := by
  have hnorm := reader.le_opNorm (thetaPositiveSquareLogAtomL1 m hm)
  rw [hread, norm_one] at hnorm
  have hsmall := norm_thetaPositiveSquareLogAtomL1_le hm
  have hreadnn : 0 ≤ ‖reader‖ := norm_nonneg _
  have hchain : 1 ≤ ‖reader‖ * Real.exp (-π * (m : ℝ) ^ 2) :=
    le_trans hnorm (mul_le_mul_of_nonneg_left hsmall hreadnn)
  have hpos : 0 < Real.exp (π * (m : ℝ) ^ 2) := Real.exp_pos _
  have hcancel : Real.exp (π * (m : ℝ) ^ 2) *
      Real.exp (-π * (m : ℝ) ^ 2) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring_nf
  calc
    Real.exp (π * (m : ℝ) ^ 2) =
        Real.exp (π * (m : ℝ) ^ 2) * 1 := by ring
    _ ≤ Real.exp (π * (m : ℝ) ^ 2) *
        (‖reader‖ * Real.exp (-π * (m : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hchain hpos.le
    _ = ‖reader‖ * (Real.exp (π * (m : ℝ) ^ 2) *
        Real.exp (-π * (m : ℝ) ^ 2)) := by ring
    _ = ‖reader‖ := by rw [hcancel, mul_one]

end RHTower
