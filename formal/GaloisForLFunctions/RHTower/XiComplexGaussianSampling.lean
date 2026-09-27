import GaloisForLFunctions.RHTower.XiScaledEvenGaussianEnergy
import GaloisForLFunctions.RHTower.XiRealAxisGaussianSampling
import GaloisForLFunctions.HTGeometry.GaussianStripSamplingError

/-!
# Actual complex Xi sampling controls Gaussian half-line mass

Injective copies in disjoint adjacent zero windows provide real grid samples.
The discrete strip estimate moves each sample to its own actual complex Xi
coordinate. Every polynomial term and the full Gaussian phase are retained.
-/

open scoped Real SchwartzMap NNReal
open Complex MeasureTheory Filter Topology GaloisForLFunctions
noncomputable section

namespace RHTower

/-- Half-line Gaussian mass is controlled by complete complex Xi energy and independent errors. -/
theorem exists_xiComplexGaussian_halfLine_sampling_bound :
    ∃ a : ℝ, 0 < a ∧ ∃ h : ℝ, 0 < h ∧
      ∀ (P : Polynomial ℝ) (r : {r : ℝ // 0 < r}),
        (∫ x : ℝ in Set.Ioi ((r : ℝ) * a),
          ‖polyGaussSchwartz (evenSquarePolynomial P) x‖ ^ 2) ≤
          2 * ((r : ℝ) * h) * xiScaledEvenGaussianEnergy P r +
            (2 * ((r : ℝ) * h) *
                Real.sqrt (4 * π * (((evenSquarePolynomial P).natDegree : ℝ) + 1)) +
              2 * (1 + 2 * ((r : ℝ) * h) *
                Real.sqrt (4 * π * (((evenSquarePolynomial P).natDegree : ℝ) + 2))) *
                verticalPolynomialGaussianDefect (evenSquarePolynomial P).natDegree ((r : ℝ) / 2) ^ 2) *
              ‖(polyGaussSchwartz (evenSquarePolynomial P)).toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
  classical
  obtain ⟨a, ha, h, hh, q, hqinj, hq⟩ := exists_xiRealAxis_sampling_grid
  refine ⟨a, ha, h, hh, ?_⟩
  intro P r
  let Q := evenSquarePolynomial P
  let f := polyGaussSchwartz Q
  let M : ℝ := ‖f.toLp 2 (volume : Measure ℝ)‖ ^ 2
  let A : ℝ := Real.sqrt (4 * π * ((Q.natDegree : ℝ) + 1))
  let E : ℝ := (1 + 2 * ((r : ℝ) * h) * Real.sqrt (4 * π * ((Q.natDegree : ℝ) + 2))) *
    verticalPolynomialGaussianDefect Q.natDegree ((r : ℝ) / 2) ^ 2
  let s : ℕ → Set.Icc (0 : ℝ) 1 := fun j =>
    ⟨((xiSpectralPoint (q j)).re - (a + (j : ℝ) * h)) / h, by
      constructor
      · exact div_nonneg (sub_nonneg.mpr (hq j).1.le) hh.le
      · apply (div_le_iff₀ hh).mpr
        linarith only [(hq j).2]⟩
  let mesh : ℝ≥0 := ⟨(r : ℝ) * h, (mul_pos r.property hh).le⟩
  let radius : ℝ≥0 := ⟨(r : ℝ) / 2, div_nonneg r.property.le (by positivity)⟩
  have him (j : ℕ) : -(1 / 2 : ℝ) ≤ (xiSpectralPoint (q j)).im ∧
      (xiSpectralPoint (q j)).im ≤ 1 / 2 := by
    have hs := xi_divisor_support_re_mem_open_unit (q j).1
    have he : (xiSpectralPoint (q j)).im = -(((q j).1 : ℂ).re - 1 / 2) := by
      simp [xiSpectralPoint]
    rw [he]
    constructor <;> linarith only [hs.1, hs.2]
  let δ : ℕ → Set.Icc (-(radius : ℝ)) radius := fun j =>
    ⟨(r : ℝ) * (xiSpectralPoint (q j)).im, by
      constructor
      · have ht := mul_le_mul_of_nonneg_left (him j).1 r.property.le
        change -((r : ℝ) / 2) ≤ (r : ℝ) * (xiSpectralPoint (q j)).im
        linarith only [ht]
      · have ht := mul_le_mul_of_nonneg_left (him j).2 r.property.le
        change (r : ℝ) * (xiSpectralPoint (q j)).im ≤ (r : ℝ) / 2
        linarith only [ht]⟩
  have hsample (j : ℕ) :
      (r : ℝ) * a + ((j : ℝ) + (s j : ℝ)) * mesh =
        (r : ℝ) * (xiSpectralPoint (q j)).re := by
    change (r : ℝ) * a + ((j : ℝ) +
      ((xiSpectralPoint (q j)).re - (a + (j : ℝ) * h)) / h) * ((r : ℝ) * h) =
        (r : ℝ) * (xiSpectralPoint (q j)).re
    field_simp [hh.ne']
    ring
  have herror (N : ℕ) :
      ((r : ℝ) * h) * ∑ j ∈ Finset.range N,
        ‖xiScaledEvenGaussianAmplitude P r (q j) -
          f ((r : ℝ) * (xiSpectralPoint (q j)).re)‖ ^ 2 ≤ E * M := by
    have he := gaussianPolynomial_grid_variableShift_error Q radius ((r : ℝ) * a) mesh s N δ
    simp_rw [hsample] at he
    change ((r : ℝ) * h) * ∑ j ∈ Finset.range N,
      ‖Q.eval₂ (algebraMap ℝ ℂ)
          ((((r : ℝ) * (xiSpectralPoint (q j)).re : ℝ) : ℂ) +
            (((r : ℝ) * (xiSpectralPoint (q j)).im : ℝ) : ℂ) * Complex.I) *
          Complex.exp (-(π : ℂ) *
            ((((r : ℝ) * (xiSpectralPoint (q j)).re : ℝ) : ℂ) +
              (((r : ℝ) * (xiSpectralPoint (q j)).im : ℝ) : ℂ) * Complex.I) ^ 2) -
        f ((r : ℝ) * (xiSpectralPoint (q j)).re)‖ ^ 2 ≤ E * M at he
    simpa only [Q, ← xiScaledEvenGaussianAmplitude_vertical] using he
  have henergy (N : ℕ) :
      (∑ j ∈ Finset.range N, ‖xiScaledEvenGaussianAmplitude P r (q j)‖ ^ 2) ≤
        xiScaledEvenGaussianEnergy P r := by
    rw [← Finset.sum_image (f := fun z : XiZeroCopy => ‖xiScaledEvenGaussianAmplitude P r z‖ ^ 2)
      (s := Finset.range N) (g := q) (fun i _ j _ hij => hqinj hij)]
    exact (summable_xiScaledEvenGaussianAmplitude_norm_sq P r).sum_le_tsum _
      (fun _ _ => sq_nonneg _)
  have href (j : ℕ) :
      ‖f ((r : ℝ) * (xiSpectralPoint (q j)).re)‖ ^ 2 ≤
        2 * ‖xiScaledEvenGaussianAmplitude P r (q j)‖ ^ 2 +
          2 * ‖xiScaledEvenGaussianAmplitude P r (q j) -
            f ((r : ℝ) * (xiSpectralPoint (q j)).re)‖ ^ 2 := by
    have ht := norm_le_norm_add_norm_sub (xiScaledEvenGaussianAmplitude P r (q j))
      (f ((r : ℝ) * (xiSpectralPoint (q j)).re))
    have hp := pow_le_pow_left₀ (norm_nonneg _) ht 2
    nlinarith only [hp, sq_nonneg (‖xiScaledEvenGaussianAmplitude P r (q j)‖ -
      ‖xiScaledEvenGaussianAmplitude P r (q j) - f ((r : ℝ) * (xiSpectralPoint (q j)).re)‖)]
  have hfinite (N : ℕ) :
      (∫ x in (r : ℝ) * a..(r : ℝ) * a + (N : ℝ) * ((r : ℝ) * h), ‖f x‖ ^ 2) ≤
        2 * ((r : ℝ) * h) * xiScaledEvenGaussianEnergy P r +
          (2 * ((r : ℝ) * h) * A + 2 * E) * M := by
    have hsum := Finset.sum_le_sum (s := Finset.range N) (fun j _ => href j)
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
    have hsum' := mul_le_mul_of_nonneg_left hsum (mul_pos r.property hh).le
    have hK := mul_le_mul_of_nonneg_left (henergy N) (mul_pos r.property hh).le
    have hquad := gaussianPolynomial_grid_quadrature_error Q ((r : ℝ) * a) mesh s N
    simp_rw [hsample] at hquad
    have hupper := (abs_le.mp hquad).2
    change (∫ x in (r : ℝ) * a..(r : ℝ) * a + (N : ℝ) * ((r : ℝ) * h), ‖f x‖ ^ 2) -
      ((r : ℝ) * h) * (∑ j ∈ Finset.range N, ‖f ((r : ℝ) * (xiSpectralPoint (q j)).re)‖ ^ 2) ≤
        2 * ((r : ℝ) * h) * A * M at hupper
    nlinarith only [hsum', hK, herror N, hupper]
  have hint : Integrable (fun x : ℝ => ‖f x‖ ^ (2 : ℕ)) :=
    (memLp_two_iff_integrable_sq_norm f.continuous.aestronglyMeasurable).mp
      (f.memLp 2 (volume : Measure ℝ))
  have htop : Tendsto (fun N : ℕ => (r : ℝ) * a + (N : ℝ) * ((r : ℝ) * h))
      atTop atTop :=
    tendsto_atTop_add_const_left atTop ((r : ℝ) * a)
      ((tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).atTop_mul_const
        (mul_pos r.property hh))
  have hlim := le_of_tendsto' (intervalIntegral_tendsto_integral_Ioi ((r : ℝ) * a)
    hint.integrableOn htop) hfinite
  simpa only [Q, f, M, A, E, mul_assoc] using hlim

end RHTower
