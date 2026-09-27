import GaloisForLFunctions.RHTower.XiRealAxisSchwartzEnergy
import GaloisForLFunctions.RHTower.XiHeatQuadraticSamplingBands
import GaloisForLFunctions.HTGeometry.GaussianPolynomialSamplingError
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Gaussian sampling on actual Xi ordinates

Disjoint fixed-width windows provide an injective sequence of actual divisor
copies. The complete real-ordinate energy dominates their samples. Gaussian
quadrature and the infinite-interval limit give a lower sampling bound uniform
over all polynomial coefficients and all positive spatial scales.
-/

open scoped Real SchwartzMap NNReal
open MeasureTheory Filter Topology
open GaloisForLFunctions
noncomputable section

namespace RHTower

/-- Disjoint adjacent windows supply distinct actual Xi divisor copies indefinitely. -/
theorem exists_xiRealAxis_sampling_grid :
    ∃ a : ℝ, 0 < a ∧ ∃ h : ℝ, 0 < h ∧ ∃ q : ℕ → XiZeroCopy,
      Function.Injective q ∧ ∀ j : ℕ,
        a + (j : ℝ) * h < (xiSpectralPoint (q j)).re ∧
          (xiSpectralPoint (q j)).re ≤ a + ((j : ℝ) + 1) * h := by
  classical
  obtain ⟨w, hw, a, ha, hwin⟩ := exists_xiSpectralPoint_in_bounded_windows
  have hall (j : ℕ) : ∃ q : XiZeroCopy,
      a + (j : ℝ) * (2 * w) < (xiSpectralPoint q).re ∧
        (xiSpectralPoint q).re ≤ a + ((j : ℝ) + 1) * (2 * w) := by
    obtain ⟨q, hL, hU⟩ := hwin (a + (2 * (j : ℝ) + 1) * w)
      (le_add_of_nonneg_right (by positivity))
    refine ⟨q, ?_, ?_⟩ <;> linarith only [hL, hU]
  choose q hq using hall
  have hmono : StrictMono (fun j : ℕ => (xiSpectralPoint (q j)).re) := by
    intro i j hij
    have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hij
    have hstep := mul_le_mul_of_nonneg_right hcast (by positivity : 0 ≤ 2 * w)
    linarith only [(hq i).2, (hq j).1, hstep]
  refine ⟨a, ha, 2 * w, by positivity, q, ?_, hq⟩
  intro i j hij
  exact hmono.injective (congrArg (fun z => (xiSpectralPoint z).re) hij)

/-- The actual Xi real-ordinate energy controls Gaussian half-line mass up to mesh error. -/
theorem exists_xiRealAxisGaussian_halfLine_sampling_bound :
    ∃ a : ℝ, 0 < a ∧ ∃ h : ℝ, 0 < h ∧
      ∀ (P : Polynomial ℝ) (r : {r : ℝ // 0 < r}),
        (∫ x : ℝ in Set.Ioi ((r : ℝ) * a), ‖polyGaussSchwartz P x‖ ^ 2) ≤
          ((r : ℝ) * h) * xiRealAxisSchwartzEnergy (polyGaussSchwartz P) r +
            2 * ((r : ℝ) * h) * Real.sqrt (4 * Real.pi * ((P.natDegree : ℝ) + 1)) *
              ‖(polyGaussSchwartz P).toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
  classical
  obtain ⟨a, ha, h, hh, q, hqinj, hq⟩ := exists_xiRealAxis_sampling_grid
  refine ⟨a, ha, h, hh, ?_⟩
  intro P r
  let f := polyGaussSchwartz P
  let s : ℕ → Set.Icc (0 : ℝ) 1 := fun j =>
    ⟨((xiSpectralPoint (q j)).re - (a + (j : ℝ) * h)) / h, by
      constructor
      · exact div_nonneg (sub_nonneg.mpr (hq j).1.le) hh.le
      · apply (div_le_iff₀ hh).mpr
        linarith only [(hq j).2]⟩
  let mesh : ℝ≥0 := ⟨(r : ℝ) * h, (mul_pos r.property hh).le⟩
  have hsample (j : ℕ) :
      (r : ℝ) * a + ((j : ℝ) + (s j : ℝ)) * mesh =
        (r : ℝ) * (xiSpectralPoint (q j)).re := by
    change (r : ℝ) * a + ((j : ℝ) +
      ((xiSpectralPoint (q j)).re - (a + (j : ℝ) * h)) / h) * ((r : ℝ) * h) =
        (r : ℝ) * (xiSpectralPoint (q j)).re
    field_simp [hh.ne']
    ring
  have hsum (N : ℕ) :
      (∑ j ∈ Finset.range N, ‖f ((r : ℝ) * (xiSpectralPoint (q j)).re)‖ ^ 2) ≤
        xiRealAxisSchwartzEnergy f r := by
    rw [← Finset.sum_image (f := fun z : XiZeroCopy =>
      ‖f ((r : ℝ) * (xiSpectralPoint z).re)‖ ^ 2)
      (s := Finset.range N) (g := q) (fun i _ j _ hij => hqinj hij)]
    exact (summable_xiRealAxisSchwartz_norm_sq f r).sum_le_tsum _
      (fun _ _ => sq_nonneg _)
  have hfinite (N : ℕ) :
      (∫ x in (r : ℝ) * a..(r : ℝ) * a + (N : ℝ) * ((r : ℝ) * h), ‖f x‖ ^ 2) ≤
        ((r : ℝ) * h) * xiRealAxisSchwartzEnergy f r +
          2 * ((r : ℝ) * h) * Real.sqrt (4 * Real.pi * ((P.natDegree : ℝ) + 1)) *
            ‖f.toLp 2 (volume : Measure ℝ)‖ ^ 2 := by
    have hb := gaussianPolynomial_grid_quadrature_error P ((r : ℝ) * a) mesh s N
    simp_rw [hsample] at hb
    have hsampleSum := mul_le_mul_of_nonneg_left (hsum N) (mul_pos r.property hh).le
    have hupper := (abs_le.mp hb).2
    change (∫ x in (r : ℝ) * a..(r : ℝ) * a + (N : ℝ) * ((r : ℝ) * h), ‖f x‖ ^ 2) -
      ((r : ℝ) * h) * (∑ j ∈ Finset.range N, ‖f ((r : ℝ) * (xiSpectralPoint (q j)).re)‖ ^ 2) ≤
        2 * ((r : ℝ) * h) * Real.sqrt (4 * Real.pi * ((P.natDegree : ℝ) + 1)) *
          ‖f.toLp 2 (volume : Measure ℝ)‖ ^ 2 at hupper
    linarith only [hupper, hsampleSum]
  have hint : Integrable (fun x : ℝ => ‖f x‖ ^ (2 : ℕ)) :=
    (memLp_two_iff_integrable_sq_norm f.continuous.aestronglyMeasurable).mp
      (f.memLp 2 (volume : Measure ℝ))
  have htop : Tendsto (fun N : ℕ => (r : ℝ) * a + (N : ℝ) * ((r : ℝ) * h))
      atTop atTop :=
    tendsto_atTop_add_const_left atTop ((r : ℝ) * a)
      ((tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).atTop_mul_const
        (mul_pos r.property hh))
  exact le_of_tendsto' (intervalIntegral_tendsto_integral_Ioi ((r : ℝ) * a)
    hint.integrableOn htop) hfinite

end RHTower
