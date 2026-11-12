import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailZeroPrefixHasAUniformRemainder
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailPrefixQuantitativeFinitePart

/-!
# Exact zero modes of the normalized harmonic convolution

Each power-weighted zero mode is a complex power prefix. Its continued
zeta value supplies the oscillating term, its power integral supplies a
constant, and its normalized remainder is uniformly at most `14/N`.
-/

noncomputable section

open Complex Finset
open _root_.RHTower

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open TransHorizonIncidenceMechanics

/-- One zero's contribution to the normalized weighted harmonic convolution. -/
def powerTailZeroConvolutionMode (a : ℝ) (N : ℕ) (q : XiZeroCopy) : ℂ :=
  (((N : ℝ) ^ (2 * a - 1) : ℝ) : ℂ) *
    ∑ m ∈ Icc 1 N, (powerTailWeight (2 * a) m : ℂ) *
      (((N : ℝ) / m : ℝ) : ℂ) ^ ((q.1 : ℂ) - (a : ℂ)) /
        ((q.1 : ℂ) - (a : ℂ))

/-- The oscillating zeta term and constant power integral of one zero mode. -/
def powerTailZeroConvolutionMain (a : ℝ) (N : ℕ) (q : XiZeroCopy) : ℂ :=
  ((N : ℝ) : ℂ) ^ ((q.1 : ℂ) - ((1 - a : ℝ) : ℂ)) *
    (riemannZeta ((q.1 : ℂ) + (a : ℂ)) / ((q.1 : ℂ) - (a : ℂ))) +
  1 / (((q.1 : ℂ) - (a : ℂ)) * (1 - ((q.1 : ℂ) + (a : ℂ))))

/-- Positive real powers factor the finite convolution into its exact
complex power prefix, before any limiting argument. -/
theorem powerTailZeroConvolutionMode_eq_prefix {a : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (q : XiZeroCopy) :
    powerTailZeroConvolutionMode a N q =
      ((N : ℝ) : ℂ) ^ ((q.1 : ℂ) - ((1 - a : ℝ) : ℂ)) *
        (cpowPartialSum ((q.1 : ℂ) + (a : ℂ)) N / ((q.1 : ℂ) - (a : ℂ))) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hNne : ((N : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hNp.ne'
  have hNpow : (((N : ℝ) ^ (2 * a - 1) : ℝ) : ℂ) *
      ((N : ℝ) : ℂ) ^ ((q.1 : ℂ) - (a : ℂ)) =
        ((N : ℝ) : ℂ) ^ ((q.1 : ℂ) - ((1 - a : ℝ) : ℂ)) := by
    rw [Complex.ofReal_cpow hNp.le, ← Complex.cpow_add _ _ hNne]
    congr 1
    push_cast
    ring
  rw [powerTailZeroConvolutionMode, Finset.mul_sum, cpowPartialSum,
    Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmp : (0 : ℝ) < m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
  have hmne : ((m : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hmp.ne'
  have hmpow : (powerTailWeight (2 * a) m : ℂ) *
      ((m : ℝ) : ℂ) ^ (-((q.1 : ℂ) - (a : ℂ))) =
        ((m : ℝ) : ℂ) ^ (-((q.1 : ℂ) + (a : ℂ))) := by
    rw [powerTailWeight, Complex.ofReal_cpow hmp.le, ← Complex.cpow_add _ _ hmne]
    congr 1
    push_cast
    ring
  rw [TransHorizonIncidenceMechanics.ofReal_div_cpow hNp hmp]
  calc
    _ = ((((N : ℝ) ^ (2 * a - 1) : ℝ) : ℂ) *
          ((N : ℝ) : ℂ) ^ ((q.1 : ℂ) - (a : ℂ))) *
        ((powerTailWeight (2 * a) m : ℂ) *
          ((m : ℝ) : ℂ) ^ (-((q.1 : ℂ) - (a : ℂ)))) /
        ((q.1 : ℂ) - (a : ℂ)) := by ring
    _ = _ := by rw [hNpow, hmpow]; ring

/-- A finite normalized mode consists exactly of its zeta oscillation,
its constant power integral, and the uniform prefix remainder. -/
theorem powerTailZeroConvolutionMode_decomposition {a : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (q : XiZeroCopy) :
    powerTailZeroConvolutionMode a N q =
      powerTailZeroConvolutionMain a N q +
      ((N : ℝ) : ℂ) ^ ((q.1 : ℂ) - ((1 - a : ℝ) : ℂ)) *
        powerTailZeroPrefixRemainder a q N := by
  unfold powerTailZeroConvolutionMain
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hNne : ((N : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hNp.ne'
  have hcancel : ((N : ℝ) : ℂ) ^ ((q.1 : ℂ) - ((1 - a : ℝ) : ℂ)) *
      ((N : ℝ) : ℂ) ^ (1 - ((q.1 : ℂ) + (a : ℂ))) = 1 := by
    rw [← Complex.cpow_add _ _ hNne,
      show (q.1 : ℂ) - ((1 - a : ℝ) : ℂ) +
        (1 - ((q.1 : ℂ) + (a : ℂ))) = 0 by push_cast; ring,
      Complex.cpow_zero]
  rw [powerTailZeroConvolutionMode_eq_prefix hN, powerTailZeroPrefixRemainder]
  calc
    _ = ((N : ℝ) : ℂ) ^ ((q.1 : ℂ) - ((1 - a : ℝ) : ℂ)) *
          (riemannZeta ((q.1 : ℂ) + (a : ℂ)) / ((q.1 : ℂ) - (a : ℂ))) +
        (((N : ℝ) : ℂ) ^ ((q.1 : ℂ) - ((1 - a : ℝ) : ℂ)) *
          ((N : ℝ) : ℂ) ^ (1 - ((q.1 : ℂ) + (a : ℂ)))) /
          (((q.1 : ℂ) - (a : ℂ)) * (1 - ((q.1 : ℂ) + (a : ℂ)))) +
        ((N : ℝ) : ℂ) ^ ((q.1 : ℂ) - ((1 - a : ℝ) : ℂ)) *
          ((cpowPartialSum ((q.1 : ℂ) + (a : ℂ)) N -
            ((N : ℝ) : ℂ) ^ (1 - ((q.1 : ℂ) + (a : ℂ))) /
              (1 - ((q.1 : ℂ) + (a : ℂ))) - riemannZeta ((q.1 : ℂ) + (a : ℂ))) /
            ((q.1 : ℂ) - (a : ℂ))) := by
      simp [div_eq_mul_inv] <;> ring
    _ = _ := by rw [hcancel]

/-- Summing the normalized mode errors costs only the number of retained
zeros, with all multiplicity copies counted. -/
theorem norm_sum_powerTailZeroConvolutionMode_sub_main_le
    {a : ℝ} {N : ℕ} (hN : 1 ≤ N) (F : Finset XiZeroCopy)
    (hF : ∀ q ∈ F, 1 / 2 ≤ (q.1 : ℂ).re + a ∧ (q.1 : ℂ).re + a ≤ 1) :
    ‖(∑ q ∈ F, powerTailZeroConvolutionMode a N q) -
      ∑ q ∈ F, powerTailZeroConvolutionMain a N q‖ ≤ 14 * (F.card : ℝ) / N := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ q ∈ F, ‖powerTailZeroConvolutionMode a N q -
        powerTailZeroConvolutionMain a N q‖ := norm_sum_le _ _
    _ ≤ ∑ _q ∈ F, 14 / (N : ℝ) := by
      apply Finset.sum_le_sum
      intro q hq
      rw [powerTailZeroConvolutionMode_decomposition hN,
        add_sub_cancel_left]
      exact norm_normalized_powerTailZeroPrefixRemainder_le q (hF q hq).1 (hF q hq).2 hN
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
