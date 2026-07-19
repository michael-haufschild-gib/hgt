import GaloisForLFunctions.HTGeometry.TotalGramMatrix
import GaloisForLFunctions.HTGeometry.RegularizedHerglotzTransform

/-!
# The scaled Gram is the Pick kernel of the chamber transform

The matrix the chamber law is stated for is the Pick kernel of an actual Herglotz function: for a
chamber member — finitely many real atoms plus the regularized transform of a measure — the scaled
Gram at the nodes above the atoms is the Pick difference quotient, scaled by the squared height.

The regularization is what makes this work without any convergence assumption beyond integrability
of the regularized kernel itself.  The subtracted term `t / (1 + t ^ 2)` is real, so it cancels in
the difference `m z - conj (m w)`, and the two Cauchy kernels combine into a single integrand
decaying like `t ^ (-2)`.  Splitting the difference into two separate Cauchy integrals would be
invalid: for an infinite measure neither piece need converge.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Matrix Finset

noncomputable section

/-- Integrability is preserved by conjugation, which is norm-preserving. -/
theorem integrable_conj {ν : Measure ℝ} {f : ℝ → ℂ} (hf : Integrable f ν) :
    Integrable (fun t => (starRingEnd ℂ) (f t)) ν := by
  refine hf.norm.mono'
    (Complex.continuous_conj.comp_aestronglyMeasurable hf.aestronglyMeasurable) ?_
  filter_upwards with t
  exact le_of_eq (Complex.norm_conj _)

/-- **The regularization cancels in the Pick difference.**  The subtracted term is real, so the
difference of the regularized kernels at `z` and `conj w` is the product of the two Cauchy kernels,
scaled by the Pick denominator. -/
theorem regularizedHerglotzKernel_sub_conj {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0) (t : ℝ) :
    regularizedHerglotzKernel t z - (starRingEnd ℂ) (regularizedHerglotzKernel t w)
      = (z - (starRingEnd ℂ) w)
        * (((t : ℂ) - z)⁻¹ * ((t : ℂ) - (starRingEnd ℂ) w)⁻¹) := by
  have hzt : ((t : ℂ) - z) ≠ 0 := real_sub_ne_zero_of_im_ne_zero hz t
  have hwt : ((t : ℂ) - (starRingEnd ℂ) w) ≠ 0 := by
    refine real_sub_ne_zero_of_im_ne_zero ?_ t
    simpa using hw
  rw [regularizedHerglotzKernel, regularizedHerglotzKernel, map_sub, map_div₀, map_div₀,
    map_one, map_sub, Complex.conj_ofReal, map_add, map_one, map_pow, Complex.conj_ofReal]
  field_simp
  ring

/-- The atomic part of a chamber member: finitely many real atoms with real coefficients. -/
def atomPart {d : ℕ} (a c : Fin d → ℝ) (z : ℂ) : ℂ :=
  ∑ j, (c j : ℂ) / ((a j : ℂ) - z)

/-- **The regularized Herglotz transform of a chamber member.** -/
def chamberHerglotz {d : ℕ} (ν : Measure ℝ) (a c : Fin d → ℝ) (z : ℂ) : ℂ :=
  atomPart a c z + ∫ t, regularizedHerglotzKernel t z ∂ν

/-- The atomic part obeys the Pick identity termwise. -/
theorem atomPart_sub_conj {d : ℕ} (a c : Fin d → ℝ) {z w : ℂ} (hz : z.im ≠ 0) (hw : w.im ≠ 0) :
    atomPart a c z - (starRingEnd ℂ) (atomPart a c w)
      = (z - (starRingEnd ℂ) w)
        * ∑ j, (c j : ℂ) / (((a j : ℂ) - z) * ((a j : ℂ) - (starRingEnd ℂ) w)) := by
  rw [atomPart, atomPart, map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hzt : ((a j : ℂ) - z) ≠ 0 := real_sub_ne_zero_of_im_ne_zero hz (a j)
  have hwt : ((a j : ℂ) - (starRingEnd ℂ) w) ≠ 0 := by
    refine real_sub_ne_zero_of_im_ne_zero ?_ (a j)
    simpa using hw
  rw [map_div₀, map_sub, Complex.conj_ofReal, Complex.conj_ofReal]
  field_simp
  ring

/-- The measure Gram is the scaled integral of the product of the two Cauchy kernels. -/
theorem measureGram_eq_scaled_integral {d : ℕ} (ν : Measure ℝ) (a : Fin d → ℝ) (y : ℝ)
    (l m : Fin d) :
    measureGram ν a y l m
      = (y : ℂ) ^ 2 * ∫ t, ((t : ℂ) - upperNode (a l) y)⁻¹
          * ((t : ℂ) - (starRingEnd ℂ) (upperNode (a m) y))⁻¹ ∂ν := by
  rw [measureGram, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  dsimp only
  rw [map_mul, Complex.conj_ofReal, map_inv₀, map_sub, Complex.conj_ofReal]
  ring

/-- **The scaled Gram is the Pick kernel of the chamber transform.**  At the nodes above the atoms,
the total scaled Gram times the Pick denominator is the squared height times the Pick difference of
the chamber member's regularized Herglotz transform.

So the chamber law's matrix is not an ad hoc object: it is the Pick kernel of an actual Herglotz
function, and the negative index it grades is that function's Krein index. -/
theorem totalGram_mul_sub_eq_pick {d : ℕ} (ν : Measure ℝ) (a c : Fin d → ℝ) {y : ℝ} (hy : y ≠ 0)
    (l m : Fin d)
    (hl : Integrable (fun t => regularizedHerglotzKernel t (upperNode (a l) y)) ν)
    (hm : Integrable (fun t => regularizedHerglotzKernel t (upperNode (a m) y)) ν) :
    totalGram ν a c y l m
        * (upperNode (a l) y - (starRingEnd ℂ) (upperNode (a m) y))
      = (y : ℂ) ^ 2 * (chamberHerglotz ν a c (upperNode (a l) y)
          - (starRingEnd ℂ) (chamberHerglotz ν a c (upperNode (a m) y))) := by
  have hz : (upperNode (a l) y).im ≠ 0 := by rw [upperNode_im]; exact hy
  have hw : (upperNode (a m) y).im ≠ 0 := by rw [upperNode_im]; exact hy
  have hmeas : (∫ t, regularizedHerglotzKernel t (upperNode (a l) y) ∂ν)
      - (starRingEnd ℂ) (∫ t, regularizedHerglotzKernel t (upperNode (a m) y) ∂ν)
      = (upperNode (a l) y - (starRingEnd ℂ) (upperNode (a m) y))
        * ∫ t, ((t : ℂ) - upperNode (a l) y)⁻¹
            * ((t : ℂ) - (starRingEnd ℂ) (upperNode (a m) y))⁻¹ ∂ν := by
    rw [← integral_conj, ← integral_sub hl (integrable_conj hm), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    dsimp only
    exact regularizedHerglotzKernel_sub_conj hz hw t
  have hchamber : chamberHerglotz ν a c (upperNode (a l) y)
        - (starRingEnd ℂ) (chamberHerglotz ν a c (upperNode (a m) y))
      = (upperNode (a l) y - (starRingEnd ℂ) (upperNode (a m) y))
        * ((∑ j, (c j : ℂ) / (((a j : ℂ) - upperNode (a l) y)
              * ((a j : ℂ) - (starRingEnd ℂ) (upperNode (a m) y))))
           + ∫ t, ((t : ℂ) - upperNode (a l) y)⁻¹
               * ((t : ℂ) - (starRingEnd ℂ) (upperNode (a m) y))⁻¹ ∂ν) := by
    rw [chamberHerglotz, chamberHerglotz, map_add, mul_add,
      ← atomPart_sub_conj a c hz hw, ← hmeas]
    ring
  rw [hchamber, totalGram_apply, atomicGram, measureGram_eq_scaled_integral]
  ring

end

end GaloisForLFunctions.HTGeometry
