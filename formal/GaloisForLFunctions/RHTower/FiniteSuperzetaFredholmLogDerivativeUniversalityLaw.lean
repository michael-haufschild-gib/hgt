import GaloisForLFunctions.RHTower.SuperzetaResolvent
import GaloisForLFunctions.HTGeometry.FredholmDeterminantExamples

/-!
# Finite superzeta–Fredholm logarithmic-derivative universality

The additive finite superzeta resolvent and multiplicative trace-class Fredholm determinant are
exact transforms. For a finite spectral packet `r : Fin n → ℂ`, the superzeta resolvent value is
the cardinality-corrected logarithmic derivative of the characteristic determinant of the
diagonal spectral operator:

`Σᵢ (1 - z rᵢ)⁻¹ = n - z · logDeriv(det₁(1 - z·diag(r)))`.

The correction is sharp: `n` restores degree zero, while the trace-class correction inside `det₁`
restores degree one removed by Hilbert–Carleman regularization.
-/

namespace GaloisForLFunctions

open scoped BigOperators

noncomputable section

/-- **Finite superzeta–Fredholm logarithmic-derivative universality law.** The finite additive
superzeta resolvent is the cardinality-corrected logarithmic derivative of the multiplicative
trace-class Fredholm determinant of the diagonal spectral operator. -/
theorem finiteSuperzetaResolventValue_eq_fredholmDet1_logDeriv
    {n : ℕ} (r : Fin n → ℂ) (R : ℝ)
    (hR : R * HilbertSchmidt.hsNorm (HilbertSchmidt.diagMul r) < 1)
    (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) R) :
    (∑ i, (1 - z * r i)⁻¹) =
      (n : ℂ) - z * logDeriv
        (fun w => HilbertSchmidt.fredholmDet1 (HilbertSchmidt.diagMul r) w) z := by
  have hg : ∀ i ∉ (Finset.univ : Finset (Fin n)), r i = 0 := by simp
  have hHS : HilbertSchmidt.IsHS (HilbertSchmidt.diagMul r) :=
    HilbertSchmidt.isHS_diagMul r Finset.univ hg
  have hzr : ‖z‖ < R := by rwa [mem_ball_zero_iff] at hz
  have hzM : ‖z‖ * HilbertSchmidt.hsNorm (HilbertSchmidt.diagMul r) < 1 :=
    lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right hzr.le (HilbertSchmidt.hsNorm_nonneg _)) hR
  have hfac : ∀ i ∈ (Finset.univ : Finset (Fin n)), ‖z * r i‖ < 1 := by
    intro i hi
    rw [norm_mul]
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_left
        (HilbertSchmidt.norm_le_hsNorm_diagMul r Finset.univ hg hi) (norm_nonneg z)) hzM
  have hlog := HilbertSchmidt.logDeriv_fredholmDet1 hHS R hR z hz
  have hres := HilbertSchmidt.resolventTrace_diagMul r Finset.univ hg z hfac
  have htr := HilbertSchmidt.tsum_diagMul_diag r Finset.univ hg
  rw [hres, HilbertSchmidt.hsTraceDiag, htr] at hlog
  rw [hlog]
  have hterm : ∀ i : Fin n,
      (1 - z * r i)⁻¹ = 1 + z * (r i + z * r i ^ 2 / (1 - z * r i)) := by
    intro i
    have hden : 1 - z * r i ≠ 0 := by
      intro h
      have hi := hfac i (Finset.mem_univ i)
      have hone : z * r i = 1 := by linear_combination -h
      rw [hone, norm_one] at hi
      exact lt_irrefl 1 hi
    rw [inv_eq_one_div]
    field_simp [hden]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

end

end GaloisForLFunctions
