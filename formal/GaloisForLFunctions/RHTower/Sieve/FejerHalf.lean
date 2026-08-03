import GaloisForLFunctions.RHTower.Sieve.LinearPhaseIntegral

/-!
# The triangular weight against a phase, on a half interval

`∫_0^T (1 - t/T) e^{itL} dt` splits into the constant and linear pieces already computed:

`∫_0^T e^{itL} dt - T^{-1} ∫_0^T t e^{itL} dt`.

Both have closed forms — `PhaseIntegral.lean` and `LinearPhaseIntegral.lean` — so the triangular
weight's transform is explicit.  Reflecting and adding gives the symmetric (Fejér) transform, whose
value is `2(1 - cos TL)/(TL²)`: nonnegative, and decaying like `|L|^{-2}` rather than the `|L|^{-1}`
of the sharp kernel.
-/

namespace RHTower.Sieve

open MeasureTheory

/-- **The triangular weight splits into constant and linear pieces.** -/
theorem integral_fejerHalf_split (L : ℝ) {T : ℝ} (hT : 0 < T) :
    (∫ t in (0 : ℝ)..T, ((1 - t / T : ℝ) : ℂ) * Complex.exp (((t * L : ℝ) : ℂ) * Complex.I))
      = (∫ t in (0 : ℝ)..T, Complex.exp (((t * L : ℝ) : ℂ) * Complex.I))
        - ((1 / T : ℝ) : ℂ)
          * (∫ t in (0 : ℝ)..T, (t : ℂ) * Complex.exp (((t * L : ℝ) : ℂ) * Complex.I)) := by
  have hTne : (T : ℝ) ≠ 0 := ne_of_gt hT
  have hpoint : ∀ t : ℝ,
      ((1 - t / T : ℝ) : ℂ) * Complex.exp (((t * L : ℝ) : ℂ) * Complex.I)
        = Complex.exp (((t * L : ℝ) : ℂ) * Complex.I)
          - ((1 / T : ℝ) : ℂ) * ((t : ℂ) * Complex.exp (((t * L : ℝ) : ℂ) * Complex.I)) := by
    intro t
    push_cast
    field_simp
  rw [intervalIntegral.integral_congr (fun t _ => hpoint t)]
  rw [intervalIntegral.integral_sub (intervalIntegrable_exp_phase L 0 T)
    ((intervalIntegrable_linPhase L 0 T).const_mul _)]
  rw [intervalIntegral.integral_const_mul]

/-- **The triangular weight's transform on a half interval, in closed form.** -/
theorem integral_fejerHalf (L : ℝ) (hL : L ≠ 0) {T : ℝ} (hT : 0 < T) :
    (∫ t in (0 : ℝ)..T, ((1 - t / T : ℝ) : ℂ) * Complex.exp (((t * L : ℝ) : ℂ) * Complex.I))
      = Complex.I / (L : ℂ)
        - (Complex.exp (((T * L : ℝ) : ℂ) * Complex.I) - 1) / ((T : ℂ) * (L : ℂ) ^ 2) := by
  have hL' : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL
  have hT' : (T : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hT)
  have hzero : linPhaseAnti L 0 = -(1 / ((L : ℂ) * Complex.I) ^ 2) := by
    rw [linPhaseAnti]
    norm_num
  rw [integral_fejerHalf_split L hT, integral_exp_phase L hL T, integral_linPhase L hL 0 T,
    hzero, linPhaseAnti]
  have hI : (Complex.I) ^ 2 = -1 := Complex.I_sq
  have hI3 : (Complex.I) ^ 3 = -Complex.I := by
    rw [pow_succ, hI, neg_one_mul]
  push_cast
  field_simp
  ring_nf
  simp only [hI, hI3]
  ring

end RHTower.Sieve
