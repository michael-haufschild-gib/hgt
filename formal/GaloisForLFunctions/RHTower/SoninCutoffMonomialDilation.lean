import GaloisForLFunctions.RHTower.FiniteTimeBandFourierSchatten
import GaloisForLFunctions.RHTower.SoninDilationSourceSupportRecovery

/-!
# Exact coherent dilation overlap of the time-band output monomials

The narrower physical cutoff makes two dilated monomials proportional.
Orthogonality then determines their full inner product, without a numerical
estimate or a prescribed decorrelation hypothesis.
-/

noncomputable section

open MeasureTheory

namespace RHTower

private theorem cutoffMonomial_memLp (a : ℝ) (n : ℕ) :
    MemLp ((Set.Icc (-a) a).indicator fun x : ℝ => (x : ℂ) ^ n) 2 volume := by
  apply (memLp_indicator_iff_restrict measurableSet_Icc).mpr
  apply MemLp.of_bound (by fun_prop) (a ^ n)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg x) (abs_le.mpr hx) n

/-- The actual physical cutoff monomial used by the time-band Taylor expansion. -/
def soninCutoffMonomial (a : ℝ) (n : ℕ) : SoninL2 :=
  (cutoffMonomial_memLp a n).toLp _

theorem soninCutoffMonomial_ae (a : ℝ) (n : ℕ) :
    (soninCutoffMonomial a n : ℝ → ℂ) =ᵐ[volume]
      (centralInterval a).indicator (fun x : ℝ => (x : ℂ) ^ n) :=
  (cutoffMonomial_memLp a n).coeFn_toLp

/-- Projecting the wider dilate onto the narrower support gives its exact monomial ratio. -/
theorem indicatorCutoff_dilation_soninCutoffMonomial_of_le
    (a : ℝ) (n : ℕ) (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s) :
    indicatorCutoff (centralInterval (a / s)) (measurableSet_centralInterval (a / s))
        (dilation r hr (soninCutoffMonomial a n)) =
      ((Real.sqrt r / Real.sqrt s * (r / s) ^ n : ℝ) : ℂ) •
        dilation s hs (soninCutoffMonomial a n) := by
  let c : ℂ := ((Real.sqrt r / Real.sqrt s * (r / s) ^ n : ℝ) : ℂ)
  apply Lp.ext
  have hmr := (soninCutoffMonomial_ae a n).comp_tendsto
    (realMul_quasiMeasurePreserving r hr.ne').tendsto_ae
  have hms := (soninCutoffMonomial_ae a n).comp_tendsto
    (realMul_quasiMeasurePreserving s hs.ne').tendsto_ae
  filter_upwards [indicatorCutoff_ae (centralInterval (a / s))
    (measurableSet_centralInterval (a / s)) (dilation r hr (soninCutoffMonomial a n)),
    dilation_ae r hr (soninCutoffMonomial a n),
    dilation_ae s hs (soninCutoffMonomial a n), hmr, hms,
    Lp.coeFn_smul c (dilation s hs (soninCutoffMonomial a n))]
      with x hcut hdr hds hmr hms hsmul
  change soninCutoffMonomial a n (r * x) = _ at hmr
  change soninCutoffMonomial a n (s * x) = _ at hms
  simp only [Function.comp_apply] at hmr hms
  change _ = c * (dilation s hs (soninCutoffMonomial a n)) x at hsmul
  rw [hcut, hsmul, hds, hms]
  have hsupport : x ∈ centralInterval (a / s) ↔ s * x ∈ centralInterval a := by
    change (- (a / s) ≤ x ∧ x ≤ a / s) ↔ (-a ≤ s * x ∧ s * x ≤ a)
    rw [← abs_le, ← abs_le, abs_mul, abs_of_pos hs, le_div_iff₀ hs]
    rw [mul_comm |x| s]
  by_cases hx : x ∈ centralInterval (a / s)
  · have hsx := hsupport.mp hx
    have hrx : r * x ∈ centralInterval a := by
      have hax : s * |x| ≤ a := by
        have h := abs_le.mpr hsx
        simpa only [abs_mul, abs_of_pos hs] using h
      apply abs_le.mp
      rw [abs_mul, abs_of_pos hr]
      exact (mul_le_mul_of_nonneg_right hrs (abs_nonneg x)).trans hax
    rw [Set.indicator_of_mem hx, Set.indicator_of_mem hsx, hdr, hmr,
      Set.indicator_of_mem hrx]
    dsimp only [c]
    push_cast
    have hsC : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
    have hsqrtC : (Real.sqrt s : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hs).ne'
    simp only [div_pow, mul_pow]
    field_simp
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt hsupport.mpr hx)]
    simp

theorem indicatorCutoff_dilation_soninCutoffMonomial_self
    (a : ℝ) (n : ℕ) (s : ℝ) (hs : 0 < s) :
    indicatorCutoff (centralInterval (a / s)) (measurableSet_centralInterval (a / s))
      (dilation s hs (soninCutoffMonomial a n)) = dilation s hs (soninCutoffMonomial a n) := by
  simpa only [div_self hs.ne', div_self (Real.sqrt_pos.mpr hs).ne', one_pow,
    mul_one, Complex.ofReal_one, one_smul] using
      indicatorCutoff_dilation_soninCutoffMonomial_of_le a n s s hs hs le_rfl

/-- Exact ordered overlap, uniform in the degree of the original time-band output. -/
theorem inner_dilation_soninCutoffMonomial_of_le
    (a : ℝ) (n : ℕ) (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s) :
    inner ℂ (dilation r hr (soninCutoffMonomial a n))
      (dilation s hs (soninCutoffMonomial a n)) =
        (((Real.sqrt r / Real.sqrt s * (r / s) ^ n) * ‖soninCutoffMonomial a n‖ ^ 2 : ℝ) : ℂ) := by
  calc
    _ = inner ℂ (dilation r hr (soninCutoffMonomial a n))
        (indicatorCutoff (centralInterval (a / s)) (measurableSet_centralInterval (a / s))
          (dilation s hs (soninCutoffMonomial a n))) := by
      rw [indicatorCutoff_dilation_soninCutoffMonomial_self]
    _ = inner ℂ
        (indicatorCutoff (centralInterval (a / s)) (measurableSet_centralInterval (a / s))
          (dilation r hr (soninCutoffMonomial a n)))
        (dilation s hs (soninCutoffMonomial a n)) :=
      (indicatorCutoff_symmetric _ _ _ _).symm
    _ = _ := by
      rw [indicatorCutoff_dilation_soninCutoffMonomial_of_le a n r s hr hs hrs,
        inner_smul_left, inner_self_eq_norm_sq_to_K, (dilation s hs).norm_map]
      simp only [Complex.ofReal_mul, Complex.ofReal_pow, map_mul, map_pow, Complex.conj_ofReal]
      rfl

/-- The overlap loss is uniform over every degree of the actual Taylor outputs. -/
theorem norm_inner_dilation_soninCutoffMonomial_le
    (a : ℝ) (n : ℕ) (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (hrs : r ≤ s) :
    ‖inner ℂ (dilation r hr (soninCutoffMonomial a n))
      (dilation s hs (soninCutoffMonomial a n))‖ ≤
        (Real.sqrt r / Real.sqrt s) * ‖soninCutoffMonomial a n‖ ^ 2 := by
  rw [inner_dilation_soninCutoffMonomial_of_le a n r s hr hs hrs,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hp : (r / s) ^ n ≤ 1 := pow_le_one₀ (by positivity) ((div_le_one hs).mpr hrs)
  calc
    _ ≤ ((Real.sqrt r / Real.sqrt s) * 1) * ‖soninCutoffMonomial a n‖ ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp (by positivity)) (sq_nonneg _)
    _ = _ := by rw [mul_one]

end RHTower
