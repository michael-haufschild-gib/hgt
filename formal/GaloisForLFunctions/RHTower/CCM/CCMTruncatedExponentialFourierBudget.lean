import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarFourierRegularity

/-!
# Endpoint budgets for translated and clipped polar source pieces

Repeated finite-prime translations and aperture restrictions preserve the
class of finite sums of truncated real exponentials. The endpoint amplitude
controls each piece and its inverse-frequency Fourier tail. Translation
preserves this amplitude exactly; restriction decreases it on each retained
interval. The sum estimate incurs no further piece-count factor.

These are the source-representation estimates needed for growing numbers of
bounded-remainder iterates. Identification with that actual Hilbert operator
and the resulting response bound require the subsequent operator argument.
-/

open MeasureTheory Set
open scoped FourierTransform
noncomputable section
namespace RHTower

/-- A literal translated and clipped pole profile. -/
def ccmTruncatedExponential (s l r : ℝ) (z : ℂ) : ℝ → ℂ :=
  (Icc l r).indicator (fun x => z * (Real.exp (s * x) : ℂ))

/-- Sum this endpoint amplitude over pieces to control repeated prime translates. -/
def ccmTruncatedExponentialBudget (s l r : ℝ) (z : ℂ) : ℝ :=
  ‖z‖ * Real.exp (max (s * l) (s * r))

theorem norm_ccmTruncatedExponential_le (s l r : ℝ) (z : ℂ) (x : ℝ) :
    ‖ccmTruncatedExponential s l r z x‖ ≤ ccmTruncatedExponentialBudget s l r z := by
  by_cases hx : x ∈ Icc l r
  · rw [ccmTruncatedExponential, indicator_of_mem hx, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
    apply Real.exp_le_exp.mpr
    by_cases hs : 0 ≤ s
    · exact (mul_le_mul_of_nonneg_left hx.2 hs).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_left hx.1 (le_of_not_ge hs)).trans (le_max_left _ _)
  · rw [ccmTruncatedExponential, indicator_of_notMem hx, norm_zero]
    unfold ccmTruncatedExponentialBudget
    positivity

theorem integrable_ccmTruncatedExponential (s l r : ℝ) (z : ℂ) :
    Integrable (ccmTruncatedExponential s l r z) := by
  have hc : Continuous (fun x : ℝ => z * (Real.exp (s * x) : ℂ)) := by fun_prop
  exact hc.integrableOn_Icc.integrable_indicator measurableSet_Icc

theorem fourier_ccmTruncatedExponential_eq_interval {l r : ℝ} (hlr : l ≤ r)
    (s : ℝ) (z : ℂ) (ξ : ℝ) :
    𝓕 (ccmTruncatedExponential s l r z) ξ =
      z * ∫ x in l..r,
        Complex.exp (((s : ℂ) - 2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)) * (x : ℂ)) := by
  rw [Real.fourier_real_eq_integral_exp_smul,
    ← intervalIntegral.integral_const_mul,
    intervalIntegral.integral_of_le hlr,
    ← integral_Icc_eq_integral_Ioc, ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Icc l r
  · rw [ccmTruncatedExponential, indicator_of_mem hx, indicator_of_mem hx]
    simp only [smul_eq_mul]
    rw [Complex.ofReal_exp, ← mul_assoc, mul_comm _ z, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  · rw [ccmTruncatedExponential, indicator_of_notMem hx, indicator_of_notMem hx, smul_zero]

/-- Fourier tail controlled by endpoint amplitude, with no interval-length or
piece-count loss. This is the quantity propagated through the prime shifts. -/
theorem norm_fourier_ccmTruncatedExponential_le {l r : ℝ} (hlr : l ≤ r)
    (s : ℝ) (z : ℂ) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ‖𝓕 (ccmTruncatedExponential s l r z) ξ‖ ≤
      ccmTruncatedExponentialBudget s l r z / (Real.pi * |ξ|) := by
  let c : ℂ := (s : ℂ) - 2 * (Real.pi : ℂ) * Complex.I * (ξ : ℂ)
  have hcim : c.im = -(2 * Real.pi * ξ) := by dsimp [c]; simp
  have hcN : 2 * Real.pi * |ξ| ≤ ‖c‖ := by
    have h := Complex.abs_im_le_norm c
    rw [hcim, abs_neg, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)] at h
    exact h
  have hcpos : 0 < ‖c‖ := (by positivity : 0 < 2 * Real.pi * |ξ|).trans_le hcN
  have hcne : c ≠ 0 := norm_pos_iff.mp hcpos
  have hend (t : ℝ) (ht : s * t ≤ max (s * l) (s * r)) :
      ‖Complex.exp (c * (t : ℂ))‖ ≤ Real.exp (max (s * l) (s * r)) := by
    rw [Complex.norm_exp]
    have hre : (c * (t : ℂ)).re = s * t := by dsimp [c]; simp
    rw [hre]
    exact Real.exp_le_exp.mpr ht
  have hnum := (norm_sub_le (Complex.exp (c * (r : ℂ)))
    (Complex.exp (c * (l : ℂ)))).trans
    (add_le_add (hend r (le_max_right _ _)) (hend l (le_max_left _ _)))
  rw [fourier_ccmTruncatedExponential_eq_interval hlr]
  change ‖z * ∫ x in l..r, Complex.exp (c * (x : ℂ))‖ ≤ _
  rw [integral_exp_mul_complex hcne, norm_mul, norm_div]
  have hdiv : ‖Complex.exp (c * (r : ℂ)) - Complex.exp (c * (l : ℂ))‖ / ‖c‖ ≤
      Real.exp (max (s * l) (s * r)) / (Real.pi * |ξ|) := by
    apply (div_le_div_iff₀ hcpos (by positivity : 0 < Real.pi * |ξ|)).mpr
    have hn := mul_le_mul_of_nonneg_right hnum (by positivity : 0 ≤ Real.pi * |ξ|)
    have hd := mul_le_mul_of_nonneg_left hcN (Real.exp_pos (max (s * l) (s * r))).le
    nlinarith only [hn, hd]
  have hm := mul_le_mul_of_nonneg_left hdiv (norm_nonneg z)
  simpa only [ccmTruncatedExponentialBudget, mul_div_assoc] using hm

/-- Translating a clipped pole profile changes only its endpoints and coefficient. -/
theorem ccmTruncatedExponential_translate (s l r h : ℝ) (z : ℂ) (x : ℝ) :
    ccmTruncatedExponential s l r z (x - h) =
      ccmTruncatedExponential s (l + h) (r + h)
        (z * (Real.exp (-s * h) : ℂ)) x := by
  have hmem : x - h ∈ Icc l r ↔ x ∈ Icc (l + h) (r + h) := by
    simp only [mem_Icc]
    constructor <;> rintro ⟨hl, hr⟩ <;> constructor <;> linarith
  by_cases hx : x - h ∈ Icc l r
  · rw [ccmTruncatedExponential, ccmTruncatedExponential,
      indicator_of_mem hx, indicator_of_mem (hmem.mp hx), mul_assoc,
      ← Complex.ofReal_mul, ← Real.exp_add]
    congr 2
    congr 1
    ring
  · rw [ccmTruncatedExponential, ccmTruncatedExponential,
      indicator_of_notMem hx, indicator_of_notMem (fun h => hx (hmem.mpr h))]

/-- Translation preserves the endpoint-amplitude budget exactly. -/
theorem ccmTruncatedExponentialBudget_translate (s l r h : ℝ) (z : ℂ) :
    ccmTruncatedExponentialBudget s (l + h) (r + h)
        (z * (Real.exp (-s * h) : ℂ)) =
      ccmTruncatedExponentialBudget s l r z := by
  have hm : max (s * (l + h)) (s * (r + h)) = max (s * l) (s * r) + s * h := by
    rw [mul_add, mul_add, max_add_add_right]
  rw [ccmTruncatedExponentialBudget, ccmTruncatedExponentialBudget,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
    hm, mul_assoc, ← Real.exp_add]
  congr 1
  congr 1
  ring

/-- Restricting an atom to a nonempty subinterval cannot increase its budget. -/
theorem ccmTruncatedExponentialBudget_mono_interval {l l' r' r : ℝ}
    (hll : l ≤ l') (hlr : l' ≤ r') (hrr : r' ≤ r) (s : ℝ) (z : ℂ) :
    ccmTruncatedExponentialBudget s l' r' z ≤
      ccmTruncatedExponentialBudget s l r z := by
  unfold ccmTruncatedExponentialBudget
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg z)
  apply Real.exp_le_exp.mpr
  by_cases hs : 0 ≤ s
  · apply max_le
    · exact (mul_le_mul_of_nonneg_left (hlr.trans hrr) hs).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonneg_left hrr hs).trans (le_max_right _ _)
  · have hs' : s ≤ 0 := le_of_not_ge hs
    apply max_le
    · exact (mul_le_mul_of_nonpos_left hll hs').trans (le_max_left _ _)
    · exact (mul_le_mul_of_nonpos_left (hll.trans hlr) hs').trans (le_max_left _ _)

/-- Fourier decay of a finite source representation uses the sum of endpoint
budgets, with no additional dependence on the number of atoms. -/
theorem norm_fourier_sum_ccmTruncatedExponential_le {ι : Type*}
    (t : Finset ι) (s l r : ι → ℝ) (z : ι → ℂ)
    (hlr : ∀ i ∈ t, l i ≤ r i) {ξ : ℝ} (hξ : ξ ≠ 0) :
    ‖𝓕 (fun x => ∑ i ∈ t, ccmTruncatedExponential (s i) (l i) (r i) (z i) x) ξ‖ ≤
      (∑ i ∈ t, ccmTruncatedExponentialBudget (s i) (l i) (r i) (z i)) /
        (Real.pi * |ξ|) := by
  let phase : ℝ → ℂ := fun x => Complex.exp (((-2 * Real.pi * x * ξ : ℝ) : ℂ) * Complex.I)
  have hc : Continuous phase := by dsimp [phase]; fun_prop
  have hn (x : ℝ) : ‖phase x‖ = 1 := by
    dsimp [phase]
    rw [Complex.norm_exp]
    simp
  have hint (i : ι) : Integrable (fun x => phase x *
      ccmTruncatedExponential (s i) (l i) (r i) (z i) x) := by
    have hi := integrable_ccmTruncatedExponential (s i) (l i) (r i) (z i)
    refine hi.norm.mono' (hc.aestronglyMeasurable.mul hi.aestronglyMeasurable) ?_
    filter_upwards with x
    rw [norm_mul, hn, one_mul]
  have heq : 𝓕 (fun x => ∑ i ∈ t, ccmTruncatedExponential (s i) (l i) (r i) (z i) x) ξ =
      ∑ i ∈ t, 𝓕 (ccmTruncatedExponential (s i) (l i) (r i) (z i)) ξ := by
    simp_rw [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
    simp_rw [Finset.mul_sum]
    exact integral_finsetSum t (fun i _ => hint i)
  rw [heq, Finset.sum_div]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi =>
    norm_fourier_ccmTruncatedExponential_le (hlr i hi) (s i) (z i) hξ)

/-- Aperture compression acts by literal intersection of the atom interval. -/
theorem ccmTruncatedExponential_restrict (s l r u v : ℝ) (z : ℂ) :
    (Icc u v).indicator (ccmTruncatedExponential s l r z) =
      ccmTruncatedExponential s (max l u) (min r v) z := by
  funext x
  have hmem : x ∈ Icc (max l u) (min r v) ↔ x ∈ Icc u v ∧ x ∈ Icc l r := by
    simp only [mem_Icc, max_le_iff, le_min_iff]
    tauto
  by_cases huv : x ∈ Icc u v
  · rw [indicator_of_mem huv]
    by_cases hlr : x ∈ Icc l r
    · rw [ccmTruncatedExponential, ccmTruncatedExponential,
        indicator_of_mem hlr, indicator_of_mem (hmem.mpr ⟨huv, hlr⟩)]
    · rw [ccmTruncatedExponential, ccmTruncatedExponential,
        indicator_of_notMem hlr, indicator_of_notMem (fun h => hlr (hmem.mp h).2)]
  · rw [indicator_of_notMem huv, ccmTruncatedExponential,
      indicator_of_notMem (fun h => huv (hmem.mp h).1)]

end RHTower
end
