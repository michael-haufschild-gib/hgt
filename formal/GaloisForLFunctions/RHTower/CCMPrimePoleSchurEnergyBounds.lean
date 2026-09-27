import GaloisForLFunctions.RHTower.CCMPrimePoleSchurDefect

/-!
# Stability of the full complex prime-edge energy

The estimates apply to the literal aperture vectors and actual prime-power
weights. They control the full correction, including all mixed terms.
-/

open Complex MeasureTheory Set
open scoped ENNReal InnerProduct BigOperators
noncomputable section
namespace RHTower

theorem ccmPrimePoleEdgeEnergy_neg (a : SuzukiPositiveAperture) (h : ℝ) (f : SoninL2) :
    ccmPrimePoleEdgeEnergy a h (-f) = ccmPrimePoleEdgeEnergy a h f := by
  unfold ccmPrimePoleEdgeEnergy
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_neg f, (Lp.coeFn_neg f).comp_tendsto
    (measurePreserving_add_right volume h).quasiMeasurePreserving.tendsto_ae] with x hx ht
  change (-f) (x+h) = -(f (x+h)) at ht
  unfold ccmPrimePoleEdgeDensity
  by_cases hm : x ∈ centralInterval a.1 ∩ (fun y : ℝ => y+h) ⁻¹' centralInterval a.1
  · simp only [indicator_of_mem hm]
    rw [hx, ht]
    simp only [Pi.neg_apply]
    rw [mul_neg, mul_neg, neg_sub_neg, norm_sub_rev]
  · simp only [indicator_of_notMem hm]

theorem ccmPrimePoleSchurEnergy_neg (a : SuzukiPositiveAperture) (f : SoninL2) :
    ccmPrimePoleSchurEnergy a (-f) = ccmPrimePoleSchurEnergy a f := by
  unfold ccmPrimePoleSchurEnergy
  simp_rw [ccmPrimePoleEdgeEnergy_neg]

private theorem norm_sub_sq_bound (z w : ℂ) :
    ‖z-w‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 + 2 * ‖w‖ ^ 2 := by
  have h := norm_sub_le z w
  nlinarith [norm_nonneg (z-w), norm_nonneg z, norm_nonneg w, sq_nonneg (‖z‖-‖w‖)]

theorem ccmPrimePoleEdgeEnergy_sub_le (a : SuzukiPositiveAperture) (h : ℝ)
    (f g : suzukiApertureHilbert a) :
    ccmPrimePoleEdgeEnergy a h (f-g).1 ≤
      2 * ccmPrimePoleEdgeEnergy a h f.1 + 2 * ccmPrimePoleEdgeEnergy a h g.1 := by
  have hsub := Lp.coeFn_sub f.1 g.1
  have hsubt := hsub.comp_tendsto
    (measurePreserving_add_right volume h).quasiMeasurePreserving.tendsto_ae
  unfold ccmPrimePoleEdgeEnergy
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((integrable_ccmPrimePoleEdgeDensity a h f).const_mul 2)
      ((integrable_ccmPrimePoleEdgeDensity a h g).const_mul 2)]
  apply integral_mono_ae (integrable_ccmPrimePoleEdgeDensity a h (f-g))
    (((integrable_ccmPrimePoleEdgeDensity a h f).const_mul 2).add
      ((integrable_ccmPrimePoleEdgeDensity a h g).const_mul 2))
  filter_upwards [hsub, hsubt] with x hs ht
  change (f.1-g.1) (x+h) = f.1 (x+h)-g.1 (x+h) at ht
  simp only [Pi.add_apply, Pi.sub_apply] at hs ⊢
  unfold ccmPrimePoleEdgeDensity
  by_cases hx : x ∈ centralInterval a.1 ∩ (fun y : ℝ => y+h) ⁻¹' centralInterval a.1
  · simp only [indicator_of_mem hx]
    change ‖(primePoleProfile x : ℂ) * (f.1-g.1) (x+h) -
      (primePoleProfile (x+h) : ℂ) * (f.1-g.1) x‖ ^ 2 / _ ≤ _
    rw [hs, ht]
    have hn := norm_sub_sq_bound
      ((primePoleProfile x : ℂ)*f.1 (x+h)-(primePoleProfile (x+h) : ℂ)*f.1 x)
      ((primePoleProfile x : ℂ)*g.1 (x+h)-(primePoleProfile (x+h) : ℂ)*g.1 x)
    have heq : (primePoleProfile x : ℂ)*(f.1 (x+h)-g.1 (x+h))-
        (primePoleProfile (x+h) : ℂ)*(f.1 x-g.1 x) =
      ((primePoleProfile x : ℂ)*f.1 (x+h)-(primePoleProfile (x+h) : ℂ)*f.1 x)-
        ((primePoleProfile x : ℂ)*g.1 (x+h)-(primePoleProfile (x+h) : ℂ)*g.1 x) := by ring
    rw [heq]
    calc
      _ ≤ (2 * ‖(primePoleProfile x : ℂ)*f.1 (x+h)-
          (primePoleProfile (x+h) : ℂ)*f.1 x‖ ^ 2 +
          2 * ‖(primePoleProfile x : ℂ)*g.1 (x+h)-
          (primePoleProfile (x+h) : ℂ)*g.1 x‖ ^ 2) /
          (primePoleProfile x * primePoleProfile (x+h)) :=
        div_le_div_of_nonneg_right hn
          (mul_pos (primePoleProfile_pos x) (primePoleProfile_pos (x+h))).le
      _ = _ := by ring
  · simp only [indicator_of_notMem hx, mul_zero, zero_add, le_refl]

theorem ccmPrimePoleSchurEnergy_sub_le (a : SuzukiPositiveAperture)
    (f g : suzukiApertureHilbert a) :
    ccmPrimePoleSchurEnergy a (f-g).1 ≤
      2 * ccmPrimePoleSchurEnergy a f.1 + 2 * ccmPrimePoleSchurEnergy a g.1 := by
  unfold ccmPrimePoleSchurEnergy
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro n _
  have hn := mul_le_mul_of_nonneg_left (ccmPrimePoleEdgeEnergy_sub_le a (Real.log n) f g)
    (show 0 ≤ ArithmeticFunction.vonMangoldt n / Real.sqrt n from
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
  convert hn using 1
  ring

/-- A physical norm bound controls every phase edge simultaneously. -/
theorem ccmPrimePoleSchurEnergy_le_two_envelope (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) :
    ccmPrimePoleSchurEnergy a f.1 ≤ 2 * ccmPrimePoleSchurEnvelope a * ‖f‖ ^ 2 := by
  have he := ccmPrimePoleSchurEnergy_le_deficit a f
  have hp : ‖ccmFinitePrimeOperator a‖ ≤ ccmPrimePoleSchurEnvelope a :=
    norm_ccmFinitePrimeOperator_le_log4 a
  have hc : -(inner ℂ (ccmFinitePrimeOperator a f) f).re ≤
      ccmPrimePoleSchurEnvelope a * ‖f‖ ^ 2 := calc
    _ ≤ ‖inner ℂ (ccmFinitePrimeOperator a f) f‖ :=
      (neg_le_abs _).trans (Complex.abs_re_le_norm _)
    _ ≤ ‖ccmFinitePrimeOperator a f‖ * ‖f‖ :=
      norm_inner_le_norm (𝕜 := ℂ) (ccmFinitePrimeOperator a f) f
    _ ≤ (‖ccmFinitePrimeOperator a‖ * ‖f‖) * ‖f‖ :=
      mul_le_mul_of_nonneg_right ((ccmFinitePrimeOperator a).le_opNorm f) (norm_nonneg f)
    _ ≤ ccmPrimePoleSchurEnvelope a * ‖f‖ ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_right hp (sq_nonneg ‖f‖)]
  linarith

end RHTower
