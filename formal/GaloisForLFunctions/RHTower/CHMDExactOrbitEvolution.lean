import GaloisForLFunctions.RHTower.CHMDExactDivisorPackets

/-!
# Exact arithmetic evolution of one CHMD divisor orbit

The multiplicity-exact selector isolates an entire time evolution. Its actual
prime--archimedean wave is `E * Re cos(t * w)`, where `E` is its full arithmetic
energy and `w` is the selected Klein--Gordon frequency. The same function is an
explicit shifted-kernel integral of the original CHMD wave. No other zero orbit
or polar contribution survives.

The failure of the real cosine addition law is one exact square: for every finite
real packet, its quadratic defect is
`2 * E^2 * (sum_i c_i * Im cos(t_i * w))^2`.
Thus the isolated defect has rank at most one. This does not prove that it vanishes,
or establish nonnegativity of the original arithmetic Weil energy.
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped BigOperators ComplexConjugate

noncomputable section

namespace RHTower.CHMDOrbitEvolution


private theorem re_cos (z : ℂ) :
    (Complex.cos z).re = Real.cos z.re * Real.cosh z.im := by
  rw [Complex.cos_eq, ← Complex.ofReal_cos, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sin, ← Complex.ofReal_sinh]
  simp [Complex.cos_ofReal_re]

private theorem im_cos (z : ℂ) :
    (Complex.cos z).im = -Real.sin z.re * Real.sinh z.im := by
  rw [Complex.cos_eq, ← Complex.ofReal_cos, ← Complex.ofReal_cosh,
    ← Complex.ofReal_sin, ← Complex.ofReal_sinh]
  simp [Complex.sin_ofReal_re, Complex.sinh_ofReal_re]

open WeilSpectral EvenSector CHMDStage3 CHMDStage15 CHMDStage16
open CHMDExactPackets CHMDGrowthCollapse

def kgCosRe (y : ℝ) (z : ℂ) : ℝ := (Complex.cos ((y : ℂ) * rhoC z)).re

theorem kgCosRe_neg (y : ℝ) (z : ℂ) : kgCosRe y (-z) = kgCosRe y z := by
  simp only [kgCosRe, rhoC_neg]

theorem kgCosRe_conj (y : ℝ) {z : ℂ} (hz : |z.im| < Real.sqrt 2) :
    kgCosRe y (conj z) = kgCosRe y z := by
  simpa only [kgCosRe, Complex.conj_re] using
    congrArg Complex.re (conj_trig_rhoC_conj y hz).1

theorem kgCosRe_eq_of_orbitSign_ne_zero (y : ℝ) {a z : ℂ}
    (hz : |z.im| < Real.sqrt 2) (hs : orbitSign a z ≠ 0) :
    kgCosRe y z = kgCosRe y a := by
  classical
  by_cases h₁ : z = a
  · rw [h₁]
  by_cases h₂ : -z = a
  · rw [← h₂, kgCosRe_neg]
  by_cases h₃ : conj z = a
  · rw [← h₃, kgCosRe_conj y hz]
  by_cases h₄ : -conj z = a
  · rw [← h₄, kgCosRe_neg, kgCosRe_conj y hz]
  exact False.elim (hs (by simp [orbitSign, h₁, h₂, h₃, h₄]))

/-- Exact complex divisor values of the selector square, with no imaginary remainder. -/
theorem specSq_zeroSelector_complex (ρ σ : zetaZeroConfig.carrier) :
    specSq (zeroSelector ρ) (gammaOf σ) =
      ((-(orbitSign (gammaOf ρ) (gammaOf σ)) ^ 2 : ℝ) : ℂ) := by
  have hsharp : conj (zeroSelector ρ (conj (gammaOf σ))) = zeroSelector ρ (gammaOf σ) := by
    change conj (selector (zeroSupport ρ) (conj (gammaOf σ))) =
      selector (zeroSupport ρ) (gammaOf σ)
    rw [selector_conj, Complex.conj_conj]
  rw [specSq, hsharp, zeroSelector_zero_values]
  push_cast
  ring_nf
  simp

theorem rhoCosShift_zeroSelector_re (ρ σ : zetaZeroConfig.carrier) (y : ℝ) :
    (rhoCosShift y (zeroSelector ρ) (gammaOf σ)).re =
      -(orbitSign (gammaOf ρ) (gammaOf σ)) ^ 2 * kgCosRe y (gammaOf ρ) := by
  rw [rhoCosShift, specSq_zeroSelector_complex]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  change kgCosRe y (gammaOf σ) * -(orbitSign (gammaOf ρ) (gammaOf σ)) ^ 2 = _
  by_cases hs : orbitSign (gammaOf ρ) (gammaOf σ) = 0
  · simp [hs]
  · have hz : |(gammaOf σ).im| < Real.sqrt 2 :=
      abs_im_lt_sqrt_two (by linarith [abs_im_gammaOf_lt σ])
    rw [kgCosRe_eq_of_orbitSign_ne_zero y hz hs]
    ring

/-- The actual arithmetic wave obtained by replacing the reference packet by the selector. -/
def orbitWave (ρ : zetaZeroConfig.carrier) (y : ℝ) : ℝ :=
  cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) (zeroSelector ρ) y

/-- Every time slice is carried by the selected Klein--Gordon orbit alone. -/
theorem orbitWave_eq (ρ : zetaZeroConfig.carrier) (y : ℝ) :
    orbitWave ρ y = zeroSelectorEnergy ρ * (Complex.cos ((y : ℂ) * kgFreq ρ)).re := by
  rw [orbitWave, cosineShiftFn_vonMangoldt_eq_tsum_re (zeroSelector_evenStrip ρ),
    zeroSelectorEnergy, evenWeilDensity_specSq_vonMangoldt_eq_tsum_re (zeroSelector_evenStrip ρ),
    ← tsum_mul_right]
  apply tsum_congr
  intro σ
  rw [rhoCosShift_zeroSelector_re, zeroSelector_specSq_re]
  change _ = _ * kgCosRe y (gammaOf ρ)
  ring

/-- Exact separation into the real oscillation and the transverse hyperbolic factor. -/
theorem orbitWave_eq_cos_mul_cosh (ρ : zetaZeroConfig.carrier) (y : ℝ) :
    orbitWave ρ y = zeroSelectorEnergy ρ *
      Real.cos (y * (kgFreq ρ).re) * Real.cosh (y * (kgFreq ρ).im) := by
  rw [orbitWave_eq, re_cos]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero]
  ring

/-- The admissible multiplier that cancels the reference `sechHalf` packet. -/
def selectorCosh (ρ : zetaZeroConfig.carrier) (z : ℂ) : ℂ :=
  zeroSelector ρ z * Complex.cosh (z / 2)

theorem multiplier_selectorCosh (ρ : zetaZeroConfig.carrier) : Multiplier (selectorCosh ρ) := by
  obtain ⟨C, hs⟩ := selector_strip (zeroSupport ρ)
  have hC := hs.const_nonneg (by norm_num)
  refine ⟨⟨1 / 4, C, by norm_num, fun z hz => ?_, fun z hz => ?_⟩,
    fun z => ?_, fun z => ?_⟩
  · exact (hs.diff z hz).mul
      (Complex.differentiable_cosh.differentiableAt.comp z (differentiableAt_id.div_const 2))
  · change ‖selector (zeroSupport ρ) z * Complex.cosh (z / 2)‖ ≤ _
    rw [norm_mul]
    have hc : ‖Complex.cosh (z / 2)‖ ≤ Real.exp (1 / 2 * |z.re|) := by
      have h1 := norm_cosh_le_real_cosh_re (z / 2)
      have hre : (z / 2).re = z.re / 2 := by simp
      rw [hre] at h1
      refine h1.trans ((real_cosh_le_exp_abs (z.re / 2)).trans (le_of_eq ?_))
      rw [abs_div, abs_two]
      ring_nf
    calc ‖selector (zeroSupport ρ) z‖ * ‖Complex.cosh (z / 2)‖
        ≤ (C * Real.exp (-(3 / 4 * |z.re|))) * Real.exp (1 / 2 * |z.re|) :=
          mul_le_mul (hs.bound z hz) hc (norm_nonneg _) (by positivity)
      _ = C * Real.exp (-(1 / 4 * |z.re|)) := by rw [mul_assoc, ← Real.exp_add]; ring_nf
  · simp only [selectorCosh, zeroSelector, selector_even, neg_div, Complex.cosh_neg]
  · simp only [selectorCosh, zeroSelector, selector_conj, map_mul,
      show conj z / 2 = conj (z / 2) by rw [map_div₀, map_ofNat], Complex.cosh_conj]

theorem sechHalf_mul_selectorCosh (ρ : zetaZeroConfig.carrier) {z : ℂ}
    (hz : |z.im| ≤ 9 / 4) : sechHalf z * selectorCosh ρ z = zeroSelector ρ z := by
  unfold sechHalf selectorCosh
  have hne := cosh_half_ne_zero hz
  field_simp

theorem cosineShiftFn_sechHalf_mul_selectorCosh_eq (ρ : zetaZeroConfig.carrier)
    (lam : ℕ → ℝ) (y : ℝ) :
    cosineShiftFn lam (fun z => sechHalf z * selectorCosh ρ z) y =
      cosineShiftFn lam (zeroSelector ρ) y := by
  have heq : ∀ z : ℂ, |z.im| ≤ 5 / 4 →
      rhoCosShift y (fun w => sechHalf w * selectorCosh ρ w) z =
        rhoCosShift y (zeroSelector ρ) z := by
    intro z hz
    unfold rhoCosShift specSq
    dsimp only
    have hz1 : |z.im| ≤ 9 / 4 := by linarith
    have hz2 : |(conj z).im| ≤ 9 / 4 := by rw [Complex.conj_im, abs_neg]; linarith
    rw [sechHalf_mul_selectorCosh ρ hz1, sechHalf_mul_selectorCosh ρ hz2]
  exact evenWeilDensity_congr (heq _ (by norm_num [abs_of_pos]))
    (heq _ (by norm_num [abs_of_pos])) (fun r => heq _ (by simp; norm_num))

/-- The explicit real convolution kernel of the selected arithmetic evolution. -/
def orbitKernel (ρ : zetaZeroConfig.carrier) : ℝ → ℝ :=
  stripTest (specSq (rhoLift (selectorCosh ρ)))

/-- Exact extraction from the original CHMD causal wave, for every real shift. -/
theorem orbitWave_convolution (ρ : zetaZeroConfig.carrier) (y : ℝ) :
    orbitWave ρ y = ∫ t : ℝ, cosShiftKernel (orbitKernel ρ) y t * chmdWave t := by
  change orbitWave ρ y = ∫ t : ℝ,
    cosShiftKernel (stripTest (specSq (rhoLift (selectorCosh ρ)))) y t *
      cosineShiftFn (fun n => (ArithmeticFunction.vonMangoldt n : ℝ)) sechHalf t
  rw [← cosineShiftFn_mul_eq_integral_cosShiftKernel_unconditional
    abs_vonMangoldt_le_sqrt_mul_one_add_log evenStrip_sechHalf (multiplier_selectorCosh ρ) y]
  exact (cosineShiftFn_sechHalf_mul_selectorCosh_eq ρ _ y).symm

/-- The full isolated evolution has no polar contribution. -/
theorem orbitWave_prime_arch (ρ : zetaZeroConfig.carrier) (y : ℝ) :
    orbitWave ρ y =
      1 / (2 * Real.pi) * evenArchPart (rhoCosShift y (zeroSelector ρ)) -
        evenPrimePart (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (rhoCosShift y (zeroSelector ρ)) := by
  change evenWeilDensity _ _ = _
  rw [evenWeilDensity_eq_parts]
  have hp : evenPolePart (rhoCosShift y (zeroSelector ρ)) = 0 := by
    simp [evenPolePart, rhoCosShift, specSq,
      (zeroSelector_pole_zero ρ).1, (zeroSelector_pole_zero ρ).2]
  rw [hp, zero_add]

/-- The imaginary cosine channel retained by an off-line Klein--Gordon mode. -/
def orbitQuadrature (ρ : zetaZeroConfig.carrier) (y : ℝ) : ℝ :=
  (Complex.cos ((y : ℂ) * kgFreq ρ)).im

theorem orbitQuadrature_eq (ρ : zetaZeroConfig.carrier) (y : ℝ) :
    orbitQuadrature ρ y =
      -Real.sin (y * (kgFreq ρ).re) * Real.sinh (y * (kgFreq ρ).im) := by
  rw [orbitQuadrature, im_cos]
  simp

/-- The arithmetic defect from the real-frequency cosine addition law. -/
def orbitAdditionDefect (ρ : zetaZeroConfig.carrier) (s t : ℝ) : ℝ :=
  2 * orbitWave ρ s * orbitWave ρ t -
    zeroSelectorEnergy ρ * (orbitWave ρ (s + t) + orbitWave ρ (s - t))

/-- The complete addition defect factors through a single real channel. -/
theorem orbitAdditionDefect_eq (ρ : zetaZeroConfig.carrier) (s t : ℝ) :
    orbitAdditionDefect ρ s t =
      2 * zeroSelectorEnergy ρ ^ 2 * orbitQuadrature ρ s * orbitQuadrature ρ t := by
  have hadd : Complex.cos (((s + t : ℝ) : ℂ) * kgFreq ρ) +
      Complex.cos (((s - t : ℝ) : ℂ) * kgFreq ρ) =
        2 * Complex.cos ((s : ℂ) * kgFreq ρ) * Complex.cos ((t : ℂ) * kgFreq ρ) := by
    rw [Complex.ofReal_add, Complex.ofReal_sub, add_mul, sub_mul, Complex.cos_add, Complex.cos_sub]
    ring
  have hreal := congrArg Complex.re hadd
  simp [Complex.mul_re] at hreal
  simp only [orbitAdditionDefect, orbitWave_eq, orbitQuadrature,
    Complex.ofReal_add, Complex.ofReal_sub]
  linear_combination -(zeroSelectorEnergy ρ) ^ 2 * hreal

/-- Every finite quadratic defect is exactly one square, without an energy-sign premise. -/
theorem orbitAdditionDefect_quadratic (ρ : zetaZeroConfig.carrier)
    {N : ℕ} (t c : Fin N → ℝ) :
    (∑ i, ∑ j, c i * c j * orbitAdditionDefect ρ (t i) (t j)) =
      2 * zeroSelectorEnergy ρ ^ 2 * (∑ i, c i * orbitQuadrature ρ (t i)) ^ 2 := by
  simp only [orbitAdditionDefect_eq]
  rw [pow_two (∑ i, c i * orbitQuadrature ρ (t i)), Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The isolated addition defect is positive semidefinite, unconditionally. -/
theorem orbitAdditionDefect_nonneg (ρ : zetaZeroConfig.carrier)
    {N : ℕ} (t c : Fin N → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j * orbitAdditionDefect ρ (t i) (t j) := by
  rw [orbitAdditionDefect_quadratic]
  positivity

end RHTower.CHMDOrbitEvolution
