import GaloisForLFunctions.VerifiedHeightRungs.ZeroGapsFromVerifiedZeros
import GaloisForLFunctions.«arithmetic-positivity-theory».SingleHeightPhaseSelectiveApertureAndPowerSaving

/-!
# The prime polynomial is rarely large

For a `C²` test `f` supported in `[−Y, Y]` the localized Weil form is `W(S_ξ f) = A_f(ξ) − Π_f(ξ)`, with `Π_f` the prime
polynomial over `n ≤ e^{2Y}`. The windowed variance law averages `|Π_f(ξ + ξ₀)|²` against the window `|η̂(−2πξ)|²` of width
`r`, `2r e^{2Y} ≤ 1`, and finds the diagonal energy `V_f`. By Chebyshev:

* `volume_window_prime_ge_le`: on `|ξ| ≤ 1/(4πr)`, where the window is at least `(3/4) r² m₁²`, the frequencies with
  `‖Π_f‖ ≥ A` have measure at most `4 m₂ V_f/(3 r m₁² A²)`;
* `volume_bad_heights_le`: in heights `t = −2πξ`, every window of length `L ≥ 2e^{2Y}` has at most
  `8π m₂ V_f L/(3 m₁² A²)` of heights with `‖Π_f(−t/2π)‖ ≥ A`.

`m₁, m₂` are the mass and energy of the window profile.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

namespace GaloisForLFunctions.VerifiedHeightRungs

open _root_.RHTower _root_.RHTower.WeilRegular Zeta23 GaloisForLFunctions.SquareRootThreshold

noncomputable section

/-- The window transform is at least `(√3/2) r m₁` on `|ξ| ≤ 1/(4πr)`. -/
theorem three_quarters_le_norm_sq_paperFT_gapTestC {r ξ : ℝ} (hr : 0 < r) (hξ : |ξ| ≤ 1 / (4 * π * r)) :
    3 / 4 * (r ^ 2 * gapMass ^ 2) ≤ ‖paperFT (gapTestC r) (-(2 * π * (ξ : ℂ)))‖ ^ 2 := by
  have hm := gapMass_pos
  set s : ℝ := r * (-(2 * π * ξ)) with hs
  have hsz : (r : ℂ) * (-(2 * π * (ξ : ℂ))) = (s : ℂ) := by rw [hs]; push_cast; ring
  rw [paperFT_gapTestC hr, hsz]
  have hK : paperFT (fun u => ((sinhTestWeight 1 u : ℝ) : ℂ)) (s : ℂ) = (gapMass : ℂ) * kernelQ 1 s := by
    rw [kernelQ]
    have hmC : ((kernelMass 1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (kernelMass_pos one_pos le_rfl).ne'
    change _ = ((kernelMass 1 : ℝ) : ℂ) * (_ / ((kernelMass 1 : ℝ) : ℂ))
    field_simp
  rw [hK]
  obtain ⟨q, hq, -, hq2⟩ := kernelQ_real one_pos le_rfl s
  rw [hq, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hr, abs_of_pos hm]
  have hs2 : s ^ 2 ≤ 1 / 4 := by
    have h1 : |s| ≤ 1 / 2 := by
      rw [hs, abs_mul, abs_of_pos hr, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
      rw [le_div_iff₀ (by positivity)] at hξ
      nlinarith [abs_nonneg ξ]
    have := sq_abs s
    nlinarith [abs_nonneg s]
  have hq2' : 3 / 4 ≤ |q| ^ 2 := by
    rw [sq_abs]
    rw [one_mul] at hq2
    linarith
  calc 3 / 4 * (r ^ 2 * gapMass ^ 2) ≤ |q| ^ 2 * (r ^ 2 * gapMass ^ 2) :=
        mul_le_mul_of_nonneg_right hq2' (by positivity)
    _ = (r * (gapMass * |q|)) ^ 2 := by ring

/-- **Large values of the prime polynomial are rare in every window.** -/
theorem volume_window_prime_ge_le {f : ℝ → ℂ} {Y r : ℝ} (hY : 0 ≤ Y) (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-Y) Y) (hr : 0 < r) (hX : 2 * r * Real.exp (2 * Y) ≤ 1) (ξ₀ : ℝ) {A₀ : ℝ}
    (hA₀ : 0 < A₀) :
    volume (Icc (-(1 / (4 * π * r))) (1 / (4 * π * r)) ∩
        {ξ | A₀ ≤ ‖primePolynomial f ⌊Real.exp (2 * Y)⌋₊ (ξ + ξ₀)‖}) ≤
      ENNReal.ofReal (4 * gapEnergy * primeVariance f ⌊Real.exp (2 * Y)⌋₊ /
        (3 * r * gapMass ^ 2 * A₀ ^ 2)) := by
  set η := gapTestC r with hηdef
  have hη : ContDiff ℝ 2 η := gapTestC_contDiff r
  have hηs : tsupport η ⊆ Icc (-r) r := tsupport_gapTestC hr
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  have hm := gapMass_pos
  have hEn := gapEnergy_pos
  set N := ⌊Real.exp (2 * Y)⌋₊ with hNdef
  set Q : ℝ → ℂ := fun ξ => primePolynomial f N (ξ + ξ₀) with hQ
  set P : ℝ → ℝ := fun ξ => ‖paperFT η (-(2 * π * (ξ : ℂ)))‖ ^ 2 with hP
  have hPi : Integrable P := by
    refine (integrable_pairTransform hη hηc).re.congr (Eventually.of_forall fun ξ => ?_)
    simp only [pairTransform_ofReal hη hηc ξ, RCLike.re_to_complex, Complex.ofReal_re, hP]
  have hPc : Continuous P := by
    have h := Complex.continuous_re.comp ((differentiable_pairTransform hη hηc).continuous.comp
      Complex.continuous_ofReal)
    refine h.congr fun ξ => ?_
    simp only [Function.comp_apply, pairTransform_ofReal hη hηc ξ, Complex.ofReal_re, hP]
  have hQc : Continuous Q := by
    simp only [hQ, primePolynomial]
    exact (continuous_expSum _ _ _).comp (continuous_id.add continuous_const)
  set C := ∑ j ∈ Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool), ‖primeCoeff f j‖ with hC
  have hQb : ∀ ξ, ‖Q ξ‖ ≤ C := fun ξ => norm_expSum_le _ _ _ _
  set G : ℝ → ℝ := fun ξ => P ξ * ‖Q ξ‖ ^ 2 / A₀ ^ 2 with hG
  have hG0 : ∀ ξ, 0 ≤ G ξ := fun ξ => by positivity
  have hGi : Integrable G := by
    refine (hPi.mul_const (C ^ 2 / A₀ ^ 2)).mono'
      ((hPc.mul (hQc.norm.pow 2)).div_const _).aestronglyMeasurable
      (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_of_nonneg (hG0 ξ)]
    have hP0 : 0 ≤ P ξ := sq_nonneg _
    have hQ2 : ‖Q ξ‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hQb ξ) 2
    show P ξ * ‖Q ξ‖ ^ 2 / A₀ ^ 2 ≤ P ξ * (C ^ 2 / A₀ ^ 2)
    rw [mul_div_assoc]
    gcongr
  have hGint : ∫ ξ, G ξ = (∫ t, ‖η t‖ ^ 2) * primeVariance f N / A₀ ^ 2 := by
    have hvar := integral_windowed_sq_deviation_eq hY hf hfs hη hηs hX ξ₀
    have hdev : ∀ ξ : ℝ, ‖zetaZeroConfig.W (heightShift (ξ + ξ₀) f) (heightShift (ξ + ξ₀) f) -
        archPart f (ξ + ξ₀)‖ = ‖Q ξ‖ := by
      intro ξ
      rw [zetaZeroConfig_W_heightShift_eq_sub hf hfs, sub_sub_cancel_left, norm_neg]
    simp_rw [hdev] at hvar
    simp only [hG, integral_div]
    rw [hvar]
  rw [integral_gapTestC_sq hr] at hGint
  -- The window set.
  set D := 1 / (4 * π * r) with hD
  set B := Icc (-D) D ∩ {ξ | A₀ ≤ ‖Q ξ‖} with hB
  have hBm : MeasurableSet B :=
    measurableSet_Icc.inter (isClosed_le continuous_const hQc.norm).measurableSet
  have hBfin : volume B < ⊤ := (measure_mono Set.inter_subset_left).trans_lt (by simp [volume_Icc])
  set c := 3 / 4 * (r ^ 2 * gapMass ^ 2) with hc
  have hc0 : 0 < c := by positivity
  have hind : ∀ ξ, B.indicator (fun _ => c) ξ ≤ G ξ := by
    intro ξ
    by_cases hξ : ξ ∈ B
    · rw [Set.indicator_of_mem hξ]
      obtain ⟨hξI, hξQ⟩ := hξ
      have hPξ : c ≤ P ξ := three_quarters_le_norm_sq_paperFT_gapTestC hr
        (abs_le.mpr ⟨hξI.1, hξI.2⟩)
      have hratio : 1 ≤ ‖Q ξ‖ ^ 2 / A₀ ^ 2 := by
        rw [le_div_iff₀ (by positivity), one_mul]
        exact pow_le_pow_left₀ hA₀.le hξQ 2
      calc c = c * 1 := by ring
        _ ≤ P ξ * (‖Q ξ‖ ^ 2 / A₀ ^ 2) := mul_le_mul hPξ hratio zero_le_one (sq_nonneg _)
        _ = G ξ := by rw [hG]; ring
    · rw [Set.indicator_of_notMem hξ]
      exact hG0 ξ
  have hint : ∫ ξ, B.indicator (fun _ => c) ξ ≤ ∫ ξ, G ξ :=
    integral_mono ((integrable_indicator_iff hBm).mpr (integrableOn_const hBfin.ne)) hGi hind
  rw [integral_indicator_const _ hBm, smul_eq_mul, hGint] at hint
  have hvol : (volume B).toReal ≤ r * gapEnergy * primeVariance f N / A₀ ^ 2 / c := by
    rw [le_div_iff₀ hc0]
    simpa [Measure.real] using hint
  have heq : r * gapEnergy * primeVariance f N / A₀ ^ 2 / c =
      4 * gapEnergy * primeVariance f N / (3 * r * gapMass ^ 2 * A₀ ^ 2) := by
    rw [hc]
    field_simp
  rw [heq] at hvol
  calc volume B = ENNReal.ofReal (volume B).toReal := (ENNReal.ofReal_toReal hBfin.ne).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal hvol

/-- **The windowed Chebyshev bound in heights.** -/
theorem volume_bad_heights_le {f : ℝ → ℂ} {Y L A : ℝ} (hY : 0 ≤ Y) (hf : ContDiff ℝ 2 f)
    (hfs : tsupport f ⊆ Icc (-Y) Y) (hL : 2 * Real.exp (2 * Y) ≤ L) (hA : 0 < A) (c : ℝ) :
    volume (Icc c (c + L) ∩
        {t : ℝ | A ≤ ‖primePolynomial (f) ⌊Real.exp (2 * Y)⌋₊ (-t / (2 * π))‖}) ≤
      ENNReal.ofReal (8 * π * gapEnergy * primeVariance (f) ⌊Real.exp (2 * Y)⌋₊ * L /
        (3 * gapMass ^ 2 * A ^ 2)) := by
  have hπ := Real.pi_pos
  have hm := gapMass_pos
  have hL0 : 0 < L := lt_of_lt_of_le (by positivity) hL
  obtain ⟨r, hr⟩ : ∃ r, r = 1 / L := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; positivity
  have hX : 2 * r * Real.exp (2 * Y) ≤ 1 := by
    rw [hr, show 2 * (1 / L) * Real.exp (2 * Y) = 2 * Real.exp (2 * Y) / L by ring, div_le_one hL0]
    exact hL
  obtain ⟨ξ₀, hξ₀⟩ : ∃ ξ₀, ξ₀ = -(c + L / 2) / (2 * π) := ⟨_, rfl⟩
  have hB := volume_window_prime_ge_le hY hf hfs hr0 hX ξ₀ hA
  set S := Icc (-(1 / (4 * π * r))) (1 / (4 * π * r)) ∩
    {ξ | A ≤ ‖primePolynomial (f) ⌊Real.exp (2 * Y)⌋₊ (ξ + ξ₀)‖} with hS
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = -(2 * π)⁻¹ := ⟨_, rfl⟩
  have hk0 : k ≠ 0 := by rw [hk]; exact neg_ne_zero.2 (inv_ne_zero (by positivity))
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = (c + L / 2) / (2 * π) := ⟨_, rfl⟩
  have hpre : Icc c (c + L) ∩
      {t : ℝ | A ≤ ‖primePolynomial (f) ⌊Real.exp (2 * Y)⌋₊ (-t / (2 * π))‖} =
      (fun t => k * t) ⁻¹' ((fun x => x + d) ⁻¹' S) := by
    ext t
    have hφ : k * t + d + ξ₀ = -t / (2 * π) := by
      rw [hk, hd, hξ₀]
      field_simp
      ring
    have hφ' : k * t + d = (c + L / 2 - t) / (2 * π) := by
      rw [hk, hd]
      field_simp
      ring
    have hD : 1 / (4 * π * r) = L / 2 / (2 * π) := by
      rw [hr]
      field_simp
      ring
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_setOf_eq, Set.mem_preimage, hS, hφ, hD]
    rw [hφ']
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨?_, ?_⟩, h3⟩
      · rw [neg_le, ← neg_div, div_le_div_iff_of_pos_right (by positivity)]
        linarith only [h2]
      · rw [div_le_div_iff_of_pos_right (by positivity)]
        linarith only [h1]
    · rintro ⟨⟨h1, h2⟩, h3⟩
      refine ⟨⟨?_, ?_⟩, h3⟩
      · rw [div_le_div_iff_of_pos_right (by positivity)] at h2
        linarith only [h2]
      · rw [neg_le, ← neg_div, div_le_div_iff_of_pos_right (by positivity)] at h1
        linarith only [h1]
  rw [hpre, Real.volume_preimage_mul_left hk0, measure_preimage_add_right]
  have hkabs : |k⁻¹| = 2 * π := by
    rw [hk, inv_neg, inv_inv, abs_neg, abs_of_pos (by positivity)]
  rw [hkabs]
  calc ENNReal.ofReal (2 * π) * volume S
      ≤ ENNReal.ofReal (2 * π) * ENNReal.ofReal (4 * gapEnergy * primeVariance (f)
          ⌊Real.exp (2 * Y)⌋₊ / (3 * r * gapMass ^ 2 * A ^ 2)) := by gcongr
    _ = _ := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [hr]
      field_simp
      ring

end

end GaloisForLFunctions.VerifiedHeightRungs
