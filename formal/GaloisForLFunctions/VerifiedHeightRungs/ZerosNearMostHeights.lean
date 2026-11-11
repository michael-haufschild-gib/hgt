import GaloisForLFunctions.VerifiedHeightRungs.ZeroGapsFromVerifiedZeros
import GaloisForLFunctions.«arithmetic-positivity-theory».SingleHeightPhaseSelectiveApertureAndPowerSaving

/-!
# Zeros near most heights

`exists_zero_near_of_onLine` needs heights above `gapHeight σ ≈ exp(138 e^Y)`: it pays the prime polynomial
by its maximum and the poles by `sinh Y` at every height. Paying both at the actual height:

* `re_W_modulatedTest_gapTest_le_of_far`: if every zero within `e^Y` of `t` is on the line and none lies within `σ`
  of `t`, then `Re W(g_t, g_t) ≤ gapWeight σ Y · 5760 log(|t| + 3)`, where `g_t` is the test of width `Y`
  modulated to `t`;
* `re_W_modulatedTest_gapTest_ge`: `Re W(g_t, g_t)` is at least `(log(1 + |t|/8) − 10) Y m₂` minus a tail `O(1/|t|)`,
  a pole term `O(e^Y/|t|⁴)` and the prime polynomial `Re Π(−t/2π)`;
* `volume_window_prime_ge_le`: by the windowed variance law, in every window `|ξ| ≤ 1/(4πr)` (`2r e^{2Y} ≤ 1`) the
  heights where `‖Π‖ ≥ A₀` have measure at most `4 m₂ V/(3 r m₁² A₀²)`, `V` the diagonal energy of the prime
  polynomial and `m₁, m₂` the mass and energy of the profile.

So the heights where the gap test fails are rare in every window of length `≍ e^{2Y}`, once the height is
`exp(O(Y))`; this replaces the double-exponential `gapHeight`.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped ComplexConjugate

namespace GaloisForLFunctions.VerifiedHeightRungs

open _root_.RHTower _root_.RHTower.WeilRegular Zeta23 GaloisForLFunctions.SquareRootThreshold

noncomputable section

/-! ### The zero side -/

/-- **No zero within `σ`.** The modulated gap test then has a small form. -/
theorem re_W_modulatedTest_gapTest_le_of_far {σ Y t : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hY : 0 < Y)
    (hon : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im - t| ≤ Real.exp Y → ρ.re = 1 / 2)
    (hfar : ∀ ρ ∈ zetaZeroConfig.carrier, σ ≤ |ρ.im - t|) :
    (zetaZeroConfig.W (modulatedTest t (gapTest Y)) (modulatedTest t (gapTest Y))).re ≤
      gapWeight σ Y * (24 * 240 * Real.log (|t| + 3)) := by
  have hloc := zeta_unit_count_le_240
  obtain ⟨hwsum, hwle⟩ := window_tsum_le zetaZeroConfig (A₀ := 240) (by norm_num) hloc t
  have hbd : ∀ ρ : zetaZeroConfig.carrier,
      ‖zetaZeroConfig.Wsummand (modulatedTest t (gapTest Y)) (modulatedTest t (gapTest Y)) ρ‖ ≤
        gapWeight σ Y * ((zetaZeroConfig.mult ρ : ℝ) / (1 + |(ρ : ℂ).im - t|) ^ 3) := fun ρ =>
    norm_Wsummand_gapTest_le hσ hσ1 hY ρ.2 (hfar ρ ρ.2) fun h => hon ρ ρ.2 h
  have hw0 : 0 ≤ gapWeight σ Y := by unfold gapWeight; positivity
  have hsumN : Summable fun ρ : zetaZeroConfig.carrier =>
      ‖zetaZeroConfig.Wsummand (modulatedTest t (gapTest Y)) (modulatedTest t (gapTest Y)) ρ‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbd (hwsum.mul_left _)
  rw [ZeroConfig.W]
  refine (Complex.re_le_norm _).trans ((norm_tsum_le_tsum_norm hsumN).trans ?_)
  refine (hsumN.tsum_le_tsum hbd (hwsum.mul_left _)).trans ?_
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hwle hw0

/-- **A large form forces a zero within `σ`.** -/
theorem exists_zero_near_of_re_W_gt {σ Y t : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hY : 0 < Y)
    (hon : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.im - t| ≤ Real.exp Y → ρ.re = 1 / 2)
    (hgt : gapWeight σ Y * (24 * 240 * Real.log (|t| + 3)) <
      (zetaZeroConfig.W (modulatedTest t (gapTest Y)) (modulatedTest t (gapTest Y))).re) :
    ∃ ρ ∈ zetaZeroConfig.carrier, |ρ.im - t| < σ := by
  by_contra hno
  push Not at hno
  exact absurd (re_W_modulatedTest_gapTest_le_of_far hσ hσ1 hY hon hno) (not_le.mpr hgt)

/-! ### The symbol side at the actual height -/

theorem heightShift_gapTestC_eq (Y t : ℝ) :
    heightShift (-t / (2 * π)) (gapTestC Y) = modulatedTest t (gapTest Y) := by
  funext u
  simp only [heightShift, modulatedTest, gapTestC]
  congr 2
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

/-- **The gap test at height `t`.** Main term, tail, decaying pole term and the prime polynomial at `−t/2π`. -/
theorem re_W_modulatedTest_gapTest_ge {Y : ℝ} (hY : 0 < Y) (t : ℝ) :
    (Real.log (1 + |t| / 8) - 10) * (Y * gapEnergy) - gapTail Y / (8 * (1 + |t| / 2)) -
        2 * Real.exp Y * gapTail Y / (1 + |t|) ^ 4 -
        (primePolynomial (gapTestC Y) ⌊Real.exp (2 * Y)⌋₊ (-t / (2 * π))).re ≤
      (zetaZeroConfig.W (modulatedTest t (gapTest Y)) (modulatedTest t (gapTest Y))).re := by
  have h := ArithmeticPositivityTheory.zetaZeroConfig_re_W_heightShift_ge_sub_re_primePolynomial_decay
    hY.le (gapTestC_contDiff Y) (tsupport_gapTestC hY) (-t / (2 * π))
  rw [heightShift_gapTestC_eq, integral_gapTestC_sq hY] at h
  have habs : |(-t / (2 * π))| = |t| / (2 * π) := by
    rw [abs_div, abs_neg, abs_of_pos (by positivity : 0 < 2 * π)]
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have e1 : 1 + π * |(-t / (2 * π))| / 4 = 1 + |t| / 8 := by rw [habs]; field_simp; ring
  have e2 : 1 + π * |(-t / (2 * π))| = 1 + |t| / 2 := by rw [habs]; field_simp
  have e3 : 1 + 2 * π * |(-t / (2 * π))| = 1 + |t| := by rw [habs]; field_simp
  rw [e1, e2, e3] at h
  have hg : (4 * ((∫ u, ‖gapTestC Y u‖) + ∫ u, ‖deriv (deriv (gapTestC Y)) u‖)) ^ 2 = gapTail Y := rfl
  rw [hg] at h
  exact h

/-! ### The windowed Chebyshev bound -/

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
theorem volume_window_prime_ge_le {Y r : ℝ} (hY : 0 < Y) (hr : 0 < r)
    (hX : 2 * r * Real.exp (2 * Y) ≤ 1) (ξ₀ : ℝ) {A₀ : ℝ} (hA₀ : 0 < A₀) :
    volume (Icc (-(1 / (4 * π * r))) (1 / (4 * π * r)) ∩
        {ξ | A₀ ≤ ‖primePolynomial (gapTestC Y) ⌊Real.exp (2 * Y)⌋₊ (ξ + ξ₀)‖}) ≤
      ENNReal.ofReal (4 * gapEnergy * primeVariance (gapTestC Y) ⌊Real.exp (2 * Y)⌋₊ /
        (3 * r * gapMass ^ 2 * A₀ ^ 2)) := by
  set f := gapTestC Y with hfdef
  set η := gapTestC r with hηdef
  have hf : ContDiff ℝ 2 f := gapTestC_contDiff Y
  have hfs : tsupport f ⊆ Icc (-Y) Y := tsupport_gapTestC hY
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
    have hvar := integral_windowed_sq_deviation_eq hY.le hf hfs hη hηs hX ξ₀
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

end

end GaloisForLFunctions.VerifiedHeightRungs
