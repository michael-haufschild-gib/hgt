import GaloisForLFunctions.ArithmeticDegenerationTheory.TheLimitingMixedStructure
import GaloisForLFunctions.RHTower.EvenSectorFullPositivity
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# The degeneration exponent is set by the profile

The conductor energies `E_m(c)` of a profile tend to `0` as the overlap grows. The rate is a
property of the profile, not of the arithmetic: it is the decay exponent of its spectral tail.

* **Every admissible profile degenerates faster than cubically**
  (`tendsto_rpow_three_mul_spectralTail`, `tendsto_rpow_three_mul_completedConductorEnergy`): for
  every `C²` profile supported in `[0, 1]`, `x³ T(x) → 0` and hence `c³ E_m(c) → 0` for every
  conductor. Two integrations by parts give `φ̂(r) = −φ''̂(r)/r²`, and Riemann–Lebesgue makes
  `φ''̂(r) → 0`, so `|φ̂(2πt)|² = o(t⁻⁴)`.
* **The tilted spline degenerates at exactly the seventh power**
  (`tiltedUnitSpline_degeneration_exponent`): `c^β E_m(c) → 0` for `β < 7`, `→ J(m) > 0` for `β = 7`,
  and `→ ∞` for `β > 7`.

The exponent `β` sets the weights of the limiting structure (`J_{β+1}`) and the inheritance radius
`1/(β+1)`; the arithmetic sets the coefficients. Every admissible profile has `β ≥ 3` in this weak
sense, which matches the RH regime `c⁴/log N → ∞` common to all `C²` profiles (EHT).
-/

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped Real

namespace GaloisForLFunctions.ArithmeticDegenerationTheory

open RenormalizedArithmeticPotentialTheory.CompletedShell SpacingScaleHarmonicAnalysis

/-- **Riemann–Lebesgue for the paper transform** on the positive real axis. -/
theorem tendsto_paperFT_atTop {g : ℝ → ℂ} :
    Tendsto (fun r : ℝ => Zeta23.paperFT g r) atTop (𝓝 0) := by
  have h := Real.tendsto_integral_exp_smul_cocompact g
  have hw : Tendsto (fun r : ℝ => -(r / (2 * π))) atTop (cocompact ℝ) :=
    (tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_div_const Real.two_pi_pos)).mono_right
      (le_sup_left.trans atBot_atTop_le_cocompact)
  refine (h.comp hw).congr fun r => ?_
  simp only [Function.comp, Zeta23.paperFT]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
  rw [mul_comm]
  congr 1
  congr 1
  push_cast
  field_simp

variable {φ : ℝ → ℝ}

/-- **Every admissible profile has an `o(x⁻³)` spectral tail.** -/
theorem tendsto_rpow_three_mul_spectralTail (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Icc (0 : ℝ) 1 → φ u = 0) :
    Tendsto (fun x => x ^ (3 : ℝ) * spectralTail φ x) atTop (𝓝 0) := by
  set g : ℝ → ℂ := fun u => (φ u : ℂ)
  have hg : ContDiff ℝ 2 g := Complex.ofRealCLM.contDiff.comp hφ
  have hgc : HasCompactSupport g := (hasCompactSupport_profile hsupp).comp_left Complex.ofReal_zero
  have hRL := tendsto_paperFT_atTop (g := deriv (deriv g))
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set ε := Real.sqrt δ
  have hε : 0 < ε := Real.sqrt_pos.mpr hδ
  obtain ⟨R, hR⟩ := Metric.tendsto_atTop.mp hRL ε hε
  refine ⟨max (R / (2 * π)) 1, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := by linarith
  -- pointwise bound on the spectrum beyond `x`
  have hpt : ∀ t ∈ Ioi x, shellSpectrum φ t ≤ ε ^ 2 * (2 * π) ^ (-(4 : ℝ)) * t ^ (-(4 : ℝ)) := by
    intro t ht
    have ht0 : 0 < t := lt_trans hx0 ht
    have hr : R ≤ 2 * π * t := by
      have : R / (2 * π) ≤ t := le_trans (le_max_left _ _) (le_trans hx (le_of_lt ht))
      rwa [div_le_iff₀ Real.two_pi_pos, mul_comm] at this
    have hd := hR (2 * π * t) hr
    rw [dist_zero_right, RHTower.EvenSector.paperFT_deriv_deriv_of_compact hg hgc, norm_mul,
      norm_neg, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at hd
    have hr0 : 0 < 2 * π * t := by positivity
    have hle : ‖Zeta23.paperFT g ((2 * π * t : ℝ) : ℂ)‖ ≤ ε / (2 * π * t) ^ 2 := by
      rw [le_div_iff₀ (by positivity), mul_comm]
      exact hd.le
    change ‖Zeta23.paperFT g ((2 * π * t : ℝ) : ℂ)‖ ^ 2 ≤ _
    calc ‖Zeta23.paperFT g ((2 * π * t : ℝ) : ℂ)‖ ^ 2 ≤ (ε / (2 * π * t) ^ 2) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hle 2
      _ = ε ^ 2 * (2 * π) ^ (-(4 : ℝ)) * t ^ (-(4 : ℝ)) := by
          rw [Real.rpow_neg (by positivity), Real.rpow_neg ht0.le,
            show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast, Real.rpow_natCast]
          field_simp
  have hint : IntegrableOn (fun t : ℝ => ε ^ 2 * (2 * π) ^ (-(4 : ℝ)) * t ^ (-(4 : ℝ))) (Ioi x) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hx0).const_mul _
  have hT : spectralTail φ x ≤ ε ^ 2 * (2 * π) ^ (-(4 : ℝ)) * (x ^ (-(3 : ℝ)) / 3) := by
    unfold spectralTail
    calc ∫ t in Ioi x, shellSpectrum φ t ≤ ∫ t in Ioi x, ε ^ 2 * (2 * π) ^ (-(4 : ℝ)) * t ^ (-(4 : ℝ)) :=
          setIntegral_mono_on (integrable_shellSpectrum hφ hsupp).integrableOn hint measurableSet_Ioi hpt
      _ = ε ^ 2 * (2 * π) ^ (-(4 : ℝ)) * (x ^ (-(3 : ℝ)) / 3) := by
          rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hx0]
          norm_num
  have hT0 := spectralTail_nonneg (φ := φ) x
  have hx3 : 0 < x ^ (3 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hcancel : x ^ (3 : ℝ) * x ^ (-(3 : ℝ)) = 1 := by
    rw [← Real.rpow_add hx0]; simp
  have hεδ : ε ^ 2 = δ := Real.sq_sqrt hδ.le
  have hpi : (2 * π) ^ (-(4 : ℝ)) < 1 := by
    rw [Real.rpow_neg (by positivity)]
    exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by linarith [Real.pi_gt_three]) (by norm_num))
  have hpi0 : 0 ≤ (2 * π) ^ (-(4 : ℝ)) := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg hx3.le hT0)]
  calc x ^ (3 : ℝ) * spectralTail φ x
      ≤ x ^ (3 : ℝ) * (ε ^ 2 * (2 * π) ^ (-(4 : ℝ)) * (x ^ (-(3 : ℝ)) / 3)) :=
        mul_le_mul_of_nonneg_left hT hx3.le
    _ = δ * (2 * π) ^ (-(4 : ℝ)) / 3 := by
        rw [← hεδ]
        field_simp
        rw [← Real.rpow_add hx0]
        norm_num
    _ < δ := by nlinarith

/-- **Every admissible profile degenerates faster than cubically.** -/
theorem tendsto_rpow_three_mul_completedConductorEnergy (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u : ℝ, u ∉ Icc (0 : ℝ) 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2) (m : ℕ) :
    Tendsto (fun c => c ^ (3 : ℝ) * completedConductorEnergy φ c m) atTop (𝓝 0) := by
  have h := tendsto_rpow_mul_completedConductorEnergy hφ hsupp hM (by norm_num : (0 : ℝ) < 3)
    (tendsto_rpow_three_mul_spectralTail hφ hsupp) m
  simpa using h

/-- **The tilted spline degenerates at exactly the seventh power.** -/
theorem tiltedUnitSpline_degeneration_exponent {m : ℕ} (hm : 0 < m) :
    (∀ β : ℝ, β < 7 →
      Tendsto (fun c => c ^ β * completedConductorEnergy tiltedUnitSpline c m) atTop (𝓝 0)) ∧
    Tendsto (fun c => c ^ (7 : ℝ) * completedConductorEnergy tiltedUnitSpline c m) atTop
      (𝓝 (jordanCoefficient m)) ∧
    (∀ β : ℝ, 7 < β →
      Tendsto (fun c => c ^ β * completedConductorEnergy tiltedUnitSpline c m) atTop atTop) := by
  have h7 := tendsto_rpow_seven_mul_completedConductorEnergy_jordan m
  have hJ := jordanCoefficient_pos hm
  refine ⟨fun β hβ => ?_, h7, fun β hβ => ?_⟩
  · have hpow : Tendsto (fun c : ℝ => c ^ (β - 7)) atTop (𝓝 0) := by
      have := tendsto_rpow_neg_atTop (y := 7 - β) (by linarith)
      simpa [neg_sub] using this
    have := hpow.mul h7
    rw [zero_mul] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with c hc
    rw [← mul_assoc, ← Real.rpow_add hc]
    ring_nf
  · have hpow : Tendsto (fun c : ℝ => c ^ (β - 7)) atTop atTop := tendsto_rpow_atTop (by linarith)
    have := hpow.atTop_mul_pos hJ h7
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with c hc
    rw [← mul_assoc, ← Real.rpow_add hc]
    ring_nf

end GaloisForLFunctions.ArithmeticDegenerationTheory
