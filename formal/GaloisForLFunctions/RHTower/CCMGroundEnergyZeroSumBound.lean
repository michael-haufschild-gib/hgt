import GaloisForLFunctions.RHTower.CCMEvenFullGroundZeroSumRH
import GaloisForLFunctions.RHTower.CanonicalProductE1RealLineBounds
import GaloisForLFunctions.RHTower.CompletionLogDerivZeroPairs
import GaloisForLFunctions.RHTower.XiStripEdgeHeightFloorRatioGate
import GaloisForLFunctions.RHTower.CCMRestrictedWeilApertureMonotonicity
import GaloisForLFunctions.RHTower.WeilInsertionAnyWeight

/-!
# Linear inverse-square zero sums of ground states bound the ground energy

Let `u` be an even full ground state of the restricted Weil form at aperture `a`, with
real-rooted transform `F(z) = ∫ conj(u) e^{izt}`, nonzero mass and `‖u‖₁ ≤ Me^{Ka}|∫u|`, and let
`S ≥ 1` bound the inverse-square zero sum `∑_ρ 1/|ρ|²`. If the aperture is large compared with `S`,
the ground energy is bounded by an absolute constant: `|μ_a| ≤ μ_max`.

Since the ground energy is antitone in the aperture and unbounded below under ¬RH, ground states
whose zero sums grow at most linearly in the aperture (`S ≤ a/(200(K+2))`) force the Riemann
hypothesis.

**Proof.** Smear the exact Euler–Lagrange identity at modulation and shift `0` against a Gaussian
of width `σ = 6S`, so that `G = F/F(0)` is tested on `e^{-σz²} b̂(-z)`.
* Zero side: `|G(γ) e^{-σγ²}| ≤ e^{-4S(Re γ)² + 8S(Im γ)²} ≤ e^{-S}`, because `(Re γ)² > 331/4`.
* Line side: `Re ∫ G b̂ e^{-σs²}` is at least `b̂(0)√(π/S)/4`. This uses
  - `Re b̂(-s) ≥ b̂(0)(1 - s²/2)`;
  - `|G(s) - 1| ≤ e^{2Ss²} - 1` on the real line;
  - Gaussian integrals.
* Error: the Gaussian tail beyond `R = a - 2` is at most `2e^{-R²/16σ}`, against the Paley–Wiener
  growth `Me^{(K+1)a}`.
-/

open Complex MeasureTheory Set Filter Topology
open GaloisForLFunctions.EntireZeroDivisor RHTower.OrderOneHadamard

namespace RHTower

noncomputable section

/-! ## A nonnegative bump test -/

/-- The standard smooth bump of radii `1/2` and `1` at the origin. -/
def posBump : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩

/-- The nonnegative bump as a smooth compact test on `[-1, 1]`. -/
def posBumpTest : SuzukiSmoothCompactTest 1 where
  toFun := fun x => ((posBump x : ℝ) : ℂ)
  smooth := Complex.ofRealCLM.contDiff.comp posBump.contDiff
  support_subset := by
    intro x hx
    have hφ : posBump x ≠ 0 := by
      intro h0
      exact hx (by simp [h0])
    have hmem : x ∈ Metric.ball (0 : ℝ) 1 := by
      have := posBump.support_eq ▸ (Function.mem_support.mpr hφ)
      simpa [posBump] using this
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hmem
    exact ⟨by linarith [neg_abs_le x], by linarith [le_abs_self x]⟩

/-- The mass `∫ φ > 0` of the bump. -/
def posBumpMass : ℝ := ∫ x : ℝ, posBump x

theorem posBumpMass_pos : 0 < posBumpMass := posBump.integral_pos

theorem posBump_eq_zero_of_one_lt_abs {x : ℝ} (hx : 1 < |x|) : posBump x = 0 := by
  by_contra h
  have := posBump.support_eq ▸ (Function.mem_support.mpr h)
  rw [Metric.mem_ball, Real.dist_eq, sub_zero] at this
  simp only [posBump] at this
  linarith

theorem integrable_posBump : Integrable fun x : ℝ => posBump x :=
  posBump.continuous.integrable_of_hasCompactSupport posBump.hasCompactSupport

/-- `|b̂(z)| ≤ b̂(0) e^{|Im z|}`. -/
theorem norm_suzukiSmoothFourier_posBumpTest_le (z : ℂ) :
    ‖suzukiSmoothFourier posBumpTest z‖ ≤ posBumpMass * Real.exp |z.im| := by
  rw [suzukiSmoothFourier, posBumpMass, ← integral_mul_const]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Eventually.of_forall fun x => norm_nonneg _) (integrable_posBump.mul_const _)
    (Eventually.of_forall fun x => ?_))
  show ‖((posBump x : ℝ) : ℂ) * cexp (I * z * (x : ℂ))‖ ≤ posBump x * Real.exp |z.im|
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (posBump.nonneg' x),
    Complex.norm_exp]
  by_cases hx : 1 < |x|
  · rw [posBump_eq_zero_of_one_lt_abs hx, zero_mul, zero_mul]
  · push Not at hx
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (posBump.nonneg' x)
    have hre : (I * z * (x : ℂ)).re = -(z.im * x) := by simp [mul_re, mul_im]
    rw [hre]
    calc -(z.im * x) ≤ |z.im * x| := neg_le_abs _
      _ = |z.im| * |x| := abs_mul _ _
      _ ≤ |z.im| * 1 := by gcongr
      _ = |z.im| := mul_one _

/-- On the real line, `Re b̂(s) ≥ b̂(0)(1 - s²/2)`. -/
theorem re_suzukiSmoothFourier_posBumpTest_ge (s : ℝ) :
    posBumpMass * (1 - s ^ 2 / 2) ≤ (suzukiSmoothFourier posBumpTest (s : ℂ)).re := by
  have hint := posBumpTest.integrable_fourierIntegrand (s : ℂ)
  have hre_int := integral_re hint
  simp only [RCLike.re_to_complex] at hre_int
  rw [suzukiSmoothFourier, ← hre_int, posBumpMass, ← integral_mul_const]
  refine integral_mono (integrable_posBump.mul_const _) hint.re (fun x => ?_)
  show posBump x * (1 - s ^ 2 / 2) ≤ (((posBump x : ℝ) : ℂ) * cexp (I * (s : ℂ) * (x : ℂ))).re
  have hre : (((posBump x : ℝ) : ℂ) * cexp (I * (s : ℂ) * (x : ℂ))).re =
      posBump x * Real.cos (s * x) := by
    have h1 : I * (s : ℂ) * (x : ℂ) = ((s * x : ℝ) : ℂ) * I := by push_cast; ring
    rw [h1, re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  rw [hre]
  by_cases hx : 1 < |x|
  · rw [posBump_eq_zero_of_one_lt_abs hx, zero_mul, zero_mul]
  · push Not at hx
    refine mul_le_mul_of_nonneg_left ?_ (posBump.nonneg' x)
    have hc := Real.one_sub_sq_div_two_le_cos (x := s * x)
    have hx2 : x ^ 2 ≤ 1 := by nlinarith [sq_abs x, abs_nonneg x]
    have : (s * x) ^ 2 ≤ s ^ 2 := by rw [mul_pow]; nlinarith [sq_nonneg s]
    linarith

/-! ## The Gaussian tail -/

theorem norm_gaussShiftConst {σ : ℝ} (hσ : 0 < σ) :
    ‖gaussShiftConst σ‖ = Real.sqrt (4 * Real.pi * σ) := by
  have hbase : (Real.pi : ℂ) / -(-(1 / (4 * (σ : ℂ)))) = ((4 * Real.pi * σ : ℝ) : ℂ) := by
    have hσ' : (σ : ℂ) ≠ 0 := ofReal_ne_zero.mpr hσ.ne'
    push_cast
    field_simp
  rw [gaussShiftConst, hbase, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity),
    Real.sqrt_eq_rpow]
  congr 1
  norm_num

/-- **The Gaussian tail bound.** For `R ≥ 8σ`, `τ_σ(R) ≤ 2 e^{-R²/16σ}`. -/
theorem gaussShiftTail_zero_le {σ R : ℝ} (hσ : 0 < σ) (hR : 8 * σ ≤ R) :
    gaussShiftTail σ 0 R ≤ 2 * Real.exp (-(R ^ 2 / (16 * σ))) := by
  have hP : 0 < Real.sqrt (4 * Real.pi * σ) := Real.sqrt_pos.mpr (by positivity)
  have hb : (0 : ℝ) < 1 / (16 * σ) := by positivity
  have hgint : Integrable fun v : ℝ => Real.exp (-(1 / (16 * σ)) * v ^ 2) :=
    integrable_exp_neg_mul_sq hb
  have hbound : ∀ v ∈ (Icc (-R) R)ᶜ,
      ‖gaussShiftWeight σ 0 v‖ * Real.exp ((1 / 2) * |v|) ≤
        (Real.sqrt (4 * Real.pi * σ))⁻¹ * Real.exp (-(R ^ 2 / (16 * σ))) *
          Real.exp (-(1 / (16 * σ)) * v ^ 2) := by
    intro v hv
    have hvR : R ≤ |v| := by
      by_contra hlt
      push Not at hlt
      exact hv (abs_le.mp hlt.le)
    rw [norm_gaussShiftWeight, norm_gaussShiftConst hσ, sub_zero]
    have hv2 : v ^ 2 = |v| ^ 2 := (sq_abs v).symm
    have h8 : 0 < 8 * σ := by positivity
    have hR0 : 0 ≤ R := le_trans h8.le hR
    have hvv : R ^ 2 ≤ |v| ^ 2 := by nlinarith [abs_nonneg v]
    have hσ16 : 0 < 16 * σ := by positivity
    have key : (1 / 2) * |v| ≤ |v| ^ 2 / (16 * σ) := by
      rw [le_div_iff₀ hσ16]
      nlinarith [abs_nonneg v]
    have e1 : -(v ^ 2) / (4 * σ) = -(4 * (|v| ^ 2 / (16 * σ))) := by
      rw [hv2]; field_simp; ring
    have e2 : -(1 / (16 * σ)) * v ^ 2 = -(|v| ^ 2 / (16 * σ)) := by rw [hv2]; ring
    have e3 : R ^ 2 / (16 * σ) ≤ |v| ^ 2 / (16 * σ) := by gcongr
    have hexp : Real.exp (-(v ^ 2) / (4 * σ)) * Real.exp ((1 / 2) * |v|) ≤
        Real.exp (-(R ^ 2 / (16 * σ))) * Real.exp (-(1 / (16 * σ)) * v ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [e1, e2]
      nlinarith [div_nonneg (sq_nonneg |v|) hσ16.le]
    calc (Real.sqrt (4 * Real.pi * σ))⁻¹ * Real.exp (-(v ^ 2) / (4 * σ)) *
          Real.exp ((1 / 2) * |v|)
        = (Real.sqrt (4 * Real.pi * σ))⁻¹ *
          (Real.exp (-(v ^ 2) / (4 * σ)) * Real.exp ((1 / 2) * |v|)) := by ring
      _ ≤ (Real.sqrt (4 * Real.pi * σ))⁻¹ *
          (Real.exp (-(R ^ 2 / (16 * σ))) * Real.exp (-(1 / (16 * σ)) * v ^ 2)) := by
          gcongr
      _ = _ := by ring
  calc gaussShiftTail σ 0 R
      ≤ ∫ v in (Icc (-R) R)ᶜ, (Real.sqrt (4 * Real.pi * σ))⁻¹ *
          Real.exp (-(R ^ 2 / (16 * σ))) * Real.exp (-(1 / (16 * σ)) * v ^ 2) := by
        rw [gaussShiftTail]
        refine setIntegral_mono_on ?_ (hgint.const_mul _).integrableOn
          measurableSet_Icc.compl hbound
        exact (integrable_norm_gaussShiftWeight_mul_exp hσ 0 (1 / 2)).integrableOn
    _ ≤ ∫ v : ℝ, (Real.sqrt (4 * Real.pi * σ))⁻¹ *
          Real.exp (-(R ^ 2 / (16 * σ))) * Real.exp (-(1 / (16 * σ)) * v ^ 2) :=
        setIntegral_le_integral (hgint.const_mul _) (ae_of_all _ fun v => by positivity)
    _ = (Real.sqrt (4 * Real.pi * σ))⁻¹ * Real.exp (-(R ^ 2 / (16 * σ))) *
          Real.sqrt (Real.pi / (1 / (16 * σ))) := by
        rw [integral_const_mul, integral_gaussian]
    _ = 2 * Real.exp (-(R ^ 2 / (16 * σ))) := by
        have h16 : Real.pi / (1 / (16 * σ)) = 4 * (4 * Real.pi * σ) := by
          rw [div_div_eq_mul_div, div_one]; ring
        have hs4 : Real.sqrt 4 = 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        rw [h16, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hs4]
        field_simp

/-! ## The normalized transform of a real-rooted even entire function -/

section NormalizedTransform

variable {F : ℂ → ℂ} {C S : ℝ}

/-- The Hadamard bounds for an even entire function with real zeros: with `P` its genus-one
product (`F = F(0) P`), `S ≥ ∑ 1/|ρ|²` and `S ≥ 1`:
* `|P(z)| ≤ e^{2S|z|²}`,
* `|P(s) - 1| ≤ e^{2Ss²} - 1` on the real line. -/
theorem norm_hadamardProduct_le_of_zeroSum (hC : 0 ≤ C) (hF : Differentiable ℂ F)
    (hF0 : F 0 ≠ 0)
    (hbound : ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    (hzero : ∑' q : ZeroCopy F, 1 / ‖zeroCopyPoint F q‖ ^ (2 : ℕ) ≤ S) (z : ℂ) :
    ‖hadamardProduct F z‖ ≤ Real.exp (2 * S * ‖z‖ ^ 2) := by
  have hAn : AnalyticOnNhd ℂ F Set.univ := fun w _ => hF.analyticAt w
  have hsum := summable_inv_sq_zeroCopyPoint hC hAn hF0 hbound
  have hne := zeroCopyPoint_ne_zero hAn hF0
  refine (canonicalProductE1Indexed_norm_le_exp_min (zeroCopyPoint F) hne hsum z).trans ?_
  apply Real.exp_le_exp.mpr
  have hdom : Summable fun q : ZeroCopy F =>
      2 * ‖z‖ ^ (2 : ℕ) * (1 / ‖zeroCopyPoint F q‖ ^ (2 : ℕ)) := hsum.mul_left _
  have hle : ∀ q : ZeroCopy F, min (2 * ‖z‖ / ‖zeroCopyPoint F q‖)
      (2 * ‖z‖ ^ (2 : ℕ) / ‖zeroCopyPoint F q‖ ^ (2 : ℕ)) ≤
        2 * ‖z‖ ^ (2 : ℕ) * (1 / ‖zeroCopyPoint F q‖ ^ (2 : ℕ)) := by
    intro q
    refine (min_le_right _ _).trans (le_of_eq ?_)
    ring
  have hnn : ∀ q : ZeroCopy F, 0 ≤ min (2 * ‖z‖ / ‖zeroCopyPoint F q‖)
      (2 * ‖z‖ ^ (2 : ℕ) / ‖zeroCopyPoint F q‖ ^ (2 : ℕ)) :=
    fun q => le_min (by positivity) (by positivity)
  calc ∑' q : ZeroCopy F, min (2 * ‖z‖ / ‖zeroCopyPoint F q‖)
        (2 * ‖z‖ ^ (2 : ℕ) / ‖zeroCopyPoint F q‖ ^ (2 : ℕ))
      ≤ ∑' q : ZeroCopy F, 2 * ‖z‖ ^ (2 : ℕ) * (1 / ‖zeroCopyPoint F q‖ ^ (2 : ℕ)) :=
        Summable.tsum_le_tsum hle (hdom.of_nonneg_of_le hnn hle) hdom
    _ = 2 * ‖z‖ ^ 2 * ∑' q : ZeroCopy F, 1 / ‖zeroCopyPoint F q‖ ^ (2 : ℕ) := tsum_mul_left
    _ ≤ 2 * ‖z‖ ^ 2 * S := by gcongr
    _ = 2 * S * ‖z‖ ^ 2 := by ring

theorem norm_hadamardProduct_ofReal_sub_one_le (hC : 0 ≤ C) (hF : Differentiable ℂ F)
    (hF0 : F 0 ≠ 0)
    (hbound : ∀ z : ℂ, ‖F z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    (hrealF : ∀ q : ZeroCopy F, (zeroCopyPoint F q).im = 0) (hS : 1 ≤ S)
    (hzero : ∑' q : ZeroCopy F, 1 / ‖zeroCopyPoint F q‖ ^ (2 : ℕ) ≤ S) (s : ℝ) :
    ‖hadamardProduct F (s : ℂ) - 1‖ ≤ Real.exp (2 * S * s ^ 2) - 1 := by
  have hAn : AnalyticOnNhd ℂ F Set.univ := fun w _ => hF.analyticAt w
  have hsum := summable_inv_sq_zeroCopyPoint hC hAn hF0 hbound
  have hne := zeroCopyPoint_ne_zero hAn hF0
  set T : ℝ := ∑' q : ZeroCopy F, 1 / ‖zeroCopyPoint F q‖ ^ (2 : ℕ) with hT
  have hT0 : 0 ≤ T := tsum_nonneg fun q => by positivity
  by_cases hsmall : S * s ^ 2 ≤ 1
  · -- near the origin
    have hz : ∀ q : ZeroCopy F, ‖(s : ℂ)‖ ≤ ‖zeroCopyPoint F q‖ := by
      intro q
      have hq : 1 / ‖zeroCopyPoint F q‖ ^ (2 : ℕ) ≤ S :=
        le_trans (hsum.le_tsum q (fun _ _ => by positivity)) hzero
      have hpos : 0 < ‖zeroCopyPoint F q‖ := norm_pos_iff.mpr (hne q)
      rw [Complex.norm_real, Real.norm_eq_abs]
      have h1 : 1 ≤ S * ‖zeroCopyPoint F q‖ ^ 2 := by
        rw [div_le_iff₀ (by positivity)] at hq
        linarith
      have h2 : s ^ 2 ≤ ‖zeroCopyPoint F q‖ ^ 2 := by
        have hS0 : 0 < S := by linarith
        nlinarith
      nlinarith [abs_nonneg s, sq_abs s, norm_nonneg (zeroCopyPoint F q)]
    have h := norm_canonicalProductE1Indexed_sub_one_le (zeroCopyPoint F) hne hsum hz
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
    refine h.trans ?_
    have : s ^ 2 * T ≤ 2 * S * s ^ 2 := by nlinarith [sq_nonneg s]
    linarith [Real.exp_le_exp.mpr this]
  · -- away from the origin: the real-line bound
    push Not at hsmall
    have h := norm_canonicalProductE1Indexed_ofReal_le (zeroCopyPoint F) hne hsum hrealF s
    have h1 : ‖hadamardProduct F (s : ℂ) - 1‖ ≤ Real.exp (S * s ^ 2 / 2) + 1 := by
      refine (norm_sub_le _ _).trans ?_
      rw [norm_one]
      have : s ^ 2 / 2 * T ≤ S * s ^ 2 / 2 := by nlinarith [sq_nonneg s]
      have h' : ‖hadamardProduct F (s : ℂ)‖ ≤ Real.exp (S * s ^ 2 / 2) :=
        h.trans (Real.exp_le_exp.mpr this)
      linarith
    refine h1.trans ?_
    set x : ℝ := S * s ^ 2 with hx
    have hx1 : 1 < x := hsmall
    have he : Real.exp (2 * S * s ^ 2) = Real.exp (x / 2) * Real.exp (3 * x / 2) := by
      rw [← Real.exp_add, hx]; congr 1; ring
    have h32 : 3 * x / 2 + 1 ≤ Real.exp (3 * x / 2) := Real.add_one_le_exp _
    have hx2 : x / 2 + 1 ≤ Real.exp (x / 2) := Real.add_one_le_exp _
    rw [he]
    nlinarith

end NormalizedTransform

/-! ## The line integral is large -/

theorem self_le_exp_half_of_nonneg (y : ℝ) (hy : 0 ≤ y) : y ≤ Real.exp (y / 2) := by
  have h1 : 1 + y / 4 ≤ Real.exp (y / 4) := by linarith [Real.add_one_le_exp (y / 4)]
  have h2 : Real.exp (y / 2) = Real.exp (y / 4) * Real.exp (y / 4) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [h2]
  have h3 : 0 ≤ 1 + y / 4 := by linarith
  nlinarith [sq_nonneg (y / 4 - 1)]

theorem sq_mul_gaussian_le_inv_mul_half {σ : ℝ} (hσ : 0 < σ) (s : ℝ) :
    s ^ 2 * Real.exp (-σ * s ^ 2) ≤ (1 / σ) * Real.exp (-(σ / 2) * s ^ 2) := by
  have h := self_le_exp_half_of_nonneg (σ * s ^ 2) (by positivity)
  have he : Real.exp (-(σ / 2) * s ^ 2) = Real.exp (σ * s ^ 2 / 2) * Real.exp (-σ * s ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [he, ← mul_assoc]
  have hpos := Real.exp_pos (-σ * s ^ 2)
  have : s ^ 2 ≤ 1 / σ * Real.exp (σ * s ^ 2 / 2) := by
    rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hσ]
    linarith
  exact mul_le_mul_of_nonneg_right this hpos.le

theorem sqrt_six_lt : Real.sqrt 6 < 49 / 20 := by
  rw [Real.sqrt_lt' (by norm_num)]
  norm_num

theorem lt_sqrt_three : 17 / 10 < Real.sqrt 3 := by
  rw [Real.lt_sqrt (by norm_num)]
  norm_num

/-- **The line integral is large.** If `G` is continuous on the real line with
`|G(s) - 1| ≤ e^{2Ss²} - 1` and `S ≥ 1`, then the smeared line integral at width `σ = 6S` has real
part at least `b̂(0) √(π/S) / 4`. -/
theorem re_integral_gaussBump_ge {G : ℂ → ℂ} {S : ℝ} (hS : 1 ≤ S)
    (hGc : Continuous fun s : ℝ => G (s : ℂ))
    (hG1 : ∀ s : ℝ, ‖G (s : ℂ) - 1‖ ≤ Real.exp (2 * S * s ^ 2) - 1) :
    posBumpMass * Real.sqrt (Real.pi / S) / 4 ≤
      (∫ s : ℝ, (G (s : ℂ) * cexp (-((6 * S : ℝ) : ℂ) * (s : ℂ) ^ 2)) *
        (suzukiSmoothFourier posBumpTest (((0 : ℝ) : ℂ) - (s : ℂ)) *
          cexp (-(I * (s : ℂ)) * ((0 : ℝ) : ℂ)))).re := by
  set σ : ℝ := 6 * S with hσdef
  have hS0 : 0 < S := by linarith
  have hσ : 0 < σ := by rw [hσdef]; linarith
  set m : ℝ := posBumpMass with hm
  have hm0 : 0 < m := posBumpMass_pos
  set g : ℝ → ℂ := fun s => (G (s : ℂ) * cexp (-((σ : ℝ) : ℂ) * (s : ℂ) ^ 2)) *
      (suzukiSmoothFourier posBumpTest (((0 : ℝ) : ℂ) - (s : ℂ)) *
        cexp (-(I * (s : ℂ)) * ((0 : ℝ) : ℂ))) with hg
  have hcexp : ∀ s : ℝ,
      cexp (-((σ : ℝ) : ℂ) * (s : ℂ) ^ 2) = ((Real.exp (-σ * s ^ 2) : ℝ) : ℂ) := by
    intro s; rw [Complex.ofReal_exp]; push_cast; ring_nf
  have hbneg : ∀ s : ℝ, ((0 : ℝ) : ℂ) - (s : ℂ) = ((-s : ℝ) : ℂ) := by intro s; push_cast; ring
  have hgs : ∀ s : ℝ, g s = ((Real.exp (-σ * s ^ 2) : ℝ) : ℂ) *
      (G (s : ℂ) * suzukiSmoothFourier posBumpTest ((-s : ℝ) : ℂ)) := by
    intro s
    simp only [hg]
    rw [hcexp, hbneg]
    simp only [ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
    ring
  have hbnorm : ∀ s : ℝ, ‖suzukiSmoothFourier posBumpTest ((-s : ℝ) : ℂ)‖ ≤ m := by
    intro s
    have := norm_suzukiSmoothFourier_posBumpTest_le ((-s : ℝ) : ℂ)
    simpa [hm] using this
  have hGnorm : ∀ s : ℝ, ‖G (s : ℂ)‖ ≤ Real.exp (2 * S * s ^ 2) := by
    intro s
    have h := norm_sub_le (G (s : ℂ) - 1) (-1)
    simp only [sub_neg_eq_add, sub_add_cancel, norm_neg, norm_one] at h
    linarith [hG1 s]
  -- integrability
  have hbc : Continuous fun s : ℝ => suzukiSmoothFourier posBumpTest ((-s : ℝ) : ℂ) :=
    (differentiable_suzukiSmoothFourier zero_le_one posBumpTest).continuous.comp (by fun_prop)
  have hgc : Continuous g := by
    have : g = fun s => ((Real.exp (-σ * s ^ 2) : ℝ) : ℂ) *
        (G (s : ℂ) * suzukiSmoothFourier posBumpTest ((-s : ℝ) : ℂ)) := funext hgs
    rw [this]
    exact (by fun_prop : Continuous fun s : ℝ => ((Real.exp (-σ * s ^ 2) : ℝ) : ℂ)).mul
      (hGc.mul hbc)
  have hgint : Integrable g := by
    refine ((integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 4 * S)).const_mul m).mono'
      hgc.aestronglyMeasurable (ae_of_all _ fun s => ?_)
    rw [hgs, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-σ * s ^ 2) * (‖G (s : ℂ)‖ *
          ‖suzukiSmoothFourier posBumpTest ((-s : ℝ) : ℂ)‖)
        ≤ Real.exp (-σ * s ^ 2) * (Real.exp (2 * S * s ^ 2) * m) := by
          gcongr
          · exact hGnorm s
          · exact hbnorm s
      _ = m * Real.exp (-(4 * S) * s ^ 2) := by
          rw [show m * Real.exp (-(4 * S) * s ^ 2) =
              m * (Real.exp (2 * S * s ^ 2) * Real.exp (-σ * s ^ 2)) by
            rw [← Real.exp_add]; congr 2; rw [hσdef]; ring]
          ring
  -- pointwise lower bound
  set lower : ℝ → ℝ := fun s => m * (2 * Real.exp (-σ * s ^ 2) -
      (1 / (2 * σ)) * Real.exp (-(σ / 2) * s ^ 2) - Real.exp (-(4 * S) * s ^ 2)) with hlower
  have hpt : ∀ s : ℝ, lower s ≤ (g s).re := by
    intro s
    rw [hgs, re_ofReal_mul]
    set b := suzukiSmoothFourier posBumpTest ((-s : ℝ) : ℂ) with hbdef
    have hbre : m * (1 - s ^ 2 / 2) ≤ b.re := by
      have := re_suzukiSmoothFourier_posBumpTest_ge (-s)
      rw [neg_sq] at this
      simpa [hm, hbdef] using this
    have hdecomp : (G (s : ℂ) * b).re = b.re + ((G (s : ℂ) - 1) * b).re := by
      rw [← Complex.add_re]; congr 1; ring
    have hcross : -(‖G (s : ℂ) - 1‖ * ‖b‖) ≤ ((G (s : ℂ) - 1) * b).re := by
      have := Complex.abs_re_le_norm ((G (s : ℂ) - 1) * b)
      rw [norm_mul] at this
      linarith [neg_abs_le ((G (s : ℂ) - 1) * b).re]
    have hGb : (G (s : ℂ) * b).re ≥ m * (1 - s ^ 2 / 2) - (Real.exp (2 * S * s ^ 2) - 1) * m := by
      rw [hdecomp]
      have hone : 1 ≤ Real.exp (2 * S * s ^ 2) := Real.one_le_exp (by positivity)
      have h1 : ‖G (s : ℂ) - 1‖ * ‖b‖ ≤ (Real.exp (2 * S * s ^ 2) - 1) * m :=
        mul_le_mul (hG1 s) (hbnorm s) (norm_nonneg _) (by linarith)
      linarith
    have hsq := sq_mul_gaussian_le_inv_mul_half hσ s
    have hexp4 :
        Real.exp (2 * S * s ^ 2) * Real.exp (-σ * s ^ 2) = Real.exp (-(4 * S) * s ^ 2) := by
      rw [← Real.exp_add]; congr 1; rw [hσdef]; ring
    have hE := Real.exp_pos (-σ * s ^ 2)
    calc lower s = m * (2 * Real.exp (-σ * s ^ 2) -
          (1 / (2 * σ)) * Real.exp (-(σ / 2) * s ^ 2) - Real.exp (-(4 * S) * s ^ 2)) := rfl
      _ ≤ m * (2 * Real.exp (-σ * s ^ 2) - (s ^ 2 / 2) * Real.exp (-σ * s ^ 2) -
          Real.exp (2 * S * s ^ 2) * Real.exp (-σ * s ^ 2)) := by
          rw [hexp4]
          have : (s ^ 2 / 2) * Real.exp (-σ * s ^ 2) ≤
              (1 / (2 * σ)) * Real.exp (-(σ / 2) * s ^ 2) := by
            have h2 : (1 / (2 * σ)) * Real.exp (-(σ / 2) * s ^ 2) =
                (1 / 2) * ((1 / σ) * Real.exp (-(σ / 2) * s ^ 2)) := by field_simp
            rw [h2]
            nlinarith
          nlinarith
      _ = Real.exp (-σ * s ^ 2) * (m * (1 - s ^ 2 / 2) - (Real.exp (2 * S * s ^ 2) - 1) * m) := by
          ring
      _ ≤ Real.exp (-σ * s ^ 2) * (G (s : ℂ) * b).re :=
          mul_le_mul_of_nonneg_left hGb hE.le
  -- integrate the lower bound
  have hi1 : Integrable fun s : ℝ => Real.exp (-σ * s ^ 2) := integrable_exp_neg_mul_sq hσ
  have hi2 : Integrable fun s : ℝ => Real.exp (-(σ / 2) * s ^ 2) :=
    integrable_exp_neg_mul_sq (by positivity)
  have hi3 : Integrable fun s : ℝ => Real.exp (-(4 * S) * s ^ 2) :=
    integrable_exp_neg_mul_sq (by positivity)
  have hlint : Integrable lower :=
    (((hi1.const_mul 2).sub (hi2.const_mul (1 / (2 * σ)))).sub hi3).const_mul m
  have hA : Integrable (fun s : ℝ => 2 * Real.exp (-σ * s ^ 2) -
      1 / (2 * σ) * Real.exp (-(σ / 2) * s ^ 2)) := (hi1.const_mul 2).sub (hi2.const_mul _)
  have hint_lower : ∫ s, lower s = m * (2 * Real.sqrt (Real.pi / σ) -
      (1 / (2 * σ)) * Real.sqrt (Real.pi / (σ / 2)) - Real.sqrt (Real.pi / (4 * S))) := by
    simp only [hlower]
    rw [integral_const_mul, integral_sub hA hi3,
      integral_sub (hi1.const_mul 2) (hi2.const_mul _), integral_const_mul, integral_const_mul,
      integral_gaussian, integral_gaussian, integral_gaussian]
  have hre : (∫ s, g s).re = ∫ s, (g s).re := by
    have := integral_re hgint
    simp only [RCLike.re_to_complex] at this
    exact this.symm
  have hmono : ∫ s, lower s ≤ ∫ s, (g s).re := integral_mono hlint hgint.re hpt
  show m * Real.sqrt (Real.pi / S) / 4 ≤ (∫ s, g s).re
  rw [hre]
  refine le_trans ?_ hmono
  rw [hint_lower]
  -- numerics
  set q : ℝ := Real.sqrt (Real.pi / S) with hq
  have hq0 : 0 < q := Real.sqrt_pos.mpr (by positivity)
  have h6 : Real.sqrt (Real.pi / σ) = q / Real.sqrt 6 := by
    rw [hq, hσdef, (show Real.pi / (6 * S) = (Real.pi / S) / 6 by field_simp),
      Real.sqrt_div' _ (by norm_num)]
  have h3 : Real.sqrt (Real.pi / (σ / 2)) = q / Real.sqrt 3 := by
    rw [hq, hσdef, (show Real.pi / (6 * S / 2) = (Real.pi / S) / 3 by field_simp; ring),
      Real.sqrt_div' _ (by norm_num)]
  have h4 : Real.sqrt (Real.pi / (4 * S)) = q / 2 := by
    have hs4 : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [hq, (show Real.pi / (4 * S) = (Real.pi / S) / 4 by field_simp),
      Real.sqrt_div' _ (by norm_num), hs4]
  rw [h6, h3, h4]
  have hs6 := sqrt_six_lt
  have hs3 := lt_sqrt_three
  have hs6p : 0 < Real.sqrt 6 := by positivity
  have hs3p : 0 < Real.sqrt 3 := by positivity
  have hA : 40 / 49 ≤ 2 / Real.sqrt 6 := by
    rw [le_div_iff₀ hs6p]; nlinarith
  have hB : 1 / (2 * σ) / Real.sqrt 3 ≤ 1 / 20 := by
    rw [div_le_iff₀ hs3p, div_le_iff₀ (by positivity)]
    rw [hσdef]
    nlinarith
  have key : 1 / 4 ≤ 2 / Real.sqrt 6 - 1 / (2 * σ) / Real.sqrt 3 - 1 / 2 := by linarith
  have expand : 2 * (q / Real.sqrt 6) - 1 / (2 * σ) * (q / Real.sqrt 3) - q / 2 =
      q * (2 / Real.sqrt 6 - 1 / (2 * σ) / Real.sqrt 3 - 1 / 2) := by ring
  rw [expand]
  have : m * q / 4 = m * (q * (1 / 4)) := by ring
  rw [this]
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left key hq0.le) hm0.le

/-! ## The zero side is exponentially small -/

private theorem abs_im_xiSpectralPoint_le' (q : XiZeroCopy) :
    |(xiSpectralPoint q).im| ≤ 1 / 2 := by
  have := xiSpectralPoint_im_mem_openHalf q
  rw [abs_le]; constructor <;> linarith [this.1, this.2]


/-- **The zero side.** If `|G(z)| ≤ e^{2S|z|²}` and `S ≥ 1`, the smeared zero sum at width `6S` is
at most `e^{-S}` times a constant. The proof uses `(Re γ)² > 331/4` for every centered Xi zero. -/
theorem norm_zeroSide_gaussBump_le {G : ℂ → ℂ} {S : ℝ} (hS : 1 ≤ S)
    (hG : ∀ z : ℂ, ‖G z‖ ≤ Real.exp (2 * S * ‖z‖ ^ 2)) :
    ‖∑' q : XiZeroCopy, (G (xiSpectralPoint q) *
        cexp (-((6 * S : ℝ) : ℂ) * xiSpectralPoint q ^ 2)) *
      (suzukiSmoothFourier posBumpTest (((0 : ℝ) : ℂ) - xiSpectralPoint q) *
        cexp (-(I * xiSpectralPoint q) * ((0 : ℝ) : ℂ)))‖ ≤
      Real.exp (-S) * (2 * suzukiTestDecayConst posBumpTest 1 *
        ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
  set K : ℝ := suzukiTestDecayConst posBumpTest 1 with hK
  have hK0 : 0 ≤ K := suzukiTestDecayConst_nonneg _ _
  rw [← tsum_mul_left, ← tsum_mul_left]
  refine tsum_of_norm_bounded ((xiSpectralPoint_inv_sq_summable.mul_left (2 * K)).mul_left
    (Real.exp (-S))).hasSum fun q => ?_
  set γ := xiSpectralPoint q with hγ
  have hy : |γ.im| ≤ 1 / 2 := abs_im_xiSpectralPoint_le' q
  have hx : (331 / 4 : ℝ) < γ.re ^ 2 := xiSpectralPoint_re_sq_gt_floor q
  have hγ0 : γ ≠ 0 := xiSpectralPoint_ne_zero q
  have hpos : 0 < ‖γ‖ ^ 2 := by positivity
  have hb := norm_suzukiSmoothFourier_sub_le posBumpTest zero_le_one 0 (z := γ)
    (hy.trans (by norm_num))
  have hexp0 : cexp (-(I * γ) * ((0 : ℝ) : ℂ)) = 1 := by simp
  rw [hexp0, mul_one, norm_mul, norm_mul, norm_cexp_neg_ofReal_mul_sq]
  have hnormsq : ‖γ‖ ^ 2 = γ.re ^ 2 + γ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hy2 : γ.im ^ 2 ≤ 1 / 4 := by nlinarith [sq_abs γ.im, abs_nonneg γ.im]
  have hexpo : Real.exp (2 * S * ‖γ‖ ^ 2) * Real.exp (-(6 * S * (γ.re ^ 2 - γ.im ^ 2))) ≤
      Real.exp (-S) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    rw [hnormsq]
    nlinarith
  have hbinv : 2 * (1 + (0 : ℝ) ^ 2) * K / (1 + ‖γ‖ ^ 2) ≤ 2 * K * (1 / ‖γ‖ ^ (2 : ℕ)) := by
    rw [div_eq_mul_one_div]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, mul_one]
    gcongr
    linarith
  calc ‖G γ‖ * Real.exp (-(6 * S * (γ.re ^ 2 - γ.im ^ 2))) *
        ‖suzukiSmoothFourier posBumpTest (((0 : ℝ) : ℂ) - γ)‖
      ≤ Real.exp (2 * S * ‖γ‖ ^ 2) * Real.exp (-(6 * S * (γ.re ^ 2 - γ.im ^ 2))) *
          (2 * K * (1 / ‖γ‖ ^ (2 : ℕ))) := by
        gcongr
        · exact hG γ
        · exact hb.trans hbinv
    _ ≤ Real.exp (-S) * (2 * K * (1 / ‖γ‖ ^ (2 : ℕ))) := by
        gcongr

/-! ## The ground energy is bounded by the zero sum -/

section GroundEnergy

open GaloisForLFunctions.HTGeometry
open RHTower.CCMFullGroundEigen RHTower.CCMRealRootedGround RHTower.CCMFullRealRootedGround

/-- Real-rooted Fourier–Laplace transforms have real zero copies. -/
theorem im_zeroCopyPoint_conjTransform_eq_zero {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℂ}
    (hf : Integrable f) (hsupp : FourierZeroFlip.SupportedIn a f)
    (hreal : ∀ w : ℂ, FourierLaplaceDivision.unitaryLaplace f w = 0 → w.im = 0)
    (q : ZeroCopy (conjTransform f)) : (zeroCopyPoint (conjTransform f) q).im = 0 := by
  have hdiff : Differentiable ℂ (conjTransform f) := differentiable_conjTransform ha hf hsupp
  have hAn : AnalyticOnNhd ℂ (conjTransform f) Set.univ := fun w _ => hdiff.analyticAt w
  have hz := RHTower.CompletionZeroPairs.apply_zeroCopyPoint hAn q
  set z := zeroCopyPoint (conjTransform f) q
  rw [conjTransform_eq_conj_unitaryLaplace, map_eq_zero] at hz
  have him := hreal _ hz
  have : ((starRingEnd ℂ) z / (2 * Real.pi : ℂ)).im = -z.im / (2 * Real.pi) := by
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring,
      Complex.div_ofReal_im, Complex.conj_im]
  rw [this] at him
  rcases div_eq_zero_iff.mp him with h | h
  · linarith
  · have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
    linarith

/-- The constant bounding the ground energy. -/
def groundEnergyZeroSumConst : ℝ :=
  2 * Real.pi * (1 + 16 * suzukiTestDecayConst posBumpTest 1 *
    (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) / (posBumpMass * Real.sqrt Real.pi))

/-- **The zero sum bounds the eigenvalue.** Let `u` be an even eigenvector of the restricted Weil
form at aperture `a`, `Q_a(u, s) = μ ⟨u, s⟩` on smooth interior sources, with real-rooted transform,
nonzero mass, `‖u‖₁ ≤ Me^{Ka}|∫u|` and inverse-square zero sum at most `S ≥ 1`. If `a - 2 ≥ 48S` and
the Gaussian tail `Me^{(K+1)a} · 2e^{-(a-2)²/96S}` is below the explicit threshold, then
`|μ| ≤ groundEnergyZeroSumConst`. Eigenvectors with large eigenvalues are therefore delocalized. -/
theorem abs_eigenvalue_le_of_zeroSum {M K S : ℝ}
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) (μ : ℝ)
    (heig : ∀ s : CCMComplexSmoothInteriorSource a, ccmRestrictedWeilForm a u s.toCCMFormVector =
      (μ : ℂ) * ∫ t : ℝ, (starRingEnd ℂ) (timeRep a u t) * s t)
    (hreal : ∀ w : ℂ, FourierLaplaceDivision.unitaryLaplace (timeRep a u) w = 0 → w.im = 0)
    (hmass : ∫ t : ℝ, timeRep a u t ≠ 0)
    (heven : ∀ t, timeRep a u (-t) = timeRep a u t)
    (hl1 : ∫ t : ℝ, ‖timeRep a u t‖ ≤ M * Real.exp (K * a.1) * ‖∫ t : ℝ, timeRep a u t‖)
    (hzero : ∑' q : ZeroCopy (conjTransform (timeRep a u)),
      1 / ‖zeroCopyPoint (conjTransform (timeRep a u)) q‖ ^ (2 : ℕ) ≤ S)
    (hS : 1 ≤ S) (hR : 48 * S ≤ a.1 - 2)
    (hsmall : M * Real.exp ((K + 1) * a.1) * (2 * Real.exp (-((a.1 - 2) ^ 2 / (16 * (6 * S))))) *
      eigenDefectConst posBumpTest (1 / 2) 0 ≤ posBumpMass * Real.sqrt (Real.pi / S) / 8) :
    |μ| ≤ groundEnergyZeroSumConst := by
  classical
  set f : ℝ → ℂ := timeRep a u with hf
  set F : ℂ → ℂ := conjTransform f with hFdef
  have hfi := integrable_timeRep a u
  have hsupp := supportedIn_timeRep a u
  have hs := bound_support_of_supportedIn hsupp
  have hF0eq : F 0 = (starRingEnd ℂ) (∫ t : ℝ, f t) := by
    simp only [hFdef, conjTransform, mul_zero, zero_mul, Complex.exp_zero, mul_one]
    exact integral_conj
  have hF0 : F 0 ≠ 0 := by rw [hF0eq, map_ne_zero]; exact hmass
  have hF0n : ‖F 0‖ = ‖∫ t : ℝ, f t‖ := by rw [hF0eq, Complex.norm_conj]
  have hF0pos : 0 < ‖F 0‖ := norm_pos_iff.mpr hF0
  obtain ⟨C, hC, hbound⟩ := exists_orderOne_bound_conjTransform a.2.le hfi hs hF0
  have hdiff : Differentiable ℂ F := differentiable_conjTransform a.2.le hfi hsupp
  have hAn : AnalyticOnNhd ℂ F Set.univ := fun w _ => hdiff.analyticAt w
  have hord : ∀ w, analyticOrderAt F w ≠ ⊤ :=
    GaloisForLFunctions.analyticOrderAt_ne_top_of_entire hdiff hF0
  have hFeven : ∀ w, F (-w) = F w := conjTransform_neg_of_even heven
  have hfac := eq_const_mul_hadamardProduct_of_even hC hAn hF0 hord hFeven hbound
  set G : ℂ → ℂ := fun z => F z / F 0 with hGdef
  have hGP : ∀ z, G z = hadamardProduct F z := by
    intro z
    simp only [hGdef]
    rw [hfac z]
    field_simp
  have hrealF : ∀ q : ZeroCopy F, (zeroCopyPoint F q).im = 0 :=
    im_zeroCopyPoint_conjTransform_eq_zero a.2.le hfi hsupp hreal
  have hGall : ∀ z : ℂ, ‖G z‖ ≤ Real.exp (2 * S * ‖z‖ ^ 2) := fun z => by
    rw [hGP]; exact norm_hadamardProduct_le_of_zeroSum hC hdiff hF0 hbound hzero z
  have hG1 : ∀ s : ℝ, ‖G (s : ℂ) - 1‖ ≤ Real.exp (2 * S * s ^ 2) - 1 := fun s => by
    rw [hGP]; exact norm_hadamardProduct_ofReal_sub_one_le hC hdiff hF0 hbound hrealF hS hzero s
  have hGdiff : DifferentiableOn ℂ G (xiOneSidedStrip (1 / 2)) :=
    (hdiff.div_const _).differentiableOn
  have hGc : Continuous fun s : ℝ => G (s : ℂ) :=
    (hdiff.div_const _).continuous.comp continuous_ofReal
  set B : ℝ := M * Real.exp ((K + 1) * a.1) with hBdef
  have hM : 0 ≤ M := by
    have h1 := le_trans (integral_nonneg fun t => norm_nonneg (f t)) hl1
    have h2 : 0 < Real.exp (K * a.1) * ‖∫ t : ℝ, f t‖ :=
      mul_pos (Real.exp_pos _) (norm_pos_iff.mpr hmass)
    rw [mul_assoc] at h1
    exact nonneg_of_mul_nonneg_left h1 h2
  have hB0 : 0 ≤ B := by positivity
  have hB : ∀ z ∈ xiOneSidedStrip (1 / 2), ‖G z‖ ≤ B := by
    intro z hz
    have hz' : |z.im| ≤ 1 := by
      have : |z.im| < 1 / 2 + 1 / 2 := hz
      linarith
    have h1 := norm_conjTransform_le_mul_exp zero_le_one hfi hs hz'
    show ‖F z / F 0‖ ≤ B
    rw [norm_div, div_le_iff₀ hF0pos, hF0n]
    calc ‖F z‖ ≤ (∫ t : ℝ, ‖f t‖) * Real.exp (1 * a.1) := h1
      _ ≤ (M * Real.exp (K * a.1) * ‖∫ t : ℝ, f t‖) * Real.exp (1 * a.1) := by gcongr
      _ = B * ‖∫ t : ℝ, f t‖ := by
          rw [hBdef, show (K + 1) * a.1 = K * a.1 + 1 * a.1 by ring, Real.exp_add]
          ring
  -- the exact shift identities for `G`
  set κ : ℂ := (μ : ℂ) * (1 / (2 * Real.pi) : ℂ) with hκdef
  have heigen : ∀ (R : ℝ), 0 ≤ R → R < a.1 → ∀ w : SuzukiSmoothCompactTest R,
      ∑' q : XiZeroCopy, G (xiSpectralPoint q) * suzukiSmoothFourier w (-xiSpectralPoint q) =
        κ * ∫ s : ℝ, G (s : ℂ) * suzukiSmoothFourier w (-(s : ℂ)) := by
    intro R hR0 hRa w
    have hid := zeroSide_eigen_of_formEigen a heig
      (testSource a w hRa)
    have hw : ∀ z, suzukiSmoothFourier (testSource a w hRa).toSuzukiSmoothCompactTest z =
        suzukiSmoothFourier w z := fun z => rfl
    simp only [hw] at hid
    simp only [hGdef, div_mul_eq_mul_div]
    rw [tsum_div_const, integral_div, hid]
    ring
  have hid : ∀ v : ℝ, |v| ≤ a.1 - 2 → ∑' q : XiZeroCopy, G (xiSpectralPoint q) *
      (suzukiSmoothFourier posBumpTest (((0 : ℝ) : ℂ) - xiSpectralPoint q) *
        cexp (-(I * xiSpectralPoint q) * v)) =
      κ * ∫ s : ℝ, G (s : ℂ) *
        (suzukiSmoothFourier posBumpTest (((0 : ℝ) : ℂ) - (s : ℂ)) * cexp (-(I * (s : ℂ)) * v)) :=
    fun v hv => eigen_shiftMod posBumpTest v 0 heigen (by linarith)
  have hdef := norm_gaussWeightedDefect_le (η := 1 / 2) (B := B) (σ := 6 * S) (κ := κ)
    (by norm_num) (by positivity) hGdiff hB posBumpTest 0 0 (a.1 - 2) hid
  set Z : ℂ := ∑' q : XiZeroCopy, (G (xiSpectralPoint q) *
      cexp (-((6 * S : ℝ) : ℂ) * xiSpectralPoint q ^ 2)) *
    (suzukiSmoothFourier posBumpTest (((0 : ℝ) : ℂ) - xiSpectralPoint q) *
      cexp (-(I * xiSpectralPoint q) * ((0 : ℝ) : ℂ))) with hZdef
  set Iint : ℂ := ∫ s : ℝ, (G (s : ℂ) * cexp (-((6 * S : ℝ) : ℂ) * (s : ℂ) ^ 2)) *
    (suzukiSmoothFourier posBumpTest (((0 : ℝ) : ℂ) - (s : ℂ)) *
      cexp (-(I * (s : ℂ)) * ((0 : ℝ) : ℂ))) with hIdef
  set E : ℝ := B * gaussShiftTail (6 * S) 0 (a.1 - 2) * eigenDefectConst posBumpTest (1 / 2) 0
    with hEdef
  have hD0 : 0 ≤ eigenDefectConst posBumpTest (1 / 2) 0 := by
    unfold eigenDefectConst
    have h1 := suzukiTestDecayConst_nonneg posBumpTest (1 / 2 + 1 / 2)
    have h2 : 0 ≤ ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) :=
      tsum_nonneg fun q => by positivity
    have h3 : 0 ≤ ∫ s : ℝ, (1 + s ^ 2)⁻¹ := integral_nonneg fun s => by positivity
    positivity
  have hτ := gaussShiftTail_zero_le (σ := 6 * S) (R := a.1 - 2) (by positivity) (by linarith)
  set m : ℝ := posBumpMass with hm
  have hm0 : 0 < m := posBumpMass_pos
  have hE : E ≤ m * Real.sqrt (Real.pi / S) / 8 := by
    refine le_trans ?_ hsmall
    rw [hEdef, hBdef]
    gcongr
  have hI := re_integral_gaussBump_ge hS hGc hG1
  have hInorm : m * Real.sqrt (Real.pi / S) / 4 ≤ ‖Iint‖ := hI.trans (Complex.re_le_norm _)
  have hZ := norm_zeroSide_gaussBump_le hS hGall
  -- algebra on `κ`
  have hkey : ‖κ‖ * ‖Iint‖ ≤ ‖Z‖ + (1 + ‖κ‖) * E := by
    have h1 : κ * Iint = Z - (Z - κ * Iint) := by ring
    rw [← norm_mul, h1]
    exact (norm_sub_le _ _).trans (add_le_add le_rfl hdef)
  have hIpos : 0 < ‖Iint‖ := lt_of_lt_of_le (by positivity) hInorm
  have hκle : ‖κ‖ ≤ 2 * ‖Z‖ / ‖Iint‖ + 1 := by
    rw [div_add_one hIpos.ne', le_div_iff₀ hIpos]
    nlinarith [norm_nonneg κ]
  set K₀ : ℝ := suzukiTestDecayConst posBumpTest 1 with hK₀
  set SX : ℝ := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) with hSX
  have hK0 : 0 ≤ K₀ := suzukiTestDecayConst_nonneg _ _
  have hSX0 : 0 ≤ SX := tsum_nonneg fun q => by positivity
  have hsqrtS : Real.sqrt S * Real.exp (-S) ≤ 1 := by
    have h1 : Real.sqrt S ≤ S := by
      have := Real.sqrt_le_sqrt (show S ≤ S ^ 2 by nlinarith)
      rwa [Real.sqrt_sq (by linarith)] at this
    have h2 : S ≤ Real.exp S := by linarith [Real.add_one_le_exp S]
    have h3 : Real.exp (-S) * Real.exp S = 1 := by rw [← Real.exp_add]; simp
    have h4 : 0 < Real.exp (-S) := Real.exp_pos _
    nlinarith
  have hratio : 2 * ‖Z‖ / ‖Iint‖ ≤ 16 * K₀ * SX / (m * Real.sqrt Real.pi) := by
    have hsq : Real.sqrt (Real.pi / S) = Real.sqrt Real.pi / Real.sqrt S :=
      Real.sqrt_div' _ (by linarith)
    have hSpos : 0 < Real.sqrt S := Real.sqrt_pos.mpr (by linarith)
    have hpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    rw [div_le_div_iff₀ hIpos (by positivity)]
    calc 2 * ‖Z‖ * (m * Real.sqrt Real.pi)
        ≤ 2 * (Real.exp (-S) * (2 * K₀ * SX)) * (m * Real.sqrt Real.pi) := by gcongr
      _ = 16 * K₀ * SX * (m * Real.sqrt Real.pi / Real.sqrt S / 4) *
            (Real.sqrt S * Real.exp (-S)) := by
          field_simp
          ring
      _ ≤ 16 * K₀ * SX * (m * Real.sqrt Real.pi / Real.sqrt S / 4) * 1 := by
          gcongr
      _ = 16 * K₀ * SX * (m * Real.sqrt (Real.pi / S) / 4) := by rw [hsq]; ring
      _ ≤ 16 * K₀ * SX * ‖Iint‖ := by gcongr
  have hκnorm : ‖κ‖ = |μ| / (2 * Real.pi) := by
    rw [hκdef, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
      rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
    rw [this]
    ring
  have hfinal : ‖κ‖ ≤ 1 + 16 * K₀ * SX / (m * Real.sqrt Real.pi) := by linarith
  rw [hκnorm, div_le_iff₀ (by positivity)] at hfinal
  rw [groundEnergyZeroSumConst]
  linarith

/-- **The zero sum bounds the ground energy.** The ground-state case of
`abs_eigenvalue_le_of_zeroSum`. -/
theorem abs_ccmRestrictedWeilGroundEnergy_le_of_zeroSum {M K S : ℝ}
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a)
    (hground : IsFullGround a u)
    (hreal : ∀ w : ℂ, FourierLaplaceDivision.unitaryLaplace (timeRep a u) w = 0 → w.im = 0)
    (hmass : ∫ t : ℝ, timeRep a u t ≠ 0)
    (heven : ∀ t, timeRep a u (-t) = timeRep a u t)
    (hl1 : ∫ t : ℝ, ‖timeRep a u t‖ ≤ M * Real.exp (K * a.1) * ‖∫ t : ℝ, timeRep a u t‖)
    (hzero : ∑' q : ZeroCopy (conjTransform (timeRep a u)),
      1 / ‖zeroCopyPoint (conjTransform (timeRep a u)) q‖ ^ (2 : ℕ) ≤ S)
    (hS : 1 ≤ S) (hR : 48 * S ≤ a.1 - 2)
    (hsmall : M * Real.exp ((K + 1) * a.1) * (2 * Real.exp (-((a.1 - 2) ^ 2 / (16 * (6 * S))))) *
      eigenDefectConst posBumpTest (1 / 2) 0 ≤ posBumpMass * Real.sqrt (Real.pi / S) / 8) :
    |ccmRestrictedWeilGroundEnergy a| ≤ groundEnergyZeroSumConst :=
  abs_eigenvalue_le_of_zeroSum a u _ (formEigen_of_isFullGround a hground) hreal hmass heven hl1
    hzero hS hR hsmall

end GroundEnergy

/-! ## Linear zero sums force RH -/

section Capstone

open GaloisForLFunctions.HTGeometry
open RHTower.CCMFullGroundEigen RHTower.CCMRealRootedGround RHTower.CCMFullRealRootedGround

/-- Along apertures tending to infinity, the Gaussian-tail condition of
`abs_ccmRestrictedWeilGroundEnergy_le_of_zeroSum` holds eventually for zero sums
`S = a / (200 (K + 2))`. -/
theorem eventually_gaussTail_small {M K D : ℝ} (hK : 0 ≤ K) (hM : 0 ≤ M) (hD : 0 ≤ D)
    {a : ℕ → ℝ} (ha : Tendsto a atTop atTop) :
    ∀ᶠ j in atTop, M * Real.exp ((K + 1) * a j) *
        (2 * Real.exp (-((a j - 2) ^ 2 / (16 * (6 * (a j / (200 * (K + 2)))))))) * D ≤
      posBumpMass * Real.sqrt (Real.pi / (a j / (200 * (K + 2)))) / 8 := by
  set c : ℝ := 1 / (200 * (K + 2)) with hc
  have hc0 : 0 < c := by positivity
  set A : ℝ := 2 * M * D * Real.exp (8 * (K + 2)) with hA
  have hA0 : 0 ≤ A := by positivity
  set L : ℝ := posBumpMass * Real.sqrt Real.pi / (8 * Real.sqrt c) with hL
  have hL0 : 0 < L := by
    have := posBumpMass_pos
    have : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    have : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc0
    positivity
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1 / 2) (K + 3)
    (by linarith)).comp ha
  have hev : ∀ᶠ j in atTop, A * ((a j) ^ (1 / 2 : ℝ) * Real.exp (-(K + 3) * a j)) < L := by
    have h2 : Tendsto (fun j => A * ((a j) ^ (1 / 2 : ℝ) * Real.exp (-(K + 3) * a j))) atTop
        (𝓝 (A * 0)) := hlim.const_mul A
    rw [mul_zero] at h2
    exact h2.eventually (gt_mem_nhds hL0)
  filter_upwards [hev, ha.eventually_ge_atTop 4] with j hj h4
  set x : ℝ := a j with hx
  have hx0 : 0 < x := by linarith
  have hS : 0 < x / (200 * (K + 2)) := by positivity
  -- the exponent
  have hexp : (K + 1) * x - (x - 2) ^ 2 / (16 * (6 * (x / (200 * (K + 2))))) ≤
      8 * (K + 2) - (K + 3) * x := by
    have h1 : (x - 2) ^ 2 / (16 * (6 * (x / (200 * (K + 2))))) =
        (200 * (K + 2)) / 96 * ((x - 2) ^ 2 / x) := by field_simp; ring
    have h2 : x - 4 ≤ (x - 2) ^ 2 / x := by
      rw [le_div_iff₀ hx0]; nlinarith
    rw [h1]
    have h3 : 2 * (K + 2) * (x - 4) ≤ (200 * (K + 2)) / 96 * ((x - 2) ^ 2 / x) := by
      have : 2 * (K + 2) ≤ (200 * (K + 2)) / 96 := by nlinarith
      have hx4 : 0 ≤ x - 4 := by linarith
      calc 2 * (K + 2) * (x - 4) ≤ (200 * (K + 2)) / 96 * (x - 4) := by gcongr
        _ ≤ (200 * (K + 2)) / 96 * ((x - 2) ^ 2 / x) := by gcongr
    nlinarith
  have hLHS : M * Real.exp ((K + 1) * x) *
      (2 * Real.exp (-((x - 2) ^ 2 / (16 * (6 * (x / (200 * (K + 2)))))))) * D ≤
      A * Real.exp (-(K + 3) * x) := by
    have : Real.exp ((K + 1) * x) * Real.exp (-((x - 2) ^ 2 / (16 * (6 * (x / (200 * (K + 2)))))))
        ≤ Real.exp (8 * (K + 2)) * Real.exp (-(K + 3) * x) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith
    calc M * Real.exp ((K + 1) * x) *
          (2 * Real.exp (-((x - 2) ^ 2 / (16 * (6 * (x / (200 * (K + 2)))))))) * D
        = 2 * M * D * (Real.exp ((K + 1) * x) *
          Real.exp (-((x - 2) ^ 2 / (16 * (6 * (x / (200 * (K + 2)))))))) := by ring
      _ ≤ 2 * M * D * (Real.exp (8 * (K + 2)) * Real.exp (-(K + 3) * x)) := by gcongr
      _ = A * Real.exp (-(K + 3) * x) := by rw [hA]; ring
  have hRHS : posBumpMass * Real.sqrt (Real.pi / (x / (200 * (K + 2)))) / 8 =
      L / x ^ (1 / 2 : ℝ) := by
    rw [hL, ← Real.sqrt_eq_rpow, show x / (200 * (K + 2)) = c * x by rw [hc]; ring,
      Real.sqrt_div' _ (by positivity), Real.sqrt_mul hc0.le]
    have : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
    have : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc0
    field_simp
  rw [hRHS]
  have hxs : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx0 _
  refine hLHS.trans ?_
  rw [le_div_iff₀ hxs]
  have : A * Real.exp (-(K + 3) * x) * x ^ (1 / 2 : ℝ) =
      A * (x ^ (1 / 2 : ℝ) * Real.exp (-(K + 3) * x)) := by ring
  rw [this]
  exact hj.le

/-- **Even real-rooted ground states with linearly growing zero sums force RH.** Let `u_j` be even
full ground states at apertures `a_j → ∞`, with real-rooted transforms, nonzero mass and
`‖u_j‖₁ ≤ Me^{Ka_j}|∫u_j|` (`K ≥ 0`). If the inverse-square zero sums satisfy
`∑_ρ 1/|ρ|² ≤ a_j/(200(K+2))`, then the ground energies stay bounded, and RH holds. -/
theorem riemannHypothesis_of_evenFullGrounds_linearZeroSum {M K : ℝ} (hK : 0 ≤ K)
    (a : ℕ → SuzukiPositiveAperture) (ha : Tendsto (fun j => (a j).1) atTop atTop)
    (u : ∀ j, CCMArchimedeanFormDomain (a j))
    (hground : ∀ j, IsFullGround (a j) (u j))
    (hreal : ∀ j (w : ℂ), FourierLaplaceDivision.unitaryLaplace (timeRep (a j) (u j)) w = 0 →
      w.im = 0)
    (hmass : ∀ j, ∫ t : ℝ, timeRep (a j) (u j) t ≠ 0)
    (heven : ∀ j t, timeRep (a j) (u j) (-t) = timeRep (a j) (u j) t)
    (hl1 : ∀ j, ∫ t : ℝ, ‖timeRep (a j) (u j) t‖ ≤
      M * Real.exp (K * (a j).1) * ‖∫ t : ℝ, timeRep (a j) (u j) t‖)
    (hzero : ∀ j, ∑' q : ZeroCopy (conjTransform (timeRep (a j) (u j))),
      1 / ‖zeroCopyPoint (conjTransform (timeRep (a j) (u j))) q‖ ^ (2 : ℕ) ≤
        (a j).1 / (200 * (K + 2))) :
    RiemannHypothesis := by
  by_contra hRH
  have hM : 0 ≤ M := by
    have h1 := le_trans (integral_nonneg fun t => norm_nonneg (timeRep (a 0) (u 0) t)) (hl1 0)
    have h2 : 0 < Real.exp (K * (a 0).1) * ‖∫ t : ℝ, timeRep (a 0) (u 0) t‖ :=
      mul_pos (Real.exp_pos _) (norm_pos_iff.mpr (hmass 0))
    rw [mul_assoc] at h1
    exact nonneg_of_mul_nonneg_left h1 h2
  have hD0 : 0 ≤ eigenDefectConst posBumpTest (1 / 2) 0 := by
    unfold eigenDefectConst
    have h1 := suzukiTestDecayConst_nonneg posBumpTest (1 / 2 + 1 / 2)
    have h2 : 0 ≤ ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) :=
      tsum_nonneg fun q => by positivity
    have h3 : 0 ≤ ∫ s : ℝ, (1 + s ^ 2)⁻¹ := integral_nonneg fun s => by positivity
    positivity
  have hconst0 : 0 ≤ groundEnergyZeroSumConst := by
    unfold groundEnergyZeroSumConst
    have h1 := suzukiTestDecayConst_nonneg posBumpTest 1
    have h2 : 0 ≤ ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) :=
      tsum_nonneg fun q => by positivity
    have h3 := posBumpMass_pos
    have h4 : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
    positivity
  obtain ⟨b, hb⟩ :=
    RHTower.WeilDeletion.exists_ccmRestrictedWeilGroundEnergy_lt_of_not_riemannHypothesis
      hRH hconst0
  have hsmall := eventually_gaussTail_small (M := M) (D := eigenDefectConst posBumpTest (1 / 2) 0)
    hK hM hD0 ha
  obtain ⟨j, hj⟩ := (hsmall.and ((ha.eventually_ge_atTop (max (200 * (K + 2)) b.1)))).exists
  obtain ⟨hjsmall, hjlarge⟩ := hj
  have hjK : 200 * (K + 2) ≤ (a j).1 := le_trans (le_max_left _ _) hjlarge
  have hjb : b.1 ≤ (a j).1 := le_trans (le_max_right _ _) hjlarge
  set S : ℝ := (a j).1 / (200 * (K + 2)) with hSdef
  have hS : 1 ≤ S := by rw [hSdef, le_div_iff₀ (by positivity)]; linarith
  have hR : 48 * S ≤ (a j).1 - 2 := by
    rw [hSdef]
    have hK2 : (2 : ℝ) ≤ K + 2 := by linarith
    have : 48 * ((a j).1 / (200 * (K + 2))) ≤ 48 * ((a j).1 / 400) := by
      gcongr
      · linarith
      · nlinarith
    have h400 : (400 : ℝ) ≤ (a j).1 := by nlinarith
    linarith
  have hbound := abs_ccmRestrictedWeilGroundEnergy_le_of_zeroSum (a j) (u j) (hground j)
    (hreal j) (hmass j) (heven j) (hl1 j) (hzero j) hS hR hjsmall
  have hanti := ccmRestrictedWeilGroundEnergy_antitone hjb
  have := neg_abs_le (ccmRestrictedWeilGroundEnergy (a j))
  linarith

/-- A ground state with nonzero mass is nonzero. -/
theorem ccmArchimedeanFormToAperture_ne_zero_of_integral_ne_zero {a : SuzukiPositiveAperture}
    {u : CCMArchimedeanFormDomain a} (hmass : ∫ t : ℝ, timeRep a u t ≠ 0) :
    ccmArchimedeanFormToAperture a u ≠ 0 := by
  intro h0
  apply hmass
  have hae := coeFn_eq_timeRep a u
  rw [h0] at hae
  have h1 : (((0 : suzukiApertureHilbert a) : SoninL2) : ℝ → ℂ) =ᵐ[volume] 0 := by
    have h00 : ((0 : suzukiApertureHilbert a) : SoninL2) = 0 := rfl
    rw [h00]
    exact Lp.coeFn_zero ℂ 2 volume
  have h2 : timeRep a u =ᵐ[volume] 0 := hae.symm.trans h1
  rw [integral_congr_ae h2]
  simp

/-- **Simple even ground states with linearly growing zero sums force RH.** If at apertures
`a_j → ∞` the ground level is one-dimensional and the ground state is even, with nonzero mass,
`‖u_j‖₁ ≤ Me^{Ka_j}|∫u_j|` and `∑_ρ 1/|ρ|² ≤ a_j/(200(K+2))`, then RH holds. Real-rootedness is
automatic for simple ground levels (`realRooted_of_finrank_eq_one`). -/
theorem riemannHypothesis_of_simpleEvenFullGrounds_linearZeroSum {M K : ℝ} (hK : 0 ≤ K)
    (a : ℕ → SuzukiPositiveAperture) (ha : Tendsto (fun j => (a j).1) atTop atTop)
    (u : ∀ j, CCMArchimedeanFormDomain (a j))
    (hsimple : ∀ j, Module.finrank ℂ (fullGroundSubmodule (a j)) = 1)
    (hground : ∀ j, IsFullGround (a j) (u j))
    (hmass : ∀ j, ∫ t : ℝ, timeRep (a j) (u j) t ≠ 0)
    (heven : ∀ j t, timeRep (a j) (u j) (-t) = timeRep (a j) (u j) t)
    (hl1 : ∀ j, ∫ t : ℝ, ‖timeRep (a j) (u j) t‖ ≤
      M * Real.exp (K * (a j).1) * ‖∫ t : ℝ, timeRep (a j) (u j) t‖)
    (hzero : ∀ j, ∑' q : ZeroCopy (conjTransform (timeRep (a j) (u j))),
      1 / ‖zeroCopyPoint (conjTransform (timeRep (a j) (u j))) q‖ ^ (2 : ℕ) ≤
        (a j).1 / (200 * (K + 2))) :
    RiemannHypothesis :=
  riemannHypothesis_of_evenFullGrounds_linearZeroSum hK a ha u hground
    (fun j => realRooted_of_finrank_eq_one (a j) (hsimple j) (hground j)
      (ccmArchimedeanFormToAperture_ne_zero_of_integral_ne_zero (hmass j)))
    hmass heven hl1 hzero

end Capstone

end

end RHTower
