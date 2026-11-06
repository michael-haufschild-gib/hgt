import GaloisForLFunctions.WindowVisibilityLaw.TheUniversalVisibilityThreshold
import GaloisForLFunctions.WindowVisibilityLaw.TheSineLocalizerOfATest
import GaloisForLFunctions.VerifiedHeightRungs.TheNormalizedSmoothingKeepsThePoles
import GaloisForLFunctions.RHTower.LowHeightHodgeExclusion
import GaloisForLFunctions.SquareRootThreshold.AnExplicitClusterDetectorConstant

/-!
# The two-lobe test has absolute constants

In a configuration with `N(t,t+1] ≤ A₀ log(|t|+3)`, take a coherent cluster of depth at least `δ` in
a sea of depth at most `σ ≤ δ`. Window positivity at `a` forces

`M_S e^{2(δ−σ)a} ≤ 12000 A₀ log(|γ₀| + 4·10⁸ A₀ log(|γ₀|+3) + 6)`,

with no dependence on `a` or `δ` on the right. The earlier bound carried `2²⁶ δ (2a+2π) e^{2π}` and a
logarithm of size `a`.

The test is the odd pair of narrow bumps `s(u) = w(u−c) − w(u+c)`, `w = (b²−v²)₊^{5/2}`, `b = 1/(2δ)`,
`c = a−b`. Three identities make it sharp:

* its pairing with `sinh(δu)` is `2 sinh(δc) ∫ w(v) cosh(δv) dv`;
* its transform is `2i sin(cz) ŵ(z)`, so sampling it costs only the support length `2b` of `w`;
* its second derivative is a difference of translates, so `testNorm s ≤ 2 testNorm w` carries no
  exponential factor, and the far tail is paid at bounded distance.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.WindowVisibilityLaw

open Zeta23 _root_.RHTower
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold
open _root_.RHTower.CCMParityQuartet

/-- The odd pair of bumps at `±c`. -/
def twoLobeTest (b c u : ℝ) : ℝ := sinhTestWeight b (u - c) - sinhTestWeight b (u + c)

theorem twoLobeTest_contDiff (b c : ℝ) : ContDiff ℝ 2 (twoLobeTest b c) := by
  unfold twoLobeTest
  exact ((sinhTestWeight_contDiff b).comp (contDiff_id.sub contDiff_const)).sub
    ((sinhTestWeight_contDiff b).comp (contDiff_id.add contDiff_const))

theorem twoLobeTest_odd (b c u : ℝ) : twoLobeTest b c (-u) = -twoLobeTest b c u := by
  unfold twoLobeTest
  rw [show -u - c = -(u + c) by ring, show -u + c = -(u - c) by ring, sinhTestWeight_even,
    sinhTestWeight_even]
  ring

theorem twoLobeTest_supp {b c : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) :
    ∀ u, twoLobeTest b c u ≠ 0 → |u| ≤ b + c := by
  intro u hu
  by_contra hn
  rw [not_le] at hn
  apply hu
  have h1 : b < |u - c| := by
    have h := abs_add_le (u - c) c
    rw [sub_add_cancel, abs_of_nonneg hc] at h
    linarith only [h, hn]
  have h2 : b < |u + c| := by
    have h := abs_sub (u + c) c
    rw [add_sub_cancel_right, abs_of_nonneg hc] at h
    linarith only [h, hn]
  unfold twoLobeTest
  rw [sinhTestWeight_eq_zero hb h1, sinhTestWeight_eq_zero hb h2, sub_zero]

theorem twoLobeTest_nonneg {b c u : ℝ} (hb : 0 ≤ b) (hbc : b < c) (hu : 0 ≤ u) :
    0 ≤ twoLobeTest b c u := by
  have h2 : b < |u + c| := by
    rw [abs_of_nonneg (by linarith only [hu, hb, hbc])]
    linarith only [hu, hbc]
  unfold twoLobeTest
  rw [sinhTestWeight_eq_zero hb h2, sub_zero]
  exact sinhTestWeight_nonneg _ _

private theorem hasCompactSupport_weight {b : ℝ} (hb : 0 ≤ b) :
    HasCompactSupport (sinhTestWeight b) :=
  hasCompactSupport_of_support_subset_abs (sinhTestWeight_supp hb)

/-- **The pairing with `sinh`.** -/
theorem integral_twoLobeTest_mul_sinh {b : ℝ} (hb : 0 ≤ b) (c δ : ℝ) :
    ∫ u, twoLobeTest b c u * Real.sinh (δ * u) =
      2 * Real.sinh (δ * c) * ∫ v, sinhTestWeight b v * Real.cosh (δ * v) := by
  have hcs := hasCompactSupport_weight hb
  have hcw := (sinhTestWeight_contDiff b).continuous
  have hI : ∀ t : ℝ, Integrable fun v => sinhTestWeight b v * Real.sinh (δ * (v + t)) := fun t =>
    (hcw.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.mul_right
  have h1 : ∫ u, sinhTestWeight b (u - c) * Real.sinh (δ * u) =
      ∫ v, sinhTestWeight b v * Real.sinh (δ * (v + c)) := by
    rw [← integral_sub_right_eq_self (fun v => sinhTestWeight b v * Real.sinh (δ * (v + c))) c]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only
    rw [sub_add_cancel]
  have h2 : ∫ u, sinhTestWeight b (u + c) * Real.sinh (δ * u) =
      ∫ v, sinhTestWeight b v * Real.sinh (δ * (v + -c)) := by
    rw [← integral_add_right_eq_self (fun v => sinhTestWeight b v * Real.sinh (δ * (v + -c))) c]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only
    rw [add_neg_cancel_right]
  have hsplit : ∫ u, twoLobeTest b c u * Real.sinh (δ * u) =
      (∫ u, sinhTestWeight b (u - c) * Real.sinh (δ * u)) -
        ∫ u, sinhTestWeight b (u + c) * Real.sinh (δ * u) := by
    rw [← integral_sub]
    · refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      simp only [twoLobeTest]
      ring
    · have := (hI c).comp_sub_right c
      refine this.congr (Eventually.of_forall fun u => ?_)
      simp only [sub_add_cancel]
    · have := (hI (-c)).comp_add_right c
      refine this.congr (Eventually.of_forall fun u => ?_)
      simp only [add_neg_cancel_right]
  rw [hsplit, h1, h2, ← integral_sub (hI c) (hI (-c)), ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  have e1 : δ * (v + c) = δ * v + δ * c := by ring
  have e2 : δ * (v + -c) = δ * v - δ * c := by ring
  rw [e1, e2, Real.sinh_add, Real.sinh_sub]
  ring

/-- **Translates do not change the test norm.** -/
theorem testNorm_twoLobeTest_le {b : ℝ} (hb : 0 ≤ b) (c : ℝ) :
    testNorm (twoLobeTest b c) ≤ 2 * testNorm (sinhTestWeight b) := by
  let F₁ : ℝ → ℂ := fun v => (sinhTestWeight b v : ℂ)
  have hF₁c : ContDiff ℝ 2 F₁ := Complex.ofRealCLM.contDiff.comp (sinhTestWeight_contDiff b)
  have hd1 : ContDiff ℝ 1 (deriv F₁) := ((contDiff_succ_iff_deriv (n := 1)).mp hF₁c).2.2
  have hF₂c : Continuous (deriv (deriv F₁)) := hd1.continuous_deriv le_rfl
  have hF₂eq : deriv (deriv F₁) = fun v => ((sinhTestWeightDeriv2 b v : ℝ) : ℂ) :=
    deriv_deriv_ofReal_sinhTestWeight b
  have hF₁int : Integrable fun v => ‖F₁ v‖ :=
    hF₁c.continuous.norm.integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_Icc (a := -b) (b := b)) fun v hv => by
        have : b < |v| := by
          by_contra h
          rw [not_lt] at h
          exact hv (abs_le.mp h)
        simp [F₁, sinhTestWeight_eq_zero hb this])
  have hF₂int : Integrable fun v => ‖deriv (deriv F₁) v‖ :=
    hF₂c.norm.integrable_of_hasCompactSupport
      (HasCompactSupport.intro (isCompact_Icc (a := -b) (b := b)) fun v hv => by
        have : b < |v| := by
          by_contra h
          rw [not_lt] at h
          exact hv (abs_le.mp h)
        rw [hF₂eq]
        simp [sinhTestWeightDeriv2_eq_zero hb this])
  have hshift : ∀ {G : ℝ → ℂ}, Integrable (fun v => ‖G v‖) →
      ∫ u, ‖G (u - c) - G (u + c)‖ ≤ 2 * ∫ v, ‖G v‖ := by
    intro G hG
    have h1 : Integrable fun u => ‖G (u - c)‖ := hG.comp_sub_right c
    have h2 : Integrable fun u => ‖G (u + c)‖ := hG.comp_add_right c
    calc ∫ u, ‖G (u - c) - G (u + c)‖
        ≤ ∫ u, (‖G (u - c)‖ + ‖G (u + c)‖) :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (h1.add h2)
            (Eventually.of_forall fun u => norm_sub_le _ _)
      _ = 2 * ∫ v, ‖G v‖ := by
          rw [integral_add h1 h2, integral_sub_right_eq_self (fun v => ‖G v‖) c,
            integral_add_right_eq_self (fun v => ‖G v‖) c]
          ring
  have hval : (fun u => ((twoLobeTest b c u : ℝ) : ℂ)) = fun u => F₁ (u - c) - F₁ (u + c) := by
    funext u
    simp [twoLobeTest, F₁]
  have hderiv1 : deriv (fun u => F₁ (u - c) - F₁ (u + c)) =
      fun u => deriv F₁ (u - c) - deriv F₁ (u + c) := by
    funext u
    have hd : Differentiable ℝ F₁ := hF₁c.differentiable (by norm_num)
    have h1 : HasDerivAt (fun u => F₁ (u - c)) (deriv F₁ (u - c)) u :=
      (hd (u - c)).hasDerivAt.comp_sub_const u c
    have h2 : HasDerivAt (fun u => F₁ (u + c)) (deriv F₁ (u + c)) u :=
      (hd (u + c)).hasDerivAt.comp_add_const u c
    exact (h1.sub h2).deriv
  have hderiv2 : deriv (fun u => deriv F₁ (u - c) - deriv F₁ (u + c)) =
      fun u => deriv (deriv F₁) (u - c) - deriv (deriv F₁) (u + c) := by
    funext u
    have hd : Differentiable ℝ (deriv F₁) := hd1.differentiable (by norm_num)
    have h1 : HasDerivAt (fun u => deriv F₁ (u - c)) (deriv (deriv F₁) (u - c)) u :=
      (hd (u - c)).hasDerivAt.comp_sub_const u c
    have h2 : HasDerivAt (fun u => deriv F₁ (u + c)) (deriv (deriv F₁) (u + c)) u :=
      (hd (u + c)).hasDerivAt.comp_add_const u c
    exact (h1.sub h2).deriv
  have htw : testNorm (sinhTestWeight b) =
      (∫ v, ‖F₁ v‖) + ∫ v, ‖deriv (deriv F₁) v‖ := rfl
  rw [htw]
  unfold testNorm
  rw [hval, hderiv1, hderiv2]
  have e1 : ∫ u, ‖((twoLobeTest b c u : ℝ) : ℂ)‖ = ∫ u, ‖F₁ (u - c) - F₁ (u + c)‖ := by
    congr 1
    funext u
    rw [congrFun hval u]
  have h1 := hshift hF₁int
  have h2 := hshift hF₂int
  change (∫ u, ‖((twoLobeTest b c u : ℝ) : ℂ)‖) +
    (∫ u, ‖deriv (deriv F₁) (u - c) - deriv (deriv F₁) (u + c)‖) ≤ _
  rw [e1]
  linarith only [h1, h2]

private theorem norm_sin_le_exp (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin]
  have h1 : ‖cexp (-z * I)‖ = Real.exp z.im := by
    rw [Complex.norm_exp]
    simp
  have h2 : ‖cexp (z * I)‖ = Real.exp (-z.im) := by
    rw [Complex.norm_exp]
    simp
  have hle1 : Real.exp z.im ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (le_abs_self _)
  have hle2 : Real.exp (-z.im) ≤ Real.exp |z.im| := Real.exp_le_exp.mpr (neg_le_abs _)
  rw [norm_div, norm_mul, Complex.norm_I, mul_one]
  have h2' : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [h2']
  have := norm_sub_le (cexp (-z * I)) (cexp (z * I))
  rw [h1, h2] at this
  linarith only [this, hle1, hle2]

/-- **The transform of the two-lobe test.** `ŝ(z) = 2i sin(cz) ŵ(z)`. -/
theorem paperFT_twoLobeTest {b : ℝ} (hb : 0 ≤ b) (c : ℝ) (z : ℂ) :
    paperFT (fun u => ((twoLobeTest b c u : ℝ) : ℂ)) z =
      2 * I * (Complex.sin (c * z) * paperFT (fun v => ((sinhTestWeight b v : ℝ) : ℂ)) z) := by
  have hcw : Continuous fun v => ((sinhTestWeight b v : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (sinhTestWeight_contDiff b).continuous
  have hcs : HasCompactSupport fun v => ((sinhTestWeight b v : ℝ) : ℂ) :=
    (hasCompactSupport_weight hb).comp_left (g := Complex.ofReal) (by simp)
  rw [← paperFT_sineLift c hcw hcs z]
  simp only [paperFT, sineLift]
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [twoLobeTest]
  push_cast
  field_simp

/-- **Sampling the two-lobe test.** The sea costs only the bump width `2b`, not the aperture. -/
theorem sum_norm_Wsummand_twoLobe_le (Z : ZeroConfig) (γ₀ : ℝ) {b c σ : ℝ} (hb : 1 ≤ b) (hc : 0 ≤ c)
    (hσ : 0 ≤ σ) (F : Finset ℂ) (hFσ : ∀ ρ ∈ F, |ρ.re - 1 / 2| ≤ σ) {K : ℕ}
    (hcell : ∀ n : ℤ, ∑ ρ ∈ F.filter (fun ρ => ⌊ρ.im / (2 * π / (2 * π * (2 * b + 1)))⌋ = n),
      Z.mult ρ ≤ K) :
    ∑ ρ ∈ F, ‖Z.Wsummand (modulatedTest γ₀ (twoLobeTest b c))
        (modulatedTest γ₀ (twoLobeTest b c)) ρ‖ ≤
      4 * Real.exp 1 * Real.exp (2 * σ * (b + c)) *
        (K * (2 * π * (2 * b + 1) * ∫ v, sinhTestWeight b v ^ 2)) := by
  have hb0 : 0 < b := by linarith only [hb]
  obtain ⟨ℓ, hℓd⟩ : ∃ ℓ, ℓ = 2 * π * (2 * b + 1) := ⟨_, rfl⟩
  rw [← hℓd] at hcell ⊢
  have hℓ : 2 * b < ℓ := by
    rw [hℓd]
    nlinarith only [Real.pi_gt_three, hb0]
  have hstep : 2 * π / ℓ = 1 / (2 * b + 1) := by
    rw [hℓd]
    field_simp
  -- The source of the sampling inequality.
  have hsupp := sinhTestWeight_supp hb0.le
  have hwm : ContDiff ℝ 2 (modulatedTest γ₀ (sinhTestWeight b)) :=
    modulatedTest_contDiff γ₀ (sinhTestWeight_contDiff b)
  have hts := tsupport_modulatedTest_subset γ₀ hsupp
  have hsrc : IntervalSource b (modulatedTest γ₀ (sinhTestWeight b)) :=
    { continuous := hwm.continuous
      hasCompactSupport := hasCompactSupport_of_tsupport_subset_Icc hts
      vanish := fun u hu => image_eq_zero_of_notMem_tsupport fun hm => hu (hts hm) }
  obtain ⟨h1, h2⟩ := sum_mult_norm_sq_paperFT_le_of_cellCount Z hb0 hℓ hσ hsrc F hFσ hcell
  have hnorm : ∫ u, ‖modulatedTest γ₀ (sinhTestWeight b) u‖ ^ 2 = ∫ v, sinhTestWeight b v ^ 2 := by
    congr 1
    funext u
    simp only [modulatedTest, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have he : ‖cexp (-(I * (γ₀ : ℂ) * (u : ℂ)))‖ = 1 := by
      rw [show -(I * (γ₀ : ℂ) * (u : ℂ)) = I * ((-γ₀ : ℝ) : ℂ) * u by push_cast; ring,
        norm_cexp_I_mul]
      simp
    rw [he, one_mul, sq_abs]
  rw [hnorm, hstep] at h1 h2
  obtain ⟨B, hBd⟩ : ∃ B, B = Real.exp (2 * (1 / (2 * b + 1) + σ) * b) *
      (K * (ℓ * ∫ v, sinhTestWeight b v ^ 2)) := ⟨_, rfl⟩
  rw [← hBd] at h1 h2
  obtain ⟨Cs, hCs⟩ : ∃ Cs, Cs = Real.exp (c * σ) := ⟨_, rfl⟩
  have hCs0 : 0 ≤ Cs := by rw [hCs]; exact (Real.exp_pos _).le
  -- The transform bound at one point.
  have hpointA : ∀ z : ℂ, |z.im| ≤ σ →
      ‖paperFT (fun u => ((twoLobeTest b c u : ℝ) : ℂ)) (z - γ₀)‖ ^ 2 ≤
        4 * Cs ^ 2 * ‖paperFT (modulatedTest γ₀ (sinhTestWeight b)) z‖ ^ 2 := by
    intro z hz
    rw [paperFT_twoLobeTest hb0.le]
    have hmod : paperFT (fun v => ((sinhTestWeight b v : ℝ) : ℂ)) (z - γ₀) =
        paperFT (modulatedTest γ₀ (sinhTestWeight b)) z :=
      (paperFT_modulate _ γ₀ z).symm
    rw [hmod, norm_mul, norm_mul, norm_mul, Complex.norm_I, mul_one]
    have h2' : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2']
    have hsin : ‖Complex.sin ((c : ℂ) * (z - γ₀))‖ ≤ Cs := by
      refine (norm_sin_le_exp _).trans ?_
      rw [hCs]
      refine Real.exp_le_exp.mpr ?_
      have him : ((c : ℂ) * (z - γ₀)).im = c * z.im := by simp [Complex.mul_im]
      rw [him, abs_mul, abs_of_nonneg hc]
      exact mul_le_mul_of_nonneg_left hz hc
    have hprod := mul_le_mul_of_nonneg_right hsin
      (norm_nonneg (paperFT (modulatedTest γ₀ (sinhTestWeight b)) z))
    have h0 : 0 ≤ ‖Complex.sin ((c : ℂ) * (z - γ₀))‖ *
        ‖paperFT (modulatedTest γ₀ (sinhTestWeight b)) z‖ := by positivity
    have hsq := pow_le_pow_left₀ h0 hprod 2
    nlinarith only [hsq]
  have hpt : ∀ ρ ∈ F, ‖Z.Wsummand (modulatedTest γ₀ (twoLobeTest b c))
      (modulatedTest γ₀ (twoLobeTest b c)) ρ‖ ≤
      2 * Cs ^ 2 * ((Z.mult ρ : ℝ) * ‖paperFT (modulatedTest γ₀ (sinhTestWeight b)) (gammaOf ρ)‖ ^ 2 +
        (Z.mult ρ : ℝ) * ‖paperFT (modulatedTest γ₀ (sinhTestWeight b)) (conj (gammaOf ρ))‖ ^ 2) := by
    intro ρ hρ
    have him1 : |(gammaOf ρ).im| ≤ σ := by
      rw [WeilEF.gammaOf_im, abs_sub_comm]
      exact hFσ ρ hρ
    have him2 : |(conj (gammaOf ρ)).im| ≤ σ := by
      rw [Complex.conj_im, abs_neg]
      exact him1
    have hA := hpointA _ him1
    have hA' := hpointA _ him2
    rw [Wsummand_modulatedTest, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_conj]
    have hm0 : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
    obtain ⟨x, hx⟩ : ∃ x, x = ‖paperFT (fun u => ((twoLobeTest b c u : ℝ) : ℂ)) (gammaOf ρ - γ₀)‖ :=
      ⟨_, rfl⟩
    obtain ⟨y, hy⟩ : ∃ y, y = ‖paperFT (fun u => ((twoLobeTest b c u : ℝ) : ℂ))
        (conj (gammaOf ρ) - γ₀)‖ := ⟨_, rfl⟩
    rw [← hx] at hA ⊢
    rw [← hy] at hA' ⊢
    have hxy : x * y ≤ (x ^ 2 + y ^ 2) / 2 := by nlinarith only [sq_nonneg (x - y)]
    have hm := mul_le_mul_of_nonneg_left hxy hm0
    have hsum : (x ^ 2 + y ^ 2) / 2 ≤ 2 * Cs ^ 2 *
        (‖paperFT (modulatedTest γ₀ (sinhTestWeight b)) (gammaOf ρ)‖ ^ 2 +
          ‖paperFT (modulatedTest γ₀ (sinhTestWeight b)) (conj (gammaOf ρ))‖ ^ 2) := by
      linarith only [hA, hA']
    have hm2 := mul_le_mul_of_nonneg_left hsum hm0
    calc (Z.mult ρ : ℝ) * x * y = (Z.mult ρ : ℝ) * (x * y) := by ring
      _ ≤ _ := hm
      _ ≤ _ := hm2
      _ = _ := by ring
  have hB0 : 0 ≤ ∫ v, sinhTestWeight b v ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hℓ0 : 0 < ℓ := by linarith only [hℓ, hb0]
  have hCB : Cs ^ 2 * Real.exp (2 * (1 / (2 * b + 1) + σ) * b) ≤
      Real.exp 1 * Real.exp (2 * σ * (b + c)) := by
    rw [hCs, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h3 : 2 * (1 / (2 * b + 1)) * b ≤ 1 := by
      rw [show 2 * (1 / (2 * b + 1)) * b = 2 * b / (2 * b + 1) by ring,
        div_le_one (by positivity)]
      linarith only []
    push_cast
    nlinarith only [h3]
  calc ∑ ρ ∈ F, ‖Z.Wsummand (modulatedTest γ₀ (twoLobeTest b c))
        (modulatedTest γ₀ (twoLobeTest b c)) ρ‖
      ≤ ∑ ρ ∈ F, 2 * Cs ^ 2 * ((Z.mult ρ : ℝ) *
          ‖paperFT (modulatedTest γ₀ (sinhTestWeight b)) (gammaOf ρ)‖ ^ 2 + (Z.mult ρ : ℝ) *
          ‖paperFT (modulatedTest γ₀ (sinhTestWeight b)) (conj (gammaOf ρ))‖ ^ 2) :=
        Finset.sum_le_sum hpt
    _ = 2 * Cs ^ 2 * ((∑ ρ ∈ F, (Z.mult ρ : ℝ) *
          ‖paperFT (modulatedTest γ₀ (sinhTestWeight b)) (gammaOf ρ)‖ ^ 2) + ∑ ρ ∈ F, (Z.mult ρ : ℝ) *
          ‖paperFT (modulatedTest γ₀ (sinhTestWeight b)) (conj (gammaOf ρ))‖ ^ 2) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ 2 * Cs ^ 2 * (B + B) :=
        mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)
    _ = 4 * (Cs ^ 2 * Real.exp (2 * (1 / (2 * b + 1) + σ) * b)) *
          (K * (ℓ * ∫ v, sinhTestWeight b v ^ 2)) := by rw [hBd]; ring
    _ ≤ 4 * (Real.exp 1 * Real.exp (2 * σ * (b + c))) *
          (K * (ℓ * ∫ v, sinhTestWeight b v ^ 2)) := by
        gcongr
    _ = _ := by ring

/-- **Window visibility with absolute constants.** A coherent cluster of depth at least `δ` in a sea
of depth at most `σ ≤ δ` obeys `M_S e^{2(δ−σ)a} ≤ 12000 A₀ log(|γ₀| + 4·10⁸ A₀ log(|γ₀|+3) + 6)`
under window positivity at `a`, for every `a ≥ 2/δ`. -/
theorem windowPositiveAt_cluster_absolute_bound (Z : ZeroConfig) {A₀ : ℝ} (hA₀ : 1 ≤ A₀)
    (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    {γ₀ a δ σ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hδa : 2 ≤ δ * a) (hσ : 0 ≤ σ) (hσδ : σ ≤ δ)
    (hpos : WindowPositiveAt Z a)
    (S : Finset ℂ) (hSne : S.Nonempty) (hSc : ∀ ρ ∈ S, ρ ∈ Z.carrier)
    (hSδ : ∀ ρ ∈ S, 1 / 2 + δ ≤ ρ.re) (hSγ : ∀ ρ ∈ S, |ρ.im - γ₀| ≤ 1 / (4 * a))
    (hsea : ∀ ρ ∈ Z.carrier, ρ ∉ S → ρ ∉ S.image reflect → |ρ.re - 1 / 2| ≤ σ) :
    (∑ ρ ∈ S, (Z.mult ρ : ℝ)) * Real.exp (2 * (δ - σ) * a) ≤
      12000 * A₀ * Real.log (|γ₀| + 4 * 10 ^ 8 * A₀ * Real.log (|γ₀| + 3) + 6) := by
  classical
  have ha4 : 4 ≤ a := by nlinarith only [hδa, hδ1, hδ]
  have ha : 0 < a := by linarith only [ha4]
  obtain ⟨b, hbd⟩ : ∃ b, b = 1 / (2 * δ) := ⟨_, rfl⟩
  have hb1 : 1 ≤ b := by
    rw [hbd, le_div_iff₀ (by positivity)]
    linarith only [hδ1]
  have hb0 : 0 < b := by linarith only [hb1]
  have hδb : δ * b = 1 / 2 := by rw [hbd]; field_simp
  have ha4b : 4 * b ≤ a := by
    have h : 2 = 4 * (δ * b) := by rw [hδb]; norm_num
    nlinarith only [hδa, h, hδ]
  obtain ⟨c, hcd⟩ : ∃ c, c = a - b := ⟨_, rfl⟩
  have hbc : b < c := by rw [hcd]; linarith only [ha4b, hb0]
  have hc0 : 0 ≤ c := by linarith only [hbc, hb0]
  have habc : b + c = a := by rw [hcd]; ring
  set s := twoLobeTest b c with hs
  set f := modulatedTest γ₀ s with hf
  have hs_cd : ContDiff ℝ 2 s := twoLobeTest_contDiff b c
  have hs_supp : ∀ u, s u ≠ 0 → |u| ≤ a := fun u hu => by
    have := twoLobeTest_supp hb0.le hc0 u hu
    rwa [habc] at this
  have hs_odd : ∀ u, s (-u) = -s u := twoLobeTest_odd b c
  have hs_nn : ∀ u, 0 ≤ u → 0 ≤ s u := fun u hu => twoLobeTest_nonneg hb0.le hbc hu
  have hf_cd : ContDiff ℝ 2 f := modulatedTest_contDiff γ₀ hs_cd
  have hf_supp : tsupport f ⊆ Icc (-a) a := tsupport_modulatedTest_subset γ₀ hs_supp
  obtain ⟨hwsum, hwle⟩ := window_tsum_le Z hA₀ hloc γ₀
  have hsumm : Summable (fun τ : Z.carrier => Z.Wsummand f f τ) :=
    Summable.of_norm_bounded (hwsum.mul_left _) fun τ =>
      norm_Wsummand_modulatedTest_le_weight Z γ₀ ha.le hs_cd hs_supp τ.2
  obtain ⟨L₀, hL₀⟩ : ∃ L₀, L₀ = Real.log (|γ₀| + 3) := ⟨_, rfl⟩
  have hL₀1 : 1 ≤ L₀ := by rw [hL₀]; exact one_le_log_abs_add_three γ₀
  obtain ⟨R, hRd⟩ : ∃ R, R = 4 * 10 ^ 8 * A₀ * L₀ := ⟨_, rfl⟩
  have hR1 : 1 ≤ R := by
    rw [hRd]
    have h : 1 ≤ A₀ * L₀ := by nlinarith only [hA₀, hL₀1]
    nlinarith only [h]
  have hR0 : 0 ≤ R := by linarith only [hR1]
  have hRcone : 1 / (4 * a) ≤ R := by
    refine le_trans ?_ hR1
    rw [div_le_one (by positivity)]
    linarith only [ha4]
  rw [← hL₀, ← hRd]
  obtain ⟨Λ, hΛd⟩ : ∃ Λ, Λ = Real.log (|γ₀| + R + 6) := ⟨_, rfl⟩
  rw [← hΛd]
  have hΛ1 : 1 ≤ Λ := by
    rw [hΛd]
    exact (one_le_log_abs_add_three γ₀).trans (Real.log_le_log (by positivity)
      (by linarith only [hR0]))
  -- The finite window, the cluster and the sea around it.
  have hfin_set : (Z.carrier ∩ {z : ℂ | γ₀ - R ≤ z.im ∧ z.im ≤ γ₀ + R}).Finite :=
    (Z.finite_window (γ₀ - R - 1) (γ₀ + R)).subset fun z ⟨hz, h1, h2⟩ => ⟨hz, by linarith, h2⟩
  set W_all : Finset ℂ := hfin_set.toFinset
  have hmem_Wall : ∀ z : ℂ, z ∈ W_all ↔ z ∈ Z.carrier ∧ |z.im - γ₀| ≤ R := fun z => by
    rw [Set.Finite.mem_toFinset, Set.mem_inter_iff, Set.mem_setOf_eq, abs_le]
    exact ⟨fun ⟨hz, h1, h2⟩ => ⟨hz, by linarith, by linarith⟩,
      fun ⟨hz, h1, h2⟩ => ⟨hz, by linarith, by linarith⟩⟩
  set S' : Finset ℂ := S.image reflect
  have hdisj_SS' : Disjoint S S' := by
    rw [Finset.disjoint_left]
    intro ρ hρ hρ'
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hρ'
    have h1 := hSδ _ hρ
    have h2 := hSδ q hq
    simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re] at h1
    linarith only [h1, h2, hδ]
  have hrefl_inj : Function.Injective reflect := fun z w h => by
    have h1 : reflect (reflect z) = z := by
      apply Complex.ext <;> simp [reflect]
    have h2 : reflect (reflect w) = w := by
      apply Complex.ext <;> simp [reflect]
    rw [← h1, ← h2, h]
  have hsub_S : S ⊆ W_all := fun ρ hρ =>
    (hmem_Wall ρ).mpr ⟨hSc ρ hρ, (hSγ ρ hρ).trans hRcone⟩
  have hsub_S' : S' ⊆ W_all := by
    intro ρ hρ
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hρ
    refine (hmem_Wall _).mpr ⟨Z.reflect_mem q (hSc q hq), ?_⟩
    have him : (reflect q).im = q.im := by simp [reflect]
    rw [him]
    exact (hSγ q hq).trans hRcone
  set F_near : Finset ℂ := W_all \ (S ∪ S')
  set P := ∫ u, s u * Real.sinh (δ * u) with hPd
  -- The pairing and the bump mass.
  obtain ⟨Iw, hIwd⟩ : ∃ I, I = ∫ v, sinhTestWeight b v * Real.cosh (δ * v) := ⟨_, rfl⟩
  have hPeq : P = 2 * Real.sinh (δ * c) * Iw := by
    rw [hPd, hIwd]
    exact integral_twoLobeTest_mul_sinh hb0.le c δ
  have hIw : 9 / 20 * b ^ 6 ≤ Iw := by
    have h1 := sinhTestWeight_cosh_energy_ge' hb0 δ
    rw [← hIwd] at h1
    have h2 := VerifiedHeightRungs.sinhTestWeight_ge hb0 (u := b / 2)
      (by rw [abs_of_pos (by positivity)])
    have h3 : sinhTestWeight b (b / 2) = (3 * b ^ 2 / 4) ^ (5 / 2 : ℝ) := by
      unfold sinhTestWeight
      congr 1
      ring
    rw [h3] at h2
    have h4 := mul_le_mul_of_nonneg_left h2 hb0.le
    calc 9 / 20 * b ^ 6 = b * (9 / 20 * b ^ 5) := by ring
      _ ≤ _ := h4
      _ ≤ Iw := h1
  have hIw0 : 0 < Iw := lt_of_lt_of_le (by positivity) hIw
  obtain ⟨Nw, hNwd⟩ : ∃ N, N = ∫ v, sinhTestWeight b v ^ 2 := ⟨_, rfl⟩
  have hwcont := (sinhTestWeight_contDiff b).continuous
  have hwcs := hasCompactSupport_weight hb0.le
  have hNwpos : 0 < Nw := by
    rw [hNwd]
    refine (hwcont.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (hwcs.comp_left (g := fun x : ℝ => x ^ 2) (by simp)) (fun _ => sq_nonneg _) (x := 0) ?_
    have h0 := VerifiedHeightRungs.sinhTestWeight_ge hb0 (u := 0) (by simpa using by positivity)
    have : 0 < sinhTestWeight b 0 := lt_of_lt_of_le (by positivity) h0
    positivity
  have hNwle : Nw ≤ b ^ 5 * Iw := by
    rw [hNwd, hIwd, ← integral_const_mul]
    refine integral_mono_of_nonneg (Eventually.of_forall fun _ => sq_nonneg _) ?_
      (Eventually.of_forall fun v => ?_)
    · exact ((hwcont.mul (by fun_prop)).integrable_of_hasCompactSupport hwcs.mul_right).const_mul _
    · simp only
      have h0 := sinhTestWeight_nonneg b v
      have h1 := VerifiedHeightRungs.sinhTestWeight_le hb0 v
      have h2 := Real.one_le_cosh (δ * v)
      nlinarith only [mul_le_mul h1 h2 (by norm_num) (by positivity), h0, h1,
        mul_le_mul_of_nonneg_right h1 h0]
  have hsinh : Real.exp (2 * δ * a) ≤ 13 * Real.sinh (δ * c) ^ 2 := by
    obtain ⟨x, hxd⟩ : ∃ x, x = δ * c := ⟨_, rfl⟩
    have hx : x = δ * a - 1 / 2 := by rw [hxd, hcd, mul_sub, hδb]
    have hx32 : 3 / 2 ≤ x := by rw [hx]; linarith only [hδa]
    have he3 : (20 : ℝ) ≤ Real.exp 3 := by
      have h3 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      have h27 : (2.718 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 :=
        pow_le_pow_left₀ (by norm_num) (by linarith only [Real.exp_one_gt_d9]) 3
      rw [h3]
      norm_num at h27 ⊢
      linarith only [h27]
    have hmin : Real.exp (-x) ≤ Real.exp x / 20 := by
      have h1 : Real.exp 3 ≤ Real.exp (2 * x) := Real.exp_le_exp.mpr (by linarith only [hx32])
      have h2 : Real.exp (2 * x) * Real.exp (-x) = Real.exp x := by
        rw [← Real.exp_add]; congr 1; ring
      have h3 := mul_le_mul_of_nonneg_right (he3.trans h1) (Real.exp_pos (-x)).le
      rw [h2] at h3
      linarith only [h3]
    have hs1 : 19 / 40 * Real.exp x ≤ Real.sinh x := by
      rw [Real.sinh_eq]
      linarith only [hmin]
    have hs2 := pow_le_pow_left₀ (by positivity) hs1 2
    have he2 : Real.exp (2 * δ * a) = Real.exp x ^ 2 * Real.exp 1 := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, hx]
      congr 1
      push_cast
      ring
    rw [he2, ← hxd]
    have hex := Real.exp_one_lt_d9
    have hx2 : 0 < Real.exp x ^ 2 := by positivity
    have hprod := mul_le_mul_of_nonneg_left hex.le hx2.le
    linarith only [hprod, hs2, hx2]
  have hsinh0 : 0 ≤ Real.sinh (δ * c) := Real.sinh_nonneg_iff.mpr (by positivity)
  have hP0 : 0 ≤ P := by
    rw [hPeq]
    positivity
  -- `P² ≥ (9/5) b sinh²(δc) Nw` and `P² ≥ (81/100) sinh²(δc) b¹²`.
  have hPsq : P ^ 2 = 4 * Real.sinh (δ * c) ^ 2 * Iw ^ 2 := by rw [hPeq]; ring
  have hP1 : 9 / 5 * b * Real.sinh (δ * c) ^ 2 * Nw ≤ P ^ 2 := by
    rw [hPsq]
    have h1 : 9 / 5 * b * Nw ≤ 4 * Iw ^ 2 := by
      calc 9 / 5 * b * Nw ≤ 9 / 5 * b * (b ^ 5 * Iw) := by gcongr
        _ = 4 * (9 / 20 * b ^ 6) * Iw := by ring
        _ ≤ 4 * Iw * Iw := by gcongr
        _ = 4 * Iw ^ 2 := by ring
    calc 9 / 5 * b * Real.sinh (δ * c) ^ 2 * Nw = Real.sinh (δ * c) ^ 2 * (9 / 5 * b * Nw) := by ring
      _ ≤ Real.sinh (δ * c) ^ 2 * (4 * Iw ^ 2) := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
      _ = _ := by ring
  have hP2 : 81 / 100 * Real.sinh (δ * c) ^ 2 * b ^ 12 ≤ P ^ 2 := by
    rw [hPsq]
    have h1 : (9 / 20 * b ^ 6) ^ 2 ≤ Iw ^ 2 := pow_le_pow_left₀ (by positivity) hIw 2
    calc 81 / 100 * Real.sinh (δ * c) ^ 2 * b ^ 12 =
        4 * Real.sinh (δ * c) ^ 2 * (9 / 20 * b ^ 6) ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
  -- The test norm.
  have hN : testNorm s ≤ 84 * b ^ 6 := by
    have h1 := testNorm_twoLobeTest_le hb0.le c
    have h2 := testNorm_sinhTestWeight_le hb0.le
    have h3 : (1 : ℝ) ≤ b ^ 2 := one_le_pow₀ hb1
    have h4 : b ^ 3 ≤ b ^ 5 := pow_le_pow_right₀ hb1 (by norm_num)
    have h5 : 2 * b * (b ^ 5 + 20 * b ^ 3) ≤ 2 * b * (21 * b ^ 5) :=
      mul_le_mul_of_nonneg_left (by linarith only [h4]) (by positivity)
    have h6 : 2 * b * (21 * b ^ 5) = 42 * b ^ 6 := by ring
    linarith only [h1, h2, h5, h6]
  have hN0 := testNorm_nonneg s
  have hN2 : testNorm s ^ 2 ≤ 7056 * b ^ 12 := by
    calc testNorm s ^ 2 ≤ (84 * b ^ 6) ^ 2 := pow_le_pow_left₀ hN0 hN 2
      _ = 7056 * b ^ 12 := by ring
  -- The pair bound on each `ρ ∈ S`.
  have hpair_le : ∀ ρ ∈ S,
      (Z.Wsummand f f ρ).re + (Z.Wsummand f f (reflect ρ)).re ≤
        -(5 / 8) * (Z.mult ρ : ℝ) * P ^ 2 := by
    intro ρ hρ
    set ε := ρ.re - 1 / 2
    have hε_ge : δ ≤ ε := by dsimp [ε]; linarith only [hSδ ρ hρ]
    have hε_pos : 0 < ε := hδ.trans_le hε_ge
    have hre : ρ.re = 1 / 2 + ε := by dsimp [ε]; ring
    have hcone : (2 ≤ ε * a ∧ |ρ.im - γ₀| ≤ 1 / (4 * a)) ∨ (ε * a ≤ 1 ∧ |ρ.im - γ₀| ≤ ε / 4) :=
      Or.inl ⟨hδa.trans (mul_le_mul_of_nonneg_right hε_ge ha.le), hSγ ρ hρ⟩
    have h1 := re_Wsummand_pair_modulatedTest_le Z γ₀ (hSc ρ hρ) hε_pos hre
      hs_cd.continuous hs_supp hs_odd hs_nn hcone
    have hP_mono : P ≤ ∫ u, s u * Real.sinh (ε * u) := by
      have hcs : HasCompactSupport s := hasCompactSupport_of_support_subset_abs hs_supp
      refine integral_mono
        ((hs_cd.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.mul_right)
        ((hs_cd.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hcs.mul_right)
        fun u => ?_
      rcases le_or_gt 0 u with hu | hu
      · exact mul_le_mul_of_nonneg_left
          (Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_right hε_ge hu)) (hs_nn u hu)
      · have hsu : s u = -s (-u) := by linarith only [hs_odd u]
        simp only
        rw [hsu, show δ * u = -(δ * -u) by ring, show ε * u = -(ε * -u) by ring,
          Real.sinh_neg, Real.sinh_neg, neg_mul_neg, neg_mul_neg]
        exact mul_le_mul_of_nonneg_left
          (Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_right hε_ge (by linarith only [hu])))
          (hs_nn (-u) (by linarith only [hu]))
    have hP2' := pow_le_pow_left₀ hP0 hP_mono 2
    have hm0 : (0 : ℝ) ≤ Z.mult ρ := Nat.cast_nonneg _
    nlinarith only [h1, hP2', hm0, mul_le_mul_of_nonneg_left hP2' hm0]
  -- Split the Weil form.
  set Wall_sub : Finset Z.carrier := W_all.subtype (· ∈ Z.carrier)
  let Wall_compl : Set Z.carrier := ((Wall_sub : Set Z.carrier))ᶜ
  have hre_sum : Summable (fun τ : Z.carrier => (Z.Wsummand f f τ).re) :=
    (Complex.hasSum_re hsumm.hasSum).summable
  have hsplit_tsum : (Z.W f f).re =
      (∑ τ ∈ Wall_sub, (Z.Wsummand f f τ).re) +
        ∑' τ : Wall_compl, (Z.Wsummand f f τ).re := by
    rw [ZeroConfig.W, Complex.re_tsum hsumm, ← hre_sum.sum_add_tsum_compl (s := Wall_sub)]
  have hWall_sum : (∑ τ ∈ Wall_sub, (Z.Wsummand f f τ).re) =
      ∑ ρ ∈ W_all, (Z.Wsummand f f ρ).re := by
    dsimp only [Wall_sub]
    exact Finset.sum_subtype_of_mem (fun ρ => (Z.Wsummand f f ρ).re)
      fun ρ hρ => ((hmem_Wall ρ).mp hρ).1
  have hWall_part : W_all = (S ∪ S') ∪ F_near := by
    ext ρ
    simp only [F_near, Finset.mem_union, Finset.mem_sdiff]
    exact ⟨fun h => by tauto, fun h => h.elim (fun h1 => h1.elim (hsub_S ·) (hsub_S' ·)) And.left⟩
  have hdisj_F : Disjoint (S ∪ S') F_near := Finset.disjoint_sdiff
  have hWall_decomp : (∑ ρ ∈ W_all, (Z.Wsummand f f ρ).re) =
      (∑ ρ ∈ S, ((Z.Wsummand f f ρ).re + (Z.Wsummand f f (reflect ρ)).re)) +
        ∑ ρ ∈ F_near, (Z.Wsummand f f ρ).re := by
    rw [hWall_part, Finset.sum_union hdisj_F, Finset.sum_union hdisj_SS',
      Finset.sum_image (fun x _ y _ h => hrefl_inj h), ← Finset.sum_add_distrib]
  obtain ⟨MS, hMSd⟩ : ∃ M, M = ∑ ρ ∈ S, (Z.mult ρ : ℝ) := ⟨_, rfl⟩
  rw [← hMSd]
  have hk1 : 1 ≤ MS := by
    obtain ⟨ρ₀, hρ₀⟩ := hSne
    have h1 : (1 : ℝ) ≤ Z.mult ρ₀ := by exact_mod_cast Z.one_le_mult ρ₀ (hSc ρ₀ hρ₀)
    rw [hMSd]
    exact h1.trans (Finset.single_le_sum (f := fun ρ => (Z.mult ρ : ℝ))
      (fun _ _ => Nat.cast_nonneg _) hρ₀)
  have hS_bound : ∑ ρ ∈ S, ((Z.Wsummand f f ρ).re + (Z.Wsummand f f (reflect ρ)).re) ≤
      -(5 / 8) * MS * P ^ 2 := by
    refine (Finset.sum_le_sum hpair_le).trans_eq ?_
    rw [hMSd, Finset.mul_sum, Finset.sum_mul]
  -- The near sea.
  obtain ⟨K, hKd⟩ : ∃ K : ℕ, K = ⌈3 * A₀ * Λ⌉₊ := ⟨_, rfl⟩
  have hK_le : (K : ℝ) ≤ 4 * A₀ * Λ := by
    have hA₀Λ : 1 ≤ A₀ * Λ := by nlinarith only [hA₀, hΛ1]
    have hlt := (Nat.ceil_lt_add_one (show 0 ≤ 3 * A₀ * Λ by positivity)).le
    rw [hKd]
    linarith only [hlt, hA₀Λ]
  have hFc : ∀ ρ ∈ F_near, ρ ∈ Z.carrier := fun ρ hρ =>
    ((hmem_Wall ρ).mp (Finset.sdiff_subset hρ)).1
  have hFr : ∀ ρ ∈ F_near, |ρ.im - γ₀| ≤ R := fun ρ hρ =>
    ((hmem_Wall ρ).mp (Finset.sdiff_subset hρ)).2
  have hFσ : ∀ ρ ∈ F_near, |ρ.re - 1 / 2| ≤ σ := fun ρ hρ => by
    obtain ⟨hw, hn⟩ := Finset.mem_sdiff.mp hρ
    rw [Finset.mem_union, not_or] at hn
    exact hsea ρ (hFc ρ hρ) hn.1 hn.2
  have hstep : 2 * π / (2 * π * (2 * b + 1)) = 1 / (2 * b + 1) := by field_simp
  have hstep0 : 0 < 1 / (2 * b + 1) := by positivity
  have hstep1 : 1 / (2 * b + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith only [hb0]
  have hcell : ∀ n : ℤ, ∑ ρ ∈ F_near.filter (fun ρ => ⌊ρ.im / (2 * π / (2 * π * (2 * b + 1)))⌋ = n),
      Z.mult ρ ≤ K := by
    intro n
    have hsub : F_near.filter (fun ρ => ⌊ρ.im / (2 * π / (2 * π * (2 * b + 1)))⌋ = n) ⊆
        F_near.filter (fun ρ => |ρ.im - (n : ℝ) * (1 / (2 * b + 1))| ≤ 1) := by
      intro ρ hρ
      obtain ⟨hρF, hρn⟩ := Finset.mem_filter.mp hρ
      refine Finset.mem_filter.mpr ⟨hρF, ?_⟩
      rw [hstep] at hρn
      have h1 : ((⌊ρ.im / (1 / (2 * b + 1))⌋ : ℤ) : ℝ) ≤ ρ.im / (1 / (2 * b + 1)) := Int.floor_le _
      have h2 : ρ.im / (1 / (2 * b + 1)) < ((⌊ρ.im / (1 / (2 * b + 1))⌋ : ℤ) : ℝ) + 1 :=
        Int.lt_floor_add_one _
      rw [hρn] at h1 h2
      have h1' := (le_div_iff₀ hstep0).mp h1
      have h2' := (div_lt_iff₀ hstep0).mp h2
      rw [abs_le]
      constructor <;> nlinarith only [h1', h2', hstep1, hstep0]
    refine (Finset.sum_le_sum_of_subset hsub).trans ?_
    have h := sum_mult_unit_ball_le Z hA₀ hloc hR0 F_near hFc hFr ((n : ℝ) * (1 / (2 * b + 1)))
    rw [← hΛd] at h
    rw [hKd]
    exact h
  have hNear := sum_norm_Wsummand_twoLobe_le Z γ₀ hb1 hc0 hσ F_near hFσ hcell
  rw [← hNwd, habc] at hNear
  obtain ⟨Eσ, hEσ⟩ : ∃ E, E = Real.exp (2 * σ * a) := ⟨_, rfl⟩
  have hEσ0 : 0 < Eσ := by rw [hEσ]; exact Real.exp_pos _
  rw [← hEσ] at hNear
  have hF_bound : ∑ ρ ∈ F_near, (Z.Wsummand f f ρ).re ≤
      4 * Real.exp 1 * Eσ * (K * (2 * π * (2 * b + 1) * Nw)) :=
    (Finset.sum_le_sum fun ρ _ => Complex.re_le_norm _).trans hNear
  -- The far tail.
  have hfar_bound : (∑' τ : Wall_compl, (Z.Wsummand f f τ).re) ≤
      384 * A₀ * L₀ * testNorm s ^ 2 * (Eσ / (1 + R)) := by
    set c_far : Z.carrier → ℝ := fun τ =>
      16 * testNorm s ^ 2 * (Eσ / (1 + R)) * ((Z.mult τ : ℝ) / (1 + |(τ : ℂ).im - γ₀|) ^ 3)
    have hc_sum : Summable c_far := hwsum.mul_left _
    have hc_nn : ∀ τ : Z.carrier, 0 ≤ c_far τ := fun τ => by
      dsimp only [c_far]; positivity
    have hpt_far : ∀ τ : Wall_compl, (Z.Wsummand f f τ).re ≤ c_far τ.1 := fun τ => by
      have hnotW : (τ.1 : ℂ) ∉ W_all := fun hm =>
        τ.2 (Finset.mem_coe.mpr (Finset.mem_subtype.mpr hm))
      have hfar : R < |(τ.1 : ℂ).im - γ₀| := by
        by_contra hle
        rw [not_lt] at hle
        exact hnotW ((hmem_Wall _).mpr ⟨τ.1.2, hle⟩)
      have hdepth : |(τ.1 : ℂ).re - 1 / 2| ≤ σ :=
        hsea _ τ.1.2 (fun h => hnotW (hsub_S h)) (fun h => hnotW (hsub_S' h))
      refine (Complex.re_le_norm _).trans
        ((norm_Wsummand_modulatedTest_le Z γ₀ hs_cd hs_supp (τ.1 : ℂ)).trans ?_)
      dsimp only [c_far]
      have hm : (0 : ℝ) ≤ Z.mult (τ.1 : ℂ) := Nat.cast_nonneg _
      have hexp : Real.exp (|1 / 2 - (τ.1 : ℂ).re| * a) ^ 2 ≤ Eσ := by
        rw [hEσ, ← Real.exp_nat_mul]
        refine Real.exp_le_exp.mpr ?_
        have h1 : |1 / 2 - (τ.1 : ℂ).re| * a ≤ σ * a :=
          mul_le_mul_of_nonneg_right (by rwa [abs_sub_comm]) ha.le
        push_cast
        linarith only [h1]
      obtain ⟨D, hD⟩ : ∃ D, D = 1 + |(τ.1 : ℂ).im - γ₀| := ⟨_, rfl⟩
      rw [← hD]
      have hDR : 1 + R ≤ D := by rw [hD]; linarith only [hfar]
      have hR0' : 0 < 1 + R := by linarith only [hR0]
      have hD0 : 0 < D := by linarith only [hDR, hR0']
      rw [div_le_iff₀ (by positivity)]
      calc (Z.mult (τ.1 : ℂ) : ℝ) * (Real.exp (|1 / 2 - (τ.1 : ℂ).re| * a) ^ 2 *
            (16 * testNorm s ^ 2))
          ≤ (Z.mult (τ.1 : ℂ) : ℝ) * (Eσ * (16 * testNorm s ^ 2)) := by gcongr
        _ = 16 * testNorm s ^ 2 * (Eσ / (1 + R)) * ((Z.mult (τ.1 : ℂ) : ℝ) / D ^ 3) *
              ((1 + R) * D ^ 3) := by field_simp
        _ ≤ 16 * testNorm s ^ 2 * (Eσ / (1 + R)) * ((Z.mult (τ.1 : ℂ) : ℝ) / D ^ 3) *
              (D * D ^ 3) := by gcongr
        _ = 16 * testNorm s ^ 2 * (Eσ / (1 + R)) * ((Z.mult (τ.1 : ℂ) : ℝ) / D ^ 3) * D ^ 4 := by
            ring
    have hle1 : (∑' τ : Wall_compl, (Z.Wsummand f f τ).re) ≤ ∑' τ : Wall_compl, c_far τ.1 :=
      Summable.tsum_le_tsum hpt_far (hre_sum.subtype _) (hc_sum.subtype _)
    have hle2 : (∑' τ : Wall_compl, c_far τ.1) ≤ ∑' τ : Z.carrier, c_far τ := by
      have hdecomp := hc_sum.sum_add_tsum_compl (s := Wall_sub)
      have hfin0 : 0 ≤ ∑ τ ∈ Wall_sub, c_far τ := Finset.sum_nonneg fun τ _ => hc_nn τ
      linarith only [hdecomp, hfin0]
    have hle3 : ∑' τ : Z.carrier, c_far τ ≤
        16 * testNorm s ^ 2 * (Eσ / (1 + R)) * (24 * A₀ * L₀) := by
      dsimp only [c_far]
      rw [tsum_mul_left, hL₀]
      exact mul_le_mul_of_nonneg_left hwle (by positivity)
    calc (∑' τ : Wall_compl, (Z.Wsummand f f τ).re)
        ≤ 16 * testNorm s ^ 2 * (Eσ / (1 + R)) * (24 * A₀ * L₀) := hle1.trans (hle2.trans hle3)
      _ = _ := by ring
  have hW := hpos f hf_cd hf_supp
  rw [hsplit_tsum, hWall_sum, hWall_decomp] at hW
  -- The far tail is at most `P²/8`.
  have hEσX : Eσ ≤ Real.exp (2 * δ * a) := by
    rw [hEσ]
    exact Real.exp_le_exp.mpr (by nlinarith only [hσδ, ha])
  have hFar : 384 * A₀ * L₀ * testNorm s ^ 2 * (Eσ / (1 + R)) ≤ 1 / 8 * P ^ 2 := by
    have hA₀L₀ : 0 < A₀ * L₀ := by nlinarith only [hA₀, hL₀1]
    have hfrac : A₀ * L₀ / (1 + R) ≤ 1 / (4 * 10 ^ 8) := by
      rw [div_le_div_iff₀ (by linarith only [hR0]) (by norm_num), hRd]
      nlinarith only [hA₀L₀]
    have hE : Eσ ≤ 13 * Real.sinh (δ * c) ^ 2 := hEσX.trans hsinh
    have hb12 : (0 : ℝ) < b ^ 12 := by positivity
    calc 384 * A₀ * L₀ * testNorm s ^ 2 * (Eσ / (1 + R))
        = 384 * (A₀ * L₀ / (1 + R)) * testNorm s ^ 2 * Eσ := by ring
      _ ≤ 384 * (1 / (4 * 10 ^ 8)) * (7056 * b ^ 12) * (13 * Real.sinh (δ * c) ^ 2) := by
          gcongr
      _ ≤ 1 / 8 * (81 / 100 * Real.sinh (δ * c) ^ 2 * b ^ 12) := by
          have h0 : 0 ≤ Real.sinh (δ * c) ^ 2 * b ^ 12 := by positivity
          nlinarith only [h0]
      _ ≤ 1 / 8 * P ^ 2 := by gcongr
  -- The final comparison.
  have hP2nn : 0 ≤ P ^ 2 := sq_nonneg _
  have hmain : 1 / 2 * MS * P ^ 2 ≤ 4 * Real.exp 1 * Eσ * (K * (2 * π * (2 * b + 1) * Nw)) := by
    have h1 : 1 * P ^ 2 ≤ MS * P ^ 2 := mul_le_mul_of_nonneg_right hk1 hP2nn
    linarith only [hW, hS_bound, hF_bound, hfar_bound, hFar, h1]
  have hbNw : 0 < b * Nw := mul_pos hb0 hNwpos
  obtain ⟨X, hXd⟩ : ∃ X, X = Real.exp (2 * δ * a) := ⟨_, rfl⟩
  rw [← hXd] at hsinh hEσX
  have hX0 : 0 < X := by rw [hXd]; exact Real.exp_pos _
  have hPX : 9 / 65 * X * (b * Nw) ≤ P ^ 2 := by
    have h0 : 9 / 65 * X * (b * Nw) ≤ 9 / 5 * b * Real.sinh (δ * c) ^ 2 * Nw := by
      have h1 := mul_le_mul_of_nonneg_left hsinh (show 0 ≤ 9 / 65 * (b * Nw) by positivity)
      calc 9 / 65 * X * (b * Nw) = 9 / 65 * (b * Nw) * X := by ring
        _ ≤ 9 / 65 * (b * Nw) * (13 * Real.sinh (δ * c) ^ 2) := h1
        _ = _ := by ring
    exact h0.trans hP1
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hNearbd : 4 * Real.exp 1 * Eσ * (K * (2 * π * (2 * b + 1) * Nw)) ≤
      823 * (A₀ * Λ) * Eσ * (b * Nw) := by
    have he := Real.exp_one_lt_d9
    have hpi := Real.pi_lt_d2
    have h3b : 2 * b + 1 ≤ 3 * b := by linarith only [hb1]
    have hA₀Λ : 0 ≤ A₀ * Λ := by positivity
    calc 4 * Real.exp 1 * Eσ * (K * (2 * π * (2 * b + 1) * Nw))
        ≤ 4 * Real.exp 1 * Eσ * ((4 * A₀ * Λ) * (2 * π * (3 * b) * Nw)) := by gcongr
      _ = (96 * (Real.exp 1 * π)) * (A₀ * Λ) * Eσ * (b * Nw) := by ring
      _ ≤ 823 * (A₀ * Λ) * Eσ * (b * Nw) := by
          have hprod : Real.exp 1 * π ≤ 2.72 * 3.15 :=
            mul_le_mul (by linarith only [he]) hpi.le Real.pi_pos.le (by norm_num)
          have hle : 96 * (Real.exp 1 * π) ≤ 823 := by
            norm_num at hprod ⊢
            linarith only [hprod]
          gcongr
  have hcancel : 9 / 130 * MS * X ≤ 823 * (A₀ * Λ) * Eσ := by
    refine le_of_mul_le_mul_right ?_ hbNw
    have h1 : MS * (9 / 65 * X * (b * Nw)) ≤ MS * P ^ 2 :=
      mul_le_mul_of_nonneg_left hPX (by linarith only [hk1])
    linarith only [h1, hmain, hNearbd]
  have hXE : Real.exp (2 * (δ - σ) * a) * Eσ = X := by
    rw [hEσ, hXd, ← Real.exp_add]
    congr 1
    ring
  have hfinal : MS * Real.exp (2 * (δ - σ) * a) * Eσ ≤ 12000 * A₀ * Λ * Eσ := by
    rw [mul_assoc MS, hXE]
    have hA₀Λ : 0 ≤ A₀ * Λ := by positivity
    have h130 := mul_le_mul_of_nonneg_left hcancel (show (0 : ℝ) ≤ 130 / 9 by norm_num)
    have hslack : 130 / 9 * (823 * (A₀ * Λ) * Eσ) ≤ 12000 * A₀ * Λ * Eσ := by
      have h0 : 0 ≤ A₀ * Λ * Eσ := by positivity
      nlinarith only [h0]
    calc MS * X = 130 / 9 * (9 / 130 * MS * X) := by ring
      _ ≤ _ := h130
      _ ≤ _ := hslack
  exact le_of_mul_le_mul_right hfinal hEσ0

/-- **Explicit form for ζ.** With the explicit count `N(t,t+1] ≤ 240 log(|t|+3)`, a coherent cluster of
ζ zeros in a sea of depth at most `σ ≤ δ` satisfies the absolute bound below any positive aperture. -/
theorem zeta_cluster_absolute_bound {γ₀ a δ σ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) (hδa : 2 ≤ δ * a)
    (hσ : 0 ≤ σ) (hσδ : σ ≤ δ) (hpos : ZetaWindowPositive a)
    (S : Finset ℂ) (hSne : S.Nonempty) (hSc : ∀ ρ ∈ S, ρ ∈ zetaZeroConfig.carrier)
    (hSδ : ∀ ρ ∈ S, 1 / 2 + δ ≤ ρ.re) (hSγ : ∀ ρ ∈ S, |ρ.im - γ₀| ≤ 1 / (4 * a))
    (hsea : ∀ ρ ∈ zetaZeroConfig.carrier, ρ ∉ S → ρ ∉ S.image reflect → |ρ.re - 1 / 2| ≤ σ) :
    (∑ ρ ∈ S, (zetaZeroConfig.mult ρ : ℝ)) * Real.exp (2 * (δ - σ) * a) ≤
      12000 * 240 * Real.log (|γ₀| + 4 * 10 ^ 8 * 240 * Real.log (|γ₀| + 3) + 6) :=
  windowPositiveAt_cluster_absolute_bound zetaZeroConfig (by norm_num) zeta_unit_count_le_240
    hδ hδ1 hδa hσ hσδ ((windowPositiveAt_zeta_iff _).mpr hpos) S hSne hSc hSδ hSγ hsea

end GaloisForLFunctions.WindowVisibilityLaw
