import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalThresholdOfAWindow
import GaloisForLFunctions.WindowVisibilityLaw.OnsetApertureAndPositivityDictionary
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.BoundedWeilEnergyUpgradesL1LimitsToStrongLimits
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheDyadicReserveHasAnExplicitConstant
import GaloisForLFunctions.RHTower.WeilMarkovArchimedeanWideTestNegativity

/-!
# The continuum window threshold grows exponentially in the onset aperture

Suppose `windowThreshold A₀ = ⊤` (`Q ≥ 0` on `IsWindowTest A₀`). Partitioning any `C²` compactly
supported profile `F` vanishing on `(0, ∞)` at `[−A₀, −(A₀ − 1)]` via
`θ₁(u) = sin((π/2) σ(u + A₀))` and `θ₂(u) = cos((π/2) σ(u + A₀))` (`θ₁² + θ₂² = 1`) localizes all
three channels of `weilQuad (θ₁ · F) − weilQuad F` to `u ≤ −(A₀ − 1)`, where the exponential
weight `e^{−8u}` exceeds `e^{8(A₀ − 1)}` while prime jumps crossing `−(A₀ − 1)` satisfy
`n ≤ e^{−u}`:

1. **Archimedean IMS commutator** (`archForm_windowLeftCutoff_sub_le`): the diagonal term
   `2 γ₀ ∫ F²` cancels identically against `archForm (θ₁ F) + archForm (θ₂ F)`, and the Lévy jump
   commutator vanishes for `u ≥ −(A₀ − 1)` (`y > 0`), costing `O(e^{−4 A₀}) M₈(F)`.
2. **Prime three-halves bound** (`primeSum_sub_windowLeftCutoff_le`): writing `F = θ₁ F + H̃₂`
   with `H̃₂` supported in `(−∞, −(A₀ − 1)]`, `H̃₂(u) F(u + log n)` forces `n ≤ e^{−u}` (`O(e^{−3 A₀}) M₈(F)`
   via `∑ Λ(n)/n^{3/2}`), while `(θ₁ F)(u) H̃₂(u + log n)` forces `log n ≤ 1` (`O(e^{−8 A₀}) M₈(F)`).
3. **Pole moment cross** (`pole_windowLeftCutoff_sub_le`): `2 C(g)² − 2 S(g)² = 2 I_+(g) I_−(g)`
   pairs one `H̃₂` moment (`O(e^{−(7/2) A₀} √M₈(F))`) against an unshifted moment (`O(√M₈(F))`).

Combining all three channels proves `weilQuad (windowLeftCutoff A₀ * F) − weilQuad F ≤
windowCutoffLocalizationConstant * e^{−3 A₀} * exponentialMass 8 F`, whence
`windowThresholdExponentialConstant * e^{3 A₀} ≤ windowThreshold A` for every `A : ℝ` and
`windowThresholdExponentialConstant * e^{6 a} ≤ ⨅ A ≥ 0, windowThreshold A` for every `0 ≤ a`
with `(a : EReal) ≤ onsetAperture zetaZeroConfig` (including `a = zetaContactAperture` off RH).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Zeta23 RHTower

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open CohomologyOfWindowsOfSpecZ WindowTowerOfSpecZ SpacingScaleHarmonicAnalysis
  CriticalArithmeticCorrelationTheory WindowVisibilityLaw SquareRootThreshold
  ArithmeticCastelnuovoSeveri ArithmeticIncidencePositivity

/-! ### 1. Smooth trigonometric left cutoff on `[−A₀, −(A₀ − 1)]` -/

/-- Smooth cutoff equal to `0` on `(−∞, −A₀]` and `1` on `[−(A₀ − 1), ∞)`. -/
def windowLeftCutoff (A₀ u : ℝ) : ℝ :=
  Real.sin ((Real.pi / 2) * Real.smoothTransition (u + A₀))

/-- Complementary cosine cutoff satisfying `windowLeftCutoff A₀ u ^ 2 + windowLeftCosCutoff A₀ u ^ 2 = 1`. -/
def windowLeftCosCutoff (A₀ u : ℝ) : ℝ :=
  Real.cos ((Real.pi / 2) * Real.smoothTransition (u + A₀))

/-- Explicit universal localization constant for `weilQuad (windowLeftCutoff A₀ · F) − weilQuad F`. -/
def windowCutoffLocalizationConstant : ℝ :=
  Real.exp 3 * (576 * Real.pi ^ 2 + 2 * |gammaHardyPhaseRate 0| +
    2 * (1 + Real.exp 1) * vonMangoldtThreeHalvesMass + 4)

/-- Explicit universal prefactor in the exponential floor `c₀ e^{3 A₀} ≤ windowThreshold A`. -/
def windowThresholdExponentialConstant : ℝ :=
  min (apertureIndependentThreshold * Real.exp (-6))
    (7 * tiltedJordanOne / (splineAtom * windowCutoffLocalizationConstant))

theorem windowCutoffLocalizationConstant_pos : 0 < windowCutoffLocalizationConstant := by
  have hv := vonMangoldtThreeHalvesMass_nonneg
  have hpi := Real.pi_pos
  unfold windowCutoffLocalizationConstant
  positivity

theorem windowThresholdExponentialConstant_pos : 0 < windowThresholdExponentialConstant := by
  have hR0 : 0 < apertureIndependentThreshold := by
    have hJ := tiltedJordanOne_pos
    have hκ := splineAtom_pos
    have hF := exponentialWeilFloor_pos (by norm_num : (1 : ℝ) < 8)
    unfold apertureIndependentThreshold
    positivity
  have hJ := tiltedJordanOne_pos
  have hκ := splineAtom_pos
  have hC := windowCutoffLocalizationConstant_pos
  unfold windowThresholdExponentialConstant
  exact lt_min (by positivity) (by positivity)

theorem contDiff_windowLeftCutoff (A₀ : ℝ) : ContDiff ℝ 2 (windowLeftCutoff A₀) := by
  unfold windowLeftCutoff
  have hs : ContDiff ℝ 2 (fun u : ℝ => Real.smoothTransition (u + A₀)) :=
    (Real.smoothTransition.contDiff (n := 2)).comp (contDiff_id.add contDiff_const)
  exact Real.contDiff_sin.comp (contDiff_const.mul hs)

theorem contDiff_windowLeftCosCutoff (A₀ : ℝ) : ContDiff ℝ 2 (windowLeftCosCutoff A₀) := by
  unfold windowLeftCosCutoff
  have hs : ContDiff ℝ 2 (fun u : ℝ => Real.smoothTransition (u + A₀)) :=
    (Real.smoothTransition.contDiff (n := 2)).comp (contDiff_id.add contDiff_const)
  exact Real.contDiff_cos.comp (contDiff_const.mul hs)

theorem windowLeftCutoff_bounds (A₀ u : ℝ) :
    0 ≤ windowLeftCutoff A₀ u ∧ windowLeftCutoff A₀ u ≤ 1 := by
  unfold windowLeftCutoff
  have hs0 : 0 ≤ Real.smoothTransition (u + A₀) := Real.smoothTransition.nonneg _
  have hs1 : Real.smoothTransition (u + A₀) ≤ 1 := Real.smoothTransition.le_one _
  have hpi := Real.pi_pos
  exact ⟨Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by nlinarith),
    Real.sin_le_one _⟩

theorem windowLeftCosCutoff_bounds (A₀ u : ℝ) :
    0 ≤ windowLeftCosCutoff A₀ u ∧ windowLeftCosCutoff A₀ u ≤ 1 := by
  unfold windowLeftCosCutoff
  have hs0 : 0 ≤ Real.smoothTransition (u + A₀) := Real.smoothTransition.nonneg _
  have hs1 : Real.smoothTransition (u + A₀) ≤ 1 := Real.smoothTransition.le_one _
  have hpi := Real.pi_pos
  exact ⟨Real.cos_nonneg_of_mem_Icc ⟨by nlinarith, by nlinarith⟩, Real.cos_le_one _⟩

theorem windowLeftCutoff_sq_add_cos_sq (A₀ u : ℝ) :
    windowLeftCutoff A₀ u ^ 2 + windowLeftCosCutoff A₀ u ^ 2 = 1 :=
  Real.sin_sq_add_cos_sq _

theorem windowLeftCutoff_eq_zero_of_le {A₀ u : ℝ} (hu : u ≤ -A₀) :
    windowLeftCutoff A₀ u = 0 := by
  unfold windowLeftCutoff
  rw [Real.smoothTransition.zero_of_nonpos (by linarith), mul_zero, Real.sin_zero]

theorem windowLeftCutoff_eq_one_of_ge {A₀ u : ℝ} (hu : -(A₀ - 1) ≤ u) :
    windowLeftCutoff A₀ u = 1 := by
  unfold windowLeftCutoff
  rw [Real.smoothTransition.one_of_one_le (by linarith), mul_one, Real.sin_pi_div_two]

theorem windowLeftCosCutoff_eq_zero_of_ge {A₀ u : ℝ} (hu : -(A₀ - 1) ≤ u) :
    windowLeftCosCutoff A₀ u = 0 := by
  unfold windowLeftCosCutoff
  rw [Real.smoothTransition.one_of_one_le (by linarith), mul_one, Real.cos_pi_div_two]

theorem isWindowTest_windowLeftCutoff_mul (A₀ : ℝ) {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hF0 : ∀ u, 0 < u → F u = 0) :
    IsWindowTest A₀ (fun u => windowLeftCutoff A₀ u * F u) where
  contDiff := (contDiff_windowLeftCutoff A₀).mul hF
  vanish u hu := by
    rw [mem_Icc, not_and_or, not_le, not_le] at hu
    rcases hu with hlt | hgt
    · rw [windowLeftCutoff_eq_zero_of_le hlt.le, zero_mul]
    · rw [hF0 u hgt, mul_zero]

private lemma windowLeftCutoff_diff_sq_le (A₀ u y : ℝ) :
    (windowLeftCutoff A₀ u - windowLeftCutoff A₀ (u + y)) ^ 2 +
      (windowLeftCosCutoff A₀ u - windowLeftCosCutoff A₀ (u + y)) ^ 2 ≤
      32 * Real.pi ^ 2 * y ^ 2 := by
  have hlip_s : LipschitzWith 8 Real.smoothTransition :=
    lipschitzWith_of_nnnorm_deriv_le
      ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num)) fun x => by
        rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs]
        exact ExplicitShell.abs_deriv_smoothTransition_le x
  have hs_diff : |Real.smoothTransition (u + A₀) - Real.smoothTransition (u + y + A₀)| ≤ 8 * |y| := by
    have h := hlip_s.dist_le_mul (u + A₀) (u + y + A₀)
    rw [Real.dist_eq, Real.dist_eq, NNReal.coe_ofNat, show (u + A₀) - (u + y + A₀) = -y by ring,
      abs_neg] at h
    exact h
  set α := (Real.pi / 2) * Real.smoothTransition (u + A₀)
  set β := (Real.pi / 2) * Real.smoothTransition (u + y + A₀)
  have hαβ : |α - β| ≤ 4 * Real.pi * |y| := by
    have hpi := Real.pi_pos
    have hid : α - β = (Real.pi / 2) *
        (Real.smoothTransition (u + A₀) - Real.smoothTransition (u + y + A₀)) := by
      dsimp only [α, β]; ring
    rw [hid, abs_mul, abs_of_pos (by positivity)]
    have hm := mul_le_mul_of_nonneg_left hs_diff (by positivity : 0 ≤ Real.pi / 2)
    linarith only [hm]
  have hsin : |Real.sin α - Real.sin β| ≤ |α - β| := Real.abs_sin_sub_sin_le α β
  have hcos : |Real.cos α - Real.cos β| ≤ |α - β| := Real.abs_cos_sub_cos_le α β
  have hs2 : (Real.sin α - Real.sin β) ^ 2 ≤ (4 * Real.pi * y) ^ 2 := by
    have h1 := pow_le_pow_left₀ (abs_nonneg _) (hsin.trans hαβ) 2
    rwa [sq_abs, mul_pow, sq_abs, ← mul_pow] at h1
  have hc2 : (Real.cos α - Real.cos β) ^ 2 ≤ (4 * Real.pi * y) ^ 2 := by
    have h1 := pow_le_pow_left₀ (abs_nonneg _) (hcos.trans hαβ) 2
    rwa [sq_abs, mul_pow, sq_abs, ← mul_pow] at h1
  change (Real.sin α - Real.sin β) ^ 2 + (Real.cos α - Real.cos β) ^ 2 ≤ 32 * Real.pi ^ 2 * y ^ 2
  linarith only [hs2, hc2, (by ring : 2 * (4 * Real.pi * y) ^ 2 = 32 * Real.pi ^ 2 * y ^ 2)]

/-! ### 2. Channel 1: Archimedean IMS commutator -/

private lemma integrable_exp_eight_mul_sq {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F) :
    Integrable fun u => Real.exp (-(8 * u)) * F u ^ 2 := by
  have hF2c : HasCompactSupport (fun u => F u ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hFc ⊢
    exact hFc.mono fun u hu => by change F u = 0 at hu; change F u ^ 2 = 0; rw [hu]; norm_num
  exact ((by fun_prop : Continuous fun u => Real.exp (-(8 * u))).mul (hF.pow 2)).integrable_of_hasCompactSupport
    hF2c.mul_left

private lemma levy_shift_commutator_integral_le {A₀ : ℝ} (hA₀ : 2 < A₀) {F : ℝ → ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) (hF0 : ∀ u, 0 < u → F u = 0)
    {y : ℝ} (hy : 0 < y) :
    let H₁ := fun u => windowLeftCutoff A₀ u * F u
    let H₂ := fun u => windowLeftCosCutoff A₀ u * F u
    (∫ u, (H₁ u - H₁ (u + y)) ^ 2) + (∫ u, (H₂ u - H₂ (u + y)) ^ 2) -
      (∫ u, (F u - F (u + y)) ^ 2) ≤
      32 * Real.pi ^ 2 * Real.exp (-4 * (A₀ - 1)) * exponentialMass 8 F * y ^ 2 := by
  intro H₁ H₂
  set b := A₀ - 1
  have hb0 : 0 < b := by dsimp only [b]; linarith
  have ishift (φ : ℝ → ℝ) (hc : Continuous φ) (hs : HasCompactSupport φ) :
      Integrable fun u => (φ u - φ (u + y)) ^ 2 := by
    have hcs : HasCompactSupport (fun u => φ u - φ (u + y)) :=
      hs.sub (hs.comp_homeomorph (Homeomorph.addRight y))
    have hcs2 : HasCompactSupport (fun u => (φ u - φ (u + y)) ^ 2) := by
      rw [hasCompactSupport_iff_eventuallyEq] at hcs ⊢
      exact hcs.mono fun u hu => by
        change φ u - φ (u + y) = 0 at hu; change (φ u - φ (u + y)) ^ 2 = 0; rw [hu]; norm_num
    exact ((hc.sub (hc.comp (continuous_add_const y))).pow 2).integrable_of_hasCompactSupport hcs2
  have hH₁c : Continuous H₁ := (contDiff_windowLeftCutoff A₀).continuous.mul hF
  have hH₂c : Continuous H₂ := (contDiff_windowLeftCosCutoff A₀).continuous.mul hF
  have hH₁s : HasCompactSupport H₁ := hFc.mul_left
  have hH₂s : HasCompactSupport H₂ := hFc.mul_left
  have i1 := ishift H₁ hH₁c hH₁s
  have i2 := ishift H₂ hH₂c hH₂s
  have i12 : Integrable fun u => (H₁ u - H₁ (u + y)) ^ 2 + (H₂ u - H₂ (u + y)) ^ 2 := i1.add i2
  have iF := ishift F hF hFc
  rw [← integral_add i1 i2, ← integral_sub i12 iF]
  have iE := integrable_exp_eight_mul_sq hF hFc
  have iEy : Integrable fun u => Real.exp (-(8 * (u + y))) * F (u + y) ^ 2 := iE.comp_add_right y
  have iEEy : Integrable fun u =>
      Real.exp (-(8 * u)) * F u ^ 2 + Real.exp (-(8 * (u + y))) * F (u + y) ^ 2 := iE.add iEy
  set K := 16 * Real.pi ^ 2 * Real.exp (-4 * b) * y ^ 2
  have hK0 : 0 ≤ K := by dsimp only [K]; positivity
  have hpt : ∀ u, ((H₁ u - H₁ (u + y)) ^ 2 + (H₂ u - H₂ (u + y)) ^ 2) - (F u - F (u + y)) ^ 2 ≤
      K * (Real.exp (-(8 * u)) * F u ^ 2 + Real.exp (-(8 * (u + y))) * F (u + y) ^ 2) := by
    intro u
    have hsq_u := windowLeftCutoff_sq_add_cos_sq A₀ u
    have hsq_uy := windowLeftCutoff_sq_add_cos_sq A₀ (u + y)
    have hid : ((H₁ u - H₁ (u + y)) ^ 2 + (H₂ u - H₂ (u + y)) ^ 2) - (F u - F (u + y)) ^ 2 =
        ((windowLeftCutoff A₀ u - windowLeftCutoff A₀ (u + y)) ^ 2 +
          (windowLeftCosCutoff A₀ u - windowLeftCosCutoff A₀ (u + y)) ^ 2) * (F u * F (u + y)) := by
      dsimp only [H₁, H₂]
      linear_combination (F u ^ 2 - F u * F (u + y)) * hsq_u +
        (F (u + y) ^ 2 - F u * F (u + y)) * hsq_uy
    rw [hid]
    by_cases hub : -b ≤ u
    · have hub' : -(A₀ - 1) ≤ u := hub
      have huby : -(A₀ - 1) ≤ u + y := by linarith
      rw [windowLeftCutoff_eq_one_of_ge hub', windowLeftCutoff_eq_one_of_ge huby,
        windowLeftCosCutoff_eq_zero_of_ge hub', windowLeftCosCutoff_eq_zero_of_ge huby]
      have hnn : 0 ≤ K * (Real.exp (-(8 * u)) * F u ^ 2 +
          Real.exp (-(8 * (u + y))) * F (u + y) ^ 2) := by positivity
      linarith only [hnn]
    · push Not at hub
      by_cases huy0 : 0 < u + y
      · rw [hF0 (u + y) huy0, mul_zero, mul_zero]
        positivity
      · push Not at huy0
        have hlip := windowLeftCutoff_diff_sq_le A₀ u y
        have hprod_le : ((windowLeftCutoff A₀ u - windowLeftCutoff A₀ (u + y)) ^ 2 +
            (windowLeftCosCutoff A₀ u - windowLeftCosCutoff A₀ (u + y)) ^ 2) * (F u * F (u + y)) ≤
            (32 * Real.pi ^ 2 * y ^ 2) * |F u * F (u + y)| := by
          calc _ ≤ ((windowLeftCutoff A₀ u - windowLeftCutoff A₀ (u + y)) ^ 2 +
                (windowLeftCosCutoff A₀ u - windowLeftCosCutoff A₀ (u + y)) ^ 2) * |F u * F (u + y)| :=
                mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
            _ ≤ (32 * Real.pi ^ 2 * y ^ 2) * |F u * F (u + y)| :=
                mul_le_mul_of_nonneg_right hlip (abs_nonneg _)
        have hamgm : 2 * |F u * F (u + y)| ≤
            Real.exp (4 * b) * F u ^ 2 + Real.exp (-4 * b) * F (u + y) ^ 2 := by
          have hs := sq_nonneg (Real.exp (2 * b) * |F u| - Real.exp (-2 * b) * |F (u + y)|)
          have he1 : Real.exp (2 * b) ^ 2 = Real.exp (4 * b) := by
            rw [sq, ← Real.exp_add]; congr 1; ring
          have he2 : Real.exp (-2 * b) ^ 2 = Real.exp (-4 * b) := by
            rw [sq, ← Real.exp_add]; congr 1; ring
          have hec : Real.exp (2 * b) * Real.exp (-2 * b) = 1 := by
            rw [← Real.exp_add, show 2 * b + -2 * b = 0 by ring, Real.exp_zero]
          rw [abs_mul]
          rw [sub_sq, mul_pow, mul_pow, he1, he2, sq_abs, sq_abs] at hs
          have hc : 2 * (Real.exp (2 * b) * |F u|) * (Real.exp (-2 * b) * |F (u + y)|) =
              2 * |F u| * |F (u + y)| := by
            linear_combination (2 * |F u| * |F (u + y)|) * hec
          linarith only [hs, hc]
        have hexp_u : Real.exp (4 * b) ≤ Real.exp (-4 * b) * Real.exp (-(8 * u)) := by
          rw [← Real.exp_add]
          exact Real.exp_le_exp.mpr (by linarith only [hub])
        have hexp_uy : Real.exp (-4 * b) ≤ Real.exp (-4 * b) * Real.exp (-(8 * (u + y))) :=
          le_mul_of_one_le_right (Real.exp_pos _).le (Real.one_le_exp (by linarith only [huy0]))
        have hF_dom : 2 * |F u * F (u + y)| ≤ Real.exp (-4 * b) *
            (Real.exp (-(8 * u)) * F u ^ 2 + Real.exp (-(8 * (u + y))) * F (u + y) ^ 2) := by
          have m1 := mul_le_mul_of_nonneg_right hexp_u (sq_nonneg (F u))
          have m2 := mul_le_mul_of_nonneg_right hexp_uy (sq_nonneg (F (u + y)))
          linarith only [hamgm, m1, m2,
            (by ring : Real.exp (-4 * b) * Real.exp (-(8 * u)) * F u ^ 2 +
              Real.exp (-4 * b) * Real.exp (-(8 * (u + y))) * F (u + y) ^ 2 =
              Real.exp (-4 * b) * (Real.exp (-(8 * u)) * F u ^ 2 +
                Real.exp (-(8 * (u + y))) * F (u + y) ^ 2))]
        have hm := mul_le_mul_of_nonneg_left hF_dom (by positivity : 0 ≤ 16 * Real.pi ^ 2 * y ^ 2)
        dsimp only [K]
        linarith only [hprod_le, hm,
          (by ring : 16 * Real.pi ^ 2 * y ^ 2 * (2 * |F u * F (u + y)|) =
            32 * Real.pi ^ 2 * y ^ 2 * |F u * F (u + y)|),
          (by ring : 16 * Real.pi ^ 2 * y ^ 2 * (Real.exp (-4 * b) *
            (Real.exp (-(8 * u)) * F u ^ 2 + Real.exp (-(8 * (u + y))) * F (u + y) ^ 2)) =
            16 * Real.pi ^ 2 * Real.exp (-4 * b) * y ^ 2 *
              (Real.exp (-(8 * u)) * F u ^ 2 + Real.exp (-(8 * (u + y))) * F (u + y) ^ 2))]
  have hint := integral_mono (i12.sub iF) (iEEy.const_mul K) hpt
  rw [integral_const_mul, integral_add iE iEy,
    integral_add_right_eq_self (μ := volume) (fun u => Real.exp (-(8 * u)) * F u ^ 2) y] at hint
  unfold exponentialMass
  dsimp only [Pi.sub_apply, K, b] at hint ⊢
  linarith only [hint]

private lemma archForm_windowLeftCutoff_sub_le {A₀ : ℝ} (hA₀ : 2 < A₀) {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hF0 : ∀ u, 0 < u → F u = 0) :
    archForm (fun u => windowLeftCutoff A₀ u * F u) - archForm F ≤
      (576 * Real.pi ^ 2 + 2 * |gammaHardyPhaseRate 0|) * Real.exp (-3 * (A₀ - 1)) *
        exponentialMass 8 F := by
  set b := A₀ - 1
  have hb1 : 1 < b := by dsimp only [b]; linarith
  set H₁ : ℝ → ℝ := fun u => windowLeftCutoff A₀ u * F u
  set H₂ : ℝ → ℝ := fun u => windowLeftCosCutoff A₀ u * F u
  have hH₁ : ContDiff ℝ 2 H₁ := (contDiff_windowLeftCutoff A₀).mul hF
  have hH₂ : ContDiff ℝ 2 H₂ := (contDiff_windowLeftCosCutoff A₀).mul hF
  have hH₁c : HasCompactSupport H₁ := hFc.mul_left
  have hH₂c : HasCompactSupport H₂ := hFc.mul_left
  have hF2c : HasCompactSupport (fun u => F u ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hFc ⊢
    exact hFc.mono fun u hu => by change F u = 0 at hu; change F u ^ 2 = 0; rw [hu]; norm_num
  have i1 : Integrable (fun u => H₁ u ^ 2) :=
    (hH₁.continuous.pow 2).integrable_of_hasCompactSupport (by
      rw [hasCompactSupport_iff_eventuallyEq] at hH₁c ⊢
      exact hH₁c.mono fun u hu => by change H₁ u = 0 at hu; change H₁ u ^ 2 = 0; rw [hu]; norm_num)
  have i2 : Integrable (fun u => H₂ u ^ 2) :=
    (hH₂.continuous.pow 2).integrable_of_hasCompactSupport (by
      rw [hasCompactSupport_iff_eventuallyEq] at hH₂c ⊢
      exact hH₂c.mono fun u hu => by change H₂ u = 0 at hu; change H₂ u ^ 2 = 0; rw [hu]; norm_num)
  have hdiag : (∫ u, H₁ u ^ 2) + (∫ u, H₂ u ^ 2) = ∫ u, F u ^ 2 := by
    rw [← integral_add i1 i2]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only [H₁, H₂]
    linear_combination F u ^ 2 * windowLeftCutoff_sq_add_cos_sq A₀ u
  have hlev_diff : levyEnergy H₁ + levyEnergy H₂ - levyEnergy F ≤
      576 * Real.pi ^ 2 * Real.exp (-4 * b) * exponentialMass 8 F := by
    have il1 := integrableOn_levyIntegrand hH₁ hH₁c
    have il2 := integrableOn_levyIntegrand hH₂ hH₂c
    have il12 : IntegrableOn (fun x =>
        (archLevyDensity x * ∫ u, (H₁ u - H₁ (u + x)) ^ 2) +
          archLevyDensity x * ∫ u, (H₂ u - H₂ (u + x)) ^ 2) (Ioi 0) := il1.add il2
    have ilF := integrableOn_levyIntegrand hF hFc
    rw [levyEnergy, levyEnergy, levyEnergy, ← integral_add il1 il2, ← integral_sub il12 ilF]
    set C_lev := 32 * Real.pi ^ 2 * Real.exp (-4 * b) * exponentialMass 8 F
    have hC0 : 0 ≤ C_lev := by
      have := exponentialMass_nonneg 8 F
      dsimp only [C_lev]; positivity
    have hmono : ∫ y in Ioi (0 : ℝ),
        ((archLevyDensity y * ∫ u, (H₁ u - H₁ (u + y)) ^ 2) +
          (archLevyDensity y * ∫ u, (H₂ u - H₂ (u + y)) ^ 2) -
          archLevyDensity y * ∫ u, (F u - F (u + y)) ^ 2) ≤
        ∫ y in Ioi (0 : ℝ), C_lev * (y ^ 2 * archLevyDensity y) := by
      refine setIntegral_mono_on (il12.sub ilF)
        (integrableOn_sq_mul_archLevyDensity.const_mul C_lev) measurableSet_Ioi fun y hy => ?_
      have hω := (archLevyDensity_pos hy).le
      have hcomm := levy_shift_commutator_integral_le hA₀ hF.continuous hFc hF0 hy
      have hm := mul_le_mul_of_nonneg_left hcomm hω
      dsimp only [C_lev, b] at hm ⊢
      linarith only [hm,
        (by ring : archLevyDensity y * ((∫ u, (H₁ u - H₁ (u + y)) ^ 2) +
            (∫ u, (H₂ u - H₂ (u + y)) ^ 2) - ∫ u, (F u - F (u + y)) ^ 2) =
          (archLevyDensity y * ∫ u, (H₁ u - H₁ (u + y)) ^ 2) +
            (archLevyDensity y * ∫ u, (H₂ u - H₂ (u + y)) ^ 2) -
            archLevyDensity y * ∫ u, (F u - F (u + y)) ^ 2),
        (by ring : archLevyDensity y * (32 * Real.pi ^ 2 * Real.exp (-4 * (A₀ - 1)) *
            exponentialMass 8 F * y ^ 2) =
          32 * Real.pi ^ 2 * Real.exp (-4 * (A₀ - 1)) * exponentialMass 8 F *
            (y ^ 2 * archLevyDensity y))]
    rw [integral_const_mul] at hmono
    have hm2 : C_lev * (∫ y in Ioi (0 : ℝ), y ^ 2 * archLevyDensity y) ≤ C_lev * 18 :=
      mul_le_mul_of_nonneg_left levySecondMoment_le hC0
    dsimp only [C_lev] at hmono hm2
    linarith only [hmono, hm2]
  have hH₂_L2 : (∫ u, H₂ u ^ 2) ≤ Real.exp (-8 * b) * exponentialMass 8 F := by
    have iE := integrable_exp_eight_mul_sq hF.continuous hFc
    refine (integral_mono i2 (iE.const_mul (Real.exp (-8 * b))) fun u => ?_).trans_eq ?_
    · by_cases hub : -b ≤ u
      · dsimp only [H₂]
        rw [windowLeftCosCutoff_eq_zero_of_ge hub, zero_mul, sq, zero_mul]
        positivity
      · push Not at hub
        have hc_b := windowLeftCosCutoff_bounds A₀ u
        have hcos2 : windowLeftCosCutoff A₀ u ^ 2 ≤ 1 := by nlinarith only [hc_b.1, hc_b.2]
        have hH₂_le : H₂ u ^ 2 ≤ F u ^ 2 := by
          dsimp only [H₂]; rw [mul_pow]
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hcos2 (sq_nonneg (F u))
        have hexp : 1 ≤ Real.exp (-8 * b) * Real.exp (-(8 * u)) := by
          rw [← Real.exp_add]; exact Real.one_le_exp (by linarith only [hub])
        exact hH₂_le.trans ((le_mul_of_one_le_left (sq_nonneg (F u)) hexp).trans_eq (mul_assoc _ _ _))
    · rw [integral_const_mul]; rfl
  have hlev2_nn : 0 ≤ levyEnergy H₂ :=
    setIntegral_nonneg measurableSet_Ioi fun y hy =>
      mul_nonneg (archLevyDensity_pos hy).le (integral_nonneg fun _ => sq_nonneg _)
  have harch1 := archForm_eq_levyEnergy hH₁ hH₁c
  have harchF := archForm_eq_levyEnergy hF hFc
  have hdiag_cancel : archForm H₁ - archForm F =
      (levyEnergy H₁ + levyEnergy H₂ - levyEnergy F) -
        2 * gammaHardyPhaseRate 0 * (∫ u, H₂ u ^ 2) - levyEnergy H₂ := by
    rw [harch1, harchF, ← hdiag]; ring
  have hγ_part : -2 * gammaHardyPhaseRate 0 * (∫ u, H₂ u ^ 2) ≤
      2 * |gammaHardyPhaseRate 0| * (Real.exp (-8 * b) * exponentialMass 8 F) := by
    have hH₂_nn : 0 ≤ ∫ u, H₂ u ^ 2 := integral_nonneg fun u => sq_nonneg (H₂ u)
    have h1 := mul_le_mul_of_nonneg_right (neg_le_abs (gammaHardyPhaseRate 0)) hH₂_nn
    have h2 := mul_le_mul_of_nonneg_left hH₂_L2
      (mul_nonneg zero_le_two (abs_nonneg (gammaHardyPhaseRate 0)))
    linarith only [h1, h2]
  have hM0 := exponentialMass_nonneg 8 F
  have hexp4 : Real.exp (-4 * b) ≤ Real.exp (-3 * b) :=
    Real.exp_le_exp.mpr (by linarith only [hb1])
  have hexp8 : Real.exp (-8 * b) ≤ Real.exp (-3 * b) :=
    Real.exp_le_exp.mpr (by linarith only [hb1])
  have hm4 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hexp4 (by positivity : 0 ≤ 576 * Real.pi ^ 2)) hM0
  have hm8 := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hexp8 hM0) (mul_nonneg zero_le_two (abs_nonneg (gammaHardyPhaseRate 0)))
  rw [hdiag_cancel]
  linarith only [hlev_diff, hγ_part, hlev2_nn, hm4, hm8,
    (by ring : 576 * Real.pi ^ 2 * Real.exp (-3 * b) * exponentialMass 8 F +
      2 * |gammaHardyPhaseRate 0| * (Real.exp (-3 * b) * exponentialMass 8 F) =
      (576 * Real.pi ^ 2 + 2 * |gammaHardyPhaseRate 0|) * Real.exp (-3 * b) * exponentialMass 8 F)]

/-! ### 3. Channel 2: Prime three-halves bound -/

private lemma prime_term_windowLeftCutoff_diff_le {A₀ : ℝ} (hA₀ : 2 < A₀) {F : ℝ → ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) (hF0 : ∀ u, 0 < u → F u = 0) (n : ℕ) :
    let H₁ := fun u => windowLeftCutoff A₀ u * F u
    vonMangoldtAtom n *
      (((∫ u, F u * F (u - Real.log n)) + ∫ u, F u * F (u + Real.log n)) -
        ((∫ u, H₁ u * H₁ (u - Real.log n)) + ∫ u, H₁ u * H₁ (u + Real.log n))) ≤
      (2 * (1 + Real.exp 1) * (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ))) *
        (Real.exp (-3 * (A₀ - 1)) * exponentialMass 8 F) := by
  intro H₁
  by_cases hn : 2 ≤ n
  · set b := A₀ - 1
    have hb1 : 1 < b := by dsimp only [b]; linarith
    set t := Real.log (n : ℝ)
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have ht0 : 0 < t := Real.log_pos (by exact_mod_cast hn)
    have hexp_t : Real.exp t = n := Real.exp_log hn0
    set H₂t : ℝ → ℝ := fun u => (1 - windowLeftCutoff A₀ u) * F u
    have hH₁c : Continuous H₁ := (contDiff_windowLeftCutoff A₀).continuous.mul hF
    have hH₂tc : Continuous H₂t :=
      (continuous_const.sub (contDiff_windowLeftCutoff A₀).continuous).mul hF
    have hH₁s : HasCompactSupport H₁ := hFc.mul_left
    have hH₂ts : HasCompactSupport H₂t := hFc.mul_left
    have hsym (g : ℝ → ℝ) : (∫ u, g u * g (u - t)) = ∫ u, g u * g (u + t) := by
      have h := integral_add_right_eq_self (μ := volume) (fun u => g u * g (u - t)) t
      rw [← h]
      exact integral_congr_ae (Eventually.of_forall fun u => by
        dsimp only
        rw [add_sub_cancel_right, mul_comm])
    rw [hsym F, hsym H₁]
    have iFF : Integrable fun u => F u * F (u + t) :=
      (hF.mul (hF.comp (continuous_add_const t))).integrable_of_hasCompactSupport hFc.mul_right
    have i11 : Integrable fun u => H₁ u * H₁ (u + t) :=
      (hH₁c.mul (hH₁c.comp (continuous_add_const t))).integrable_of_hasCompactSupport hH₁s.mul_right
    have iA : Integrable fun u => H₂t u * F (u + t) :=
      (hH₂tc.mul (hF.comp (continuous_add_const t))).integrable_of_hasCompactSupport hH₂ts.mul_right
    have iB : Integrable fun u => H₁ u * H₂t (u + t) :=
      (hH₁c.mul (hH₂tc.comp (continuous_add_const t))).integrable_of_hasCompactSupport hH₁s.mul_right
    have hdiff_eq : ((∫ u, F u * F (u + t)) + ∫ u, F u * F (u + t)) -
        ((∫ u, H₁ u * H₁ (u + t)) + ∫ u, H₁ u * H₁ (u + t)) =
        2 * ((∫ u, H₂t u * F (u + t)) + ∫ u, H₁ u * H₂t (u + t)) := by
      have hsub : (∫ u, F u * F (u + t)) - (∫ u, H₁ u * H₁ (u + t)) =
          (∫ u, H₂t u * F (u + t)) + ∫ u, H₁ u * H₂t (u + t) := by
        rw [← integral_sub iFF i11, ← integral_add iA iB]
        exact integral_congr_ae (Eventually.of_forall fun u => by dsimp only [H₁, H₂t]; ring)
      linarith only [hsub]
    rw [hdiff_eq]
    have iE := integrable_exp_eight_mul_sq hF hFc
    have iEt : Integrable fun u => Real.exp (-(8 * (u + t))) * F (u + t) ^ 2 := iE.comp_add_right t
    have iEEt : Integrable fun u =>
        Real.exp (-(8 * u)) * F u ^ 2 + Real.exp (-(8 * (u + t))) * F (u + t) ^ 2 := iE.add iEt
    -- Bound Term A: `n * ∫ H₂t(u) F(u + t) ≤ e^{-3b} M₈(F)`
    have hTermA : (n : ℝ) * (∫ u, H₂t u * F (u + t)) ≤
        Real.exp (-3 * b) * exponentialMass 8 F := by
      have hptA : ∀ u, (n : ℝ) * (H₂t u * F (u + t)) ≤
          ((1 / 2 : ℝ) * Real.exp (-3 * b)) *
            (Real.exp (-(8 * u)) * F u ^ 2 + Real.exp (-(8 * (u + t))) * F (u + t) ^ 2) := by
        intro u
        by_cases hub : -b ≤ u
        · dsimp only [H₂t]
          rw [windowLeftCutoff_eq_one_of_ge hub, sub_self, zero_mul, zero_mul, mul_zero]
          positivity
        · push Not at hub
          by_cases hut0 : 0 < u + t
          · rw [hF0 (u + t) hut0, mul_zero, mul_zero]; positivity
          · push Not at hut0
            have hn_le : (n : ℝ) ≤ Real.exp (-u) := by
              rw [← hexp_t]; exact Real.exp_le_exp.mpr (by linarith only [hut0])
            have hθ := windowLeftCutoff_bounds A₀ u
            have h1θ : |1 - windowLeftCutoff A₀ u| ≤ 1 := by
              rw [abs_of_nonneg (by linarith [hθ.2])]; linarith [hθ.1]
            have hH₂t_abs : |H₂t u| ≤ |F u| := by
              dsimp only [H₂t]; rw [abs_mul]
              simpa only [one_mul] using mul_le_mul_of_nonneg_right h1θ (abs_nonneg (F u))
            have hprod : (n : ℝ) * (H₂t u * F (u + t)) ≤ Real.exp (-u) * |F u| * |F (u + t)| := by
              calc (n : ℝ) * (H₂t u * F (u + t))
                  ≤ (n : ℝ) * |H₂t u * F (u + t)| :=
                    mul_le_mul_of_nonneg_left (le_abs_self _) hn0.le
                _ = (n : ℝ) * (|H₂t u| * |F (u + t)|) := by rw [abs_mul]
                _ ≤ Real.exp (-u) * (|F u| * |F (u + t)|) :=
                    mul_le_mul hn_le (mul_le_mul_of_nonneg_right hH₂t_abs (abs_nonneg _))
                      (by positivity) (Real.exp_pos _).le
                _ = Real.exp (-u) * |F u| * |F (u + t)| := by ring
            have hamgm : 2 * (Real.exp (-u) * |F u| * |F (u + t)|) ≤
                Real.exp (3 * b - 2 * u) * F u ^ 2 + Real.exp (-3 * b) * F (u + t) ^ 2 := by
              have hs := sq_nonneg
                (Real.exp ((3 * b - 2 * u) / 2) * |F u| - Real.exp (-3 * b / 2) * |F (u + t)|)
              have he1 : Real.exp ((3 * b - 2 * u) / 2) ^ 2 = Real.exp (3 * b - 2 * u) := by
                rw [sq, ← Real.exp_add]; congr 1; ring
              have he2 : Real.exp (-3 * b / 2) ^ 2 = Real.exp (-3 * b) := by
                rw [sq, ← Real.exp_add]; congr 1; ring
              have hec : Real.exp ((3 * b - 2 * u) / 2) * Real.exp (-3 * b / 2) = Real.exp (-u) := by
                rw [← Real.exp_add]; congr 1; ring
              rw [sub_sq, mul_pow, mul_pow, he1, he2, sq_abs, sq_abs] at hs
              have hc : 2 * (Real.exp ((3 * b - 2 * u) / 2) * |F u|) *
                  (Real.exp (-3 * b / 2) * |F (u + t)|) =
                  2 * (Real.exp (-u) * |F u| * |F (u + t)|) := by
                linear_combination (2 * |F u| * |F (u + t)|) * hec
              linarith only [hs, hc]
            have hexp1 : Real.exp (3 * b - 2 * u) ≤ Real.exp (-3 * b) * Real.exp (-(8 * u)) := by
              rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith only [hub])
            have hexp2 : Real.exp (-3 * b) ≤ Real.exp (-3 * b) * Real.exp (-(8 * (u + t))) :=
              le_mul_of_one_le_right (Real.exp_pos _).le (Real.one_le_exp (by linarith only [hut0]))
            have m1 := mul_le_mul_of_nonneg_right hexp1 (sq_nonneg (F u))
            have m2 := mul_le_mul_of_nonneg_right hexp2 (sq_nonneg (F (u + t)))
            linarith only [hprod, hamgm, m1, m2,
              (by ring : Real.exp (-3 * b) * Real.exp (-(8 * u)) * F u ^ 2 +
                Real.exp (-3 * b) * Real.exp (-(8 * (u + t))) * F (u + t) ^ 2 =
                2 * (((1 / 2 : ℝ) * Real.exp (-3 * b)) *
                  (Real.exp (-(8 * u)) * F u ^ 2 + Real.exp (-(8 * (u + t))) * F (u + t) ^ 2)))]
      have hint := integral_mono (iA.const_mul (n : ℝ))
        (iEEt.const_mul ((1 / 2 : ℝ) * Real.exp (-3 * b))) hptA
      rw [integral_const_mul, integral_const_mul, integral_add iE iEt,
        integral_add_right_eq_self (μ := volume) (fun u => Real.exp (-(8 * u)) * F u ^ 2) t] at hint
      unfold exponentialMass
      linarith only [hint]
    -- Bound Term B: `n * ∫ H₁(u) H₂t(u + t) ≤ e * e^{-3b} M₈(F)`
    have hTermB : (n : ℝ) * (∫ u, H₁ u * H₂t (u + t)) ≤
        Real.exp 1 * Real.exp (-3 * b) * exponentialMass 8 F := by
      have hptB : ∀ u, (n : ℝ) * (H₁ u * H₂t (u + t)) ≤
          ((1 / 2 : ℝ) * Real.exp 1 * Real.exp (-3 * b)) *
            (Real.exp (-(8 * u)) * F u ^ 2 + Real.exp (-(8 * (u + t))) * F (u + t) ^ 2) := by
        intro u
        by_cases huA : u ≤ -A₀
        · dsimp only [H₁]
          rw [windowLeftCutoff_eq_zero_of_le huA, zero_mul, zero_mul, mul_zero]
          positivity
        · push Not at huA
          by_cases hutb : -b ≤ u + t
          · dsimp only [H₂t]
            rw [windowLeftCutoff_eq_one_of_ge hutb, sub_self, zero_mul, mul_zero, mul_zero]
            positivity
          · push Not at hutb
            have ht_le1 : t ≤ 1 := by dsimp only [b] at hutb; linarith only [huA, hutb]
            have hn_le_e : (n : ℝ) ≤ Real.exp 1 := by
              rw [← hexp_t]; exact Real.exp_le_exp.mpr ht_le1
            have hub : u < -b := by linarith only [hutb, ht0]
            have hθ1 := windowLeftCutoff_bounds A₀ u
            have hθ2 := windowLeftCutoff_bounds A₀ (u + t)
            have hH₁_abs : |H₁ u| ≤ |F u| := by
              dsimp only [H₁]; rw [abs_mul, abs_of_nonneg hθ1.1]
              simpa only [one_mul] using mul_le_mul_of_nonneg_right hθ1.2 (abs_nonneg (F u))
            have hH₂_abs : |H₂t (u + t)| ≤ |F (u + t)| := by
              dsimp only [H₂t]; rw [abs_mul, abs_of_nonneg (by linarith [hθ2.2])]
              simpa only [one_mul] using
                mul_le_mul_of_nonneg_right (by linarith [hθ2.1] : 1 - windowLeftCutoff A₀ (u + t) ≤ 1)
                  (abs_nonneg (F (u + t)))
            have hprod : (n : ℝ) * (H₁ u * H₂t (u + t)) ≤
                Real.exp 1 * ((1 / 2 : ℝ) * (F u ^ 2 + F (u + t) ^ 2)) := by
              have hsq := sq_nonneg (|F u| - |F (u + t)|)
              rw [sub_sq, sq_abs, sq_abs] at hsq
              have hab : |H₁ u * H₂t (u + t)| ≤ (1 / 2 : ℝ) * (F u ^ 2 + F (u + t) ^ 2) := by
                rw [abs_mul]
                have hm := mul_le_mul hH₁_abs hH₂_abs (abs_nonneg _) (abs_nonneg _)
                linarith only [hm, hsq]
              calc (n : ℝ) * (H₁ u * H₂t (u + t))
                  ≤ (n : ℝ) * |H₁ u * H₂t (u + t)| :=
                    mul_le_mul_of_nonneg_left (le_abs_self _) hn0.le
                _ ≤ Real.exp 1 * ((1 / 2 : ℝ) * (F u ^ 2 + F (u + t) ^ 2)) :=
                    mul_le_mul hn_le_e hab (abs_nonneg _) (Real.exp_pos 1).le
            have hexp1 : 1 ≤ Real.exp (-3 * b) * Real.exp (-(8 * u)) := by
              rw [← Real.exp_add]; exact Real.one_le_exp (by linarith only [hub, hb1])
            have hexp2 : 1 ≤ Real.exp (-3 * b) * Real.exp (-(8 * (u + t))) := by
              rw [← Real.exp_add]; exact Real.one_le_exp (by linarith only [hutb, hb1])
            have m1 : F u ^ 2 ≤ Real.exp (-3 * b) * Real.exp (-(8 * u)) * F u ^ 2 :=
              le_mul_of_one_le_left (sq_nonneg (F u)) hexp1
            have m2 : F (u + t) ^ 2 ≤ Real.exp (-3 * b) * Real.exp (-(8 * (u + t))) * F (u + t) ^ 2 :=
              le_mul_of_one_le_left (sq_nonneg (F (u + t))) hexp2
            have hm := mul_le_mul_of_nonneg_left (add_le_add m1 m2)
              (by positivity : 0 ≤ (1 / 2 : ℝ) * Real.exp 1)
            linarith only [hprod, hm,
              (by ring : Real.exp 1 * ((1 / 2 : ℝ) * (F u ^ 2 + F (u + t) ^ 2)) =
                ((1 / 2 : ℝ) * Real.exp 1) * (F u ^ 2 + F (u + t) ^ 2)),
              (by ring : ((1 / 2 : ℝ) * Real.exp 1) *
                  (Real.exp (-3 * b) * Real.exp (-(8 * u)) * F u ^ 2 +
                    Real.exp (-3 * b) * Real.exp (-(8 * (u + t))) * F (u + t) ^ 2) =
                ((1 / 2 : ℝ) * Real.exp 1 * Real.exp (-3 * b)) *
                  (Real.exp (-(8 * u)) * F u ^ 2 + Real.exp (-(8 * (u + t))) * F (u + t) ^ 2))]
      have hint := integral_mono (iB.const_mul (n : ℝ))
        (iEEt.const_mul ((1 / 2 : ℝ) * Real.exp 1 * Real.exp (-3 * b))) hptB
      rw [integral_const_mul, integral_const_mul, integral_add iE iEt,
        integral_add_right_eq_self (μ := volume) (fun u => Real.exp (-(8 * u)) * F u ^ 2) t] at hint
      unfold exponentialMass
      linarith only [hint]
    -- Combine Term A and Term B via `vonMangoldtAtom n = (Λ n / n^{3/2}) * n`
    have hatom : vonMangoldtAtom n =
        (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ)) * (n : ℝ) := by
      have hp : Real.sqrt (n : ℝ) * (n : ℝ) = (n : ℝ) ^ (3 / 2 : ℝ) := by
        calc Real.sqrt (n : ℝ) * (n : ℝ)
            = (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 : ℝ) := by rw [Real.sqrt_eq_rpow, Real.rpow_one]
          _ = (n : ℝ) ^ ((1 / 2 : ℝ) + 1) := (Real.rpow_add hn0 _ _).symm
          _ = (n : ℝ) ^ (3 / 2 : ℝ) := by congr 1; ring
      rw [vonMangoldtAtom, if_pos hn, ← hp]
      field_simp [hn0.ne', (Real.sqrt_pos.mpr hn0).ne']
    rw [hatom]
    have hcoeff_nn : 0 ≤ ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ) :=
      div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg hn0.le _)
    have hsum_AB : (n : ℝ) * ((∫ u, H₂t u * F (u + t)) + ∫ u, H₁ u * H₂t (u + t)) ≤
        (1 + Real.exp 1) * (Real.exp (-3 * b) * exponentialMass 8 F) := by
      linarith only [hTermA, hTermB,
        (by ring : (n : ℝ) * ((∫ u, H₂t u * F (u + t)) + ∫ u, H₁ u * H₂t (u + t)) =
          (n : ℝ) * (∫ u, H₂t u * F (u + t)) + (n : ℝ) * (∫ u, H₁ u * H₂t (u + t))),
        (by ring : Real.exp (-3 * b) * exponentialMass 8 F +
          Real.exp 1 * Real.exp (-3 * b) * exponentialMass 8 F =
          (1 + Real.exp 1) * (Real.exp (-3 * b) * exponentialMass 8 F))]
    have hm := mul_le_mul_of_nonneg_left hsum_AB (mul_nonneg zero_le_two hcoeff_nn)
    dsimp only [b] at hm
    linarith only [hm,
      (by ring : (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ)) * (n : ℝ) *
          (2 * ((∫ u, H₂t u * F (u + t)) + ∫ u, H₁ u * H₂t (u + t))) =
        2 * (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ)) *
          ((n : ℝ) * ((∫ u, H₂t u * F (u + t)) + ∫ u, H₁ u * H₂t (u + t)))),
      (by ring : 2 * (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ)) *
          ((1 + Real.exp 1) * (Real.exp (-3 * (A₀ - 1)) * exponentialMass 8 F)) =
        (2 * (1 + Real.exp 1) * (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ))) *
          (Real.exp (-3 * (A₀ - 1)) * exponentialMass 8 F))]
  · simp only [vonMangoldtAtom, if_neg hn, zero_mul]
    have hv := ArithmeticFunction.vonMangoldt_nonneg (n := n)
    have hM := exponentialMass_nonneg 8 F
    positivity

private lemma primeSum_sub_windowLeftCutoff_le {A₀ : ℝ} (hA₀ : 2 < A₀) {F : ℝ → ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) (hF0 : ∀ u, 0 < u → F u = 0) :
    primeSum F - primeSum (fun u => windowLeftCutoff A₀ u * F u) ≤
      2 * (1 + Real.exp 1) * vonMangoldtThreeHalvesMass * Real.exp (-3 * (A₀ - 1)) *
        exponentialMass 8 F := by
  set H₁ : ℝ → ℝ := fun u => windowLeftCutoff A₀ u * F u
  have hH₁s : HasCompactSupport H₁ := hFc.mul_left
  have sF := summable_primeSum_terms hFc
  have s1 := summable_primeSum_terms hH₁s
  unfold primeSum
  rw [← sF.tsum_sub s1]
  have hterm : ∀ n : ℕ,
      vonMangoldtAtom n * ((∫ u, F u * F (u - Real.log n)) + ∫ u, F u * F (u + Real.log n)) -
        vonMangoldtAtom n * ((∫ u, H₁ u * H₁ (u - Real.log n)) + ∫ u, H₁ u * H₁ (u + Real.log n)) ≤
      (2 * (1 + Real.exp 1) * (ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (3 / 2 : ℝ))) *
        (Real.exp (-3 * (A₀ - 1)) * exponentialMass 8 F) := fun n => by
    rw [← mul_sub]
    exact prime_term_windowLeftCutoff_diff_le hA₀ hF hFc hF0 n
  have sBound := (summable_vonMangoldt_div_threeHalves.mul_left (2 * (1 + Real.exp 1))).mul_right
    (Real.exp (-3 * (A₀ - 1)) * exponentialMass 8 F)
  have hsum := (sF.sub s1).tsum_le_tsum hterm sBound
  rw [tsum_mul_right, tsum_mul_left] at hsum
  exact hsum.trans_eq (by unfold vonMangoldtThreeHalvesMass; ring)

/-! ### 4. Channel 3: Pole moment cross -/

private lemma laplaceMoment_sq_le_shifted_exponentialMass {g : ℝ → ℝ} {L q : ℝ}
    (hg : Continuous g) (hgc : HasCompactSupport g) (_hL0 : 0 ≤ L)
    (hgs : ∀ u, -L < u → g u = 0) (hq : 0 < 8 + 2 * q) :
    (∫ u, g u * Real.exp (q * u)) ^ 2 ≤
      (Real.exp (-(8 + 2 * q) * L) / (8 + 2 * q)) * exponentialMass 8 g := by
  let B : ℝ → ℝ := (Iic (-L)).indicator fun u => Real.exp ((8 + 2 * q) * u)
  have iB : Integrable B :=
    (integrable_indicator_iff measurableSet_Iic).mpr (integrableOn_exp_mul_Iic hq (-L))
  have hnormB : (∫ u, B u) = Real.exp (-(8 + 2 * q) * L) / (8 + 2 * q) := by
    dsimp only [B]
    rw [integral_indicator measurableSet_Iic, integral_exp_mul_Iic hq (-L)]
    congr 1; ring
  have iE := integrable_exp_eight_mul_sq hg hgc
  have igq : Integrable fun u => g u * Real.exp (q * u) :=
    (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right
  set M := exponentialMass 8 g
  have hM0 : 0 ≤ M := exponentialMass_nonneg 8 g
  have hquad : ∀ t : ℝ, 0 ≤ M * (t * t) + (2 * ∫ u, g u * Real.exp (q * u)) * t + ∫ u, B u := by
    intro t
    have hpt : ∀ u, 0 ≤ (t * t) * (Real.exp (-(8 * u)) * g u ^ 2) +
        2 * t * (g u * Real.exp (q * u)) + B u := by
      intro u
      by_cases hu : u ≤ -L
      · dsimp only [B]
        rw [indicator_of_mem (mem_Iic.mpr hu)]
        have hs := sq_nonneg (t * Real.exp (-4 * u) * g u + Real.exp ((4 + q) * u))
        have he1 : Real.exp (-4 * u) ^ 2 = Real.exp (-(8 * u)) := by
          rw [sq, ← Real.exp_add]; congr 1; ring
        have he2 : Real.exp ((4 + q) * u) ^ 2 = Real.exp ((8 + 2 * q) * u) := by
          rw [sq, ← Real.exp_add]; congr 1; ring
        have hec : Real.exp (-4 * u) * Real.exp ((4 + q) * u) = Real.exp (q * u) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [add_sq, mul_pow, mul_pow, he1, he2] at hs
        have hc : 2 * (t * Real.exp (-4 * u) * g u) * Real.exp ((4 + q) * u) =
            2 * t * (g u * Real.exp (q * u)) := by
          linear_combination (2 * t * g u) * hec
        linarith only [hs, hc]
      · push Not at hu
        dsimp only [B]
        rw [indicator_of_notMem (fun hm => not_lt.mpr (mem_Iic.mp hm) hu), hgs u hu]
        norm_num
    have i1 := iE.const_mul (t * t)
    have i2 := igq.const_mul (2 * t)
    have i12 : Integrable fun u =>
        (t * t) * (Real.exp (-(8 * u)) * g u ^ 2) + 2 * t * (g u * Real.exp (q * u)) := i1.add i2
    have hint : 0 ≤ ∫ u, ((t * t) * (Real.exp (-(8 * u)) * g u ^ 2) +
        2 * t * (g u * Real.exp (q * u)) + B u) := integral_nonneg hpt
    rw [integral_add i12 iB, integral_add i1 i2,
      integral_const_mul, integral_const_mul] at hint
    dsimp only [M, exponentialMass]
    linarith only [hint]
  have hd := discrim_le_zero hquad
  rw [discrim, hnormB] at hd
  nlinarith only [hd, hM0]

private lemma two_mul_cosh_sq_sub_sinh_sq {g : ℝ → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    2 * coshHalfMoment g ^ 2 - 2 * sinhHalfMoment g ^ 2 =
      2 * (∫ u, g u * Real.exp (u / 2)) * (∫ u, g u * Real.exp (-(u / 2))) := by
  have ip : Integrable fun u => g u * Real.exp (u / 2) :=
    (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right
  have im : Integrable fun u => g u * Real.exp (-(u / 2)) :=
    (hg.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right
  have hcosh : coshHalfMoment g =
      ((∫ u, g u * Real.exp (u / 2)) + ∫ u, g u * Real.exp (-(u / 2))) / 2 := by
    unfold coshHalfMoment
    rw [← integral_add ip im, ← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only
    rw [Real.cosh_eq]; ring
  have hsinh : sinhHalfMoment g =
      ((∫ u, g u * Real.exp (u / 2)) - ∫ u, g u * Real.exp (-(u / 2))) / 2 := by
    unfold sinhHalfMoment
    rw [← integral_sub ip im, ← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only
    rw [Real.sinh_eq]; ring
  rw [hcosh, hsinh]; ring

private lemma pole_windowLeftCutoff_sub_le {A₀ : ℝ} (hA₀ : 2 < A₀) {F : ℝ → ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) (hF0 : ∀ u, 0 < u → F u = 0) :
    let H₁ := fun u => windowLeftCutoff A₀ u * F u
    (2 * coshHalfMoment H₁ ^ 2 - 2 * sinhHalfMoment H₁ ^ 2) -
      (2 * coshHalfMoment F ^ 2 - 2 * sinhHalfMoment F ^ 2) ≤
      4 * Real.exp (-3 * (A₀ - 1)) * exponentialMass 8 F := by
  intro H₁
  set b := A₀ - 1
  have hb1 : 1 < b := by dsimp only [b]; linarith
  set H₂t : ℝ → ℝ := fun u => (1 - windowLeftCutoff A₀ u) * F u
  have hH₁c : Continuous H₁ := (contDiff_windowLeftCutoff A₀).continuous.mul hF
  have hH₂tc : Continuous H₂t :=
    (continuous_const.sub (contDiff_windowLeftCutoff A₀).continuous).mul hF
  have hH₁s : HasCompactSupport H₁ := hFc.mul_left
  have hH₂ts : HasCompactSupport H₂t := hFc.mul_left
  rw [two_mul_cosh_sq_sub_sinh_sq hH₁c hH₁s, two_mul_cosh_sq_sub_sinh_sq hF hFc]
  have i1p : Integrable fun u => H₁ u * Real.exp (u / 2) :=
    (hH₁c.mul (by fun_prop)).integrable_of_hasCompactSupport hH₁s.mul_right
  have i2p : Integrable fun u => H₂t u * Real.exp (u / 2) :=
    (hH₂tc.mul (by fun_prop)).integrable_of_hasCompactSupport hH₂ts.mul_right
  have i1m : Integrable fun u => H₁ u * Real.exp (-(u / 2)) :=
    (hH₁c.mul (by fun_prop)).integrable_of_hasCompactSupport hH₁s.mul_right
  have i2m : Integrable fun u => H₂t u * Real.exp (-(u / 2)) :=
    (hH₂tc.mul (by fun_prop)).integrable_of_hasCompactSupport hH₂ts.mul_right
  have hFp : (∫ u, F u * Real.exp (u / 2)) =
      (∫ u, H₁ u * Real.exp (u / 2)) + ∫ u, H₂t u * Real.exp (u / 2) := by
    rw [← integral_add i1p i2p]
    exact integral_congr_ae (Eventually.of_forall fun u => by dsimp only [H₁, H₂t]; ring)
  have hFm : (∫ u, F u * Real.exp (-(u / 2))) =
      (∫ u, H₁ u * Real.exp (-(u / 2))) + ∫ u, H₂t u * Real.exp (-(u / 2)) := by
    rw [← integral_add i1m i2m]
    exact integral_congr_ae (Eventually.of_forall fun u => by dsimp only [H₁, H₂t]; ring)
  rw [hFp, hFm]
  have iE := integrable_exp_eight_mul_sq hF hFc
  have hM1 : exponentialMass 8 H₁ ≤ exponentialMass 8 F := by
    refine integral_mono (integrable_exp_eight_mul_sq hH₁c hH₁s) iE fun u => ?_
    have hθ := windowLeftCutoff_bounds A₀ u
    have hθ2 : windowLeftCutoff A₀ u ^ 2 ≤ 1 := by nlinarith only [hθ.1, hθ.2]
    dsimp only [H₁]; rw [mul_pow]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hθ2 (sq_nonneg (F u)))
      (Real.exp_pos _).le
  have hM2 : exponentialMass 8 H₂t ≤ exponentialMass 8 F := by
    refine integral_mono (integrable_exp_eight_mul_sq hH₂tc hH₂ts) iE fun u => ?_
    have hθ := windowLeftCutoff_bounds A₀ u
    have h1θ : (1 - windowLeftCutoff A₀ u) ^ 2 ≤ 1 := by
      nlinarith only [hθ.1, hθ.2, mul_nonneg hθ.1 (sub_nonneg.mpr hθ.2)]
    dsimp only [H₂t]; rw [mul_pow]
    exact mul_le_mul_of_nonneg_left
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right h1θ (sq_nonneg (F u)))
      (Real.exp_pos _).le
  have hH₁_0 : ∀ u, -(0 : ℝ) < u → H₁ u = 0 := fun u hu => by
    dsimp only [H₁]; rw [hF0 u (by linarith), mul_zero]
  have hF_0 : ∀ u, -(0 : ℝ) < u → F u = 0 := fun u hu => hF0 u (by linarith)
  have hH₂_b : ∀ u, -b < u → H₂t u = 0 := fun u hu => by
    dsimp only [H₂t]; rw [windowLeftCutoff_eq_one_of_ge hu.le, sub_self, zero_mul]
  have hM0 := exponentialMass_nonneg 8 F
  have b1p : (∫ u, H₁ u * Real.exp (u / 2)) ^ 2 ≤ exponentialMass 8 F := by
    have h := laplaceMoment_sq_le_shifted_exponentialMass hH₁c hH₁s le_rfl hH₁_0
      (q := 1 / 2) (by norm_num)
    have heq : (∫ u, H₁ u * Real.exp (1 / 2 * u)) = ∫ u, H₁ u * Real.exp (u / 2) :=
      integral_congr_ae (Eventually.of_forall fun u => by
        dsimp only; rw [show (1 / 2 : ℝ) * u = u / 2 by ring])
    rw [heq, mul_zero, Real.exp_zero] at h
    have h' : (∫ u, H₁ u * Real.exp (u / 2)) ^ 2 ≤ (1 / 9 : ℝ) * exponentialMass 8 H₁ := by
      linarith only [h]
    exact h'.trans ((mul_le_mul_of_nonneg_left hM1 (by norm_num)).trans (by linarith only [hM0]))
  have bFm : (∫ u, F u * Real.exp (-(u / 2))) ^ 2 ≤ exponentialMass 8 F := by
    have h := laplaceMoment_sq_le_shifted_exponentialMass hF hFc le_rfl hF_0
      (q := -(1 / 2)) (by norm_num)
    have heq : (∫ u, F u * Real.exp (-(1 / 2) * u)) = ∫ u, F u * Real.exp (-(u / 2)) :=
      integral_congr_ae (Eventually.of_forall fun u => by
        dsimp only; rw [show -(1 / 2 : ℝ) * u = -(u / 2) by ring])
    rw [heq, mul_zero, Real.exp_zero] at h
    have h' : (∫ u, F u * Real.exp (-(u / 2))) ^ 2 ≤ (1 / 7 : ℝ) * exponentialMass 8 F := by
      linarith only [h]
    linarith only [h', hM0]
  have b2p : (∫ u, H₂t u * Real.exp (u / 2)) ^ 2 ≤ Real.exp (-6 * b) * exponentialMass 8 F := by
    have h := laplaceMoment_sq_le_shifted_exponentialMass hH₂tc hH₂ts (by linarith) hH₂_b
      (q := 1 / 2) (by norm_num)
    have heq : (∫ u, H₂t u * Real.exp (1 / 2 * u)) = ∫ u, H₂t u * Real.exp (u / 2) :=
      integral_congr_ae (Eventually.of_forall fun u => by
        dsimp only; rw [show (1 / 2 : ℝ) * u = u / 2 by ring])
    rw [heq, show -(8 + 2 * (1 / 2 : ℝ)) * b = -9 * b by ring,
      show (8 : ℝ) + 2 * (1 / 2) = 9 by norm_num] at h
    have hexp : Real.exp (-9 * b) / 9 ≤ Real.exp (-6 * b) := by
      calc Real.exp (-9 * b) / 9 ≤ Real.exp (-9 * b) := div_le_self (Real.exp_pos _).le (by norm_num)
        _ ≤ Real.exp (-6 * b) := Real.exp_le_exp.mpr (by linarith only [hb1])
    exact h.trans ((mul_le_mul_of_nonneg_left hM2 (by positivity)).trans
      (mul_le_mul_of_nonneg_right hexp hM0))
  have b2m : (∫ u, H₂t u * Real.exp (-(u / 2))) ^ 2 ≤ Real.exp (-6 * b) * exponentialMass 8 F := by
    have h := laplaceMoment_sq_le_shifted_exponentialMass hH₂tc hH₂ts (by linarith) hH₂_b
      (q := -(1 / 2)) (by norm_num)
    have heq : (∫ u, H₂t u * Real.exp (-(1 / 2) * u)) = ∫ u, H₂t u * Real.exp (-(u / 2)) :=
      integral_congr_ae (Eventually.of_forall fun u => by
        dsimp only; rw [show -(1 / 2 : ℝ) * u = -(u / 2) by ring])
    rw [heq, show -(8 + 2 * -(1 / 2 : ℝ)) * b = -7 * b by ring,
      show (8 : ℝ) + 2 * -(1 / 2) = 7 by norm_num] at h
    have hexp : Real.exp (-7 * b) / 7 ≤ Real.exp (-6 * b) := by
      calc Real.exp (-7 * b) / 7 ≤ Real.exp (-7 * b) := div_le_self (Real.exp_pos _).le (by norm_num)
        _ ≤ Real.exp (-6 * b) := Real.exp_le_exp.mpr (by linarith only [hb1])
    exact h.trans ((mul_le_mul_of_nonneg_left hM2 (by positivity)).trans
      (mul_le_mul_of_nonneg_right hexp hM0))
  set Ip1 := ∫ u, H₁ u * Real.exp (u / 2)
  set Ip2 := ∫ u, H₂t u * Real.exp (u / 2)
  set Im1 := ∫ u, H₁ u * Real.exp (-(u / 2))
  set Im2 := ∫ u, H₂t u * Real.exp (-(u / 2))
  have hid : 2 * Ip1 * Im1 - 2 * (Ip1 + Ip2) * (Im1 + Im2) =
      -(2 * Ip2 * (Im1 + Im2)) - 2 * Ip1 * Im2 := by ring
  rw [hid]
  have ham1 : -(2 * Ip2 * (Im1 + Im2)) ≤ 2 * Real.exp (-3 * b) * exponentialMass 8 F := by
    have hs := sq_nonneg (Real.exp (3 * b / 2) * Ip2 + Real.exp (-3 * b / 2) * (Im1 + Im2))
    have he1 : Real.exp (3 * b / 2) ^ 2 = Real.exp (3 * b) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    have he2 : Real.exp (-3 * b / 2) ^ 2 = Real.exp (-3 * b) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    have hec : Real.exp (3 * b / 2) * Real.exp (-3 * b / 2) = 1 := by
      rw [← Real.exp_add, show 3 * b / 2 + -3 * b / 2 = 0 by ring, Real.exp_zero]
    rw [add_sq, mul_pow, mul_pow, he1, he2] at hs
    have hc : 2 * (Real.exp (3 * b / 2) * Ip2) * (Real.exp (-3 * b / 2) * (Im1 + Im2)) =
        2 * Ip2 * (Im1 + Im2) := by
      linear_combination (2 * Ip2 * (Im1 + Im2)) * hec
    have hm1 := mul_le_mul_of_nonneg_left b2p (Real.exp_pos (3 * b)).le
    have hexp_cancel : Real.exp (3 * b) * (Real.exp (-6 * b) * exponentialMass 8 F) =
        Real.exp (-3 * b) * exponentialMass 8 F := by
      rw [← mul_assoc, ← Real.exp_add, show 3 * b + -6 * b = -3 * b by ring]
    have hFm_eq : Im1 + Im2 = ∫ u, F u * Real.exp (-(u / 2)) := hFm.symm
    rw [← hFm_eq] at bFm
    have hm2 := mul_le_mul_of_nonneg_left bFm (Real.exp_pos (-3 * b)).le
    linarith only [hs, hc, hm1, hexp_cancel, hm2]
  have ham2 : -(2 * Ip1 * Im2) ≤ 2 * Real.exp (-3 * b) * exponentialMass 8 F := by
    have hs := sq_nonneg (Real.exp (-3 * b / 2) * Ip1 + Real.exp (3 * b / 2) * Im2)
    have he1 : Real.exp (-3 * b / 2) ^ 2 = Real.exp (-3 * b) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    have he2 : Real.exp (3 * b / 2) ^ 2 = Real.exp (3 * b) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    have hec : Real.exp (-3 * b / 2) * Real.exp (3 * b / 2) = 1 := by
      rw [← Real.exp_add, show -3 * b / 2 + 3 * b / 2 = 0 by ring, Real.exp_zero]
    rw [add_sq, mul_pow, mul_pow, he1, he2] at hs
    have hc : 2 * (Real.exp (-3 * b / 2) * Ip1) * (Real.exp (3 * b / 2) * Im2) =
        2 * Ip1 * Im2 := by
      linear_combination (2 * Ip1 * Im2) * hec
    have hm1 := mul_le_mul_of_nonneg_left b1p (Real.exp_pos (-3 * b)).le
    have hm2 := mul_le_mul_of_nonneg_left b2m (Real.exp_pos (3 * b)).le
    have hexp_cancel : Real.exp (3 * b) * (Real.exp (-6 * b) * exponentialMass 8 F) =
        Real.exp (-3 * b) * exponentialMass 8 F := by
      rw [← mul_assoc, ← Real.exp_add, show 3 * b + -6 * b = -3 * b by ring]
    linarith only [hs, hc, hm1, hm2, hexp_cancel]
  dsimp only [b] at ham1 ham2
  linarith only [ham1, ham2]

/-! ### 5. Exponential growth of `windowThreshold` in the onset aperture -/

/-- **Smooth left-cutoff localization of `weilQuad`.** For any `2 < A₀` and any `C²` compactly
supported profile `F` vanishing on `(0, ∞)`, cutting `F` off smoothly on `[−A₀, 0]` increases
`weilQuad` by at most `windowCutoffLocalizationConstant * e^{−3 A₀} * exponentialMass 8 F`. -/
theorem weilQuad_windowLeftCutoff_sub_le {A₀ : ℝ} (hA₀ : 2 < A₀) {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (hF0 : ∀ u, 0 < u → F u = 0) :
    weilQuad (fun u => windowLeftCutoff A₀ u * F u) - weilQuad F ≤
      windowCutoffLocalizationConstant * Real.exp (-3 * A₀) * exponentialMass 8 F := by
  set H₁ : ℝ → ℝ := fun u => windowLeftCutoff A₀ u * F u
  have hH₁ : ContDiff ℝ 2 H₁ := (contDiff_windowLeftCutoff A₀).mul hF
  have hH₁c : HasCompactSupport H₁ := hFc.mul_left
  rw [weilQuad_eq_arch_sub_prime_add_pole hH₁ hH₁c, weilQuad_eq_arch_sub_prime_add_pole hF hFc]
  have harch := archForm_windowLeftCutoff_sub_le hA₀ hF hFc hF0
  have hprime := primeSum_sub_windowLeftCutoff_le hA₀ hF.continuous hFc hF0
  have hpole := pole_windowLeftCutoff_sub_le hA₀ hF.continuous hFc hF0
  have hexp : Real.exp (-3 * (A₀ - 1)) = Real.exp 3 * Real.exp (-3 * A₀) := by
    rw [← Real.exp_add]; congr 1; ring
  unfold windowCutoffLocalizationConstant
  dsimp only [H₁] at harch hprime hpole ⊢
  linarith only [harch, hprime, hpole,
    (by rw [hexp]; ring :
      (576 * Real.pi ^ 2 + 2 * |gammaHardyPhaseRate 0|) * Real.exp (-3 * (A₀ - 1)) *
          exponentialMass 8 F +
        2 * (1 + Real.exp 1) * vonMangoldtThreeHalvesMass * Real.exp (-3 * (A₀ - 1)) *
          exponentialMass 8 F +
        4 * Real.exp (-3 * (A₀ - 1)) * exponentialMass 8 F =
      Real.exp 3 * (576 * Real.pi ^ 2 + 2 * |gammaHardyPhaseRate 0| +
          2 * (1 + Real.exp 1) * vonMangoldtThreeHalvesMass + 4) *
        Real.exp (-3 * A₀) * exponentialMass 8 F)]

/-- **Exponential window threshold floor from any positive window `A₀`.** Whenever `0 ≤ A₀` has
`windowThreshold A₀ = ⊤`, every window `A : ℝ` satisfies
`windowThresholdExponentialConstant * e^{3 A₀} ≤ windowThreshold A`. -/
theorem windowThreshold_ge_exp_three_mul_of_eq_top {A₀ : ℝ} (_hA₀0 : 0 ≤ A₀)
    (htop : windowThreshold A₀ = ⊤) (A : ℝ) :
    ((windowThresholdExponentialConstant * Real.exp (3 * A₀) : ℝ) : EReal) ≤
      windowThreshold A := by
  by_cases hA₀2 : A₀ ≤ 2
  · refine le_trans (EReal.coe_le_coe_iff.mpr ?_) (apertureIndependentThreshold_le_windowThreshold A)
    have hm1 : windowThresholdExponentialConstant ≤ apertureIndependentThreshold * Real.exp (-6) :=
      min_le_left _ _
    have hexp : Real.exp (3 * A₀) ≤ Real.exp 6 := Real.exp_le_exp.mpr (by linarith only [hA₀2])
    have hm2 := mul_le_mul hm1 hexp (Real.exp_pos _).le (by
      have hJ := tiltedJordanOne_pos
      have hκ := splineAtom_pos
      have hF := exponentialWeilFloor_pos (by norm_num : (1 : ℝ) < 8)
      unfold apertureIndependentThreshold; positivity)
    exact hm2.trans_eq (by
      rw [mul_assoc, ← Real.exp_add, show (-6 : ℝ) + 6 = 0 by ring, Real.exp_zero, mul_one])
  · push Not at hA₀2
    have hpos_A₀ := windowThreshold_eq_top_iff.mp htop
    set F_loc := windowCutoffLocalizationConstant * Real.exp (-3 * A₀)
    have hC := windowCutoffLocalizationConstant_pos
    have hFloc_pos : 0 < F_loc := by dsimp only [F_loc]; positivity
    have hfloor : ∀ H : ℝ → ℝ, IsWindowTest A H → -weilQuad H ≤ F_loc * exponentialMass 8 H := by
      intro H hH
      have hH0 : ∀ u, 0 < u → H u = 0 := fun u hu =>
        hH.vanish u fun hm => not_le.mpr hu hm.2
      have hH₁_test := isWindowTest_windowLeftCutoff_mul A₀ hH.contDiff hH0
      have hQ₁ : 0 ≤ weilQuad (fun u => windowLeftCutoff A₀ u * H u) := hpos_A₀ _ hH₁_test
      have hdiff := weilQuad_windowLeftCutoff_sub_le hA₀2 hH.contDiff hH.hasCompactSupport hH0
      dsimp only [F_loc]
      linarith only [hQ₁, hdiff]
    refine le_trans (EReal.coe_le_coe_iff.mpr ?_) (le_windowThreshold_of_floor hFloc_pos hfloor)
    have hm1 : windowThresholdExponentialConstant ≤
        7 * tiltedJordanOne / (splineAtom * windowCutoffLocalizationConstant) :=
      min_le_right _ _
    refine (mul_le_mul_of_nonneg_right hm1 (Real.exp_pos _).le).trans_eq ?_
    dsimp only [F_loc]
    have hκ := splineAtom_pos.ne'
    have hCne := hC.ne'
    have hene := (Real.exp_pos (3 * A₀)).ne'
    rw [show -3 * A₀ = -(3 * A₀) by ring, Real.exp_neg]
    field_simp [hκ, hCne, hene]

/-- **Global infimum of `windowThreshold` grows at least like `e^{6 a}` in the onset aperture.**
For every `0 ≤ a` with `(a : EReal) ≤ onsetAperture zetaZeroConfig`,
`windowThresholdExponentialConstant * e^{6 a} ≤ ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A`. -/
theorem iInf_windowThreshold_ge_exp_six_mul_of_le_onsetAperture {a : ℝ} (ha0 : 0 ≤ a)
    (ha : (a : EReal) ≤ onsetAperture zetaZeroConfig) :
    ((windowThresholdExponentialConstant * Real.exp (6 * a) : ℝ) : EReal) ≤
      ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A := by
  have h2a0 : 0 ≤ 2 * a := by linarith
  have htop : windowThreshold (2 * a) = ⊤ := by
    rw [windowThreshold_eq_top_iff_le_onsetAperture h2a0]
    simpa only [mul_div_cancel_left₀ a two_ne_zero] using ha
  refine le_iInf fun A => le_iInf fun _ => ?_
  simpa only [show 3 * (2 * a) = 6 * a by ring] using
    windowThreshold_ge_exp_three_mul_of_eq_top h2a0 htop A

/-- **Endpoint-sharp off-RH exponential lower bound.** If `¬ RiemannHypothesis`,
`windowThresholdExponentialConstant * e^{6 zetaContactAperture} ≤ ⨅ A ≥ 0, windowThreshold A` with
zero endpoint loss. -/
theorem iInf_windowThreshold_ge_exp_six_mul_contact_of_not_rh (hRH : ¬ RiemannHypothesis) :
    ((windowThresholdExponentialConstant * Real.exp (6 * zetaContactAperture) : ℝ) : EReal) ≤
      ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A :=
  iInf_windowThreshold_ge_exp_six_mul_of_le_onsetAperture (zetaContactAperture_pos hRH).le
    (onsetAperture_zeta_eq_contact_of_not_rh hRH).ge

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
