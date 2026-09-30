import GaloisForLFunctions.RHTower.RiemannKernelTransformInjectivity
import GaloisForLFunctions.RHTower.WeilPositivityMajorantRigidity

/-!
# `Λ` is an extreme point of the full Weil cone

**Theorem** (`eq_zero_of_weilPositiveFull_add_of_sub`, unconditional). Let `w` be real weights with
`Σ |w(n)| n^{−2} < ∞`. If both `Λ + w` and `Λ − w` are Weil-positive with the pole term
(`WeilPositiveFull`), then `w(n) = 0` for all `n ≥ 2`.

No Herglotz representation, Schwarz reflection or continuation of `Σ w(n) n^{−s}` is used.

* **Two-sided bound** (`abs_atomPairing_le`). By the explicit formula, the functional of `Λ ± w`
  on `f ⋆ f̃` is `W(f, f) ∓ T_w(f)`, where
  `T_w(f) = Σ_{n ≥ 2} w(n) n^{−1/2} (k_f(log n) + k_f(−log n))`. So `|T_w(f)| ≤ Re W(f, f)`.
* **First-order perturbation of a near-null vector.** Put `f = Φχ_L + εH`, with `H` smooth and
  compactly supported. Then `T_w(f) = T_0 + 2εT_1 + ε²T_2` with `T_1 = T_w(Φχ_L, H)`, and
  `W(f, f) ≤ (5/4) S (E_L + εE_H)²` (`norm_W_le_of_zero_bound`). The energy `E_L` of the
  truncated kernel tends to `0`, so `T_1 → 0`.
* **Transform.** `T_1` tends to `∫ H G_w`, where `G_w(s) = Σ_n w(n) n^{−1/2}
  (Φ(s + log n) + Φ(s − log n))`. So `G_w ≡ 0`, and the injectivity of the Riemann-kernel
  transform (`eq_zero_of_riemannKernelTransform_eq_zero_of_sq`, Hamburger) gives `w = 0`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

namespace RHTower

noncomputable section

/-! ## Real correlations and the atom pairing -/

/-- `k_{X,Y}(y) = ∫ X(t) Y(t − y) dt`. -/
def crossCorr (X Y : ℝ → ℝ) (y : ℝ) : ℝ := ∫ t, X t * Y (t - y)

/-- `T_w(g) = Σ_{n ≥ 2} w(n) n^{−1/2} (g(log n) + g(−log n))`. -/
def atomPairing (w : ℕ → ℝ) (g : ℝ → ℝ) : ℝ :=
  ∑' n : ℕ, (if 2 ≤ n then w n / Real.sqrt n else 0) * (g (Real.log n) + g (-Real.log n))

theorem integrable_translate_prod {X Y : ℝ → ℝ} (hX : Continuous X) (hXc : HasCompactSupport X)
    (hY : Continuous Y) (y : ℝ) : Integrable fun t => X t * Y (t - y) :=
  (hX.mul (hY.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
    hXc.mul_right

theorem crossCorr_eq_zero {X Y : ℝ → ℝ} {R₁ R₂ : ℝ} (hX : ∀ t, R₁ < |t| → X t = 0)
    (hY : ∀ t, R₂ < |t| → Y t = 0) {y : ℝ} (hy : R₁ + R₂ < |y|) : crossCorr X Y y = 0 := by
  unfold crossCorr
  refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
  simp only [Pi.zero_apply]
  rcases le_or_gt |t| R₁ with ht | ht
  · have : R₂ < |t - y| := by
      have := abs_sub_abs_le_abs_sub y t
      rw [abs_sub_comm] at this; linarith
    rw [hY _ this, mul_zero]
  · rw [hX _ ht, zero_mul]

theorem crossCorr_swap {X Y : ℝ → ℝ} (y : ℝ) : crossCorr Y X y = crossCorr X Y (-y) := by
  unfold crossCorr
  rw [← integral_add_right_eq_self (μ := volume) (fun t => Y t * X (t - y)) y]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only
  rw [show t + y - y = t by ring, show t - -y = t + y by ring, mul_comm]

theorem summable_atomPairing (w : ℕ → ℝ) {g : ℝ → ℝ} {R : ℝ} (hg : ∀ y, R < |y| → g y = 0) :
    Summable fun n : ℕ =>
      (if 2 ≤ n then w n / Real.sqrt n else 0) * (g (Real.log n) + g (-Real.log n)) := by
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp (|R| + 1))
  refine summable_of_ne_finset_zero (s := Finset.range N) (fun n hn => ?_)
  rw [Finset.mem_range, not_lt] at hn
  have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (0 : ℝ) < n := lt_of_lt_of_le (lt_trans (Real.exp_pos _) hN) hnR
  have hlog : |R| + 1 < Real.log n := by rw [Real.lt_log_iff_exp_lt hpos]; linarith
  have hl0 : 0 < Real.log n := by linarith [abs_nonneg R]
  rw [hg _ (by rw [abs_of_pos hl0]; linarith [le_abs_self R]),
    hg _ (by rw [abs_neg, abs_of_pos hl0]; linarith [le_abs_self R]), add_zero, mul_zero]

theorem atomPairing_neg (w : ℕ → ℝ) (g : ℝ → ℝ) : atomPairing (fun n => -w n) g = -atomPairing w g := by
  unfold atomPairing
  rw [← tsum_neg]
  refine tsum_congr fun n => ?_
  split_ifs <;> ring

theorem atomPairing_reflect (w : ℕ → ℝ) (g : ℝ → ℝ) :
    atomPairing w (fun y => g (-y)) = atomPairing w g := by
  unfold atomPairing
  refine tsum_congr fun n => ?_
  simp only [neg_neg]; ring

theorem atomPairing_add_smul (w : ℕ → ℝ) {g₁ g₂ g₃ : ℝ → ℝ} {R : ℝ}
    (h₁ : ∀ y, R < |y| → g₁ y = 0) (h₂ : ∀ y, R < |y| → g₂ y = 0) (h₃ : ∀ y, R < |y| → g₃ y = 0)
    (a b : ℝ) :
    atomPairing w (fun y => g₁ y + a * g₂ y + b * g₃ y) =
      atomPairing w g₁ + a * atomPairing w g₂ + b * atomPairing w g₃ := by
  unfold atomPairing
  have s₁ := summable_atomPairing w h₁
  have s₂ := (summable_atomPairing w h₂).mul_left a
  have s₃ := (summable_atomPairing w h₃).mul_left b
  rw [← tsum_mul_left, ← tsum_mul_left, ← s₁.tsum_add s₂, ← (s₁.add s₂).tsum_add s₃]
  refine tsum_congr fun n => ?_
  ring

/-! ## The two-sided bound -/

/-- The functional of `Λ + v` on the autocorrelation of a real test. -/
theorem re_weilFullFunctional_add_eq (v : ℕ → ℝ) {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 fun u => (F u : ℂ)) (hFc : HasCompactSupport F) :
    (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) + v n)
      (EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ)))).re =
      (zetaZeroConfig.W (fun u => (F u : ℂ)) (fun u => (F u : ℂ))).re -
        atomPairing v (crossCorr F F) := by
  set f : ℝ → ℂ := fun u => (F u : ℂ) with hf
  have hfc : HasCompactSupport f := hFc.comp_left Complex.ofReal_zero
  have hk : EF.weilTest f f = fun y => ((crossCorr F F y : ℝ) : ℂ) :=
    funext fun y => weilTest_ofReal_eq F y
  have hkc : HasCompactSupport (EF.weilTest f f) := EF.weilTest_hasCompactSupport hfc hfc
  have hW : zetaZeroConfig.W f f = EF.literatureRHS (EF.weilTest f f) := by
    rw [zeta_W_eq_weilFullFunctional hF hfc, weilFullFunctional_vonMangoldt]
  rw [weilFullFunctional_eq_sub _ hkc, ← hW]
  have hsum : (∑' n : ℕ, ((if 2 ≤ n then ((ArithmeticFunction.vonMangoldt n : ℝ) + v n -
      ArithmeticFunction.vonMangoldt n) / Real.sqrt n else 0 : ℝ) : ℂ) *
        (EF.weilTest f f (Real.log n) + EF.weilTest f f (-Real.log n))) =
      ((atomPairing v (crossCorr F F) : ℝ) : ℂ) := by
    rw [atomPairing, Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    rw [hk]
    simp only [add_sub_cancel_left]
    push_cast
    ring
  rw [hsum, Complex.sub_re, Complex.ofReal_re]

/-- **Two-sided bound.** If `Λ ± w` are Weil-positive, then `|T_w(F)| ≤ Re W(F, F)` for every real
`C²` compactly supported test `F`. -/
theorem abs_atomPairing_le {w : ℕ → ℝ}
    (hp : WeilPositiveFull fun n => (ArithmeticFunction.vonMangoldt n : ℝ) + w n)
    (hm : WeilPositiveFull fun n => (ArithmeticFunction.vonMangoldt n : ℝ) - w n) {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 fun u => (F u : ℂ)) (hFc : HasCompactSupport F) :
    |atomPairing w (crossCorr F F)| ≤
      (zetaZeroConfig.W (fun u => (F u : ℂ)) (fun u => (F u : ℂ))).re := by
  have hfc : HasCompactSupport fun u => (F u : ℂ) := hFc.comp_left Complex.ofReal_zero
  have h1 := hp _ hF hfc
  have h2 := hm _ hF hfc
  rw [re_weilFullFunctional_add_eq w hF hFc] at h1
  have e : (fun n => (ArithmeticFunction.vonMangoldt n : ℝ) - w n) =
      fun n => (ArithmeticFunction.vonMangoldt n : ℝ) + (fun n => -w n) n := by
    funext n; ring
  rw [e, re_weilFullFunctional_add_eq (fun n => -w n) hF hFc, atomPairing_neg] at h2
  rw [abs_le]; constructor <;> linarith

theorem atomPairing_add (w : ℕ → ℝ) {g₁ g₂ : ℝ → ℝ} {R : ℝ}
    (h₁ : ∀ y, R < |y| → g₁ y = 0) (h₂ : ∀ y, R < |y| → g₂ y = 0) :
    atomPairing w (fun y => g₁ y + g₂ y) = atomPairing w g₁ + atomPairing w g₂ := by
  unfold atomPairing
  rw [← (summable_atomPairing w h₁).tsum_add (summable_atomPairing w h₂)]
  refine tsum_congr fun n => ?_
  ring

/-! ## Test functions and their transforms -/

theorem superExpDecay_ofReal {H : ℝ → ℝ} (hH : Continuous H) (hHc : HasCompactSupport H) :
    SuperExpDecay fun u => (H u : ℂ) := by
  refine ⟨Complex.continuous_ofReal.comp hH, fun c => ?_⟩
  refine ((Complex.continuous_ofReal.comp hH).norm.mul
    (by fun_prop : Continuous fun u : ℝ => Real.exp (c * |u|))).integrable_of_hasCompactSupport ?_
  exact (hHc.comp_left Complex.ofReal_zero).norm.mul_right

/-- In the critical strip, `(1 + |Re z|) |Ĝ(z)| ≤ ∫ |G| e^{|u|/2} + ∫ |G'| e^{|u|/2}`. -/
theorem one_add_abs_re_mul_norm_paperFT_le {G G' : ℝ → ℂ} (hG : SuperExpDecay G)
    (hG' : SuperExpDecay G') (hd : ∀ x, HasDerivAt G (G' x) x) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    (1 + |z.re|) * ‖paperFT G z‖ ≤
      (∫ u : ℝ, ‖G u‖ * Real.exp (1 / 2 * |u|)) + ∫ u : ℝ, ‖G' u‖ * Real.exp (1 / 2 * |u|) := by
  have h1 := norm_paperFT_le_weighted hG hz
  have hder := paperFT_deriv_of_superExpDecay hG hG' hd z
  have h2 := norm_paperFT_le_weighted hG' hz
  rw [hder, norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul] at h2
  have hre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hn := norm_nonneg (paperFT G z)
  nlinarith [mul_le_mul_of_nonneg_right hre hn]

/-- The weighted energy `∫ |H| e^{|u|/2} + ∫ |H'| e^{|u|/2}` of a real test. -/
def testEnergy (H : ℝ → ℝ) : ℝ :=
  (∫ u : ℝ, ‖((H u : ℝ) : ℂ)‖ * Real.exp (1 / 2 * |u|)) +
    ∫ u : ℝ, ‖((deriv H u : ℝ) : ℂ)‖ * Real.exp (1 / 2 * |u|)

theorem testEnergy_nonneg (H : ℝ → ℝ) : 0 ≤ testEnergy H :=
  add_nonneg (integral_nonneg fun _ => by positivity) (integral_nonneg fun _ => by positivity)

theorem test_zero_bound {H : ℝ → ℝ} (hH : ContDiff ℝ 2 H) (hHc : HasCompactSupport H)
    (ρ : zetaZeroConfig.carrier) :
    (1 + |(ρ : ℂ).im|) * ‖paperFT (fun u => (H u : ℂ)) (gammaOf ρ)‖ ≤ testEnergy H ∧
      (1 + |(ρ : ℂ).im|) * ‖paperFT (fun u => (H u : ℂ)) ((starRingEnd ℂ) (gammaOf ρ))‖ ≤
        testEnergy H := by
  have hG := superExpDecay_ofReal hH.continuous hHc
  have hG' := superExpDecay_ofReal (hH.continuous_deriv (by norm_num)) hHc.deriv
  have hd : ∀ x, HasDerivAt (fun u => (H u : ℂ)) ((deriv H x : ℝ) : ℂ) x := fun x =>
    ((hH.differentiable (by norm_num)) x).hasDerivAt.ofReal_comp
  have hmem := ρ.2
  have hstrip' : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
    have h : IsNontrivialZero (ρ : ℂ) := hmem
    exact ⟨h.2.1, h.2.2⟩
  have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt hstrip').le
  have hIm' : |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by
    rw [Complex.conj_im, abs_neg]; exact hIm
  constructor
  · have h := one_add_abs_re_mul_norm_paperFT_le hG hG' hd hIm
    rwa [WeilEF.gammaOf_re] at h
  · have h := one_add_abs_re_mul_norm_paperFT_le hG hG' hd hIm'
    rwa [Complex.conj_re, WeilEF.gammaOf_re] at h

theorem integrable_ofReal_mul_cexp_of_hasCompactSupport {H : ℝ → ℝ} (hH : Continuous H) (hHc : HasCompactSupport H)
    (z : ℂ) : Integrable fun u : ℝ => (H u : ℂ) * Complex.exp (I * z * u) :=
  ((Complex.continuous_ofReal.comp hH).mul (by fun_prop)).integrable_of_hasCompactSupport
    (hHc.comp_left Complex.ofReal_zero).mul_right

theorem continuous_truncatedRiemannKernelReal₀ (L : ℝ) : Continuous (truncatedRiemannKernelReal L) :=
  continuous_truncatedRiemannKernelReal L

theorem truncatedRiemannKernelReal_eq_zero {L u : ℝ} (hu : L < |u|) :
    truncatedRiemannKernelReal L u = 0 := by
  have h := truncatedRiemannKernel_eq_zero hu
  rw [truncatedRiemannKernel_eq] at h
  exact_mod_cast h

/-- The perturbed near-null vector `Φχ_L + εH` as a real function. -/
def perturbedKernel (L ε : ℝ) (H : ℝ → ℝ) (u : ℝ) : ℝ := truncatedRiemannKernelReal L u + ε * H u

theorem ofReal_perturbedKernel (L ε : ℝ) (H : ℝ → ℝ) :
    (fun u => (perturbedKernel L ε H u : ℂ)) =
      fun u => truncatedRiemannKernel L u + (ε : ℂ) * (H u : ℂ) := by
  funext u; rw [truncatedRiemannKernel_eq, perturbedKernel]; push_cast; ring

theorem contDiff_perturbedKernel (L ε : ℝ) {H : ℝ → ℝ} (hH : ContDiff ℝ 2 H) :
    ContDiff ℝ 2 fun u => (perturbedKernel L ε H u : ℂ) := by
  rw [ofReal_perturbedKernel]
  exact (contDiff_nearRadicalTest L _).add (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hH))

theorem hasCompactSupport_perturbedKernel (L ε : ℝ) {H : ℝ → ℝ} (hHc : HasCompactSupport H) :
    HasCompactSupport (perturbedKernel L ε H) :=
  (hasCompactSupport_truncatedRiemannKernelReal L).add (hHc.mul_left)

/-- The zero side of the perturbed vector: `‖W‖ ≤ (5/4) S (E_L + |ε| E_H)²`. -/
theorem norm_W_perturbedKernel_le (L ε : ℝ) {H : ℝ → ℝ} (hH : ContDiff ℝ 2 H)
    (hHc : HasCompactSupport H) :
    ‖zetaZeroConfig.W (fun u => (perturbedKernel L ε H u : ℂ)) (fun u => (perturbedKernel L ε H u : ℂ))‖ ≤
      (5 / 4) * zetaInvSqSum * (truncatedRiemannTailEnergy L + |ε| * testEnergy H) ^ 2 := by
  obtain ⟨Λ', -, hΛ'⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  have hE0 := truncatedRiemannTailEnergy_nonneg L
  have hH0 := testEnergy_nonneg H
  have hlin : ∀ z : ℂ, paperFT (fun u => (perturbedKernel L ε H u : ℂ)) z =
      paperFT (truncatedRiemannKernel L) z + (ε : ℂ) * paperFT (fun u => (H u : ℂ)) z := by
    intro z
    rw [ofReal_perturbedKernel]
    unfold paperFT
    have h0 : Integrable fun u : ℝ => truncatedRiemannKernel L u * Complex.exp (I * z * u) := by
      simpa using integrable_translate_mul_cexp L 0 z
    have h1 := (integrable_ofReal_mul_cexp_of_hasCompactSupport hH.continuous hHc z).const_mul (ε : ℂ)
    rw [← integral_const_mul, ← integral_add h0 h1]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only; ring
  refine norm_W_le_of_zero_bound (by positivity) fun ρ => ?_
  obtain ⟨hu1, hu2⟩ := truncatedRiemannKernel_zero_bound L hΛ' ρ
  obtain ⟨hh1, hh2⟩ := test_zero_bound hH hHc ρ
  have hd : 0 ≤ 1 + |(ρ : ℂ).im| := by positivity
  constructor
  · rw [hlin]
    calc (1 + |(ρ : ℂ).im|) * ‖paperFT (truncatedRiemannKernel L) (gammaOf ρ) +
          (ε : ℂ) * paperFT (fun u => (H u : ℂ)) (gammaOf ρ)‖
        ≤ (1 + |(ρ : ℂ).im|) * ‖paperFT (truncatedRiemannKernel L) (gammaOf ρ)‖ +
          |ε| * ((1 + |(ρ : ℂ).im|) * ‖paperFT (fun u => (H u : ℂ)) (gammaOf ρ)‖) := by
          have := norm_add_le (paperFT (truncatedRiemannKernel L) (gammaOf ρ))
            ((ε : ℂ) * paperFT (fun u => (H u : ℂ)) (gammaOf ρ))
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at this
          nlinarith
      _ ≤ _ := by nlinarith [abs_nonneg ε]
  · rw [hlin]
    calc (1 + |(ρ : ℂ).im|) * ‖paperFT (truncatedRiemannKernel L) ((starRingEnd ℂ) (gammaOf ρ)) +
          (ε : ℂ) * paperFT (fun u => (H u : ℂ)) ((starRingEnd ℂ) (gammaOf ρ))‖
        ≤ (1 + |(ρ : ℂ).im|) * ‖paperFT (truncatedRiemannKernel L) ((starRingEnd ℂ) (gammaOf ρ))‖ +
          |ε| * ((1 + |(ρ : ℂ).im|) *
            ‖paperFT (fun u => (H u : ℂ)) ((starRingEnd ℂ) (gammaOf ρ))‖) := by
          have := norm_add_le (paperFT (truncatedRiemannKernel L) ((starRingEnd ℂ) (gammaOf ρ)))
            ((ε : ℂ) * paperFT (fun u => (H u : ℂ)) ((starRingEnd ℂ) (gammaOf ρ)))
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at this
          nlinarith
      _ ≤ _ := by nlinarith [abs_nonneg ε]

/-! ## The first-order inequality -/

theorem crossCorr_perturbedKernel (L ε : ℝ) {H : ℝ → ℝ} (hH : Continuous H)
    (hHc : HasCompactSupport H) (y : ℝ) :
    crossCorr (perturbedKernel L ε H) (perturbedKernel L ε H) y =
      crossCorr (truncatedRiemannKernelReal L) (truncatedRiemannKernelReal L) y +
        ε * (crossCorr (truncatedRiemannKernelReal L) H y + crossCorr H (truncatedRiemannKernelReal L) y) +
        ε ^ 2 * crossCorr H H y := by
  have hU := continuous_truncatedRiemannKernelReal L
  have hUc := hasCompactSupport_truncatedRiemannKernelReal L
  have i1 := integrable_translate_prod hU hUc hU y
  have i2 := (integrable_translate_prod hU hUc hH y).const_mul ε
  have i3 := (integrable_translate_prod hH hHc hU y).const_mul ε
  have i4 := (integrable_translate_prod hH hHc hH y).const_mul (ε ^ 2)
  have i23 : Integrable fun t => ε * (truncatedRiemannKernelReal L t * H (t - y)) +
      ε * (H t * truncatedRiemannKernelReal L (t - y)) := i2.add i3
  have i123 : Integrable fun t => truncatedRiemannKernelReal L t * truncatedRiemannKernelReal L (t - y) +
      (ε * (truncatedRiemannKernelReal L t * H (t - y)) +
        ε * (H t * truncatedRiemannKernelReal L (t - y))) := i1.add i23
  unfold crossCorr perturbedKernel
  have e : (fun t => (truncatedRiemannKernelReal L t + ε * H t) *
      (truncatedRiemannKernelReal L (t - y) + ε * H (t - y))) =
      fun t => truncatedRiemannKernelReal L t * truncatedRiemannKernelReal L (t - y) +
        (ε * (truncatedRiemannKernelReal L t * H (t - y)) +
          ε * (H t * truncatedRiemannKernelReal L (t - y))) + ε ^ 2 * (H t * H (t - y)) := by
    funext t; ring
  rw [e, integral_add i123 i4, integral_add i1 i23, integral_add i2 i3, integral_const_mul,
    integral_const_mul, integral_const_mul]
  ring

theorem exists_vanish_of_hasCompactSupport {H : ℝ → ℝ} (hHc : HasCompactSupport H) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t, R < |t| → H t = 0 := by
  obtain ⟨R, hR⟩ := hHc.isCompact.isBounded.subset_closedBall 0
  refine ⟨|R|, abs_nonneg R, fun t ht => ?_⟩
  by_contra hne
  have hmem := hR (subset_tsupport H hne)
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hmem
  linarith [le_abs_self R]

/-- **Expansion of the pairing along `Φχ_L + εH`.** -/
theorem atomPairing_perturbedKernel (w : ℕ → ℝ) (L ε : ℝ) {H : ℝ → ℝ} (hH : Continuous H)
    (hHc : HasCompactSupport H) :
    atomPairing w (crossCorr (perturbedKernel L ε H) (perturbedKernel L ε H)) =
      atomPairing w (crossCorr (truncatedRiemannKernelReal L) (truncatedRiemannKernelReal L)) +
        2 * ε * atomPairing w (crossCorr (truncatedRiemannKernelReal L) H) +
        ε ^ 2 * atomPairing w (crossCorr H H) := by
  obtain ⟨R, hR0, hR⟩ := exists_vanish_of_hasCompactSupport hHc
  have hU : ∀ t, |L| < |t| → truncatedRiemannKernelReal L t = 0 := fun t ht =>
    truncatedRiemannKernelReal_eq_zero (lt_of_le_of_lt (le_abs_self L) ht)
  set R₀ := 2 * (|L| + R) with hR₀
  have hvan : ∀ {X Y : ℝ → ℝ} {R₁ R₂ : ℝ}, (∀ t, R₁ < |t| → X t = 0) → (∀ t, R₂ < |t| → Y t = 0) →
      R₁ + R₂ ≤ R₀ → ∀ y, R₀ < |y| → crossCorr X Y y = 0 := fun hX hY hle y hy =>
    crossCorr_eq_zero hX hY (by linarith)
  have hL0 := abs_nonneg L
  have vUU := hvan hU hU (by rw [hR₀]; linarith)
  have vUH := hvan hU hR (by rw [hR₀]; linarith)
  have vHU := hvan hR hU (by rw [hR₀]; linarith)
  have vHH := hvan hR hR (by rw [hR₀]; linarith)
  have hmid : ∀ y, R₀ < |y| → crossCorr (truncatedRiemannKernelReal L) H y +
      crossCorr H (truncatedRiemannKernelReal L) y = 0 := fun y hy => by
    rw [vUH y hy, vHU y hy, add_zero]
  rw [show crossCorr (perturbedKernel L ε H) (perturbedKernel L ε H) = fun y =>
      crossCorr (truncatedRiemannKernelReal L) (truncatedRiemannKernelReal L) y +
        ε * (crossCorr (truncatedRiemannKernelReal L) H y +
          crossCorr H (truncatedRiemannKernelReal L) y) + ε ^ 2 * crossCorr H H y from
      funext (crossCorr_perturbedKernel L ε hH hHc)]
  rw [atomPairing_add_smul w vUU hmid vHH, atomPairing_add w vUH vHU]
  have hswap : atomPairing w (crossCorr H (truncatedRiemannKernelReal L)) =
      atomPairing w (crossCorr (truncatedRiemannKernelReal L) H) := by
    rw [show crossCorr H (truncatedRiemannKernelReal L) =
        fun y => crossCorr (truncatedRiemannKernelReal L) H (-y) from funext fun y => crossCorr_swap y,
      atomPairing_reflect]
  rw [hswap]; ring

/-- **The first-order inequality.** With `S = S_Z`, `E_L` the tail energy of `Φχ_L` and `ε > 0`:
`2ε |T_w(Φχ_L, H)| ≤ (5/4)S E_L² + (5/4)S (E_L + εE_H)² + ε² |T_w(H, H)|`. -/
theorem two_mul_abs_atomPairing_le {w : ℕ → ℝ}
    (hp : WeilPositiveFull fun n => (ArithmeticFunction.vonMangoldt n : ℝ) + w n)
    (hm : WeilPositiveFull fun n => (ArithmeticFunction.vonMangoldt n : ℝ) - w n) {H : ℝ → ℝ}
    (hH : ContDiff ℝ 2 H) (hHc : HasCompactSupport H) (L : ℝ) {ε : ℝ} (hε : 0 < ε) :
    2 * ε * |atomPairing w (crossCorr (truncatedRiemannKernelReal L) H)| ≤
      (5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2 +
        (5 / 4) * zetaInvSqSum * (truncatedRiemannTailEnergy L + ε * testEnergy H) ^ 2 +
        ε ^ 2 * |atomPairing w (crossCorr H H)| := by
  have bound : ∀ e : ℝ, |atomPairing w (crossCorr (perturbedKernel L e H) (perturbedKernel L e H))| ≤
      (5 / 4) * zetaInvSqSum * (truncatedRiemannTailEnergy L + |e| * testEnergy H) ^ 2 := by
    intro e
    refine (abs_atomPairing_le hp hm (contDiff_perturbedKernel L e hH)
      (hasCompactSupport_perturbedKernel L e hHc)).trans ?_
    exact (Complex.re_le_norm _).trans (norm_W_perturbedKernel_le L e hH hHc)
  have b0 := bound 0
  have b1 := bound ε
  rw [atomPairing_perturbedKernel w L 0 hH.continuous hHc] at b0
  rw [atomPairing_perturbedKernel w L ε hH.continuous hHc, abs_of_pos hε] at b1
  simp only [abs_zero, zero_mul, add_zero, mul_zero, zero_pow two_ne_zero] at b0
  set T0 := atomPairing w (crossCorr (truncatedRiemannKernelReal L) (truncatedRiemannKernelReal L))
  set T1 := atomPairing w (crossCorr (truncatedRiemannKernelReal L) H)
  set T2 := atomPairing w (crossCorr H H)
  have key : 2 * ε * T1 = (T0 + 2 * ε * T1 + ε ^ 2 * T2) - T0 - ε ^ 2 * T2 := by ring
  have hT2 : |ε ^ 2 * T2| = ε ^ 2 * |T2| := by rw [abs_mul, abs_of_nonneg (sq_nonneg ε)]
  calc 2 * ε * |T1| = |2 * ε * T1| := by rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * ε)]
    _ = |(T0 + 2 * ε * T1 + ε ^ 2 * T2) - T0 - ε ^ 2 * T2| := by rw [← key]
    _ ≤ |T0 + 2 * ε * T1 + ε ^ 2 * T2| + |T0| + |ε ^ 2 * T2| := by
        have h1 := abs_sub (T0 + 2 * ε * T1 + ε ^ 2 * T2 - T0) (ε ^ 2 * T2)
        have h2 := abs_sub (T0 + 2 * ε * T1 + ε ^ 2 * T2) T0
        linarith
    _ ≤ _ := by rw [hT2]; linarith

/-! ## Decay estimates -/

theorem exists_riemannKernelReal_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, riemannKernelReal x ≤ C * Real.exp (-(4 * |x|)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_riemannPhiKernel_le_exp (B := 4) (by norm_num)
  refine ⟨C, hC0, fun x => ?_⟩
  have h := hC x
  rwa [riemannPhiKernel_eq_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (riemannKernelReal_pos x)] at h

/-- The truncation defect `Φ − Φχ_L` is `≤ C e^{−2(L−1)} e^{−2|t|}`. -/
theorem riemannKernelReal_sub_truncated_le {C : ℝ}
    (hC : ∀ x, riemannKernelReal x ≤ C * Real.exp (-(4 * |x|))) (L t : ℝ) :
    0 ≤ riemannKernelReal t - truncatedRiemannKernelReal L t ∧
      riemannKernelReal t - truncatedRiemannKernelReal L t ≤
        C * Real.exp (-(2 * (L - 1))) * Real.exp (-(2 * |t|)) := by
  have hpos := riemannKernelReal_pos t
  have hb1 := bulkCutoff_le_one L t
  have hb0 := bulkCutoff_nonneg L t
  unfold truncatedRiemannKernelReal
  constructor
  · nlinarith
  · rcases le_or_gt |t| (L - 1) with ht | ht
    · rw [bulkCutoff_eq_one ht, mul_one, sub_self]
      have hC0 : 0 ≤ C := by
        have := hC 0; have := Real.exp_pos (-(4 * |(0 : ℝ)|)); nlinarith [riemannKernelReal_pos 0]
      positivity
    · calc riemannKernelReal t - riemannKernelReal t * bulkCutoff L t ≤ riemannKernelReal t := by
            nlinarith
        _ ≤ C * Real.exp (-(4 * |t|)) := hC t
        _ = C * (Real.exp (-(2 * |t|)) * Real.exp (-(2 * |t|))) := by
            rw [← Real.exp_add]; ring_nf
        _ ≤ C * (Real.exp (-(2 * (L - 1))) * Real.exp (-(2 * |t|))) := by
            have hC0 : 0 ≤ C := by
              have := hC t; have := Real.exp_pos (-(4 * |t|)); nlinarith
            gcongr
        _ = _ := by ring

/-- `|∫ Z(t) H(t − y) dt| ≤ M A · 2R e^{2R} · e^{−2|y|}` when `|Z(t)| ≤ A e^{−2|t|}`, `|H| ≤ M`
and `H` vanishes outside `[−R, R]`. -/
theorem abs_integral_mul_translate_le {Z H : ℝ → ℝ} {A M R : ℝ} (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hR : 0 ≤ R) (hZ : ∀ t, |Z t| ≤ A * Real.exp (-(2 * |t|))) (hHM : ∀ t, |H t| ≤ M)
    (hHR : ∀ t, R < |t| → H t = 0) (y : ℝ) :
    |∫ t, Z t * H (t - y)| ≤ M * A * (2 * R) * Real.exp (2 * R) * Real.exp (-(2 * |y|)) := by
  have hsupp : ∀ t ∉ Icc (y - R) (y + R), Z t * H (t - y) = 0 := by
    intro t ht
    have : R < |t - y| := by
      rw [mem_Icc, not_and_or, not_le, not_le] at ht
      rcases ht with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    rw [hHR _ this, mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp, ← Real.norm_eq_abs]
  have hbound : ∀ t ∈ Icc (y - R) (y + R),
      ‖Z t * H (t - y)‖ ≤ M * A * Real.exp (2 * R) * Real.exp (-(2 * |y|)) := by
    intro t ht
    have hty : |t - y| ≤ R := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
    have hyt : |y| - R ≤ |t| := by
      have := abs_sub_abs_le_abs_sub y t; rw [abs_sub_comm] at this; linarith
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := hZ t
    have h2 := hHM (t - y)
    have he : Real.exp (-(2 * |t|)) ≤ Real.exp (2 * R) * Real.exp (-(2 * |y|)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    calc |Z t| * |H (t - y)| ≤ (A * Real.exp (-(2 * |t|))) * M :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ ≤ (A * (Real.exp (2 * R) * Real.exp (-(2 * |y|)))) * M := by gcongr
      _ = _ := by ring
  have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (y - R) (y + R))
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top) hbound
  rw [Real.volume_real_Icc_of_le (by linarith)] at h
  calc _ ≤ M * A * Real.exp (2 * R) * Real.exp (-(2 * |y|)) * (y + R - (y - R)) := h
    _ = _ := by ring

/-- A pairing against a function with `|g(y)| ≤ K e^{−2|y|}` converges and is at most
`2K Σ |w(n)|/n²`. -/
theorem summable_atomPairing_of_decay {w : ℕ → ℝ} (hw2 : Summable fun n : ℕ => |w n| / (n : ℝ) ^ 2)
    {g : ℝ → ℝ} {K : ℝ} (hg : ∀ y, |g y| ≤ K * Real.exp (-(2 * |y|))) :
    Summable (fun n : ℕ =>
      (if 2 ≤ n then w n / Real.sqrt n else 0) * (g (Real.log n) + g (-Real.log n))) ∧
    |atomPairing w g| ≤ 2 * K * ∑' n : ℕ, |w n| / (n : ℝ) ^ 2 := by
  have hK : 0 ≤ K := by have := hg 0; have := Real.exp_pos (-(2 * |(0 : ℝ)|)); nlinarith [abs_nonneg (g 0)]
  have hpt : ∀ n : ℕ, |(if 2 ≤ n then w n / Real.sqrt n else 0) * (g (Real.log n) + g (-Real.log n))| ≤
      2 * K * (|w n| / (n : ℝ) ^ 2) := by
    intro n
    split_ifs with h2
    · have hn : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
      have hnpos : (0 : ℝ) < n := by linarith
      have hsq : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hn
      have hlog := Real.log_nonneg hn
      have he : Real.exp (-(2 * |Real.log n|)) = 1 / (n : ℝ) ^ 2 := by
        rw [abs_of_nonneg hlog, show -(2 * Real.log n) = -(Real.log n + Real.log n) by ring,
          Real.exp_neg, Real.exp_add, Real.exp_log hnpos]; ring
      have he' : Real.exp (-(2 * |-Real.log n|)) = 1 / (n : ℝ) ^ 2 := by rw [abs_neg, he]
      have hg1 := hg (Real.log n)
      have hg2 := hg (-Real.log n)
      rw [he] at hg1; rw [he'] at hg2
      rw [abs_mul, abs_div, abs_of_pos (by positivity : (0 : ℝ) < Real.sqrt n)]
      have hsum : |g (Real.log n) + g (-Real.log n)| ≤ 2 * (K * (1 / (n : ℝ) ^ 2)) := by
        have := abs_add_le (g (Real.log n)) (g (-Real.log n)); linarith
      calc |w n| / Real.sqrt n * |g (Real.log n) + g (-Real.log n)|
          ≤ |w n| * (2 * (K * (1 / (n : ℝ) ^ 2))) := by
            have : |w n| / Real.sqrt n ≤ |w n| := div_le_self (abs_nonneg _) hsq
            exact mul_le_mul this hsum (abs_nonneg _) (abs_nonneg _)
        _ = 2 * K * (|w n| / (n : ℝ) ^ 2) := by ring
    · simp only [zero_mul, abs_zero]; positivity
  have hs : Summable fun n : ℕ =>
      (if 2 ≤ n then w n / Real.sqrt n else 0) * (g (Real.log n) + g (-Real.log n)) :=
    Summable.of_norm_bounded (hw2.mul_left (2 * K)) fun n => by rw [Real.norm_eq_abs]; exact hpt n
  refine ⟨hs, ?_⟩
  unfold atomPairing
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm hs.norm).trans ?_
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun n => by rw [Real.norm_eq_abs]; exact hpt n) hs.norm
    (hw2.mul_left _)

/-! ## The Riemann-kernel transform of the weights -/

/-- `G_w(s) = Σ_{n ≥ 2} w(n) n^{−1/2} (Φ(s + log n) + Φ(s − log n))`. -/
def weightKernelTransform (w : ℕ → ℝ) (s : ℝ) : ℝ :=
  ∑' n : ℕ, (if 2 ≤ n then w n / Real.sqrt n else 0) *
    (riemannKernelReal (s + Real.log n) + riemannKernelReal (s - Real.log n))

/-- For `n ≥ 1` and `|s| ≤ R`: `Φ(s ± log n) ≤ C e^{4R} n^{−2}`. -/
theorem riemannKernelReal_shift_le {C : ℝ} (hC : ∀ x, riemannKernelReal x ≤ C * Real.exp (-(4 * |x|)))
    (hC0 : 0 ≤ C) {R s : ℝ} (hs : |s| ≤ R) {n : ℕ} (hn : 1 ≤ n) :
    riemannKernelReal (s + Real.log n) + riemannKernelReal (s - Real.log n) ≤
      2 * (C * Real.exp (4 * R)) * (1 / (n : ℝ) ^ 2) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hlog := Real.log_nonneg hnR
  have hkey : ∀ v : ℝ, Real.log n - R ≤ |v| →
      riemannKernelReal v ≤ C * Real.exp (4 * R) * (1 / (n : ℝ) ^ 2) := by
    intro v hv
    have h1 : Real.exp (-(4 * |v|)) ≤ Real.exp (4 * R) * Real.exp (-(2 * Real.log n)) := by
      rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith [abs_nonneg s]
    have h2 : Real.exp (-(2 * Real.log n)) = 1 / (n : ℝ) ^ 2 := by
      rw [show -(2 * Real.log n) = -(Real.log n + Real.log n) by ring, Real.exp_neg, Real.exp_add,
        Real.exp_log hnpos]; ring
    calc riemannKernelReal v ≤ C * Real.exp (-(4 * |v|)) := hC v
      _ ≤ C * (Real.exp (4 * R) * Real.exp (-(2 * Real.log n))) := mul_le_mul_of_nonneg_left h1 hC0
      _ = _ := by rw [h2]; ring
  have e1 := hkey (s + Real.log n) (by
    have := abs_sub_abs_le_abs_sub (Real.log n) (-s)
    rw [abs_neg, abs_of_nonneg hlog, show Real.log n - -s = s + Real.log n by ring] at this
    linarith)
  have e2 := hkey (s - Real.log n) (by
    have := abs_sub_abs_le_abs_sub (Real.log n) s
    rw [abs_of_nonneg hlog, abs_sub_comm] at this
    linarith)
  linarith

theorem abs_weightTerm_le {w : ℕ → ℝ} {C : ℝ}
    (hC : ∀ x, riemannKernelReal x ≤ C * Real.exp (-(4 * |x|))) (hC0 : 0 ≤ C) {R s : ℝ}
    (hs : |s| ≤ R) (n : ℕ) :
    |(if 2 ≤ n then w n / Real.sqrt n else 0) *
      (riemannKernelReal (s + Real.log n) + riemannKernelReal (s - Real.log n))| ≤
      2 * (C * Real.exp (4 * R)) * (|w n| / (n : ℝ) ^ 2) := by
  split_ifs with h2
  · have hn : 1 ≤ n := by omega
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hsq : 1 ≤ Real.sqrt n := Real.one_le_sqrt.mpr hnR
    have hb := riemannKernelReal_shift_le hC hC0 hs hn
    have hp : 0 ≤ riemannKernelReal (s + Real.log n) + riemannKernelReal (s - Real.log n) :=
      add_nonneg (riemannKernelReal_pos _).le (riemannKernelReal_pos _).le
    rw [abs_mul, abs_of_nonneg hp, abs_div, abs_of_pos (by positivity : (0 : ℝ) < Real.sqrt n)]
    calc |w n| / Real.sqrt n * (riemannKernelReal (s + Real.log n) +
          riemannKernelReal (s - Real.log n))
        ≤ |w n| * (2 * (C * Real.exp (4 * R)) * (1 / (n : ℝ) ^ 2)) :=
          mul_le_mul (div_le_self (abs_nonneg _) hsq) hb hp (abs_nonneg _)
      _ = _ := by ring
  · simp only [zero_mul, abs_zero]; positivity

theorem continuous_weightKernelTransform {w : ℕ → ℝ}
    (hw2 : Summable fun n : ℕ => |w n| / (n : ℝ) ^ 2) : Continuous (weightKernelTransform w) := by
  obtain ⟨C, hC0, hC⟩ := exists_riemannKernelReal_le
  refine continuous_iff_continuousAt.mpr fun s₀ => ?_
  set R := |s₀| + 1
  have hon : ContinuousOn (weightKernelTransform w) (Icc (-R) R) := by
    refine continuousOn_tsum (fun n => Continuous.continuousOn ?_)
      (hw2.mul_left (2 * (C * Real.exp (4 * R)))) fun n s hs => ?_
    · exact continuous_const.mul ((continuous_riemannKernelReal.comp (continuous_id.add
        continuous_const)).add (continuous_riemannKernelReal.comp (continuous_id.sub continuous_const)))
    · rw [Real.norm_eq_abs]
      exact abs_weightTerm_le hC hC0 (abs_le.mpr ⟨hs.1, hs.2⟩) n
  exact hon.continuousAt (Icc_mem_nhds (by linarith [neg_abs_le s₀]) (by linarith [le_abs_self s₀]))

theorem summable_weightTerm {w : ℕ → ℝ} (hw2 : Summable fun n : ℕ => |w n| / (n : ℝ) ^ 2) (s : ℝ) :
    Summable fun n : ℕ => (if 2 ≤ n then w n / Real.sqrt n else 0) *
      (riemannKernelReal (s + Real.log n) + riemannKernelReal (s - Real.log n)) := by
  obtain ⟨C, hC0, hC⟩ := exists_riemannKernelReal_le
  exact Summable.of_norm_bounded (hw2.mul_left (2 * (C * Real.exp (4 * |s|)))) fun n => by
    rw [Real.norm_eq_abs]; exact abs_weightTerm_le hC hC0 le_rfl n

theorem integrable_mul_translate_right {X Y : ℝ → ℝ} (hX : Continuous X) (hY : Continuous Y)
    (hYc : HasCompactSupport Y) (y : ℝ) : Integrable fun t => X t * Y (t - y) :=
  (hX.mul (hY.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
    (HasCompactSupport.mul_left (hYc.comp_homeomorph (Homeomorph.subRight y)))

/-- **Fubini.** `T_w(Φ, H) = ∫ H G_w`. -/
theorem atomPairing_riemannKernel_eq_integral {w : ℕ → ℝ}
    (hw2 : Summable fun n : ℕ => |w n| / (n : ℝ) ^ 2) {H : ℝ → ℝ} (hH : Continuous H)
    (hHc : HasCompactSupport H) :
    atomPairing w (crossCorr riemannKernelReal H) = ∫ s, H s * weightKernelTransform w s := by
  obtain ⟨C, hC0, hC⟩ := exists_riemannKernelReal_le
  obtain ⟨R, hR0, hR⟩ := exists_vanish_of_hasCompactSupport hHc
  obtain ⟨M, hM⟩ : ∃ M, ∀ t, |H t| ≤ M := by
    obtain ⟨M, hM⟩ := hH.bounded_above_of_compact_support hHc
    exact ⟨M, fun t => by rw [← Real.norm_eq_abs]; exact hM t⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set c : ℕ → ℝ := fun n => if 2 ≤ n then w n / Real.sqrt n else 0 with hc
  set F : ℕ → ℝ → ℝ := fun n s => c n * (H s * (riemannKernelReal (s + Real.log n) +
    riemannKernelReal (s - Real.log n))) with hF
  have hΦc := continuous_riemannKernelReal
  have hFi : ∀ n, Integrable (F n) := by
    intro n
    have h1 : Integrable fun s => H s * riemannKernelReal (s + Real.log n) :=
      (hH.mul (hΦc.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
        hHc.mul_right
    have h2 : Integrable fun s => H s * riemannKernelReal (s - Real.log n) :=
      (hH.mul (hΦc.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
        hHc.mul_right
    refine ((h1.add h2).const_mul (c n)).congr (Eventually.of_forall fun s => ?_)
    simp only [hF, Pi.add_apply]; ring
  -- each summand is an integral
  have hterm : ∀ n : ℕ, c n * (crossCorr riemannKernelReal H (Real.log n) +
      crossCorr riemannKernelReal H (-Real.log n)) = ∫ s, F n s := by
    intro n
    have e1 : crossCorr riemannKernelReal H (Real.log n) =
        ∫ s, H s * riemannKernelReal (s + Real.log n) := by
      unfold crossCorr
      rw [← integral_add_right_eq_self (μ := volume)
        (fun t => riemannKernelReal t * H (t - Real.log n)) (Real.log n)]
      refine integral_congr_ae (Eventually.of_forall fun s => ?_)
      simp only; rw [show s + Real.log n - Real.log n = s by ring, mul_comm]
    have e2 : crossCorr riemannKernelReal H (-Real.log n) =
        ∫ s, H s * riemannKernelReal (s - Real.log n) := by
      unfold crossCorr
      rw [← integral_sub_right_eq_self (μ := volume)
        (fun t => riemannKernelReal t * H (t - -Real.log n)) (Real.log n)]
      refine integral_congr_ae (Eventually.of_forall fun s => ?_)
      simp only; rw [show s - Real.log n - -Real.log n = s by ring, mul_comm]
    have i1 : Integrable fun s => H s * riemannKernelReal (s + Real.log n) :=
      (hH.mul (hΦc.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
        hHc.mul_right
    have i2 : Integrable fun s => H s * riemannKernelReal (s - Real.log n) :=
      (hH.mul (hΦc.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
        hHc.mul_right
    rw [e1, e2, ← integral_add i1 i2, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only [hF]; ring
  -- norms of the summands are summable
  have hnorm : ∀ n : ℕ, ∫ s, ‖F n s‖ ≤ (2 * R) * (M * (2 * (C * Real.exp (4 * R)) * (|w n| / (n : ℝ) ^ 2))) := by
    intro n
    have hsupp : ∀ s ∉ Icc (-R) R, ‖F n s‖ = 0 := by
      intro s hs
      have : R < |s| := by
        rw [mem_Icc, not_and_or, not_le, not_le] at hs
        rcases hs with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; exact h
      simp only [hF, hR s this, zero_mul, mul_zero, norm_zero]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp]
    have hb : ∀ s ∈ Icc (-R) R, ‖‖F n s‖‖ ≤ M * (2 * (C * Real.exp (4 * R)) * (|w n| / (n : ℝ) ^ 2)) := by
      intro s hs
      have hs' : |s| ≤ R := abs_le.mpr ⟨hs.1, hs.2⟩
      rw [norm_norm, Real.norm_eq_abs]
      simp only [hF]
      rw [show c n * (H s * (riemannKernelReal (s + Real.log n) + riemannKernelReal (s - Real.log n))) =
        H s * (c n * (riemannKernelReal (s + Real.log n) + riemannKernelReal (s - Real.log n))) by ring,
        abs_mul]
      exact mul_le_mul (hM s) (abs_weightTerm_le hC hC0 hs' n) (abs_nonneg _) hM0
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (-R) R)
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top) hb
    rw [Real.volume_real_Icc_of_le (by linarith), Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)] at h
    calc _ ≤ M * (2 * (C * Real.exp (4 * R)) * (|w n| / (n : ℝ) ^ 2)) * (R - -R) := h
      _ = _ := by ring
  have hsumnorm : Summable fun n : ℕ => ∫ s, ‖F n s‖ :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) hnorm
      ((hw2.mul_left (2 * (C * Real.exp (4 * R)))).mul_left M |>.mul_left (2 * R))
  unfold atomPairing
  rw [tsum_congr hterm, integral_tsum_of_summable_integral_norm hFi hsumnorm]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  simp only [hF, weightKernelTransform]
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  ring

/-- **Truncation limit.** `|T_w(Φχ_L, H) − T_w(Φ, H)| ≤ K e^{−2(L−1)}`. -/
theorem exists_abs_atomPairing_truncated_sub_le {w : ℕ → ℝ}
    (hw2 : Summable fun n : ℕ => |w n| / (n : ℝ) ^ 2) {H : ℝ → ℝ} (hH : Continuous H)
    (hHc : HasCompactSupport H) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ L : ℝ,
      |atomPairing w (crossCorr (truncatedRiemannKernelReal L) H) -
        atomPairing w (crossCorr riemannKernelReal H)| ≤ K * Real.exp (-(2 * (L - 1))) := by
  obtain ⟨C, hC0, hC⟩ := exists_riemannKernelReal_le
  obtain ⟨R, hR0, hR⟩ := exists_vanish_of_hasCompactSupport hHc
  obtain ⟨M, hM⟩ : ∃ M, ∀ t, |H t| ≤ M := by
    obtain ⟨M, hM⟩ := hH.bounded_above_of_compact_support hHc
    exact ⟨M, fun t => by rw [← Real.norm_eq_abs]; exact hM t⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set Sw := ∑' n : ℕ, |w n| / (n : ℝ) ^ 2 with hSw
  have hSw0 : 0 ≤ Sw := tsum_nonneg fun _ => by positivity
  refine ⟨2 * (M * C * (2 * R) * Real.exp (2 * R)) * Sw, by positivity, fun L => ?_⟩
  -- decay of the full correlation
  have hΦdecay : ∀ y, |crossCorr riemannKernelReal H y| ≤
      M * C * (2 * R) * Real.exp (2 * R) * Real.exp (-(2 * |y|)) := by
    intro y
    refine abs_integral_mul_translate_le hC0 hM0 hR0 (fun t => ?_) hM hR y
    rw [abs_of_pos (riemannKernelReal_pos t)]
    refine (hC t).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC0)
    nlinarith [abs_nonneg t]
  -- the defect correlation
  set D : ℝ → ℝ := fun y => crossCorr (truncatedRiemannKernelReal L) H y -
    crossCorr riemannKernelReal H y with hDdef
  have hDeq : ∀ y, D y = ∫ t, (truncatedRiemannKernelReal L t - riemannKernelReal t) * H (t - y) := by
    intro y
    simp only [hDdef, crossCorr]
    rw [← integral_sub (integrable_mul_translate_right (continuous_truncatedRiemannKernelReal L) hH hHc y)
      (integrable_mul_translate_right continuous_riemannKernelReal hH hHc y)]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only; ring
  have hDdecay : ∀ y, |D y| ≤
      M * (C * Real.exp (-(2 * (L - 1)))) * (2 * R) * Real.exp (2 * R) * Real.exp (-(2 * |y|)) := by
    intro y
    rw [hDeq]
    refine abs_integral_mul_translate_le (by positivity) hM0 hR0 (fun t => ?_) hM hR y
    obtain ⟨h1, h2⟩ := riemannKernelReal_sub_truncated_le hC L t
    rw [abs_sub_comm, abs_of_nonneg h1]
    exact h2
  obtain ⟨hsD, hD⟩ := summable_atomPairing_of_decay hw2 hDdecay
  obtain ⟨hsΦ, -⟩ := summable_atomPairing_of_decay hw2 hΦdecay
  have hU : ∀ t, |L| < |t| → truncatedRiemannKernelReal L t = 0 := fun t ht =>
    truncatedRiemannKernelReal_eq_zero (lt_of_le_of_lt (le_abs_self L) ht)
  have hsU := summable_atomPairing w (g := crossCorr (truncatedRiemannKernelReal L) H)
    (R := |L| + R) fun y hy => crossCorr_eq_zero hU hR hy
  have hsub : atomPairing w (crossCorr (truncatedRiemannKernelReal L) H) -
      atomPairing w (crossCorr riemannKernelReal H) = atomPairing w D := by
    unfold atomPairing
    rw [← hsU.tsum_sub hsΦ]
    refine tsum_congr fun n => ?_
    simp only [hDdef]; ring
  rw [hsub]
  calc |atomPairing w D| ≤ 2 * (M * (C * Real.exp (-(2 * (L - 1)))) * (2 * R) * Real.exp (2 * R)) * Sw := hD
    _ = _ := by ring

/-- **Injectivity of the Riemann-kernel transform on the atoms `n ≥ 2`.** If `Σ |w(n)| n^{−2} < ∞`
and `G_w ≡ 0`, then `w(n) = 0` for all `n ≥ 2`. -/
theorem eq_zero_of_weightKernelTransform_eq_zero {w : ℕ → ℝ}
    (hw2 : Summable fun n : ℕ => |w n| / (n : ℝ) ^ 2)
    (hG : ∀ y, weightKernelTransform w y = 0) :
    ∀ n, 2 ≤ n → w n = 0 := by
  set w' : ℕ → ℝ := fun n => if 2 ≤ n then w n else 0 with hw'
  have hsum' : Summable fun n : ℕ => |w' (n + 1)| / ((n : ℝ) + 1) ^ (2 : ℝ) := by
    have h := (summable_nat_add_iff 1).mpr hw2
    refine Summable.of_nonneg_of_le (fun _ => by positivity) (fun n => ?_) h
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    simp only [hw']
    push_cast
    split_ifs
    · exact le_rfl
    · rw [abs_zero, zero_div]; positivity
  have hG' : ∀ y : ℝ, ∑' n : ℕ, w' (n + 1) / Real.sqrt ((n + 1 : ℕ) : ℝ) *
      (riemannKernelReal (y - Real.log ((n + 1 : ℕ) : ℝ)) +
        riemannKernelReal (y + Real.log ((n + 1 : ℕ) : ℝ))) = 0 := by
    intro y
    have h := hG y
    simp only [weightKernelTransform] at h
    rw [(summable_weightTerm hw2 y).tsum_eq_zero_add] at h
    simp only [show ¬ (2 ≤ 0) by omega, if_false, zero_mul, zero_add] at h
    rw [← h]
    refine tsum_congr fun n => ?_
    simp only [hw']
    split_ifs <;> ring
  have hzero := eq_zero_of_riemannKernelTransform_eq_zero_of_sq hsum' hG'
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have := hzero m
  simp only [hw', if_pos hn] at this
  exact this

/-- **Vanishing of the pairing with Φ forces `w = 0`.** If `T_w(Φ, H) = 0` for every `C²` compactly
supported `H`, then the Riemann-kernel transform of `w` vanishes, and `w(n) = 0` for all `n ≥ 2`. -/
theorem eq_zero_of_forall_atomPairing_riemannKernel_eq_zero {w : ℕ → ℝ}
    (hw2 : Summable fun n : ℕ => |w n| / (n : ℝ) ^ 2)
    (hstep1 : ∀ H : ℝ → ℝ, ContDiff ℝ 2 H → HasCompactSupport H →
      atomPairing w (crossCorr riemannKernelReal H) = 0) :
    ∀ n, 2 ≤ n → w n = 0 := by
  -- `G_w = 0`
  have hGc := continuous_weightKernelTransform hw2
  have hG : weightKernelTransform w = fun _ => 0 := by
    have hae : ∀ᵐ x ∂(volume : Measure ℝ), weightKernelTransform w x = 0 := by
      refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hGc.locallyIntegrable fun g hg hgc => ?_
      have h := hstep1 g (hg.of_le (WithTop.coe_le_coe.mpr le_top)) hgc
      rw [atomPairing_riemannKernel_eq_integral hw2 hg.continuous hgc] at h
      simpa [smul_eq_mul] using h
    exact (hGc.ae_eq_iff_eq volume continuous_const).mp hae
  exact eq_zero_of_weightKernelTransform_eq_zero hw2 (congrFun hG)

/-- **`Λ` is an extreme point of the full Weil cone.** Let `w` be real weights with
`Σ |w(n)| n^{−2} < ∞`. If `Λ + w` and `Λ − w` are both Weil-positive with the pole term, then
`w(n) = 0` for all `n ≥ 2`. Unconditional. (Weil positivity itself gives the summability:
`RHTower.weilFullCone_extreme_at_vonMangoldt`.) -/
theorem eq_zero_of_weilPositiveFull_add_of_sub {w : ℕ → ℝ}
    (hw2 : Summable fun n : ℕ => |w n| / (n : ℝ) ^ 2)
    (hp : WeilPositiveFull fun n => (ArithmeticFunction.vonMangoldt n : ℝ) + w n)
    (hm : WeilPositiveFull fun n => (ArithmeticFunction.vonMangoldt n : ℝ) - w n) :
    ∀ n, 2 ≤ n → w n = 0 := by
  -- Step 1: the pairing with `Φ` vanishes against every smooth compactly supported test
  have hstep1 : ∀ H : ℝ → ℝ, ContDiff ℝ 2 H → HasCompactSupport H →
      atomPairing w (crossCorr riemannKernelReal H) = 0 := by
    intro H hH2 hHc
    set T := atomPairing w (crossCorr riemannKernelReal H) with hT
    by_contra hT0
    set τ := |T| with hτ
    have hτ0 : 0 < τ := abs_pos.mpr hT0
    set T2 := atomPairing w (crossCorr H H)
    set EH := testEnergy H
    have hS0 := zetaInvSqSum_nonneg
    set M₂ := (5 / 4) * zetaInvSqSum * (2 * EH ^ 2) + |T2| with hM₂
    have hM₂0 : 0 ≤ M₂ := by positivity
    set ε := τ / (2 * M₂ + 2) with hε
    have hεpos : 0 < ε := by positivity
    obtain ⟨K, hK0, hK⟩ := exists_abs_atomPairing_truncated_sub_le hw2 hH2.continuous hHc
    obtain ⟨L₁, hL₁⟩ := exists_nearRadicalEnergy_le (ε := ε * τ / 12) (by positivity)
    set L := max L₁ (1 + 2 * K / τ) with hL
    have hEL := hL₁ L (le_max_left _ _)
    have hLK : K * Real.exp (-(2 * (L - 1))) ≤ τ / 4 := by
      have h1 : 4 * K / τ ≤ Real.exp (2 * (L - 1)) := by
        have := Real.add_one_le_exp (2 * (L - 1))
        have hL2 : 1 + 2 * K / τ ≤ L := le_max_right _ _
        have : 4 * K / τ = 2 * (2 * K / τ) := by ring
        linarith
      have hE : Real.exp (-(2 * (L - 1))) * Real.exp (2 * (L - 1)) = 1 := by
        rw [← Real.exp_add]; simp
      rw [div_le_iff₀ hτ0] at h1
      have hEpos := Real.exp_pos (-(2 * (L - 1)))
      nlinarith
    have hineq := two_mul_abs_atomPairing_le hp hm hH2 hHc L hεpos
    set EL := truncatedRiemannTailEnergy L
    set T1 := atomPairing w (crossCorr (truncatedRiemannKernelReal L) H)
    have hsq : (EL + ε * EH) ^ 2 ≤ 2 * EL ^ 2 + 2 * (ε ^ 2 * EH ^ 2) := by
      nlinarith [sq_nonneg (EL - ε * EH)]
    have hT1 : 2 * ε * |T1| ≤ ε * τ / 4 + ε ^ 2 * M₂ := by
      have : (5 / 4) * zetaInvSqSum * (EL + ε * EH) ^ 2 ≤
          2 * ((5 / 4) * zetaInvSqSum * EL ^ 2) + ε ^ 2 * ((5 / 4) * zetaInvSqSum * (2 * EH ^ 2)) := by
        have h := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ (5 / 4) * zetaInvSqSum)
        linarith
      rw [hM₂]
      nlinarith [abs_nonneg T2]
    have hT1' : |T1| ≤ τ / 8 + ε * M₂ / 2 := by
      have h := hT1
      have : 2 * ε * |T1| ≤ 2 * ε * (τ / 8 + ε * M₂ / 2) := by nlinarith
      exact le_of_mul_le_mul_left this (by positivity)
    have hεM : ε * M₂ ≤ τ / 2 := by
      rw [hε, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    have hdiff : |T1 - T| ≤ τ / 4 := (hK L).trans hLK
    have htri : |T| - |T1| ≤ |T - T1| := abs_sub_abs_le_abs_sub T T1
    rw [abs_sub_comm] at htri
    linarith
  exact eq_zero_of_forall_atomPairing_riemannKernel_eq_zero hw2 hstep1

end

end RHTower
