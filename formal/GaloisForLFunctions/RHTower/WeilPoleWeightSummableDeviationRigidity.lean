import GaloisForLFunctions.RHTower.WeilPoleWeightAboveOneVonMangoldt

/-!
# Pole weights other than one fail near `Λ`

Let `F₀` be the strip test with transform `Ξ` (`xiShiftedGammaTest 0`).  For `σ ∈ ℝ` and `b ∈ ℝ`
put `G_{σ,b}(u) = F₀(u − b) + σ F₀(u + b)` (`xiTranslatePair`).

* Its transform is `(e^{ibz} + σ e^{−ibz}) Ξ(z)`, so it vanishes at every zero of `ζ`
  (`paperFT_xiTranslatePair_gammaOf`).
* For `|σ| ≤ 1` its `L²` mass is at most `4 ∫ F₀²`, uniformly in `b`
  (`integral_xiTranslatePair_sq_le`).
* Its exponential moments are `∫ G e^{cu} = (e^{cb} + σ e^{−cb}) ∫ F₀ e^{cu}`
  (`integral_xiTranslatePair_mul_exp`).  So the pole term is `½(e^{b/2} + e^{−b/2})²` for
  `σ = 1` and `−½(e^{b/2} − e^{−b/2})²` for `σ = −1`: it is unbounded in both signs while the
  mass stays bounded.

**Theorem** (`not_forall_re_weilPoleWeightFunctional_nonneg_of_summable_deviation`).  Let `β ≠ 1`
and let `lam` deviate summably from `Λ`: `Σ_n |lam(n) − Λ(n)|/√n < ∞`.  Then the Weil functional
with pole weight `β` and weights `lam` is negative on the autocorrelation of some real `C²`
compactly supported test.

Proof.  For a test `G` of the decay class whose transform vanishes at the zeros of `ζ`, the
functional on the truncations `G_L` is the zeta side (which tends to `0`), minus the prime pairing
of the deviation, plus `(β − 1)` times the pole term (`re_weilPoleWeightFunctional_ofReal`).
Because `|k_{G_L}(y)| ≤ ∫ G_L² ≤ ∫ G²` (`abs_crossCorr_self_le`), the deviation pairing is at
most `2 M ∫ G²`, `M = Σ |lam(n) − Λ(n)|/√n` (`abs_atomPairing_le_of_summable`).  Positivity therefore gives
`(β − 1)·pole(G) + 2M ∫ G² ≥ 0` (`pole_add_deviation_nonneg`).  For `G = G_{σ,b}` the second term
is at most `8 M ∫ F₀²` for every `b`, and the choice `σ = −1` (if `β > 1`) or `σ = 1` (if `β < 1`)
makes the first term tend to `−∞` as `b → ∞`.

So inside the ball `Σ |lam − Λ|/√n < ∞` around `Λ` only the pole weight `β = 1` can be
Weil-positive.  On `Ξ`-divisible tests the pole term is a point evaluation of the transform at
`±i/2`, unbounded relative to the `L²` mass and hence relative to every prime node.
-/

open Complex MeasureTheory Filter Topology Set
open Zeta23

noncomputable section

namespace RHTower.WeilPoleWeight

open WeilSpectral

/-! ### Correlation and atom-pairing bounds -/

/-- A real autocorrelation is bounded by its value at the origin: `|k_G(y)| ≤ ∫ G²`. -/
theorem abs_mul_le_half_sq_add (a c : ℝ) : |a * c| ≤ (a ^ 2 + c ^ 2) / 2 := by
  have h := two_mul_le_add_sq |a| |c|
  rw [sq_abs, sq_abs] at h
  rw [abs_mul]
  linarith

theorem hasCompactSupport_sq {G : ℝ → ℝ} (hGc : HasCompactSupport G) :
    HasCompactSupport fun t => G t ^ 2 := by
  have h := hGc.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num)
  simpa only [Function.comp_def] using h

theorem integrable_sq_of_hasCompactSupport {G : ℝ → ℝ} (hG : Continuous G)
    (hGc : HasCompactSupport G) : Integrable fun t => G t ^ 2 :=
  (hG.pow 2).integrable_of_hasCompactSupport (hasCompactSupport_sq hGc)

theorem abs_crossCorr_self_le {G : ℝ → ℝ} (hG : Continuous G) (hGc : HasCompactSupport G)
    (y : ℝ) : |crossCorr G G y| ≤ ∫ t, G t ^ 2 := by
  have hsq : Integrable fun t => G t ^ 2 := integrable_sq_of_hasCompactSupport hG hGc
  have hsq' : Integrable fun t => G (t - y) ^ 2 := hsq.comp_sub_right y
  have hprod : Integrable fun t => G t * G (t - y) := integrable_translate_prod hG hGc hG y
  have hshift : ∫ t, G (t - y) ^ 2 = ∫ t, G t ^ 2 :=
    integral_sub_right_eq_self (fun t => G t ^ 2) y
  have hmid : ∫ t, |G t * G (t - y)| ≤ ∫ t, (G t ^ 2 + G (t - y) ^ 2) / 2 :=
    integral_mono hprod.abs ((hsq.add hsq').div_const 2) fun t =>
      abs_mul_le_half_sq_add (G t) (G (t - y))
  have hval : ∫ t, (G t ^ 2 + G (t - y) ^ 2) / 2 = ∫ t, G t ^ 2 := by
    rw [integral_div, integral_add hsq hsq', hshift]; ring
  unfold crossCorr
  exact (abs_integral_le_integral_abs).trans (hmid.trans hval.le)

/-- The atom pairing of a summable weight against a bounded function. -/
theorem abs_atomPairing_le_of_summable {w : ℕ → ℝ} (hw : Summable fun n : ℕ => |w n| / Real.sqrt n)
    {g : ℝ → ℝ} {S : ℝ} (hg : ∀ y, |g y| ≤ S) :
    |atomPairing w g| ≤ 2 * S * ∑' n : ℕ, |w n| / Real.sqrt n := by
  have hS : 0 ≤ S := (abs_nonneg _).trans (hg 0)
  unfold atomPairing
  rw [← tsum_mul_left, ← Real.norm_eq_abs]
  refine tsum_of_norm_bounded (hw.mul_left (2 * S)).hasSum fun n => ?_
  rw [Real.norm_eq_abs]
  split_ifs with hn
  · have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
    have h2 : |g (Real.log n) + g (-Real.log n)| ≤ 2 * S :=
      (abs_add_le _ _).trans (by linarith [hg (Real.log n), hg (-Real.log n)])
    rw [abs_mul, abs_div, abs_of_pos hsq]
    calc |w n| / Real.sqrt n * |g (Real.log n) + g (-Real.log n)|
        ≤ |w n| / Real.sqrt n * (2 * S) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = 2 * S * (|w n| / Real.sqrt n) := by ring
  · rw [zero_mul, abs_zero]; positivity

/-! ### Decay-class bookkeeping -/

theorem decayBound_comp_sub {F : ℝ → ℝ} {δ C : ℝ} (hδ : 0 ≤ δ) (hF : DecayBound F δ C) (b : ℝ) :
    DecayBound (fun u => F (u - b)) δ (C * Real.exp ((1 / 2 + δ) * |b|)) := by
  refine ⟨hF.1.comp (contDiff_id.sub contDiff_const), mul_nonneg hF.2.1 (Real.exp_pos _).le,
    fun x => ?_⟩
  have hk : 0 ≤ 1 / 2 + δ := by linarith
  have hex : Real.exp (-((1 / 2 + δ) * |x - b|)) ≤
      Real.exp ((1 / 2 + δ) * |b|) * Real.exp (-((1 / 2 + δ) * |x|)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_le_mul_of_nonneg_left (abs_sub_abs_le_abs_sub x b) hk]
  obtain ⟨h1, h2⟩ := hF.2.2 (x - b)
  have hC := hF.2.1
  refine ⟨?_, ?_⟩
  · calc |F (x - b)| ≤ C * Real.exp (-((1 / 2 + δ) * |x - b|)) := h1
      _ ≤ C * (Real.exp ((1 / 2 + δ) * |b|) * Real.exp (-((1 / 2 + δ) * |x|))) :=
          mul_le_mul_of_nonneg_left hex hC
      _ = _ := by ring
  · rw [deriv_comp_sub_const]
    calc |deriv F (x - b)| ≤ C * Real.exp (-((1 / 2 + δ) * |x - b|)) := h2
      _ ≤ C * (Real.exp ((1 / 2 + δ) * |b|) * Real.exp (-((1 / 2 + δ) * |x|))) :=
          mul_le_mul_of_nonneg_left hex hC
      _ = _ := by ring

theorem decayBound_add_mul {F G : ℝ → ℝ} {δ C D : ℝ} (hF : DecayBound F δ C)
    (hG : DecayBound G δ D) {σ : ℝ} (hσ : |σ| ≤ 1) :
    DecayBound (fun u => F u + σ * G u) δ (C + D) := by
  refine ⟨hF.1.add (contDiff_const.mul hG.1), add_nonneg hF.2.1 hG.2.1, fun x => ?_⟩
  have hdF : DifferentiableAt ℝ F x := (hF.1.differentiable (by norm_num)).differentiableAt
  have hdG : DifferentiableAt ℝ G x := (hG.1.differentiable (by norm_num)).differentiableAt
  have hd : deriv (fun u => F u + σ * G u) x = deriv F x + σ * deriv G x :=
    (hdF.hasDerivAt.add (hdG.hasDerivAt.const_mul σ)).deriv
  have key : ∀ a c E : ℝ, 0 ≤ E → |a| ≤ C * E → |c| ≤ D * E → |a + σ * c| ≤ (C + D) * E := by
    intro a c E hE ha hc
    have hσc : |σ * c| ≤ D * E := by
      rw [abs_mul]
      calc |σ| * |c| ≤ 1 * |c| := mul_le_mul_of_nonneg_right hσ (abs_nonneg _)
        _ ≤ D * E := by rw [one_mul]; exact hc
    calc |a + σ * c| ≤ |a| + |σ * c| := abs_add_le _ _
      _ ≤ C * E + D * E := add_le_add ha hσc
      _ = (C + D) * E := by ring
  obtain ⟨f1, f2⟩ := hF.2.2 x
  obtain ⟨g1, g2⟩ := hG.2.2 x
  exact ⟨key _ _ _ (Real.exp_pos _).le f1 g1, by rw [hd]; exact key _ _ _ (Real.exp_pos _).le f2 g2⟩

theorem integrable_mul_exp_of_decayBound {F : ℝ → ℝ} {δ C : ℝ} (hδ : 0 < δ)
    (hF : DecayBound F δ C) {c : ℝ} (hc : |c| ≤ 1 / 2) :
    Integrable fun u => F u * Real.exp (c * u) := by
  refine ((integrable_exp_neg_mul_abs_fam hδ).const_mul C).mono'
    ((hF.1.continuous).mul (by fun_prop)).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs]
  exact abs_mul_exp_le_of_decayBound hF hc u

theorem integrable_sq_of_decayBound {F : ℝ → ℝ} {δ C : ℝ} (hδ : 0 ≤ δ) (hF : DecayBound F δ C) :
    Integrable fun u => F u ^ 2 := by
  have hk : (0 : ℝ) < 2 * (1 / 2 + δ) := by linarith
  refine ((integrable_exp_neg_mul_abs_fam hk).const_mul (C ^ 2)).mono'
    ((hF.1.continuous).pow 2).aestronglyMeasurable (Eventually.of_forall fun u => ?_)
  have h1 := (hF.2.2 u).1
  rw [Real.norm_eq_abs, abs_pow]
  have hC := hF.2.1
  calc |F u| ^ 2 ≤ (C * Real.exp (-((1 / 2 + δ) * |u|))) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h1 2
    _ = C ^ 2 * Real.exp (-(2 * (1 / 2 + δ) * |u|)) := by
        rw [mul_pow, ← Real.exp_nat_mul]; congr 2; push_cast; ring

theorem integrable_ofReal_mul_cexp_of_decayBound {F : ℝ → ℝ} {δ C : ℝ} (hδ : 0 < δ)
    (hF : DecayBound F δ C) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    Integrable fun u : ℝ => (F u : ℂ) * Complex.exp (I * z * u) := by
  refine ((integrable_exp_neg_mul_abs_fam hδ).const_mul C).mono'
    (((Complex.continuous_ofReal.comp hF.1.continuous).mul (by fun_prop)).aestronglyMeasurable)
    (Eventually.of_forall fun u => ?_)
  have hre : (I * z * (u : ℂ)).re = -(z.im * u) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [norm_mul, Complex.norm_exp, hre, Complex.norm_real, Real.norm_eq_abs]
  have h1 := (hF.2.2 u).1
  have h2 : -(z.im * u) ≤ |u| / 2 := by
    have := neg_abs_le (z.im * u)
    calc -(z.im * u) ≤ |z.im * u| := by linarith [le_abs_self (-(z.im * u)), abs_neg (z.im * u)]
      _ = |z.im| * |u| := abs_mul _ _
      _ ≤ 1 / 2 * |u| := mul_le_mul_of_nonneg_right hz (abs_nonneg _)
      _ = |u| / 2 := by ring
  calc |F u| * Real.exp (-(z.im * u)) ≤ C * Real.exp (-((1 / 2 + δ) * |u|)) * Real.exp (|u| / 2) :=
        mul_le_mul h1 (Real.exp_le_exp.mpr h2) (Real.exp_pos _).le
          (le_trans (abs_nonneg _) h1)
    _ = C * Real.exp (-(δ * |u|)) := by
        rw [mul_assoc, ← Real.exp_add]; congr 2; ring

/-! ### Translates -/

theorem paperFT_ofReal_comp_sub (F : ℝ → ℝ) (b : ℝ) (z : ℂ) :
    paperFT (fun u => (F (u - b) : ℂ)) z = Complex.exp (I * z * b) * paperFT (fun u => (F u : ℂ)) z := by
  rw [paperFT_def, paperFT_def]
  have := integral_sub_right_eq_self (μ := volume)
    (fun v : ℝ => (F v : ℂ) * Complex.exp (I * z * ((v + b : ℝ) : ℂ))) b
  simp only [sub_add_cancel] at this
  rw [this, ← integral_const_mul]
  congr 1; funext v
  push_cast
  rw [mul_add, Complex.exp_add]; ring

theorem integral_comp_sub_mul_exp (F : ℝ → ℝ) (b c : ℝ) :
    ∫ u, F (u - b) * Real.exp (c * u) = Real.exp (c * b) * ∫ u, F u * Real.exp (c * u) := by
  have h := integral_sub_right_eq_self (μ := volume) (fun v : ℝ => F v * Real.exp (c * (v + b))) b
  simp only [sub_add_cancel] at h
  rw [h, ← integral_const_mul]
  congr 1; funext v
  rw [mul_add, Real.exp_add]; ring

/-! ### Translate pairs of the `Ξ`-test -/

/-- `G_{σ,b}(u) = F₀(u − b) + σ F₀(u + b)`, with `F₀` the strip test of `Ξ`. -/
def xiTranslatePair (σ b u : ℝ) : ℝ :=
  xiShiftedGammaTest 0 (u - b) + σ * xiShiftedGammaTest 0 (u - -b)

theorem exists_decayBound_xiTest : ∃ C : ℝ, DecayBound (xiShiftedGammaTest 0) (1 / 4) C := by
  obtain ⟨C, -, hC⟩ := exists_decayBound_xiShiftedGammaTest
  exact ⟨_, hC 0⟩

theorem exists_decayBound_xiTranslatePair {σ : ℝ} (hσ : |σ| ≤ 1) (b : ℝ) :
    ∃ C : ℝ, DecayBound (xiTranslatePair σ b) (1 / 4) C := by
  obtain ⟨C, hC⟩ := exists_decayBound_xiTest
  exact ⟨_, decayBound_add_mul (decayBound_comp_sub (by norm_num) hC b)
    (decayBound_comp_sub (by norm_num) hC (-b)) hσ⟩

theorem paperFT_xiTranslatePair_gammaOf (σ b : ℝ) (ρ : zetaZeroConfig.carrier) :
    paperFT (fun u => (xiTranslatePair σ b u : ℂ)) (gammaOf ρ) = 0 := by
  obtain ⟨C, hC⟩ := exists_decayBound_xiTest
  have hmem : IsNontrivialZero (ρ : ℂ) := ρ.2
  have hIm : |(gammaOf (ρ : ℂ)).im| < 1 / 2 := WeilEF.abs_gammaOf_im_lt ⟨hmem.2.1, hmem.2.2⟩
  have hδ : (0 : ℝ) < 1 / 4 := by norm_num
  have i1 := integrable_ofReal_mul_cexp_of_decayBound hδ
    (decayBound_comp_sub (by norm_num) hC b) hIm.le
  have i2 := integrable_ofReal_mul_cexp_of_decayBound hδ
    (decayBound_comp_sub (by norm_num) hC (-b)) hIm.le
  have hsplit : paperFT (fun u => (xiTranslatePair σ b u : ℂ)) (gammaOf ρ) =
      paperFT (fun u => (xiShiftedGammaTest 0 (u - b) : ℂ)) (gammaOf ρ) +
        (σ : ℂ) * paperFT (fun u => (xiShiftedGammaTest 0 (u - -b) : ℂ)) (gammaOf ρ) := by
    rw [paperFT_def, paperFT_def, paperFT_def, ← integral_const_mul, ← integral_add i1
      (i2.const_mul (σ : ℂ))]
    congr 1; funext u
    unfold xiTranslatePair
    push_cast; ring
  rw [hsplit, paperFT_ofReal_comp_sub, paperFT_ofReal_comp_sub,
    paperFT_xiShiftedGammaTest_gammaOf 0 ρ]
  ring

theorem integral_xiTranslatePair_mul_exp (σ b : ℝ) {c : ℝ} (hc : |c| ≤ 1 / 2) :
    ∫ u, xiTranslatePair σ b u * Real.exp (c * u) =
      (Real.exp (c * b) + σ * Real.exp (c * -b)) * ∫ u, xiShiftedGammaTest 0 u * Real.exp (c * u) := by
  obtain ⟨C, hC⟩ := exists_decayBound_xiTest
  have hδ : (0 : ℝ) < 1 / 4 := by norm_num
  have i1 := integrable_mul_exp_of_decayBound hδ (decayBound_comp_sub (by norm_num) hC b) hc
  have i2 := integrable_mul_exp_of_decayBound hδ (decayBound_comp_sub (by norm_num) hC (-b)) hc
  have e : (fun u => xiTranslatePair σ b u * Real.exp (c * u)) =
      fun u => xiShiftedGammaTest 0 (u - b) * Real.exp (c * u) +
        σ * (xiShiftedGammaTest 0 (u - -b) * Real.exp (c * u)) := by
    funext u; unfold xiTranslatePair; ring
  rw [e, integral_add i1 (i2.const_mul σ), integral_const_mul, integral_comp_sub_mul_exp,
    integral_comp_sub_mul_exp]
  ring

theorem integral_xiTranslatePair_sq_le {σ : ℝ} (hσ : |σ| ≤ 1) (b : ℝ) :
    ∫ u, xiTranslatePair σ b u ^ 2 ≤ 4 * ∫ u, xiShiftedGammaTest 0 u ^ 2 := by
  obtain ⟨C, hC⟩ := exists_decayBound_xiTest
  set F₀ := xiShiftedGammaTest 0 with hF₀
  have hsq := integrable_sq_of_decayBound (by norm_num) hC
  have h1 : Integrable fun u => F₀ (u - b) ^ 2 := hsq.comp_sub_right b
  have h2 : Integrable fun u => F₀ (u - -b) ^ 2 := hsq.comp_sub_right (-b)
  have hG := integrable_sq_of_decayBound (by norm_num)
    (decayBound_add_mul (decayBound_comp_sub (by norm_num) hC b)
      (decayBound_comp_sub (by norm_num) hC (-b)) hσ)
  have hσ2 : σ ^ 2 ≤ 1 := by nlinarith [abs_nonneg σ, sq_abs σ]
  calc ∫ u, xiTranslatePair σ b u ^ 2 ≤ ∫ u, (2 * F₀ (u - b) ^ 2 + 2 * F₀ (u - -b) ^ 2) := by
        refine integral_mono hG ((h1.const_mul 2).add (h2.const_mul 2)) fun u => ?_
        show (F₀ (u - b) + σ * F₀ (u - -b)) ^ 2 ≤ _
        nlinarith [sq_nonneg (F₀ (u - b) - σ * F₀ (u - -b)), sq_nonneg (F₀ (u - -b)),
          mul_le_mul_of_nonneg_right hσ2 (sq_nonneg (F₀ (u - -b)))]
    _ = 4 * ∫ u, F₀ u ^ 2 := by
        rw [integral_add (h1.const_mul 2) (h2.const_mul 2), integral_const_mul, integral_const_mul,
          integral_sub_right_eq_self (fun u => F₀ u ^ 2) b,
          integral_sub_right_eq_self (fun u => F₀ u ^ 2) (-b)]
        ring

/-! ### The positivity inequality on a `Ξ`-divisible test -/

/-- **Pole plus deviation is nonnegative.**  If the Weil functional with pole weight `β` and
weights `lam` is nonnegative on every compactly supported autocorrelation, then every test `G`
of the decay class whose transform vanishes at the zeros of `ζ` satisfies
`(β − 1)·pole(G) + 2 (∫ G²) Σ |lam(n) − Λ(n)|/√n ≥ 0`. -/
theorem pole_add_deviation_nonneg {β : ℝ} {lam : ℕ → ℝ}
    (hlam : Summable fun n : ℕ => |lam n - ArithmeticFunction.vonMangoldt n| / Real.sqrt n)
    (hpos : ∀ F : ℝ → ℝ, ContDiff ℝ 2 (fun u => (F u : ℂ)) → HasCompactSupport F →
      0 ≤ (weilPoleWeightFunctional β lam
        (EF.weilTest (fun u => (F u : ℂ)) fun u => (F u : ℂ))).re)
    {G : ℝ → ℝ} {C : ℝ} (hG : DecayBound G (1 / 4) C)
    (hzero : ∀ ρ : zetaZeroConfig.carrier, paperFT (fun u => (G u : ℂ)) (gammaOf ρ) = 0) :
    0 ≤ (β - 1) * (2 * ((∫ u, G u * Real.exp (-u / 2)) * ∫ u, G u * Real.exp (u / 2))) +
      2 * (∫ u, G u ^ 2) *
        ∑' n : ℕ, |lam n - ArithmeticFunction.vonMangoldt n| / Real.sqrt n := by
  set M := ∑' n : ℕ, |lam n - ArithmeticFunction.vonMangoldt n| / Real.sqrt n with hM
  have hM0 : 0 ≤ M := tsum_nonneg fun n => by positivity
  have hsqG := integrable_sq_of_decayBound (by norm_num) hG
  obtain ⟨Λc, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  have hδ : (0 : ℝ) < 1 / 4 := by norm_num
  -- the zeta side of the truncations tends to `0`
  set w : ℕ → ℝ := fun j => if j = 0 then 1 else 0 with hw
  have hw0 : ∀ j, 0 ≤ w j := fun j => by simp only [hw]; split_ifs <;> norm_num
  have hsum : Summable fun j => w j * C ^ 2 :=
    summable_of_ne_finset_zero (s := {0}) fun j hj => by
      simp only [Finset.mem_singleton] at hj; simp [hw, hj]
  have h1 := tendsto_tsum_W_truncTest (F := fun _ => G) (C := fun _ => C) hδ (fun _ => hG) hw0
    hsum hΛ0 hΛ (fun _ ρ => hzero ρ)
  have hsingle : ∀ L : ℝ, (∑' j, w j * (zetaZeroConfig.W (fun u => (truncTest G L u : ℂ))
      (fun u => (truncTest G L u : ℂ))).re) =
      (zetaZeroConfig.W (fun u => (truncTest G L u : ℂ)) (fun u => (truncTest G L u : ℂ))).re := by
    intro L
    rw [tsum_eq_single 0 fun j hj => by simp [hw, hj]]
    simp [hw]
  simp_rw [hsingle] at h1
  -- the pole term of the truncations
  have hneg : ∀ u : ℝ, -u / 2 = (-1 / 2 : ℝ) * u := fun u => by ring
  have hpos2 : ∀ u : ℝ, u / 2 = (1 / 2 : ℝ) * u := fun u => by ring
  have ta := tendsto_integral_truncTest_mul_exp hδ hG (c := -1 / 2) (by norm_num [abs_of_neg])
  have tb := tendsto_integral_truncTest_mul_exp hδ hG (c := 1 / 2) (by norm_num)
  simp_rw [← hneg] at ta
  simp_rw [← hpos2] at tb
  have h3 := ((ta.mul tb).const_mul 2).const_mul (β - 1)
  -- the lower bound on every truncation
  have hlow : ∀ L : ℝ, 0 ≤
      (zetaZeroConfig.W (fun u => (truncTest G L u : ℂ)) (fun u => (truncTest G L u : ℂ))).re +
        (β - 1) * (2 * ((∫ u, truncTest G L u * Real.exp (-u / 2)) *
          ∫ u, truncTest G L u * Real.exp (u / 2))) + 2 * (∫ u, G u ^ 2) * M := by
    intro L
    have hc := (contDiff_truncTest hG.1 L).continuous
    have hcs := hasCompactSupport_truncTest G L
    have hS := hpos _ (contDiff_ofReal_truncTest hG.1 L) hcs
    rw [re_weilPoleWeightFunctional_ofReal β lam (contDiff_ofReal_truncTest hG.1 L) hc hcs] at hS
    have hsqL : Integrable fun u => truncTest G L u ^ 2 :=
      integrable_sq_of_hasCompactSupport hc hcs
    have hmass : ∫ u, truncTest G L u ^ 2 ≤ ∫ u, G u ^ 2 :=
      integral_mono hsqL hsqG fun u => by
        have := abs_truncTest_le G L u
        nlinarith [abs_nonneg (truncTest G L u), sq_abs (truncTest G L u), sq_abs (G u)]
    have hdev := abs_atomPairing_le_of_summable (w := fun n => lam n - ArithmeticFunction.vonMangoldt n)
      hlam (g := crossCorr (truncTest G L) (truncTest G L)) (S := ∫ u, truncTest G L u ^ 2)
      (abs_crossCorr_self_le hc hcs)
    have hdev' : -(2 * (∫ u, G u ^ 2) * M) ≤ atomPairing
        (fun n => lam n - ArithmeticFunction.vonMangoldt n)
        (crossCorr (truncTest G L) (truncTest G L)) := by
      have := neg_abs_le (atomPairing (fun n => lam n - ArithmeticFunction.vonMangoldt n)
        (crossCorr (truncTest G L) (truncTest G L)))
      have hm : 2 * (∫ u, truncTest G L u ^ 2) * M ≤ 2 * (∫ u, G u ^ 2) * M :=
        mul_le_mul_of_nonneg_right (by linarith) hM0
      linarith
    linarith
  have hlim : Tendsto (fun L : ℝ =>
      (zetaZeroConfig.W (fun u => (truncTest G L u : ℂ)) (fun u => (truncTest G L u : ℂ))).re +
        (β - 1) * (2 * ((∫ u, truncTest G L u * Real.exp (-u / 2)) *
          ∫ u, truncTest G L u * Real.exp (u / 2))) + 2 * (∫ u, G u ^ 2) * M) atTop
      (𝓝 (0 + (β - 1) * (2 * ((∫ u, G u * Real.exp (-u / 2)) *
        ∫ u, G u * Real.exp (u / 2))) + 2 * (∫ u, G u ^ 2) * M)) :=
    (h1.add h3).add_const _
  have := ge_of_tendsto hlim (Eventually.of_forall hlow)
  linarith

/-! ### The theorem -/

theorem sub_inv_exp_half_ge {b : ℝ} (hb : 0 ≤ b) :
    b / 2 ≤ Real.exp (b / 2) - Real.exp (-(b / 2)) := by
  have h1 := Real.add_one_le_exp (b / 2)
  have h2 : Real.exp (-(b / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  linarith

/-- **Pole weights other than one fail near `Λ`.**  If `β ≠ 1` and
`Σ_n |lam(n) − Λ(n)|/√n < ∞`, the Weil functional with pole weight `β` and weights `lam` is
negative on the autocorrelation of some real `C²` compactly supported test. -/
theorem not_forall_re_weilPoleWeightFunctional_nonneg_of_summable_deviation {β : ℝ} (hβ : β ≠ 1)
    {lam : ℕ → ℝ}
    (hlam : Summable fun n : ℕ => |lam n - ArithmeticFunction.vonMangoldt n| / Real.sqrt n) :
    ¬ ∀ F : ℝ → ℝ, ContDiff ℝ 2 (fun u => (F u : ℂ)) → HasCompactSupport F →
      0 ≤ (weilPoleWeightFunctional β lam
        (EF.weilTest (fun u => (F u : ℂ)) fun u => (F u : ℂ))).re := by
  intro hpos
  set M := ∑' n : ℕ, |lam n - ArithmeticFunction.vonMangoldt n| / Real.sqrt n with hM
  have hM0 : 0 ≤ M := tsum_nonneg fun n => by positivity
  set E₀ := ∫ u, xiShiftedGammaTest 0 u ^ 2 with hE₀
  have hE0 : 0 ≤ E₀ := integral_nonneg fun u => sq_nonneg _
  set A₀ := ∫ u, xiShiftedGammaTest 0 u * Real.exp (-u / 2) with hA₀
  set B₀ := ∫ u, xiShiftedGammaTest 0 u * Real.exp (u / 2) with hB₀
  have hAB : A₀ * B₀ = 1 / 4 := by have := pole_xiShiftedGammaTest_zero; linarith
  have hneg : ∀ u : ℝ, -u / 2 = (-1 / 2 : ℝ) * u := fun u => by ring
  have hpos2 : ∀ u : ℝ, u / 2 = (1 / 2 : ℝ) * u := fun u => by ring
  -- the inequality for a translate pair
  have key : ∀ σ : ℝ, |σ| ≤ 1 → ∀ b : ℝ,
      0 ≤ (β - 1) * (2 * (((Real.exp (-(b / 2)) + σ * Real.exp (b / 2)) * A₀) *
        ((Real.exp (b / 2) + σ * Real.exp (-(b / 2))) * B₀))) + 2 * (4 * E₀) * M := by
    intro σ hσ b
    obtain ⟨C, hC⟩ := exists_decayBound_xiTranslatePair hσ b
    have h := pole_add_deviation_nonneg hlam hpos hC (paperFT_xiTranslatePair_gammaOf σ b)
    have ea := integral_xiTranslatePair_mul_exp σ b (c := -1 / 2) (by norm_num [abs_of_neg])
    have eb := integral_xiTranslatePair_mul_exp σ b (c := 1 / 2) (by norm_num)
    simp_rw [← hneg] at ea
    simp_rw [← hpos2] at eb
    rw [ea, eb] at h
    have hmass := integral_xiTranslatePair_sq_le hσ b
    have e1 : -b / 2 = -(b / 2) := by ring
    have e2 : - -b / 2 = b / 2 := by ring
    rw [e1, e2] at h
    have hm : 2 * (∫ u, xiTranslatePair σ b u ^ 2) * M ≤ 2 * (4 * E₀) * M :=
      mul_le_mul_of_nonneg_right (by linarith) hM0
    linarith
  rcases lt_or_gt_of_ne hβ with hlt | hgt
  · -- `β < 1`: the even pair
    set K := 16 * E₀ * M / (1 - β) with hK
    have hK0 : 0 ≤ K := div_nonneg (by positivity) (by linarith)
    set b := 2 * (Real.sqrt K + 1) with hb
    have hb0 : 0 ≤ b := by positivity
    have h := key 1 (by norm_num) b
    have hs := sub_inv_exp_half_ge hb0
    have hpe : 0 < Real.exp (-(b / 2)) := Real.exp_pos _
    have hsum : b / 2 ≤ Real.exp (b / 2) + Real.exp (-(b / 2)) := by linarith
    have hsq : K < (b / 2) ^ 2 := by
      have hr := Real.sq_sqrt hK0
      have : b / 2 = Real.sqrt K + 1 := by rw [hb]; ring
      rw [this]; nlinarith [Real.sqrt_nonneg K]
    have hbig : K < (Real.exp (b / 2) + Real.exp (-(b / 2))) ^ 2 :=
      lt_of_lt_of_le hsq (pow_le_pow_left₀ (by positivity) hsum 2)
    have hfac : (Real.exp (-(b / 2)) + 1 * Real.exp (b / 2)) * A₀ *
        ((Real.exp (b / 2) + 1 * Real.exp (-(b / 2))) * B₀) =
        (Real.exp (b / 2) + Real.exp (-(b / 2))) ^ 2 * (A₀ * B₀) := by ring
    rw [hfac, hAB] at h
    have h1β : 0 < 1 - β := by linarith
    have hKe : K * (1 - β) = 16 * E₀ * M := by rw [hK]; field_simp
    nlinarith [mul_lt_mul_of_pos_right hbig h1β]
  · -- `β > 1`: the odd pair
    set K := 16 * E₀ * M / (β - 1) with hK
    have hK0 : 0 ≤ K := div_nonneg (by positivity) (by linarith)
    set b := 2 * (Real.sqrt K + 1) with hb
    have hb0 : 0 ≤ b := by positivity
    have h := key (-1) (by norm_num) b
    have hs := sub_inv_exp_half_ge hb0
    have hsq : K < (b / 2) ^ 2 := by
      have hr := Real.sq_sqrt hK0
      have : b / 2 = Real.sqrt K + 1 := by rw [hb]; ring
      rw [this]; nlinarith [Real.sqrt_nonneg K]
    have hbig : K < (Real.exp (b / 2) - Real.exp (-(b / 2))) ^ 2 :=
      lt_of_lt_of_le hsq (pow_le_pow_left₀ (by positivity) hs 2)
    have hfac : (Real.exp (-(b / 2)) + -1 * Real.exp (b / 2)) * A₀ *
        ((Real.exp (b / 2) + -1 * Real.exp (-(b / 2))) * B₀) =
        -((Real.exp (b / 2) - Real.exp (-(b / 2))) ^ 2 * (A₀ * B₀)) := by ring
    rw [hfac, hAB] at h
    have hβ1 : 0 < β - 1 := by linarith
    have hKe : K * (β - 1) = 16 * E₀ * M := by rw [hK]; field_simp
    nlinarith [mul_lt_mul_of_pos_right hbig hβ1]

end RHTower.WeilPoleWeight
