import GaloisForLFunctions.RHTower.EvenSectorTwistedArcNull

/-!
# Dilation of strip tests and the twisted-arc null ray

For a strip function `Φ` put `Φ_t(z) = t Φ(tz)` (`dil`).  Then `stripTest Φ_t = stripTest Φ (·/t)`
(`stripTest_dil`): dilating a test by `t` dilates its transform by `1/t`, and the autocorrelation
becomes `t (F ⋆ F̃)(·/t)` (`crossCorr_stripTest_dil`).

A *null family* (`NullFamily`) is a sequence of strip functions `Φ_j`, holomorphic with decay
`C_j e^{−ε|Re z|}` on `|Im z| ≤ 5/4`, with weights `w_j ≥ 0`, `Σ_j w_j C_j² < ∞`, every `Φ_j`
vanishing at the spectral point `γ_ρ` of every nontrivial zero of `ζ`, and with a jointly prime-blind
autocorrelation `G₀ = Σ_j w_j F_j ⋆ F̃_j` (`nullRay`), `F_j = stripTest Φ_j`.

`G₀` is the strip test of the density `R = Σ_j w_j Φ_j Φ_j^#` (`nullRay_eq_stripTest`), which is
holomorphic with decay on `|Im z| ≤ 9/8` (`stripDecay_nullDensity`) and nonnegative on the real line
(`nullDensity_ofReal`).  Hence `G₀` is differentiable with `|G₀′(y)| ≤ K e^{−9|y|/8}`
(`hasDerivAt_nullRay`, `exists_abs_deriv_nullRay_le`).
-/

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped ComplexConjugate

noncomputable section

namespace RHTower.NullRayDilation

open WeilOneSided WeilSpectral EvenSector

/-! ## Dilation of strip functions -/

/-- `Φ_t(z) = t Φ(tz)`. -/
def dil (t : ℝ) (Φ : ℂ → ℂ) (z : ℂ) : ℂ := t * Φ (t * z)

theorem dil_one (Φ : ℂ → ℂ) : dil 1 Φ = Φ := by
  funext z; simp [dil]

theorem stripDecay_mono {Φ : ℂ → ℂ} {b b' ε ε' C C' : ℝ} (hΦ : StripDecay Φ b ε C)
    (hb : b' ≤ b) (hb0 : 0 ≤ b') (hε : ε' ≤ ε) (hC : C ≤ C') : StripDecay Φ b' ε' C' := by
  have hC0 := hΦ.const_nonneg (hb0.trans hb)
  refine ⟨fun z hz => hΦ.diff z (hz.trans hb), fun z hz => ?_⟩
  refine (hΦ.bound z (hz.trans hb)).trans ?_
  have : Real.exp (-(ε * |z.re|)) ≤ Real.exp (-(ε' * |z.re|)) :=
    Real.exp_le_exp.mpr (by nlinarith [abs_nonneg z.re])
  exact mul_le_mul hC this (Real.exp_pos _).le (hC0.trans hC)

theorem stripDecay_dil {Φ : ℂ → ℂ} {b ε C t : ℝ} (hΦ : StripDecay Φ b ε C) (ht : 0 < t) :
    StripDecay (dil t Φ) (b / t) (ε * t) (t * C) := by
  have him : ∀ z : ℂ, |z.im| ≤ b / t → |((t : ℂ) * z).im| ≤ b := fun z hz => by
    rw [show ((t : ℂ) * z).im = t * z.im by simp, abs_mul, abs_of_pos ht]
    rw [le_div_iff₀ ht] at hz; linarith
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · unfold dil
    exact ((hΦ.diff _ (him z hz)).comp z (differentiableAt_id.const_mul (t : ℂ))).const_mul _
  · unfold dil
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    have h := hΦ.bound _ (him z hz)
    rw [show ((t : ℂ) * z).re = t * z.re by simp, abs_mul, abs_of_pos ht] at h
    calc t * ‖Φ (t * z)‖ ≤ t * (C * Real.exp (-(ε * (t * |z.re|)))) :=
          mul_le_mul_of_nonneg_left h ht.le
      _ = t * C * Real.exp (-(ε * t * |z.re|)) := by
          rw [show ε * (t * |z.re|) = ε * t * |z.re| by ring]; ring

theorem dil_neg_conj {Φ : ℂ → ℂ} (h : ∀ z, Φ (-z) = conj (Φ (conj z))) (t : ℝ) (z : ℂ) :
    dil t Φ (-z) = conj (dil t Φ (conj z)) := by
  simp only [dil, mul_neg, h, map_mul, Complex.conj_ofReal]

theorem neg_ofReal_of_neg_conj {Φ : ℂ → ℂ} (h : ∀ z, Φ (-z) = conj (Φ (conj z))) (r : ℝ) :
    Φ (-(r : ℂ)) = conj (Φ r) := by
  rw [h, Complex.conj_ofReal]

theorem stripInvFT_dil (Φ : ℂ → ℂ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    stripInvFT (dil t Φ) x = stripInvFT Φ (x / t) := by
  unfold stripInvFT dil
  congr 1
  have h := Measure.integral_comp_mul_left
    (fun r : ℝ => Φ r * cexp (-(I * r * ((x / t : ℝ) : ℂ)))) t
  rw [abs_of_pos (inv_pos.mpr ht)] at h
  have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have e : (fun r : ℝ => (t : ℂ) * Φ ((t : ℂ) * (r : ℂ)) * cexp (-(I * r * x))) =
      fun r : ℝ => (t : ℂ) *
        (Φ ((t * r : ℝ) : ℂ) * cexp (-(I * ((t * r : ℝ) : ℂ) * ((x / t : ℝ) : ℂ)))) := by
    funext r
    have e2 : I * ((t * r : ℝ) : ℂ) * ((x / t : ℝ) : ℂ) = I * r * x := by
      push_cast; field_simp
    rw [e2]; push_cast; ring
  rw [e, integral_const_mul, h, Complex.real_smul, ← mul_assoc, ← ofReal_mul,
    mul_inv_cancel₀ ht.ne', ofReal_one, one_mul]

theorem stripTest_dil (Φ : ℂ → ℂ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    stripTest (dil t Φ) x = stripTest Φ (x / t) := by
  simp only [stripTest, stripInvFT_dil Φ ht]

/-- The autocorrelation of `F(·/t)` is `t (F ⋆ F̃)(·/t)`. -/
theorem crossCorr_comp_div (F : ℝ → ℝ) {t : ℝ} (ht : 0 < t) (y : ℝ) :
    crossCorr (fun x => F (x / t)) (fun x => F (x / t)) y = t * crossCorr F F (y / t) := by
  unfold crossCorr
  have h := Measure.integral_comp_div (fun s : ℝ => F s * F (s - y / t)) t
  rw [abs_of_pos ht, smul_eq_mul] at h
  rw [← h]
  congr 1; funext x
  show F (x / t) * F ((x - y) / t) = _
  rw [sub_div]

theorem crossCorr_stripTest_dil (Φ : ℂ → ℂ) {t : ℝ} (ht : 0 < t) (y : ℝ) :
    crossCorr (stripTest (dil t Φ)) (stripTest (dil t Φ)) y =
      t * crossCorr (stripTest Φ) (stripTest Φ) (y / t) := by
  have e : stripTest (dil t Φ) = fun x => stripTest Φ (x / t) := funext (stripTest_dil Φ ht)
  rw [e, crossCorr_comp_div _ ht]

/-- The transform of the dilated strip test inside the strip. -/
theorem paperFT_stripTest_dil {Φ : ℂ → ℂ} {b ε C : ℝ} (hb : 0 < b) (hε : 0 < ε)
    (hΦ : StripDecay Φ b ε C) (h : ∀ z, Φ (-z) = conj (Φ (conj z))) {t : ℝ} (ht : 0 < t) {z : ℂ}
    (hz : |z.im| < b / t) :
    paperFT (fun u => (stripTest (dil t Φ) u : ℂ)) z = t * Φ (t * z) :=
  paperFT_stripTest (by positivity) (by positivity) (stripDecay_dil hΦ ht)
    (neg_ofReal_of_neg_conj (dil_neg_conj h t)) hz

/-! ## Autocorrelations of strip tests -/

/-- The autocorrelation of a strip test is the strip test of its spectral square. -/
theorem crossCorr_stripTest_eq_specSq {Φ : ℂ → ℂ} {ε C : ℝ} (hε : 0 < ε)
    (hΦ : StripDecay Φ (5 / 4) ε C) (h : ∀ z, Φ (-z) = conj (Φ (conj z))) (y : ℝ) :
    crossCorr (stripTest Φ) (stripTest Φ) y = stripTest (specSq Φ) y := by
  rw [crossCorr_stripTest (by norm_num) hε hΦ (neg_ofReal_of_neg_conj h)]
  have hg := (goodDensity_specSq_of_neg_conj hε hΦ h).integral_cos_eq y
  simp_rw [specSq_re_ofReal] at hg
  unfold stripTest
  calc 1 / (2 * Real.pi) * ∫ r : ℝ, ‖Φ r‖ ^ 2 * Real.cos (r * y) =
      1 / 2 * (1 / Real.pi * ∫ r : ℝ, ‖Φ r‖ ^ 2 * Real.cos (r * y)) := by ring
    _ = _ := by rw [hg]; ring

theorem stripDecay_specSq {Φ : ℂ → ℂ} {b ε C : ℝ} (hΦ : StripDecay Φ b ε C) :
    StripDecay (specSq Φ) b (2 * ε) (C ^ 2) :=
  ⟨fun _ hz => differentiableAt_specSq hΦ hz, fun _ hz => norm_specSq_le hΦ hz⟩

/-- The constant `(∫ e^{−a|r|} dr)/(2π)` of the strip inversion bound. -/
def invConst (a : ℝ) : ℝ := (∫ r : ℝ, Real.exp (-(a * |r|))) / (2 * Real.pi)

theorem invConst_nonneg (a : ℝ) : 0 ≤ invConst a := by
  unfold invConst
  have : 0 ≤ ∫ r : ℝ, Real.exp (-(a * |r|)) := integral_nonneg fun _ => (Real.exp_pos _).le
  positivity

theorem abs_crossCorr_stripTest_le {Φ : ℂ → ℂ} {ε C : ℝ} (hε : 0 < ε)
    (hΦ : StripDecay Φ (5 / 4) ε C) (h : ∀ z, Φ (-z) = conj (Φ (conj z))) (y : ℝ) :
    |crossCorr (stripTest Φ) (stripTest Φ) y| ≤
      C ^ 2 * invConst (2 * ε) * Real.exp (-(5 / 4 * |y|)) := by
  rw [crossCorr_stripTest_eq_specSq hε hΦ h]
  have hb := norm_stripInvFT_le (by norm_num) (by linarith) (stripDecay_specSq hΦ) y
  unfold stripTest
  refine (Complex.abs_re_le_norm _).trans (hb.trans (le_of_eq ?_))
  unfold invConst; ring

/-! ## Null families -/

/-- A null family: `Ξ`-divisible strip functions whose weighted autocorrelation is prime-blind. -/
structure NullFamily (Φ : ℕ → ℂ → ℂ) (w : ℕ → ℝ) (ε : ℝ) (c : ℕ → ℝ) : Prop where
  rate : 0 < ε
  strip : ∀ j, StripDecay (Φ j) (5 / 4) ε (c j)
  weight : ∀ j, 0 ≤ w j
  summable : Summable fun j => w j * c j ^ 2
  sym : ∀ j z, Φ j (-z) = conj (Φ j (conj z))
  zero : ∀ j, ∀ ρ : zetaZeroConfig.carrier, Φ j (gammaOf ρ) = 0
  blind : ∀ n : ℕ, 2 ≤ n →
    ∑' j, w j * crossCorr (stripTest (Φ j)) (stripTest (Φ j)) (Real.log n) = 0

/-- The null ray `G₀ = Σ_j w_j F_j ⋆ F̃_j`. -/
def nullRay (Φ : ℕ → ℂ → ℂ) (w : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' j, w j * crossCorr (stripTest (Φ j)) (stripTest (Φ j)) x

/-- The spectral density `R = Σ_j w_j Φ_j Φ_j^#` of the null ray. -/
def nullDensity (Φ : ℕ → ℂ → ℂ) (w : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑' j, (w j : ℂ) * specSq (Φ j) z

variable {Φ : ℕ → ℂ → ℂ} {w : ℕ → ℝ} {ε : ℝ} {c : ℕ → ℝ}

/-- The total mass `Σ_j w_j C_j²`. -/
def familyMass (w c : ℕ → ℝ) : ℝ := ∑' j, w j * c j ^ 2

theorem NullFamily.mass_nonneg (hN : NullFamily Φ w ε c) : 0 ≤ familyMass w c :=
  tsum_nonneg fun j => mul_nonneg (hN.weight j) (sq_nonneg _)

theorem NullFamily.const_nonneg (hN : NullFamily Φ w ε c) (j : ℕ) : 0 ≤ c j :=
  (hN.strip j).const_nonneg (by norm_num)

theorem NullFamily.summable_crossCorr (hN : NullFamily Φ w ε c) (y : ℝ) :
    Summable fun j => w j * crossCorr (stripTest (Φ j)) (stripTest (Φ j)) y := by
  refine Summable.of_norm_bounded
    (hN.summable.mul_right (invConst (2 * ε) * Real.exp (-(5 / 4 * |y|)))) fun j => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hN.weight j)]
  have := abs_crossCorr_stripTest_le hN.rate (hN.strip j) (hN.sym j) y
  calc w j * |crossCorr (stripTest (Φ j)) (stripTest (Φ j)) y|
      ≤ w j * (c j ^ 2 * invConst (2 * ε) * Real.exp (-(5 / 4 * |y|))) :=
        mul_le_mul_of_nonneg_left this (hN.weight j)
    _ = _ := by ring

/-- The null ray is blind at every `log n`, `n ≥ 2`. -/
theorem NullFamily.nullRay_log (hN : NullFamily Φ w ε c) {n : ℕ} (hn : 2 ≤ n) :
    nullRay Φ w (Real.log n) = 0 :=
  hN.blind n hn

theorem nullRay_neg (Φ : ℕ → ℂ → ℂ) (w : ℕ → ℝ) (y : ℝ) : nullRay Φ w (-y) = nullRay Φ w y := by
  unfold nullRay
  simp_rw [crossCorr_self_neg]

theorem NullFamily.norm_term_le (hN : NullFamily Φ w ε c) (j : ℕ) {z : ℂ} (hz : |z.im| ≤ 5 / 4) :
    ‖(w j : ℂ) * specSq (Φ j) z‖ ≤ w j * c j ^ 2 * Real.exp (-(2 * ε * |z.re|)) := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hN.weight j), mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_specSq_le (hN.strip j) hz) (hN.weight j)

/-- **The density of the null ray** is holomorphic with decay on `|Im z| ≤ 9/8`. -/
theorem NullFamily.stripDecay_nullDensity (hN : NullFamily Φ w ε c) :
    StripDecay (nullDensity Φ w) (9 / 8) (2 * ε) (familyMass w c) := by
  set U : Set ℂ := {z | |z.im| < 5 / 4} with hUdef
  have hU : IsOpen U := isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const
  have hdiff : DifferentiableOn ℂ (nullDensity Φ w) U := by
    refine Complex.differentiableOn_tsum_of_summable_norm hN.summable (fun j => ?_) hU
      (fun j z hz => ?_)
    · intro z hz
      exact ((differentiableAt_specSq (hN.strip j) (le_of_lt hz)).const_mul
        _).differentiableWithinAt
    · refine (hN.norm_term_le j (le_of_lt hz)).trans ?_
      refine mul_le_of_le_one_right (mul_nonneg (hN.weight j) (sq_nonneg _))
        (Real.exp_le_one_iff.mpr ?_)
      have := hN.rate
      have := abs_nonneg z.re
      nlinarith
  refine ⟨fun z hz => hdiff.differentiableAt (hU.mem_nhds (show |z.im| < 5 / 4 by linarith)),
    fun z hz => ?_⟩
  have hz' : |z.im| ≤ 5 / 4 := by linarith
  have hs : Summable fun j => w j * c j ^ 2 * Real.exp (-(2 * ε * |z.re|)) :=
    hN.summable.mul_right _
  have hns : Summable fun j => ‖(w j : ℂ) * specSq (Φ j) z‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => hN.norm_term_le j hz') hs
  calc ‖nullDensity Φ w z‖ ≤ ∑' j, ‖(w j : ℂ) * specSq (Φ j) z‖ := norm_tsum_le_tsum_norm hns
    _ ≤ ∑' j, w j * c j ^ 2 * Real.exp (-(2 * ε * |z.re|)) :=
        hns.tsum_le_tsum (fun j => hN.norm_term_le j hz') hs
    _ = familyMass w c * Real.exp (-(2 * ε * |z.re|)) := by rw [tsum_mul_right]; rfl

/-- On the real line the density is `Σ_j w_j |Φ_j(r)|² ≥ 0`. -/
theorem nullDensity_ofReal (Φ : ℕ → ℂ → ℂ) (w : ℕ → ℝ) (r : ℝ) :
    nullDensity Φ w r = ((∑' j, w j * ‖Φ j r‖ ^ 2 : ℝ) : ℂ) := by
  unfold nullDensity
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun j => ?_
  unfold specSq
  rw [Complex.conj_ofReal, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast; ring

theorem NullFamily.nullDensity_ofReal_nonneg (hN : NullFamily Φ w ε c) (r : ℝ) :
    0 ≤ ∑' j, w j * ‖Φ j r‖ ^ 2 :=
  tsum_nonneg fun j => mul_nonneg (hN.weight j) (sq_nonneg _)

/-- **The null ray is the strip test of its density.** -/
theorem NullFamily.nullRay_eq_stripTest (hN : NullFamily Φ w ε c) (y : ℝ) :
    nullRay Φ w y = stripTest (nullDensity Φ w) y := by
  have hε := hN.rate
  set e : ℝ → ℂ := fun r => cexp (-(I * r * y)) with he
  have hne : ∀ r : ℝ, ‖e r‖ = 1 := fun r => norm_cexp_neg_I_real r y
  have hbd : ∀ j (r : ℝ), ‖(w j : ℂ) * specSq (Φ j) r * e r‖ ≤
      w j * c j ^ 2 * Real.exp (-(2 * ε * |r|)) := fun j r => by
    rw [norm_mul, hne, mul_one]
    have h := hN.norm_term_le j (z := r) (by simp; norm_num)
    simpa using h
  have hint : ∀ j, Integrable fun r : ℝ => (w j : ℂ) * specSq (Φ j) r * e r := by
    intro j
    have hc : Continuous fun r : ℝ => (w j : ℂ) * specSq (Φ j) r * e r := by
      have h1 := continuous_ofReal_comp_of_stripDecay (stripDecay_specSq (hN.strip j))
        (by norm_num)
      exact (continuous_const.mul h1).mul (by fun_prop)
    exact ((integrable_exp_neg_rate_abs (by linarith : (0 : ℝ) < 2 * ε)).const_mul
      (w j * c j ^ 2)).mono' hc.aestronglyMeasurable (Eventually.of_forall (hbd j))
  have hI : Integrable fun r : ℝ => Real.exp (-(2 * ε * |r|)) :=
    integrable_exp_neg_rate_abs (by linarith)
  have hsumI : Summable fun j => ∫ r : ℝ, ‖(w j : ℂ) * specSq (Φ j) r * e r‖ := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun _ => norm_nonneg _)
      (fun j => ?_) (hN.summable.mul_right (∫ r : ℝ, Real.exp (-(2 * ε * |r|))))
    rw [← integral_const_mul]
    exact integral_mono (hint j).norm (hI.const_mul _) (hbd j)
  have key : stripInvFT (nullDensity Φ w) y =
      ∑' j, (w j : ℂ) * stripInvFT (specSq (Φ j)) y := by
    unfold stripInvFT nullDensity
    have h1 : (fun r : ℝ => (∑' j, (w j : ℂ) * specSq (Φ j) r) * cexp (-(I * r * y))) =
        fun r : ℝ => ∑' j, (w j : ℂ) * specSq (Φ j) r * e r := by
      funext r; rw [tsum_mul_right]
    rw [h1, ← integral_tsum_of_summable_integral_norm hint hsumI, ← tsum_mul_left]
    refine tsum_congr fun j => ?_
    simp_rw [mul_assoc (w j : ℂ)]
    rw [integral_const_mul]; ring
  have hsC : Summable fun j => (w j : ℂ) * stripInvFT (specSq (Φ j)) y := by
    refine Summable.of_norm_bounded
      (hN.summable.mul_right (invConst (2 * ε) * Real.exp (-(5 / 4 * |y|)))) fun j => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hN.weight j)]
    have hb := norm_stripInvFT_le (by norm_num) (by linarith) (stripDecay_specSq (hN.strip j)) y
    calc w j * ‖stripInvFT (specSq (Φ j)) y‖ ≤
        w j * (c j ^ 2 * (∫ r : ℝ, Real.exp (-(2 * ε * |r|))) / (2 * Real.pi) *
          Real.exp (-(5 / 4 * |y|))) := mul_le_mul_of_nonneg_left hb (hN.weight j)
      _ = _ := by unfold invConst; ring
  unfold nullRay
  rw [show stripTest (nullDensity Φ w) y = (stripInvFT (nullDensity Φ w) y).re from rfl, key,
    Complex.re_tsum hsC]
  refine tsum_congr fun j => ?_
  rw [Complex.re_ofReal_mul, crossCorr_stripTest_eq_specSq hε (hN.strip j) (hN.sym j)]
  rfl

/-- **The null ray is differentiable.** -/
theorem NullFamily.hasDerivAt_nullRay (hN : NullFamily Φ w ε c) (y : ℝ) :
    HasDerivAt (nullRay Φ w) (stripInvFT (fun z => -I * z * nullDensity Φ w z) y).re y := by
  have e : nullRay Φ w = stripTest (nullDensity Φ w) := funext hN.nullRay_eq_stripTest
  have h := (Complex.reCLM.hasFDerivAt (x := stripInvFT (nullDensity Φ w) y)).comp_hasDerivAt y
    (hasDerivAt_stripInvFT (b := 9 / 8) (by norm_num) (by linarith [hN.rate])
      hN.stripDecay_nullDensity y)
  have h2 : HasDerivAt (stripTest (nullDensity Φ w))
      (Complex.reCLM (stripInvFT (fun z => -I * z * nullDensity Φ w z) y)) y := by
    rw [stripTest_eq_comp]; exact h
  rw [e]
  rwa [Complex.reCLM_apply] at h2

/-- **Decay of the derivative of the null ray.** -/
theorem NullFamily.exists_abs_deriv_nullRay_le (hN : NullFamily Φ w ε c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ, |deriv (nullRay Φ w) y| ≤ K * Real.exp (-(9 / 8 * |y|)) := by
  have hε := hN.rate
  have hs := hN.stripDecay_nullDensity.neg_I_mul_id (by norm_num : (0 : ℝ) ≤ 9 / 8)
    (by linarith : (0 : ℝ) < 2 * ε)
  refine ⟨familyMass w c * (2 / (2 * ε) + 9 / 8) * invConst (2 * ε / 2), ?_, fun y => ?_⟩
  · have := hN.mass_nonneg
    have := invConst_nonneg (2 * ε / 2)
    have : 0 ≤ 2 / (2 * ε) + 9 / 8 := by positivity
    positivity
  rw [(hN.hasDerivAt_nullRay y).deriv]
  refine (Complex.abs_re_le_norm _).trans ((norm_stripInvFT_le (by norm_num) (by linarith) hs
    y).trans (le_of_eq ?_))
  unfold invConst; ring

end RHTower.NullRayDilation

end
