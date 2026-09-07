import GaloisForLFunctions.RHTower.ConstrainedWeilTwistedOddTest
import GaloisForLFunctions.HTGeometry.CompactTestTransform

/-!
# A negativity witness for Suzuki's screw form from a top off-line zero

Let `ψ` be an odd smooth profile supported in `[−a, a]`, `q₀` a Xi zero copy with spectral point
`z₀ = γ₀ − i a₀` (`a₀ > 0`, `γ₀ ≥ 2`), and suppose the excess `a₀` is maximal with a margin `δ`:
every copy whose spectral point is neither `z₀` nor `conj z₀` has `|Im z_q| ≤ a₀ − δ`.  Then the
twisted odd test `cos(γ₀ x) ψ(x)` has screw form with real part at most

`−Φ₊² / (6 γ₀²) + N² e^{2a(a₀ − δ)} S₂`,

where `Φ₊ = ∫ e^{a₀ u} ψ(u) du`, `N = ∫ |ψ|`, and `S₂ = Σ_q |z_q|^{−2}`, provided the second-frequency
moment `∫ e^{a₀ u} e^{2iγ₀ u} ψ(u) du` is at most `Φ₊/8` in modulus (one integration by parts gives
`e^{a a₀} ‖ψ'‖₁ / (2γ₀)`, so this holds for large `γ₀`) and `32 a₀ ≤ γ₀`.

Mechanism.  The ray energy `Σ'_q −(1/4)(A_q + A'_q)²/z_q²` is split at `q₀`.  Every copy with spectral
point `z₀` contributes the same term, every copy with spectral point `conj z₀` the conjugate term, and
all other copies are bounded trivially by `e^{2a|Im z_q|} N² / |z_q|²`.  At the centre the pair moment is
`Φ₊ + A'`, and `Re((Φ₊ + A')² / z₀²) ≥ 0.72 Φ₊²/γ₀²` when `|A'| ≤ Φ₊/8` and `|Im z₀| ≤ Re z₀ / 32`.
Nothing here uses the Riemann hypothesis.
-/

open MeasureTheory Complex Set

namespace RHTower

noncomputable section

/-! ## Twisted moments as compact test transforms -/

/-- The twisted moment is the compact test transform at the complex frequency `μ − b i`. -/
theorem twistedMoment_eq_testTransform {a : ℝ} (ψ : OddSmoothProfile a) (b μ : ℝ) :
    twistedMoment ψ b μ
      = GaloisForLFunctions.HTGeometry.testTransform (fun u : ℝ => ((ψ u : ℝ) : ℂ))
          ((μ : ℂ) - (b : ℂ) * I) := by
  unfold twistedMoment GaloisForLFunctions.HTGeometry.testTransform
  congr 1
  funext u
  rw [mul_comm]
  congr 1
  congr 1
  linear_combination ((b : ℂ) * (u : ℂ)) * Complex.I_sq

theorem OddSmoothProfile.eq_zero_of_abs_gt {a : ℝ} (ψ : OddSmoothProfile a) {x : ℝ}
    (hx : a < |x|) : ψ x = 0 := by
  by_contra h
  have hmem : x ∈ Icc (-a) a := ψ.support_subset h
  rw [mem_Icc] at hmem
  rw [lt_abs] at hx
  rcases hx with hx | hx <;> linarith

theorem OddSmoothProfile.ofReal_eq_zero_of_abs_gt {a : ℝ} (ψ : OddSmoothProfile a) {x : ℝ}
    (hx : a < |x|) : ((ψ x : ℝ) : ℂ) = 0 := by
  rw [ψ.eq_zero_of_abs_gt hx, Complex.ofReal_zero]

theorem OddSmoothProfile.contDiff_ofReal {a : ℝ} (ψ : OddSmoothProfile a) :
    ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ => ((ψ u : ℝ) : ℂ)) :=
  (ContinuousLinearMap.contDiff Complex.ofRealCLM).comp ψ.smooth

/-- The `L¹` norm of a profile. -/
def profileMass {a : ℝ} (ψ : OddSmoothProfile a) : ℝ := ∫ u : ℝ, ‖((ψ u : ℝ) : ℂ)‖

/-- The `L¹` norm of the derivative of a profile. -/
def profileDerivMass {a : ℝ} (ψ : OddSmoothProfile a) : ℝ :=
  ∫ u : ℝ, ‖deriv (fun v : ℝ => ((ψ v : ℝ) : ℂ)) u‖

theorem profileMass_nonneg {a : ℝ} (ψ : OddSmoothProfile a) : 0 ≤ profileMass ψ :=
  integral_nonneg fun _ => norm_nonneg _

theorem profileDerivMass_nonneg {a : ℝ} (ψ : OddSmoothProfile a) : 0 ≤ profileDerivMass ψ :=
  integral_nonneg fun _ => norm_nonneg _

/-- **Trivial bound.** `‖A(b, μ)‖ ≤ e^{a|b|} ∫|ψ|`. -/
theorem norm_twistedMoment_le {a : ℝ} (ψ : OddSmoothProfile a) (ha : 0 ≤ a) (b μ : ℝ) :
    ‖twistedMoment ψ b μ‖ ≤ Real.exp (a * |b|) * profileMass ψ := by
  rw [twistedMoment_eq_testTransform]
  refine GaloisForLFunctions.HTGeometry.norm_testTransform_le_exp
    (Complex.continuous_ofReal.comp ψ.continuous) ψ.hasCompactSupport_ofReal ha
    (fun x hx => ψ.ofReal_eq_zero_of_abs_gt hx) _ ?_
  simp

theorem deriv_ofReal_profile_eq_zero_of_abs_gt {a : ℝ} (ψ : OddSmoothProfile a) {x : ℝ}
    (hx : a < |x|) : deriv (fun v : ℝ => ((ψ v : ℝ) : ℂ)) x = 0 := by
  have hopen : IsOpen {y : ℝ | a < |y|} := isOpen_lt continuous_const continuous_abs
  have hmem : {y : ℝ | a < |y|} ∈ nhds x := hopen.mem_nhds hx
  have heq : (fun v : ℝ => ((ψ v : ℝ) : ℂ)) =ᶠ[nhds x] fun _ => (0 : ℂ) :=
    Filter.eventually_of_mem hmem fun y hy => ψ.ofReal_eq_zero_of_abs_gt hy
  rw [heq.deriv_eq, deriv_const]

/-- **One integration by parts.** `‖A(b, μ)‖ · ‖μ − b i‖ ≤ e^{a|b|} ∫|ψ'|`. -/
theorem norm_twistedMoment_mul_norm_le {a : ℝ} (ψ : OddSmoothProfile a) (ha : 0 ≤ a) (b μ : ℝ) :
    ‖twistedMoment ψ b μ‖ * ‖(μ : ℂ) - (b : ℂ) * I‖
      ≤ Real.exp (a * |b|) * profileDerivMass ψ := by
  rw [twistedMoment_eq_testTransform]
  have h1 : ContDiff ℝ 1 (fun u : ℝ => ((ψ u : ℝ) : ℂ)) :=
    ψ.contDiff_ofReal.of_le (by exact_mod_cast le_top)
  have hibp := GaloisForLFunctions.HTGeometry.testTransform_ibp h1 ψ.hasCompactSupport_ofReal
    ((μ : ℂ) - (b : ℂ) * I)
  have hnorm : ‖GaloisForLFunctions.HTGeometry.testTransform (fun u : ℝ => ((ψ u : ℝ) : ℂ))
      ((μ : ℂ) - (b : ℂ) * I)‖ * ‖(μ : ℂ) - (b : ℂ) * I‖
      = ‖GaloisForLFunctions.HTGeometry.testTransform
          (deriv fun u : ℝ => ((ψ u : ℝ) : ℂ)) ((μ : ℂ) - (b : ℂ) * I)‖ := by
    rw [← norm_neg (GaloisForLFunctions.HTGeometry.testTransform (deriv _) _), ← hibp, norm_mul,
      norm_mul, Complex.norm_I, one_mul]
  rw [hnorm]
  refine GaloisForLFunctions.HTGeometry.norm_testTransform_le_exp
    (ψ.contDiff_ofReal.continuous_deriv (by exact_mod_cast le_top))
    ψ.hasCompactSupport_ofReal.deriv ha
    (fun x hx => deriv_ofReal_profile_eq_zero_of_abs_gt ψ hx) _ ?_
  simp

/-- The derivative bound in division form, for nonzero frequency. -/
theorem norm_twistedMoment_le_div {a : ℝ} (ψ : OddSmoothProfile a) (ha : 0 ≤ a) (b : ℝ)
    {μ : ℝ} (hμ : μ ≠ 0) :
    ‖twistedMoment ψ b μ‖ ≤ Real.exp (a * |b|) * profileDerivMass ψ / |μ| := by
  have hz : |μ| ≤ ‖(μ : ℂ) - (b : ℂ) * I‖ := by
    have : ((μ : ℂ) - (b : ℂ) * I).re = μ := by simp
    calc |μ| = |((μ : ℂ) - (b : ℂ) * I).re| := by rw [this]
      _ ≤ ‖(μ : ℂ) - (b : ℂ) * I‖ := Complex.abs_re_le_norm _
  have hμ0 : 0 < |μ| := abs_pos.mpr hμ
  have h := norm_twistedMoment_mul_norm_le ψ ha b μ
  rw [le_div_iff₀ hμ0]
  calc ‖twistedMoment ψ b μ‖ * |μ|
      ≤ ‖twistedMoment ψ b μ‖ * ‖(μ : ℂ) - (b : ℂ) * I‖ :=
        mul_le_mul_of_nonneg_left hz (norm_nonneg _)
    _ ≤ Real.exp (a * |b|) * profileDerivMass ψ := h

/-- The trivial bound for the pair moment: `‖A_q + A'_q‖ ≤ 2 e^{a|Im z_q|} ∫|ψ|`. -/
theorem norm_twistedPairMoment_le {a : ℝ} (ψ : OddSmoothProfile a) (ha : 0 ≤ a) (γ : ℝ)
    (q : XiZeroCopy) :
    ‖twistedPairMoment ψ γ q‖
      ≤ 2 * Real.exp (a * |(xiSpectralPoint q).im|) * profileMass ψ := by
  unfold twistedPairMoment
  refine le_trans (norm_add_le _ _) ?_
  have h1 := norm_twistedMoment_le ψ ha (-(xiSpectralPoint q).im) ((xiSpectralPoint q).re - γ)
  have h2 := norm_twistedMoment_le ψ ha (-(xiSpectralPoint q).im) ((xiSpectralPoint q).re + γ)
  rw [abs_neg] at h1 h2
  linarith

/-! ## The ray term of a copy -/

/-- The ray term of the twisted odd test at a copy. -/
def twistedRayTerm {a : ℝ} (ψ : OddSmoothProfile a) (γ : ℝ) (q : XiZeroCopy) : ℂ :=
  -(1 / 4 : ℂ) * twistedPairMoment ψ γ q ^ 2 / xiSpectralPoint q ^ 2

theorem norm_twistedRayTerm_le {a : ℝ} (ψ : OddSmoothProfile a) (ha : 0 ≤ a) (γ : ℝ)
    (q : XiZeroCopy) :
    ‖twistedRayTerm ψ γ q‖
      ≤ Real.exp (2 * a * |(xiSpectralPoint q).im|) * profileMass ψ ^ 2
          * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
  unfold twistedRayTerm
  rw [norm_div, norm_mul, norm_pow, norm_pow, norm_neg, norm_div, norm_one, Complex.norm_ofNat]
  have hz : 0 < ‖xiSpectralPoint q‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have hP := norm_twistedPairMoment_le ψ ha γ q
  have hP0 : 0 ≤ ‖twistedPairMoment ψ γ q‖ := norm_nonneg _
  have hE : 0 ≤ Real.exp (a * |(xiSpectralPoint q).im|) := (Real.exp_pos _).le
  have hM : 0 ≤ profileMass ψ := profileMass_nonneg ψ
  have hsq : ‖twistedPairMoment ψ γ q‖ ^ 2
      ≤ (2 * Real.exp (a * |(xiSpectralPoint q).im|) * profileMass ψ) ^ 2 :=
    pow_le_pow_left₀ hP0 hP 2
  have hexp : (2 * Real.exp (a * |(xiSpectralPoint q).im|) * profileMass ψ) ^ 2
      = 4 * Real.exp (2 * a * |(xiSpectralPoint q).im|) * profileMass ψ ^ 2 := by
    rw [mul_pow, mul_pow, ← Real.exp_nat_mul]
    push_cast
    ring_nf
  rw [div_le_iff₀ (by positivity)]
  calc 1 / 4 * ‖twistedPairMoment ψ γ q‖ ^ 2
      ≤ 1 / 4 * (4 * Real.exp (2 * a * |(xiSpectralPoint q).im|) * profileMass ψ ^ 2) := by
        rw [← hexp]; exact mul_le_mul_of_nonneg_left hsq (by norm_num)
    _ = Real.exp (2 * a * |(xiSpectralPoint q).im|) * profileMass ψ ^ 2
          * (1 / ‖xiSpectralPoint q‖ ^ 2) * ‖xiSpectralPoint q‖ ^ 2 := by
        field_simp

theorem summable_twistedRayTerm {a : ℝ} (ψ : OddSmoothProfile a) (γ : ℝ) :
    Summable (fun q : XiZeroCopy => twistedRayTerm ψ γ q) :=
  summable_twistedOddTest_rayEnergy ψ γ

theorem re_suzukiScrewSmoothForm_twistedOddTest_eq_tsum_rayTerm {a : ℝ} (ψ : OddSmoothProfile a)
    (γ : ℝ) :
    (suzukiScrewSmoothForm (twistedOddTest ψ γ) (twistedOddTest ψ γ)).re
      = ∑' q : XiZeroCopy, (twistedRayTerm ψ γ q).re :=
  re_suzukiScrewSmoothForm_twistedOddTest ψ γ

/-- Copies with the same spectral point have the same ray term. -/
theorem twistedRayTerm_congr {a : ℝ} (ψ : OddSmoothProfile a) (γ : ℝ) {q q' : XiZeroCopy}
    (h : xiSpectralPoint q = xiSpectralPoint q') :
    twistedRayTerm ψ γ q = twistedRayTerm ψ γ q' := by
  unfold twistedRayTerm twistedPairMoment
  rw [h]

/-- Copies with conjugate spectral points have conjugate ray terms. -/
theorem twistedRayTerm_of_conj {a : ℝ} (ψ : OddSmoothProfile a) (γ : ℝ) {q q' : XiZeroCopy}
    (h : xiSpectralPoint q = (starRingEnd ℂ) (xiSpectralPoint q')) :
    twistedRayTerm ψ γ q = (starRingEnd ℂ) (twistedRayTerm ψ γ q') := by
  have hre : (xiSpectralPoint q).re = (xiSpectralPoint q').re := by rw [h, Complex.conj_re]
  have him : (xiSpectralPoint q).im = -(xiSpectralPoint q').im := by rw [h, Complex.conj_im]
  have hP : twistedPairMoment ψ γ q = -(starRingEnd ℂ) (twistedPairMoment ψ γ q') := by
    unfold twistedPairMoment
    rw [hre, him, neg_neg, map_add, conj_twistedMoment, conj_twistedMoment]
    have e1 := twistedMoment_neg_neg ψ ((xiSpectralPoint q').im) ((xiSpectralPoint q').re - γ)
    have e2 := twistedMoment_neg_neg ψ ((xiSpectralPoint q').im) ((xiSpectralPoint q').re + γ)
    rw [e1, e2]
    ring
  unfold twistedRayTerm
  rw [hP, h, map_div₀, map_mul, map_pow, map_pow, map_neg, map_div₀, map_one, map_ofNat,
    neg_sq]

/-! ## The centred term -/

/-- Real-part lower bound for `(Φ + E)² w` with `w = z⁻²`, `|E| ≤ Φ/8`, `|Im z| ≤ Re z / 32`,
`Re z ≥ 2`. -/
theorem re_sq_div_sq_ge {z : ℂ} (hre : 2 ≤ z.re) (him : |z.im| ≤ z.re / 32) {Φ : ℝ} (hΦ : 0 ≤ Φ)
    {E : ℂ} (hE : ‖E‖ ≤ Φ / 8) :
    (18 / 25 : ℝ) * Φ ^ 2 / z.re ^ 2 ≤ ((((Φ : ℂ) + E) ^ 2) / z ^ 2).re := by
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_re] at hre
    linarith
  have hre0 : 0 < z.re := by linarith
  set w : ℂ := (z ^ 2)⁻¹ with hw
  have hnorm2 : Complex.normSq (z ^ 2) = Complex.normSq z ^ 2 := by rw [map_pow]
  have hnsq : Complex.normSq z = z.re ^ 2 + z.im ^ 2 := by rw [Complex.normSq_apply]; ring
  have hnsq_pos : 0 < Complex.normSq z := by rw [hnsq]; positivity
  have hwre : w.re = (z.re ^ 2 - z.im ^ 2) / Complex.normSq z ^ 2 := by
    rw [hw, Complex.inv_re, hnorm2]
    congr 1
    rw [pow_two, Complex.mul_re]
    ring
  have hwnorm : ‖w‖ = 1 / Complex.normSq z := by
    rw [hw, norm_inv, norm_pow, Complex.sq_norm]
    ring
  -- bounds on the pieces
  have him2 : z.im ^ 2 ≤ z.re ^ 2 / 1024 := by
    have h1 : z.im ^ 2 = |z.im| ^ 2 := (sq_abs _).symm
    rw [h1]
    have := pow_le_pow_left₀ (abs_nonneg _) him 2
    calc |z.im| ^ 2 ≤ (z.re / 32) ^ 2 := this
      _ = z.re ^ 2 / 1024 := by ring
  have hnsq_le : Complex.normSq z ≤ z.re ^ 2 * (1025 / 1024) := by
    rw [hnsq]; linarith
  have hwre_ge : (1023 / 1025) * ‖w‖ ≤ w.re := by
    rw [hwre, hwnorm]
    have hL : (1023 / 1025 : ℝ) * (1 / Complex.normSq z) = (1023 / 1025) / Complex.normSq z := by
      ring
    rw [hL, div_le_div_iff₀ hnsq_pos (by positivity)]
    have hpos : 0 ≤ (2 / 1025 : ℝ) * z.re ^ 2 - (2048 / 1025) * z.im ^ 2 := by
      nlinarith [him2]
    nlinarith [mul_nonneg hnsq_pos.le hpos, hnsq]
  -- the expansion
  have hexp : (((Φ : ℂ) + E) ^ 2) / z ^ 2 = (Φ : ℂ) ^ 2 * w + (2 * (Φ : ℂ) * E + E ^ 2) * w := by
    rw [hw, div_eq_mul_inv]; ring
  rw [hexp, Complex.add_re]
  have h1 : ((Φ : ℂ) ^ 2 * w).re = Φ ^ 2 * w.re := by
    rw [← Complex.ofReal_pow, Complex.re_ofReal_mul]
  have h2 : -(‖2 * (Φ : ℂ) * E + E ^ 2‖ * ‖w‖) ≤ ((2 * (Φ : ℂ) * E + E ^ 2) * w).re := by
    have := Complex.abs_re_le_norm ((2 * (Φ : ℂ) * E + E ^ 2) * w)
    rw [norm_mul] at this
    linarith [(abs_le.mp this).1]
  have h3 : ‖2 * (Φ : ℂ) * E + E ^ 2‖ ≤ (17 / 64) * Φ ^ 2 := by
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΦ,
      Complex.norm_ofNat]
    have hE2 : ‖E‖ ^ 2 ≤ (Φ / 8) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hE 2
    nlinarith [mul_le_mul_of_nonneg_left hE hΦ]
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg _
  have hwnorm_ge : 1 / (z.re ^ 2 * (1025 / 1024)) ≤ ‖w‖ := by
    rw [hwnorm]
    exact one_div_le_one_div_of_le hnsq_pos hnsq_le
  rw [h1]
  have key : (18 / 25 : ℝ) * Φ ^ 2 / z.re ^ 2 ≤ Φ ^ 2 * w.re - (17 / 64) * Φ ^ 2 * ‖w‖ := by
    have hΦ2 : 0 ≤ Φ ^ 2 := sq_nonneg _
    have : (18 / 25 : ℝ) / z.re ^ 2 ≤ (1023 / 1025 - 17 / 64) * ‖w‖ := by
      calc (18 / 25 : ℝ) / z.re ^ 2
          ≤ (1023 / 1025 - 17 / 64) * (1 / (z.re ^ 2 * (1025 / 1024))) := by
            have hrw : (1023 / 1025 - 17 / 64 : ℝ) * (1 / (z.re ^ 2 * (1025 / 1024)))
                = ((1023 / 1025 - 17 / 64) * (1024 / 1025)) / z.re ^ 2 := by
              field_simp
            rw [hrw]
            exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
        _ ≤ (1023 / 1025 - 17 / 64) * ‖w‖ := by gcongr
    calc (18 / 25 : ℝ) * Φ ^ 2 / z.re ^ 2 = Φ ^ 2 * ((18 / 25) / z.re ^ 2) := by ring
      _ ≤ Φ ^ 2 * ((1023 / 1025 - 17 / 64) * ‖w‖) := mul_le_mul_of_nonneg_left this hΦ2
      _ ≤ Φ ^ 2 * w.re - (17 / 64) * Φ ^ 2 * ‖w‖ := by nlinarith
  linarith [mul_le_mul_of_nonneg_right h3 hw0]

/-- **The centred ray term of a top copy is negative**: with `Φ₊ = ∫ e^{a₀u}ψ` and the second
frequency moment `A'` of modulus at most `Φ₊/8`, the ray term at the centre `γ₀ = Re z₀` has real part
at most `−(9/50) Φ₊² / γ₀²`. -/
theorem re_twistedRayTerm_centre_le {a : ℝ} (ψ : OddSmoothProfile a) (q₀ : XiZeroCopy)
    (hre : 2 ≤ (xiSpectralPoint q₀).re)
    (him : |(xiSpectralPoint q₀).im| ≤ (xiSpectralPoint q₀).re / 32)
    (hΦ : 0 ≤ (twistedMoment ψ (-(xiSpectralPoint q₀).im) 0).re)
    (hA' : ‖twistedMoment ψ (-(xiSpectralPoint q₀).im) (2 * (xiSpectralPoint q₀).re)‖
      ≤ (twistedMoment ψ (-(xiSpectralPoint q₀).im) 0).re / 8) :
    (twistedRayTerm ψ (xiSpectralPoint q₀).re q₀).re
      ≤ -((9 / 50 : ℝ) * (twistedMoment ψ (-(xiSpectralPoint q₀).im) 0).re ^ 2
          / (xiSpectralPoint q₀).re ^ 2) := by
  set Φ : ℝ := (twistedMoment ψ (-(xiSpectralPoint q₀).im) 0).re with hΦdef
  have hreal : twistedMoment ψ (-(xiSpectralPoint q₀).im) 0 = (Φ : ℂ) := by
    apply Complex.ext
    · simp [hΦdef]
    · simp [twistedMoment_im_zero]
  have hpair : twistedPairMoment ψ (xiSpectralPoint q₀).re q₀
      = (Φ : ℂ) + twistedMoment ψ (-(xiSpectralPoint q₀).im) (2 * (xiSpectralPoint q₀).re) := by
    rw [twistedPairMoment_centre, hreal]
  unfold twistedRayTerm
  rw [hpair]
  have hkey := re_sq_div_sq_ge hre him hΦ hA'
  have hsplit : (-(1 / 4 : ℂ) * ((Φ : ℂ) + twistedMoment ψ (-(xiSpectralPoint q₀).im)
      (2 * (xiSpectralPoint q₀).re)) ^ 2 / xiSpectralPoint q₀ ^ 2).re
      = -(1 / 4 : ℝ) * ((((Φ : ℂ) + twistedMoment ψ (-(xiSpectralPoint q₀).im)
          (2 * (xiSpectralPoint q₀).re)) ^ 2) / xiSpectralPoint q₀ ^ 2).re := by
    rw [mul_div_assoc, show (-(1 / 4 : ℂ)) = ((-(1 / 4 : ℝ) : ℝ) : ℂ) by push_cast; ring,
      Complex.re_ofReal_mul]
  rw [hsplit]
  have hq : (9 / 50 : ℝ) * Φ ^ 2 / (xiSpectralPoint q₀).re ^ 2
      = (1 / 4 : ℝ) * ((18 / 25 : ℝ) * Φ ^ 2 / (xiSpectralPoint q₀).re ^ 2) := by ring
  rw [hq]
  linarith

/-! ## Assembly -/

/-- The universal sum `Σ_q |z_q|^{−2}` over the Xi zero copies. -/
def xiSpectralInvSqTotal : ℝ := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2

/-- **Negativity witness.**  If the copy `q₀` has spectral point `z₀ = γ₀ − i a₀` with
`γ₀ ≥ 2`, `|a₀| ≤ γ₀/32`, the second-frequency moment is at most `Φ₊/8`, and every copy whose spectral
point is neither `z₀` nor `conj z₀` has `|Im z_q| ≤ a₀ − δ`, then the twisted odd test centred at `γ₀`
has screw form with real part at most `−(9/50) Φ₊²/γ₀² + N² e^{2a(a₀ − δ)} S₂`. -/
theorem re_suzukiScrewSmoothForm_twistedOddTest_le_of_topExcess {a : ℝ} (ψ : OddSmoothProfile a)
    (ha : 0 ≤ a) (q₀ : XiZeroCopy)
    (hre : 2 ≤ (xiSpectralPoint q₀).re)
    (him : |(xiSpectralPoint q₀).im| ≤ (xiSpectralPoint q₀).re / 32)
    (hΦ : 0 ≤ (twistedMoment ψ (-(xiSpectralPoint q₀).im) 0).re)
    (hA' : ‖twistedMoment ψ (-(xiSpectralPoint q₀).im) (2 * (xiSpectralPoint q₀).re)‖
      ≤ (twistedMoment ψ (-(xiSpectralPoint q₀).im) 0).re / 8)
    {δ : ℝ}
    (hgap : ∀ q : XiZeroCopy, xiSpectralPoint q ≠ xiSpectralPoint q₀ →
      xiSpectralPoint q ≠ (starRingEnd ℂ) (xiSpectralPoint q₀) →
      |(xiSpectralPoint q).im| ≤ -(xiSpectralPoint q₀).im - δ) :
    (suzukiScrewSmoothForm (twistedOddTest ψ (xiSpectralPoint q₀).re)
        (twistedOddTest ψ (xiSpectralPoint q₀).re)).re
      ≤ -((9 / 50 : ℝ) * (twistedMoment ψ (-(xiSpectralPoint q₀).im) 0).re ^ 2
            / (xiSpectralPoint q₀).re ^ 2)
        + Real.exp (2 * a * (-(xiSpectralPoint q₀).im - δ)) * profileMass ψ ^ 2
            * xiSpectralInvSqTotal := by
  classical
  set γ₀ : ℝ := (xiSpectralPoint q₀).re with hγ₀
  rw [re_suzukiScrewSmoothForm_twistedOddTest_eq_tsum_rayTerm]
  have hsum : Summable fun q : XiZeroCopy => (twistedRayTerm ψ γ₀ q).re :=
    (Complex.hasSum_re (summable_twistedRayTerm ψ γ₀).hasSum).summable
  -- split off `q₀`
  rw [← (hsum.sum_add_tsum_compl (s := {q₀}))]
  rw [Finset.sum_singleton]
  have hmain := re_twistedRayTerm_centre_le ψ q₀ hre him hΦ hA'
  -- bound the rest
  set g : XiZeroCopy → ℝ := fun q =>
    if xiSpectralPoint q = xiSpectralPoint q₀ ∨ xiSpectralPoint q = (starRingEnd ℂ) (xiSpectralPoint q₀)
    then 0
    else Real.exp (2 * a * (-(xiSpectralPoint q₀).im - δ)) * profileMass ψ ^ 2
      * (1 / ‖xiSpectralPoint q‖ ^ 2) with hg
  have hg_nonneg : ∀ q, 0 ≤ g q := by
    intro q
    simp only [hg]
    split_ifs
    · exact le_rfl
    · have := profileMass_nonneg ψ
      positivity
  have hg_summable : Summable g := by
    refine Summable.of_nonneg_of_le hg_nonneg (fun q => ?_)
      (xiSpectralPoint_inv_sq_summable.mul_left
        (Real.exp (2 * a * (-(xiSpectralPoint q₀).im - δ)) * profileMass ψ ^ 2))
    simp only [hg]
    split_ifs
    · have := profileMass_nonneg ψ
      positivity
    · exact le_rfl
  have hterm_le : ∀ q : XiZeroCopy, q ≠ q₀ → (twistedRayTerm ψ γ₀ q).re ≤ g q := by
    intro q hq
    simp only [hg]
    split_ifs with hcase
    · rcases hcase with hcase | hcase
      · rw [twistedRayTerm_congr ψ γ₀ hcase]
        have : 0 ≤ (9 / 50 : ℝ) * (twistedMoment ψ (-(xiSpectralPoint q₀).im) 0).re ^ 2
            / (xiSpectralPoint q₀).re ^ 2 := by positivity
        linarith
      · rw [twistedRayTerm_of_conj ψ γ₀ hcase, Complex.conj_re]
        have : 0 ≤ (9 / 50 : ℝ) * (twistedMoment ψ (-(xiSpectralPoint q₀).im) 0).re ^ 2
            / (xiSpectralPoint q₀).re ^ 2 := by positivity
        linarith
    · push Not at hcase
      have hgapq := hgap q hcase.1 hcase.2
      have hb := norm_twistedRayTerm_le ψ ha γ₀ q
      have hre_le : (twistedRayTerm ψ γ₀ q).re ≤ ‖twistedRayTerm ψ γ₀ q‖ :=
        Complex.re_le_norm _
      have hexp : Real.exp (2 * a * |(xiSpectralPoint q).im|)
          ≤ Real.exp (2 * a * (-(xiSpectralPoint q₀).im - δ)) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left hgapq (by linarith)
      have hM : 0 ≤ profileMass ψ ^ 2 := sq_nonneg _
      have hz : 0 ≤ 1 / ‖xiSpectralPoint q‖ ^ 2 := by positivity
      calc (twistedRayTerm ψ γ₀ q).re ≤ ‖twistedRayTerm ψ γ₀ q‖ := hre_le
        _ ≤ Real.exp (2 * a * |(xiSpectralPoint q).im|) * profileMass ψ ^ 2
            * (1 / ‖xiSpectralPoint q‖ ^ 2) := hb
        _ ≤ Real.exp (2 * a * (-(xiSpectralPoint q₀).im - δ)) * profileMass ψ ^ 2
            * (1 / ‖xiSpectralPoint q‖ ^ 2) := by gcongr
  have hrest : ∑' q : ↥((({q₀} : Finset XiZeroCopy) : Set XiZeroCopy)ᶜ),
      (twistedRayTerm ψ γ₀ (q : XiZeroCopy)).re
      ≤ Real.exp (2 * a * (-(xiSpectralPoint q₀).im - δ)) * profileMass ψ ^ 2
          * xiSpectralInvSqTotal := by
    have hsub : Summable fun q : ↥((({q₀} : Finset XiZeroCopy) : Set XiZeroCopy)ᶜ) =>
        (twistedRayTerm ψ γ₀ (q : XiZeroCopy)).re :=
      hsum.subtype _
    have hgsub : Summable fun q : ↥((({q₀} : Finset XiZeroCopy) : Set XiZeroCopy)ᶜ) =>
        g (q : XiZeroCopy) := hg_summable.subtype _
    calc ∑' q : ↥((({q₀} : Finset XiZeroCopy) : Set XiZeroCopy)ᶜ),
          (twistedRayTerm ψ γ₀ (q : XiZeroCopy)).re
        ≤ ∑' q : ↥((({q₀} : Finset XiZeroCopy) : Set XiZeroCopy)ᶜ), g (q : XiZeroCopy) := by
          refine hsub.tsum_le_tsum (fun q => ?_) hgsub
          apply hterm_le
          have hq := q.2
          simp only [Set.mem_compl_iff, Finset.coe_singleton, Set.mem_singleton_iff] at hq
          exact hq
      _ ≤ ∑' q : XiZeroCopy, g q :=
          Summable.tsum_subtype_le g ((({q₀} : Finset XiZeroCopy) : Set XiZeroCopy)ᶜ) hg_nonneg
            hg_summable
      _ ≤ ∑' q : XiZeroCopy, Real.exp (2 * a * (-(xiSpectralPoint q₀).im - δ))
            * profileMass ψ ^ 2 * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
          refine hg_summable.tsum_le_tsum (fun q => ?_)
            (xiSpectralPoint_inv_sq_summable.mul_left _)
          simp only [hg]
          split_ifs
          · have := profileMass_nonneg ψ
            positivity
          · exact le_rfl
      _ = Real.exp (2 * a * (-(xiSpectralPoint q₀).im - δ)) * profileMass ψ ^ 2
            * xiSpectralInvSqTotal := by
          unfold xiSpectralInvSqTotal
          rw [tsum_mul_left]
  linarith

end

end RHTower
