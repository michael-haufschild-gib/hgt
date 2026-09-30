import GaloisForLFunctions.RHTower.ZetaNotchScaleMixture
import GaloisForLFunctions.RHTower.ZetaNotchStripExtensions
import GaloisForLFunctions.RHTower.WeilNullPotentialExpPairing

/-!
# The mixed `|ζ|²` notch: pairing inequality and analytic tail

With the Gaussian mixture `Ω_L` of notch windows, a weight `q ≥ 0` that is the restriction of a
function `Q` holomorphic and bounded on `|Im z| ≤ c` (`0 < c < 1/2`), and
`M_Ω(y) = ∫ Ω_L(t) q(t) |ζ(½+it)|² e^{−iyt} dt`:

* **pairing inequality** (`sum_mul_re_mixMoment_nonpos`): if `−ψ_v` is positive definite and
  `Σ_n |v(n)| n^{−c} < ∞`, then `Σ_n v(n) Re M_Ω(log n) ≤ 0`. The test `G = Ω_L Q W` is holomorphic
  on the strip with real-direction decay `e^{−|Re z|}` (`exists_norm_mixTest_le`), so its transform
  decays like `e^{−c|v|}` and the exponential pairing applies;
* **analytic tail** (`exists_norm_mixMoment_le`): `‖M_Ω(y)‖ ≤ C (1 + L²) e^{−cy}` for `y ≥ 0`, by
  shifting `∫ Ω_L Q Z e^{−iyz}` to `Im z = −c` and bounding the quadratic moment of `Ω_L`;
* **scale split** (`mixMoment_eq`): `M_Ω(y)` is the scale integral of the notch-window moments
  `M_u(y)` plus the negative half-line, which is `O(e^{−L²})` (`exists_norm_mixMomentNeg_le`).
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry
open FourierTransform
open scoped ComplexConjugate

namespace RHTower.ZetaNotch

/-- The mixed moment `M_Ω(y) = ∫ Ω_L(t) q(t) |ζ(½+it)|² e^{−iyt} dt`. -/
def mixMoment (L : ℝ) (q : ℝ → ℝ) (y : ℝ) : ℂ :=
  ∫ t : ℝ, mixWindow L t * (q t : ℂ) * zetaSq t * Complex.exp (-(y * t) * I)

/-- The analytic notch test `G(z) = Ω_L(z) Q(z) W(z)`. -/
def mixTest (L : ℝ) (Q : ℂ → ℂ) (z : ℂ) : ℂ := mixWindow L z * Q z * gammaWeightC z

/-! ## Real-direction decay -/

theorem gauss_mul_exp_pi_le (x : ℝ) :
    Real.exp (-(2 / 25) * x ^ 2) * Real.exp (Real.pi * |x|) ≤ Real.exp 56 * Real.exp (-|x|) := by
  rw [← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hx : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
  rw [hx]
  have hπ := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  nlinarith [sq_nonneg (|x| - 25 * (Real.pi + 1) / 4), abs_nonneg x,
    mul_self_le_mul_self (by linarith : (0 : ℝ) ≤ Real.pi + 1) (by linarith : Real.pi + 1 ≤ 4.15)]

theorem norm_mixWindow_le_line (L : ℝ) (z : ℂ) :
    ‖mixWindow L z‖ ≤ Real.exp (4 * z.im ^ 2) * mixWindowReal L z.re := by
  have h := norm_mixWindow_le L z.re z.im
  rwa [Complex.re_add_im] at h

theorem norm_mixWindow_le_gauss (L : ℝ) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖mixWindow L z‖ ≤ Real.exp 1 * (4 * (Real.exp (L ^ 2) * Real.exp (-(2 / 25) * z.re ^ 2))) := by
  have h1 := norm_mixWindow_le_line L z
  have h2 := mixWindowReal_le_gauss L z.re
  have h3 : Real.exp (4 * z.im ^ 2) ≤ Real.exp 1 := by
    refine Real.exp_le_exp.mpr ?_
    have := abs_le.mp hz
    nlinarith
  calc ‖mixWindow L z‖ ≤ Real.exp (4 * z.im ^ 2) * mixWindowReal L z.re := h1
    _ ≤ Real.exp 1 * (4 * (Real.exp (L ^ 2) * Real.exp (-(2 / 25) * z.re ^ 2))) :=
        mul_le_mul h3 h2 (mixWindowReal_nonneg _ _) (Real.exp_pos _).le

theorem differentiableAt_mixTest (L : ℝ) {Q : ℂ → ℂ} (hQd : Differentiable ℂ Q) {z : ℂ}
    (hz : |z.im| < 1 / 2) : DifferentiableAt ℂ (mixTest L Q) z :=
  (((differentiable_mixWindow L) z).mul (hQd z)).mul (differentiableAt_gammaWeightC hz)

/-- **The analytic test decays in the real direction** on every substrip `|Im z| ≤ c < 1/2`. -/
theorem exists_norm_mixTest_le (L : ℝ) {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 2) {Q : ℂ → ℂ}
    {CQ : ℝ} (hQb : ∀ z : ℂ, |z.im| ≤ c → ‖Q z‖ ≤ CQ) :
    ∃ C, 0 ≤ C ∧ ∀ z : ℂ, |z.im| ≤ c → ‖mixTest L Q z‖ ≤ C * Real.exp (-|z.re|) := by
  obtain ⟨CW, hCW0, hCW⟩ := exists_norm_gammaWeightC_le hc0 hc
  have hCQ0 : 0 ≤ CQ := (norm_nonneg _).trans (hQb 0 (by simpa using hc0))
  refine ⟨Real.exp 1 * (4 * Real.exp (L ^ 2)) * CQ * CW * Real.exp 56, by positivity,
    fun z hz => ?_⟩
  have h1 := norm_mixWindow_le_gauss L (z := z) (by linarith)
  have h2 := hQb z hz
  have h3 := hCW z hz
  have h4 := gauss_mul_exp_pi_le z.re
  unfold mixTest
  rw [norm_mul, norm_mul]
  calc ‖mixWindow L z‖ * ‖Q z‖ * ‖gammaWeightC z‖
      ≤ (Real.exp 1 * (4 * (Real.exp (L ^ 2) * Real.exp (-(2 / 25) * z.re ^ 2)))) * CQ *
          (CW * Real.exp (Real.pi * |z.re|)) :=
        mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h3 (norm_nonneg _)
          (by positivity)
    _ = Real.exp 1 * (4 * Real.exp (L ^ 2)) * CQ * CW *
          (Real.exp (-(2 / 25) * z.re ^ 2) * Real.exp (Real.pi * |z.re|)) := by ring
    _ ≤ Real.exp 1 * (4 * Real.exp (L ^ 2)) * CQ * CW * (Real.exp 56 * Real.exp (-|z.re|)) :=
        mul_le_mul_of_nonneg_left h4 (by positivity)
    _ = _ := by ring

/-! ## The pairing inequality -/

theorem mixTest_ofReal (L : ℝ) {Q : ℂ → ℂ} {q : ℝ → ℝ} (hQq : ∀ t : ℝ, Q t = q t) (t : ℝ) :
    mixTest L Q t = ((mixWindowReal L t * q t *
      ((2 / (1 / 4 + t ^ 2)) ^ 2 / Complex.normSq (Complex.Gammaℝ (linePt t))) : ℝ) : ℂ) := by
  unfold mixTest
  rw [mixWindow_ofReal, hQq, gammaWeightC_ofReal, gammaWeightInv_eq_ofReal]
  push_cast
  ring

theorem mixWindow_mul_gammaWeight (L : ℝ) {Q : ℂ → ℂ} {q : ℝ → ℝ} (hQq : ∀ t : ℝ, Q t = q t)
    (t : ℝ) : XiC (t : ℂ) ^ 2 * mixTest L Q t = mixWindow L t * (q t : ℂ) * zetaSq t := by
  unfold mixTest
  rw [hQq, gammaWeightC_ofReal, ← XiC_sq_mul_gammaWeightInv]
  ring

theorem fourier_riemannXi_sq_mul_mixTest (L : ℝ) {Q : ℂ → ℂ} {q : ℝ → ℝ}
    (hQq : ∀ t : ℝ, Q t = q t) (y : ℝ) :
    𝓕 (fun ξ : ℝ => RHTower.WeilExcess.riemannXi ξ ^ 2 * mixTest L Q ((2 * Real.pi * ξ : ℝ) : ℂ))
        y = ((1 / (2 * Real.pi) : ℝ) : ℂ) * mixMoment L q y := by
  rw [RHTower.WeilExcess.fourier_eq_integral]
  set f : ℝ → ℂ := fun t => mixWindow L t * (q t : ℂ) * zetaSq t * Complex.exp (-(y * t) * I)
    with hf
  have e : (fun ξ : ℝ => Complex.exp (-(2 * Real.pi * ξ * y : ℝ) * I) *
      (RHTower.WeilExcess.riemannXi ξ ^ 2 * mixTest L Q ((2 * Real.pi * ξ : ℝ) : ℂ))) =
      fun ξ : ℝ => f (2 * Real.pi * ξ) := by
    funext ξ
    rw [RHTower.WeilExcess.riemannXi_eq_XiC,
      show (2 * Real.pi * ξ : ℂ) = ((2 * Real.pi * ξ : ℝ) : ℂ) by push_cast; ring,
      mixWindow_mul_gammaWeight L hQq, hf]
    simp only
    rw [show -((2 * Real.pi * ξ * y : ℝ) : ℂ) * I = -((y : ℂ) * ((2 * Real.pi * ξ : ℝ) : ℂ)) * I by
      push_cast; ring]
    ring
  rw [e, Measure.integral_comp_mul_left f (2 * Real.pi), Complex.real_smul]
  congr 1
  rw [abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi)⁻¹), one_div]

theorem mixMoment_neg (L : ℝ) (q : ℝ → ℝ) (y : ℝ) :
    mixMoment L q (-y) = conj (mixMoment L q y) := by
  unfold mixMoment
  rw [← integral_conj]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  simp only [map_mul, mixWindow_ofReal, Complex.conj_ofReal, zetaSq_eq_normSq]
  rw [← Complex.exp_conj]
  congr 2
  simp

/-- **From the spectral pairing to the sign.** If the pairing identity holds for the mixed test, the
paired mixed moments are nonpositive: the right side `−∫ G dσ` has `G ≥ 0` on the real line. -/
theorem sum_mul_re_mixMoment_nonpos_of_pairing {v : ℕ → ℝ} (L : ℝ) {Q : ℂ → ℂ} {q : ℝ → ℝ}
    (hQq : ∀ t : ℝ, Q t = q t) (hq0 : ∀ t, 0 ≤ q t) (σ : Measure ℝ) [IsFiniteMeasure σ]
    (hGc : Continuous fun t : ℝ => mixTest L Q t) {CG : ℝ}
    (hGb1 : ∀ t : ℝ, ‖mixTest L Q t‖ ≤ CG)
    (hpair : ∑' n : ℕ, (v n : ℂ) *
        (𝓕 (fun ξ : ℝ => RHTower.WeilExcess.riemannXi ξ ^ 2 *
          mixTest L Q ((2 * Real.pi * ξ : ℝ) : ℂ)) (Real.log n) +
        𝓕 (fun ξ : ℝ => RHTower.WeilExcess.riemannXi ξ ^ 2 *
          mixTest L Q ((2 * Real.pi * ξ : ℝ) : ℂ)) (-Real.log n)) =
      -∫ t, mixTest L Q ((2 * Real.pi * (t / (2 * Real.pi)) : ℝ) : ℂ) ∂σ) :
    ∑' n : ℕ, v n * (mixMoment L q (Real.log n)).re ≤ 0 := by
  set k : ℝ := 1 / (2 * Real.pi) with hk
  have hk0 : 0 < k := by positivity
  have hF : ∀ y, 𝓕 (fun ξ : ℝ => RHTower.WeilExcess.riemannXi ξ ^ 2 *
      mixTest L Q ((2 * Real.pi * ξ : ℝ) : ℂ)) y = (k : ℂ) * mixMoment L q y :=
    fun y => fourier_riemannXi_sq_mul_mixTest L hQq y
  have hterm : ∀ n : ℕ, (v n : ℂ) *
      (𝓕 (fun ξ : ℝ => RHTower.WeilExcess.riemannXi ξ ^ 2 *
          mixTest L Q ((2 * Real.pi * ξ : ℝ) : ℂ)) (Real.log n) +
        𝓕 (fun ξ : ℝ => RHTower.WeilExcess.riemannXi ξ ^ 2 *
          mixTest L Q ((2 * Real.pi * ξ : ℝ) : ℂ)) (-Real.log n)) =
      ((2 * k * (v n * (mixMoment L q (Real.log n)).re) : ℝ) : ℂ) := by
    intro n
    rw [hF, hF, mixMoment_neg, ← mul_add, Complex.add_conj]
    push_cast
    ring
  rw [tsum_congr hterm, ← Complex.ofReal_tsum] at hpair
  have hre := congrArg Complex.re hpair
  rw [Complex.ofReal_re, Complex.neg_re] at hre
  have hGeq : (fun t => mixTest L Q ((2 * Real.pi * (t / (2 * Real.pi)) : ℝ) : ℂ)) =
      fun t : ℝ => mixTest L Q t := by
    funext t
    congr 2
    field_simp
  have hGi : Integrable (fun t : ℝ => mixTest L Q t) σ :=
    Integrable.of_bound hGc.aestronglyMeasurable CG (Eventually.of_forall hGb1)
  have hnn : 0 ≤ (∫ t, mixTest L Q ((2 * Real.pi * (t / (2 * Real.pi)) : ℝ) : ℂ) ∂σ).re := by
    have h := integral_re hGi
    simp only [RCLike.re_to_complex] at h
    rw [hGeq, ← h]
    refine integral_nonneg fun t => ?_
    rw [mixTest_ofReal L hQq, Complex.ofReal_re]
    exact mul_nonneg (mul_nonneg (mixWindowReal_nonneg L t) (hq0 t))
      (gammaWeightInv_real_pos t).le
  rw [tsum_mul_left] at hre
  have h2k : 0 < 2 * k := by positivity
  by_contra hpos
  push Not at hpos
  have : 0 < 2 * k * ∑' n : ℕ, v n * (mixMoment L q (Real.log n)).re := mul_pos h2k hpos
  linarith

/-- The mixed test is continuous and bounded on the real line. -/
theorem continuous_mixTest_ofReal (L : ℝ) {Q : ℂ → ℂ} (hQd : Differentiable ℂ Q) :
    Continuous fun t : ℝ => mixTest L Q t := by
  rw [continuous_iff_continuousAt]
  intro t
  exact (differentiableAt_mixTest L hQd (by simp)).continuousAt.comp
    Complex.continuous_ofReal.continuousAt

/-- **The pairing inequality for the mixed notch.** -/
theorem sum_mul_re_mixMoment_nonpos {v : ℕ → ℝ} (hv0 : v 0 = 0) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ n, |v n| ≤ 2 * Real.log n + A) {c : ℝ} (hc0 : 0 < c) (hc : c < 1 / 2)
    (hs : Summable fun n : ℕ => |v n| * (n : ℝ) ^ (-c))
    (hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ))
    (L : ℝ) {Q : ℂ → ℂ} (hQd : Differentiable ℂ Q) {CQ : ℝ}
    (hQb : ∀ z : ℂ, |z.im| ≤ c → ‖Q z‖ ≤ CQ) {q : ℝ → ℝ} (hQq : ∀ t : ℝ, Q t = q t)
    (hq0 : ∀ t, 0 ≤ q t) :
    ∑' n : ℕ, v n * (mixMoment L q (Real.log n)).re ≤ 0 := by
  have hcont := RHTower.WeilRegular.continuous_nullPotential_of_log hv0 hA ha
  obtain ⟨σ, hσf, hσ⟩ := exists_charFun_eq_of_positiveDefinite hPD
    (Complex.continuous_ofReal.comp hcont.neg)
  set G : ℂ → ℂ := mixTest L Q with hG
  set g : ℝ → ℂ := fun ξ => G ((2 * Real.pi * ξ : ℝ) : ℂ) with hg
  obtain ⟨CG, hCG0, hGb⟩ := exists_norm_mixTest_le L hc0.le hc hQb
  have hGd : ∀ z : ℂ, |z.im| ≤ c → DifferentiableAt ℂ G z := fun z hz =>
    differentiableAt_mixTest L hQd (by linarith)
  have hGc : Continuous fun t : ℝ => G t := continuous_mixTest_ofReal L hQd
  have hgc : Continuous g := hGc.comp (by fun_prop)
  have hgb : ∀ ξ : ℝ, ‖g ξ‖ ≤ CG * Real.exp (-(1 * |ξ|)) := by
    intro ξ
    have h := hGb ((2 * Real.pi * ξ : ℝ) : ℂ) (by simpa using hc0.le)
    rw [Complex.ofReal_re] at h
    refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hCG0)
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), one_mul]
    have := Real.pi_gt_three
    nlinarith [abs_nonneg ξ]
  have hgi : Integrable g :=
    ((integrable_exp_neg_mul_abs' one_pos).const_mul CG).mono' hgc.aestronglyMeasurable
      (Eventually.of_forall hgb)
  -- exponential decay of the transform
  set E : ℝ := ∫ x : ℝ, Real.exp (-(1 * |x|)) with hE
  have hE0 : 0 ≤ E := integral_nonneg fun _ => (Real.exp_pos _).le
  have hdec : ∀ w, ‖𝓕 g w‖ ≤ ((2 * Real.pi)⁻¹ * (CG * E)) * Real.exp (-(c * |w|)) := by
    intro w
    rw [RHTower.WeilExcess.fourier_eq_integral]
    set h : ℝ → ℂ := fun t => G t * Complex.exp (-(w * t) * I) with hh
    have e : (fun ξ : ℝ => Complex.exp (-(2 * Real.pi * ξ * w : ℝ) * I) * g ξ) =
        fun ξ : ℝ => h (2 * Real.pi * ξ) := by
      funext ξ
      rw [hh, hg]
      simp only
      rw [show -((2 * Real.pi * ξ * w : ℝ) : ℂ) * I = -((w : ℂ) * ((2 * Real.pi * ξ : ℝ) : ℂ)) * I by
        push_cast; ring]
      ring
    rw [e, Measure.integral_comp_mul_left h (2 * Real.pi), norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0 : ℝ) < |(2 * Real.pi)⁻¹|),
      abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi)⁻¹)]
    have hb := norm_integral_mul_cexp_le_of_strip hc0.le hGd hGb w
    calc (2 * Real.pi)⁻¹ * ‖∫ t, h t‖ ≤ (2 * Real.pi)⁻¹ * (CG * E * Real.exp (-(c * |w|))) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by ring
  have hGb1 : ∀ t : ℝ, ‖G t‖ ≤ CG := fun t => by
    have h := hGb t (by simpa using hc0.le)
    exact h.trans (mul_le_of_le_one_right hCG0 (Real.exp_le_one_iff.mpr (by
      simp only [Complex.ofReal_re]; linarith [abs_nonneg t])))
  exact sum_mul_re_mixMoment_nonpos_of_pairing L hQq hq0 σ hGc hGb1
    (RHTower.WeilRegular.nullPotential_pairing_exp hv0 hc0 (by linarith) hs σ hσ hgc hgi hdec)

/-! ## The analytic tail -/

/-- **Transform bound on the lower line.** If `G` is holomorphic on `|Im z| ≤ c` with real-direction
decay, and `‖G(x − ic)‖ ≤ m(x)` with `m` integrable, then
`‖∫ G(x) e^{−ivx} dx‖ ≤ e^{−cv} ∫ m`. -/
theorem norm_integral_mul_cexp_le_lower {G : ℂ → ℂ} {c C : ℝ} (hc : 0 ≤ c)
    (hG : ∀ z : ℂ, |z.im| ≤ c → DifferentiableAt ℂ G z)
    (hbound : ∀ z : ℂ, |z.im| ≤ c → ‖G z‖ ≤ C * Real.exp (-|z.re|)) (v : ℝ)
    {m : ℝ → ℝ} (hm : Integrable m) (hGm : ∀ x : ℝ, ‖G ((x : ℂ) - (c : ℂ) * I)‖ ≤ m x) :
    ‖∫ x : ℝ, G x * Complex.exp (-(v * x) * I)‖ ≤ Real.exp (-(c * v)) * ∫ x, m x := by
  set F : ℂ → ℂ := fun z => G z * Complex.exp (-((v : ℂ) * z) * I) with hFdef
  have hFd : ∀ z : ℂ, |z.im| ≤ c → DifferentiableAt ℂ F z := fun z hz =>
    (hG z hz).mul (by fun_prop)
  have hnormF : ∀ z : ℂ, ‖F z‖ = ‖G z‖ * Real.exp (v * z.im) := by
    intro z
    rw [hFdef, norm_mul, Complex.norm_exp, re_neg_mul_mul_I]
  have hFb : ∀ z : ℂ, |z.im| ≤ c →
      ‖F z‖ ≤ (C * Real.exp (|v| * c)) * Real.exp (-(1 * |z.re|)) := by
    intro z hz
    rw [hnormF, one_mul]
    have hvz : v * z.im ≤ |v| * c := by
      calc v * z.im ≤ |v * z.im| := le_abs_self _
        _ = |v| * |z.im| := abs_mul _ _
        _ ≤ |v| * c := mul_le_mul_of_nonneg_left hz (abs_nonneg _)
    calc ‖G z‖ * Real.exp (v * z.im) ≤ (C * Real.exp (-|z.re|)) * Real.exp (|v| * c) :=
          mul_le_mul (hbound z hz) (Real.exp_le_exp.mpr hvz) (Real.exp_pos _).le
            ((norm_nonneg _).trans (hbound z hz))
      _ = C * Real.exp (|v| * c) * Real.exp (-|z.re|) := by ring
  have hid : (∫ x : ℝ, G x * Complex.exp (-(v * x) * I)) = ∫ x : ℝ, F (x : ℂ) := rfl
  rw [hid, ← integral_horizontal_shift_lower hc one_pos hFd hFb, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hm.const_mul _) (Eventually.of_forall fun x => ?_)
  rw [hnormF]
  have him : ((x : ℂ) - (c : ℂ) * I).im = -c := by simp
  rw [him, mul_comm (Real.exp _)]
  have hvc : v * -c = -(c * v) := by ring
  rw [hvc]
  exact mul_le_mul_of_nonneg_right (hGm x) (Real.exp_pos _).le

theorem one_add_abs_sq_le_exp (x : ℝ) : (1 + |x|) ^ 2 ≤ Real.exp (Real.pi * |x|) := by
  have h1 : 1 + |x| ≤ Real.exp |x| := by linarith [Real.add_one_le_exp |x|]
  have h2 : (1 + |x|) ^ 2 ≤ Real.exp |x| ^ 2 := pow_le_pow_left₀ (by positivity) h1 2
  have h3 : Real.exp |x| ^ 2 = Real.exp (2 * |x|) := by rw [← Real.exp_nat_mul]; ring_nf
  have h4 : Real.exp (2 * |x|) ≤ Real.exp (Real.pi * |x|) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith [Real.pi_gt_three]) (abs_nonneg x))
  linarith

/-- **The analytic tail**: `‖M_Ω(y)‖ ≤ C (1 + L²) e^{−cy}` for `L, y ≥ 0`. -/
theorem exists_norm_mixMoment_le {c : ℝ} (hc0 : 0 ≤ c) (hc : c < 1 / 2) {Q : ℂ → ℂ}
    (hQd : Differentiable ℂ Q) {CQ : ℝ} (hQb : ∀ z : ℂ, |z.im| ≤ c → ‖Q z‖ ≤ CQ) {q : ℝ → ℝ}
    (hQq : ∀ t : ℝ, Q t = q t) :
    ∃ C, 0 ≤ C ∧ ∀ L : ℝ, 0 ≤ L → ∀ y : ℝ, 0 ≤ y →
      ‖mixMoment L q y‖ ≤ C * (1 + L ^ 2) * Real.exp (-(c * y)) := by
  obtain ⟨CZ, hCZ0, hCZ⟩ := exists_norm_zetaPairC_le hc
  obtain ⟨CI, hCI0, hCI⟩ := exists_integral_mixWindowReal_mul_sq_le
  have hCQ0 : 0 ≤ CQ := (norm_nonneg _).trans (hQb 0 (by simpa using hc0))
  refine ⟨Real.exp (4 * c ^ 2) * CQ * CZ * CI, by positivity, fun L hL y hy => ?_⟩
  set F : ℂ → ℂ := fun z => mixWindow L z * Q z * zetaPairC z with hFdef
  have hFd : ∀ z : ℂ, |z.im| ≤ c → DifferentiableAt ℂ F z := fun z hz =>
    (((differentiable_mixWindow L) z).mul (hQd z)).mul (differentiableAt_zetaPairC (by linarith))
  have hFb : ∀ z : ℂ, |z.im| ≤ c → ‖F z‖ ≤
      (Real.exp 1 * (4 * Real.exp (L ^ 2)) * CQ * CZ * Real.exp 56) * Real.exp (-|z.re|) := by
    intro z hz
    have h1 := norm_mixWindow_le_gauss L (z := z) (by linarith)
    have h2 := hQb z hz
    have h3 := (hCZ z hz).trans (mul_le_mul_of_nonneg_left (one_add_abs_sq_le_exp z.re) hCZ0)
    have h4 := gauss_mul_exp_pi_le z.re
    rw [hFdef]
    simp only
    rw [norm_mul, norm_mul]
    calc ‖mixWindow L z‖ * ‖Q z‖ * ‖zetaPairC z‖
        ≤ (Real.exp 1 * (4 * (Real.exp (L ^ 2) * Real.exp (-(2 / 25) * z.re ^ 2)))) * CQ *
            (CZ * Real.exp (Real.pi * |z.re|)) :=
          mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h3 (norm_nonneg _)
            (by positivity)
      _ = Real.exp 1 * (4 * Real.exp (L ^ 2)) * CQ * CZ *
            (Real.exp (-(2 / 25) * z.re ^ 2) * Real.exp (Real.pi * |z.re|)) := by ring
      _ ≤ Real.exp 1 * (4 * Real.exp (L ^ 2)) * CQ * CZ * (Real.exp 56 * Real.exp (-|z.re|)) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = _ := by ring
  set m : ℝ → ℝ := fun x => Real.exp (4 * c ^ 2) * CQ * CZ * (mixWindowReal L x * (1 + |x|) ^ 2)
    with hm
  have hmi : Integrable m := (integrable_mixWindowReal_mul_sq L).const_mul _
  have hFm : ∀ x : ℝ, ‖F ((x : ℂ) - (c : ℂ) * I)‖ ≤ m x := by
    intro x
    set z : ℂ := (x : ℂ) - (c : ℂ) * I with hz
    have hzre : z.re = x := by simp [hz]
    have hzim : z.im = -c := by simp [hz]
    have hzc : |z.im| ≤ c := by rw [hzim, abs_neg, abs_of_nonneg hc0]
    have h1 := norm_mixWindow_le_line L z
    rw [hzre, hzim, neg_sq] at h1
    have h2 := hQb z hzc
    have h3 := hCZ z hzc
    rw [hzre] at h3
    rw [hFdef]
    simp only
    rw [norm_mul, norm_mul, hm]
    simp only
    calc ‖mixWindow L z‖ * ‖Q z‖ * ‖zetaPairC z‖
        ≤ (Real.exp (4 * c ^ 2) * mixWindowReal L x) * CQ * (CZ * (1 + |x|) ^ 2) :=
          mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _)
            (mul_nonneg (Real.exp_pos _).le (mixWindowReal_nonneg _ _))) h3 (norm_nonneg _)
            (mul_nonneg (mul_nonneg (Real.exp_pos _).le (mixWindowReal_nonneg _ _)) hCQ0)
      _ = _ := by ring
  have hmm : mixMoment L q y = ∫ x : ℝ, F x * Complex.exp (-(y * x) * I) := by
    unfold mixMoment
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    rw [hFdef]
    simp only
    rw [hQq, zetaPairC_ofReal]
  rw [hmm]
  have h := norm_integral_mul_cexp_le_lower hc0 hFd hFb y hmi hFm
  have hint : ∫ x, m x ≤ Real.exp (4 * c ^ 2) * CQ * CZ * (CI * (1 + L ^ 2)) := by
    rw [hm, integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hCI L hL) (by positivity)
  calc ‖∫ x : ℝ, F x * Complex.exp (-(y * x) * I)‖ ≤ Real.exp (-(c * y)) * ∫ x, m x := h
    _ ≤ Real.exp (-(c * y)) * (Real.exp (4 * c ^ 2) * CQ * CZ * (CI * (1 + L ^ 2))) :=
        mul_le_mul_of_nonneg_left hint (Real.exp_pos _).le
    _ = _ := by ring

/-! ## The scale split -/

/-- The negative half-line part of the mixed moment. -/
def mixMomentNeg (L : ℝ) (q : ℝ → ℝ) (y : ℝ) : ℂ :=
  ∫ t in Iic 0, (mixWindowReal L t : ℂ) * (q t : ℂ) * zetaSq t * Complex.exp (-(y * t) * I)

theorem exists_norm_zetaSq_le : ∃ C, 0 ≤ C ∧ ∀ t : ℝ, ‖zetaSq t‖ ≤ C * (1 + |t|) ^ 2 := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_zetaPairC_le (c := 0) (by norm_num)
  refine ⟨C, hC0, fun t => ?_⟩
  have h := hC (t : ℂ) (by simp)
  rwa [zetaPairC_ofReal, Complex.ofReal_re] at h

/-- The scale integrand of the moment. -/
theorem norm_momentIntegrand_le {q : ℝ → ℝ} {CQ CZ : ℝ} (hqb : ∀ t, |q t| ≤ CQ)
    (hCZ : ∀ t : ℝ, ‖zetaSq t‖ ≤ CZ * (1 + |t|) ^ 2) (y t : ℝ) :
    ‖(q t : ℂ) * zetaSq t * Complex.exp (-(y * t) * I)‖ ≤ CQ * CZ * (1 + |t|) ^ 2 := by
  have hCQ0 : 0 ≤ CQ := (abs_nonneg _).trans (hqb 0)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    show -((y : ℂ) * t) * I = ((-(y * t) : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one]
  calc |q t| * ‖zetaSq t‖ ≤ CQ * (CZ * (1 + |t|) ^ 2) :=
        mul_le_mul (hqb t) (hCZ t) (norm_nonneg _) hCQ0
    _ = CQ * CZ * (1 + |t|) ^ 2 := by ring

theorem continuous_momentIntegrand {q : ℝ → ℝ} (hqc : Continuous q) (y : ℝ) :
    Continuous fun t : ℝ => (q t : ℂ) * zetaSq t * Complex.exp (-(y * t) * I) :=
  ((Complex.continuous_ofReal.comp hqc).mul (contDiff_zetaSq 0).continuous).mul (by fun_prop)

/-- **The scale split**: `M_Ω(y) = ∫_0^∞ ρ_L(u) u^{−1} M_u(y) du + M_Ω^{−}(y)`. -/
theorem mixMoment_eq (L : ℝ) {q : ℝ → ℝ} (hqc : Continuous q) {CQ : ℝ}
    (hqb : ∀ t, |q t| ≤ CQ) (y : ℝ) :
    mixMoment L q y = (∫ u in Ioi 0, ((scaleWeight L u / u : ℝ) : ℂ) * weightedMoment u q y) +
      mixMomentNeg L q y := by
  obtain ⟨CZ, hCZ0, hCZ⟩ := exists_norm_zetaSq_le
  have hCQ0 : 0 ≤ CQ := (abs_nonneg _).trans (hqb 0)
  set F : ℝ → ℂ := fun t => (q t : ℂ) * zetaSq t * Complex.exp (-(y * t) * I) with hFdef
  have hFc : Continuous F := continuous_momentIntegrand hqc y
  have hFb : ∀ t, ‖F t‖ ≤ CQ * CZ * (1 + |t|) ^ 2 := norm_momentIntegrand_le hqb hCZ y
  have hform : ∀ t : ℝ, mixWindow L t * (q t : ℂ) * zetaSq t * Complex.exp (-(y * t) * I) =
      (mixWindowReal L t : ℂ) * F t := by
    intro t
    rw [mixWindow_ofReal, hFdef]
    ring
  have hint : Integrable fun t : ℝ => (mixWindowReal L t : ℂ) * F t := by
    refine ((integrable_mixWindowReal_mul_sq L).const_mul (CQ * CZ)).mono'
      ((Complex.continuous_ofReal.comp (continuous_mixWindowReal L)).mul hFc).aestronglyMeasurable
      (Eventually.of_forall fun t => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mixWindowReal_nonneg L t)]
    calc mixWindowReal L t * ‖F t‖ ≤ mixWindowReal L t * (CQ * CZ * (1 + |t|) ^ 2) :=
          mul_le_mul_of_nonneg_left (hFb t) (mixWindowReal_nonneg L t)
      _ = CQ * CZ * (mixWindowReal L t * (1 + |t|) ^ 2) := by ring
  unfold mixMoment mixMomentNeg
  simp_rw [hform]
  rw [← integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hint, compl_Ioi,
    integral_Ioi_mixWindowReal_mul L hFc hFb]
  congr 1
  · refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    unfold weightedMoment
    simp only [hFdef]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    ring
  · refine setIntegral_congr_fun measurableSet_Iic fun t _ => ?_
    simp only [hFdef]
    ring

/-- **The negative half-line is `O(e^{−L²})`.** -/
theorem exists_norm_mixMomentNeg_le {q : ℝ → ℝ} {CQ : ℝ} (hqb : ∀ t, |q t| ≤ CQ) :
    ∃ C, 0 ≤ C ∧ ∀ L : ℝ, 0 ≤ L → ∀ y : ℝ, ‖mixMomentNeg L q y‖ ≤ C * Real.exp (-L ^ 2) := by
  obtain ⟨CZ, hCZ0, hCZ⟩ := exists_norm_zetaSq_le
  obtain ⟨CN, hCN0, hCN⟩ := exists_integral_Iic_mixWindowReal_mul_sq_le
  have hCQ0 : 0 ≤ CQ := (abs_nonneg _).trans (hqb 0)
  refine ⟨CQ * CZ * CN, by positivity, fun L hL y => ?_⟩
  unfold mixMomentNeg
  have hb : ∀ t, ‖(mixWindowReal L t : ℂ) * (q t : ℂ) * zetaSq t * Complex.exp (-(y * t) * I)‖ ≤
      CQ * CZ * (mixWindowReal L t * (1 + |t|) ^ 2) := by
    intro t
    have h := norm_momentIntegrand_le hqb hCZ y t
    rw [show (mixWindowReal L t : ℂ) * (q t : ℂ) * zetaSq t * Complex.exp (-(y * t) * I) =
      (mixWindowReal L t : ℂ) * ((q t : ℂ) * zetaSq t * Complex.exp (-(y * t) * I)) by ring,
      norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mixWindowReal_nonneg L t)]
    calc mixWindowReal L t * ‖(q t : ℂ) * zetaSq t * Complex.exp (-(y * t) * I)‖
        ≤ mixWindowReal L t * (CQ * CZ * (1 + |t|) ^ 2) :=
          mul_le_mul_of_nonneg_left h (mixWindowReal_nonneg L t)
      _ = _ := by ring
  calc ‖∫ t in Iic 0, (mixWindowReal L t : ℂ) * (q t : ℂ) * zetaSq t * Complex.exp (-(y * t) * I)‖
      ≤ ∫ t in Iic 0, CQ * CZ * (mixWindowReal L t * (1 + |t|) ^ 2) :=
        norm_integral_le_of_norm_le ((integrable_mixWindowReal_mul_sq L).const_mul _).integrableOn
          (Eventually.of_forall hb)
    _ = CQ * CZ * ∫ t in Iic 0, mixWindowReal L t * (1 + |t|) ^ 2 := integral_const_mul _ _
    _ ≤ CQ * CZ * (CN * Real.exp (-L ^ 2)) :=
        mul_le_mul_of_nonneg_left (hCN L hL) (by positivity)
    _ = _ := by ring

end RHTower.ZetaNotch
