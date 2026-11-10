import GaloisForLFunctions.SelectiveArithmetic.ThePolarPacketsOfAWindow
import GaloisForLFunctions.RHTower.IsolatedDeepZeroWeilDetection
import GaloisForLFunctions.RHTower.DigammaVerticalLogGrowth
import GaloisForLFunctions.RHTower.BlindDecayClassPoleCertificate
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz

/-!
# The height of a packet is a mass

The conductor of a character enters the form of its system as the mass `log q`. The height of a
packet is a second mass. On a packet `f` supported in `[−a, a]` and modulated to the height `t`,
`F(u) = e^{−itu} f(u)`, the transform is the transform of `f` moved to `t`, and the archimedean
symbol there is `log(2 + |t|) + O(1)`.

* **The archimedean energy at a height** (`integral_arch_modulated_ge`):
  `(1/2π) ∫ |F̂|² S_∞ ≥ (log(2 + |t|) − A₁) ∫ f² − ∫ f'²`. The symbol is at least
  `log(2 + |τ|) − c₀`, and `(τ − t)² |F̂(τ)|²` is the transform of the modulated derivative.
* **The form of a dominated system at a height** (`systemForm_modulated_ge`):
  `𝔚_{w,q}(F) ≥ (log q + log(2 + |t|) − A₁ − K e^{a} − B − (1 + 2a)²) ∫ f² − ∫ f'²`: conductor
  and height add up to one mass, the logarithm of the analytic conductor.
* **The pole plane does not reach a height** (`re_weilPoleTerm_modulated_ge`): for
  `e^{a} ≤ |t|` the pole term of the modulated packet is at least `−4 ∫ f'²`; one integration by
  parts at the points `±i/2 − t`.
* **Weil's form at a height** (`re_weilFullFunctional_modulated_ge`, `exists_height_margin`): for
  every dominated system with pole plane, in particular for `ζ`, and every `η > 0`: at every
  height with `|t|` large and every aperture `a ≤ log log |t| − η`,
  `Re W_w(F ⋆ F̃) ≥ ½ (1 − e^{−η/2}) log |t| ∫ f² − 5 ∫ f'²`.

So Weil's form of `ζ` is positive at every large height on packets of bounded shape
(`∫ f'² ≤ M ∫ f²`) up to the aperture `log log |t| − o(1)`, for the reason that pays every
dominated system. In the aspect of the height the trivial aperture is `log log |t|`.
-/

open Filter Topology MeasureTheory Set
open Zeta23
open scoped ArithmeticFunction.vonMangoldt Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SelectiveArithmetic

open AbsoluteGeometryOfSpecZ

/-! ### Modulated packets -/

theorem norm_modulatedTest (t : ℝ) (f : ℝ → ℝ) (u : ℝ) :
    ‖_root_.RHTower.modulatedTest t f u‖ = |f u| := by
  unfold _root_.RHTower.modulatedTest
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
  have h : (-(Complex.I * (t : ℂ) * (u : ℂ))).re = 0 := by simp
  rw [h, Real.exp_zero, one_mul]

theorem integral_norm_modulatedTest_sq (t : ℝ) (f : ℝ → ℝ) :
    ∫ u, ‖_root_.RHTower.modulatedTest t f u‖ ^ 2 = ∫ u, f u ^ 2 :=
  integral_congr_ae (Eventually.of_forall fun u => by
    show ‖_root_.RHTower.modulatedTest t f u‖ ^ 2 = f u ^ 2
    rw [norm_modulatedTest, sq_abs])

/-- Modulation moves the transform: `F̂(z) = f̂(z − t)`. -/
theorem paperFT_modulatedTest (t : ℝ) (f : ℝ → ℝ) (z : ℂ) :
    paperFT (_root_.RHTower.modulatedTest t f) z = paperFT (fun u => (f u : ℂ)) (z - t) :=
  _root_.RHTower.paperFT_modulate (fun u => (f u : ℂ)) t z

theorem abs_le_of_ne_zero {f : ℝ → ℝ} {a : ℝ} (h0 : ∀ u, a ≤ |u| → f u = 0) (u : ℝ)
    (hu : f u ≠ 0) : |u| ≤ a :=
  le_of_lt (lt_of_not_ge fun h => hu (h0 u h))

/-- The derivative of a `C³` packet is a `C²` packet. -/
theorem contDiff_two_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f) : ContDiff ℝ 2 (deriv f) := by
  have h : ContDiff ℝ (2 + 1) f := by
    have e : ((2 : WithTop ℕ∞) + 1) = 3 := by norm_num
    rw [e]
    exact hf
  exact (contDiff_succ_iff_deriv.mp h).2.2

theorem deriv_abs_le_of_ne_zero {f : ℝ → ℝ} {a : ℝ} (h0 : ∀ u, a ≤ |u| → f u = 0) (u : ℝ)
    (hu : deriv f u ≠ 0) : |u| ≤ a :=
  le_of_not_gt fun h => hu (deriv_eq_zero_of_abs_gt h0 h)

/-- The transform of the modulated derivative: `(τ − t)` times the transform of the modulated
packet, up to the factor `−i`. -/
theorem paperFT_modulatedTest_deriv {a : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (h0 : ∀ u, a ≤ |u| → f u = 0) (t : ℝ) (z : ℂ) :
    paperFT (_root_.RHTower.modulatedTest t (deriv f)) z =
      -(Complex.I * (z - t)) * paperFT (_root_.RHTower.modulatedTest t f) z := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hG : ContDiff ℝ 1 fun u => (f u : ℂ) := (contDiff_ofReal_packet hf2).of_le (by norm_num)
  have hGc : HasCompactSupport fun u => (f u : ℂ) :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _)
      (tsupport_ofReal_subset_of_eq_zero h0)
  have hderiv : deriv (fun u => (f u : ℂ)) = fun u => ((deriv f u : ℝ) : ℂ) := by
    funext u
    exact ((hf2.differentiable (by norm_num) u).hasDerivAt.ofReal_comp).deriv
  rw [paperFT_modulatedTest, paperFT_modulatedTest, ← hderiv,
    _root_.RHTower.EvenSector.paperFT_deriv_of_compact hG hGc]

/-! ### The archimedean symbol grows with the height -/

/-- The constant of the archimedean energy at a height. -/
def archGrowthConstant : ℝ :=
  _root_.RHTower.digammaVerticalCoercivityConst (1 / 4) + Real.log 2 + Real.log π + 1

/-- `S_∞(τ) ≥ log(2 + |τ|) − c₀`. -/
theorem log_sub_le_archimedeanWeilSymbol (τ : ℝ) :
    Real.log (2 + |τ|) -
        (_root_.RHTower.digammaVerticalCoercivityConst (1 / 4) + Real.log 2 + Real.log π) ≤
      _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π)) := by
  have hd := _root_.RHTower.re_digamma_vertical_ge (a := 1 / 4) (by norm_num) (by norm_num)
    (τ / 2)
  have hl : Real.log (2 + |τ|) ≤ Real.log 2 + Real.log (2 + |τ / 2|) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    apply Real.log_le_log (by positivity)
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    linarith [abs_nonneg τ]
  rw [_root_.RHTower.archimedeanWeilSymbol_eq]
  have he : π * (τ / (2 * π)) = τ / 2 := by field_simp
  rw [he]
  linarith

/-- Moving the height by `τ − t` costs at most `1 + (τ − t)²`. -/
theorem log_two_add_abs_le (τ t : ℝ) :
    Real.log (2 + |t|) ≤ Real.log (2 + |τ|) + 1 + (τ - t) ^ 2 := by
  have htri : |t| ≤ |τ| + |τ - t| := by
    have h := abs_sub τ (τ - t)
    rwa [sub_sub_cancel] at h
  have hprod : 2 + |t| ≤ (2 + |τ|) * (1 + |τ - t|) := by
    nlinarith [abs_nonneg τ, abs_nonneg (τ - t), mul_nonneg (abs_nonneg τ) (abs_nonneg (τ - t))]
  have h1 : Real.log (2 + |t|) ≤ Real.log (2 + |τ|) + Real.log (1 + |τ - t|) := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by positivity) hprod
  have h2 : Real.log (1 + |τ - t|) ≤ |τ - t| := by
    have := Real.log_le_sub_one_of_pos (by positivity : (0 : ℝ) < 1 + |τ - t|)
    linarith
  have h3 : |τ - t| ≤ 1 + (τ - t) ^ 2 := by
    nlinarith [sq_nonneg (|τ - t| - 1), sq_abs (τ - t), abs_nonneg (τ - t)]
  linarith

/-- **The archimedean energy at a height.** For a `C³` packet `f` vanishing off `(−a, a)` and
every height `t`: `(1/2π) ∫ |F̂|² S_∞ ≥ (log(2 + |t|) − A₁) ∫ f² − ∫ f'²`. -/
theorem integral_arch_modulated_ge {a : ℝ} {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (h0 : ∀ u, a ≤ |u| → f u = 0) (t : ℝ) :
    (Real.log (2 + |t|) - archGrowthConstant) * (∫ u, f u ^ 2) - ∫ u, deriv f u ^ 2 ≤
      1 / (2 * π) * ∫ τ : ℝ, ‖paperFT (_root_.RHTower.modulatedTest t f) τ‖ ^ 2 *
        _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π)) := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hF := _root_.RHTower.modulatedTest_contDiff t hf2
  have hFs := _root_.RHTower.tsupport_modulatedTest_subset t (abs_le_of_ne_zero h0)
  have hG := _root_.RHTower.modulatedTest_contDiff t (contDiff_two_deriv hf)
  have hGs := _root_.RHTower.tsupport_modulatedTest_subset t (deriv_abs_le_of_ne_zero h0)
  have hI := _root_.RHTower.integrable_normSq_paperFT hF hFs
  have hI' := _root_.RHTower.integrable_normSq_paperFT hG hGs
  set L := Real.log (2 + |t|) - archGrowthConstant with hL
  have hnorm : ∀ τ : ℝ, ‖paperFT (_root_.RHTower.modulatedTest t (deriv f)) τ‖ ^ 2 =
      (τ - t) ^ 2 * ‖paperFT (_root_.RHTower.modulatedTest t f) τ‖ ^ 2 := fun τ => by
    rw [paperFT_modulatedTest_deriv hf h0, norm_mul, mul_pow, norm_neg, norm_mul,
      Complex.norm_I, one_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hmono : ∫ τ : ℝ, (L * ‖paperFT (_root_.RHTower.modulatedTest t f) τ‖ ^ 2 -
        ‖paperFT (_root_.RHTower.modulatedTest t (deriv f)) τ‖ ^ 2) ≤
      ∫ τ : ℝ, ‖paperFT (_root_.RHTower.modulatedTest t f) τ‖ ^ 2 *
        _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π)) := by
    refine integral_mono ((hI.const_mul L).sub hI')
      (_root_.RHTower.integrable_normSq_paperFT_mul_arch hF hFs) fun τ => ?_
    show L * ‖paperFT (_root_.RHTower.modulatedTest t f) τ‖ ^ 2 -
        ‖paperFT (_root_.RHTower.modulatedTest t (deriv f)) τ‖ ^ 2 ≤
      ‖paperFT (_root_.RHTower.modulatedTest t f) τ‖ ^ 2 *
        _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π))
    rw [hnorm]
    have h1 := log_sub_le_archimedeanWeilSymbol τ
    have h2 := log_two_add_abs_le τ t
    have h3 : L - (τ - t) ^ 2 ≤ _root_.RHTower.archimedeanWeilSymbol (τ / (2 * π)) := by
      rw [hL, archGrowthConstant]
      linarith
    nlinarith [mul_le_mul_of_nonneg_left h3
      (sq_nonneg ‖paperFT (_root_.RHTower.modulatedTest t f) τ‖)]
  rw [integral_sub (hI.const_mul L) hI', integral_const_mul,
    _root_.RHTower.integral_norm_paperFT_sq hF hFs,
    _root_.RHTower.integral_norm_paperFT_sq hG hGs, integral_norm_modulatedTest_sq,
    integral_norm_modulatedTest_sq] at hmono
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have h1 := mul_le_mul_of_nonneg_left hmono (by positivity : (0 : ℝ) ≤ 1 / (2 * π))
  have e : 1 / (2 * π) * (L * (2 * π * ∫ u, f u ^ 2) - 2 * π * ∫ u, deriv f u ^ 2) =
      L * (∫ u, f u ^ 2) - ∫ u, deriv f u ^ 2 := by
    field_simp
  rwa [e] at h1

/-! ### The form of a dominated system at a height -/

/-- **Conductor and height add up to one mass.** If `ψ(x) ≤ Kx + B`, the form of a dominated
system with conductor `q` on a packet modulated to the height `t` is at least
`(log q + log(2 + |t|) − A₁ − K e^{a} − B − (1 + 2a)²) ∫ f² − ∫ f'²`. -/
theorem systemForm_modulated_ge {K B : ℝ}
    (hψ : ∀ x : ℝ, 0 ≤ x → Chebyshev.psi x ≤ K * x + B) {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 3 f) (h0 : ∀ u, a ≤ |u| → f u = 0) {w : ℕ → ℝ} (hw : Dominated w)
    (q t : ℝ) :
    (Real.log q + Real.log (2 + |t|) - archGrowthConstant - K * Real.exp a - B -
          (1 + 2 * a) ^ 2) * (∫ u, f u ^ 2) - ∫ u, deriv f u ^ 2 ≤
      systemForm w q a (_root_.RHTower.modulatedTest t f) := by
  have hF := _root_.RHTower.modulatedTest_contDiff t (hf.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
  have hFs := _root_.RHTower.tsupport_modulatedTest_subset t (abs_le_of_ne_zero h0)
  have h1 := integral_arch_modulated_ge hf h0 t
  have h2 := (abs_le.mp (abs_contactForm_le_of_psi hψ ha hF.continuous hFs hw
    ⌊Real.exp (2 * a)⌋₊)).2
  rw [integral_norm_modulatedTest_sq] at h2
  rw [systemForm_eq hF hFs, integral_norm_modulatedTest_sq]
  linarith

/-! ### The pole plane does not reach a height -/

/-- `(∫ |g|)² ≤ 2a ∫ g²` for a continuous function vanishing off `[−a, a]`. -/
theorem sq_integral_abs_le {g : ℝ → ℝ} (hg : Continuous g) {a : ℝ} (ha : 0 ≤ a)
    (h0 : ∀ u, a < |u| → g u = 0) : (∫ u, |g u|) ^ 2 ≤ 2 * a * ∫ u, g u ^ 2 := by
  have hgc : HasCompactSupport g :=
    HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun u hu => h0 u (by
      rw [mem_Icc, not_and_or, not_le, not_le] at hu
      rcases hu with h | h
      · exact lt_abs.mpr (Or.inr (by linarith))
      · exact lt_abs.mpr (Or.inl h))
  set ind : ℝ → ℝ := (Icc (-a) a).indicator fun _ => (1 : ℝ) with hind
  have hindsq : ∀ u, ind u ^ 2 = ind u := fun u => by
    by_cases hu : u ∈ Icc (-a) a
    · rw [hind, Set.indicator_of_mem hu, one_pow]
    · rw [hind, Set.indicator_of_notMem hu]
      norm_num
  have hindI : Integrable ind := by
    rw [hind]
    exact (continuous_const (y := (1 : ℝ))).integrableOn_Icc.integrable_indicator
      measurableSet_Icc
  have hmul : ∀ u, |g u| * ind u = |g u| := fun u => by
    by_cases hu : u ∈ Icc (-a) a
    · rw [hind, Set.indicator_of_mem hu, mul_one]
    · have : a < |u| := by
        rw [mem_Icc, not_and_or, not_le, not_le] at hu
        rcases hu with h | h
        · exact lt_abs.mpr (Or.inr (by linarith))
        · exact lt_abs.mpr (Or.inl h)
      rw [h0 u this, abs_zero, zero_mul]
  have hsqI : Integrable fun u => |g u| ^ 2 := by
    have e : (fun u => |g u| ^ 2) = fun u => g u * g u := by
      funext u
      rw [sq_abs, sq]
    rw [e]
    exact (hg.mul hg).integrable_of_hasCompactSupport hgc.mul_right
  have hcs := GaloisForLFunctions.HTGeometry.sq_integral_mul_le (μ := volume)
    (f := fun u => |g u|) (g := ind) hg.abs.aestronglyMeasurable hindI.aestronglyMeasurable hsqI
    (by simpa [hindsq] using hindI)
  have hindint : ∫ u, ind u = 2 * a := by
    rw [hind, integral_indicator_const _ measurableSet_Icc, measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith), smul_eq_mul]
    ring
  simp_rw [hmul, sq_abs, hindsq] at hcs
  rw [hindint] at hcs
  linarith

/-- **The pole term of a packet at a height.** For `e^{a} ≤ |t|` the pole term of the packet
modulated to the height `t` is at least `−4 ∫ f'²`. -/
theorem re_weilPoleTerm_modulated_ge {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℝ} (hf : ContDiff ℝ 3 f)
    (h0 : ∀ u, a ≤ |u| → f u = 0) {t : ℝ} (ht : Real.exp a ≤ |t|) :
    -(4 * ∫ u, deriv f u ^ 2) ≤
      (_root_.RHTower.weilPoleTerm (EF.weilTest (_root_.RHTower.modulatedTest t f)
        (_root_.RHTower.modulatedTest t f))).re := by
  have hf2 : ContDiff ℝ 2 f := hf.of_le (by norm_num)
  have hF := _root_.RHTower.modulatedTest_contDiff t hf2
  have hFs := _root_.RHTower.tsupport_modulatedTest_subset t (abs_le_of_ne_zero h0)
  have hFc : HasCompactSupport (_root_.RHTower.modulatedTest t f) :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hFs
  have hG := _root_.RHTower.modulatedTest_contDiff t (contDiff_two_deriv hf)
  have hGs := _root_.RHTower.tsupport_modulatedTest_subset t (deriv_abs_le_of_ne_zero h0)
  have hGc : HasCompactSupport (_root_.RHTower.modulatedTest t (deriv f)) :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hGs
  have hdc : Continuous (deriv f) := (contDiff_two_deriv hf).continuous
  have hd0 : ∀ u, a < |u| → deriv f u = 0 := fun u hu => deriv_eq_zero_of_abs_gt h0 hu
  have ht0 : 0 < |t| := (Real.exp_pos a).trans_le ht
  set D := ∫ u, deriv f u ^ 2 with hD
  have hD0 : 0 ≤ D := integral_nonneg fun _ => sq_nonneg _
  set J := ∫ u, |deriv f u| with hJ
  have hJ0 : 0 ≤ J := integral_nonneg fun _ => abs_nonneg _
  -- one integration by parts at a point of real part `−t` and imaginary part `±½`
  have hkey : ∀ z : ℂ, z.re = 0 → |z.im| ≤ 1 / 2 →
      ‖paperFT (_root_.RHTower.modulatedTest t f) z‖ * |t| ≤ Real.exp (a / 2) * J := by
    intro z hzre hzim
    have h1 := paperFT_modulatedTest_deriv hf h0 t z
    have h2 := _root_.RHTower.EvenSector.norm_paperFT_le_of_compact hG.continuous hGc
      (b := 1 / 2) (z := z) hzim
    have h3 : ∫ u, ‖_root_.RHTower.modulatedTest t (deriv f) u‖ * Real.exp (1 / 2 * |u|) ≤
        Real.exp (a / 2) * J := by
      rw [hJ, ← integral_const_mul]
      refine integral_mono_of_nonneg (Eventually.of_forall fun u => by positivity)
        ((hdc.abs.integrable_of_hasCompactSupport
          (HasCompactSupport.intro (isCompact_Icc (a := -a) (b := a)) fun u hu => by
            have : a < |u| := by
              rw [mem_Icc, not_and_or, not_le, not_le] at hu
              rcases hu with h | h
              · exact lt_abs.mpr (Or.inr (by linarith))
              · exact lt_abs.mpr (Or.inl h)
            rw [hd0 u this, abs_zero])).const_mul _) (Eventually.of_forall fun u => ?_)
      show ‖_root_.RHTower.modulatedTest t (deriv f) u‖ * Real.exp (1 / 2 * |u|) ≤
        Real.exp (a / 2) * |deriv f u|
      rw [norm_modulatedTest, mul_comm]
      by_cases hu : a < |u|
      · rw [hd0 u hu, abs_zero, mul_zero, mul_zero]
      · exact mul_le_mul_of_nonneg_right
          (Real.exp_le_exp.mpr (by linarith [not_lt.mp hu])) (abs_nonneg _)
    have hw : |t| ≤ ‖z - (t : ℂ)‖ := by
      have h := Complex.abs_re_le_norm (z - (t : ℂ))
      rwa [Complex.sub_re, hzre, Complex.ofReal_re, zero_sub, abs_neg] at h
    have hnorm : ‖paperFT (_root_.RHTower.modulatedTest t (deriv f)) z‖ =
        ‖z - (t : ℂ)‖ * ‖paperFT (_root_.RHTower.modulatedTest t f) z‖ := by
      rw [h1, norm_mul, norm_neg, norm_mul, Complex.norm_I, one_mul]
    calc ‖paperFT (_root_.RHTower.modulatedTest t f) z‖ * |t|
        ≤ ‖paperFT (_root_.RHTower.modulatedTest t f) z‖ * ‖z - (t : ℂ)‖ :=
          mul_le_mul_of_nonneg_left hw (norm_nonneg _)
      _ = ‖paperFT (_root_.RHTower.modulatedTest t (deriv f)) z‖ := by rw [hnorm, mul_comm]
      _ ≤ Real.exp (a / 2) * J := h2.trans h3
  have hA := hkey (Complex.I / 2) (by simp) (by simp)
  have hB := hkey (-Complex.I / 2) (by simp) (by
    simp
    rw [abs_le]
    constructor <;> norm_num)
  set A := paperFT (_root_.RHTower.modulatedTest t f) (Complex.I / 2) with hAdef
  set Bc := paperFT (_root_.RHTower.modulatedTest t f) (-Complex.I / 2) with hBdef
  -- Cauchy–Schwarz on the support
  have hJsq : J ^ 2 ≤ 2 * a * D := sq_integral_abs_le hdc ha hd0
  have hexp : Real.exp (a / 2) * Real.exp (a / 2) = Real.exp a := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hat : a * Real.exp a ≤ |t| * |t| :=
    mul_le_mul ((by linarith [Real.add_one_le_exp a] : a ≤ Real.exp a).trans ht) ht
      (Real.exp_pos a).le (abs_nonneg t)
  have hprod : ‖A‖ * ‖Bc‖ * (|t| * |t|) ≤ Real.exp a * J ^ 2 := by
    have h := mul_le_mul hA hB (mul_nonneg (norm_nonneg _) ht0.le)
      (mul_nonneg (Real.exp_pos _).le hJ0)
    calc ‖A‖ * ‖Bc‖ * (|t| * |t|) = ‖A‖ * |t| * (‖Bc‖ * |t|) := by ring
      _ ≤ Real.exp (a / 2) * J * (Real.exp (a / 2) * J) := h
      _ = Real.exp a * J ^ 2 := by rw [← hexp]; ring
  have hAB : ‖A‖ * ‖Bc‖ ≤ 2 * D := by
    have h1 : Real.exp a * J ^ 2 ≤ Real.exp a * (2 * a * D) :=
      mul_le_mul_of_nonneg_left hJsq (Real.exp_pos a).le
    have h2 : Real.exp a * (2 * a * D) ≤ 2 * D * (|t| * |t|) := by
      nlinarith [mul_le_mul_of_nonneg_right hat hD0]
    have h3 : ‖A‖ * ‖Bc‖ * (|t| * |t|) ≤ 2 * D * (|t| * |t|) := hprod.trans (h1.trans h2)
    exact le_of_mul_le_mul_right h3 (mul_pos ht0 ht0)
  have hre : -(‖A‖ * ‖Bc‖) ≤ (A * conj Bc).re := by
    have h := Complex.abs_re_le_norm (A * conj Bc)
    rw [norm_mul, Complex.norm_conj] at h
    exact neg_le_of_abs_le h
  rw [_root_.RHTower.WeilOneSided.weilPoleTerm_re_eq_two_re hF.continuous hFc]
  linarith

/-! ### Weil's form at a height -/

/-- **Weil's form of a dominated system with pole plane, at a height.** If `ψ(x) ≤ Kx + B` and
`e^{a} ≤ |t|`, then on a packet modulated to the height `t`
`Re W_w(F ⋆ F̃) ≥ (log(2 + |t|) − A₁ − K e^{a} − B − (1 + 2a)²) ∫ f² − 5 ∫ f'²`. -/
theorem re_weilFullFunctional_modulated_ge {K B : ℝ}
    (hψ : ∀ x : ℝ, 0 ≤ x → Chebyshev.psi x ≤ K * x + B) {a : ℝ} (ha : 0 ≤ a) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 3 f) (h0 : ∀ u, a ≤ |u| → f u = 0) {w : ℕ → ℝ} (hw : Dominated w)
    {t : ℝ} (ht : Real.exp a ≤ |t|) :
    (Real.log (2 + |t|) - archGrowthConstant - K * Real.exp a - B - (1 + 2 * a) ^ 2) *
          (∫ u, f u ^ 2) - 5 * ∫ u, deriv f u ^ 2 ≤
      (_root_.RHTower.weilFullFunctional w (EF.weilTest (_root_.RHTower.modulatedTest t f)
        (_root_.RHTower.modulatedTest t f))).re := by
  have hF := _root_.RHTower.modulatedTest_contDiff t (hf.of_le (by norm_num : (2 : WithTop ℕ∞) ≤ 3))
  have hFs := _root_.RHTower.tsupport_modulatedTest_subset t (abs_le_of_ne_zero h0)
  have hsys := systemForm_modulated_ge hψ ha hf h0 hw 1 t
  have hpole := re_weilPoleTerm_modulated_ge ha hf h0 ht
  have e : systemForm w 1 a (_root_.RHTower.modulatedTest t f) =
      1 / (2 * π) * ∫ τ : ℝ, ‖paperFT (_root_.RHTower.modulatedTest t f) τ‖ ^ 2 *
        _root_.RHTower.weilAtomSymbol w ⌊Real.exp (2 * a)⌋₊ (τ / (2 * π)) := by
    unfold systemForm
    simp only [Real.log_one, add_zero]
  rw [re_weilFullFunctional_eq_pole_add_symbol w hF hFs, ← e]
  rw [Real.log_one, zero_add] at hsys
  linarith

/-- **In the aspect of the height the trivial aperture is `log log |t|`.** For every `η > 0`
there is `T₀` such that at every height with `|t| ≥ T₀`, every aperture `a ≤ log log |t| − η`,
every dominated system with pole plane and every `C³` packet `f` vanishing off `(−a, a)`:
`Re W_w(F ⋆ F̃) ≥ ½ (1 − e^{−η/2}) log |t| ∫ f² − 5 ∫ f'²`, `F(u) = e^{−itu} f(u)`. -/
theorem exists_height_margin {η : ℝ} (hη : 0 < η) :
    ∃ T₀ : ℝ, ∀ t : ℝ, T₀ ≤ |t| → ∀ a : ℝ, 0 ≤ a → a ≤ Real.log (Real.log |t|) - η →
      ∀ {w : ℕ → ℝ}, Dominated w → ∀ {f : ℝ → ℝ}, ContDiff ℝ 3 f →
        (∀ u, a ≤ |u| → f u = 0) →
        (1 - Real.exp (-η / 2)) / 2 * Real.log |t| * (∫ u, f u ^ 2) - 5 * ∫ u, deriv f u ^ 2 ≤
          (_root_.RHTower.weilFullFunctional w (EF.weilTest (_root_.RHTower.modulatedTest t f)
            (_root_.RHTower.modulatedTest t f))).re := by
  have hδ : 0 < 1 - Real.exp (-η / 2) := by
    have : Real.exp (-η / 2) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
    rw [Real.exp_zero] at this
    linarith
  have hε : 0 < Real.exp (η / 2) - 1 := by
    have : Real.exp 0 < Real.exp (η / 2) := Real.exp_lt_exp.mpr (by linarith)
    rw [Real.exp_zero] at this
    linarith
  obtain ⟨B, hB⟩ := BiScaleUncertainty.exists_psi_le_linear hε
  obtain ⟨M₁, hM₁⟩ := eventually_atTop.mp
    (eventually_const_add_log_sq_le (half_pos hδ) (archGrowthConstant + B))
  refine ⟨Real.exp (max M₁ 1), fun t ht a ha0 ha w hw f hf h0 => ?_⟩
  have ht0 : 0 < |t| := (Real.exp_pos _).trans_le ht
  set x := Real.log |t| with hx
  have hxM : max M₁ 1 ≤ x := by
    rw [hx, ← Real.log_exp (max M₁ 1)]
    exact Real.log_le_log (Real.exp_pos _) ht
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hxM
  have hx0 : 0 < x := by linarith
  have ha' : a ≤ Real.log x := by linarith
  -- the prime side: `(1 + ε) e^{a} ≤ e^{−η/2} log |t|`
  have hexpa : Real.exp a ≤ x / Real.exp η := by
    have h1 : Real.exp a ≤ Real.exp (Real.log x - η) := Real.exp_le_exp.mpr ha
    rwa [Real.exp_sub, Real.exp_log hx0] at h1
  have hexp : (1 + (Real.exp (η / 2) - 1)) * Real.exp a ≤ Real.exp (-η / 2) * x := by
    have h2 : Real.exp (η / 2) * (x / Real.exp η) = Real.exp (-η / 2) * x := by
      rw [show -η / 2 = η / 2 - η by ring, Real.exp_sub]
      ring
    calc (1 + (Real.exp (η / 2) - 1)) * Real.exp a = Real.exp (η / 2) * Real.exp a := by ring
      _ ≤ Real.exp (η / 2) * (x / Real.exp η) :=
          mul_le_mul_of_nonneg_left hexpa (Real.exp_pos _).le
      _ = Real.exp (-η / 2) * x := h2
  -- the pole plane: `e^{a} ≤ log |t| ≤ |t|`
  have hat : Real.exp a ≤ |t| := by
    have h1 : x / Real.exp η ≤ x :=
      div_le_self hx0.le (Real.one_le_exp hη.le)
    have h2 : x ≤ |t| := by
      have := Real.log_le_sub_one_of_pos ht0
      linarith
    linarith
  have hlow : archGrowthConstant + B + (1 + 2 * a) ^ 2 ≤ (1 - Real.exp (-η / 2)) / 2 * x := by
    have h := hM₁ x ((le_max_left _ _).trans hxM)
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    nlinarith
  have hlog : x ≤ Real.log (2 + |t|) := Real.log_le_log ht0 (by linarith)
  have hmass : 0 ≤ ∫ u, f u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  refine le_trans ?_ (re_weilFullFunctional_modulated_ge hB ha0 hf h0 hw hat)
  have hc : (1 - Real.exp (-η / 2)) / 2 * x ≤
      Real.log (2 + |t|) - archGrowthConstant - (1 + (Real.exp (η / 2) - 1)) * Real.exp a - B -
        (1 + 2 * a) ^ 2 := by linarith
  linarith [mul_le_mul_of_nonneg_right hc hmass]

end GaloisForLFunctions.SelectiveArithmetic
