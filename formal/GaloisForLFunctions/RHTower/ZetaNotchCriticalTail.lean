import GaloisForLFunctions.RHTower.WeilAbscissaScaleBounds
import GaloisForLFunctions.RHTower.ZetaNotchMixtureMoments
import GaloisForLFunctions.RHTower.BurnolResidueCriticalLineKernelL2
import GaloisForLFunctions.RHTower.ZetaVerticalStripPolynomialBound
import GaloisForLFunctions.HTGeometry.VerticalStripResidueShift

/-!
# The mixed `|ζ|²` notch moment past the pole of `ζ`

Let `R` be holomorphic and bounded on `−1 ≤ Im z ≤ 0`, real-valued `r` on the real line. In the
variable `s = ½ + iz` the weighted mixed moment `∫ Ω_L q r |ζ|² e^{−iyt}` is the line integral over
`Re s = ½` of `Φ(s) = Ω_L(z) Q(z) R(z) ζ(s) ζ(1 − s) e^{−y(s − ½)}`. Shifting to `Re s = 3/2` crosses
the simple pole of `ζ(s)` at `s = 1` with residue `Ω_L(−i/2) Q(−i/2) R(−i/2) ζ(0) e^{−y/2}`. On the
new line `|ζ(3/2 + it)| ≤ ζ(3/2)`, `|ζ(−½ − it)| ≤ K (1 + |t|)` and `|Ω_L(t − i)| ≤ e⁴ Ω_L(t)`, so
(`exists_norm_weightedMixMoment_le`), for `L, y ≥ 0`:

`‖∫ Ω_L q r |ζ|² e^{−iyt}‖ ≤ C₁ (1 + L) e^{−y} + C₂ ‖R(−i/2)‖ e^{−y/2}`,

using the linear moment `∫ Ω_L(x)(1 + |x|) dx ≤ C (1 + L)`. The residue term vanishes when `R` has a
zero at `−i/2`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry

namespace RHTower.ZetaNotch

/-- The weighted mixed moment integrand in the variable `s = ½ + iz`. -/
def weightedTailIntegrand (L y : ℝ) (Q R : ℂ → ℂ) (s : ℂ) : ℂ :=
  mixWindow L (-I * (s - 1 / 2)) * Q (-I * (s - 1 / 2)) * R (-I * (s - 1 / 2)) *
    (riemannZeta s * riemannZeta (1 - s)) * Complex.exp (-(y : ℂ) * (s - 1 / 2))

theorem neg_I_mul_line (x t : ℝ) :
    -I * (((x : ℝ) : ℂ) + (t : ℂ) * I - 1 / 2) = (t : ℂ) - ((x - 1 / 2 : ℝ) : ℂ) * I := by
  push_cast
  ring_nf
  rw [I_sq]
  ring

theorem weightedTailIntegrand_half (L y : ℝ) {Q R : ℂ → ℂ} {q : ℝ → ℝ} {r : ℝ → ℂ}
    (hQq : ∀ t : ℝ, Q t = q t) (hRr : ∀ t : ℝ, R t = r t) (t : ℝ) :
    weightedTailIntegrand L y Q R (((1 / 2 : ℝ) : ℂ) + t * I) =
      mixWindow L t * (q t : ℂ) * r t * zetaSq t * Complex.exp (-(y * t) * I) := by
  have hz : -I * (((1 / 2 : ℝ) : ℂ) + t * I - 1 / 2) = (t : ℂ) := by
    rw [neg_I_mul_line]; push_cast; ring
  have h1 : (1 : ℂ) - (((1 / 2 : ℝ) : ℂ) + t * I) = ((1 / 2 : ℝ) : ℂ) + (-(t : ℂ)) * I := by
    push_cast; ring
  have he : -(y : ℂ) * (((1 / 2 : ℝ) : ℂ) + t * I - 1 / 2) = -((y : ℂ) * t) * I := by
    push_cast; ring
  unfold weightedTailIntegrand
  rw [hz, hQq, hRr, h1, he, ← zetaPairC_ofReal]
  rfl

theorem norm_mixWindow_neg_half_I_le (L : ℝ) : ‖mixWindow L (-I / 2)‖ ≤ 4 * Real.exp 1 := by
  have h := norm_mixWindow_le_line L (-I / 2)
  have hre : (-I / 2 : ℂ).re = 0 := by simp
  have him : (-I / 2 : ℂ).im = -1 / 2 := by simp
  rw [hre, him] at h
  have h0 : mixWindowReal L 0 ≤ 4 * 1 := mixWindowReal_le_of_forall fun r _ _ => scaleWeight_le_one L _
  calc ‖mixWindow L (-I / 2)‖ ≤ Real.exp (4 * (-1 / 2) ^ 2) * mixWindowReal L 0 := h
    _ ≤ Real.exp 1 * (4 * 1) := by
        apply mul_le_mul (by norm_num) h0 (mixWindowReal_nonneg _ _) (Real.exp_pos _).le
    _ = 4 * Real.exp 1 := by ring

/-- `‖ζ(−½ − it)‖ ≤ K (1 + |t|)`. -/
theorem exists_norm_riemannZeta_neg_half_le :
    ∃ K, 0 ≤ K ∧ ∀ t : ℝ, ‖riemannZeta (smoothAFEZetaLeftLinePt (-t))‖ ≤ K * (1 + |t|) := by
  refine ⟨GaloisForLFunctions.zetaHalfPlaneBound (3 / 2) / (2 * Real.pi), ?_, fun t => ?_⟩
  · have := (norm_nonneg _).trans
      (GaloisForLFunctions.norm_riemannZeta_le_halfPlane (c := 3 / 2) (by norm_num) (z := 3 / 2) (by norm_num))
    positivity
  · refine (norm_riemannZeta_leftLine_le_linear (-t)).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by
      have := (norm_nonneg _).trans
        (GaloisForLFunctions.norm_riemannZeta_le_halfPlane (c := 3 / 2) (by norm_num) (z := 3 / 2) (by norm_num))
      positivity)
    unfold smoothAFEZetaLeftLinePt
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_neg]
    norm_num

/-- **The weighted mixed moment past the pole**:
`‖∫ Ω_L q r |ζ|² e^{−iyt}‖ ≤ C₁ (1 + L) e^{−y} + C₂ ‖R(−i/2)‖ e^{−y/2}` for `L, y ≥ 0`. -/
theorem exists_norm_weightedMixMoment_le {Q : ℂ → ℂ} (hQd : Differentiable ℂ Q) {CQ : ℝ}
    (hQb : ∀ z : ℂ, |z.im| ≤ 1 → ‖Q z‖ ≤ CQ) {q : ℝ → ℝ} (hQq : ∀ t : ℝ, Q t = q t)
    {R : ℂ → ℂ} (hRd : ∀ z : ℂ, -1 ≤ z.im → z.im ≤ 0 → DifferentiableAt ℂ R z) {CR : ℝ}
    (hRb : ∀ z : ℂ, -1 ≤ z.im → z.im ≤ 0 → ‖R z‖ ≤ CR) {r : ℝ → ℂ} (hRr : ∀ t : ℝ, R t = r t) :
    ∃ C₁ C₂, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ L : ℝ, 0 ≤ L → ∀ y : ℝ, 0 ≤ y →
      ‖∫ t : ℝ, mixWindow L t * (q t : ℂ) * r t * zetaSq t * Complex.exp (-(y * t) * I)‖ ≤
        C₁ * (1 + L) * Real.exp (-y) + C₂ * ‖R (-I / 2)‖ * Real.exp (-(y / 2)) := by
  have hCQ0 : 0 ≤ CQ := (norm_nonneg _).trans (hQb 0 (by simp))
  have hCR0 : 0 ≤ CR := (norm_nonneg _).trans (hRb (-I) (by simp) (by simp))
  obtain ⟨Cζ, N, hCζ0, hCζ⟩ := exists_bound_norm_riemannZeta_strip 2
  obtain ⟨B, hB0, hB⟩ := RHTower.WeilAbscissa.exists_pow_mul_exp_neg_le (2 * N + 2)
  obtain ⟨CI, hCI0, hCI⟩ := exists_integral_mixWindowReal_mul_one_add_le
  obtain ⟨K, hK0, hK⟩ := exists_norm_riemannZeta_neg_half_le
  set Z : ℝ := GaloisForLFunctions.zetaHalfPlaneBound (3 / 2) with hZ
  have hZ0 : 0 ≤ Z := (norm_nonneg _).trans
    (GaloisForLFunctions.norm_riemannZeta_le_halfPlane (c := 3 / 2) (by norm_num) (z := 3 / 2) (by norm_num))
  refine ⟨Real.exp 4 * CQ * CR * Z * K * CI, 2 * Real.pi * (2 * Real.exp 1 * CQ), by positivity,
    by positivity, fun L hL y hy => ?_⟩
  set Φ : ℂ → ℂ := weightedTailIntegrand L y Q R with hΦ
  have hz : Differentiable ℂ fun w : ℂ => -I * (w - 1 / 2) := by fun_prop
  have hzim : ∀ s : ℂ, (-I * (s - 1 / 2)).im = -(s.re - 1 / 2) := fun s => by simp
  -- differentiability off the pole
  have hdiff : ∀ s : ℂ, (1 / 2 : ℝ) ≤ s.re → s.re ≤ (3 / 2 : ℝ) → s ≠ 1 →
      DifferentiableAt ℂ Φ s := by
    intro s hs1 hs2 hs
    have hs0 : 1 - s ≠ 1 := by
      intro h
      have : s = 0 := by linear_combination -h
      rw [this, Complex.zero_re] at hs1
      norm_num at hs1
    have hR' : DifferentiableAt ℂ (fun w => R (-I * (w - 1 / 2))) s :=
      (hRd _ (by rw [hzim]; linarith) (by rw [hzim]; linarith)).comp s (hz s)
    refine ((((((differentiable_mixWindow L).comp hz) s).mul ((hQd.comp hz) s)).mul hR').mul
      ((differentiableAt_riemannZeta hs).mul
        ((differentiableAt_riemannZeta hs0).comp s (by fun_prop)))).mul (by fun_prop)
  -- the residue at `s = 1`
  set G : ℂ → ℂ := fun s => mixWindow L (-I * (s - 1 / 2)) * Q (-I * (s - 1 / 2)) *
    R (-I * (s - 1 / 2)) * riemannZeta (1 - s) * Complex.exp (-(y : ℂ) * (s - 1 / 2)) with hG
  have hGc : ContinuousAt G 1 := by
    have h0 : (1 : ℂ) - 1 ≠ 1 := by norm_num
    have hR' : DifferentiableAt ℂ (fun w => R (-I * (w - 1 / 2))) 1 :=
      (hRd _ (by rw [hzim]; norm_num) (by rw [hzim]; norm_num)).comp (1 : ℂ) (hz 1)
    exact ((((((differentiable_mixWindow L).comp hz) 1).mul ((hQd.comp hz) 1)).mul hR').mul
      ((differentiableAt_riemannZeta h0).comp (1 : ℂ) (by fun_prop))).mul
      (by fun_prop) |>.continuousAt
  have hres : Tendsto (fun s => (s - 1) * Φ s) (𝓝[≠] 1) (𝓝 (1 * G 1)) := by
    refine (riemannZeta_residue_one.mul (hGc.tendsto.mono_left nhdsWithin_le_nhds)).congr ?_
    intro s
    simp only [hΦ, hG, weightedTailIntegrand]
    ring
  have hA : ‖1 * G 1‖ ≤ 2 * Real.exp 1 * CQ * ‖R (-I / 2)‖ * Real.exp (-(y / 2)) := by
    have hz1 : -I * ((1 : ℂ) - 1 / 2) = -I / 2 := by ring
    have hs1 : (1 : ℂ) - 1 = 0 := by ring
    have he : ‖Complex.exp (-(y : ℂ) * ((1 : ℂ) - 1 / 2))‖ = Real.exp (-(y / 2)) := by
      rw [Complex.norm_exp]; congr 1; simp; ring
    simp only [hG, one_mul]
    rw [hz1, hs1, riemannZeta_zero, norm_mul, norm_mul, norm_mul, norm_mul, he]
    have hQ := hQb (-I / 2) (by simp; norm_num)
    have hW := norm_mixWindow_neg_half_I_le L
    have hz0 : ‖(-1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [hz0]
    calc ‖mixWindow L (-I / 2)‖ * ‖Q (-I / 2)‖ * ‖R (-I / 2)‖ * (1 / 2) * Real.exp (-(y / 2))
        ≤ (4 * Real.exp 1) * CQ * ‖R (-I / 2)‖ * (1 / 2) * Real.exp (-(y / 2)) := by gcongr
      _ = 2 * Real.exp 1 * CQ * ‖R (-I / 2)‖ * Real.exp (-(y / 2)) := by ring
  -- decay in the strip
  have hdec : ∀ s : ℂ, (1 / 2 : ℝ) ≤ s.re → s.re ≤ (3 / 2 : ℝ) → 1 ≤ |s.im| →
      ‖Φ s‖ ≤ (Real.exp 4 * (4 * Real.exp (L ^ 2)) * CQ * CR * (Cζ * Cζ) * B) *
        (1 + s.im ^ 2)⁻¹ := by
    intro s hs1 hs2 ht
    set t := s.im with ht_def
    have hzre : (-I * (s - 1 / 2)).re = t := by simp [ht_def]
    have hzi : |(-I * (s - 1 / 2)).im| ≤ 1 := by
      rw [hzim, abs_le]; constructor <;> linarith
    have h1 := norm_mixWindow_le_line L (-I * (s - 1 / 2))
    rw [hzre] at h1
    have h1' : ‖mixWindow L (-I * (s - 1 / 2))‖ ≤
        Real.exp 4 * (4 * (Real.exp (L ^ 2) * Real.exp (-(2 / 25) * t ^ 2))) := by
      refine h1.trans (mul_le_mul (Real.exp_le_exp.mpr ?_) (mixWindowReal_le_gauss L t)
        (mixWindowReal_nonneg _ _) (Real.exp_pos _).le)
      have := abs_le.mp hzi
      nlinarith
    have h2 := hQb _ hzi
    have h2' := hRb (-I * (s - 1 / 2)) (by rw [hzim]; linarith) (by rw [hzim]; linarith)
    have h3 : ‖riemannZeta s‖ ≤ Cζ * |t| ^ N := by
      have := hCζ s.re s.im (by rw [abs_le]; constructor <;> linarith) ht
      rwa [Complex.re_add_im] at this
    have h4 : ‖riemannZeta (1 - s)‖ ≤ Cζ * |t| ^ N := by
      have h := hCζ (1 - s.re) (-s.im) (by rw [abs_le]; constructor <;> linarith)
        (by rw [abs_neg]; exact ht)
      have e : ((1 - s.re : ℝ) : ℂ) + ((-s.im : ℝ) : ℂ) * I = 1 - s := by
        apply Complex.ext <;> simp
      rw [e, abs_neg] at h
      exact h
    have h5 : ‖Complex.exp (-(y : ℂ) * (s - 1 / 2))‖ ≤ 1 := by
      rw [Complex.norm_exp, Real.exp_le_one_iff]
      simp
      nlinarith
    have hpoly : |t| ^ N * |t| ^ N * Real.exp (-(2 / 25) * t ^ 2) ≤ B * (1 + t ^ 2)⁻¹ := by
      have ht0 : 0 ≤ |t| := abs_nonneg t
      have hb := hB |t| ht0
      have hsq : 1 + t ^ 2 ≤ (1 + |t|) ^ 2 := by
        rw [← sq_abs t]; nlinarith
      have hpow : |t| ^ N * |t| ^ N * (1 + t ^ 2) ≤ (1 + |t|) ^ (2 * N + 2) := by
        have ha : |t| ^ N ≤ (1 + |t|) ^ N := pow_le_pow_left₀ ht0 (by linarith) N
        calc |t| ^ N * |t| ^ N * (1 + t ^ 2) ≤ (1 + |t|) ^ N * (1 + |t|) ^ N * (1 + |t|) ^ 2 := by
              gcongr
          _ = (1 + |t|) ^ (2 * N + 2) := by ring
      have hexp : Real.exp (-(2 / 25) * t ^ 2) ≤ Real.exp (-(|t| ^ 2 / 256)) :=
        Real.exp_le_exp.mpr (by rw [sq_abs]; nlinarith [sq_nonneg t])
      have hpos : 0 < 1 + t ^ 2 := by positivity
      rw [le_mul_inv_iff₀ hpos]
      calc |t| ^ N * |t| ^ N * Real.exp (-(2 / 25) * t ^ 2) * (1 + t ^ 2)
          = (|t| ^ N * |t| ^ N * (1 + t ^ 2)) * Real.exp (-(2 / 25) * t ^ 2) := by ring
        _ ≤ (1 + |t|) ^ (2 * N + 2) * Real.exp (-(|t| ^ 2 / 256)) :=
            mul_le_mul hpow hexp (Real.exp_pos _).le (by positivity)
        _ ≤ B := hb
    simp only [hΦ, weightedTailIntegrand]
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul]
    calc ‖mixWindow L (-I * (s - 1 / 2))‖ * ‖Q (-I * (s - 1 / 2))‖ * ‖R (-I * (s - 1 / 2))‖ *
          (‖riemannZeta s‖ * ‖riemannZeta (1 - s)‖) * ‖Complex.exp (-(y : ℂ) * (s - 1 / 2))‖
        ≤ (Real.exp 4 * (4 * (Real.exp (L ^ 2) * Real.exp (-(2 / 25) * t ^ 2)))) * CQ * CR *
            ((Cζ * |t| ^ N) * (Cζ * |t| ^ N)) * 1 := by
          gcongr
      _ = Real.exp 4 * (4 * Real.exp (L ^ 2)) * CQ * CR * (Cζ * Cζ) *
            (|t| ^ N * |t| ^ N * Real.exp (-(2 / 25) * t ^ 2)) := by ring
      _ ≤ Real.exp 4 * (4 * Real.exp (L ^ 2)) * CQ * CR * (Cζ * Cζ) * (B * (1 + t ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left hpoly (by positivity)
      _ = _ := by ring
  -- the residue shift
  have hshift := integral_line_sub_integral_line_eq (F := Φ) (a := 1 / 2) (b := 3 / 2) (p := 1)
    (A := 1 * G 1) (by norm_num) (by norm_num) hdiff hres (T₀ := 1) hdec
  -- the moment is the line integral on `Re s = ½`
  have hmom : (∫ t : ℝ, mixWindow L t * (q t : ℂ) * r t * zetaSq t * Complex.exp (-(y * t) * I)) =
      ∫ t : ℝ, Φ (((1 / 2 : ℝ) : ℂ) + t * I) := by
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only [hΦ]
    rw [weightedTailIntegrand_half L y hQq hRr t]
  -- the line `Re s = 3/2`
  set m : ℝ → ℝ := fun t => Real.exp 4 * CQ * CR * Z * K * Real.exp (-y) *
    (mixWindowReal L t * (1 + |t|)) with hm
  have hmi : Integrable m :=
    (integrable_mixWindowReal_mul_of_le (L := L) (by fun_prop) (fun t => by positivity)
      (fun t => by nlinarith [abs_nonneg t])).const_mul _
  have hline : ∀ t : ℝ, ‖Φ (((3 / 2 : ℝ) : ℂ) + t * I)‖ ≤ m t := by
    intro t
    have hzt : -I * (((3 / 2 : ℝ) : ℂ) + t * I - 1 / 2) = (t : ℂ) - ((1 : ℝ) : ℂ) * I := by
      rw [neg_I_mul_line]; norm_num
    have h1s : (1 : ℂ) - (((3 / 2 : ℝ) : ℂ) + t * I) = smoothAFEZetaLeftLinePt (-t) := by
      unfold smoothAFEZetaLeftLinePt; push_cast; ring
    have he : ‖Complex.exp (-(y : ℂ) * (((3 / 2 : ℝ) : ℂ) + t * I - 1 / 2))‖ = Real.exp (-y) := by
      rw [Complex.norm_exp]; congr 1; simp; ring
    have hw := norm_mixWindow_le_line L ((t : ℂ) - ((1 : ℝ) : ℂ) * I)
    have hwre : ((t : ℂ) - ((1 : ℝ) : ℂ) * I).re = t := by simp
    have hwim : ((t : ℂ) - ((1 : ℝ) : ℂ) * I).im = -1 := by simp
    rw [hwre, hwim] at hw
    have hQ := hQb ((t : ℂ) - ((1 : ℝ) : ℂ) * I) (by rw [hwim]; norm_num)
    have hRt := hRb ((t : ℂ) - ((1 : ℝ) : ℂ) * I) (by rw [hwim]) (by rw [hwim]; norm_num)
    have hζ1 : ‖riemannZeta (((3 / 2 : ℝ) : ℂ) + t * I)‖ ≤ Z :=
      GaloisForLFunctions.norm_riemannZeta_le_halfPlane (c := 3 / 2) (by norm_num) (by simp)
    have hζ2 := hK t
    simp only [hΦ, weightedTailIntegrand]
    rw [hzt, h1s, norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, he, hm]
    have hA0 : 0 ≤ Real.exp (4 * (-1) ^ 2) * mixWindowReal L t :=
      mul_nonneg (Real.exp_pos _).le (mixWindowReal_nonneg L t)
    calc ‖mixWindow L ((t : ℂ) - ((1 : ℝ) : ℂ) * I)‖ * ‖Q ((t : ℂ) - ((1 : ℝ) : ℂ) * I)‖ *
          ‖R ((t : ℂ) - ((1 : ℝ) : ℂ) * I)‖ *
          (‖riemannZeta (((3 / 2 : ℝ) : ℂ) + t * I)‖ *
            ‖riemannZeta (smoothAFEZetaLeftLinePt (-t))‖) * Real.exp (-y)
        ≤ (Real.exp (4 * (-1) ^ 2) * mixWindowReal L t) * CQ * CR * (Z * (K * (1 + |t|))) *
            Real.exp (-y) :=
          mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul (mul_le_mul hw hQ (norm_nonneg _) hA0)
            hRt (norm_nonneg _) (mul_nonneg hA0 hCQ0))
            (mul_le_mul hζ1 hζ2 (norm_nonneg _) hZ0) (by positivity)
            (mul_nonneg (mul_nonneg hA0 hCQ0) hCR0)) (Real.exp_pos _).le
      _ = _ := by norm_num; ring
  have hint : ‖∫ t : ℝ, Φ (((3 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      Real.exp 4 * CQ * CR * Z * K * CI * (1 + L) * Real.exp (-y) := by
    refine (norm_integral_le_of_norm_le hmi (Eventually.of_forall hline)).trans ?_
    rw [hm, integral_const_mul]
    calc Real.exp 4 * CQ * CR * Z * K * Real.exp (-y) * ∫ t, mixWindowReal L t * (1 + |t|)
        ≤ Real.exp 4 * CQ * CR * Z * K * Real.exp (-y) * (CI * (1 + L)) :=
          mul_le_mul_of_nonneg_left (hCI L hL) (by positivity)
      _ = _ := by ring
  have hmom' : (∫ t : ℝ, mixWindow L t * (q t : ℂ) * r t * zetaSq t *
      Complex.exp (-(y * t) * I)) = (∫ t : ℝ, Φ (((3 / 2 : ℝ) : ℂ) + t * I)) -
      2 * Real.pi * (1 * G 1) := by
    rw [hmom]
    push_cast at hshift ⊢
    linear_combination -hshift
  rw [hmom']
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, show ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi by
    rw [show (2 * Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]]
  have := mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
  nlinarith

/-- **The mixed moment past the pole**: `‖M_Ω(y)‖ ≤ C₁ (1 + L²) e^{−y} + C₂ e^{−y/2}` for
`L, y ≥ 0`, for every entire `Q` bounded on `|Im z| ≤ 1` and real on the real line. -/
theorem exists_norm_mixMoment_le_crit {Q : ℂ → ℂ} (hQd : Differentiable ℂ Q) {CQ : ℝ}
    (hQb : ∀ z : ℂ, |z.im| ≤ 1 → ‖Q z‖ ≤ CQ) {q : ℝ → ℝ} (hQq : ∀ t : ℝ, Q t = q t) :
    ∃ C₁ C₂, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ L : ℝ, 0 ≤ L → ∀ y : ℝ, 0 ≤ y →
      ‖mixMoment L q y‖ ≤ C₁ * (1 + L ^ 2) * Real.exp (-y) + C₂ * Real.exp (-(y / 2)) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, h⟩ := exists_norm_weightedMixMoment_le hQd hQb hQq (R := fun _ => 1)
    (fun z _ _ => differentiableAt_const _) (CR := 1) (fun z _ _ => by simp) (r := fun _ => 1)
    (fun t => rfl)
  refine ⟨2 * C₁, C₂, by positivity, hC₂, fun L hL y hy => ?_⟩
  have hm : mixMoment L q y = ∫ t : ℝ, mixWindow L t * (q t : ℂ) * (fun _ : ℝ => (1 : ℂ)) t *
      zetaSq t * Complex.exp (-(y * t) * I) := by
    unfold mixMoment
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp
  rw [hm]
  refine (h L hL y hy).trans ?_
  simp only [norm_one, mul_one]
  have hL2 : 1 + L ≤ 2 * (1 + L ^ 2) := by nlinarith [sq_nonneg (L - 1)]
  have he := Real.exp_pos (-y)
  nlinarith [mul_le_mul_of_nonneg_left hL2 (mul_nonneg hC₁ he.le)]

end RHTower.ZetaNotch
