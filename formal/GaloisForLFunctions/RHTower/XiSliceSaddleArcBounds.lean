import GaloisForLFunctions.RHTower.XiLogDerivSymmetry
import GaloisForLFunctions.RHTower.XiLogDerivFactorization
import GaloisForLFunctions.RHTower.LorentzianZeroMass
import GaloisForLFunctions.HTGeometry.DigammaHalfPlaneAsymptotic
import GaloisForLFunctions.HTGeometry.SaddleArcControl
import GaloisForLFunctions.RHTower.XiSliceCircleDecay


/-!
# The saddle arc of the slice product

For `g_t(w) = ξ(½+w+it) ξ(½−w+it)` the scaled logarithmic derivative is
`F(w) = w g_t'(w)/g_t(w) = w L(w)`, with `L(w) = ξ'/ξ(½+w+it) + ξ'/ξ(½+w−it)`.  The functional
equation turns the second factor's derivative into the reflected point, and conjugation makes `F`
real on the real axis.

On `Re s ≥ 2`, `|s| ≥ 4` the four-factor splitting of `ξ'/ξ` together with the digamma bound
`|ψ(w) − log w| ≤ 3/|w|` and the Dirichlet series of `ζ'/ζ` gives

```
|ξ'/ξ(s) − ½ log(s/2)| ≤ C := 3 + Σ Λ(n)/n².
```

For `t ≥ 8`, `5 ≤ R ≤ t/2` and `|w − R| ≤ R/2` both points `½ + w ± it` lie in the annulus
`3t/4 ≤ |s| ≤ 3t`, so

* `|L(w)| ≤ log(3t/2) + π/2 + 2C`, `|L(w) − L(R)| ≤ log 4 + π + 4C`;
* `L(R)` is real with `log(t/2) − 2C ≤ L(R) ≤ log t + 2C`;
* `|F(w) − F(R)| ≤ R · xiSliceDiscConstant t`, and the saddle slope `F'(R) = L(R) + R L'(R)` lies
  within `2(log 4 + π + 4C)` of `L(R)`.

These are the inputs of `HTGeometry.saddleArc_bounds`, which is instantiated here for `θ ≤ 1/4`.
-/

open Complex Real Metric

namespace RHTower

noncomputable section

/-- The constant bounding `ξ'/ξ(s) − ½ log(s/2)` on `Re s ≥ 2`, `|s| ≥ 4`. -/
def xiLogDerivStirlingConstant : ℝ := 3 + vonMangoldtSquareMass

theorem xiLogDerivStirlingConstant_pos : 0 < xiLogDerivStirlingConstant := by
  unfold xiLogDerivStirlingConstant; linarith [vonMangoldtSquareMass_nonneg]

/-- **Stirling form of `ξ'/ξ` on the right.**  For `Re s ≥ 2` and `|s| ≥ 4`,
`|ξ'/ξ(s) − ½ log(s/2)| ≤ 3 + Σ Λ(n)/n²`: the rational terms, `½ log π`, the digamma error
`|ψ(w) − log w| ≤ 3/|w|` and the Dirichlet series of `ζ'/ζ` are each bounded. -/
theorem norm_logDeriv_xi_sub_half_log_le {s : ℂ} (hs : 2 ≤ s.re) (hs4 : 4 ≤ ‖s‖) :
    ‖logDeriv xi s - Complex.log (s / 2) / 2‖ ≤ xiLogDerivStirlingConstant := by
  rw [logDeriv_xi_fourFactor (by linarith)]
  have e : 1 / s + 1 / (s - 1) - (Real.log Real.pi : ℂ) / 2 + Complex.digamma (s / 2) / 2
      + logDeriv riemannZeta s - Complex.log (s / 2) / 2
      = (1 / s + 1 / (s - 1)) - (Real.log Real.pi : ℂ) / 2
        + ((Complex.digamma (s / 2) - Complex.log (s / 2)) / 2 + logDeriv riemannZeta s) := by
    ring
  rw [e]
  have h1 : ‖1 / s‖ ≤ 1 / 4 := by
    rw [norm_div, norm_one]; exact one_div_le_one_div_of_le (by norm_num) hs4
  have h2 : ‖1 / (s - 1)‖ ≤ 1 / 3 := by
    rw [norm_div, norm_one]
    apply one_div_le_one_div_of_le (by norm_num)
    have := norm_sub_norm_le s 1; simp only [norm_one] at this; linarith
  have h3 : ‖(Real.log Real.pi : ℂ) / 2‖ ≤ 11 / 10 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith [Real.pi_gt_three]))]
    have := Real.log_le_sub_one_of_pos Real.pi_pos
    have h2' : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2']
    linarith [Real.pi_lt_d2]
  have hs2re : 0 < (s / 2).re := by
    have : (s / 2).re = s.re / 2 := by simp
    rw [this]; linarith
  have hs2 : 2 ≤ ‖s / 2‖ := by
    rw [norm_div]; simp only [Complex.norm_ofNat]; linarith
  have h4 : ‖(Complex.digamma (s / 2) - Complex.log (s / 2)) / 2‖ ≤ 3 / 4 := by
    rw [norm_div]; simp only [Complex.norm_ofNat]
    have := GaloisForLFunctions.HTGeometry.norm_digamma_sub_log_le_of_re_pos hs2re hs2
    have h' : 3 / ‖s / 2‖ ≤ 3 / 2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs2
    linarith
  have h5 := norm_logDeriv_zeta_le_of_two_le_re hs
  calc _ ≤ ‖(1 / s + 1 / (s - 1)) - (Real.log Real.pi : ℂ) / 2‖
        + ‖(Complex.digamma (s / 2) - Complex.log (s / 2)) / 2 + logDeriv riemannZeta s‖ :=
        norm_add_le _ _
    _ ≤ (‖1 / s‖ + ‖1 / (s - 1)‖ + ‖(Real.log Real.pi : ℂ) / 2‖)
        + (‖(Complex.digamma (s / 2) - Complex.log (s / 2)) / 2‖ + ‖logDeriv riemannZeta s‖) := by
        gcongr
        · exact (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
        · exact norm_add_le _ _
    _ ≤ (1 / 4 + 1 / 3 + 11 / 10) + (3 / 4 + vonMangoldtSquareMass) := by gcongr
    _ ≤ xiLogDerivStirlingConstant := by unfold xiLogDerivStirlingConstant; linarith

/-- In the right half-plane, `|log z| ≤ log|z| + π/2` once `|z| ≥ 1`. -/
theorem norm_log_le_of_re_pos {z : ℂ} (hz : 0 < z.re) (h1 : 1 ≤ ‖z‖) :
    ‖Complex.log z‖ ≤ Real.log ‖z‖ + Real.pi / 2 := by
  have harg : |z.arg| ≤ Real.pi / 2 := Complex.abs_arg_le_pi_div_two_iff.mpr hz.le
  have hlog : 0 ≤ Real.log ‖z‖ := Real.log_nonneg h1
  calc ‖Complex.log z‖ ≤ |(Complex.log z).re| + |(Complex.log z).im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = Real.log ‖z‖ + |z.arg| := by rw [Complex.log_re, Complex.log_im, abs_of_nonneg hlog]
    _ ≤ Real.log ‖z‖ + Real.pi / 2 := by gcongr

/-- In the right half-plane, `|log z − log z'| ≤ |log|z| − log|z'|| + π`. -/
theorem norm_log_sub_log_le_of_re_pos {z z' : ℂ} (hz : 0 < z.re) (hz' : 0 < z'.re) :
    ‖Complex.log z - Complex.log z'‖ ≤ |Real.log ‖z‖ - Real.log ‖z'‖| + Real.pi := by
  have h1 : |z.arg| ≤ Real.pi / 2 := Complex.abs_arg_le_pi_div_two_iff.mpr hz.le
  have h2 : |z'.arg| ≤ Real.pi / 2 := Complex.abs_arg_le_pi_div_two_iff.mpr hz'.le
  calc ‖Complex.log z - Complex.log z'‖
        ≤ |(Complex.log z - Complex.log z').re| + |(Complex.log z - Complex.log z').im| :=
        Complex.norm_le_abs_re_add_abs_im _
    _ = |Real.log ‖z‖ - Real.log ‖z'‖| + |z.arg - z'.arg| := by
        rw [Complex.sub_re, Complex.sub_im, Complex.log_re, Complex.log_re, Complex.log_im,
          Complex.log_im]
    _ ≤ |Real.log ‖z‖ - Real.log ‖z'‖| + Real.pi := by
        gcongr
        calc |z.arg - z'.arg| ≤ |z.arg| + |z'.arg| := abs_sub _ _
          _ ≤ Real.pi / 2 + Real.pi / 2 := add_le_add h1 h2
          _ = Real.pi := by ring

/-- The log-derivative sum of the slice product. -/
def xiSliceLogDeriv (t : ℝ) (w : ℂ) : ℂ :=
  logDeriv xi (1 / 2 + w + (t : ℂ) * I) + logDeriv xi (1 / 2 + w - (t : ℂ) * I)

/-- The slice product has no zeros on `Re w > 1/2`. -/
theorem xiSliceProduct_ne_zero_of_re {t : ℝ} {w : ℂ} (hw : 1 / 2 < w.re) :
    xiSliceProduct t w ≠ 0 := by
  unfold xiSliceProduct
  have e : (1 / 2 : ℂ) - w + (t : ℂ) * I = 1 - (1 / 2 + w - (t : ℂ) * I) := by ring
  rw [e, xi_one_sub]
  refine mul_ne_zero (xi_ne_zero_of_one_lt_re ?_) (xi_ne_zero_of_one_lt_re ?_)
  · simp; linarith
  · simp; linarith

/-- **Scaled logarithmic derivative of the slice product.**  On `Re w > 1/2`,
`w g_t'(w)/g_t(w) = w (ξ'/ξ(½+w+it) + ξ'/ξ(½+w−it))`. -/
theorem scaledLogDeriv_xiSliceProduct {t : ℝ} {w : ℂ} (hw : 1 / 2 < w.re) :
    HTGeometry.scaledLogDeriv (xiSliceProduct t) w = w * xiSliceLogDeriv t w := by
  have hA : xi (1 / 2 + w + (t : ℂ) * I) ≠ 0 := xi_ne_zero_of_one_lt_re (by simp; linarith)
  have e : (1 / 2 : ℂ) - w + (t : ℂ) * I = 1 - (1 / 2 + w - (t : ℂ) * I) := by ring
  have hB : xi (1 / 2 - w + (t : ℂ) * I) ≠ 0 := by
    rw [e, xi_one_sub]; exact xi_ne_zero_of_one_lt_re (by simp; linarith)
  have h1 : HasDerivAt (fun x : ℂ => xi (1 / 2 + x + (t : ℂ) * I))
      (deriv xi (1 / 2 + w + (t : ℂ) * I)) w := by
    have := (xi_differentiable (1 / 2 + w + (t : ℂ) * I)).hasDerivAt.comp w
      (((hasDerivAt_id' w).const_add (1 / 2 : ℂ)).add_const ((t : ℂ) * I))
    exact this.congr_deriv (by simp)
  have h2 : HasDerivAt (fun x : ℂ => xi (1 / 2 - x + (t : ℂ) * I))
      (-deriv xi (1 / 2 - w + (t : ℂ) * I)) w := by
    have := (xi_differentiable (1 / 2 - w + (t : ℂ) * I)).hasDerivAt.comp w
      (((hasDerivAt_id' w).const_sub (1 / 2 : ℂ)).add_const ((t : ℂ) * I))
    exact this.congr_deriv (by simp)
  have hd : deriv (xiSliceProduct t) w
      = deriv xi (1 / 2 + w + (t : ℂ) * I) * xi (1 / 2 - w + (t : ℂ) * I)
        + xi (1 / 2 + w + (t : ℂ) * I) * (-deriv xi (1 / 2 - w + (t : ℂ) * I)) :=
    (h1.mul h2).deriv
  have hfe : logDeriv xi (1 / 2 - w + (t : ℂ) * I) = -logDeriv xi (1 / 2 + w - (t : ℂ) * I) := by
    rw [e, logDeriv_xi_one_sub_xiLogDerivSymmetry]
  have key : ∀ a b da db : ℂ, a ≠ 0 → b ≠ 0 →
      w * (da * b + a * -db) / (a * b) = w * (da / a + -(db / b)) := by
    intro a b da db ha hb; field_simp
  have hsl : xiSliceProduct t w = xi (1 / 2 + w + (t : ℂ) * I) * xi (1 / 2 - w + (t : ℂ) * I) := rfl
  unfold HTGeometry.scaledLogDeriv xiSliceLogDeriv
  rw [hd, hsl, show logDeriv xi (1 / 2 + w - (t : ℂ) * I) = -logDeriv xi (1 / 2 - w + (t : ℂ) * I)
    by rw [hfe, neg_neg], logDeriv_apply, logDeriv_apply]
  exact key _ _ _ _ hA hB

/-- The scaled logarithmic derivative is real on the real axis. -/
theorem im_scaledLogDeriv_xiSliceProduct_ofReal {t x : ℝ} (hx : 1 / 2 < x) :
    (HTGeometry.scaledLogDeriv (xiSliceProduct t) (x : ℂ)).im = 0 := by
  rw [scaledLogDeriv_xiSliceProduct (by simpa using hx)]
  have hc : (1 / 2 : ℂ) + (x : ℂ) - (t : ℂ) * I
      = (starRingEnd ℂ) (1 / 2 + (x : ℂ) + (t : ℂ) * I) := by
    apply Complex.ext <;> simp
  unfold xiSliceLogDeriv
  rw [hc, logDeriv_xi_conj_xiLogDerivSymmetry]
  simp [Complex.mul_im]

/-- Bounds for `ξ'/ξ` on an annulus `m₁ ≤ |s| ≤ m₂` (`m₁ ≥ 4`) in `Re s ≥ 2`. -/
theorem logDeriv_xi_annulus_bounds {s : ℂ} {m₁ m₂ : ℝ} (hs : 2 ≤ s.re) (hm₁ : 4 ≤ m₁)
    (h₁ : m₁ ≤ ‖s‖) (h₂ : ‖s‖ ≤ m₂) :
    ‖logDeriv xi s‖ ≤ Real.log (m₂ / 2) / 2 + Real.pi / 4 + xiLogDerivStirlingConstant
      ∧ Real.log (m₁ / 2) / 2 - xiLogDerivStirlingConstant ≤ (logDeriv xi s).re
      ∧ (logDeriv xi s).re ≤ Real.log (m₂ / 2) / 2 + xiLogDerivStirlingConstant := by
  have hs4 : 4 ≤ ‖s‖ := le_trans hm₁ h₁
  have hE := norm_logDeriv_xi_sub_half_log_le hs hs4
  set C := xiLogDerivStirlingConstant
  have hre2 : 0 < (s / 2).re := by
    have : (s / 2).re = s.re / 2 := by simp
    rw [this]; linarith
  have hn2 : ‖s / 2‖ = ‖s‖ / 2 := by rw [norm_div]; simp
  have hn1 : 1 ≤ ‖s / 2‖ := by rw [hn2]; linarith
  have hlogle : Real.log ‖s / 2‖ ≤ Real.log (m₂ / 2) := by
    rw [hn2]; exact Real.log_le_log (by linarith) (by linarith)
  have hlogge : Real.log (m₁ / 2) ≤ Real.log ‖s / 2‖ := by
    rw [hn2]; exact Real.log_le_log (by linarith) (by linarith)
  have hlog := norm_log_le_of_re_pos hre2 hn1
  have hre : (Complex.log (s / 2) / 2).re = Real.log ‖s / 2‖ / 2 := by
    rw [Complex.div_ofNat_re, Complex.log_re]
  have hEre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hE))
  rw [Complex.sub_re, hre] at hEre
  refine ⟨?_, by linarith [hEre.1], by linarith [hEre.2]⟩
  calc ‖logDeriv xi s‖ ≤ ‖Complex.log (s / 2) / 2‖ + ‖logDeriv xi s - Complex.log (s / 2) / 2‖ := by
        have := norm_add_le (Complex.log (s / 2) / 2) (logDeriv xi s - Complex.log (s / 2) / 2)
        simpa using this
    _ ≤ (Real.log (m₂ / 2) + Real.pi / 2) / 2 + C := by
        rw [norm_div]; simp only [Complex.norm_ofNat]
        gcongr
        linarith
    _ = Real.log (m₂ / 2) / 2 + Real.pi / 4 + C := by ring

/-- Two points of the same annulus: `|ξ'/ξ(s) − ξ'/ξ(s')| ≤ ½ log(m₂/m₁) + π/2 + 2C`. -/
theorem norm_logDeriv_xi_sub_le_annulus {s s' : ℂ} {m₁ m₂ : ℝ} (hs : 2 ≤ s.re) (hs' : 2 ≤ s'.re)
    (hm₁ : 4 ≤ m₁) (h₁ : m₁ ≤ ‖s‖) (h₂ : ‖s‖ ≤ m₂) (h₁' : m₁ ≤ ‖s'‖) (h₂' : ‖s'‖ ≤ m₂) :
    ‖logDeriv xi s - logDeriv xi s'‖
      ≤ Real.log (m₂ / m₁) / 2 + Real.pi / 2 + 2 * xiLogDerivStirlingConstant := by
  have hE := norm_logDeriv_xi_sub_half_log_le hs (le_trans hm₁ h₁)
  have hE' := norm_logDeriv_xi_sub_half_log_le hs' (le_trans hm₁ h₁')
  set C := xiLogDerivStirlingConstant
  have hre : ∀ z : ℂ, 2 ≤ z.re → 0 < (z / 2).re := fun z hz => by
    have : (z / 2).re = z.re / 2 := by simp
    rw [this]; linarith
  have hlog := norm_log_sub_log_le_of_re_pos (hre s hs) (hre s' hs')
  have hn2 : ∀ z : ℂ, ‖z / 2‖ = ‖z‖ / 2 := fun z => by rw [norm_div]; simp
  have hm1pos : 0 < m₁ := by linarith
  have hspos : 0 < ‖s‖ := by linarith
  have hs'pos : 0 < ‖s'‖ := by linarith
  have hratio : |Real.log ‖s / 2‖ - Real.log ‖s' / 2‖| ≤ Real.log (m₂ / m₁) := by
    rw [hn2, hn2, ← Real.log_div (by positivity) (by positivity), abs_le]
    have hp : 0 < ‖s‖ / 2 / (‖s'‖ / 2) := by positivity
    constructor
    · rw [neg_le, ← Real.log_inv, inv_div]
      apply Real.log_le_log (by positivity)
      rw [div_le_div_iff₀ (by linarith) hm1pos]
      nlinarith
    · apply Real.log_le_log hp
      rw [div_le_div_iff₀ (by linarith) hm1pos]
      nlinarith
  calc ‖logDeriv xi s - logDeriv xi s'‖
      ≤ ‖Complex.log (s / 2) / 2 - Complex.log (s' / 2) / 2‖
        + ‖logDeriv xi s - Complex.log (s / 2) / 2‖ + ‖logDeriv xi s' - Complex.log (s' / 2) / 2‖ := by
        have e : logDeriv xi s - logDeriv xi s' = (Complex.log (s / 2) / 2 - Complex.log (s' / 2) / 2)
            + (logDeriv xi s - Complex.log (s / 2) / 2)
            - (logDeriv xi s' - Complex.log (s' / 2) / 2) := by ring
        rw [e]
        exact (norm_sub_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ (Real.log (m₂ / m₁) + Real.pi) / 2 + C + C := by
        gcongr
        rw [← sub_div, norm_div]; simp only [Complex.norm_ofNat]
        gcongr
        linarith
    _ = Real.log (m₂ / m₁) / 2 + Real.pi / 2 + 2 * C := by ring

/-- Geometry of the two points `½ + w ± it` for `w` in the disc `|w − R| ≤ R/2`. -/
theorem slicePoint_annulus {t R : ℝ} (hR : 5 ≤ R) (hRt : R ≤ t / 2) {w : ℂ}
    (hw : w ∈ closedBall (R : ℂ) (R / 2)) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    2 ≤ (1 / 2 + w + (ε * t : ℝ) * I).re ∧ 3 * t / 4 ≤ ‖1 / 2 + w + (ε * t : ℝ) * I‖
      ∧ ‖1 / 2 + w + (ε * t : ℝ) * I‖ ≤ 3 * t := by
  rw [mem_closedBall, dist_eq_norm] at hw
  have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hw))
  have him := (abs_le.mp ((Complex.abs_im_le_norm _).trans hw))
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero] at hre him
  have hεt : |ε * t| = t := by
    rcases hε with h | h <;> subst h <;> simp [abs_of_pos (by linarith : (0 : ℝ) < t)]
  have hsre : (1 / 2 + w + (ε * t : ℝ) * I).re = 1 / 2 + w.re := by simp
  have hsim : (1 / 2 + w + (ε * t : ℝ) * I).im = w.im + ε * t := by simp
  refine ⟨by rw [hsre]; linarith, ?_, ?_⟩
  · refine le_trans ?_ (Complex.abs_im_le_norm _)
    rw [hsim]
    have h1 : |ε * t| - |w.im| ≤ |w.im + ε * t| := by
      have := abs_sub_abs_le_abs_sub (ε * t) (-w.im)
      rw [abs_neg, sub_neg_eq_add, add_comm] at this; linarith
    rw [hεt] at h1
    have : |w.im| ≤ R / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    linarith
  · refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [hsre, hsim]
    have h1 : |1 / 2 + w.re| ≤ 1 / 2 + 3 * R / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 : |w.im + ε * t| ≤ R / 2 + t := by
      refine (abs_add_le _ _).trans ?_
      rw [hεt]; have : |w.im| ≤ R / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    linarith

/-- **Log-derivative of the slice on the saddle disc.**  For `t ≥ 8`, `5 ≤ R ≤ t/2` and
`|w − R| ≤ R/2`: `|L(w)| ≤ log(3t/2) + π/2 + 2C` and `|L(w) − L(R)| ≤ log 4 + π + 4C`, where
`L = ξ'/ξ(½+·+it) + ξ'/ξ(½+·−it)` and `C = xiLogDerivStirlingConstant`. -/
theorem xiSliceLogDeriv_disc_bounds {t R : ℝ} (ht : 8 ≤ t) (hR : 5 ≤ R) (hRt : R ≤ t / 2) {w : ℂ}
    (hw : w ∈ closedBall (R : ℂ) (R / 2)) :
    ‖xiSliceLogDeriv t w‖ ≤ Real.log (3 * t / 2) + Real.pi / 2 + 2 * xiLogDerivStirlingConstant
      ∧ ‖xiSliceLogDeriv t w - xiSliceLogDeriv t R‖
        ≤ Real.log 4 + Real.pi + 4 * xiLogDerivStirlingConstant := by
  have hR0 : (R : ℂ) ∈ closedBall (R : ℂ) (R / 2) := mem_closedBall_self (by linarith)
  have ep : ∀ z : ℂ, (1 / 2 + z + ((1 : ℝ) * t : ℝ) * I) = 1 / 2 + z + (t : ℂ) * I := by
    intro z; push_cast; ring
  have em : ∀ z : ℂ, (1 / 2 + z + ((-1 : ℝ) * t : ℝ) * I) = 1 / 2 + z - (t : ℂ) * I := by
    intro z; push_cast; ring
  obtain ⟨p1, p2, p3⟩ := slicePoint_annulus hR hRt hw 1 (Or.inl rfl)
  obtain ⟨m1, m2, m3⟩ := slicePoint_annulus hR hRt hw (-1) (Or.inr rfl)
  obtain ⟨q1, q2, q3⟩ := slicePoint_annulus hR hRt hR0 1 (Or.inl rfl)
  obtain ⟨n1, n2, n3⟩ := slicePoint_annulus hR hRt hR0 (-1) (Or.inr rfl)
  rw [ep] at p1 p2 p3 q1 q2 q3
  rw [em] at m1 m2 m3 n1 n2 n3
  have hm : (4 : ℝ) ≤ 3 * t / 4 := by linarith
  have e3 : 3 * t / 2 = 3 * t / 2 := rfl
  have hA := (logDeriv_xi_annulus_bounds p1 hm p2 p3).1
  have hB := (logDeriv_xi_annulus_bounds m1 hm m2 m3).1
  have hdiv : 3 * t / (3 * t / 4) = 4 := by field_simp
  have hD1 := norm_logDeriv_xi_sub_le_annulus p1 q1 hm p2 p3 q2 q3
  have hD2 := norm_logDeriv_xi_sub_le_annulus m1 n1 hm m2 m3 n2 n3
  rw [hdiv] at hD1 hD2
  have h32 : 3 * t / 2 = 3 * t / 2 := rfl
  constructor
  · unfold xiSliceLogDeriv
    have h2 : Real.log (3 * t / 2) = Real.log (3 * t / 2) := rfl
    calc _ ≤ ‖logDeriv xi (1 / 2 + w + (t : ℂ) * I)‖ + ‖logDeriv xi (1 / 2 + w - (t : ℂ) * I)‖ :=
          norm_add_le _ _
      _ ≤ (Real.log (3 * t / 2) / 2 + Real.pi / 4 + xiLogDerivStirlingConstant)
          + (Real.log (3 * t / 2) / 2 + Real.pi / 4 + xiLogDerivStirlingConstant) := by
          gcongr
      _ = _ := by ring
  · unfold xiSliceLogDeriv
    have e : logDeriv xi (1 / 2 + w + (t : ℂ) * I) + logDeriv xi (1 / 2 + w - (t : ℂ) * I)
        - (logDeriv xi (1 / 2 + (R : ℂ) + (t : ℂ) * I) + logDeriv xi (1 / 2 + (R : ℂ) - (t : ℂ) * I))
        = (logDeriv xi (1 / 2 + w + (t : ℂ) * I) - logDeriv xi (1 / 2 + (R : ℂ) + (t : ℂ) * I))
          + (logDeriv xi (1 / 2 + w - (t : ℂ) * I) - logDeriv xi (1 / 2 + (R : ℂ) - (t : ℂ) * I)) := by
      ring
    rw [e]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ (Real.log 4 / 2 + Real.pi / 2 + 2 * xiLogDerivStirlingConstant)
          + (Real.log 4 / 2 + Real.pi / 2 + 2 * xiLogDerivStirlingConstant) := add_le_add hD1 hD2
      _ = _ := by ring

/-- `L(R)` is real, with `log(t/2) − 2C ≤ L(R) ≤ log t + 2C`. -/
theorem xiSliceLogDeriv_real_bounds {t R : ℝ} (ht : 8 ≤ t) (hR : 3 / 2 ≤ R) (hRt : R ≤ t / 2) :
    (xiSliceLogDeriv t R).im = 0
      ∧ Real.log (t / 2) - 2 * xiLogDerivStirlingConstant ≤ (xiSliceLogDeriv t R).re
      ∧ (xiSliceLogDeriv t R).re ≤ Real.log t + 2 * xiLogDerivStirlingConstant := by
  set s : ℂ := 1 / 2 + (R : ℂ) + (t : ℂ) * I with hs
  have hc : (1 / 2 : ℂ) + (R : ℂ) - (t : ℂ) * I = (starRingEnd ℂ) s := by
    rw [hs]; apply Complex.ext <;> simp
  have hL : xiSliceLogDeriv t R = logDeriv xi s + (starRingEnd ℂ) (logDeriv xi s) := by
    unfold xiSliceLogDeriv; rw [hc, logDeriv_xi_conj_xiLogDerivSymmetry]
  have hsre : s.re = 1 / 2 + R := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have h1 : t ≤ ‖s‖ := by
    have := Complex.abs_im_le_norm s; rw [hsim, abs_of_pos (by linarith)] at this; exact this
  have h2 : ‖s‖ ≤ 2 * t := by
    refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
    rw [hsre, hsim, abs_of_pos (by linarith), abs_of_pos (by linarith)]; linarith
  obtain ⟨-, hlo, hhi⟩ := logDeriv_xi_annulus_bounds (s := s) (m₁ := t) (m₂ := 2 * t)
    (by rw [hsre]; linarith) (by linarith) h1 h2
  rw [hL]
  have hre : (logDeriv xi s + (starRingEnd ℂ) (logDeriv xi s)).re = 2 * (logDeriv xi s).re := by
    simp; ring
  have him : (logDeriv xi s + (starRingEnd ℂ) (logDeriv xi s)).im = 0 := by simp
  rw [hre, him]
  have e : 2 * t / 2 = t := by ring
  rw [e] at hhi
  refine ⟨rfl, by linarith, by linarith⟩

/-- The saddle-disc constant: `M = R · xiSliceDiscConstant t` bounds `|F(w) − F(R)|`. -/
def xiSliceDiscConstant (t : ℝ) : ℝ :=
  (Real.log (3 * t / 2) + Real.pi / 2 + 2 * xiLogDerivStirlingConstant) / 2
    + (Real.log 4 + Real.pi + 4 * xiLogDerivStirlingConstant)

theorem differentiableOn_xiSliceLogDeriv (t : ℝ) :
    DifferentiableOn ℂ (xiSliceLogDeriv t) {w : ℂ | 1 / 2 < w.re} := by
  have hd : Differentiable ℂ (deriv xi) := fun s =>
    ((xi_differentiable.differentiableOn.deriv isOpen_univ) s (Set.mem_univ _)).differentiableAt
      (Filter.univ_mem)
  intro w hw
  have hw' : 1 / 2 < w.re := hw
  have h1 : DifferentiableAt ℂ (fun w : ℂ => logDeriv xi (1 / 2 + w + (t : ℂ) * I)) w := by
    have hne : xi (1 / 2 + w + (t : ℂ) * I) ≠ 0 := xi_ne_zero_of_one_lt_re (by simp; linarith)
    have hin : DifferentiableAt ℂ (fun w : ℂ => 1 / 2 + w + (t : ℂ) * I) w := by fun_prop
    simp only [logDeriv_apply]
    exact ((hd _).comp w hin).div ((xi_differentiable _).comp w hin) hne
  have h2 : DifferentiableAt ℂ (fun w : ℂ => logDeriv xi (1 / 2 + w - (t : ℂ) * I)) w := by
    have hne : xi (1 / 2 + w - (t : ℂ) * I) ≠ 0 := xi_ne_zero_of_one_lt_re (by simp; linarith)
    have hin : DifferentiableAt ℂ (fun w : ℂ => 1 / 2 + w - (t : ℂ) * I) w := by fun_prop
    simp only [logDeriv_apply]
    exact ((hd _).comp w hin).div ((xi_differentiable _).comp w hin) hne
  exact (h1.add h2).differentiableWithinAt

/-- **Saddle-arc control for the slice product.**  For `t ≥ 8`, `5 ≤ R ≤ t/2` and
`0 ≤ θ ≤ 1/4`, with `F = w g_t'/g_t`, `F₁ = F'(R)` and `M = R · xiSliceDiscConstant t`, the
normalised arc value obeys the two bounds of `HTGeometry.saddleArc_bounds` with `r = R/2`. -/
theorem xiSlice_saddleArc_bounds {t R θ : ℝ} (ht : 8 ≤ t) (hR : 5 ≤ R) (hRt : R ≤ t / 2)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 4) :
    ‖HTGeometry.saddleArc (xiSliceProduct t) R
        (HTGeometry.scaledLogDeriv (xiSliceProduct t) R).re θ‖
        ≤ Real.exp (-((deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re * R
            * (1 - Real.cos θ)) + 32 * (R * xiSliceDiscConstant t) / (R / 2) ^ 2 * R ^ 2 * θ ^ 3 / 3)
      ∧ (|(deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re| * R * θ ^ 3 / 6
            + 32 * (R * xiSliceDiscConstant t) / (R / 2) ^ 2 * R ^ 2 * θ ^ 3 / 3 ≤ Real.pi / 2 →
        Real.exp (-((deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re * R
            * (1 - Real.cos θ)) - 32 * (R * xiSliceDiscConstant t) / (R / 2) ^ 2 * R ^ 2 * θ ^ 3 / 3)
          * Real.cos (|(deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re| * R * θ ^ 3 / 6
            + 32 * (R * xiSliceDiscConstant t) / (R / 2) ^ 2 * R ^ 2 * θ ^ 3 / 3)
        ≤ (HTGeometry.saddleArc (xiSliceProduct t) R
            (HTGeometry.scaledLogDeriv (xiSliceProduct t) R).re θ).re) := by
  set U : Set ℂ := {w : ℂ | 1 / 2 < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hball : closedBall (R : ℂ) (R / 2) ⊆ U := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    have := (abs_le.mp ((Complex.abs_re_le_norm _).trans hw)).1
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    show 1 / 2 < w.re; linarith
  apply HTGeometry.saddleArc_bounds hUo (differentiable_xiSliceProduct t).differentiableOn
    (fun w hw => xiSliceProduct_ne_zero_of_re hw) (by linarith) (by linarith) hball
  · intro w hw
    have hwU : 1 / 2 < w.re := hball hw
    have hRU : 1 / 2 < (R : ℂ).re := by simp; linarith
    rw [scaledLogDeriv_xiSliceProduct hwU, scaledLogDeriv_xiSliceProduct hRU]
    obtain ⟨h1, h2⟩ := xiSliceLogDeriv_disc_bounds ht hR hRt hw
    have hwR : ‖w - R‖ ≤ R / 2 := by rwa [mem_closedBall, dist_eq_norm] at hw
    have e : w * xiSliceLogDeriv t w - R * xiSliceLogDeriv t R
        = (w - R) * xiSliceLogDeriv t w + R * (xiSliceLogDeriv t w - xiSliceLogDeriv t R) := by ring
    rw [e]
    calc _ ≤ ‖(w - R) * xiSliceLogDeriv t w‖ + ‖(R : ℂ) * (xiSliceLogDeriv t w - xiSliceLogDeriv t R)‖ :=
          norm_add_le _ _
      _ = ‖w - R‖ * ‖xiSliceLogDeriv t w‖ + R * ‖xiSliceLogDeriv t w - xiSliceLogDeriv t R‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      _ ≤ R / 2 * (Real.log (3 * t / 2) + Real.pi / 2 + 2 * xiLogDerivStirlingConstant)
          + R * (Real.log 4 + Real.pi + 4 * xiLogDerivStirlingConstant) := by
          gcongr
      _ = R * xiSliceDiscConstant t := by unfold xiSliceDiscConstant; ring
  · intro x hx
    have hx' : 1 / 2 < ((x : ℂ)).re := hx
    exact im_scaledLogDeriv_xiSliceProduct_ofReal (by simpa using hx')
  · exact hθ0
  · nlinarith

/-- **The saddle slope.**  With `F = w g_t'/g_t`, `F'(R) = L(R) + R L'(R)` and the Cauchy estimate
for `L` on `|w − R| ≤ R/2` give `|F'(R) − L(R)| ≤ 2(log 4 + π + 4C)`, so
`log(t/2) − 2C − 2(log 4 + π + 4C) ≤ F'(R) ≤ log t + 2C + 2(log 4 + π + 4C)`. -/
theorem xiSlice_saddleSlope_bounds {t R : ℝ} (ht : 8 ≤ t) (hR : 5 ≤ R) (hRt : R ≤ t / 2) :
    Real.log (t / 2) - 2 * xiLogDerivStirlingConstant
        - 2 * (Real.log 4 + Real.pi + 4 * xiLogDerivStirlingConstant)
      ≤ (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re
    ∧ (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re
      ≤ Real.log t + 2 * xiLogDerivStirlingConstant
        + 2 * (Real.log 4 + Real.pi + 4 * xiLogDerivStirlingConstant) := by
  set U : Set ℂ := {w : ℂ | 1 / 2 < w.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hRU : (R : ℂ) ∈ U := by show 1 / 2 < (R : ℂ).re; simp; linarith
  have hball : closedBall (R : ℂ) (R / 2) ⊆ U := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    have := (abs_le.mp ((Complex.abs_re_le_norm _).trans hw)).1
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    show 1 / 2 < w.re; linarith
  have hLd := differentiableOn_xiSliceLogDeriv t
  have hev : HTGeometry.scaledLogDeriv (xiSliceProduct t) =ᶠ[nhds (R : ℂ)]
      fun w => w * xiSliceLogDeriv t w := by
    filter_upwards [hUo.mem_nhds hRU] with w hw
    exact scaledLogDeriv_xiSliceProduct hw
  have hLR : HasDerivAt (xiSliceLogDeriv t) (deriv (xiSliceLogDeriv t) R) R :=
    (hLd.differentiableAt (hUo.mem_nhds hRU)).hasDerivAt
  have hderiv : deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R
      = xiSliceLogDeriv t R + R * deriv (xiSliceLogDeriv t) R := by
    rw [hev.deriv_eq]
    have := (hasDerivAt_id' (R : ℂ)).mul hLR
    exact this.deriv.trans (by ring)
  have hcauchy : ‖deriv (xiSliceLogDeriv t) R‖
      ≤ (Real.log 4 + Real.pi + 4 * xiLogDerivStirlingConstant) / (R / 2) :=
    HTGeometry.norm_deriv_le_of_norm_sub_le hLd (c := (R : ℂ)) (by linarith) hball
      (fun z hz => (xiSliceLogDeriv_disc_bounds ht hR hRt (sphere_subset_closedBall hz)).2)
  obtain ⟨-, hlo, hhi⟩ := xiSliceLogDeriv_real_bounds ht (by linarith) hRt
  have hRd : |(R * deriv (xiSliceLogDeriv t) R : ℂ).re|
      ≤ 2 * (Real.log 4 + Real.pi + 4 * xiLogDerivStirlingConstant) := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    calc R * ‖deriv (xiSliceLogDeriv t) R‖
        ≤ R * ((Real.log 4 + Real.pi + 4 * xiLogDerivStirlingConstant) / (R / 2)) := by gcongr
      _ = 2 * (Real.log 4 + Real.pi + 4 * xiLogDerivStirlingConstant) := by field_simp
  rw [hderiv, Complex.add_re]
  have := abs_le.mp hRd
  constructor <;> linarith [this.1, this.2]

end

end RHTower
