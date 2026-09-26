import GaloisForLFunctions.RHTower.XiSliceHighOrderCoeffPositivity
import GaloisForLFunctions.HTGeometry.GammaImaginaryShiftBounds


/-!
# The slice product on circles of radius comparable to or larger than the height

For the Taylor coefficients `c_{2k}(t)` of `g_t(x) = ξ(½+x+it) ξ(½−x+it)` with `k ≳ t log t` the
saddle radius `R` is at least a fixed fraction of `t`.  This file supplies the analytic inputs of the
saddle-point evaluation in the regime `R ≥ 8`, `0 ≤ t ≤ 5R`, with scale `log R`.

* **Saddle disc.**  For `|w − R| ≤ R/2` the points `½ + w ± it` lie in `R/2 ≤ |s| ≤ 8R`, so
  `|L(w)| ≤ log(4R) + π/2 + 2C`, `|L(w) − L(R)| ≤ log 16 + π + 4C`, `L(R) ∈ [log(R/2) − 2C, log(4R) + 2C]`,
  and the saddle-arc control and slope bounds follow as for `R ≤ t/2`.
* **Near arc** `θ ≤ π/3`.  The two Stirling segments stay in `Re ≥ R/4`, so the symmetric-split
  law applies without any restriction on `t`:
  `|g_t(Re^{iθ})| ≤ 16 g_t(R) exp(−R(1−cos θ) log(R/4π) + 12(1−cos θ+sin θ) + 6θ)`.
* **Far arc** `π/3 ≤ θ ≤ π/2`.  The points have abscissa at most `½ + R/2`, where
  `|ξ| ≤ M₀ + 196R²Γ(R/4+2)(2+24R)` (compact box plus `|Γ(x+iy)| ≤ Γ(x)` and crude `ζ` bounds).  At
  the saddle point, `|ξ|` carries `Γ((½+R)/2)`, which exceeds `Γ(R/4+2)` by `exp((R/4) log R − O(R))`.
  Hence `|g_t(Re^{iθ})| ≤ g_t(R) exp(−(R/8) log R)` for `R ≥ R₁`.
-/

open Complex Real Metric intervalIntegral

namespace RHTower

noncomputable section

/-- Geometry of `½ + w ± it` for `|w − R| ≤ R/2` when `R ≥ 8` and `0 ≤ t ≤ 5R`. -/
theorem slicePoint_annulus_large {t R : ℝ} (hR : 8 ≤ R) (ht0 : 0 ≤ t) (htR : t ≤ 5 * R) {w : ℂ}
    (hw : w ∈ closedBall (R : ℂ) (R / 2)) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) :
    2 ≤ (1 / 2 + w + (ε * t : ℝ) * I).re ∧ R / 2 ≤ ‖1 / 2 + w + (ε * t : ℝ) * I‖
      ∧ ‖1 / 2 + w + (ε * t : ℝ) * I‖ ≤ 8 * R := by
  rw [mem_closedBall, dist_eq_norm] at hw
  have hre := (abs_le.mp ((Complex.abs_re_le_norm _).trans hw))
  have him := (abs_le.mp ((Complex.abs_im_le_norm _).trans hw))
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero] at hre him
  have hεt : |ε * t| = t := by
    rcases hε with h | h <;> subst h <;> simp [abs_of_nonneg ht0]
  have hsre : (1 / 2 + w + (ε * t : ℝ) * I).re = 1 / 2 + w.re := by simp
  have hsim : (1 / 2 + w + (ε * t : ℝ) * I).im = w.im + ε * t := by simp
  refine ⟨by rw [hsre]; linarith, ?_, ?_⟩
  · refine le_trans ?_ (Complex.re_le_norm _)
    rw [hsre]; linarith
  · refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [hsre, hsim]
    have h1 : |1 / 2 + w.re| ≤ 1 / 2 + 3 * R / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 : |w.im + ε * t| ≤ R / 2 + t := by
      refine (abs_add_le _ _).trans ?_
      rw [hεt]; have : |w.im| ≤ R / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    linarith

/-- **Log-derivative of the slice on a large saddle disc.**  For `R ≥ 8`, `0 ≤ t ≤ 5R` and
`|w − R| ≤ R/2`: `|L(w)| ≤ log(4R) + π/2 + 2C` and `|L(w) − L(R)| ≤ log 16 + π + 4C`. -/
theorem xiSliceLogDeriv_disc_bounds_large {t R : ℝ} (hR : 8 ≤ R) (ht0 : 0 ≤ t) (htR : t ≤ 5 * R)
    {w : ℂ} (hw : w ∈ closedBall (R : ℂ) (R / 2)) :
    ‖xiSliceLogDeriv t w‖ ≤ Real.log (4 * R) + Real.pi / 2 + 2 * xiLogDerivStirlingConstant
      ∧ ‖xiSliceLogDeriv t w - xiSliceLogDeriv t R‖
        ≤ Real.log 16 + Real.pi + 4 * xiLogDerivStirlingConstant := by
  have hR0 : (R : ℂ) ∈ closedBall (R : ℂ) (R / 2) := mem_closedBall_self (by linarith)
  have ep : ∀ z : ℂ, (1 / 2 + z + ((1 : ℝ) * t : ℝ) * I) = 1 / 2 + z + (t : ℂ) * I := by
    intro z; push_cast; ring
  have em : ∀ z : ℂ, (1 / 2 + z + ((-1 : ℝ) * t : ℝ) * I) = 1 / 2 + z - (t : ℂ) * I := by
    intro z; push_cast; ring
  obtain ⟨p1, p2, p3⟩ := slicePoint_annulus_large hR ht0 htR hw 1 (Or.inl rfl)
  obtain ⟨m1, m2, m3⟩ := slicePoint_annulus_large hR ht0 htR hw (-1) (Or.inr rfl)
  obtain ⟨q1, q2, q3⟩ := slicePoint_annulus_large hR ht0 htR hR0 1 (Or.inl rfl)
  obtain ⟨n1, n2, n3⟩ := slicePoint_annulus_large hR ht0 htR hR0 (-1) (Or.inr rfl)
  rw [ep] at p1 p2 p3 q1 q2 q3
  rw [em] at m1 m2 m3 n1 n2 n3
  have hm : (4 : ℝ) ≤ R / 2 := by linarith
  have hA := (logDeriv_xi_annulus_bounds p1 hm p2 p3).1
  have hB := (logDeriv_xi_annulus_bounds m1 hm m2 m3).1
  have hdiv : 8 * R / (R / 2) = 16 := by field_simp; ring
  have h82 : 8 * R / 2 = 4 * R := by ring
  rw [h82] at hA hB
  have hD1 := norm_logDeriv_xi_sub_le_annulus p1 q1 hm p2 p3 q2 q3
  have hD2 := norm_logDeriv_xi_sub_le_annulus m1 n1 hm m2 m3 n2 n3
  rw [hdiv] at hD1 hD2
  constructor
  · unfold xiSliceLogDeriv
    calc _ ≤ ‖logDeriv xi (1 / 2 + w + (t : ℂ) * I)‖ + ‖logDeriv xi (1 / 2 + w - (t : ℂ) * I)‖ :=
          norm_add_le _ _
      _ ≤ (Real.log (4 * R) / 2 + Real.pi / 4 + xiLogDerivStirlingConstant)
          + (Real.log (4 * R) / 2 + Real.pi / 4 + xiLogDerivStirlingConstant) := by gcongr
      _ = _ := by ring
  · unfold xiSliceLogDeriv
    have e : logDeriv xi (1 / 2 + w + (t : ℂ) * I) + logDeriv xi (1 / 2 + w - (t : ℂ) * I)
        - (logDeriv xi (1 / 2 + (R : ℂ) + (t : ℂ) * I) + logDeriv xi (1 / 2 + (R : ℂ) - (t : ℂ) * I))
        = (logDeriv xi (1 / 2 + w + (t : ℂ) * I) - logDeriv xi (1 / 2 + (R : ℂ) + (t : ℂ) * I))
          + (logDeriv xi (1 / 2 + w - (t : ℂ) * I) - logDeriv xi (1 / 2 + (R : ℂ) - (t : ℂ) * I)) := by
      ring
    rw [e]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ (Real.log 16 / 2 + Real.pi / 2 + 2 * xiLogDerivStirlingConstant)
          + (Real.log 16 / 2 + Real.pi / 2 + 2 * xiLogDerivStirlingConstant) := add_le_add hD1 hD2
      _ = _ := by ring

/-- `L(R)` is real with `log(R/2) − 2C ≤ L(R) ≤ log(4R) + 2C` when `R ≥ 8`, `0 ≤ t ≤ 5R`. -/
theorem xiSliceLogDeriv_real_bounds_large {t R : ℝ} (hR : 8 ≤ R) (ht0 : 0 ≤ t) (htR : t ≤ 5 * R) :
    (xiSliceLogDeriv t R).im = 0
      ∧ Real.log (R / 2) - 2 * xiLogDerivStirlingConstant ≤ (xiSliceLogDeriv t R).re
      ∧ (xiSliceLogDeriv t R).re ≤ Real.log (4 * R) + 2 * xiLogDerivStirlingConstant := by
  set s : ℂ := 1 / 2 + (R : ℂ) + (t : ℂ) * I with hs
  have hc : (1 / 2 : ℂ) + (R : ℂ) - (t : ℂ) * I = (starRingEnd ℂ) s := by
    rw [hs]; apply Complex.ext <;> simp
  have hL : xiSliceLogDeriv t R = logDeriv xi s + (starRingEnd ℂ) (logDeriv xi s) := by
    unfold xiSliceLogDeriv; rw [hc, logDeriv_xi_conj_xiLogDerivSymmetry]
  have hsre : s.re = 1 / 2 + R := by simp [hs]
  have hsim : s.im = t := by simp [hs]
  have h1 : R ≤ ‖s‖ := by
    have := Complex.re_le_norm s; rw [hsre] at this; linarith
  have h2 : ‖s‖ ≤ 8 * R := by
    refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
    rw [hsre, hsim, abs_of_pos (by linarith), abs_of_nonneg ht0]; linarith
  obtain ⟨-, hlo, hhi⟩ := logDeriv_xi_annulus_bounds (s := s) (m₁ := R) (m₂ := 8 * R)
    (by rw [hsre]; linarith) (by linarith) h1 h2
  rw [hL]
  have hre : (logDeriv xi s + (starRingEnd ℂ) (logDeriv xi s)).re = 2 * (logDeriv xi s).re := by
    simp; ring
  have him : (logDeriv xi s + (starRingEnd ℂ) (logDeriv xi s)).im = 0 := by simp
  rw [hre, him]
  have e : 8 * R / 2 = 4 * R := by ring
  rw [e] at hhi
  refine ⟨rfl, by linarith, by linarith⟩

/-- The large-radius disc constant. -/
def xiSliceDiscConstantLarge (R : ℝ) : ℝ :=
  (Real.log (4 * R) + Real.pi / 2 + 2 * xiLogDerivStirlingConstant) / 2
    + (Real.log 16 + Real.pi + 4 * xiLogDerivStirlingConstant)

/-- **Saddle-arc control on a large circle.**  For `R ≥ 8`, `0 ≤ t ≤ 5R`, `0 ≤ θ ≤ 1/4`. -/
theorem xiSlice_saddleArc_bounds_large {t R θ : ℝ} (hR : 8 ≤ R) (ht0 : 0 ≤ t) (htR : t ≤ 5 * R)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 4) :
    ‖HTGeometry.saddleArc (xiSliceProduct t) R
        (HTGeometry.scaledLogDeriv (xiSliceProduct t) R).re θ‖
        ≤ Real.exp (-((deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re * R
            * (1 - Real.cos θ)) + 32 * (R * xiSliceDiscConstantLarge R) / (R / 2) ^ 2 * R ^ 2 * θ ^ 3 / 3)
      ∧ (|(deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re| * R * θ ^ 3 / 6
            + 32 * (R * xiSliceDiscConstantLarge R) / (R / 2) ^ 2 * R ^ 2 * θ ^ 3 / 3
            ≤ Real.pi / 2 →
        Real.exp (-((deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re * R
            * (1 - Real.cos θ)) - 32 * (R * xiSliceDiscConstantLarge R) / (R / 2) ^ 2 * R ^ 2 * θ ^ 3 / 3)
          * Real.cos (|(deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re| * R * θ ^ 3 / 6
            + 32 * (R * xiSliceDiscConstantLarge R) / (R / 2) ^ 2 * R ^ 2 * θ ^ 3 / 3)
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
    obtain ⟨h1, h2⟩ := xiSliceLogDeriv_disc_bounds_large hR ht0 htR hw
    have hwR : ‖w - R‖ ≤ R / 2 := by rwa [mem_closedBall, dist_eq_norm] at hw
    have e : w * xiSliceLogDeriv t w - R * xiSliceLogDeriv t R
        = (w - R) * xiSliceLogDeriv t w + R * (xiSliceLogDeriv t w - xiSliceLogDeriv t R) := by ring
    rw [e]
    calc _ ≤ ‖(w - R) * xiSliceLogDeriv t w‖ + ‖(R : ℂ) * (xiSliceLogDeriv t w - xiSliceLogDeriv t R)‖ :=
          norm_add_le _ _
      _ = ‖w - R‖ * ‖xiSliceLogDeriv t w‖ + R * ‖xiSliceLogDeriv t w - xiSliceLogDeriv t R‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      _ ≤ R / 2 * (Real.log (4 * R) + Real.pi / 2 + 2 * xiLogDerivStirlingConstant)
          + R * (Real.log 16 + Real.pi + 4 * xiLogDerivStirlingConstant) := by gcongr
      _ = R * xiSliceDiscConstantLarge R := by unfold xiSliceDiscConstantLarge; ring
  · intro x hx
    have hx' : 1 / 2 < ((x : ℂ)).re := hx
    exact im_scaledLogDeriv_xiSliceProduct_ofReal (by simpa using hx')
  · exact hθ0
  · nlinarith

/-- **The saddle slope on a large circle.** -/
theorem xiSlice_saddleSlope_bounds_large {t R : ℝ} (hR : 8 ≤ R) (ht0 : 0 ≤ t) (htR : t ≤ 5 * R) :
    Real.log (R / 2) - 2 * xiLogDerivStirlingConstant
        - 2 * (Real.log 16 + Real.pi + 4 * xiLogDerivStirlingConstant)
      ≤ (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re
    ∧ (deriv (HTGeometry.scaledLogDeriv (xiSliceProduct t)) R).re
      ≤ Real.log (4 * R) + 2 * xiLogDerivStirlingConstant
        + 2 * (Real.log 16 + Real.pi + 4 * xiLogDerivStirlingConstant) := by
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
      ≤ (Real.log 16 + Real.pi + 4 * xiLogDerivStirlingConstant) / (R / 2) :=
    HTGeometry.norm_deriv_le_of_norm_sub_le hLd (c := (R : ℂ)) (by linarith) hball
      (fun z hz => (xiSliceLogDeriv_disc_bounds_large hR ht0 htR (sphere_subset_closedBall hz)).2)
  obtain ⟨-, hlo, hhi⟩ := xiSliceLogDeriv_real_bounds_large hR ht0 htR
  have hRd : |(R * deriv (xiSliceLogDeriv t) R : ℂ).re|
      ≤ 2 * (Real.log 16 + Real.pi + 4 * xiLogDerivStirlingConstant) := by
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    calc R * ‖deriv (xiSliceLogDeriv t) R‖
        ≤ R * ((Real.log 16 + Real.pi + 4 * xiLogDerivStirlingConstant) / (R / 2)) := by gcongr
      _ = 2 * (Real.log 16 + Real.pi + 4 * xiLogDerivStirlingConstant) := by field_simp
  rw [hderiv, Complex.add_re]
  have := abs_le.mp hRd
  constructor <;> linarith [this.1, this.2]

/-- **Symmetric split of `|Γ|` away from the imaginary axis.**  For `2 ≤ X₁ ≤ X₀` and any `Y, d`,
`log|Γ(X₁+i(Y+d))| + log|Γ(X₁+i(Y−d))| − 2 log|Γ(X₀+iY)| ≤ −2(X₀−X₁) log|X₁+iY| + 6(X₀−X₁+|d|)/X₁`;
both segments stay in `Re ≥ X₁`, so the Stirling difference applies with `m = X₁`. -/
theorem log_norm_Gamma_split_le_of_re {X₀ X₁ Y d : ℝ} (hX₁ : 2 ≤ X₁) (hX : X₁ ≤ X₀) :
    Real.log ‖Complex.Gamma ((X₁ : ℂ) + ((Y + d : ℝ) : ℂ) * I)‖
      + Real.log ‖Complex.Gamma ((X₁ : ℂ) + ((Y - d : ℝ) : ℂ) * I)‖
      - 2 * Real.log ‖Complex.Gamma ((X₀ : ℂ) + (Y : ℂ) * I)‖
      ≤ -2 * (X₀ - X₁) * Real.log ‖(X₁ : ℂ) + (Y : ℂ) * I‖ + 6 * (X₀ - X₁ + |d|) / X₁ := by
  have seg : ∀ e : ℝ,
      |(Real.log ‖Complex.Gamma ((X₁ : ℂ) + ((Y + e : ℝ) : ℂ) * I)‖
          - Real.log ‖Complex.Gamma ((X₀ : ℂ) + (Y : ℂ) * I)‖)
        - (HTGeometry.stirlingRe X₁ (Y + e) - HTGeometry.stirlingRe X₀ Y)|
        ≤ 3 * (X₀ - X₁ + |e|) / X₁ := by
    intro e
    have hseg : ∀ l ∈ Set.Icc (0 : ℝ) 1,
        0 < ((X₀ : ℂ) + (Y : ℂ) * I + (l : ℂ) *
          (((X₁ : ℂ) + ((Y + e : ℝ) : ℂ) * I) - ((X₀ : ℂ) + (Y : ℂ) * I))).re ∧
        X₁ ≤ ‖(X₀ : ℂ) + (Y : ℂ) * I + (l : ℂ) *
          (((X₁ : ℂ) + ((Y + e : ℝ) : ℂ) * I) - ((X₀ : ℂ) + (Y : ℂ) * I))‖ := by
      intro l hl
      obtain ⟨hl0, hl1⟩ := hl
      have hre : ((X₀ : ℂ) + (Y : ℂ) * I + (l : ℂ) *
          (((X₁ : ℂ) + ((Y + e : ℝ) : ℂ) * I) - ((X₀ : ℂ) + (Y : ℂ) * I))).re
          = X₀ + l * (X₁ - X₀) := by simp
      have hge : X₁ ≤ X₀ + l * (X₁ - X₀) := by nlinarith
      refine ⟨by rw [hre]; linarith, ?_⟩
      exact le_trans (by rw [hre]; exact hge) (Complex.re_le_norm _)
    have hS := HTGeometry.abs_log_norm_Gamma_sub_stirlingMain_le hX₁ hseg
    have hnorm : ‖((X₁ : ℂ) + ((Y + e : ℝ) : ℂ) * I) - ((X₀ : ℂ) + (Y : ℂ) * I)‖
        ≤ X₀ - X₁ + |e| := by
      have : ((X₁ : ℂ) + ((Y + e : ℝ) : ℂ) * I) - ((X₀ : ℂ) + (Y : ℂ) * I)
          = ((X₁ - X₀ : ℝ) : ℂ) + ((e : ℝ) : ℂ) * I := by push_cast; ring
      rw [this, Complex.norm_add_mul_I]
      have := Real.sqrt_le_sqrt (show (X₁ - X₀) ^ 2 + e ^ 2 ≤ (X₀ - X₁ + |e|) ^ 2 by
        nlinarith [abs_nonneg e, sq_abs e])
      rwa [Real.sqrt_sq (by linarith [abs_nonneg e])] at this
    calc _ ≤ 3 * ‖((X₁ : ℂ) + ((Y + e : ℝ) : ℂ) * I) - ((X₀ : ℂ) + (Y : ℂ) * I)‖ / X₁ := by
            simpa [HTGeometry.stirlingRe] using hS
      _ ≤ 3 * (X₀ - X₁ + |e|) / X₁ := by gcongr
  have hp := seg d
  have hm' := seg (-d)
  rw [abs_neg] at hm'
  have hsub : Y + -d = Y - d := by ring
  rw [hsub] at hm'
  have hmain := HTGeometry.stirlingRe_split_le (Y := Y) (d := d) (by linarith) hX
  have e6 : 3 * (X₀ - X₁ + |d|) / X₁ + 3 * (X₀ - X₁ + |d|) / X₁ = 6 * (X₀ - X₁ + |d|) / X₁ := by
    ring
  have ha := (abs_le.mp hp).2
  have hb := (abs_le.mp hm').2
  linarith

/-- Quadratic factors near the real point: with `s₀ = ½+R+it`, `s_{1,2} = s₀ + (a−R) ± ic` and
`|(a−R)+ic| ≤ ρ`, `|s₁(s₁−1)/2| |s₂(s₂−1)/2| ≤ |s₀(s₀−1)/2|² (1+ρ/R)²(1+2ρ/R)²` for `R ≥ 1`. -/
theorem norm_quadratic_near_le {t R a c ρ : ℝ} (hR : 1 ≤ R)
    (hρ : ‖((a - R : ℝ) : ℂ) + (c : ℂ) * I‖ ≤ ρ) :
    ‖(((1 / 2 + a : ℝ) : ℂ) + ((t + c : ℝ) : ℂ) * I) * ((((1 / 2 + a : ℝ) : ℂ)
        + ((t + c : ℝ) : ℂ) * I) - 1) / 2‖
      * ‖(((1 / 2 + a : ℝ) : ℂ) + ((t - c : ℝ) : ℂ) * I) * ((((1 / 2 + a : ℝ) : ℂ)
        + ((t - c : ℝ) : ℂ) * I) - 1) / 2‖
      ≤ ‖(((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I) * ((((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I) - 1) / 2‖ ^ 2
        * ((1 + ρ / R) ^ 2 * (1 + 2 * ρ / R) ^ 2) := by
  simp only [norm_mul_sub_one_div_two]
  set s₀ : ℂ := ((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I with hs₀
  have hR0 : 0 < R := by linarith
  have hρ0 : 0 ≤ ρ := le_trans (norm_nonneg _) hρ
  have hd1 : ((1 / 2 + a : ℝ) : ℂ) + ((t + c : ℝ) : ℂ) * I = s₀ + (((a - R : ℝ) : ℂ) + (c : ℂ) * I) := by
    rw [hs₀]; push_cast; ring
  have hd2 : ((1 / 2 + a : ℝ) : ℂ) + ((t - c : ℝ) : ℂ) * I
      = s₀ + (starRingEnd ℂ) (((a - R : ℝ) : ℂ) + (c : ℂ) * I) := by
    rw [hs₀]; apply Complex.ext <;> simp; ring
  have hρ' : ‖(starRingEnd ℂ) (((a - R : ℝ) : ℂ) + (c : ℂ) * I)‖ ≤ ρ := by rwa [Complex.norm_conj]
  have hs₀re : s₀.re = 1 / 2 + R := by rw [hs₀, re_ofReal_add_ofReal_mul_I_eq]
  have hs₀R : R ≤ ‖s₀‖ := by
    have := Complex.re_le_norm s₀; rw [hs₀re] at this; linarith
  have hs₀1 : R / 2 ≤ ‖s₀ - 1‖ := by
    have := Complex.re_le_norm (s₀ - 1)
    rw [Complex.sub_re, hs₀re, Complex.one_re] at this; linarith
  have b1 : ∀ δ : ℂ, ‖δ‖ ≤ ρ → ‖s₀ + δ‖ ≤ ‖s₀‖ * (1 + ρ / R) := by
    intro δ hδ
    have : ρ ≤ ‖s₀‖ * (ρ / R) := by
      rw [mul_div_assoc']; rw [le_div_iff₀ hR0]; nlinarith
    calc ‖s₀ + δ‖ ≤ ‖s₀‖ + ‖δ‖ := norm_add_le _ _
      _ ≤ ‖s₀‖ + ρ := by linarith
      _ ≤ ‖s₀‖ * (1 + ρ / R) := by nlinarith
  have b2 : ∀ δ : ℂ, ‖δ‖ ≤ ρ → ‖s₀ + δ - 1‖ ≤ ‖s₀ - 1‖ * (1 + 2 * ρ / R) := by
    intro δ hδ
    have : ρ ≤ ‖s₀ - 1‖ * (2 * ρ / R) := by
      rw [mul_div_assoc']; rw [le_div_iff₀ hR0]; nlinarith
    calc ‖s₀ + δ - 1‖ = ‖(s₀ - 1) + δ‖ := by ring_nf
      _ ≤ ‖s₀ - 1‖ + ‖δ‖ := norm_add_le _ _
      _ ≤ ‖s₀ - 1‖ + ρ := by linarith
      _ ≤ ‖s₀ - 1‖ * (1 + 2 * ρ / R) := by nlinarith
  rw [hd1, hd2]
  have e1 := b1 _ hρ
  have e2 := b2 _ hρ
  have e3 := b1 _ hρ'
  have e4 := b2 _ hρ'
  have hp1 : 0 ≤ 1 + ρ / R := by positivity
  have hp2 : 0 ≤ 1 + 2 * ρ / R := by positivity
  calc ‖s₀ + (((a - R : ℝ) : ℂ) + (c : ℂ) * I)‖ * ‖s₀ + (((a - R : ℝ) : ℂ) + (c : ℂ) * I) - 1‖ / 2
        * (‖s₀ + (starRingEnd ℂ) (((a - R : ℝ) : ℂ) + (c : ℂ) * I)‖
          * ‖s₀ + (starRingEnd ℂ) (((a - R : ℝ) : ℂ) + (c : ℂ) * I) - 1‖ / 2)
      ≤ (‖s₀‖ * (1 + ρ / R)) * (‖s₀ - 1‖ * (1 + 2 * ρ / R)) / 2
        * ((‖s₀‖ * (1 + ρ / R)) * (‖s₀ - 1‖ * (1 + 2 * ρ / R)) / 2) := by
        gcongr
    _ = (‖s₀‖ * ‖s₀ - 1‖ / 2) ^ 2 * ((1 + ρ / R) ^ 2 * (1 + 2 * ρ / R) ^ 2) := by ring

/-- **Assembly of the four factors of `ξ`.**  Bounds for the quadratic, archimedean and `ζ` factors
of `ξ` at two points against a reference point combine into a bound for `|ξ(s₁)| |ξ(s₂)|`. -/
theorem norm_xi_mul_le_of_factors {s₀ s₁ s₂ : ℂ} (h₀ : 0 < s₀.re) (h₀' : s₀ ≠ 1)
    (h₁ : 0 < s₁.re) (h₁' : s₁ ≠ 1) (h₂ : 0 < s₂.re) (h₂' : s₂ ≠ 1)
    {eP eG eπ B m₀ : ℝ} (hm₀ : 0 < m₀) (hz₀ : m₀ ≤ ‖riemannZeta s₀‖)
    (hz₁ : ‖riemannZeta s₁‖ ≤ B) (hz₂ : ‖riemannZeta s₂‖ ≤ B)
    (hP : ‖s₁ * (s₁ - 1) / 2‖ * ‖s₂ * (s₂ - 1) / 2‖ ≤ ‖s₀ * (s₀ - 1) / 2‖ ^ 2 * eP)
    (hG : ‖Complex.Gamma (s₁ / 2)‖ * ‖Complex.Gamma (s₂ / 2)‖ ≤ ‖Complex.Gamma (s₀ / 2)‖ ^ 2 * eG)
    (hπ : Real.pi ^ (-(s₁.re / 2)) * Real.pi ^ (-(s₂.re / 2)) ≤ (Real.pi ^ (-(s₀.re / 2))) ^ 2 * eπ)
    (heP : 0 ≤ eP) (heG : 0 ≤ eG) (heπ : 0 ≤ eπ) :
    ‖xi s₁‖ * ‖xi s₂‖ ≤ ‖xi s₀‖ ^ 2 * (B / m₀) ^ 2 * (eP * eG * eπ) := by
  rw [norm_xi_eq_factors h₀ h₀', norm_xi_eq_factors h₁ h₁', norm_xi_eq_factors h₂ h₂']
  set P₀ := ‖s₀ * (s₀ - 1) / 2‖
  set P₁ := ‖s₁ * (s₁ - 1) / 2‖
  set P₂ := ‖s₂ * (s₂ - 1) / 2‖
  set G₀ := ‖Complex.Gamma (s₀ / 2)‖
  set G₁ := ‖Complex.Gamma (s₁ / 2)‖
  set G₂ := ‖Complex.Gamma (s₂ / 2)‖
  set q₀ := Real.pi ^ (-(s₀.re / 2))
  set q₁ := Real.pi ^ (-(s₁.re / 2))
  set q₂ := Real.pi ^ (-(s₂.re / 2))
  set Z₀ := ‖riemannZeta s₀‖
  set Z₁ := ‖riemannZeta s₁‖
  set Z₂ := ‖riemannZeta s₂‖
  have hB : 0 ≤ B := le_trans (norm_nonneg _) hz₁
  have hZ : Z₁ * Z₂ ≤ B ^ 2 := by rw [sq]; exact mul_le_mul hz₁ hz₂ (norm_nonneg _) hB
  have hq₁ : 0 ≤ q₁ := (Real.rpow_pos_of_pos Real.pi_pos _).le
  have hq₂ : 0 ≤ q₂ := (Real.rpow_pos_of_pos Real.pi_pos _).le
  have hlhs : P₁ * (q₁ * G₁) * Z₁ * (P₂ * (q₂ * G₂) * Z₂)
      = (P₁ * P₂) * (q₁ * q₂) * (G₁ * G₂) * (Z₁ * Z₂) := by ring
  rw [hlhs]
  have hm2 : m₀ ^ 2 ≤ Z₀ ^ 2 := by gcongr
  calc (P₁ * P₂) * (q₁ * q₂) * (G₁ * G₂) * (Z₁ * Z₂)
      ≤ (P₀ ^ 2 * eP) * (q₀ ^ 2 * eπ) * (G₀ ^ 2 * eG) * B ^ 2 := by
        have h0 : 0 ≤ q₀ ^ 2 * eπ := mul_nonneg (sq_nonneg _) heπ
        have h1 : 0 ≤ G₀ ^ 2 * eG := mul_nonneg (sq_nonneg _) heG
        have h2 : 0 ≤ P₀ ^ 2 * eP := mul_nonneg (sq_nonneg _) heP
        apply mul_le_mul _ hZ (by positivity) (mul_nonneg (mul_nonneg h2 h0) h1)
        apply mul_le_mul _ hG (by positivity) (mul_nonneg h2 h0)
        exact mul_le_mul hP hπ (mul_nonneg hq₁ hq₂) h2
    _ = (P₀ * (q₀ * G₀)) ^ 2 * m₀ ^ 2 * ((B / m₀) ^ 2 * (eP * eG * eπ)) := by
        rw [div_pow]; field_simp
    _ ≤ (P₀ * (q₀ * G₀)) ^ 2 * Z₀ ^ 2 * ((B / m₀) ^ 2 * (eP * eG * eπ)) := by
        have : 0 ≤ (B / m₀) ^ 2 * (eP * eG * eπ) := by positivity
        gcongr
    _ = (P₀ * (q₀ * G₀) * Z₀) ^ 2 * (B / m₀) ^ 2 * (eP * eG * eπ) := by ring

/-- Gamma factor on a split away from the imaginary axis, multiplicative form: for
`4 ≤ a ≤ R`, `|Γ(s₁/2)||Γ(s₂/2)| ≤ |Γ(s₀/2)|² exp(−(R−a) log((½+a)/2) + 6(R−a+|c|)/(½+a))`. -/
theorem norm_Gamma_half_split_le_large {t R a c : ℝ} (ha4 : 4 ≤ a) (haR : a ≤ R) :
    ‖Complex.Gamma ((((1 / 2 + a : ℝ) : ℂ) + ((t + c : ℝ) : ℂ) * I) / 2)‖
      * ‖Complex.Gamma ((((1 / 2 + a : ℝ) : ℂ) + ((t - c : ℝ) : ℂ) * I) / 2)‖
      ≤ ‖Complex.Gamma ((((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I) / 2)‖ ^ 2
        * Real.exp (-(R - a) * Real.log ((1 / 2 + a) / 2) + 6 * (R - a + |c|) / (1 / 2 + a)) := by
  have e₀ : (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I) / 2
      = (((1 / 2 + R) / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by push_cast; ring
  have e₁ : (((1 / 2 + a : ℝ) : ℂ) + ((t + c : ℝ) : ℂ) * I) / 2
      = (((1 / 2 + a) / 2 : ℝ) : ℂ) + ((t / 2 + c / 2 : ℝ) : ℂ) * I := by push_cast; ring
  have e₂ : (((1 / 2 + a : ℝ) : ℂ) + ((t - c : ℝ) : ℂ) * I) / 2
      = (((1 / 2 + a) / 2 : ℝ) : ℂ) + ((t / 2 - c / 2 : ℝ) : ℂ) * I := by push_cast; ring
  rw [e₀, e₁, e₂]
  have hsplit := log_norm_Gamma_split_le_of_re (X₀ := (1 / 2 + R) / 2) (X₁ := (1 / 2 + a) / 2)
    (Y := t / 2) (d := c / 2) (by linarith) (by linarith)
  have hX₁ : 0 < (1 / 2 + a) / 2 := by linarith
  have hlogX : Real.log ((1 / 2 + a) / 2)
      ≤ Real.log ‖(((1 / 2 + a) / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I‖ := by
    apply Real.log_le_log hX₁
    have := Complex.re_le_norm ((((1 / 2 + a) / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)
    rwa [re_ofReal_add_ofReal_mul_I_eq] at this
  have hRa : 0 ≤ (1 / 2 + R) / 2 - (1 / 2 + a) / 2 := by linarith
  have hmain : -2 * ((1 / 2 + R) / 2 - (1 / 2 + a) / 2)
      * Real.log ‖(((1 / 2 + a) / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I‖
      ≤ -(R - a) * Real.log ((1 / 2 + a) / 2) := by
    have := mul_le_mul_of_nonneg_left hlogX hRa
    nlinarith
  have herr : 6 * ((1 / 2 + R) / 2 - (1 / 2 + a) / 2 + |c / 2|) / ((1 / 2 + a) / 2)
      = 6 * (R - a + |c|) / (1 / 2 + a) := by
    rw [abs_div, abs_two]; field_simp; ring
  set G₀ := ‖Complex.Gamma ((((1 / 2 + R) / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I)‖
  set G₁ := ‖Complex.Gamma ((((1 / 2 + a) / 2 : ℝ) : ℂ) + ((t / 2 + c / 2 : ℝ) : ℂ) * I)‖
  set G₂ := ‖Complex.Gamma ((((1 / 2 + a) / 2 : ℝ) : ℂ) + ((t / 2 - c / 2 : ℝ) : ℂ) * I)‖
  have hpos : ∀ x y : ℝ, 0 < x → 0 < ‖Complex.Gamma ((x : ℂ) + (y : ℂ) * I)‖ := fun x y hx =>
    norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by simpa using hx))
  have hG₀ : 0 < G₀ := hpos _ _ (by linarith)
  have hG₁ : 0 < G₁ := hpos _ _ hX₁
  have hG₂ : 0 < G₂ := hpos _ _ hX₁
  set E := -(R - a) * Real.log ((1 / 2 + a) / 2) + 6 * (R - a + |c|) / (1 / 2 + a)
  calc G₁ * G₂ = Real.exp (Real.log G₁ + Real.log G₂) := by
        rw [Real.exp_add, Real.exp_log hG₁, Real.exp_log hG₂]
    _ ≤ Real.exp (2 * Real.log G₀ + E) := Real.exp_le_exp.mpr (by linarith)
    _ = G₀ ^ 2 * Real.exp E := by
        rw [Real.exp_add, show 2 * Real.log G₀ = Real.log (G₀ ^ 2) by
          rw [Real.log_pow]; push_cast; ring, Real.exp_log (by positivity)]

/-- **Near arc of a large circle.**  For `R ≥ 8`, every height `t` and `0 ≤ θ ≤ π/3`,
`|g_t(Re^{iθ})| ≤ g_t(R) · 16 · exp(−R(1−cos θ) log(R/4π) + 12(1−cos θ+sin θ) + 6θ)`. -/
theorem norm_xiSliceProduct_circle_le_large {t R θ : ℝ} (hR : 8 ≤ R)
    (hθ0 : 0 ≤ θ) (hθ : θ ≤ Real.pi / 3) :
    ‖xiSliceProduct t ((R : ℂ) * Complex.exp ((θ : ℂ) * I))‖
      ≤ ‖xiSliceProduct t (R : ℂ)‖ * 16
        * Real.exp (-(R * (1 - Real.cos θ)) * Real.log (R / (4 * Real.pi))
          + 12 * (1 - Real.cos θ + Real.sin θ) + 6 * θ) := by
  have hR0 : 0 < R := by linarith
  have hcos : 1 / 2 ≤ Real.cos θ := by
    rw [← Real.cos_pi_div_three]
    exact Real.cos_le_cos_of_nonneg_of_le_pi hθ0 (by linarith [Real.pi_pos]) hθ
  have hsin : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith [Real.pi_pos])
  have hcos1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  set a := R * Real.cos θ with ha
  set c := R * Real.sin θ with hc
  have ha4 : 4 ≤ a := by rw [ha]; nlinarith
  have haR : a ≤ R := by rw [ha]; nlinarith
  rw [ofReal_mul_exp_mul_I, norm_xiSliceProduct_eq, norm_xiSliceProduct_real]
  set s₀ : ℂ := ((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I with hs₀
  set s₁ : ℂ := ((1 / 2 + a : ℝ) : ℂ) + ((t + c : ℝ) : ℂ) * I with hs₁
  set s₂ : ℂ := ((1 / 2 + a : ℝ) : ℂ) + ((t - c : ℝ) : ℂ) * I with hs₂
  have hr₀ : s₀.re = 1 / 2 + R := by rw [hs₀, re_ofReal_add_ofReal_mul_I_eq]
  have hr₁ : s₁.re = 1 / 2 + a := by rw [hs₁, re_ofReal_add_ofReal_mul_I_eq]
  have hr₂ : s₂.re = 1 / 2 + a := by rw [hs₂, re_ofReal_add_ofReal_mul_I_eq]
  have hne : ∀ s : ℂ, 2 ≤ s.re → s ≠ 1 := fun s h h1 => by rw [h1] at h; norm_num at h
  have hz2 : ∀ s : ℂ, 2 ≤ s.re → ‖riemannZeta s‖ ≤ 2 := fun s h => by
    have := norm_riemannZeta_le_of_two_le_re h
    nlinarith [Real.pi_lt_d2, Real.pi_pos]
  -- the quadratic factor
  have hρ : ‖((a - R : ℝ) : ℂ) + (c : ℂ) * I‖ ≤ R * θ := by
    have e : ((a - R : ℝ) : ℂ) + (c : ℂ) * I = (R : ℂ) * (Complex.exp ((θ : ℂ) * I) - 1) := by
      rw [mul_sub, ofReal_mul_exp_mul_I, ha, hc]; push_cast; ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0]
    have := HTGeometry.norm_exp_ofReal_mul_I_sub_one_le_abs θ
    rw [abs_of_nonneg hθ0] at this
    exact mul_le_mul_of_nonneg_left this hR0.le
  have hP := norm_quadratic_near_le (t := t) (by linarith) hρ
  have hθR : R * θ / R = θ := by field_simp
  have hθR2 : 2 * (R * θ) / R = 2 * θ := by field_simp
  rw [hθR, hθR2] at hP
  have haR2 : R / 2 ≤ a := by rw [ha]; nlinarith
  -- the Gamma factor
  have hG := norm_Gamma_half_split_le_large (t := t) (c := c) ha4 haR
  -- the π factor
  have hπ := pi_rpow_split R a
  have hπ' : Real.pi ^ (-(s₁.re / 2)) * Real.pi ^ (-(s₂.re / 2))
      ≤ (Real.pi ^ (-(s₀.re / 2))) ^ 2 * Real.exp ((R - a) * Real.log Real.pi) := by
    rw [hr₀, hr₁, hr₂]
    have e1 : -((1 / 2 + a) / 2) = -((1 / 2 + a) / 2) := rfl
    rw [hπ]
  have h := norm_xi_mul_le_of_factors (s₀ := s₀) (s₁ := s₁) (s₂ := s₂)
    (by rw [hr₀]; linarith) (hne _ (by rw [hr₀]; linarith))
    (by rw [hr₁]; linarith) (hne _ (by rw [hr₁]; linarith))
    (by rw [hr₂]; linarith) (hne _ (by rw [hr₂]; linarith))
    (by norm_num : (0 : ℝ) < 1 / 2)
    (one_half_le_norm_riemannZeta_of_three_le_re (by rw [hr₀]; linarith))
    (hz2 _ (by rw [hr₁]; linarith)) (hz2 _ (by rw [hr₂]; linarith)) hP hG hπ'
    (by positivity) (Real.exp_pos _).le (Real.exp_pos _).le
  refine h.trans ?_
  -- bound the multipliers
  have hPe : (1 + θ) ^ 2 * (1 + 2 * θ) ^ 2 ≤ Real.exp (6 * θ) := by
    have h1 : 1 + θ ≤ Real.exp θ := by linarith only [Real.add_one_le_exp θ]
    have h2 : 1 + 2 * θ ≤ Real.exp (2 * θ) := by linarith only [Real.add_one_le_exp (2 * θ)]
    calc (1 + θ) ^ 2 * (1 + 2 * θ) ^ 2 ≤ Real.exp θ ^ 2 * Real.exp (2 * θ) ^ 2 := by gcongr
      _ = Real.exp (6 * θ) := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  have hlogR : Real.log (R / 4) ≤ Real.log ((1 / 2 + a) / 2) :=
    Real.log_le_log (by positivity) (by linarith only [haR2])
  have herr : 6 * (R - a + |c|) / (1 / 2 + a) ≤ 12 * (1 - Real.cos θ + Real.sin θ) := by
    rw [abs_of_nonneg (by rw [hc]; positivity), div_le_iff₀ (by linarith only [ha4])]
    have : R - a + c = R * (1 - Real.cos θ + Real.sin θ) := by rw [ha, hc]; ring
    rw [this]
    have hq : 0 ≤ 1 - Real.cos θ + Real.sin θ := by linarith only [hcos1, hsin]
    nlinarith only [mul_le_mul_of_nonneg_left haR2 hq, hq]
  have hGe : Real.exp (-(R - a) * Real.log ((1 / 2 + a) / 2) + 6 * (R - a + |c|) / (1 / 2 + a))
      ≤ Real.exp (-(R - a) * Real.log (R / 4) + 12 * (1 - Real.cos θ + Real.sin θ)) := by
    apply Real.exp_le_exp.mpr
    have : (R - a) * Real.log (R / 4) ≤ (R - a) * Real.log ((1 / 2 + a) / 2) :=
      mul_le_mul_of_nonneg_left hlogR (by linarith only [haR])
    linarith only [this, herr]
  have hlog4 : Real.log (R / (4 * Real.pi)) = Real.log (R / 4) - Real.log Real.pi := by
    rw [← Real.log_div (by positivity) Real.pi_pos.ne']; congr 1; field_simp
  have hRa : R - a = R * (1 - Real.cos θ) := by rw [ha]; ring
  have hfinal : (1 + θ) ^ 2 * (1 + 2 * θ) ^ 2
      * Real.exp (-(R - a) * Real.log ((1 / 2 + a) / 2) + 6 * (R - a + |c|) / (1 / 2 + a))
      * Real.exp ((R - a) * Real.log Real.pi)
      ≤ Real.exp (-(R * (1 - Real.cos θ)) * Real.log (R / (4 * Real.pi))
          + 12 * (1 - Real.cos θ + Real.sin θ) + 6 * θ) := by
    calc _ ≤ Real.exp (6 * θ)
          * Real.exp (-(R - a) * Real.log (R / 4) + 12 * (1 - Real.cos θ + Real.sin θ))
          * Real.exp ((R - a) * Real.log Real.pi) := by gcongr
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add, hlog4, hRa]; congr 1; ring
  have e16 : ((2 : ℝ) / (1 / 2)) ^ 2 = 16 := by norm_num
  rw [e16]
  have hxi := sq_nonneg ‖xi s₀‖
  calc ‖xi s₀‖ ^ 2 * 16 * ((1 + θ) ^ 2 * (1 + 2 * θ) ^ 2
        * Real.exp (-(R - a) * Real.log ((1 / 2 + a) / 2) + 6 * (R - a + |c|) / (1 / 2 + a))
        * Real.exp ((R - a) * Real.log Real.pi))
      ≤ ‖xi s₀‖ ^ 2 * 16 * Real.exp (-(R * (1 - Real.cos θ)) * Real.log (R / (4 * Real.pi))
          + 12 * (1 - Real.cos θ + Real.sin θ) + 6 * θ) := by gcongr
    _ = _ := rfl

/-! ## The far arc of a large circle -/

/-- `|Γ(x+iy)| ≤ Γ(x)` for `x > 0`. -/
theorem norm_Gamma_ofReal_add_mul_I_le {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖Complex.Gamma ((x : ℂ) + y * I)‖ ≤ Real.Gamma x := by
  have h := HasSum.nonneg (fun j : ℕ => HTGeometry.gammaShiftWeight_nonneg x y (j : ℝ))
    (HTGeometry.hasSum_gammaShiftWeight hx y)
  have hΓC : 0 < ‖Complex.Gamma ((x : ℂ) + y * I)‖ :=
    norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by simp [hx]))
  have hle : Real.log ‖Complex.Gamma ((x : ℂ) + y * I)‖ ≤ Real.log (Real.Gamma x) := by linarith
  exact (Real.log_le_log_iff hΓC (Real.Gamma_pos_of_pos hx)).mp hle

/-- `log|Γ(x+iy)| ≥ log Γ(x) − ½ log(1+y²/x²) − (π/2)|y|` for `x > 0`. -/
theorem log_Gamma_sub_le_log_norm_Gamma {x : ℝ} (hx : 0 < x) (y : ℝ) :
    Real.log (Real.Gamma x) - Real.log (1 + y ^ 2 / x ^ 2) / 2 - Real.pi / 2 * |y|
      ≤ Real.log ‖Complex.Gamma ((x : ℂ) + y * I)‖ := by
  have h := (HTGeometry.log_norm_Gamma_sub_log_Gamma_bounds hx y).1
  have hw : HTGeometry.gammaShiftWeight x y 0 = Real.log (1 + y ^ 2 / x ^ 2) := by
    simp [HTGeometry.gammaShiftWeight]
  have hP : 0 ≤ HTGeometry.gammaShiftPrimitive y x := by
    unfold HTGeometry.gammaShiftPrimitive
    have h1 : 0 ≤ Real.log (1 + y ^ 2 / x ^ 2) := Real.log_nonneg (by
      have : 0 ≤ y ^ 2 / x ^ 2 := by positivity
      linarith)
    have h2 : 0 ≤ Real.arctan (x / |y|) := Real.arctan_nonneg.mpr (by positivity)
    positivity
  have hI : HTGeometry.gammaShiftIntegral x y ≤ Real.pi * |y| := by
    unfold HTGeometry.gammaShiftIntegral; linarith
  rw [hw] at h
  linarith

/-- On `[1, b]` with `b ≥ 2`, `Γ ≤ Γ(b)`. -/
theorem Gamma_le_Gamma_of_mem_Icc {u b : ℝ} (hu : 1 ≤ u) (hub : u ≤ b) (hb : 2 ≤ b) :
    Real.Gamma u ≤ Real.Gamma b := by
  have hseg : u ∈ segment ℝ (1 : ℝ) b := by
    rw [segment_eq_Icc (by linarith)]; exact ⟨hu, hub⟩
  have h := Real.convexOn_Gamma.le_on_segment (by norm_num : (1 : ℝ) ∈ Set.Ioi 0)
    (by show (0 : ℝ) < b; linarith) hseg
  rw [Real.Gamma_one] at h
  have hb1 : 1 ≤ Real.Gamma b := by
    rw [← Real.Gamma_two]
    exact Real.Gamma_strictMonoOn_Ici.monotoneOn (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hb) hb
  rwa [max_eq_right hb1] at h

/-- A bound for `|ξ|` on the compact box `[½, 2] × [−2, 2]`. -/
theorem exists_bound_xi_box : ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ σ τ : ℝ, 1 / 2 ≤ σ → σ ≤ 2 → |τ| ≤ 2 →
    ‖xi ((σ : ℂ) + (τ : ℂ) * I)‖ ≤ M₀ := by
  have hK : IsCompact ((fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * I)) ''
      (Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (-2 : ℝ) 2)) :=
    (isCompact_Icc.prod isCompact_Icc).image (by fun_prop)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn xi_differentiable.continuous.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun σ τ h1 h2 h3 => ?_⟩
  have hmem : ((σ : ℂ) + (τ : ℂ) * I) ∈ (fun p : ℝ × ℝ => ((p.1 : ℂ) + (p.2 : ℂ) * I)) ''
      (Set.Icc (1 / 2 : ℝ) 2 ×ˢ Set.Icc (-2 : ℝ) 2) :=
    ⟨(σ, τ), ⟨⟨h1, h2⟩, (abs_le.mp h3).1, (abs_le.mp h3).2⟩, rfl⟩
  exact (hM _ hmem).trans (le_max_left _ _)

/-- **Crude bound for `ξ` left of the saddle.**  For `R ≥ 8`, `½ ≤ σ ≤ ½ + R/2` and `|τ| ≤ 6R`,
`|ξ(σ+iτ)| ≤ M₀ + 49R² · 4Γ(R/4+2) · (2 + 24R)`. -/
theorem norm_xi_le_crude {M₀ : ℝ}
    (hM₀ : ∀ σ τ : ℝ, 1 / 2 ≤ σ → σ ≤ 2 → |τ| ≤ 2 → ‖xi ((σ : ℂ) + (τ : ℂ) * I)‖ ≤ M₀)
    (hM₀0 : 0 ≤ M₀) {R σ τ : ℝ} (hR : 8 ≤ R) (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 1 / 2 + R / 2)
    (hτ : |τ| ≤ 6 * R) :
    ‖xi ((σ : ℂ) + (τ : ℂ) * I)‖
      ≤ M₀ + 49 * R ^ 2 * (4 * Real.Gamma (R / 4 + 2)) * (2 + 24 * R) := by
  have hG0 : 0 ≤ Real.Gamma (R / 4 + 2) := (Real.Gamma_pos_of_pos (by linarith)).le
  by_cases hbox : σ ≤ 2 ∧ |τ| ≤ 2
  · have := hM₀ σ τ hσ1 hbox.1 hbox.2
    have : 0 ≤ 49 * R ^ 2 * (4 * Real.Gamma (R / 4 + 2)) * (2 + 24 * R) := by positivity
    linarith
  · set s : ℂ := (σ : ℂ) + (τ : ℂ) * I with hs
    have hsre : s.re = σ := by rw [hs, re_ofReal_add_ofReal_mul_I_eq]
    have hsim : s.im = τ := by simp [hs]
    have hs1 : s ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h; have him := congrArg Complex.im h
      rw [hsre] at hre; rw [hsim] at him; simp at hre him
      apply hbox; rw [him]; constructor <;> simp [hre]
    have hns : 2 ≤ ‖s‖ := by
      rcases not_and_or.mp hbox with h | h
      · push Not at h; have := Complex.re_le_norm s; rw [hsre] at this; linarith
      · push Not at h; have := Complex.abs_im_le_norm s; rw [hsim] at this; linarith
    have hns7 : ‖s‖ ≤ 7 * R := by
      refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
      rw [hsre, hsim, abs_of_pos (by linarith)]; linarith
    rw [norm_xi_eq_factors (by rw [hsre]; linarith) hs1]
    -- the quadratic factor
    have hq : ‖s * (s - 1) / 2‖ ≤ 49 * R ^ 2 := by
      rw [norm_mul_sub_one_div_two]
      have : ‖s - 1‖ ≤ ‖s‖ + 1 := by
        have := norm_sub_le s 1; simpa using this
      have h1 : ‖s‖ * ‖s - 1‖ ≤ ‖s‖ * (2 * ‖s‖) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); linarith
      nlinarith
    -- the archimedean factor
    have hpi : Real.pi ^ (-(s.re / 2)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.pi_gt_three]) (by rw [hsre]; linarith)
    have hΓ : ‖Complex.Gamma (s / 2)‖ ≤ 4 * Real.Gamma (R / 4 + 2) := by
      have e : s / 2 = ((σ / 2 : ℝ) : ℂ) + ((τ / 2 : ℝ) : ℂ) * I := by rw [hs]; push_cast; ring
      rw [e]
      have h1 := norm_Gamma_ofReal_add_mul_I_le (x := σ / 2) (by linarith) (τ / 2)
      push_cast at h1 ⊢
      have h2 : Real.Gamma (σ / 2) = Real.Gamma (σ / 2 + 1) / (σ / 2) := by
        rw [Real.Gamma_add_one (by linarith)]; field_simp
      have h3 : Real.Gamma (σ / 2 + 1) ≤ Real.Gamma (R / 4 + 2) :=
        Gamma_le_Gamma_of_mem_Icc (by linarith) (by linarith) (by linarith)
      have h4 : Real.Gamma (σ / 2 + 1) / (σ / 2) ≤ 4 * Real.Gamma (σ / 2 + 1) := by
        rw [div_le_iff₀ (by linarith)]
        have := (Real.Gamma_pos_of_pos (by linarith : (0 : ℝ) < σ / 2 + 1)).le
        nlinarith
      calc ‖Complex.Gamma (↑σ / 2 + ↑τ / 2 * I)‖ ≤ Real.Gamma (σ / 2) := h1
        _ ≤ 4 * Real.Gamma (R / 4 + 2) := by rw [h2]; linarith
    -- the zeta factor
    have hζ : ‖riemannZeta s‖ ≤ 2 + 24 * R := by
      by_cases hσ : 2 ≤ σ
      · have := norm_riemannZeta_le_of_two_le_re (s := s) (by rw [hsre]; exact hσ)
        nlinarith [Real.pi_lt_d2, Real.pi_pos]
      · push Not at hσ
        have hτ2 : 2 ≤ |τ| := by
          by_contra h; push Not at h; exact hbox ⟨hσ.le, h.le⟩
        have := norm_riemannZeta_le_of_half_le_re hσ1 hτ2
        rw [hs]; linarith
    have hΓ0 : 0 ≤ ‖Complex.Gamma (s / 2)‖ := norm_nonneg _
    calc ‖s * (s - 1) / 2‖ * (Real.pi ^ (-(s.re / 2)) * ‖Complex.Gamma (s / 2)‖) * ‖riemannZeta s‖
        ≤ 49 * R ^ 2 * (1 * (4 * Real.Gamma (R / 4 + 2))) * (2 + 24 * R) := by
          gcongr
      _ ≤ M₀ + 49 * R ^ 2 * (4 * Real.Gamma (R / 4 + 2)) * (2 + 24 * R) := by
          linarith

/-- Lower bound at the saddle point: for `R ≥ 8`, `0 ≤ t ≤ 5R`,
`log|ξ(½+R+it)| ≥ 2 log R − log 8 − ((½+R)/2) log π + log Γ((½+R)/2) − (log 26)/2 − (5π/4)R`. -/
theorem log_norm_xi_saddle_ge {t R : ℝ} (hR : 8 ≤ R) (ht0 : 0 ≤ t) (htR : t ≤ 5 * R) :
    2 * Real.log R - Real.log 8 - (1 / 2 + R) / 2 * Real.log Real.pi
      + Real.log (Real.Gamma ((1 / 2 + R) / 2)) - Real.log 26 / 2 - 5 * Real.pi / 4 * R
      ≤ Real.log ‖xi (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖ := by
  set s : ℂ := ((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I with hs
  have hsre : s.re = 1 / 2 + R := by rw [hs, re_ofReal_add_ofReal_mul_I_eq]
  have hs1 : s ≠ 1 := fun h => by rw [h] at hsre; simp at hsre; linarith
  rw [norm_xi_eq_factors (by rw [hsre]; linarith) hs1]
  have hR0 : 0 < R := by linarith
  -- quadratic factor
  have hq : R ^ 2 / 4 ≤ ‖s * (s - 1) / 2‖ := by
    rw [norm_mul_sub_one_div_two]
    have h1 : R ≤ ‖s‖ := by have := Complex.re_le_norm s; rw [hsre] at this; linarith
    have h2 : R / 2 ≤ ‖s - 1‖ := by
      have := Complex.re_le_norm (s - 1); rw [Complex.sub_re, hsre, Complex.one_re] at this
      linarith
    have := mul_le_mul h1 h2 (by linarith) (norm_nonneg _)
    linarith
  -- archimedean factor
  have hX0 : 0 < (1 / 2 + R) / 2 := by linarith
  have hΓ := log_Gamma_sub_le_log_norm_Gamma hX0 (t / 2)
  have e : s / 2 = (((1 / 2 + R) / 2 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * I := by rw [hs]; push_cast; ring
  have hlog26 : Real.log (1 + (t / 2) ^ 2 / ((1 / 2 + R) / 2) ^ 2) ≤ Real.log 26 := by
    apply Real.log_le_log (by positivity)
    have : (t / 2) ^ 2 / ((1 / 2 + R) / 2) ^ 2 ≤ 25 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  have hta : |t / 2| ≤ 5 * R / 2 := by rw [abs_of_nonneg (by linarith)]; linarith
  have hΓ' : Real.log (Real.Gamma ((1 / 2 + R) / 2)) - Real.log 26 / 2 - 5 * Real.pi / 4 * R
      ≤ Real.log ‖Complex.Gamma (s / 2)‖ := by
    rw [e]
    have := mul_le_mul_of_nonneg_left hta (by linarith [Real.pi_pos] : (0 : ℝ) ≤ Real.pi / 2)
    push_cast at hΓ ⊢
    linarith
  -- zeta factor
  have hζ : 1 / 2 ≤ ‖riemannZeta s‖ := one_half_le_norm_riemannZeta_of_three_le_re (by rw [hsre]; linarith)
  have hq0 : 0 < ‖s * (s - 1) / 2‖ := lt_of_lt_of_le (by positivity) hq
  have hπ0 : 0 < Real.pi ^ (-(s.re / 2)) := Real.rpow_pos_of_pos Real.pi_pos _
  have hΓ0 : 0 < ‖Complex.Gamma (s / 2)‖ :=
    norm_pos_iff.mpr (Complex.Gamma_ne_zero_of_re_pos (by rw [Complex.div_ofNat_re, hsre]; linarith))
  have hζ0 : 0 < ‖riemannZeta s‖ := by linarith
  rw [Real.log_mul (by positivity) hζ0.ne', Real.log_mul hq0.ne' (by positivity),
    Real.log_mul hπ0.ne' hΓ0.ne']
  have hlq : 2 * Real.log R - Real.log 4 ≤ Real.log ‖s * (s - 1) / 2‖ := by
    have : Real.log (R ^ 2 / 4) = 2 * Real.log R - Real.log 4 := by
      rw [Real.log_div (by positivity) (by norm_num), Real.log_pow]; push_cast; ring
    rw [← this]; exact Real.log_le_log (by positivity) hq
  have hlπ : Real.log (Real.pi ^ (-(s.re / 2))) = -((1 / 2 + R) / 2) * Real.log Real.pi := by
    rw [Real.log_rpow Real.pi_pos, hsre]
  have hlζ : -Real.log 2 ≤ Real.log ‖riemannZeta s‖ := by
    rw [← Real.log_inv, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]; exact Real.log_le_log (by norm_num) hζ
  have h48 : Real.log 8 = Real.log 4 + Real.log 2 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  rw [hlπ]
  linarith

/-- **Growth of `Γ` along the real axis**: for `R ≥ 8`,
`log Γ((½+R)/2) − log Γ(R/4+2) ≥ (R/4 − 7/4)(log((½+R)/2) − 1) − 3`. -/
theorem log_Gamma_growth_quarter {R : ℝ} (hR : 8 ≤ R) :
    (R / 4 - 7 / 4) * (Real.log ((1 / 2 + R) / 2) - 1) - 3
      ≤ Real.log (Real.Gamma ((1 / 2 + R) / 2)) - Real.log (Real.Gamma (R / 4 + 2)) := by
  set a := R / 4 + 2 with ha
  set b := (1 / 2 + R) / 2 with hb
  have ha2 : 2 ≤ a := by rw [ha]; linarith
  have hab : a ≤ b := by rw [ha, hb]; linarith
  have hseg : ∀ l ∈ Set.Icc (0 : ℝ) 1,
      0 < ((a : ℂ) + (l : ℂ) * ((b : ℂ) - (a : ℂ))).re ∧
        a ≤ ‖(a : ℂ) + (l : ℂ) * ((b : ℂ) - (a : ℂ))‖ := by
    intro l hl
    have hre : ((a : ℂ) + (l : ℂ) * ((b : ℂ) - (a : ℂ))).re = a + l * (b - a) := by simp
    have : a ≤ a + l * (b - a) := by nlinarith [hl.1]
    exact ⟨by rw [hre]; linarith, le_trans (by rw [hre]; exact this) (Complex.re_le_norm _)⟩
  have hS := HTGeometry.abs_log_norm_Gamma_sub_stirlingMain_le ha2 hseg
  have hnorm : ∀ x : ℝ, 0 < x → ‖Complex.Gamma (x : ℂ)‖ = Real.Gamma x := fun x hx => by
    rw [Complex.Gamma_ofReal, Complex.norm_real, Real.norm_of_nonneg (Real.Gamma_pos_of_pos hx).le]
  have hstir : ∀ x : ℝ, 0 < x → (HTGeometry.stirlingMain (x : ℂ)).re = x * Real.log x - x := by
    intro x hx
    unfold HTGeometry.stirlingMain
    rw [← Complex.ofReal_log hx.le]
    simp
  rw [hnorm a (by linarith), hnorm b (by linarith)] at hS
  have hsub : (HTGeometry.stirlingMain (b : ℂ) - HTGeometry.stirlingMain (a : ℂ)).re
      = (b * Real.log b - b) - (a * Real.log a - a) := by
    rw [Complex.sub_re, hstir b (by linarith), hstir a (by linarith)]
  rw [hsub] at hS
  have hn : ‖(b : ℂ) - (a : ℂ)‖ = b - a := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
  rw [hn] at hS
  have herr : 3 * (b - a) / a ≤ 3 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith
  have hmain : (b - a) * (Real.log b - 1) ≤ (b * Real.log b - b) - (a * Real.log a - a) := by
    have hl : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
    nlinarith
  have hba : b - a = R / 4 - 7 / 4 := by rw [ha, hb]; ring
  rw [hba] at hmain
  have := (abs_le.mp hS).1
  linarith

/-- **Far arc of a large circle.**  There is `R₁ ≥ 8` such that for `R ≥ R₁`, `0 ≤ t ≤ 5R` and
`π/3 ≤ θ ≤ π/2`, `|g_t(Re^{iθ})| ≤ g_t(R) · exp(−(R/8) log R)`.  The points `½ + R cos θ + i(t ± R sin θ)`
have abscissa at most `½ + R/2`, where `|ξ|` is at most polynomial times `Γ(R/4+2)`, while at the
saddle point `|ξ|` carries `Γ((½+R)/2)`, larger by `exp((R/4) log R − O(R))`. -/
theorem exists_far_arc_bound_large : ∃ R₁ : ℝ, 8 ≤ R₁ ∧ ∀ R t θ : ℝ, R₁ ≤ R → 0 ≤ t → t ≤ 5 * R →
    Real.pi / 3 ≤ θ → θ ≤ Real.pi / 2 →
    ‖xiSliceProduct t ((R : ℂ) * Complex.exp ((θ : ℂ) * I))‖
      ≤ ‖xiSliceProduct t (R : ℂ)‖ * Real.exp (-(R / 8) * Real.log R) := by
  obtain ⟨M₀, hM₀0, hM₀⟩ := exists_bound_xi_box
  set K := 7 + 11 / 4 + Real.log (M₀ + 1) + 240 with hK
  have hlM : 0 ≤ Real.log (M₀ + 1) := Real.log_nonneg (by linarith)
  refine ⟨max 8 (Real.exp (16 / 3 * K)), le_max_left _ _, ?_⟩
  intro R t θ hR ht0 htR hθ1 hθ2
  have hR8 : 8 ≤ R := le_trans (le_max_left _ _) hR
  have hR0 : 0 < R := by linarith
  have hlogK : 16 / 3 * K ≤ Real.log R := by
    rw [← Real.log_exp (16 / 3 * K)]
    exact Real.log_le_log (Real.exp_pos _) (le_trans (le_max_right _ _) hR)
  have hθ0 : 0 ≤ θ := by linarith [Real.pi_pos]
  have hcos0 : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], hθ2⟩
  have hcos2 : Real.cos θ ≤ 1 / 2 := by
    rw [← Real.cos_pi_div_three]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (by linarith [Real.pi_pos]) (by linarith) hθ1
  have hsin0 : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith)
  have hsin1 : Real.sin θ ≤ 1 := Real.sin_le_one θ
  rw [ofReal_mul_exp_mul_I, norm_xiSliceProduct_eq, norm_xiSliceProduct_real]
  set a := R * Real.cos θ with ha
  set c := R * Real.sin θ with hc
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have haR : a ≤ R / 2 := by rw [ha]; nlinarith
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hcR : c ≤ R := by rw [hc]; nlinarith
  set U := 49 * R ^ 2 * (4 * Real.Gamma (R / 4 + 2)) * (2 + 24 * R) with hU
  have hΓ1 : 1 ≤ Real.Gamma (R / 4 + 2) := by
    have := Gamma_le_Gamma_of_mem_Icc (u := 2) (b := R / 4 + 2) (by norm_num) (by linarith)
      (by linarith)
    rwa [Real.Gamma_two] at this
  have hU1 : 1 ≤ U := by
    rw [hU]
    have h1 : 1 ≤ 49 * R ^ 2 := by nlinarith
    have h2 : 1 ≤ 2 + 24 * R := by linarith
    have h3 : 1 ≤ 4 * Real.Gamma (R / 4 + 2) := by linarith
    calc (1 : ℝ) = 1 * 1 * 1 := by norm_num
      _ ≤ 49 * R ^ 2 * (4 * Real.Gamma (R / 4 + 2)) * (2 + 24 * R) := by gcongr
  have hx1 := norm_xi_le_crude hM₀ hM₀0 (σ := 1 / 2 + a) (τ := t + c) hR8 (by linarith)
    (by linarith) (by rw [abs_of_nonneg (by linarith)]; linarith)
  have hx2 := norm_xi_le_crude hM₀ hM₀0 (σ := 1 / 2 + a) (τ := t - c) hR8 (by linarith)
    (by linarith) (by rw [abs_le]; constructor <;> linarith)
  rw [← hU] at hx1 hx2
  -- the saddle value
  have hsad := log_norm_xi_saddle_ge (t := t) hR8 ht0 htR
  have hgrow := log_Gamma_growth_quarter hR8
  set ξ₀ := ‖xi (((1 / 2 + R : ℝ) : ℂ) + (t : ℂ) * I)‖ with hξ₀
  have hξ₀pos : 0 < ξ₀ := norm_pos_iff.mpr (xi_ne_zero_of_one_lt_re (by
    rw [re_ofReal_add_ofReal_mul_I_eq]; linarith))
  have hV : M₀ + U ≤ (M₀ + 1) * U := by nlinarith
  have hlogU : Real.log U = Real.log 196 + 2 * Real.log R + Real.log (Real.Gamma (R / 4 + 2))
      + Real.log (2 + 24 * R) := by
    have hG0 : 0 < Real.Gamma (R / 4 + 2) := by linarith
    rw [hU, show 49 * R ^ 2 * (4 * Real.Gamma (R / 4 + 2)) * (2 + 24 * R)
      = 196 * R ^ 2 * Real.Gamma (R / 4 + 2) * (2 + 24 * R) by ring,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) hG0.ne',
      Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast; ring
  -- crude numerical facts
  have hl196 : Real.log 196 ≤ 195 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 196)]
  have hl26 : Real.log 26 ≤ 25 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 26)]
  have hl8 : Real.log 8 ≤ 7 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8)]
  have hl8' : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hl26' : 0 ≤ Real.log 26 := Real.log_nonneg (by norm_num)
  have hlπ : Real.log Real.pi ≤ 3 := by
    linarith [Real.log_le_sub_one_of_pos Real.pi_pos, Real.pi_lt_d2]
  have hlπ0 : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  have hl2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hlogRR : Real.log R ≤ R := by linarith [Real.log_le_sub_one_of_pos hR0]
  have hlog24 : Real.log (2 + 24 * R) ≤ Real.log 26 + Real.log R := by
    rw [← Real.log_mul (by norm_num) hR0.ne']; exact Real.log_le_log (by positivity) (by linarith)
  have hlogX : Real.log R - 1 ≤ Real.log ((1 / 2 + R) / 2) := by
    have : Real.log (R / 2) ≤ Real.log ((1 / 2 + R) / 2) := Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_div hR0.ne' (by norm_num)] at this; linarith
  have hP1 : (R / 4 - 7 / 4) * (Real.log R - 2) ≤ (R / 4 - 7 / 4) * (Real.log ((1 / 2 + R) / 2) - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hP2 : R * (16 / 3 * K) ≤ R * Real.log R := mul_le_mul_of_nonneg_left hlogK hR0.le
  have hK0 : 0 ≤ K := by rw [hK]; linarith
  -- the key logarithmic inequality
  have hkey : Real.log (M₀ + 1) + Real.log U + R / 16 * Real.log R ≤ Real.log ξ₀ := by
    rw [hlogU]
    have hπ4 : Real.pi ≤ 4 := by linarith [Real.pi_lt_d2]
    have hπR : 5 * Real.pi / 4 * R ≤ 5 * R := by
      have := mul_le_mul_of_nonneg_right hπ4 hR0.le; linarith only [this]
    have hπR2 : (1 / 2 + R) / 2 * Real.log Real.pi ≤ (1 / 2 + R) / 2 * 3 :=
      mul_le_mul_of_nonneg_left hlπ (by linarith)
    have hRlogR : R * (7 + 11 / 4) + (Real.log (M₀ + 1) + 240) ≤ R * K := by
      have h1 : (1 : ℝ) * (Real.log (M₀ + 1) + 240) ≤ R * (Real.log (M₀ + 1) + 240) :=
        mul_le_mul_of_nonneg_right (by linarith only [hR8]) (by linarith only [hlM])
      rw [hK]; linarith only [h1]
    linarith only [hsad, hgrow, hP1, hP2, hπR, hπR2, hRlogR, hlogRR, hlog24, hl196, hl26, hl8,
      hl8', hl26', hlπ0, hl2, hK0, hR8, hlM]
  -- conclude
  have hVle : M₀ + U ≤ ξ₀ * Real.exp (-(R / 16) * Real.log R) := by
    have h1 : Real.log (M₀ + U) ≤ Real.log (ξ₀ * Real.exp (-(R / 16) * Real.log R)) := by
      rw [Real.log_mul hξ₀pos.ne' (Real.exp_pos _).ne', Real.log_exp]
      have : Real.log (M₀ + U) ≤ Real.log ((M₀ + 1) * U) :=
        Real.log_le_log (by linarith only [hM₀0, hU1]) hV
      rw [Real.log_mul (by linarith only [hM₀0] : (0 : ℝ) < M₀ + 1).ne'
        (by linarith only [hU1] : (0 : ℝ) < U).ne'] at this
      linarith only [this, hkey]
    exact (Real.log_le_log_iff (by linarith only [hM₀0, hU1]) (by positivity)).mp h1
  have e : Real.exp (-(R / 8) * Real.log R) = Real.exp (-(R / 16) * Real.log R) ^ 2 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [e]
  calc ‖xi (((1 / 2 + a : ℝ) : ℂ) + ((t + c : ℝ) : ℂ) * I)‖
        * ‖xi (((1 / 2 + a : ℝ) : ℂ) + ((t - c : ℝ) : ℂ) * I)‖
      ≤ (M₀ + U) * (M₀ + U) := by
        apply mul_le_mul hx1 hx2 (norm_nonneg _) (by linarith only [hM₀0, hU1])
    _ ≤ (ξ₀ * Real.exp (-(R / 16) * Real.log R)) * (ξ₀ * Real.exp (-(R / 16) * Real.log R)) := by
        have : 0 ≤ M₀ + U := by linarith only [hM₀0, hU1]
        exact mul_le_mul hVle hVle this (by positivity)
    _ = ξ₀ ^ 2 * Real.exp (-(R / 16) * Real.log R) ^ 2 := by ring

end

end RHTower
