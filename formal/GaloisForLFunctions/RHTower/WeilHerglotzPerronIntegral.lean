import GaloisForLFunctions.RHTower.PerronLaplacePoleKernel
import GaloisForLFunctions.RHTower.WeilFullConeLocalMassBound
import GaloisForLFunctions.HTGeometry.DigammaHalfPlaneAsymptotic

/-!
# The weighted Perron integral of the Herglotz function of a Weil-positive system

Let `lam` be full-cone Weil-positive with boundary measure `μ_lam` and Herglotz function
`H(z) = ∫ (1/(z − ir) − ir/(1 + r²)) dμ_lam(r)` (`Re z > 0`).  For `Re z₀ > 0`, `c > 0`, `L ≥ 0`
and `s = c + 2πiw`,

`∫ H(z₀ + s) e^{sL}/s² dw = ∫ ((e^{bL} − 1 − bL)/b² − irL/(1 + r²)) dμ_lam(r)`,  `b = ir − z₀`

(`integral_herglotzFunction_mul_perron`).  Each atom of `μ_lam` contributes the residues of
`e^{sL}/(s²(s − b))` at `s = b` and at the double pole `s = 0`, exactly as a zero of `ζ` does in
the classical explicit formula; no continuation past the critical line is used.

**Proof.**  Fubini, for which the only input is a sublinear bound on the kernel mass along the
contour.  With `a = Re z`, `z = a + iτ`, the kernel difference satisfies the pointwise bound

`|1/(z − ir) − 1/(a − ir)| ≤ (4b/a)(P_b(r − τ) + P_b(r))`,  `P_b(u) = b/(b² + u²)`,

whenever `aτ ≤ 2b²` (`norm_inv_sub_inv_le`): one of `|z − ir|`, `|a − ir|` is at least `|τ|/2`.
Integrating, the kernel mass at height `τ` is at most a constant plus
`(4b/a)(Re H(b + iτ) + Re H(b))` with `b ≍ √|τ|`.  At abscissa `b ≥ 4` the Herglotz function is
the Weil function, whose real part is `½ log|s| + O(1)` by the digamma asymptotic.  So the kernel
mass is `O(|τ|^{3/4})`, integrable against `|s|^{−2}`.  The inner `w`-integral is the pole
integral of `PerronLaplacePoleKernel`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace RHTower.WeilSpectral

open WeilHerglotz PerronPole

/-! ### The kernel comparison -/

theorem le_mul_poisson_of_le {a b x u τ D : ℝ} (ha : 0 < a) (hb : 0 < b) (hax : a ≤ x)
    (hux : u ^ 2 ≤ x ^ 2) (hτ : a * |τ| ≤ 2 * b ^ 2) (hD1 : D ≤ 2 / x)
    (hD2 : D ≤ |τ| / x ^ 2) : D ≤ 4 * b / a * (b / (b ^ 2 + u ^ 2)) := by
  have hx : 0 < x := ha.trans_le hax
  rcases le_or_gt (x ^ 2) (b ^ 2) with h | h
  · calc D ≤ 2 / x := hD1
      _ ≤ 2 / a := div_le_div_of_nonneg_left (by norm_num) ha hax
      _ = 4 * b / a * (1 / (2 * b)) := by field_simp; ring
      _ ≤ 4 * b / a * (b / (b ^ 2 + u ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
  · calc D ≤ |τ| / x ^ 2 := hD2
      _ ≤ (2 * b ^ 2 / a) / x ^ 2 := by
        gcongr
        rw [le_div_iff₀ ha]; linarith
      _ = 4 * b / a * (b / (2 * x ^ 2)) := by field_simp; ring
      _ ≤ 4 * b / a * (b / (b ^ 2 + u ^ 2)) := by
        gcongr
        linarith

/-- **Kernel comparison.**  If `a τ ≤ 2b²` then
`|1/(a + iτ − ir) − 1/(a − ir)| ≤ (4b/a)(P_b(r − τ) + P_b(r))`. -/
theorem norm_inv_sub_inv_le {a b τ r : ℝ} (ha : 0 < a) (hb : 0 < b) (hτ : a * |τ| ≤ 2 * b ^ 2) :
    ‖1 / ((a : ℂ) + τ * I - I * r) - 1 / ((a : ℂ) - I * r)‖ ≤
      4 * b / a * (b / (b ^ 2 + (r - τ) ^ 2) + b / (b ^ 2 + r ^ 2)) := by
  set X : ℂ := (a : ℂ) + τ * I - I * r with hX
  set Y : ℂ := (a : ℂ) - I * r with hY
  have hXre : X.re = a := by simp [hX]
  have hYre : Y.re = a := by simp [hY]
  have hax : a ≤ ‖X‖ := hXre ▸ Complex.re_le_norm X
  have hay : a ≤ ‖Y‖ := hYre ▸ Complex.re_le_norm Y
  have hx : 0 < ‖X‖ := ha.trans_le hax
  have hy : 0 < ‖Y‖ := ha.trans_le hay
  have hX0 : X ≠ 0 := norm_pos_iff.mp hx
  have hY0 : Y ≠ 0 := norm_pos_iff.mp hy
  have hXn : ‖X‖ ^ 2 = a ^ 2 + (r - τ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [hX]; ring
  have hYn : ‖Y‖ ^ 2 = a ^ 2 + r ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp [hY]; ring
  have hnorm : ‖1 / X - 1 / Y‖ = |τ| / (‖X‖ * ‖Y‖) := by
    have hdiff : 1 / X - 1 / Y = -((τ : ℂ) * I) / (X * Y) := by
      field_simp
      simp only [hX, hY]
      ring
    rw [hdiff, norm_div, norm_neg, norm_mul, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
  have htri : |τ| ≤ ‖X‖ + ‖Y‖ := by
    have e : (τ : ℂ) * I = X - Y := by simp only [hX, hY]; ring
    have h := norm_sub_le X Y
    rwa [← e, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at h
  have hP1 : 0 ≤ b / (b ^ 2 + (r - τ) ^ 2) := by positivity
  have hP2 : 0 ≤ b / (b ^ 2 + r ^ 2) := by positivity
  have hc : 0 ≤ 4 * b / a := by positivity
  rw [hnorm]
  rcases le_total ‖X‖ ‖Y‖ with h | h
  · have hb1 := le_mul_poisson_of_le ha hb hax (u := r - τ) (by rw [hXn]; nlinarith) hτ
      (D := |τ| / (‖X‖ * ‖Y‖))
      (by
        rw [div_le_div_iff₀ (by positivity) hx]
        nlinarith [mul_le_mul_of_nonneg_right (htri.trans (by linarith : ‖X‖ + ‖Y‖ ≤ 2 * ‖Y‖))
          hx.le])
      (by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left h (mul_nonneg (abs_nonneg τ) hx.le)])
    nlinarith
  · have hb1 := le_mul_poisson_of_le ha hb hay (u := r) (by rw [hYn]; nlinarith) hτ
      (D := |τ| / (‖X‖ * ‖Y‖))
      (by
        rw [div_le_div_iff₀ (by positivity) hy]
        nlinarith [mul_le_mul_of_nonneg_right (htri.trans (by linarith : ‖X‖ + ‖Y‖ ≤ 2 * ‖X‖))
          hy.le])
      (by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_left h (mul_nonneg (abs_nonneg τ) hy.le)])
    nlinarith

theorem herglotzKernel_sub_eq (a τ r : ℝ) :
    herglotzKernel ((a : ℂ) + τ * I) r - herglotzKernel (a : ℂ) r =
      1 / ((a : ℂ) + τ * I - I * r) - 1 / ((a : ℂ) - I * r) := by
  unfold herglotzKernel; ring

theorem re_herglotzKernel_eq_poisson {b : ℝ} (hb : 0 < b) (τ r : ℝ) :
    (herglotzKernel ((b : ℂ) + τ * I) r).re = b / (b ^ 2 + (r - τ) ^ 2) := by
  have hz : 0 < ((b : ℂ) + τ * I).re := by simpa using hb
  rw [re_herglotzKernel hz]
  have hn : ‖(b : ℂ) + τ * I - I * r‖ ^ 2 = b ^ 2 + (r - τ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; ring
  rw [norm_div, norm_one, div_pow, hn]
  simp [div_eq_mul_inv]

theorem re_integral_herglotzKernel {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {z : ℂ}
    (hz : 0 < z.re) :
    ∫ r, (herglotzKernel z r).re ∂boundaryMeasure hW = (herglotzFunction hW z).re := by
  unfold herglotzFunction
  rw [← RCLike.re_eq_complex_re, ← integral_re (integrable_herglotzKernel hW hz)]

/-- **Kernel mass along a vertical line.**  For `a, b > 0` with `a|τ| ≤ 2b²`,
`∫ |K(a + iτ, r)| dμ ≤ ∫ |K(a, r)| dμ + (4b/a)(Re H(b + iτ) + Re H(b))`. -/
theorem integral_norm_herglotzKernel_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {a b τ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hτ : a * |τ| ≤ 2 * b ^ 2) :
    ∫ r, ‖herglotzKernel ((a : ℂ) + τ * I) r‖ ∂boundaryMeasure hW ≤
      ∫ r, ‖herglotzKernel (a : ℂ) r‖ ∂boundaryMeasure hW +
        4 * b / a * ((herglotzFunction hW ((b : ℂ) + τ * I)).re +
          (herglotzFunction hW (b : ℂ)).re) := by
  have hza : 0 < ((a : ℂ) + τ * I).re := by simpa using ha
  have ha' : 0 < (a : ℂ).re := by simpa using ha
  have hzb : 0 < ((b : ℂ) + τ * I).re := by simpa using hb
  have hb' : 0 < (b : ℂ).re := by simpa using hb
  have hI1 := (integrable_herglotzKernel hW ha').norm
  have hI2 : Integrable (fun r => (herglotzKernel ((b : ℂ) + τ * I) r).re)
      (boundaryMeasure hW) := (integrable_herglotzKernel hW hzb).re
  have hI3 : Integrable (fun r => (herglotzKernel (b : ℂ) r).re) (boundaryMeasure hW) :=
    (integrable_herglotzKernel hW hb').re
  have hpt : ∀ r, ‖herglotzKernel ((a : ℂ) + τ * I) r‖ ≤ ‖herglotzKernel (a : ℂ) r‖ +
      4 * b / a * ((herglotzKernel ((b : ℂ) + τ * I) r).re + (herglotzKernel (b : ℂ) r).re) := by
    intro r
    rw [re_herglotzKernel_eq_poisson hb, show (b : ℂ) = (b : ℂ) + (0 : ℝ) * I by simp,
      re_herglotzKernel_eq_poisson hb]
    have h := norm_inv_sub_inv_le (r := r) ha hb hτ
    rw [← herglotzKernel_sub_eq] at h
    have h2 := norm_sub_norm_le (herglotzKernel ((a : ℂ) + τ * I) r) (herglotzKernel (a : ℂ) r)
    simp only [sub_zero] at h ⊢
    linarith
  calc ∫ r, ‖herglotzKernel ((a : ℂ) + τ * I) r‖ ∂boundaryMeasure hW
      ≤ ∫ r, (‖herglotzKernel (a : ℂ) r‖ + 4 * b / a * ((herglotzKernel ((b : ℂ) + τ * I) r).re +
          (herglotzKernel (b : ℂ) r).re)) ∂boundaryMeasure hW :=
        integral_mono (integrable_herglotzKernel hW hza).norm
          (hI1.add ((hI2.add hI3).const_mul _)) hpt
    _ = _ := by
        have e1 : ∫ r, (‖herglotzKernel (a : ℂ) r‖ + 4 * b / a *
            ((herglotzKernel ((b : ℂ) + τ * I) r).re + (herglotzKernel (b : ℂ) r).re))
              ∂boundaryMeasure hW =
            ∫ r, ‖herglotzKernel (a : ℂ) r‖ ∂boundaryMeasure hW + ∫ r, 4 * b / a *
              ((herglotzKernel ((b : ℂ) + τ * I) r).re + (herglotzKernel (b : ℂ) r).re)
                ∂boundaryMeasure hW :=
          integral_add hI1 ((hI2.add hI3).const_mul _)
        have e2 : ∫ r, ((herglotzKernel ((b : ℂ) + τ * I) r).re + (herglotzKernel (b : ℂ) r).re)
              ∂boundaryMeasure hW =
            ∫ r, (herglotzKernel ((b : ℂ) + τ * I) r).re ∂boundaryMeasure hW +
              ∫ r, (herglotzKernel (b : ℂ) r).re ∂boundaryMeasure hW :=
          integral_add hI2 hI3
        rw [e1, integral_const_mul, e2, re_integral_herglotzKernel hW hzb,
          re_integral_herglotzKernel hW hb']

/-! ### Growth of `Re H` far to the right -/

theorem norm_LSeries_lamC_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {s : ℂ}
    (hs : 3 / 2 ≤ s.re) :
    ‖LSeries (lamC lam) s‖ ≤ ∑' n : ℕ, |lam n| / (n : ℝ) ^ (3 / 2 : ℝ) := by
  have hsum := WeilMeanSquare.summable_abs_div_rpow_of_weilPositiveFull hW
    (σ := 3 / 2) (by norm_num)
  have hbound : ∀ n : ℕ, ‖LSeries.term (lamC lam) s n‖ ≤ |lam n| / (n : ℝ) ^ (3 / 2 : ℝ) := by
    intro n
    rw [LSeries.norm_term_eq]
    split_ifs with hn
    · positivity
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hlam : ‖lamC lam n‖ ≤ |lam n| := by
        unfold lamC
        rw [Complex.norm_real, Real.norm_eq_abs]
        split_ifs
        · exact le_rfl
        · simp
      calc ‖lamC lam n‖ / (n : ℝ) ^ s.re ≤ |lam n| / (n : ℝ) ^ s.re :=
            div_le_div_of_nonneg_right hlam (by positivity)
        _ ≤ |lam n| / (n : ℝ) ^ (3 / 2 : ℝ) :=
            div_le_div_of_nonneg_left (abs_nonneg _) (by positivity)
              (Real.rpow_le_rpow_of_exponent_le hn1 hs)
  have hsn : Summable fun n => ‖LSeries.term (lamC lam) s n‖ :=
    hsum.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  exact (norm_tsum_le_tsum_norm hsn).trans (hsn.tsum_le_tsum hbound hsum)

/-- **Logarithmic growth of `Re H` to the right of abscissa `4`.**  There is `K ≥ 0` with
`Re H(v) ≤ ½ log(|v| + 1) + K` for `Re v ≥ 4`: there `H(v) = Φ_lam(v + ½) − const`, and
`Re Φ_lam(s) = ½ Re ψ(s/2) + O(1)` with `Re ψ(z) ≤ log|z| + 3/|z|`. -/
theorem exists_re_herglotzFunction_le_log {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v : ℂ, 4 ≤ v.re →
      (herglotzFunction hW v).re ≤ Real.log (‖v‖ + 1) / 2 + K := by
  set Lsum : ℝ := ∑' n : ℕ, |lam n| / (n : ℝ) ^ (3 / 2 : ℝ) with hLsum
  have hL0 : 0 ≤ Lsum := tsum_nonneg fun n => by positivity
  set C : ℂ := weilFunction lam 2 - herglotzFunction hW (2 - 1 / 2) with hC
  refine ⟨3 / 4 + |Real.log π| / 2 + 2 + Lsum + ‖C‖, by positivity, fun v hv => ?_⟩
  set s : ℂ := v + 1 / 2 with hs
  have hsre : s.re = v.re + 1 / 2 := by simp [hs]
  have hH : herglotzFunction hW v = weilFunction lam s - C := by
    have h1 : weilContinuation hW s = herglotzFunction hW v + C := by
      simp only [weilContinuation, hs, add_sub_cancel_right, hC]
    rw [← weilContinuation_eq hW (by linarith : 1 < s.re), h1]
    ring
  have hnv : 0 ≤ ‖v‖ := norm_nonneg v
  -- the digamma term
  have hs2re : 0 < (s / 2).re := by
    have : (s / 2).re = s.re / 2 := by simp
    rw [this]; linarith
  have hs2n : 2 ≤ ‖s / 2‖ := by
    have h := Complex.re_le_norm (s / 2)
    have : (s / 2).re = s.re / 2 := by simp
    linarith
  have hdig : (Complex.digamma (s / 2)).re ≤ Real.log (‖v‖ + 1) + 3 / 2 := by
    have h := GaloisForLFunctions.HTGeometry.norm_digamma_sub_log_le_of_re_pos hs2re hs2n
    have h1 : (Complex.digamma (s / 2) - Complex.log (s / 2)).re ≤ 3 / ‖s / 2‖ :=
      (Complex.re_le_norm _).trans h
    rw [Complex.sub_re, Complex.log_re] at h1
    have h2 : 3 / ‖s / 2‖ ≤ 3 / 2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs2n
    have h3 : Real.log ‖s / 2‖ ≤ Real.log (‖v‖ + 1) := by
      refine Real.log_le_log (by linarith) ?_
      rw [norm_div, Complex.norm_two]
      have := norm_add_le v (1 / 2 : ℂ)
      rw [← hs] at this
      norm_num at this
      linarith
    linarith
  have hinv : ∀ u : ℂ, 1 ≤ u.re → (1 / u).re ≤ 1 := by
    intro u hu
    have hn : 1 ≤ ‖u‖ := hu.trans (Complex.re_le_norm u)
    refine (Complex.re_le_norm _).trans ?_
    rw [norm_div, norm_one]
    exact (div_le_one (by linarith)).mpr hn
  have hp1 := hinv s (by linarith)
  have hp2 := hinv (s - 1) (by rw [Complex.sub_re, Complex.one_re]; linarith)
  have hD := norm_LSeries_lamC_le hW (s := s) (by linarith)
  have hDre : -(LSeries (lamC lam) s).re ≤ ‖LSeries (lamC lam) s‖ := by
    have := Complex.abs_re_le_norm (LSeries (lamC lam) s)
    have := neg_abs_le (LSeries (lamC lam) s).re
    linarith
  have hCre : -C.re ≤ ‖C‖ := by
    have := Complex.abs_re_le_norm C
    have := neg_abs_le C.re
    linarith
  have hpi : -(Real.log π / 2) ≤ |Real.log π| / 2 := by
    have := neg_abs_le (Real.log π); linarith
  have hWre : (weilFunction lam s).re = (Complex.digamma (s / 2)).re / 2 - Real.log π / 2 +
      (1 / s).re + (1 / (s - 1)).re - (LSeries (lamC lam) s).re := by
    unfold weilFunction
    simp only [Complex.sub_re, Complex.add_re]
    congr 3
    simp
  rw [hH, Complex.sub_re, hWre]
  linarith

theorem log_add_one_div_two_le {D y x : ℝ} (hD : 1 ≤ D) (hy : 1 ≤ y) (hx : 0 ≤ x)
    (hxD : x ≤ D * y) : Real.log (x + 1) / 2 ≤ 4 * D ^ (1 / 4 : ℝ) * y ^ (1 / 4 : ℝ) := by
  have hy0 : 0 < y := by linarith
  have hD0 : 0 < D := by linarith
  have hDy : 1 ≤ D * y := one_le_mul_of_one_le_of_one_le hD hy
  have h1 : Real.log (x + 1) ≤ Real.log (2 * D * y) := Real.log_le_log (by linarith) (by linarith)
  have h3 := Real.log_le_rpow_div (x := 2 * D * y) (by positivity) (by norm_num : (0 : ℝ) < 1 / 4)
  have e : (2 * D * y) ^ (1 / 4 : ℝ) / (1 / 4) = 4 * (2 * D * y) ^ (1 / 4 : ℝ) := by ring
  rw [e] at h3
  have h4 : (2 * D * y) ^ (1 / 4 : ℝ) ≤ 2 * (D ^ (1 / 4 : ℝ) * y ^ (1 / 4 : ℝ)) := by
    rw [Real.mul_rpow (by positivity) hy0.le, Real.mul_rpow (by norm_num) hD0.le, mul_assoc]
    have h2 : (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (1 / 4 : ℝ) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    exact mul_le_mul_of_nonneg_right h2 (by positivity)
  have : 4 * D ^ (1 / 4 : ℝ) * y ^ (1 / 4 : ℝ) = 4 * (D ^ (1 / 4 : ℝ) * y ^ (1 / 4 : ℝ)) := by
    ring
  rw [this]
  linarith

/-- **Sublinear kernel mass along a vertical line.**  For `a > 0` and `τ₀ ∈ ℝ` there is `C` with
`∫ |K(a + i(τ₀ + 2πw), r)| dμ_lam(r) ≤ C (1 + |w|)^{3/4}` for all `w`. -/
theorem exists_integral_norm_herglotzKernel_le_rpow {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {a : ℝ} (ha : 0 < a) (τ₀ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℝ,
      ∫ r, ‖herglotzKernel ((a : ℂ) + ((τ₀ + 2 * π * w : ℝ) : ℂ) * I) r‖ ∂boundaryMeasure hW ≤
        C * (1 + |w|) ^ (3 / 4 : ℝ) := by
  obtain ⟨K, hK, hKb⟩ := exists_re_herglotzFunction_le_log hW
  set K₀ : ℝ := ∫ r, ‖herglotzKernel (a : ℂ) r‖ ∂boundaryMeasure hW with hK₀
  have hK₀0 : 0 ≤ K₀ := integral_nonneg fun r => norm_nonneg _
  have hpi := Real.pi_pos
  have hτ₀ := abs_nonneg τ₀
  set B : ℝ := Real.sqrt (a * (|τ₀| + 2 * π) + 16) with hB
  have hB2 : B ^ 2 = a * (|τ₀| + 2 * π) + 16 := Real.sq_sqrt (by positivity)
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hB4 : 4 ≤ B := by
    have h16 : (16 : ℝ) ≤ B ^ 2 := by rw [hB2]; have := mul_pos ha (by positivity : (0:ℝ) < |τ₀| + 2 * π); linarith
    nlinarith
  set D : ℝ := B + |τ₀| + 2 * π + 1 with hD
  have hD1 : 1 ≤ D := by rw [hD]; linarith
  refine ⟨K₀ + 4 * B / a * (8 * D ^ (1 / 4 : ℝ) + 2 * K), by positivity, fun w => ?_⟩
  have hw := abs_nonneg w
  set y : ℝ := 1 + |w| with hy
  have hy1 : 1 ≤ y := by rw [hy]; linarith
  have hy0 : 0 < y := by linarith
  set q : ℝ := y ^ (1 / 2 : ℝ) with hq
  have hq1 : 1 ≤ q := Real.one_le_rpow hy1 (by norm_num)
  have hq2 : q ^ 2 = y := by rw [hq, ← Real.sqrt_eq_rpow, Real.sq_sqrt hy0.le]
  have hqy : q ≤ y := by nlinarith
  set b : ℝ := B * q with hbdef
  have hb4 : 4 ≤ b := by
    have := mul_le_mul hB4 hq1 (by norm_num) hB0; rw [hbdef]; linarith
  have hb0 : 0 < b := by linarith
  have hbBy : b ≤ B * y := by rw [hbdef]; exact mul_le_mul_of_nonneg_left hqy hB0
  set τ : ℝ := τ₀ + 2 * π * w with hτdef
  have hτabs : |τ| ≤ |τ₀| + 2 * π * |w| := by
    calc |τ| ≤ |τ₀| + |2 * π * w| := abs_add_le _ _
      _ = |τ₀| + 2 * π * |w| := by rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  have hτy : |τ| ≤ (|τ₀| + 2 * π) * y := by
    have e : (|τ₀| + 2 * π) * y = |τ₀| + 2 * π * |w| + (|τ₀| * |w| + 2 * π) := by rw [hy]; ring
    have : 0 ≤ |τ₀| * |w| := mul_nonneg hτ₀ hw
    linarith
  have hτ : a * |τ| ≤ 2 * b ^ 2 := by
    have hb2 : b ^ 2 = B ^ 2 * y := by rw [hbdef, mul_pow, hq2]
    have h2 : a * |τ| ≤ a * ((|τ₀| + 2 * π) * y) := mul_le_mul_of_nonneg_left hτy ha.le
    have h3 : a * ((|τ₀| + 2 * π) * y) ≤ B ^ 2 * y := by
      rw [hB2, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (by linarith) hy0.le
    have h4 : 0 ≤ b ^ 2 := sq_nonneg b
    rw [hb2] at h4 ⊢
    linarith
  have hmain := integral_norm_herglotzKernel_le hW ha hb0 hτ
  have hDy : D * y = B * y + (|τ₀| + 2 * π + 1) * y := by rw [hD]; ring
  have hv1 : (herglotzFunction hW ((b : ℂ) + τ * I)).re ≤
      4 * D ^ (1 / 4 : ℝ) * y ^ (1 / 4 : ℝ) + K := by
    refine (hKb _ (by simpa using hb4)).trans ?_
    have hn : ‖(b : ℂ) + τ * I‖ ≤ D * y := by
      have h := norm_add_le (b : ℂ) ((τ : ℂ) * I)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb0, norm_mul, Complex.norm_I,
        mul_one, Complex.norm_real, Real.norm_eq_abs] at h
      have : (|τ₀| + 2 * π) * y ≤ (|τ₀| + 2 * π + 1) * y :=
        mul_le_mul_of_nonneg_right (by linarith) hy0.le
      linarith
    linarith [log_add_one_div_two_le hD1 hy1 (norm_nonneg _) hn]
  have hv2 : (herglotzFunction hW (b : ℂ)).re ≤ 4 * D ^ (1 / 4 : ℝ) * y ^ (1 / 4 : ℝ) + K := by
    refine (hKb _ (by simpa using hb4)).trans ?_
    have hn : ‖(b : ℂ)‖ ≤ D * y := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hb0]
      have : 0 ≤ (|τ₀| + 2 * π + 1) * y := by positivity
      linarith
    linarith [log_add_one_div_two_le hD1 hy1 (norm_nonneg _) hn]
  have hy34 : 1 ≤ y ^ (3 / 4 : ℝ) := Real.one_le_rpow hy1 (by norm_num)
  have hqy34 : q * y ^ (1 / 4 : ℝ) = y ^ (3 / 4 : ℝ) := by
    rw [hq, ← Real.rpow_add hy0]; norm_num
  have hq34 : q ≤ y ^ (3 / 4 : ℝ) := by
    rw [hq]; exact Real.rpow_le_rpow_of_exponent_le hy1 (by norm_num)
  have hc : 0 ≤ 4 * b / a := by positivity
  have hBa : 0 ≤ 4 * B / a := by positivity
  have hD14 : 0 ≤ D ^ (1 / 4 : ℝ) := by positivity
  calc ∫ r, ‖herglotzKernel ((a : ℂ) + ((τ₀ + 2 * π * w : ℝ) : ℂ) * I) r‖ ∂boundaryMeasure hW
      ≤ K₀ + 4 * b / a * ((herglotzFunction hW ((b : ℂ) + τ * I)).re +
          (herglotzFunction hW (b : ℂ)).re) := hmain
    _ ≤ K₀ + 4 * b / a * (8 * D ^ (1 / 4 : ℝ) * y ^ (1 / 4 : ℝ) + 2 * K) := by
        have := mul_le_mul_of_nonneg_left (show (herglotzFunction hW ((b : ℂ) + τ * I)).re +
          (herglotzFunction hW (b : ℂ)).re ≤ 8 * D ^ (1 / 4 : ℝ) * y ^ (1 / 4 : ℝ) + 2 * K by
            linarith) hc
        linarith
    _ = K₀ + 4 * B / a * (8 * D ^ (1 / 4 : ℝ) * (q * y ^ (1 / 4 : ℝ)) + 2 * K * q) := by
        rw [hbdef]; ring
    _ ≤ K₀ * y ^ (3 / 4 : ℝ) + 4 * B / a * (8 * D ^ (1 / 4 : ℝ) * y ^ (3 / 4 : ℝ) +
          2 * K * y ^ (3 / 4 : ℝ)) := by
        rw [hqy34]
        have h1 : K₀ ≤ K₀ * y ^ (3 / 4 : ℝ) := le_mul_of_one_le_right hK₀0 hy34
        have h2 : 2 * K * q ≤ 2 * K * y ^ (3 / 4 : ℝ) :=
          mul_le_mul_of_nonneg_left hq34 (by positivity)
        gcongr
    _ = (K₀ + 4 * B / a * (8 * D ^ (1 / 4 : ℝ) + 2 * K)) * (1 + |w|) ^ (3 / 4 : ℝ) := by
        rw [hy]; ring

/-! ### Fubini -/

/-- **The weighted Perron integral of the Herglotz function.**  For `Re z₀ > 0`, `c > 0`, `L ≥ 0`
and `s = c + 2πiw`, with `b(r) = ir − z₀`:

`∫ H(z₀ + s) e^{sL}/s² dw = ∫ ((e^{bL} − 1 − bL)/b² − irL/(1 + r²)) dμ_lam(r)`. -/
theorem integral_herglotzFunction_mul_perron {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {z₀ : ℂ} (hz₀ : 0 < z₀.re) {c : ℝ} (hc : 0 < c) {L : ℝ} (hL : 0 ≤ L) :
    ∫ w : ℝ, herglotzFunction hW (z₀ + contour c w) *
        (cexp (contour c w * L) / contour c w ^ 2) =
      ∫ r, ((cexp ((I * r - z₀) * L) - 1 - (I * r - z₀) * L) / (I * r - z₀) ^ 2 -
        I * r / (1 + (r : ℂ) ^ 2) * L) ∂boundaryMeasure hW := by
  haveI := sFinite_boundaryMeasure hW
  set a : ℝ := z₀.re + c with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  set P : ℝ → ℂ := fun w => cexp (contour c w * L) / contour c w ^ 2 with hP
  have hre : ∀ w : ℝ, 0 < (z₀ + contour c w).re := fun w => by
    rw [Complex.add_re, contour_re]; linarith
  have hpt : ∀ w : ℝ, z₀ + contour c w = (a : ℂ) + ((z₀.im + 2 * π * w : ℝ) : ℂ) * I := by
    intro w; apply Complex.ext <;> simp [contour, ha_def]
  set f : ℝ → ℝ → ℂ := fun w r => herglotzKernel (z₀ + contour c w) r * P w with hf
  have hfc : Continuous (Function.uncurry f) := by
    have hne1 : ∀ p : ℝ × ℝ, z₀ + ((c : ℂ) + 2 * π * p.1 * I) - I * (p.2 : ℂ) ≠ 0 :=
      fun p => sub_I_mul_ne_zero (hre p.1) p.2
    have hne2 : ∀ p : ℝ × ℝ, 1 + ((p.2 : ℝ) : ℂ) ^ 2 ≠ 0 := fun p => one_add_sq_ne_zero p.2
    have hne3 : ∀ p : ℝ × ℝ, ((c : ℂ) + 2 * π * p.1 * I) ^ 2 ≠ 0 := fun p =>
      pow_ne_zero 2 (contour_ne_zero hc p.1)
    show Continuous fun p : ℝ × ℝ => f p.1 p.2
    simp only [hf, hP, herglotzKernel, contour]
    exact Continuous.mul (Continuous.sub (continuous_const.div (by fun_prop) hne1)
      (Continuous.div (by fun_prop) (by fun_prop) hne2))
      (Continuous.div (by fun_prop) (by fun_prop) hne3)
  have hmeas : AEStronglyMeasurable (Function.uncurry f) (volume.prod (boundaryMeasure hW)) :=
    hfc.aestronglyMeasurable
  obtain ⟨C, hC0, hC⟩ := exists_integral_norm_herglotzKernel_le_rpow hW ha z₀.im
  have hint : Integrable (Function.uncurry f) (volume.prod (boundaryMeasure hW)) := by
    rw [integrable_prod_iff hmeas]
    refine ⟨Eventually.of_forall fun w => ?_, ?_⟩
    · have h := (integrable_herglotzKernel hW (hre w)).mul_const (P w)
      exact h
    refine Integrable.mono' (((integrable_one_add_norm (E := ℝ) (μ := volume)
      (r := 5 / 4) (by norm_num)).const_mul
        (C * Real.exp (c * L) * (2 / min (c ^ 2) 1)))) hmeas.norm.integral_prod_right'
      (Eventually.of_forall fun w => ?_)
    have hnn : 0 ≤ ∫ r, ‖Function.uncurry f (w, r)‖ ∂boundaryMeasure hW :=
      integral_nonneg fun _ => norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have e : ∫ r, ‖Function.uncurry f (w, r)‖ ∂boundaryMeasure hW =
        (∫ r, ‖herglotzKernel (z₀ + contour c w) r‖ ∂boundaryMeasure hW) * ‖P w‖ := by
      rw [← integral_mul_const]
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      simp only [Function.uncurry, hf, norm_mul]
    have hPn : ‖P w‖ = Real.exp (c * L) / (c ^ 2 + (2 * π * w) ^ 2) :=
      norm_perron_integrand (a := c) L w
    rw [e, hPn, hpt, mul_comm]
    exact (mul_le_mul_of_nonneg_left (hC w) (by positivity)).trans
      (perron_bound_mul_rpow_le hc hC0)
  have hswap := integral_integral_swap hint
  have hleft : ∀ w, ∫ r, f w r ∂boundaryMeasure hW = herglotzFunction hW (z₀ + contour c w) * P w :=
    fun w => by rw [integral_mul_const]; rfl
  have hright : ∀ r : ℝ, ∫ w, f w r = (cexp ((I * r - z₀) * L) - 1 - (I * r - z₀) * L) /
      (I * r - z₀) ^ 2 - I * r / (1 + (r : ℂ) ^ 2) * L := by
    intro r
    set b : ℂ := I * r - z₀ with hb
    have hbre : b.re < c := by rw [hb]; simp; linarith
    have hb0 : b ≠ 0 := fun h0 => by
      have := congrArg Complex.re h0; rw [hb] at this; simp at this; linarith
    have hfe : ∀ w, f w r = 1 / (contour c w - b) * P w - I * r / (1 + (r : ℂ) ^ 2) * P w := by
      intro w
      simp only [hf, herglotzKernel, hb]
      ring_nf
    have hI1 : Integrable (fun w => 1 / (contour c w - b) * P w) :=
      integrable_inv_sub_mul_perron hc L hbre
    have hI2 : Integrable (fun w => I * r / (1 + (r : ℂ) ^ 2) * P w) :=
      (integrable_perron_integrand hc L).const_mul _
    have h3 : ∫ w, 1 / (contour c w - b) * P w = (cexp (b * L) - 1 - b * L) / b ^ 2 :=
      integral_inv_sub_mul_perron_eq hc hL hbre hb0
    rw [integral_congr_ae (Eventually.of_forall hfe), integral_sub hI1 hI2, integral_const_mul, h3]
    have hK := perron_weighted_kernel hc L
    have hPint : ∫ w, P w = (L : ℂ) := by
      rw [show (L : ℂ) = ((max L 0 : ℝ) : ℂ) by rw [max_eq_left hL]]
      exact hK
    rw [hPint]
  calc ∫ w : ℝ, herglotzFunction hW (z₀ + contour c w) * P w
      = ∫ w, ∫ r, f w r ∂boundaryMeasure hW := integral_congr_ae
        (Eventually.of_forall fun w => (hleft w).symm)
    _ = ∫ r, ∫ w, f w r ∂volume ∂boundaryMeasure hW := hswap
    _ = _ := integral_congr_ae (Eventually.of_forall hright)

/-- The Herglotz function along the contour times the Perron kernel is integrable. -/
theorem integrable_herglotzFunction_mul_perron {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {z₀ : ℂ} (hz₀ : 0 < z₀.re) {c : ℝ} (hc : 0 < c) (L : ℝ) :
    Integrable fun w : ℝ => herglotzFunction hW (z₀ + contour c w) *
      (cexp (contour c w * L) / contour c w ^ 2) := by
  have ha : 0 < z₀.re + c := by linarith
  have hre : ∀ w : ℝ, 0 < (z₀ + contour c w).re := fun w => by
    rw [Complex.add_re, contour_re]; linarith
  have hpt : ∀ w : ℝ, z₀ + contour c w =
      ((z₀.re + c : ℝ) : ℂ) + ((z₀.im + 2 * π * w : ℝ) : ℂ) * I := by
    intro w; apply Complex.ext <;> simp [contour]
  obtain ⟨C, hC0, hC⟩ := exists_integral_norm_herglotzKernel_le_rpow hW ha z₀.im
  have hHc : Continuous fun w : ℝ => herglotzFunction hW (z₀ + contour c w) :=
    (differentiableOn_herglotzFunction hW).continuousOn.comp_continuous
      (by simp only [contour]; fun_prop) hre
  have hPc : Continuous fun w : ℝ => cexp (contour c w * L) / contour c w ^ 2 := by
    have hne : ∀ w : ℝ, ((c : ℂ) + 2 * π * w * I) ^ 2 ≠ 0 := fun w =>
      pow_ne_zero 2 (contour_ne_zero hc w)
    simp only [contour]
    exact Continuous.div (by fun_prop) (by fun_prop) hne
  refine Integrable.mono' ((integrable_one_add_norm (E := ℝ) (μ := volume)
    (r := 5 / 4) (by norm_num)).const_mul (C * Real.exp (c * L) * (2 / min (c ^ 2) 1)))
    (hHc.mul hPc).aestronglyMeasurable (Eventually.of_forall fun w => ?_)
  have hHn : ‖herglotzFunction hW (z₀ + contour c w)‖ ≤ C * (1 + |w|) ^ (3 / 4 : ℝ) := by
    unfold herglotzFunction
    refine (norm_integral_le_integral_norm _).trans ?_
    rw [hpt]
    exact hC w
  have hPn : ‖cexp (contour c w * L) / contour c w ^ 2‖ =
      Real.exp (c * L) / (c ^ 2 + (2 * π * w) ^ 2) := norm_perron_integrand (a := c) L w
  rw [norm_mul, hPn, mul_comm]
  exact (mul_le_mul_of_nonneg_left hHn (by positivity)).trans (perron_bound_mul_rpow_le hc hC0)

end RHTower.WeilSpectral

end
