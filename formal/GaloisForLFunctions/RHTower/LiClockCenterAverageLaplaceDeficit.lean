import GaloisForLFunctions.RHTower.LiClockCenterAverageEulerShadow
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockPrimitive
import GaloisForLFunctions.RHTower.XiReciprocalSquareSecondMomentRadius

/-!
# The Laplace deficit of the center-averaged Li clock

Let `A(t)` be the Cauchy center-averaged Li clock and `F(t)` its Euler shadow
(`LiClockCenterAverageEulerShadow`).  For `p ≥ 1` both have Laplace transforms on `(0, ∞)`, and

* an on-line zero contributes the same atom to `A` and to `F`;
* an off-line zero and its reflection `ρ ↦ 1 − ρ` (spectral points `a` and `−a`, `Im a > 0`) together
  contribute `Re((p − i(a−i)^{−1})^{−1} − (p − i(a+i)^{−1})^{−1}) = Re(−2/D)` to
  `∫e^{−pt}(A − F)`, where `D = (p(a−i) − i)(p(a+i) − i)` has
  `Re D = p²(Re a² + 1) + 2p Im a − 1 > 0`.

Every off-line pair therefore lowers the Laplace transform of `A` strictly below that of `F`, and
the transform of `F` is `Re ξ'/ξ(3/2 + 1/p)/p²`.  This gives a one-sided single-number criterion
(`riemannHypothesis_iff_integral_exp_mul_liClockCenterAverage_ge`): for any fixed `p ≥ 1`,

`RH ⟺ ∫_0^∞ e^{−pt} A(t) dt ≥ Re ξ'/ξ(3/2 + 1/p) / p²`.

The left side averages clocks centered on the critical line; the right side is a value of the
logarithmic derivative of `ξ` in the half-plane of absolute convergence.

The gap is a depth-free count (`xiOfflineInverseSquareMass_bounds_laplaceGap`): each off-line pair
costs between `1/(p²‖a‖²)` and `3/(p²‖a‖²)` (`centerClockLaplaceDeficit_pair_bounds`) however close
it lies to the line, so with `M = Σ_{off-line copies} ‖a_q‖^{−2}`,

`M/p² ≤ 2(Re ξ'/ξ(3/2 + 1/p)/p² − ∫_0^∞ e^{−pt}A(t)dt) ≤ 3M/p²`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology

namespace RHTower

/-! ## The Laplace transform of a cosine atom -/

/-- `∫_0^∞ e^{−pt} Re(1 − cos(tc)) dt` for `|Im c| < p`. -/
theorem integral_exp_mul_re_one_sub_cos {p : ℝ} (hp : 0 < p) {c : ℂ} (hc : |c.im| < p) :
    IntegrableOn (fun t : ℝ => Real.exp (-(p * t)) * (1 - Complex.cos ((t : ℂ) * c)).re) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * (1 - Complex.cos ((t : ℂ) * c)).re =
        (((p : ℂ)⁻¹ - ((p : ℂ) + -I * c)⁻¹).re + ((p : ℂ)⁻¹ - ((p : ℂ) + I * c)⁻¹).re) / 2 := by
  obtain ⟨hc1, hc2⟩ := abs_lt.mp hc
  have h1 := integral_exp_mul_re_one_sub_exp hp (w := -I * c)
    (by simp [Complex.mul_re]; linarith)
  have h2 := integral_exp_mul_re_one_sub_exp hp (w := I * c)
    (by simp [Complex.mul_re]; linarith)
  have hpt : ∀ t : ℝ, Real.exp (-(p * t)) * (1 - Complex.cos ((t : ℂ) * c)).re =
      (Real.exp (-(p * t)) * (1 - Complex.exp (-(t : ℂ) * (-I * c))).re +
        Real.exp (-(p * t)) * (1 - Complex.exp (-(t : ℂ) * (I * c))).re) / 2 := by
    intro t
    have hcos : 1 - Complex.cos ((t : ℂ) * c) =
        ((1 - Complex.exp (-(t : ℂ) * (-I * c))) + (1 - Complex.exp (-(t : ℂ) * (I * c)))) / 2 := by
      rw [Complex.cos]
      have e1 : -(t : ℂ) * (-I * c) = (t : ℂ) * c * I := by ring
      have e2 : -(t : ℂ) * (I * c) = -((t : ℂ) * c) * I := by ring
      rw [e1, e2]
      ring
    rw [hcos]
    simp only [Complex.add_re, Complex.div_ofNat_re]
    ring
  have hI : IntegrableOn (fun t : ℝ => (Real.exp (-(p * t)) * (1 - Complex.exp (-(t : ℂ) * (-I * c))).re +
      Real.exp (-(p * t)) * (1 - Complex.exp (-(t : ℂ) * (I * c))).re) / 2) (Ioi 0) :=
    (h1.1.add h2.1).div_const 2
  refine ⟨hI.congr_fun (fun t _ => (hpt t).symm) measurableSet_Ioi, ?_⟩
  · simp_rw [hpt]
    rw [integral_div, integral_add h1.1 h2.1, h1.2, h2.2]

/-! ## Spectral points -/

private theorem spectral_im_eq (q : XiZeroCopy) :
    (xiSpectralPoint q).im = 1 / 2 - (q.1 : ℂ).re := by
  rw [xiSpectralPoint]; simp [Complex.mul_im]

private theorem abs_spectral_im_lt (q : XiZeroCopy) : |(xiSpectralPoint q).im| < 1 / 2 := by
  rw [spectral_im_eq]
  obtain ⟨h0, h1⟩ := xi_divisor_support_re_mem_open_unit q.1
  rw [abs_lt]; constructor <;> linarith

private theorem spectral_norm_le_norm_sub_I {a : ℂ} (ha : a.im ≤ 1 / 2) : ‖a‖ ≤ ‖a - I‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.I_re, sub_zero, Complex.sub_im, Complex.I_im]
  nlinarith

private theorem spectral_norm_le_norm_add_I {a : ℂ} (ha : -(1 / 2) ≤ a.im) : ‖a‖ ≤ ‖a + I‖ := by
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.I_re, add_zero, Complex.add_im, Complex.I_im]
  nlinarith

/-- `‖(a ∓ i)^{−1}‖ ≤ ‖a‖^{−1}` in the strip `|Im a| ≤ ½`. -/
private theorem norm_inv_sub_I_le {a : ℂ} (ha0 : a ≠ 0) (ha : |a.im| ≤ 1 / 2) :
    ‖(a - I)⁻¹‖ ≤ ‖a‖⁻¹ := by
  rw [norm_inv]
  exact inv_anti₀ (norm_pos_iff.mpr ha0) (spectral_norm_le_norm_sub_I (abs_le.mp ha).2)

private theorem norm_inv_add_I_le {a : ℂ} (ha0 : a ≠ 0) (ha : |a.im| ≤ 1 / 2) :
    ‖(a + I)⁻¹‖ ≤ ‖a‖⁻¹ := by
  rw [norm_inv]
  exact inv_anti₀ (norm_pos_iff.mpr ha0) (spectral_norm_le_norm_add_I (abs_le.mp ha).1)

/-! ## The pair identity -/

/-- The reflection-pair Laplace deficit in closed form:
`(p − i(a−i)^{−1})^{−1} − (p − i(a+i)^{−1})^{−1} = −2/((p(a−i) − i)(p(a+i) − i))`. -/
private theorem pair_deficit_eq {p : ℝ} {a : ℂ} (h1 : a - I ≠ 0) (h2 : a + I ≠ 0)
    (h3 : (p : ℂ) * (a - I) - I ≠ 0) (h4 : (p : ℂ) * (a + I) - I ≠ 0) :
    ((p : ℂ) + -I * (a - I)⁻¹)⁻¹ - ((p : ℂ) + -I * (a + I)⁻¹)⁻¹ =
      -2 / (((p : ℂ) * (a - I) - I) * ((p : ℂ) * (a + I) - I)) := by
  have e1 : (p : ℂ) + -I * (a - I)⁻¹ = ((p : ℂ) * (a - I) - I) / (a - I) := by
    field_simp; ring
  have e2 : (p : ℂ) + -I * (a + I)⁻¹ = ((p : ℂ) * (a + I) - I) / (a + I) := by
    field_simp; ring
  rw [e1, e2, inv_div, inv_div, div_sub_div _ _ h3 h4]
  congr 1
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The real part of `D = (p(a−i) − i)(p(a+i) − i)`. -/
private theorem pair_den_re (p : ℝ) (a : ℂ) :
    (((p : ℂ) * (a - I) - I) * ((p : ℂ) * (a + I) - I)).re =
      p ^ 2 * (a.re ^ 2 - a.im ^ 2 + 1) + 2 * p * a.im - 1 := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

private theorem pair_den_re_pos {p : ℝ} (hp : 1 ≤ p) {a : ℂ} (ha : 0 < a.im) (ha' : a.im < 1 / 2)
    (hn : 150 < ‖a‖ ^ (2 : ℕ)) :
    0 < (((p : ℂ) * (a - I) - I) * ((p : ℂ) * (a + I) - I)).re := by
  rw [pair_den_re]
  have hn' : 150 < a.re * a.re + a.im * a.im := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at hn; exact hn
  have hre : 149 ≤ a.re ^ 2 - a.im ^ 2 + 1 := by nlinarith
  have hp2 : 1 ≤ p ^ 2 := by nlinarith
  have hprod : 1 * 149 ≤ p ^ 2 * (a.re ^ 2 - a.im ^ 2 + 1) :=
    mul_le_mul hp2 hre (by norm_num) (by positivity)
  have hpim : 0 < 2 * p * a.im := by positivity
  linarith

/-- The imaginary part of `D = (p(a−i) − i)(p(a+i) − i)`. -/
private theorem pair_den_im (p : ℝ) (a : ℂ) :
    (((p : ℂ) * (a - I) - I) * ((p : ℂ) * (a + I) - I)).im =
      2 * p * a.re * (p * a.im - 1) := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- The real inequality behind the pair bounds: `R` within `[p²n − ½, p²n + 2p²]` and
`J² ≤ 5p⁴n` give `1/(p²n) ≤ 2R/(R² + J²) ≤ 3/(p²n)` once `n > 150`. -/
private theorem pair_ratio_bounds {p n R J : ℝ} (hp : 1 ≤ p) (hn : 150 < n)
    (hRlo : p ^ 2 * n - 1 / 2 ≤ R) (hRhi : R ≤ p ^ 2 * n + 2 * p ^ 2)
    (hJ2 : J ^ 2 ≤ 5 * p ^ 4 * n) :
    1 / (p ^ 2 * n) ≤ 2 * R / (R ^ 2 + J ^ 2) ∧ 2 * R / (R ^ 2 + J ^ 2) ≤ 3 / (p ^ 2 * n) := by
  have hp2 : 1 ≤ p ^ 2 := by nlinarith
  have hpn : 150 ≤ p ^ 2 * n := by nlinarith
  have hRpos : 0 < R := by linarith
  have hden : 0 < R ^ 2 + J ^ 2 := by positivity
  have hpn0 : 0 < p ^ 2 * n := by linarith
  constructor
  · rw [div_le_div_iff₀ hpn0 hden]
    have h1 : -(1 / 2) ≤ R - p ^ 2 * n := by linarith
    have h2 : R - p ^ 2 * n ≤ 2 * p ^ 2 := by linarith
    have hu : (R - p ^ 2 * n) ^ 2 ≤ 4 * p ^ 4 := by nlinarith
    have hn2 : 4 + 5 * n - n ^ 2 ≤ 0 := by nlinarith
    have hp4 : 0 ≤ p ^ 4 := by positivity
    have hk := mul_nonpos_of_nonneg_of_nonpos hp4 hn2
    have hexp : R ^ 2 + J ^ 2 - 2 * R * (p ^ 2 * n) =
        (R - p ^ 2 * n) ^ 2 - p ^ 4 * n ^ 2 + J ^ 2 := by ring
    nlinarith
  · rw [div_le_div_iff₀ hden hpn0]
    nlinarith [sq_nonneg J]

/-- **Depth-free size of the pair deficit.** For `0 < Im a < ½` and `‖a‖² > 150`,
`1/(p²‖a‖²) ≤ −Re(−2/D) ≤ 3/(p²‖a‖²)`; the bounds do not involve `Im a`. -/
private theorem pair_deficit_bounds {p : ℝ} (hp : 1 ≤ p) {a : ℂ} (ha : 0 < a.im)
    (ha' : a.im < 1 / 2) (hn : 150 < ‖a‖ ^ (2 : ℕ)) :
    1 / (p ^ 2 * ‖a‖ ^ (2 : ℕ)) ≤
        -(-2 / (((p : ℂ) * (a - I) - I) * ((p : ℂ) * (a + I) - I))).re ∧
      -(-2 / (((p : ℂ) * (a - I) - I) * ((p : ℂ) * (a + I) - I))).re ≤
        3 / (p ^ 2 * ‖a‖ ^ (2 : ℕ)) := by
  have hnxy : ‖a‖ ^ (2 : ℕ) = a.re ^ 2 + a.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hp0 : 0 < p := by linarith
  have hy2 : a.im ^ 2 < 1 / 4 := by nlinarith
  have hpy : 2 * p * a.im ≤ p := by nlinarith
  have hRlo : p ^ 2 * ‖a‖ ^ (2 : ℕ) - 1 / 2 ≤
      (((p : ℂ) * (a - I) - I) * ((p : ℂ) * (a + I) - I)).re := by
    rw [pair_den_re, hnxy]; nlinarith [mul_pos hp0 ha]
  have hRhi : (((p : ℂ) * (a - I) - I) * ((p : ℂ) * (a + I) - I)).re ≤
      p ^ 2 * ‖a‖ ^ (2 : ℕ) + 2 * p ^ 2 := by
    rw [pair_den_re, hnxy]; nlinarith
  have hJ2 : (((p : ℂ) * (a - I) - I) * ((p : ℂ) * (a + I) - I)).im ^ 2 ≤
      5 * p ^ 4 * ‖a‖ ^ (2 : ℕ) := by
    rw [pair_den_im]
    have hpy1 : (p * a.im - 1) ^ 2 ≤ 5 / 4 * p ^ 2 := by
      have h1 : p * a.im < p / 2 := by nlinarith
      have h2 : 0 < p * a.im := mul_pos hp0 ha
      nlinarith
    have hpx : (2 * p * a.re) ^ 2 ≤ 4 * p ^ 2 * ‖a‖ ^ (2 : ℕ) := by
      rw [hnxy]; nlinarith [sq_nonneg a.im, sq_nonneg p]
    calc (2 * p * a.re * (p * a.im - 1)) ^ 2 = (2 * p * a.re) ^ 2 * (p * a.im - 1) ^ 2 := by
          ring
      _ ≤ (4 * p ^ 2 * ‖a‖ ^ (2 : ℕ)) * (5 / 4 * p ^ 2) := by gcongr
      _ = 5 * p ^ 4 * ‖a‖ ^ (2 : ℕ) := by ring
  have hval : ∀ D : ℂ, -(-2 / D).re = 2 * D.re / (D.re ^ 2 + D.im ^ 2) := by
    intro D
    rw [Complex.div_re, Complex.normSq_apply]
    have e1 : ((-2 : ℂ)).re = -2 := by norm_num
    have e2 : ((-2 : ℂ)).im = 0 := by norm_num
    rw [e1, e2]
    ring
  rw [hval]
  exact pair_ratio_bounds hp hn hRlo hRhi hJ2

/-! ## Atomwise Laplace transforms -/

/-- The Laplace deficit of one spectral point: averaged atom minus shadow atom. -/
def centerClockLaplaceDeficit (p : ℝ) (a : ℂ) : ℝ :=
  (∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * centerClockAverage t a) -
    ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * centerClockShadowAtom t a

/-- On the line the averaged and the shadow atom agree, so the deficit vanishes. -/
theorem centerClockLaplaceDeficit_of_im_eq_zero (p : ℝ) {a : ℂ} (ha : a.im = 0) :
    centerClockLaplaceDeficit p a = 0 := by
  unfold centerClockLaplaceDeficit
  rw [sub_eq_zero]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [centerClockAverage_eq_of_im_eq_zero ha (le_of_lt ht)]
  rfl

private theorem shadow_eq_exp (t : ℝ) (a : ℂ) :
    centerClockShadowAtom t a = (1 - Complex.exp (-(t : ℂ) * (-I * (a - I)⁻¹))).re := by
  unfold centerClockShadowAtom
  congr 3
  rw [div_eq_mul_inv]; ring

private theorem shadow_laplace_gen {p : ℝ} (hp : 0 < p) {a : ℂ} (hc : |((a - I)⁻¹).im| < p) :
    IntegrableOn (fun t : ℝ => Real.exp (-(p * t)) * centerClockShadowAtom t a) (Ioi 0) ∧
      ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * centerClockShadowAtom t a =
        ((p : ℂ)⁻¹ - ((p : ℂ) + -I * (a - I)⁻¹)⁻¹).re := by
  have hre : (-I * (a - I)⁻¹).re = ((a - I)⁻¹).im := by
    set z := (a - I)⁻¹
    simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im]
    ring
  have hw : 0 < p + (-I * (a - I)⁻¹).re := by
    rw [hre]; linarith [(abs_lt.mp hc).1]
  have h := integral_exp_mul_re_one_sub_exp hp hw
  simp_rw [shadow_eq_exp]
  exact h

private theorem average_eq_cos_of_im_neg {a : ℂ} (ha : a.im < 0) (t : ℝ) :
    centerClockAverage t a = (1 - Complex.cos ((t : ℂ) * (a - I)⁻¹)).re := by
  rw [centerClockAverage_eq_of_im_neg ha t, div_eq_mul_inv]

private theorem average_eq_cos_of_im_pos {a : ℂ} (ha : 0 < a.im) (t : ℝ) :
    centerClockAverage t a = (1 - Complex.cos ((t : ℂ) * (a + I)⁻¹)).re := by
  rw [centerClockAverage_eq_of_im_pos ha t, div_eq_mul_inv]

private theorem abs_im_inv_lt_one {a : ℂ} (ha0 : a ≠ 0) (ha : |a.im| ≤ 1 / 2)
    (hn : 150 < ‖a‖ ^ (2 : ℕ)) :
    |((a - I)⁻¹).im| < 1 ∧ |((a + I)⁻¹).im| < 1 := by
  have hna : 1 < ‖a‖ := by
    by_contra h; push Not at h
    have : ‖a‖ ^ (2 : ℕ) ≤ 1 := by
      calc ‖a‖ ^ (2 : ℕ) ≤ 1 ^ (2 : ℕ) := pow_le_pow_left₀ (norm_nonneg _) h 2
        _ = 1 := by norm_num
    linarith
  have hinv : ‖a‖⁻¹ < 1 := inv_lt_one_of_one_lt₀ hna
  exact ⟨(Complex.abs_im_le_norm _).trans_lt ((norm_inv_sub_I_le ha0 ha).trans_lt hinv),
    (Complex.abs_im_le_norm _).trans_lt ((norm_inv_add_I_le ha0 ha).trans_lt hinv)⟩

/-- **The reflection-pair deficit in closed form.** For `0 < Im b < ½` and `‖b‖² > 150`, the
deficits of `b` and `−b` add up to `Re(−2/D)` with `D = (p(b−i) − i)(p(b+i) − i)`. -/
theorem centerClockLaplaceDeficit_add_neg_eq {p : ℝ} (hp : 1 ≤ p) {b : ℂ} (hb : 0 < b.im)
    (hb' : b.im < 1 / 2) (hn : 150 < ‖b‖ ^ (2 : ℕ)) :
    centerClockLaplaceDeficit p b + centerClockLaplaceDeficit p (-b) =
      (-2 / (((p : ℂ) * (b - I) - I) * ((p : ℂ) * (b + I) - I))).re := by
  have hp0 : 0 < p := by linarith
  have hb0 : b ≠ 0 := by intro h; rw [h, Complex.zero_im] at hb; exact lt_irrefl _ hb
  have habs : |b.im| ≤ 1 / 2 := by rw [abs_of_pos hb]; linarith
  obtain ⟨hc3, hc4⟩ := abs_im_inv_lt_one hb0 habs hn
  have hc3p : |((b - I)⁻¹).im| < p := by linarith
  have hc4p : |((b + I)⁻¹).im| < p := by linarith
  have hnb : (-b - I)⁻¹ = -(b + I)⁻¹ := by
    rw [show -b - I = -(b + I) by ring, inv_neg]
  have hc4p' : |((-b - I)⁻¹).im| < p := by rw [hnb, Complex.neg_im, abs_neg]; exact hc4p
  have hcos4 := integral_exp_mul_re_one_sub_cos hp0 hc4p
  have hcosn : |(((-b) - I)⁻¹).im| < p := hc4p'
  have hcos4n := integral_exp_mul_re_one_sub_cos hp0 hcosn
  have hF1 := shadow_laplace_gen hp0 hc3p
  have hF2 := shadow_laplace_gen hp0 hcosn
  have hnegb : (-b).im < 0 := by simp; linarith
  unfold centerClockLaplaceDeficit
  have hA1 : ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * centerClockAverage t b =
      ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * (1 - Complex.cos ((t : ℂ) * (b + I)⁻¹)).re := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [average_eq_cos_of_im_pos hb]
  have hA2 : ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * centerClockAverage t (-b) =
      ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) *
        (1 - Complex.cos ((t : ℂ) * ((-b) - I)⁻¹)).re := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [average_eq_cos_of_im_neg hnegb]
  rw [hA1, hA2, hcos4.2, hcos4n.2, hF1.2, hF2.2]
  have hD := pair_den_re_pos hp hb hb' hn
  have hDne : ((p : ℂ) * (b - I) - I) * ((p : ℂ) * (b + I) - I) ≠ 0 := by
    intro h; rw [h, Complex.zero_re] at hD; exact lt_irrefl _ hD
  have h1 : b - I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have h2 : b + I ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  rw [← pair_deficit_eq h1 h2 (left_ne_zero_of_mul hDne) (right_ne_zero_of_mul hDne), hnb]
  simp only [neg_mul, mul_neg, neg_neg, Complex.sub_re]
  ring

/-- **Every off-line reflection pair lowers the Laplace transform.** For `0 < Im b < ½` and
`‖b‖² > 150`, the deficits of `b` and `−b` add up to a negative number. -/
theorem centerClockLaplaceDeficit_add_neg_lt {p : ℝ} (hp : 1 ≤ p) {b : ℂ} (hb : 0 < b.im)
    (hb' : b.im < 1 / 2) (hn : 150 < ‖b‖ ^ (2 : ℕ)) :
    centerClockLaplaceDeficit p b + centerClockLaplaceDeficit p (-b) < 0 := by
  rw [centerClockLaplaceDeficit_add_neg_eq hp hb hb' hn]
  have h := (pair_deficit_bounds hp hb hb' hn).1
  have hpos : 0 < 1 / (p ^ 2 * ‖b‖ ^ (2 : ℕ)) := by
    have : 0 < ‖b‖ ^ (2 : ℕ) := by linarith
    have : 0 < p := by linarith
    positivity
  linarith

/-- **Depth-free pair deficit.** For `0 < Im b < ½` and `‖b‖² > 150` the pair `b, −b` lowers the
Laplace transform of the averaged clock by between `1/(p²‖b‖²)` and `3/(p²‖b‖²)`. Neither bound
depends on `Im b`: a reflection pair arbitrarily close to the critical line still costs about
`2/(p²‖b‖²)`, whereas a pair on the line costs nothing. -/
theorem centerClockLaplaceDeficit_pair_bounds {p : ℝ} (hp : 1 ≤ p) {b : ℂ} (hb : 0 < b.im)
    (hb' : b.im < 1 / 2) (hn : 150 < ‖b‖ ^ (2 : ℕ)) :
    1 / (p ^ 2 * ‖b‖ ^ (2 : ℕ)) ≤
        -(centerClockLaplaceDeficit p b + centerClockLaplaceDeficit p (-b)) ∧
      -(centerClockLaplaceDeficit p b + centerClockLaplaceDeficit p (-b)) ≤
        3 / (p ^ 2 * ‖b‖ ^ (2 : ℕ)) := by
  rw [centerClockLaplaceDeficit_add_neg_eq hp hb hb' hn]
  exact pair_deficit_bounds hp hb hb' hn

/-! ## Summing over the zero copies -/

private theorem twelve_lt_norm (q : XiZeroCopy) : 12 < ‖xiSpectralPoint q‖ := by
  have h := oneHundredFifty_lt_norm_xiSpectralPoint_sq q
  by_contra hle; push Not at hle
  have : ‖xiSpectralPoint q‖ ^ (2 : ℕ) ≤ 12 ^ (2 : ℕ) := pow_le_pow_left₀ (norm_nonneg _) hle 2
  norm_num at this; linarith

private theorem spectral_ne_zero (q : XiZeroCopy) : xiSpectralPoint q ≠ 0 := by
  intro h; have := twelve_lt_norm q; rw [h, norm_zero] at this; linarith

/-- The averaged atom is bounded by `(t² + 2t)e^{t/12}/‖a‖²` for `t ≥ 0`. -/
private theorem abs_average_le (q : XiZeroCopy) {t : ℝ} (ht : 0 ≤ t) :
    |centerClockAverage t (xiSpectralPoint q)| ≤
      (t ^ 2 + 2 * t) * Real.exp (t / 12) / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
  set a := xiSpectralPoint q with ha_def
  have ha0 : a ≠ 0 := spectral_ne_zero q
  have habs : |a.im| ≤ 1 / 2 := (abs_spectral_im_lt q).le
  have h12 : 12 < ‖a‖ := twelve_lt_norm q
  have hnpos : 0 < ‖a‖ := by linarith
  have he1 : 1 ≤ Real.exp (t / 12) := Real.one_le_exp (by positivity)
  have hcos : ∀ c : ℂ, ‖c‖ ≤ ‖a‖⁻¹ →
      |(1 - Complex.cos ((t : ℂ) * c)).re| ≤ (t ^ 2 + 2 * t) * Real.exp (t / 12) / ‖a‖ ^ (2 : ℕ) := by
    intro c hc
    have hb := liClock_norm_one_sub_cos_le_imaginary_exp t c
    have himc : |c.im| ≤ 1 / 12 := by
      have h1 : ‖a‖⁻¹ ≤ 1 / 12 := by rw [inv_le_comm₀ hnpos (by norm_num)]; norm_num; linarith
      exact (Complex.abs_im_le_norm c).trans (hc.trans h1)
    have hexp : Real.exp (|t| * |c.im|) ≤ Real.exp (t / 12) := by
      apply Real.exp_le_exp.mpr
      rw [abs_of_nonneg ht]; nlinarith [abs_nonneg c.im]
    have hc2 : ‖c‖ ^ 2 ≤ (‖a‖ ^ (2 : ℕ))⁻¹ := by
      rw [← inv_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hc 2
    calc |(1 - Complex.cos ((t : ℂ) * c)).re| ≤ ‖1 - Complex.cos ((t : ℂ) * c)‖ :=
          Complex.abs_re_le_norm _
      _ ≤ t ^ 2 / 2 * ‖c‖ ^ 2 * Real.exp (|t| * |c.im|) := hb
      _ ≤ t ^ 2 / 2 * (‖a‖ ^ (2 : ℕ))⁻¹ * Real.exp (t / 12) := by
          gcongr
      _ ≤ (t ^ 2 + 2 * t) * Real.exp (t / 12) / ‖a‖ ^ (2 : ℕ) := by
          rw [div_eq_mul_inv]
          have hpos : 0 ≤ (‖a‖ ^ (2 : ℕ))⁻¹ := by positivity
          have : t ^ 2 / 2 ≤ t ^ 2 + 2 * t := by nlinarith
          calc t ^ 2 / 2 * (‖a‖ ^ (2 : ℕ))⁻¹ * Real.exp (t / 12)
              = t ^ 2 / 2 * Real.exp (t / 12) * (‖a‖ ^ (2 : ℕ))⁻¹ := by ring
            _ ≤ (t ^ 2 + 2 * t) * Real.exp (t / 12) * (‖a‖ ^ (2 : ℕ))⁻¹ := by gcongr
  rcases lt_trichotomy a.im 0 with hneg | hzero | hpos
  · rw [average_eq_cos_of_im_neg hneg]
    exact hcos _ (norm_inv_sub_I_le ha0 habs)
  · rw [abs_of_nonneg (centerClockAverage_nonneg_of_im_eq_zero hzero t)]
    refine (centerClockAverage_le_of_im_eq_zero hzero ha0 ht).trans ?_
    have hpos2 : 0 < ‖a‖ ^ (2 : ℕ) := by positivity
    rw [div_le_div_iff_of_pos_right hpos2]
    nlinarith
  · rw [average_eq_cos_of_im_pos hpos]
    exact hcos _ (norm_inv_add_I_le ha0 habs)

/-- The majorant `e^{−pt}(t² + 2t)e^{t/12}` is integrable on `(0, ∞)` for `p ≥ 1`. -/
private theorem integrableOn_centerClockMajorant {p : ℝ} (hp : 1 ≤ p) :
    IntegrableOn (fun t : ℝ => Real.exp (-(p * t)) * ((t ^ 2 + 2 * t) * Real.exp (t / 12)))
      (Ioi 0) := by
  have hb : 0 < p - 1 / 12 := by linarith
  have h2 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 2) (p := 1) (by norm_num) le_rfl hb
  have h1 := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (by norm_num) le_rfl hb
  refine (h2.add (h1.const_mul 2)).congr_fun (fun t ht => ?_) measurableSet_Ioi
  have ht0 : 0 ≤ t := le_of_lt ht
  simp only [Pi.add_apply, Real.rpow_one]
  rw [show (t : ℝ) ^ (2 : ℝ) = t ^ 2 by norm_cast]
  have he : Real.exp (-(p - 1 / 12) * t) = Real.exp (-(p * t)) * Real.exp (t / 12) := by
    rw [← Real.exp_add]; ring_nf
  rw [he]; ring

private theorem integrableOn_exp_mul_average {p : ℝ} (hp : 1 ≤ p) (q : XiZeroCopy) :
    IntegrableOn (fun t : ℝ => Real.exp (-(p * t)) * centerClockAverage t (xiSpectralPoint q))
      (Ioi 0) := by
  have hp0 : 0 < p := by linarith
  set a := xiSpectralPoint q with ha_def
  have ha0 : a ≠ 0 := spectral_ne_zero q
  have habs : |a.im| ≤ 1 / 2 := (abs_spectral_im_lt q).le
  obtain ⟨hc3, hc4⟩ := abs_im_inv_lt_one ha0 habs (oneHundredFifty_lt_norm_xiSpectralPoint_sq q)
  rcases lt_trichotomy a.im 0 with hneg | hzero | hpos
  · refine (integral_exp_mul_re_one_sub_cos hp0 (by linarith : |((a - I)⁻¹).im| < p)).1.congr_fun
      (fun t _ => ?_) measurableSet_Ioi
    rw [average_eq_cos_of_im_neg hneg]
  · refine (integrableOn_exp_mul_centerClockShadowAtom hp0 q).congr_fun (fun t ht => ?_)
      measurableSet_Ioi
    rw [centerClockAverage_eq_of_im_eq_zero hzero (le_of_lt ht)]
    rfl
  · refine (integral_exp_mul_re_one_sub_cos hp0 (by linarith : |((a + I)⁻¹).im| < p)).1.congr_fun
      (fun t _ => ?_) measurableSet_Ioi
    rw [average_eq_cos_of_im_pos hpos]

/-- **The atomwise Laplace transforms of the averaged clock sum to its Laplace transform.** -/
theorem hasSum_integral_exp_mul_centerClockAverage {p : ℝ} (hp : 1 ≤ p) :
    HasSum (fun q : XiZeroCopy => ∫ t in Ioi (0 : ℝ),
      Real.exp (-(p * t)) * centerClockAverage t (xiSpectralPoint q))
      (∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockCenterAverage t) := by
  set M : ℝ := ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * ((t ^ 2 + 2 * t) * Real.exp (t / 12))
  have hint : ∀ q : XiZeroCopy, Integrable (fun t : ℝ => Real.exp (-(p * t)) *
      centerClockAverage t (xiSpectralPoint q)) (volume.restrict (Ioi 0)) :=
    fun q => integrableOn_exp_mul_average hp q
  have hbound : ∀ q : XiZeroCopy, ∫ t in Ioi (0 : ℝ),
      ‖Real.exp (-(p * t)) * centerClockAverage t (xiSpectralPoint q)‖ ≤
        M * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
    intro q
    have hpos : 0 < ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
      have := twelve_lt_norm q; positivity
    rw [show M * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) = ∫ t in Ioi (0 : ℝ),
        Real.exp (-(p * t)) * ((t ^ 2 + 2 * t) * Real.exp (t / 12)) / ‖xiSpectralPoint q‖ ^ (2 : ℕ)
        by rw [integral_div]; ring]
    refine setIntegral_mono_on (hint q).norm ((integrableOn_centerClockMajorant hp).div_const _)
      measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 ≤ t := le_of_lt ht
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (abs_average_le q ht0) (Real.exp_pos _).le
  have hsum : Summable fun q : XiZeroCopy => ∫ t in Ioi (0 : ℝ),
      ‖Real.exp (-(p * t)) * centerClockAverage t (xiSpectralPoint q)‖ :=
    (xiSpectralPoint_inv_sq_summable.mul_left M).of_nonneg_of_le
      (fun q => integral_nonneg fun t => norm_nonneg _) hbound
  have h := hasSum_integral_of_summable_integral_norm hint hsum
  have hpull : (fun t : ℝ => ∑' q : XiZeroCopy, Real.exp (-(p * t)) *
      centerClockAverage t (xiSpectralPoint q)) =
      fun t => Real.exp (-(p * t)) * liClockCenterAverage t := by
    funext t
    simp only [liClockCenterAverage]
    exact tsum_mul_left
  rw [hpull] at h
  exact h

/-- **Off the line, the averaged clock falls short of its Euler shadow in Laplace mean.** For
`p ≥ 1`, if RH fails then `∫_0^∞ e^{−pt}A(t)dt < Re ξ'/ξ(3/2 + 1/p)/p²`. -/
theorem integral_exp_mul_liClockCenterAverage_lt_of_not_rh {p : ℝ} (hp : 1 ≤ p)
    (h : ¬ RiemannHypothesis) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockCenterAverage t <
      (logDeriv xi ((3 / 2 + 1 / p : ℝ) : ℂ)).re / p ^ 2 := by
  have hp0 : 0 < p := by linarith
  have hA := hasSum_integral_exp_mul_centerClockAverage hp
  have hF := hasSum_integral_exp_mul_centerClockShadowAtom hp0
  have hD : HasSum (fun q : XiZeroCopy => centerClockLaplaceDeficit p (xiSpectralPoint q))
      ((∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockCenterAverage t) -
        (logDeriv xi ((3 / 2 + 1 / p : ℝ) : ℂ)).re / p ^ 2) := hA.sub hF
  have hDσ : HasSum (fun q : XiZeroCopy =>
      centerClockLaplaceDeficit p (xiSpectralPoint (xiZeroCopyReflectEquiv q)))
      ((∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockCenterAverage t) -
        (logDeriv xi ((3 / 2 + 1 / p : ℝ) : ℂ)).re / p ^ 2) :=
    (xiZeroCopyReflectEquiv.hasSum_iff (f := fun q =>
      centerClockLaplaceDeficit p (xiSpectralPoint q))).mpr hD
  simp_rw [xiSpectralPoint_reflect] at hDσ
  have hpair := hD.add hDσ
  have hle : ∀ q : XiZeroCopy, centerClockLaplaceDeficit p (xiSpectralPoint q) +
      centerClockLaplaceDeficit p (-xiSpectralPoint q) ≤ 0 := by
    intro q
    set a := xiSpectralPoint q
    have hn := oneHundredFifty_lt_norm_xiSpectralPoint_sq q
    have habs := abs_spectral_im_lt q
    rcases lt_trichotomy a.im 0 with hneg | hzero | hpos
    · have h1 := centerClockLaplaceDeficit_add_neg_lt hp (b := -a) (by simp; linarith)
        (by simp; linarith [(abs_lt.mp habs).1]) (by rw [norm_neg]; exact hn)
      rw [neg_neg] at h1; linarith
    · rw [centerClockLaplaceDeficit_of_im_eq_zero p hzero,
        centerClockLaplaceDeficit_of_im_eq_zero p (by simp [hzero])]
      norm_num
    · exact (centerClockLaplaceDeficit_add_neg_lt hp hpos (abs_lt.mp habs).2 hn).le
  obtain ⟨q₀, hq₀⟩ := exists_xiSpectralPoint_im_ne_zero_of_not_rh h
  have hlt : centerClockLaplaceDeficit p (xiSpectralPoint q₀) +
      centerClockLaplaceDeficit p (-xiSpectralPoint q₀) < 0 := by
    have hn := oneHundredFifty_lt_norm_xiSpectralPoint_sq q₀
    have habs := abs_spectral_im_lt q₀
    rcases lt_or_gt_of_ne hq₀ with hneg | hpos
    · have h1 := centerClockLaplaceDeficit_add_neg_lt hp (b := -xiSpectralPoint q₀)
        (by simp; linarith) (by simp; linarith [(abs_lt.mp habs).1]) (by rw [norm_neg]; exact hn)
      rw [neg_neg] at h1; linarith
    · exact centerClockLaplaceDeficit_add_neg_lt hp hpos (abs_lt.mp habs).2 hn
  have := hasSum_lt (f := fun q : XiZeroCopy => centerClockLaplaceDeficit p (xiSpectralPoint q) +
      centerClockLaplaceDeficit p (-xiSpectralPoint q)) (g := fun _ => (0 : ℝ))
    (fun q => hle q) hlt hpair hasSum_zero
  linarith

/-- **RH as a one-sided Laplace inequality.** For any fixed `p ≥ 1`, RH holds iff
`∫_0^∞ e^{−pt}A(t)dt ≥ Re ξ'/ξ(3/2 + 1/p)/p²`; for instance `∫_0^∞ e^{−t}A(t)dt ≥ Re ξ'/ξ(5/2)`. -/
theorem riemannHypothesis_iff_integral_exp_mul_liClockCenterAverage_ge {p : ℝ} (hp : 1 ≤ p) :
    RiemannHypothesis ↔ (logDeriv xi ((3 / 2 + 1 / p : ℝ) : ℂ)).re / p ^ 2 ≤
      ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockCenterAverage t := by
  constructor
  · intro hRH
    have hp0 : 0 < p := by linarith
    have heq : ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockCenterAverage t =
        ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockEulerShadow t :=
      setIntegral_congr_fun measurableSet_Ioi fun t ht => by
        rw [riemannHypothesis_iff_liClockCenterAverage_eq_eulerShadow.mp hRH t (le_of_lt ht)]
    rw [heq, integral_exp_mul_liClockEulerShadow hp0]
  · intro hge
    by_contra h
    have := integral_exp_mul_liClockCenterAverage_lt_of_not_rh hp h
    linarith

/-! ## The Laplace gap is a depth-free count of off-line zeros -/

/-- The off-line term of a zero copy: `‖a_q‖^{−2}` off the critical line, `0` on it. -/
def xiOfflineInverseSquareTerm (q : XiZeroCopy) : ℝ :=
  if (xiSpectralPoint q).im = 0 then 0 else 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)

/-- The off-line inverse-square mass `M = Σ_{off-line copies} ‖a_q‖^{−2}`. Every copy off the
critical line contributes `‖a_q‖^{−2}`, however close to the line it lies. -/
def xiOfflineInverseSquareMass : ℝ := ∑' q : XiZeroCopy, xiOfflineInverseSquareTerm q

private theorem xiOfflineInverseSquareTerm_le (q : XiZeroCopy) :
    0 ≤ xiOfflineInverseSquareTerm q ∧
      xiOfflineInverseSquareTerm q ≤ 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
  unfold xiOfflineInverseSquareTerm
  split_ifs
  · exact ⟨le_rfl, by positivity⟩
  · exact ⟨by positivity, le_rfl⟩

private theorem summable_xiOfflineInverseSquareTerm : Summable xiOfflineInverseSquareTerm :=
  xiSpectralPoint_inv_sq_summable.of_nonneg_of_le (fun q => (xiOfflineInverseSquareTerm_le q).1)
    (fun q => (xiOfflineInverseSquareTerm_le q).2)

/-- The pair deficit of one copy, read from that copy, lies between `M_q/p²` and `3M_q/p²`. -/
private theorem pair_gap_bounds {p : ℝ} (hp : 1 ≤ p) (q : XiZeroCopy) :
    xiOfflineInverseSquareTerm q / p ^ 2 ≤
        -(centerClockLaplaceDeficit p (xiSpectralPoint q) +
          centerClockLaplaceDeficit p (-xiSpectralPoint q)) ∧
      -(centerClockLaplaceDeficit p (xiSpectralPoint q) +
          centerClockLaplaceDeficit p (-xiSpectralPoint q)) ≤
        3 * xiOfflineInverseSquareTerm q / p ^ 2 := by
  set a := xiSpectralPoint q with ha_def
  have hn := oneHundredFifty_lt_norm_xiSpectralPoint_sq q
  have habs := abs_spectral_im_lt q
  have hp0 : 0 < p := by linarith
  have hrw : ∀ x : ℝ, 1 / x / p ^ 2 = 1 / (p ^ 2 * x) := fun x => by
    rw [div_div, mul_comm]
  have hrw3 : ∀ x : ℝ, 3 * (1 / x) / p ^ 2 = 3 / (p ^ 2 * x) := fun x => by
    rw [mul_one_div, div_div, mul_comm x]
  rcases lt_trichotomy a.im 0 with hneg | hzero | hpos
  · have hb : 0 < (-a).im := by simp; linarith
    have hb' : (-a).im < 1 / 2 := by simp; linarith [(abs_lt.mp habs).1]
    have hnb : 150 < ‖-a‖ ^ (2 : ℕ) := by rw [norm_neg]; exact hn
    have h := centerClockLaplaceDeficit_pair_bounds hp hb hb' hnb
    rw [neg_neg, norm_neg, add_comm (centerClockLaplaceDeficit p (-a))] at h
    have hterm : xiOfflineInverseSquareTerm q = 1 / ‖a‖ ^ (2 : ℕ) := by
      unfold xiOfflineInverseSquareTerm; rw [← ha_def, if_neg hneg.ne]
    rw [hterm, hrw, hrw3]
    exact h
  · have hterm : xiOfflineInverseSquareTerm q = 0 := by
      unfold xiOfflineInverseSquareTerm; rw [← ha_def, if_pos hzero]
    rw [hterm, centerClockLaplaceDeficit_of_im_eq_zero p hzero,
      centerClockLaplaceDeficit_of_im_eq_zero p (by simp [hzero])]
    norm_num
  · have h := centerClockLaplaceDeficit_pair_bounds hp hpos (abs_lt.mp habs).2 hn
    have hterm : xiOfflineInverseSquareTerm q = 1 / ‖a‖ ^ (2 : ℕ) := by
      unfold xiOfflineInverseSquareTerm; rw [← ha_def, if_neg hpos.ne']
    rw [hterm, hrw, hrw3]
    exact h

/-- **The Laplace gap counts off-line zeros without depth weights.** For every `p ≥ 1`,
with `M = Σ_{off-line copies} ‖a_q‖^{−2}`,

`M/p² ≤ 2(Re ξ'/ξ(3/2 + 1/p)/p² − ∫_0^∞ e^{−pt}A(t)dt) ≤ 3M/p²`.

Classical zero-density functionals (Littlewood's lemma, the Balazard–Saias–Yor integral) weight an
off-line zero by its distance from the critical line. Here every off-line zero is weighted by
`‖a_q‖^{−2}` alone, uniformly in its depth. -/
theorem xiOfflineInverseSquareMass_bounds_laplaceGap {p : ℝ} (hp : 1 ≤ p) :
    xiOfflineInverseSquareMass / p ^ 2 ≤
        2 * ((logDeriv xi ((3 / 2 + 1 / p : ℝ) : ℂ)).re / p ^ 2 -
          ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockCenterAverage t) ∧
      2 * ((logDeriv xi ((3 / 2 + 1 / p : ℝ) : ℂ)).re / p ^ 2 -
          ∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockCenterAverage t) ≤
        3 * xiOfflineInverseSquareMass / p ^ 2 := by
  have hp0 : 0 < p := by linarith
  have hA := hasSum_integral_exp_mul_centerClockAverage hp
  have hF := hasSum_integral_exp_mul_centerClockShadowAtom hp0
  have hD : HasSum (fun q : XiZeroCopy => centerClockLaplaceDeficit p (xiSpectralPoint q))
      ((∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockCenterAverage t) -
        (logDeriv xi ((3 / 2 + 1 / p : ℝ) : ℂ)).re / p ^ 2) := hA.sub hF
  have hDσ : HasSum (fun q : XiZeroCopy =>
      centerClockLaplaceDeficit p (xiSpectralPoint (xiZeroCopyReflectEquiv q)))
      ((∫ t in Ioi (0 : ℝ), Real.exp (-(p * t)) * liClockCenterAverage t) -
        (logDeriv xi ((3 / 2 + 1 / p : ℝ) : ℂ)).re / p ^ 2) :=
    (xiZeroCopyReflectEquiv.hasSum_iff (f := fun q =>
      centerClockLaplaceDeficit p (xiSpectralPoint q))).mpr hD
  simp_rw [xiSpectralPoint_reflect] at hDσ
  have hneg := (hD.add hDσ).neg
  have hm := summable_xiOfflineInverseSquareTerm.hasSum
  have h1 := hasSum_le (fun q => (pair_gap_bounds hp q).1) (hm.div_const (p ^ 2)) hneg
  have h2 := hasSum_le (fun q => (pair_gap_bounds hp q).2) hneg
    ((hm.mul_left 3).div_const (p ^ 2))
  unfold xiOfflineInverseSquareMass
  constructor <;> linarith

end RHTower
