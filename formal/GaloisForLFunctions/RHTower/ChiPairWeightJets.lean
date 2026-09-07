import GaloisForLFunctions.RHTower.ChiRatioProductJets

/-!
# Height jets of the modulus weight `χ(σ+it)·χ(σ−it)`

On the displaced line `σ = 1/2 − d` the product `P(t) = χ(σ+it)χ(σ−it)` is the modulus weight
`|χ(σ+it)|²` of the dual side of the product approximate functional equation.  Its logarithmic
height derivative is `E(t) = i(L(σ+it) − L(σ−it))` with `L = χ'/χ`, and through the closed form
`L(z) = −ψ(z/2)/2 − ψ((1−z)/2)/2 + log π` the difference regroups into two *horizontal* digamma
increments of length `d` at heights `±t/2`:

`E(t) = −(i/2)·(A(t) − A(−t))`,  `A(t) = ψ(σ/2 + it/2) − ψ((1−σ)/2 + it/2)`.

The segment estimate with the explicit polygamma decay `‖ψ^{(n+1)}(z)‖ ≤ 5(n+1)!/|Im z|^{n+1}`
then gives `‖E^{(n)}(t)‖ ≤ 10 d (n+1)!/t^{n+1}`, so that the modulus weight has no height
oscillation at all: `‖P^{(n)}(t)‖ ≤ n! ‖P(t)‖ (11/t)^n` for `t ≥ 4`, `0 < d ≤ 1/4`.
-/

noncomputable section

namespace RHTower

open Complex GaloisForLFunctions GaloisForLFunctions.HTGeometry Sieve

/-- The modulus weight `P(t) = χ(σ+it)·χ(σ−it)`, `σ = 1/2 − d`. -/
def chiPairWeight (d : ℝ) (t : ℝ) : ℂ :=
  zetaChi (displacedLinePt d t) * zetaChi (displacedLinePt d (-t))

/-- The logarithmic height slope `E(t) = i·L(σ+it) − i·L(σ−it)` of the modulus weight. -/
def chiPairLogSlope (d : ℝ) (t : ℝ) : ℂ :=
  I * logDeriv zetaChi (displacedLinePt d t) - I * logDeriv zetaChi (displacedLinePt d (-t))

theorem displacedLinePt_im (d τ : ℝ) : (displacedLinePt d τ).im = τ := by
  simp [displacedLinePt]

theorem gammaR_one_sub_displaced_ne_zero {d : ℝ} (hd : 0 < d) (u : ℝ) :
    Gammaℝ (1 - displacedLinePt d u) ≠ 0 := by
  apply Gammaℝ_ne_zero_of_re_pos
  rw [Complex.sub_re, Complex.one_re, displacedLinePt_re]
  linarith

theorem zetaChi_displaced_ne_zero {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) (u : ℝ) :
    zetaChi (displacedLinePt d u) ≠ 0 :=
  zetaChi_ne_zero_of_mem_openStrip (displacedLinePt_mem_openStrip hd (by linarith) u).1
    (displacedLinePt_mem_openStrip hd (by linarith) u).2

theorem analyticAt_zetaChi_displaced {d : ℝ} (hd : 0 < d) (u : ℝ) :
    AnalyticAt ℝ (fun s : ℝ => zetaChi (displacedLinePt d s)) u :=
  AnalyticAt.comp (g := zetaChi) (f := fun s : ℝ => displacedLinePt d s)
    (zetaChi_analyticAt (gammaR_one_sub_displaced_ne_zero hd u)).restrictScalars
    (analyticAt_displacedLine d u)

theorem hasDerivAt_displacedLine (d : ℝ) (u : ℝ) :
    HasDerivAt (fun s : ℝ => displacedLinePt d s) I u := by
  have h := (((hasDerivAt_id u).ofReal_comp).mul_const I).const_add ((1 / 2 - d : ℝ) : ℂ)
  simpa [displacedLinePt] using h

/-- The height derivative of `χ` along the displaced line is `i·χ·(χ'/χ)`. -/
theorem hasDerivAt_zetaChi_displaced {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) (u : ℝ) :
    HasDerivAt (fun s : ℝ => zetaChi (displacedLinePt d s))
      (I * zetaChi (displacedLinePt d u) * logDeriv zetaChi (displacedLinePt d u)) u := by
  have hχ : HasDerivAt zetaChi (deriv zetaChi (displacedLinePt d u)) (displacedLinePt d u) :=
    (zetaChi_analyticAt (gammaR_one_sub_displaced_ne_zero hd u)).differentiableAt.hasDerivAt
  have h := hχ.comp u (hasDerivAt_displacedLine d u)
  refine h.congr_deriv ?_
  have hne := zetaChi_displaced_ne_zero hd hdq u
  rw [logDeriv_apply]
  field_simp

/-- **`P' = P·E`.** -/
theorem hasDerivAt_chiPairWeight {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) (t : ℝ) :
    HasDerivAt (chiPairWeight d) (chiPairWeight d t * chiPairLogSlope d t) t := by
  have h1 := hasDerivAt_zetaChi_displaced hd hdq t
  have h2raw := hasDerivAt_zetaChi_displaced hd hdq (-t)
  have h2 := h2raw.scomp t (hasDerivAt_neg t)
  have h := h1.mul h2
  have hfun : chiPairWeight d = fun x : ℝ => zetaChi (displacedLinePt d x) *
      ((fun u : ℝ => zetaChi (displacedLinePt d u)) ∘ Neg.neg) x := rfl
  rw [hfun]
  refine h.congr_deriv ?_
  unfold chiPairLogSlope
  simp only [Function.comp_apply, Complex.real_smul]
  push_cast
  ring

theorem analyticAt_chiPairWeight {d : ℝ} (hd : 0 < d) (u : ℝ) :
    AnalyticAt ℝ (chiPairWeight d) u := by
  have h1 := analyticAt_zetaChi_displaced hd u
  have h2 := analyticAt_zetaChi_displaced hd (-u)
  have h2' : AnalyticAt ℝ (fun s : ℝ => zetaChi (displacedLinePt d (-s))) u :=
    AnalyticAt.comp (g := fun s : ℝ => zetaChi (displacedLinePt d s)) (f := fun s : ℝ => -s) h2
      analyticAt_id.neg
  exact h1.mul h2'

theorem contDiff_chiPairWeight {d : ℝ} (hd : 0 < d) (n : ℕ) : ContDiff ℝ n (chiPairWeight d) :=
  contDiff_iff_contDiffAt.mpr fun u => (analyticAt_chiPairWeight hd u).contDiffAt

theorem analyticAt_logDeriv_zetaChi_displaced {d u : ℝ} (hu : u ≠ 0) :
    AnalyticAt ℝ (fun s : ℝ => logDeriv zetaChi (displacedLinePt d s)) u := by
  have hL : AnalyticAt ℂ (logDeriv zetaChi) (displacedLinePt d u) :=
    analyticAt_logDeriv_zetaChi (by rw [displacedLinePt_im]; exact hu)
  exact AnalyticAt.comp (g := logDeriv zetaChi) (f := fun s : ℝ => displacedLinePt d s)
    hL.restrictScalars (analyticAt_displacedLine d u)

theorem analyticAt_chiPairLogSlope {d u : ℝ} (hu : u ≠ 0) :
    AnalyticAt ℝ (chiPairLogSlope d) u := by
  have h1 := analyticAt_logDeriv_zetaChi_displaced (d := d) hu
  have h2 := analyticAt_logDeriv_zetaChi_displaced (d := d) (neg_ne_zero.mpr hu)
  have h2' : AnalyticAt ℝ (fun s : ℝ => logDeriv zetaChi (displacedLinePt d (-s))) u :=
    AnalyticAt.comp (g := fun s : ℝ => logDeriv zetaChi (displacedLinePt d s))
      (f := fun s : ℝ => -s) h2 analyticAt_id.neg
  exact (analyticAt_const.mul h1).sub (analyticAt_const.mul h2')

/-! ## The digamma form of the slope -/

/-- `ψ(c + i t/2)` along a horizontal abscissa `c`. -/
def digammaHalfLine (c : ℝ) (t : ℝ) : ℂ :=
  Complex.digamma ((c : ℂ) + (((1 / 2 : ℝ) * t : ℝ) : ℂ) * I)

/-- The horizontal digamma increment between the abscissae `σ/2` and `(1−σ)/2`, `σ = 1/2 − d`. -/
def chiPairDigammaIncrement (d : ℝ) (t : ℝ) : ℂ :=
  digammaHalfLine ((1 / 2 - d) / 2) t - digammaHalfLine ((1 / 2 + d) / 2) t

/-- **The slope is a difference of two horizontal digamma increments.** -/
theorem chiPairLogSlope_eq {d t : ℝ} (ht : t ≠ 0) :
    chiPairLogSlope d t = -(I / 2) * (chiPairDigammaIncrement d t - chiPairDigammaIncrement d (-t)) := by
  have him₁ : (displacedLinePt d t).im ≠ 0 := by rw [displacedLinePt_im]; exact ht
  have him₂ : (displacedLinePt d (-t)).im ≠ 0 := by
    rw [displacedLinePt_im]; exact neg_ne_zero.mpr ht
  unfold chiPairLogSlope
  rw [logDeriv_zetaChi_off_poles (half_ne_neg_nat_of_im_ne_zero him₁)
      (reflect_half_ne_neg_nat_of_im_ne_zero him₁),
    logDeriv_zetaChi_off_poles (half_ne_neg_nat_of_im_ne_zero him₂)
      (reflect_half_ne_neg_nat_of_im_ne_zero him₂)]
  unfold chiPairDigammaIncrement digammaHalfLine displacedLinePt
  have e1 : (((1 / 2 - d : ℝ) : ℂ) + (t : ℂ) * I) / 2
      = (((1 / 2 - d) / 2 : ℝ) : ℂ) + (((1 / 2 : ℝ) * t : ℝ) : ℂ) * I := by push_cast; ring
  have e2 : (1 - (((1 / 2 - d : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I)) / 2
      = (((1 / 2 + d) / 2 : ℝ) : ℂ) + (((1 / 2 : ℝ) * t : ℝ) : ℂ) * I := by push_cast; ring
  have e3 : (1 - (((1 / 2 - d : ℝ) : ℂ) + (t : ℂ) * I)) / 2
      = (((1 / 2 + d) / 2 : ℝ) : ℂ) + (((1 / 2 : ℝ) * -t : ℝ) : ℂ) * I := by push_cast; ring
  have e4 : (((1 / 2 - d : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I) / 2
      = (((1 / 2 - d) / 2 : ℝ) : ℂ) + (((1 / 2 : ℝ) * -t : ℝ) : ℂ) * I := by push_cast; ring
  rw [e1, e2, e3, e4]
  ring

/-! ## Jets of the horizontal increments -/

/-- The open right half-plane, where the digamma function is analytic. -/
theorem analyticOnNhd_digamma_rightHalf :
    AnalyticOnNhd ℂ Complex.digamma {z : ℂ | 0 < z.re} := by
  intro z hz
  apply analyticAt_digamma_of_offPoles
  intro p h
  have := congrArg Complex.re h
  simp at this
  have hz' : 0 < z.re := hz
  linarith [(Nat.cast_nonneg p : (0 : ℝ) ≤ p)]

theorem isOpen_rePos : IsOpen {z : ℂ | 0 < z.re} :=
  isOpen_lt continuous_const Complex.continuous_re

/-- Real scaling of iterated derivatives, with no smoothness hypothesis. -/
theorem iteratedDeriv_comp_const_mul_real (f : ℝ → ℂ) (n : ℕ) {μ : ℝ} (hμ : μ ≠ 0) (x : ℝ) :
    iteratedDeriv n (fun y => f (μ * y)) x = μ ^ n * iteratedDeriv n f (μ * x) := by
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.smulLeft (Units.mk0 μ hμ)
  have he (y : ℝ) : e y = μ * y := by
    simp [e]
  have h := e.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (Set.mem_univ (e x)) n
  have h' : iteratedFDeriv ℝ n (f ∘ e) x =
      (iteratedFDeriv ℝ n f (e x)).compContinuousLinearMap (fun _ => e) := by
    simpa only [iteratedFDerivWithin_univ, Set.preimage_univ] using h
  have happ := congrArg
    (fun p : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ) ℂ => p (fun _ => 1)) h'
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, he] at happ
  have heconst : (fun _ : Fin n => e (1 : ℝ)) = (fun _ => μ) := by
    funext i
    simpa using he 1
  change _ = (iteratedFDeriv ℝ n f (μ * x) : (Fin n → ℝ) → ℂ) (fun _ => e (1 : ℝ)) at happ
  rw [heconst] at happ
  have hscale : (iteratedFDeriv ℝ n f (μ * x) : (Fin n → ℝ) → ℂ) (fun _ => μ) =
      μ ^ n * iteratedDeriv n f (μ * x) := by
    rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
    simp
  rw [hscale] at happ
  have hcomp : f ∘ e = (fun y => f (μ * y)) := by
    funext y
    simp [Function.comp_apply, he]
  rw [hcomp] at happ
  simpa [Function.comp_apply, he, iteratedDeriv_eq_iteratedFDeriv] using happ

/-- The vertical line `s ↦ ψ(c + s i)` at a positive abscissa. -/
def digammaVertical (c : ℝ) (s : ℝ) : ℂ := Complex.digamma ((c : ℂ) + (s : ℂ) * I)

theorem iteratedDeriv_digammaVertical {c : ℝ} (hc : 0 < c) (n : ℕ) (s : ℝ) :
    iteratedDeriv n (digammaVertical c) s
      = I ^ n * iteratedDeriv n Complex.digamma ((c : ℂ) + (s : ℂ) * I) := by
  have h := iteratedDeriv_line_of_analyticOnNhd isOpen_rePos analyticOnNhd_digamma_rightHalf
    (c : ℂ) n s (by show 0 < ((c : ℂ) + (s : ℂ) * I).re; simp [hc])
  exact h

theorem analyticAt_digammaVertical {c : ℝ} (hc : 0 < c) (s : ℝ) :
    AnalyticAt ℝ (digammaVertical c) s := by
  have hline : AnalyticAt ℝ (fun u : ℝ => (c : ℂ) + (u : ℂ) * I) s :=
    analyticAt_const.add ((Complex.ofRealCLM.analyticAt s).mul analyticAt_const)
  have hψ : AnalyticAt ℂ Complex.digamma ((c : ℂ) + (s : ℂ) * I) :=
    analyticOnNhd_digamma_rightHalf _ (by show 0 < ((c : ℂ) + (s : ℂ) * I).re; simp [hc])
  exact AnalyticAt.comp (g := Complex.digamma) (f := fun u : ℝ => (c : ℂ) + (u : ℂ) * I)
    hψ.restrictScalars hline

theorem contDiff_digammaVertical {c : ℝ} (hc : 0 < c) (n : ℕ) :
    ContDiff ℝ n (digammaVertical c) :=
  contDiff_iff_contDiffAt.mpr fun s => (analyticAt_digammaVertical hc s).contDiffAt

theorem digammaHalfLine_eq (c : ℝ) :
    digammaHalfLine c = fun t : ℝ => digammaVertical c ((1 / 2 : ℝ) * t) := rfl

theorem iteratedDeriv_digammaHalfLine {c : ℝ} (hc : 0 < c) (n : ℕ) (t : ℝ) :
    iteratedDeriv n (digammaHalfLine c) t
      = (1 / 2 : ℝ) ^ n * (I ^ n
          * iteratedDeriv n Complex.digamma ((c : ℂ) + (((1 / 2 : ℝ) * t : ℝ) : ℂ) * I)) := by
  rw [digammaHalfLine_eq, iteratedDeriv_comp_const_mul_real (digammaVertical c) n (by norm_num) t,
    iteratedDeriv_digammaVertical hc]

theorem contDiff_digammaHalfLine {c : ℝ} (hc : 0 < c) (n : ℕ) :
    ContDiff ℝ n (digammaHalfLine c) := by
  rw [digammaHalfLine_eq]
  exact (contDiff_digammaVertical hc n).comp (contDiff_const.mul contDiff_id)

/-- The segment estimate for a horizontal digamma increment at height `t/2`, `|t| ≥ 2`. -/
theorem norm_iteratedDeriv_digamma_horizontal_sub_le {c₁ c₂ : ℝ} (h₁ : 0 < c₁) (h₂ : 0 < c₂)
    {t : ℝ} (ht : 2 ≤ |t|) (n : ℕ) :
    ‖iteratedDeriv n Complex.digamma ((c₁ : ℂ) + (((1 / 2 : ℝ) * t : ℝ) : ℂ) * I)
        - iteratedDeriv n Complex.digamma ((c₂ : ℂ) + (((1 / 2 : ℝ) * t : ℝ) : ℂ) * I)‖
      ≤ (5 * (n + 1).factorial * 2 ^ (n + 1) / |t| ^ (n + 1)) * |c₁ - c₂| := by
  have hpos : (0 : ℝ) < |t| := by linarith
  set z₁ : ℂ := (c₁ : ℂ) + (((1 / 2 : ℝ) * t : ℝ) : ℂ) * I with hz₁
  set z₂ : ℂ := (c₂ : ℂ) + (((1 / 2 : ℝ) * t : ℝ) : ℂ) * I with hz₂
  have hseg_re : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → 0 < (z₂ + (s : ℂ) * (z₁ - z₂)).re := by
    intro s hs
    have hs0 := hs.1
    have hs1 := hs.2
    simp only [hz₁, hz₂, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im]
    nlinarith [mul_nonneg hs0 h₁.le, mul_nonneg (sub_nonneg.mpr hs1) h₂.le]
  have hseg_im : ∀ s : ℝ, (z₂ + (s : ℂ) * (z₁ - z₂)).im = (1 / 2 : ℝ) * t := by
    intro s
    simp only [hz₁, hz₂, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im]
    ring
  have hM : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      ‖deriv (iteratedDeriv n Complex.digamma) (z₂ + (s : ℂ) * (z₁ - z₂))‖
        ≤ 5 * (n + 1).factorial * 2 ^ (n + 1) / |t| ^ (n + 1) := by
    intro s hs
    rw [← iteratedDeriv_succ]
    have hb := norm_iteratedDeriv_digamma_le (m := n) (z := z₂ + (s : ℂ) * (z₁ - z₂))
      (by linarith [hseg_re s hs]) (by rw [hseg_im, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/2)]; linarith)
    refine hb.trans (le_of_eq ?_)
    rw [hseg_im, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1/2), mul_pow, one_div, inv_pow]
    field_simp
  have hdiff : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      DifferentiableAt ℂ (iteratedDeriv n Complex.digamma) (z₂ + (s : ℂ) * (z₁ - z₂)) :=
    fun s hs => (analyticOnNhd_iteratedDeriv_of_analyticOnNhd analyticOnNhd_digamma_rightHalf n _
      (hseg_re s hs)).differentiableAt
  have h := norm_sub_le_segment hdiff hM
  refine h.trans (le_of_eq ?_)
  congr 1
  simp only [hz₁, hz₂]
  rw [show ((c₁ : ℂ) + (((1 / 2 : ℝ) * t : ℝ) : ℂ) * I) - ((c₂ : ℂ) + (((1 / 2 : ℝ) * t : ℝ) : ℂ) * I)
      = ((c₁ - c₂ : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs]

/-- Jets of the horizontal increment `A(t)`: `‖A^{(n)}(t)‖ ≤ 10 d (n+1)!/|t|^{n+1}`. -/
theorem norm_iteratedDeriv_chiPairDigammaIncrement_le {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4)
    {t : ℝ} (ht : 2 ≤ |t|) (n : ℕ) :
    ‖iteratedDeriv n (chiPairDigammaIncrement d) t‖ ≤ 10 * d * (n + 1).factorial / |t| ^ (n + 1) := by
  have hc₁ : (0 : ℝ) < (1 / 2 - d) / 2 := by linarith
  have hc₂ : (0 : ℝ) < (1 / 2 + d) / 2 := by linarith
  have hfun : chiPairDigammaIncrement d
      = digammaHalfLine ((1 / 2 - d) / 2) - digammaHalfLine ((1 / 2 + d) / 2) := rfl
  rw [hfun, iteratedDeriv_sub (contDiff_digammaHalfLine hc₁ n).contDiffAt
    (contDiff_digammaHalfLine hc₂ n).contDiffAt, iteratedDeriv_digammaHalfLine hc₁,
    iteratedDeriv_digammaHalfLine hc₂, ← mul_sub, ← mul_sub, norm_mul, norm_mul, norm_pow, norm_pow,
    Complex.norm_I, one_pow, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hseg := norm_iteratedDeriv_digamma_horizontal_sub_le hc₁ hc₂ ht n
  have hdiff : |(1 / 2 - d) / 2 - (1 / 2 + d) / 2| = d := by
    rw [show (1 / 2 - d) / 2 - (1 / 2 + d) / 2 = -d by ring, abs_neg, abs_of_pos hd]
  rw [hdiff] at hseg
  calc (1 / 2 : ℝ) ^ n * ‖iteratedDeriv n Complex.digamma (((1 / 2 - d) / 2 : ℝ) + (((1 / 2 : ℝ) * t : ℝ) : ℂ) * I)
        - iteratedDeriv n Complex.digamma (((1 / 2 + d) / 2 : ℝ) + (((1 / 2 : ℝ) * t : ℝ) : ℂ) * I)‖
      ≤ (1 / 2 : ℝ) ^ n * ((5 * (n + 1).factorial * 2 ^ (n + 1) / |t| ^ (n + 1)) * d) :=
        mul_le_mul_of_nonneg_left hseg (by positivity)
    _ = 10 * d * (n + 1).factorial / |t| ^ (n + 1) := by
        rw [pow_succ, show (1 / 2 : ℝ) ^ n = 1 / 2 ^ n by rw [div_pow, one_pow]]
        field_simp
        ring

theorem contDiff_chiPairDigammaIncrement {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) (n : ℕ) :
    ContDiff ℝ n (chiPairDigammaIncrement d) := by
  have hfun : chiPairDigammaIncrement d
      = digammaHalfLine ((1 / 2 - d) / 2) - digammaHalfLine ((1 / 2 + d) / 2) := rfl
  rw [hfun]
  exact (contDiff_digammaHalfLine (by linarith) n).sub (contDiff_digammaHalfLine (by linarith) n)

/-- **Jets of the slope**: `‖E^{(n)}(t)‖ ≤ 10 d (n+1)!/t^{n+1}` for `t ≥ 2`. -/
theorem norm_iteratedDeriv_chiPairLogSlope_le {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) {t : ℝ}
    (ht : 2 ≤ t) (n : ℕ) :
    ‖iteratedDeriv n (chiPairLogSlope d) t‖ ≤ 10 * d * (n + 1).factorial / t ^ (n + 1) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hA := contDiff_chiPairDigammaIncrement hd hdq n
  have hA' : ContDiff ℝ n (fun s : ℝ => chiPairDigammaIncrement d (-s)) :=
    hA.comp contDiff_id.neg
  have heq : chiPairLogSlope d =ᶠ[nhds t]
      fun s => -(I / 2) * ((chiPairDigammaIncrement d - fun s => chiPairDigammaIncrement d (-s)) s) := by
    filter_upwards [Ioi_mem_nhds ht0] with s hs
    rw [chiPairLogSlope_eq (ne_of_gt hs)]
    rfl
  rw [heq.iteratedDeriv_eq,
    iteratedDeriv_const_mul (f := chiPairDigammaIncrement d - fun s => chiPairDigammaIncrement d (-s))
      (-(I / 2)) (hA.sub hA').contDiffAt,
    iteratedDeriv_sub hA.contDiffAt hA'.contDiffAt, iteratedDeriv_comp_neg, norm_mul, norm_neg,
    norm_div, Complex.norm_I, Complex.norm_ofNat, one_div]
  have h1 := norm_iteratedDeriv_chiPairDigammaIncrement_le hd hdq (t := t)
    (by rw [abs_of_pos ht0]; exact ht) n
  have h2 := norm_iteratedDeriv_chiPairDigammaIncrement_le hd hdq (t := -t)
    (by rw [abs_neg, abs_of_pos ht0]; exact ht) n
  rw [abs_of_pos ht0] at h1
  rw [abs_neg, abs_of_pos ht0] at h2
  have hsub : ‖iteratedDeriv n (chiPairDigammaIncrement d) t
      - (-1 : ℝ) ^ n • iteratedDeriv n (chiPairDigammaIncrement d) (-t)‖
      ≤ 2 * (10 * d * (n + 1).factorial / t ^ (n + 1)) := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_smul, norm_pow, Real.norm_eq_abs, abs_neg, abs_one, one_pow, one_mul]
    linarith
  calc (2 : ℝ)⁻¹ * ‖iteratedDeriv n (chiPairDigammaIncrement d) t
        - (-1 : ℝ) ^ n • iteratedDeriv n (chiPairDigammaIncrement d) (-t)‖
      ≤ (2 : ℝ)⁻¹ * (2 * (10 * d * (n + 1).factorial / t ^ (n + 1))) :=
        mul_le_mul_of_nonneg_left hsub (by norm_num)
    _ = 10 * d * (n + 1).factorial / t ^ (n + 1) := by ring

/-! ## Jets of the modulus weight -/

/-- The open half-line `{3 < t}` on which the slope is smooth. -/
theorem isOpen_Ioi_three : IsOpen (Set.Ioi (3 : ℝ)) := isOpen_Ioi

theorem contDiffOn_chiPairLogSlope (d : ℝ) (n : ℕ) :
    ContDiffOn ℝ n (chiPairLogSlope d) (Set.Ioi (3 : ℝ)) :=
  fun t ht => (analyticAt_chiPairLogSlope (d := d) (ne_of_gt (by linarith [Set.mem_Ioi.mp ht])))
    |>.contDiffAt.contDiffWithinAt

/-- **All-order height jets of the modulus weight**: for `0 < d ≤ 1/4` and `t ≥ 4`,
`‖P^{(n)}(t)‖ ≤ n!·‖P(t)‖·(11/t)^n`. -/
theorem norm_iteratedDeriv_chiPairWeight_le {d : ℝ} (hd : 0 < d) (hdq : d ≤ 1 / 4) {t : ℝ}
    (ht : 4 ≤ t) (n : ℕ) :
    ‖iteratedDeriv n (chiPairWeight d) t‖
      ≤ n.factorial * ‖chiPairWeight d t‖ * (11 / t) ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  cases n with
  | zero => simp
  | succ n =>
    have ht0 : (0 : ℝ) < t := by linarith
    have hderiv : deriv (chiPairWeight d) = fun s => chiPairWeight d s * chiPairLogSlope d s :=
      funext fun s => (hasDerivAt_chiPairWeight hd hdq s).deriv
    rw [iteratedDeriv_succ', hderiv]
    have hwin := isOpen_Ioi_three
    have htw : t ∈ Set.Ioi (3 : ℝ) := by show (3 : ℝ) < t; linarith
    have hPc : ContDiffOn ℝ n (chiPairWeight d) (Set.Ioi (3 : ℝ)) :=
      (contDiff_chiPairWeight hd n).contDiffOn
    have hEc : ContDiffOn ℝ n (chiPairLogSlope d) (Set.Ioi (3 : ℝ)) :=
      contDiffOn_chiPairLogSlope d n
    have hleib := norm_iteratedFDerivWithin_mul_le hPc hEc hwin.uniqueDiffOn htw
      (le_refl ((n : ℕ∞) : WithTop ℕ∞))
    have hconv : ∀ (k : ℕ) (f : ℝ → ℂ),
        iteratedFDerivWithin ℝ k f (Set.Ioi (3 : ℝ)) t = iteratedFDeriv ℝ k f t :=
      fun k f => iteratedFDerivWithin_of_isOpen k hwin htw
    simp only [hconv, norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hleib
    refine hleib.trans ?_
    have hEb : ∀ j, j ≤ n → ‖iteratedDeriv j (chiPairLogSlope d) t‖
        ≤ 10 * (j + 1).factorial * ((11 / t) / 11) ^ (j + 1) := by
      intro j _
      refine (norm_iteratedDeriv_chiPairLogSlope_le hd hdq (by linarith) j).trans ?_
      rw [show (11 / t) / 11 = 1 / t by field_simp, div_pow, one_pow, mul_one_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hf : (0 : ℝ) ≤ (j + 1).factorial := by positivity
      nlinarith
    have hPb : ∀ i, i ≤ n → ‖iteratedDeriv i (chiPairWeight d) t‖
        ≤ i.factorial * ‖chiPairWeight d t‖ * (11 / t) ^ i :=
      fun i hi => ih i (Nat.lt_succ_of_le hi)
    exact leibniz_factorial_sum_le n (norm_nonneg _) (by positivity)
      (fun i => ‖iteratedDeriv i (chiPairWeight d) t‖)
      (fun j => ‖iteratedDeriv j (chiPairLogSlope d) t‖)
      (fun j => norm_nonneg _) hPb hEb

end RHTower

end
