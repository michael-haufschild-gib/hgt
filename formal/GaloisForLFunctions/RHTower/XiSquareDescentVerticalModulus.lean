import GaloisForLFunctions.RHTower.XiSquaredSeamCassiniResolventSourceLaw
import GaloisForLFunctions.HTGeometry.VerticalModulusDerivative
import GaloisForLFunctions.RHTower.XiVerticalMonotoneCriterion

/-!
# Vertical modulus monotonicity of the Xi square descent

The centered completed function is even, so it descends through `z ↦ z²` to an entire `F` with
`F (z²) = XiC z`.  Off the squared divisor the logarithmic derivative of `F` is the halved
reciprocal-square resolvent of the Xi divisor.

Under the Riemann hypothesis every reciprocal square is a positive real, so that resolvent has
nonnegative imaginary part on the closed upper half plane; the vertical modulus derivative
identity then makes `v ↦ |F (u + i v)|` monotone on `[0, ∞)` for every abscissa.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The entire square descent of the centered completed function. -/
abbrev xiSquareDescent : ℂ → ℂ := xiSquaredSeamEntireQuotient

theorem xiSquareDescent_sqrt (w : ℂ) : xiSquareDescent w = XiC (Complex.sqrt w) := by
  rw [← xiSquaredSeamEntireQuotient_sq (Complex.sqrt w),
    GaloisForLFunctions.HTGeometry.complex_sqrt_sq w]

/-- The reciprocal-square resolvent of the Xi divisor, in the squared coordinate. -/
def xiSquareDescentResolvent (w : ℂ) : ℂ :=
  ∑' q : XiZeroCopy,
    xiZeroCopyReciprocalSquare q / (1 - w * xiZeroCopyReciprocalSquare q)

theorem xiSquareDescentResolvent_sq (z : ℂ) :
    xiSquareDescentResolvent (z ^ (2 : ℕ)) =
      ∑' q : XiZeroCopy, xiReciprocalSquareResolventTerm z q := by
  rfl

/-- Chain rule through the square cover. -/
theorem logDeriv_XiC_eq_two_mul_logDeriv_xiSquareDescent
    {z : ℂ} (hXi : XiC z ≠ 0) :
    logDeriv XiC z = 2 * z * logDeriv xiSquareDescent (z ^ (2 : ℕ)) := by
  have hinner : HasDerivAt (fun w : ℂ => w ^ (2 : ℕ)) (2 * z) z := by
    simpa using (hasDerivAt_pow 2 z)
  have houter :=
    differentiable_xiSquaredSeamEntireQuotient.differentiableAt.hasDerivAt.comp z hinner
  have hcomp : xiSquareDescent ∘ (fun w : ℂ => w ^ (2 : ℕ)) = XiC := by
    funext w
    exact xiSquaredSeamEntireQuotient_sq w
  rw [hcomp] at houter
  have hval : xiSquareDescent (z ^ (2 : ℕ)) = XiC z := xiSquaredSeamEntireQuotient_sq z
  rw [logDeriv_apply, logDeriv_apply, houter.deriv, hval]
  field_simp [hXi]

/-- **Squared-coordinate resolvent identity.**  Away from the origin and the divisor, the
logarithmic derivative of the square descent is the halved reciprocal-square resolvent. -/
theorem logDeriv_xiSquareDescent_eq_resolvent
    {z : ℂ} (hz : z ≠ 0) (hXi : XiC z ≠ 0) :
    logDeriv xiSquareDescent (z ^ (2 : ℕ)) = -(1 / 2) * xiSquareDescentResolvent (z ^ (2 : ℕ)) := by
  have hlog := logDeriv_XiC_eq_relativeResolventTrace hXi
  rw [xiRelativeResolventTrace_eq_reciprocalSquareResolvent hXi,
    logDeriv_XiC_eq_two_mul_logDeriv_xiSquareDescent hXi] at hlog
  rw [xiSquareDescentResolvent_sq]
  apply mul_left_cancel₀ hz
  linear_combination hlog / 2

/-! ## Reality on the real axis -/

theorem xiSquareDescent_ofReal_im (x : ℝ) : (xiSquareDescent (x : ℂ)).im = 0 := by
  show (xiSquaredSeamEntireQuotient ((x : ℝ) : ℂ)).im = 0
  rcases le_or_gt 0 x with hx | hx
  · have hsq : ((Real.sqrt x : ℝ) : ℂ) ^ (2 : ℕ) = (x : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt hx]
    have := xiSquaredSeamEntireQuotient_sq ((Real.sqrt x : ℝ) : ℂ)
    rw [hsq] at this
    rw [this, XiC_ofReal]
    simp
  · set s : ℝ := Real.sqrt (-x) with hs
    have hsq : (((s : ℝ) : ℂ) * Complex.I) ^ (2 : ℕ) = (x : ℂ) := by
      have hpos : (0 : ℝ) ≤ -x := by linarith
      have : (s : ℝ) ^ (2 : ℕ) = -x := Real.sq_sqrt hpos
      rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, this]
      push_cast
      ring
    have hval := xiSquaredSeamEntireQuotient_sq (((s : ℝ) : ℂ) * Complex.I)
    rw [hsq] at hval
    have hreal : XiC (((s : ℝ) : ℂ) * Complex.I) =
        (starRingEnd ℂ) (XiC (((s : ℝ) : ℂ) * Complex.I)) := by
      have hconj : (starRingEnd ℂ) (((s : ℝ) : ℂ) * Complex.I) =
          -(((s : ℝ) : ℂ) * Complex.I) := by
        simp
      rw [← XiC_conj, hconj, XiC_even]
    rw [hval]
    have := congrArg Complex.im hreal
    simp only [Complex.conj_im] at this
    linarith

theorem im_deriv_xiSquareDescent_ofReal (x : ℝ) : (deriv xiSquareDescent (x : ℂ)).im = 0 := by
  have hpath : HasDerivAt (fun t : ℝ => ((x : ℂ) + (t : ℂ))) 1 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_add ((x : ℂ))
  have hbase : HasDerivAt xiSquareDescent (deriv xiSquareDescent ((x : ℂ) + ((0 : ℝ) : ℂ)))
      ((x : ℂ) + ((0 : ℝ) : ℂ)) :=
    differentiable_xiSquaredSeamEntireQuotient.differentiableAt.hasDerivAt
  have hcomp : HasDerivAt (fun t : ℝ => xiSquareDescent ((x : ℂ) + (t : ℂ)))
      (deriv xiSquareDescent ((x : ℂ) + ((0 : ℝ) : ℂ))) 0 := by
    have hraw := hbase.scomp (0 : ℝ) hpath
    simpa only [Function.comp_apply, smul_eq_mul, one_mul] using! hraw
  have him : HasDerivAt (fun t : ℝ => (xiSquareDescent ((x : ℂ) + (t : ℂ))).im)
      (deriv xiSquareDescent ((x : ℂ) + ((0 : ℝ) : ℂ))).im 0 :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hcomp
  have hconst : (fun t : ℝ => (xiSquareDescent ((x : ℂ) + (t : ℂ))).im) = fun _ : ℝ => (0 : ℝ) := by
    funext t
    have hcast : ((x : ℂ) + (t : ℂ)) = (((x + t : ℝ)) : ℂ) := by push_cast; ring
    rw [hcast]
    exact xiSquareDescent_ofReal_im (x + t)
  rw [hconst] at him
  have hzero := (hasDerivAt_const (0 : ℝ) (0 : ℝ)).unique him
  simpa using hzero.symm

/-! ## The Riemann-hypothesis sign on the closed upper half plane -/

theorem exists_pos_xiZeroCopyReciprocalSquare_of_rh
    (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    ∃ u : ℝ, 0 < u ∧ xiZeroCopyReciprocalSquare q = (u : ℂ) := by
  obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
  have hne : ((t : ℝ) : ℂ) ≠ 0 := by
    rw [← ht]; exact xiSpectralPoint_ne_zero q
  have ht0 : (t : ℝ) ≠ 0 := by
    intro h; exact hne (by rw [h]; simp)
  have hinv : (t : ℝ)⁻¹ ≠ 0 := inv_ne_zero ht0
  refine ⟨((t : ℝ)⁻¹) ^ (2 : ℕ), by positivity, ?_⟩
  rw [xiZeroCopyReciprocalSquare, ht]
  push_cast
  ring

theorem sqrt_ne_zero_of_ne_zero {w : ℂ} (hw : w ≠ 0) : Complex.sqrt w ≠ 0 := by
  intro h
  apply hw
  rw [← GaloisForLFunctions.HTGeometry.complex_sqrt_sq w, h]
  ring

theorem xiSquareDescent_ne_zero_of_im_ne_zero_of_rh
    (hRH : RiemannHypothesis) {w : ℂ} (hw : w.im ≠ 0) :
    xiSquareDescent w ≠ 0 := by
  intro hzero
  rw [xiSquareDescent_sqrt] at hzero
  obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy _).mp hzero
  obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
  rw [ht] at hq
  have hwval : w = ((t : ℝ) : ℂ) ^ (2 : ℕ) := by
    rw [hq, GaloisForLFunctions.HTGeometry.complex_sqrt_sq]
  apply hw
  rw [hwval]
  simp [pow_two, Complex.mul_im]

private theorem im_resolventTerm_nonneg {w : ℂ} (hwim : 0 ≤ w.im) {u : ℝ} (hu : 0 < u)
    (hden : 1 - w * (u : ℂ) ≠ 0) :
    0 ≤ (((u : ℝ) : ℂ) / (1 - w * ((u : ℝ) : ℂ))).im := by
  have hns : 0 < Complex.normSq (1 - w * ((u : ℝ) : ℂ)) :=
    Complex.normSq_pos.mpr hden
  have him : (1 - w * ((u : ℝ) : ℂ)).im = -(w.im * u) := by simp
  rw [Complex.div_im, Complex.ofReal_im, Complex.ofReal_re, zero_mul, zero_div, zero_sub, him]
  have hneg : u * -(w.im * u) / Complex.normSq (1 - w * ((u : ℝ) : ℂ)) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg _ hns.le
    nlinarith [mul_nonneg (mul_nonneg hu.le hu.le) hwim]
  linarith

theorem im_xiSquareDescentResolvent_nonneg_of_rh
    (hRH : RiemannHypothesis) {w : ℂ} (hwim : 0 ≤ w.im)
    (hF : xiSquareDescent w ≠ 0) :
    0 ≤ (xiSquareDescentResolvent w).im := by
  set z : ℂ := Complex.sqrt w with hz
  have hzsq : z ^ (2 : ℕ) = w := GaloisForLFunctions.HTGeometry.complex_sqrt_sq w
  have hXi : XiC z ≠ 0 := by
    rw [← xiSquaredSeamEntireQuotient_sq z, hzsq]
    exact hF
  have hsummable : Summable (fun q : XiZeroCopy =>
      xiZeroCopyReciprocalSquare q / (1 - w * xiZeroCopyReciprocalSquare q)) := by
    have h := summable_xiReciprocalSquareResolventTerm hXi
    apply h.congr
    intro q
    rw [xiReciprocalSquareResolventTerm, hzsq]
  rw [xiSquareDescentResolvent, Complex.im_tsum hsummable]
  apply tsum_nonneg
  intro q
  obtain ⟨u, hu, hueq⟩ := exists_pos_xiZeroCopyReciprocalSquare_of_rh hRH q
  have hden : 1 - w * ((u : ℝ) : ℂ) ≠ 0 := by
    rw [← hueq, ← hzsq]
    exact one_sub_sq_mul_xiZeroCopyReciprocalSquare_ne_zero hXi q
  rw [hueq]
  exact im_resolventTerm_nonneg hwim hu hden

theorem im_logDeriv_xiSquareDescent_nonpos_of_rh
    (hRH : RiemannHypothesis) {w : ℂ} (hwim : 0 ≤ w.im) (hw0 : w ≠ 0)
    (hF : xiSquareDescent w ≠ 0) :
    (logDeriv xiSquareDescent w).im ≤ 0 := by
  set z : ℂ := Complex.sqrt w with hz
  have hzsq : z ^ (2 : ℕ) = w := GaloisForLFunctions.HTGeometry.complex_sqrt_sq w
  have hzne : z ≠ 0 := sqrt_ne_zero_of_ne_zero hw0
  have hXi : XiC z ≠ 0 := by
    rw [← xiSquaredSeamEntireQuotient_sq z, hzsq]
    exact hF
  have hid := logDeriv_xiSquareDescent_eq_resolvent hzne hXi
  rw [hzsq] at hid
  rw [hid]
  have hres := im_xiSquareDescentResolvent_nonneg_of_rh hRH hwim hF
  simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im]
  norm_num
  linarith

/-! ## Vertical monotonicity under the Riemann hypothesis -/

theorem neg_im_deriv_mul_conj_nonneg_of_rh (hRH : RiemannHypothesis) (x : ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    0 ≤ -(deriv xiSquareDescent ((x : ℂ) + (t : ℂ) * Complex.I) *
      (starRingEnd ℂ) (xiSquareDescent ((x : ℂ) + (t : ℂ) * Complex.I))).im := by
  rcases eq_or_lt_of_le ht with hzero | hpos
  · have hpt : ((x : ℂ) + (t : ℂ) * Complex.I) = ((x : ℝ) : ℂ) := by
      rw [← hzero]
      simp
    rw [hpt]
    have h1 := im_deriv_xiSquareDescent_ofReal x
    have h2 := xiSquareDescent_ofReal_im x
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, h1, h2]
    norm_num
  · set w : ℂ := (x : ℂ) + (t : ℂ) * Complex.I with hw
    have hwim : w.im = t := by rw [hw]; simp
    have hwimpos : 0 < w.im := by rw [hwim]; exact hpos
    have hw0 : w ≠ 0 := by
      intro h
      rw [h] at hwimpos
      simp at hwimpos
    have hF : xiSquareDescent w ≠ 0 :=
      xiSquareDescent_ne_zero_of_im_ne_zero_of_rh hRH (by rw [hwim]; exact hpos.ne')
    have hlog := im_logDeriv_xiSquareDescent_nonpos_of_rh hRH hwimpos.le hw0 hF
    have hconv := HTGeometry.neg_two_im_deriv_mul_conj_eq
      xiSquareDescent hF
    have hns : 0 ≤ Complex.normSq (xiSquareDescent w) := Complex.normSq_nonneg _
    nlinarith [hconv, hlog, hns]

/-- **RH forces vertical modulus monotonicity of the square descent.** -/
theorem monotoneOn_normSq_xiSquareDescent_vertical_of_rh
    (hRH : RiemannHypothesis) (x : ℝ) :
    MonotoneOn (fun t : ℝ =>
      Complex.normSq (xiSquareDescent ((x : ℂ) + (t : ℂ) * Complex.I))) (Set.Ici 0) := by
  refine HTGeometry.monotoneOn_normSq_vertical_of_neg_im_nonneg
    xiSquareDescent x (convex_Ici 0) (fun t _ =>
      differentiable_xiSquaredSeamEntireQuotient.differentiableAt) ?_
  intro t ht
  exact neg_im_deriv_mul_conj_nonneg_of_rh hRH x ht

/-- The vertical modulus condition `(VM)` of the square descent. -/
def XiSquareDescentVerticalModulus : Prop :=
  ∀ x t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ →
    ‖xiSquareDescent ((x : ℂ) + (t₁ : ℂ) * Complex.I)‖ ≤
      ‖xiSquareDescent ((x : ℂ) + (t₂ : ℂ) * Complex.I)‖

theorem xiSquareDescentVerticalModulus_of_rh (hRH : RiemannHypothesis) :
    XiSquareDescentVerticalModulus := by
  intro x t₁ t₂ h1 h12
  have hmono := monotoneOn_normSq_xiSquareDescent_vertical_of_rh hRH x
    (Set.mem_Ici.mpr h1) (Set.mem_Ici.mpr (h1.trans h12)) h12
  simp only [Complex.normSq_eq_norm_sq] at hmono
  nlinarith [norm_nonneg (xiSquareDescent ((x : ℂ) + (t₁ : ℂ) * Complex.I)),
    norm_nonneg (xiSquareDescent ((x : ℂ) + (t₂ : ℂ) * Complex.I))]

end

end RHTower
