import GaloisForLFunctions.RHTower.XiRelativeResolventTrace
import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardHardyTransport
import GaloisForLFunctions.RHTower.XiWardEdgeCriticalCollapseGram
import GaloisForLFunctions.RHTower.GammaRealHalfPlane
import GaloisForLFunctions.RHTower.XiRealAxisGrowth

/-!
# Interior spectral-trace splitting

Away from the Xi divisor the absolutely convergent full relative resolvent
trace splits exactly into the strict-right relative trace plus the
logarithmic derivative of the complementary Wiener–Hopf factor.  All three
objects converge absolutely at interior points: the splitting realizes the
full-trace/spectral-trace subtraction with no divergent regularization. -/

open Complex

namespace RHTower

noncomputable section

/-- **Interior trace splitting**: away from the Xi divisor,
`fullTrace = rightTrace + logDeriv(nonright factor)` exactly. -/
theorem xiRelativeResolventTrace_eq_right_add_logDeriv_nonright
    {z : ℂ} (hz : XiC z ≠ 0) :
    xiRelativeResolventTrace z =
      xiRightRelativeResolventTrace z +
        logDeriv xiNonrightCanonicalProduct z := by
  have hcan_ne : xiCanonicalProduct z ≠ 0 := by
    intro h
    apply hz
    have hsource := congrFun xiHadamardQuotient_mul_canonicalProduct z
    rw [Pi.mul_apply] at hsource
    rw [← hsource, h, mul_zero]
  have hright_ne : xiRightCanonicalProduct z ≠ 0 := by
    intro h
    apply hcan_ne
    rw [xiCanonicalProduct_eq_right_mul_nonright z, h, zero_mul]
  have hnonright_ne : xiNonrightCanonicalProduct z ≠ 0 := by
    rw [xiNonrightCanonicalProduct]
    exact div_ne_zero hcan_ne hright_ne
  have hfull_diff : DifferentiableAt ℂ xiCanonicalProduct z :=
    (xiCanonicalProduct_analytic z (Set.mem_univ z)).differentiableAt
  have hright_diff : DifferentiableAt ℂ xiRightCanonicalProduct z :=
    (xiRightCanonicalProduct_analytic z (Set.mem_univ z)).differentiableAt
  have hnonright_diff :
      DifferentiableAt ℂ xiNonrightCanonicalProduct z :=
    hfull_diff.div hright_diff hright_ne
  calc xiRelativeResolventTrace z
      = logDeriv xiCanonicalProduct z :=
        (logDeriv_xiCanonicalProduct_eq_relativeResolventTrace hz).symm
    _ = logDeriv (fun w : ℂ => xiRightCanonicalProduct w *
          xiNonrightCanonicalProduct w) z := by
        exact congrFun (congrArg logDeriv
          (funext xiCanonicalProduct_eq_right_mul_nonright)) z
    _ = logDeriv xiRightCanonicalProduct z +
          logDeriv xiNonrightCanonicalProduct z :=
        logDeriv_mul z hright_ne hnonright_ne hright_diff hnonright_diff
    _ = xiRightRelativeResolventTrace z +
          logDeriv xiNonrightCanonicalProduct z := by
        rw [logDeriv_xiRightCanonicalProduct_eq_relativeResolventTrace
          hright_ne]

/-- **Interior decomposition of the Ward response**: away from the rotated
Xi divisor the continued anti-causal response is the rotated FULL trace
minus the rotated complementary-factor logarithmic derivative plus the
boundary self-symbol.  Every summand converges absolutely on the right
half-plane: the response's full-trace/spectral-remainder subtraction is an
exact certified identity, not a divergent regularization. -/
theorem continuedXiAntiCausalWardResponse_eq_full_sub_nonright
    {w : ℂ} (hz : XiC (I * w) ≠ 0) :
    continuedXiAntiCausalWardResponse w =
      2 * I * xiRelativeResolventTrace (I * w) -
        2 * I * logDeriv xiNonrightCanonicalProduct (I * w) +
        xiAntiCausalWardBoundarySelfSymbol := by
  have hsplit := xiRelativeResolventTrace_eq_right_add_logDeriv_nonright hz
  have hright : xiRightRelativeResolventTrace (I * w) =
      xiRelativeResolventTrace (I * w) -
        logDeriv xiNonrightCanonicalProduct (I * w) := by
    rw [hsplit]
    ring
  rw [continuedXiAntiCausalWardResponse,
    continuedXiCenteredAntiCausalWardResponse, hright]
  ring

/-- The completed source's logarithmic derivative splits into the entire
zero-free Hadamard factor and the absolutely summable full trace. -/
theorem logDeriv_XiC_eq_quotient_add_trace {z : ℂ} (hz : XiC z ≠ 0) :
    logDeriv XiC z =
      logDeriv xiHadamardQuotient z + xiRelativeResolventTrace z := by
  have hcan_ne : xiCanonicalProduct z ≠ 0 := by
    intro h
    apply hz
    have hsource := congrFun xiHadamardQuotient_mul_canonicalProduct z
    rw [Pi.mul_apply] at hsource
    rw [← hsource, h, mul_zero]
  have hquot_ne := xiHadamardQuotient_ne_zero z
  have hq_diff : DifferentiableAt ℂ xiHadamardQuotient z :=
    xiHadamardQuotient_differentiable z
  have hc_diff : DifferentiableAt ℂ xiCanonicalProduct z :=
    (xiCanonicalProduct_analytic z (Set.mem_univ z)).differentiableAt
  calc logDeriv XiC z
      = logDeriv (fun w : ℂ => xiHadamardQuotient w *
          xiCanonicalProduct w) z := by
        have h := congrArg logDeriv xiHadamardQuotient_mul_canonicalProduct
        exact (congrFun h z).symm
    _ = logDeriv xiHadamardQuotient z +
          logDeriv xiCanonicalProduct z :=
        logDeriv_mul z hquot_ne hcan_ne hq_diff hc_diff
    _ = logDeriv xiHadamardQuotient z + xiRelativeResolventTrace z := by
        rw [logDeriv_xiCanonicalProduct_eq_relativeResolventTrace hz]

/-- **Master interior identity**: away from the rotated divisor the Ward
response is the rotated logarithmic derivative of the completed source
minus the entire Hadamard and complementary-factor corrections plus the
boundary self-symbol.  This expresses the response through `XiC` itself —
the object welded to the arithmetic side — with every term absolutely
convergent. -/
theorem continuedXiAntiCausalWardResponse_eq_logDeriv_XiC_sub
    {w : ℂ} (hz : XiC (I * w) ≠ 0) :
    continuedXiAntiCausalWardResponse w =
      2 * I * logDeriv XiC (I * w) -
        2 * I * logDeriv xiHadamardQuotient (I * w) -
        2 * I * logDeriv xiNonrightCanonicalProduct (I * w) +
        xiAntiCausalWardBoundarySelfSymbol := by
  rw [continuedXiAntiCausalWardResponse_eq_full_sub_nonright hz]
  have htrace : xiRelativeResolventTrace (I * w) =
      logDeriv XiC (I * w) - logDeriv xiHadamardQuotient (I * w) := by
    rw [logDeriv_XiC_eq_quotient_add_trace hz]
    ring
  rw [htrace]
  ring

/-- Logarithmic-derivative reflection from the functional equation. -/
theorem logDeriv_xi_one_sub (s : ℂ) :
    logDeriv xi (1 - s) = -logDeriv xi s := by
  have hcomp : xi = xi ∘ (fun t : ℂ => 1 - t) :=
    funext fun t => by
      simp only [Function.comp_apply]
      exact (xi_one_sub t).symm
  have hg : HasDerivAt (fun t : ℂ => 1 - t) (-1) s := by
    simpa using (hasDerivAt_id s).const_sub 1
  have h2 := logDeriv_comp (xi_differentiable (1 - s))
    hg.differentiableAt
  rw [hg.deriv] at h2
  have h1 : logDeriv xi s = logDeriv xi (1 - s) * (-1) := by
    conv_lhs => rw [hcomp]
    exact h2
  linear_combination h1

/-- Rotation head: the rotated `XiC` logarithmic derivative is the plain
`xi` logarithmic derivative at the reflected interior point. -/
theorem two_I_logDeriv_XiC_I_mul_eq (w : ℂ) :
    2 * I * logDeriv XiC (I * w) =
      2 * logDeriv xi ((1 / 2 : ℂ) + w) := by
  have hXiC : XiC = xi ∘ (fun z : ℂ => (1 / 2 : ℂ) + z * I) := rfl
  have hg : HasDerivAt (fun z : ℂ => (1 / 2 : ℂ) + z * I) I (I * w) := by
    simpa using ((hasDerivAt_id (I * w)).mul_const I).const_add
      ((1 : ℂ) / 2)
  have hcomp := logDeriv_comp (f := xi)
    (g := fun z : ℂ => (1 / 2 : ℂ) + z * I)
    (xi_differentiable ((1 / 2 : ℂ) + (I * w) * I)) hg.differentiableAt
  rw [hg.deriv] at hcomp
  have harg : (1 / 2 : ℂ) + (I * w) * I = 1 - ((1 / 2 : ℂ) + w) := by
    have hII : (I * w) * I = -w := by
      rw [mul_comm I w, mul_assoc, I_mul_I]
      ring
    rw [hII]
    ring
  rw [hXiC]
  rw [hcomp]
  rw [harg, logDeriv_xi_one_sub ((1 / 2 : ℂ) + w)]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Arithmetic-headed master identity**: away from the rotated divisor
the Ward response is `2·logDeriv xi(½+w)` — the reflected interior
logarithmic derivative of the completed source — minus the entire and
complementary corrections plus the boundary self-symbol. -/
theorem continuedXiAntiCausalWardResponse_eq_two_logDeriv_xi_sub
    {w : ℂ} (hz : XiC (I * w) ≠ 0) :
    continuedXiAntiCausalWardResponse w =
      2 * logDeriv xi ((1 / 2 : ℂ) + w) -
        2 * I * logDeriv xiHadamardQuotient (I * w) -
        2 * I * logDeriv xiNonrightCanonicalProduct (I * w) +
        xiAntiCausalWardBoundarySelfSymbol := by
  rw [continuedXiAntiCausalWardResponse_eq_logDeriv_XiC_sub hz,
    two_I_logDeriv_XiC_I_mul_eq w]

/-- Local `logDeriv` only sees the germ. -/
theorem logDeriv_congr_of_eventuallyEq {f g : ℂ → ℂ} {s : ℂ}
    (h : f =ᶠ[nhds s] g) : logDeriv f s = logDeriv g s := by
  rw [logDeriv, logDeriv]
  simp only [Pi.div_apply]
  rw [h.deriv_eq, h.eq_of_nhds]

/-- On `Re s > 1` the completed source factors as `Γℝ · ζ`. -/
theorem completedRiemannZeta_eq_gammaR_mul_zeta {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta s = Complex.Gammaℝ s * riemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  rw [riemannZeta_def_of_ne_zero hs0]
  have hG : Complex.Gammaℝ s ≠ 0 :=
    Complex.Gammaℝ_ne_zero_of_re_pos (by linarith)
  field_simp

/-- The completed source is nonvanishing on `Re s > 1`. -/
theorem completedRiemannZeta_ne_zero_of_one_lt_re {s : ℂ}
    (hs : 1 < s.re) : completedRiemannZeta s ≠ 0 := by
  rw [completedRiemannZeta_eq_gammaR_mul_zeta hs]
  exact mul_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by linarith))
    (riemannZeta_ne_zero_of_one_lt_re hs)

/-- `logDeriv` splitting of the completed source on `Re s > 1`. -/
theorem logDeriv_completedRiemannZeta_eq {s : ℂ} (hs : 1 < s.re) :
    logDeriv completedRiemannZeta s =
      logDeriv Complex.Gammaℝ s + logDeriv riemannZeta s := by
  have hopen : IsOpen {t : ℂ | 1 < t.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hev : completedRiemannZeta =ᶠ[nhds s]
      fun t : ℂ => Complex.Gammaℝ t * riemannZeta t :=
    Filter.eventually_of_mem (hopen.mem_nhds hs) fun t ht =>
      completedRiemannZeta_eq_gammaR_mul_zeta ht
  rw [logDeriv_congr_of_eventuallyEq hev]
  exact logDeriv_mul s
    (Complex.Gammaℝ_ne_zero_of_re_pos (by linarith))
    (riemannZeta_ne_zero_of_one_lt_re hs)
    (differentiableAt_Gammaℝ_of_re_pos (by linarith))
    (differentiableAt_riemannZeta (by
      intro h
      rw [h] at hs
      norm_num at hs))

/-- `logDeriv` of the corpus `xi` on `Re s > 1`: pole terms plus the
completed factor. -/
theorem logDeriv_xi_eq {s : ℂ} (hs : 1 < s.re) :
    logDeriv xi s =
      s⁻¹ + (s - 1)⁻¹ + logDeriv completedRiemannZeta s := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have hopen : IsOpen {t : ℂ | 1 < t.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hev : xi =ᶠ[nhds s]
      fun t : ℂ => t * (t - 1) / 2 * completedRiemannZeta t :=
    Filter.eventually_of_mem (hopen.mem_nhds hs) fun t ht =>
      xi_eq_mul_completedRiemannZeta
        (by intro h; rw [h] at ht; norm_num at ht)
        (by intro h; rw [h] at ht; norm_num at ht)
  rw [logDeriv_congr_of_eventuallyEq hev]
  have hpoly_ne : s * (s - 1) / 2 ≠ 0 := by
    apply div_ne_zero (mul_ne_zero hs0 hs1')
    norm_num
  have hpoly_diff : DifferentiableAt ℂ
      (fun t : ℂ => t * (t - 1) / 2) s :=
    (differentiableAt_id.mul
      (differentiableAt_id.sub_const 1)).div_const 2
  have hLam_ne := completedRiemannZeta_ne_zero_of_one_lt_re hs
  have hLam_diff : DifferentiableAt ℂ completedRiemannZeta s :=
    differentiableAt_completedZeta hs0 hs1
  have hmul := logDeriv_mul s hpoly_ne hLam_ne hpoly_diff hLam_diff
  rw [hmul]
  have hderiv : HasDerivAt (fun t : ℂ => t * (t - 1) / 2)
      ((1 * (s - 1) + s * 1) / 2) s :=
    ((hasDerivAt_id s).mul ((hasDerivAt_id s).sub_const 1)).div_const 2
  have hld : logDeriv (fun t : ℂ => t * (t - 1) / 2) s =
      s⁻¹ + (s - 1)⁻¹ := by
    rw [logDeriv]
    simp only [Pi.div_apply]
    rw [hderiv.deriv]
    field_simp
  rw [hld]

/-- The von Mangoldt head: on `Re s > 1` the zeta logarithmic derivative
is the negative of the absolutely convergent von Mangoldt `L`-series. -/
theorem logDeriv_riemannZeta_eq_neg_LSeries {s : ℂ} (hs : 1 < s.re) :
    logDeriv riemannZeta s =
      -LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
  rw [ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs,
    logDeriv]
  simp only [Pi.div_apply]
  ring

/-- **Fully opened arithmetic head** on `Re s > 1`:
`logDeriv xi = 1/s + 1/(s−1) + logDeriv Γℝ − L(Λ,·)`. -/
theorem logDeriv_xi_eq_arithmetic {s : ℂ} (hs : 1 < s.re) :
    logDeriv xi s =
      s⁻¹ + (s - 1)⁻¹ + logDeriv Complex.Gammaℝ s -
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s := by
  rw [logDeriv_xi_eq hs, logDeriv_completedRiemannZeta_eq hs,
    logDeriv_riemannZeta_eq_neg_LSeries hs]
  ring

/-- **THE ARITHMETIC RESPONSE IDENTITY**: for `Re w > ½` away from the
rotated divisor, the anti-causal Ward response equals the explicit
arithmetic expression — pole terms, the `Γℝ` factor, and the absolutely
convergent von Mangoldt `L`-series — minus the entire and complementary
corrections plus the boundary self-symbol.  The prime side and the Ward
side are welded by an exact certified identity with every term absolutely
convergent. -/
theorem continuedXiAntiCausalWardResponse_eq_arithmetic
    {w : ℂ} (hw : 1 / 2 < w.re) (hz : XiC (I * w) ≠ 0) :
    continuedXiAntiCausalWardResponse w =
      2 * (((1 / 2 : ℂ) + w)⁻¹ + ((1 / 2 : ℂ) + w - 1)⁻¹ +
        logDeriv Complex.Gammaℝ ((1 / 2 : ℂ) + w) -
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          ((1 / 2 : ℂ) + w)) -
        2 * I * logDeriv xiHadamardQuotient (I * w) -
        2 * I * logDeriv xiNonrightCanonicalProduct (I * w) +
        xiAntiCausalWardBoundarySelfSymbol := by
  have hre : (1 : ℝ) < ((1 / 2 : ℂ) + w).re := by
    have h : ((1 / 2 : ℂ) + w).re = 1 / 2 + w.re := by
      simp [Complex.add_re]
    rw [h]
    linarith
  rw [continuedXiAntiCausalWardResponse_eq_two_logDeriv_xi_sub hz,
    logDeriv_xi_eq_arithmetic hre]

/-- The zero-free Hadamard factor is constant, so its logarithmic
derivative vanishes identically. -/
theorem logDeriv_xiHadamardQuotient_eq_zero (z : ℂ) :
    logDeriv xiHadamardQuotient z = 0 := by
  have hconst : xiHadamardQuotient = fun _ : ℂ => xiHadamardQuotient 0 :=
    funext xiHadamardQuotient_constant
  rw [logDeriv]
  simp only [Pi.div_apply]
  rw [hconst]
  simp

/-- Rearranged interior splitting: the complementary factor's logarithmic
derivative is the full trace minus the strict-right trace. -/
theorem logDeriv_nonright_eq_full_sub_right {z : ℂ} (hz : XiC z ≠ 0) :
    logDeriv xiNonrightCanonicalProduct z =
      xiRelativeResolventTrace z - xiRightRelativeResolventTrace z := by
  have h := xiRelativeResolventTrace_eq_right_add_logDeriv_nonright hz
  linear_combination -h

/-- **Per-term interior positivity**: every non-right divisor term has
nonnegative rotated real part at interior points above the strip. -/
theorem re_two_I_mul_relativeResolventTerm_nonneg
    {q : XiZeroCopy} (hq : (I * xiSpectralPoint q).re ≤ 0)
    {z₀ : ℂ} (hz₀ : 1 / 2 < z₀.im) :
    0 ≤ (2 * I * xiRelativeResolventTerm z₀ q).re := by
  have hIm : 0 ≤ (xiSpectralPoint q).im := by
    have h : (I * xiSpectralPoint q).re = -(xiSpectralPoint q).im := by
      simp [Complex.mul_re]
    rw [h] at hq
    linarith
  have hstrip := abs_re_I_mul_xiSpectralPoint_le_half q
  have hImlt : (xiSpectralPoint q).im < 1 / 2 := by
    have h : (I * xiSpectralPoint q).re = -(xiSpectralPoint q).im := by
      simp [Complex.mul_re]
    rw [h] at hstrip
    have := (abs_lt.mp hstrip).1
    linarith
  have hsub_ne : xiSpectralPoint q - z₀ ≠ 0 := by
    intro h
    have him := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.zero_im] at him
    linarith
  have hval : (2 * I * xiRelativeResolventTerm z₀ q).re =
      2 * (xiSpectralPoint q).im / Complex.normSq (xiSpectralPoint q) +
        2 * (z₀.im - (xiSpectralPoint q).im) /
          Complex.normSq (xiSpectralPoint q - z₀) := by
    rw [xiRelativeResolventTerm]
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im, Complex.inv_re, Complex.inv_im, Complex.I_re,
      Complex.I_im, Complex.re_ofNat, Complex.im_ofNat]
    ring
  rw [hval]
  have hn1 : 0 < Complex.normSq (xiSpectralPoint q) :=
    Complex.normSq_pos.mpr (xiSpectralPoint_ne_zero q)
  have hn2 : 0 < Complex.normSq (xiSpectralPoint q - z₀) :=
    Complex.normSq_pos.mpr hsub_ne
  have e1 := div_nonneg
    (by linarith : (0 : ℝ) ≤ 2 * (xiSpectralPoint q).im) hn1.le
  have e2 := div_nonneg
    (by linarith : (0 : ℝ) ≤ 2 * (z₀.im - (xiSpectralPoint q).im)) hn2.le
  linarith

/-- **The interior discard**: the rotated complementary logarithmic
derivative has nonnegative real part at every interior point `Re w > ½`
away from the rotated divisor. -/
theorem re_two_I_logDeriv_nonright_nonneg {w : ℂ} (hw : 1 / 2 < w.re)
    (hz : XiC (I * w) ≠ 0) :
    0 ≤ (2 * I * logDeriv xiNonrightCanonicalProduct (I * w)).re := by
  have hz₀ : 1 / 2 < (I * w).im := by
    have h : (I * w).im = w.re := by simp [Complex.mul_im]
    rw [h]
    exact hw
  have hcan_ne : xiCanonicalProduct (I * w) ≠ 0 := by
    intro h
    apply hz
    have hsource := congrFun xiHadamardQuotient_mul_canonicalProduct (I * w)
    rw [Pi.mul_apply] at hsource
    rw [← hsource, h, mul_zero]
  have hright_ne : xiRightCanonicalProduct (I * w) ≠ 0 := by
    intro h
    apply hcan_ne
    rw [xiCanonicalProduct_eq_right_mul_nonright (I * w), h, zero_mul]
  have hsumF := summable_xiRelativeResolventTerm hz
  have hsumR := summable_xiRightRelativeResolventTerm hright_ne
  have hreF : (2 * I * xiRelativeResolventTrace (I * w)).re =
      ∑' q : XiZeroCopy, (2 * I * xiRelativeResolventTerm (I * w) q).re := by
    rw [xiRelativeResolventTrace, ← tsum_mul_left,
      Complex.re_tsum (hsumF.mul_left (2 * I))]
  have hreR : (2 * I * xiRightRelativeResolventTrace (I * w)).re =
      ∑' q : XiRightZeroCopy,
        (2 * I * xiRelativeResolventTerm (I * w) q.1).re := by
    rw [xiRightRelativeResolventTrace, ← tsum_mul_left,
      Complex.re_tsum (hsumR.mul_left (2 * I))]
    exact tsum_congr fun q => rfl
  have hsumreF : Summable (fun q : XiZeroCopy =>
      (2 * I * xiRelativeResolventTerm (I * w) q).re) :=
    (Complex.hasSum_re (hsumF.mul_left (2 * I)).hasSum).summable
  have hsplit := hsumreF.tsum_subtype_add_tsum_subtype_compl
    {q : XiZeroCopy | 0 < (I * xiSpectralPoint q).re}
  have hnonneg : 0 ≤ ∑' q : ↑{q : XiZeroCopy |
      0 < (I * xiSpectralPoint q).re}ᶜ,
      (2 * I * xiRelativeResolventTerm (I * w) q.1).re :=
    tsum_nonneg fun q =>
      re_two_I_mul_relativeResolventTerm_nonneg
        (not_lt.mp q.2) hz₀
  have hld : logDeriv xiNonrightCanonicalProduct (I * w) =
      xiRelativeResolventTrace (I * w) -
        xiRightRelativeResolventTrace (I * w) :=
    logDeriv_nonright_eq_full_sub_right hz
  have hexpand : (2 * I * logDeriv xiNonrightCanonicalProduct (I * w)).re =
      (2 * I * xiRelativeResolventTrace (I * w)).re -
        (2 * I * xiRightRelativeResolventTrace (I * w)).re := by
    rw [hld]
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re,
      Complex.sub_im]
    ring
  rw [hexpand, hreF, hreR]
  have hright_eq :
      (∑' q : XiRightZeroCopy,
          (2 * I * xiRelativeResolventTerm (I * w) q.1).re) =
        ∑' q : ↑{q : XiZeroCopy |
            0 < (I * xiSpectralPoint q).re},
          (2 * I * xiRelativeResolventTerm (I * w) q.1).re := rfl
  rw [hright_eq]
  linarith [hsplit, hnonneg]

/-- **UNCONDITIONAL ARITHMETIC UPPER BOUND on the Ward response** at
interior points: discarding the nonnegative complementary spectral mass
bounds the response's real part by the explicit arithmetic side. -/
theorem re_continuedXiAntiCausalWardResponse_le_arithmetic
    {w : ℂ} (hw : 1 / 2 < w.re) (hz : XiC (I * w) ≠ 0) :
    (continuedXiAntiCausalWardResponse w).re ≤
      (2 * (((1 / 2 : ℂ) + w)⁻¹ + ((1 / 2 : ℂ) + w - 1)⁻¹ +
        logDeriv Complex.Gammaℝ ((1 / 2 : ℂ) + w) -
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          ((1 / 2 : ℂ) + w))).re +
        (xiAntiCausalWardBoundarySelfSymbol).re := by
  have hid := continuedXiAntiCausalWardResponse_eq_arithmetic hw hz
  have hquot := logDeriv_xiHadamardQuotient_eq_zero (I * w)
  rw [hquot, mul_zero, sub_zero] at hid
  have hdiscard := re_two_I_logDeriv_nonright_nonneg hw hz
  have hre := congrArg Complex.re hid
  rw [Complex.add_re, Complex.sub_re] at hre
  linarith [hre, hdiscard]

/-- The certified interior arithmetic bound as a single named quantity. -/
noncomputable def xiWardInteriorArithmeticBound (w : ℂ) : ℝ :=
  (2 * (((1 / 2 : ℂ) + w)⁻¹ + ((1 / 2 : ℂ) + w - 1)⁻¹ +
    logDeriv Complex.Gammaℝ ((1 / 2 : ℂ) + w) -
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      ((1 / 2 : ℂ) + w))).re +
  (xiAntiCausalWardBoundarySelfSymbol).re

theorem re_continuedXiAntiCausalWardResponse_le_interiorBound
    {w : ℂ} (hw : 1 / 2 < w.re) (hz : XiC (I * w) ≠ 0) :
    (continuedXiAntiCausalWardResponse w).re ≤
      xiWardInteriorArithmeticBound w := by
  unfold xiWardInteriorArithmeticBound
  exact re_continuedXiAntiCausalWardResponse_le_arithmetic hw hz

/-- **Per-pair interior window quantum**: a strict-right pair whose height
lies within `δ` of the probe height deposits at least
`2h/((h+½)² + δ²)` into the interior response value. -/
theorem interior_pair_quantum {h c δ : ℝ} (hh : 0 < h)
    (q : XiRightUpperZeroCopy)
    (hwin : ((xiRightCenteredZero q.1).im - c) ^ 2 ≤ δ ^ 2) :
    2 * h / ((h + 1 / 2) ^ 2 + δ ^ 2) ≤
      (xiAntiCausalWardSchwarzPairResponse q
        (((h : ℝ) : ℂ) + I * ((c : ℝ) : ℂ))).re := by
  rw [re_xiAntiCausalWardSchwarzPairResponse_line_eq q h c]
  have hre := xiRightCenteredZero_re_pos q.1
  have hlt := (abs_lt.mp (abs_xiRightCenteredZero_re_lt_half q.1)).2
  have hx : 0 < h + (xiRightCenteredZero q.1).re := by linarith
  have hfirst : 0 ≤ 2 * ((h + (xiRightCenteredZero q.1).re) /
      ((h + (xiRightCenteredZero q.1).re) ^ 2 +
        (c + (xiRightCenteredZero q.1).im) ^ 2)) := by positivity
  have hsecond : 2 * h / ((h + 1 / 2) ^ 2 + δ ^ 2) ≤
      2 * ((h + (xiRightCenteredZero q.1).re) /
        ((h + (xiRightCenteredZero q.1).re) ^ 2 +
          (c - (xiRightCenteredZero q.1).im) ^ 2)) := by
    have hden : 0 < (h + (xiRightCenteredZero q.1).re) ^ 2 +
        (c - (xiRightCenteredZero q.1).im) ^ 2 := by positivity
    have hdenle : (h + (xiRightCenteredZero q.1).re) ^ 2 +
        (c - (xiRightCenteredZero q.1).im) ^ 2 ≤
        (h + 1 / 2) ^ 2 + δ ^ 2 := by
      have h1 : (h + (xiRightCenteredZero q.1).re) ^ 2 ≤
          (h + 1 / 2) ^ 2 := by nlinarith
      linarith [hwin]
    have h0 : (0 : ℝ) ≤ 2 * (h + (xiRightCenteredZero q.1).re) := by
      linarith
    have hnum : 2 * h ≤ 2 * (h + (xiRightCenteredZero q.1).re) := by
      linarith
    have hcmp := div_le_div₀ h0 hnum hden hdenle
    calc 2 * h / ((h + 1 / 2) ^ 2 + δ ^ 2)
        ≤ 2 * (h + (xiRightCenteredZero q.1).re) /
            ((h + (xiRightCenteredZero q.1).re) ^ 2 +
              (c - (xiRightCenteredZero q.1).im) ^ 2) := hcmp
      _ = 2 * ((h + (xiRightCenteredZero q.1).re) /
            ((h + (xiRightCenteredZero q.1).re) ^ 2 +
              (c - (xiRightCenteredZero q.1).im) ^ 2)) := by
          rw [mul_div_assoc]
  linarith

/-- **THE WINDOW-CLEARING ENGINE**: if the certified interior arithmetic
bound at probe `w₀ = h + ic` falls below the window quantum, then no
strict-right pair has height within `δ` of `c`.  A single certified
arithmetic inequality at one interior point clears a whole height window
of off-critical zeros. -/
theorem xiWard_window_clearing {h c δ : ℝ} (hh : 1 / 2 < h)
    (hz : XiC (I * (((h : ℝ) : ℂ) + I * ((c : ℝ) : ℂ))) ≠ 0)
    (hA : xiWardInteriorArithmeticBound
        (((h : ℝ) : ℂ) + I * ((c : ℝ) : ℂ)) <
      2 * h / ((h + 1 / 2) ^ 2 + δ ^ 2))
    (q : XiRightUpperZeroCopy) :
    δ ^ 2 < ((xiRightCenteredZero q.1).im - c) ^ 2 := by
  by_contra hcon
  push Not at hcon
  have hwin : ((xiRightCenteredZero q.1).im - c) ^ 2 ≤ δ ^ 2 := hcon
  have hq := interior_pair_quantum (by linarith : (0:ℝ) < h) q hwin
  have hwre : (0 : ℝ) < ((((h : ℝ) : ℂ) + I * ((c : ℝ) : ℂ))).re := by
    norm_num [Complex.add_re, Complex.mul_re]
    linarith
  have hdom := re_xiAntiCausalWardSchwarzPairResponse_le_continued q hwre
  have hwre2 : (1 / 2 : ℝ) <
      ((((h : ℝ) : ℂ) + I * ((c : ℝ) : ℂ))).re := by
    norm_num [Complex.add_re, Complex.mul_re]
    linarith
  have hup := re_continuedXiAntiCausalWardResponse_le_interiorBound
    hwre2 hz
  linarith

/-- Complex-to-real domination of the von Mangoldt `L`-series: the modulus
never exceeds the real series at the real part. -/
theorem norm_LSeries_vonMangoldt_le {s : ℂ} (hs : 1 < s.re) :
    ‖LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s‖ ≤
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) /
        (n : ℝ) ^ s.re := by
  have hsum := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hnorm : Summable (fun n : ℕ =>
      ‖LSeries.term
        (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s n‖) :=
    summable_norm_iff.mpr hsum
  have hle := norm_tsum_le_tsum_norm hnorm
  rw [LSeries]
  refine le_trans hle (le_of_eq ?_)
  apply tsum_congr
  intro n
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with h0 | h0
  · subst h0
    simp
  · rw [if_neg h0, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]

/-- The `Γℝ` logarithmic derivative splits into the exact constant
`−(log π)/2` and half the digamma at half the argument. -/
theorem logDeriv_Gammaℝ_eq {s : ℂ} (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s =
      -((Real.log Real.pi : ℂ) / 2) + Complex.digamma (s / 2) / 2 := by
  have hfun : Complex.Gammaℝ = fun z : ℂ =>
      (Real.pi : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2) :=
    funext fun z => Complex.Gammaℝ_def z
  have hπ0 : (Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hlin : HasDerivAt (fun z : ℂ => -z / 2) (-1 / 2) s := by
    simpa using (hasDerivAt_id s).neg.div_const 2
  have hf : HasDerivAt (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2))
      ((Real.pi : ℂ) ^ (-s / 2) * Complex.log (Real.pi : ℂ) * (-1 / 2))
      s := HasDerivAt.const_cpow hlin (Or.inl hπ0)
  have hfne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := by
    intro h
    rcases (Complex.cpow_eq_zero_iff _ _).mp h with ⟨h0, _⟩
    exact hπ0 h0
  have hnon : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m h
    have hre := congrArg Complex.re h
    have hdiv : (s / 2).re = s.re / 2 := by
      rw [Complex.div_re]
      simp
      ring
    rw [hdiv] at hre
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hg_diff : DifferentiableAt ℂ
      (fun z : ℂ => Complex.Gamma (z / 2)) s :=
    (Complex.differentiableAt_Gamma _ hnon).comp s
      (differentiableAt_id.div_const 2)
  have hgne : Complex.Gamma (s / 2) ≠ 0 := Complex.Gamma_ne_zero hnon
  rw [hfun]
  rw [logDeriv_mul s hfne hgne hf.differentiableAt hg_diff]
  have h1 : logDeriv (fun z : ℂ => (Real.pi : ℂ) ^ (-z / 2)) s =
      -((Real.log Real.pi : ℂ) / 2) := by
    rw [logDeriv]
    simp only [Pi.div_apply]
    rw [hf.deriv, ← Complex.ofReal_log Real.pi_pos.le]
    field_simp
  have h2 : logDeriv (fun z : ℂ => Complex.Gamma (z / 2)) s =
      Complex.digamma (s / 2) / 2 := by
    have hcomp := logDeriv_comp (f := Complex.Gamma)
      (g := fun z : ℂ => z / 2) (x := s)
      (Complex.differentiableAt_Gamma _ hnon)
      (differentiableAt_id.div_const 2)
    rw [show (fun z : ℂ => Complex.Gamma (z / 2)) =
        Complex.Gamma ∘ (fun z : ℂ => z / 2) from rfl, hcomp]
    have hd : deriv (fun z : ℂ => z / 2) s = 1 / 2 := by
      simp [deriv_div_const]
    rw [hd]
    rw [show logDeriv Complex.Gamma (s / 2) =
        Complex.digamma (s / 2) from rfl]
    ring
  rw [h1, h2]

/-- The real von Mangoldt Dirichlet series is summable for `σ > 1`. -/
theorem summable_vonMangoldt_div_rpow {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ) := by
  have hre : (1 : ℝ) < ((σ : ℂ)).re := by simpa using hσ
  have hsum := ArithmeticFunction.LSeriesSummable_vonMangoldt hre
  have hnorm : Summable (fun n : ℕ =>
      ‖LSeries.term
        (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n‖) :=
    summable_norm_iff.mpr hsum
  apply hnorm.congr
  intro n
  rw [LSeries.norm_term_eq]
  rcases eq_or_ne n 0 with h0 | h0
  · subst h0
    simp
  · rw [if_neg h0, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      Complex.ofReal_re]

/-- Any finite partial sum bounds the real von Mangoldt series below. -/
theorem finiteSum_le_tsum_vonMangoldt {σ : ℝ} (hσ : 1 < σ)
    (F : Finset ℕ) :
    ∑ n ∈ F, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ ≤
      ∑' n : ℕ,
        (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ :=
  (summable_vonMangoldt_div_rpow hσ).sum_le_tsum F fun n _ =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.rpow_nonneg (Nat.cast_nonneg n) σ)

/-- At a real point the von Mangoldt `L`-series is the real series. -/
theorem LSeries_vonMangoldt_ofReal (σ : ℝ) :
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) =
      ((∑' n : ℕ,
        (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ σ : ℝ) : ℂ) := by
  rw [LSeries, Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  rcases eq_or_ne n 0 with h0 | h0
  · subst h0
    rw [LSeries.term_zero]
    simp
  · rw [LSeries.term_of_ne_zero h0, Complex.ofReal_div,
      Complex.ofReal_cpow (Nat.cast_nonneg n)]
    norm_num

/-- Certified numeric floor for the real von Mangoldt series at `σ = 2`:
the five prime-power terms at `2, 3, 4, 8, 9` already exceed `0.35`. -/
theorem vonMangoldt_tsum_two_ge :
    (0.35 : ℝ) ≤ ∑' n : ℕ,
      (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ (2 : ℝ) := by
  have hle := finiteSum_le_tsum_vonMangoldt
    (by norm_num : (1 : ℝ) < 2) ({2, 3, 4, 8, 9} : Finset ℕ)
  refine le_trans ?_ hle
  rw [show ({2, 3, 4, 8, 9} : Finset ℕ) =
      insert 2 (insert 3 (insert 4 (insert 8 {9}))) from rfl]
  rw [Finset.sum_insert (by norm_num), Finset.sum_insert (by norm_num),
    Finset.sum_insert (by norm_num), Finset.sum_insert (by norm_num),
    Finset.sum_singleton]
  have h2 := ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
  have h3 := ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three
  have h4 : ArithmeticFunction.vonMangoldt 4 = Real.log 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 from by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), h2]
    norm_num
  have h8 : ArithmeticFunction.vonMangoldt 8 = Real.log 2 := by
    rw [show (8 : ℕ) = 2 ^ 3 from by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), h2]
    norm_num
  have h9 : ArithmeticFunction.vonMangoldt 9 = Real.log 3 := by
    rw [show (9 : ℕ) = 3 ^ 2 from by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), h3]
    norm_num
  rw [h2, h3, h4, h8, h9]
  have hrp : ∀ n : ℕ, ((n : ℝ)) ^ (2 : ℝ) = ((n : ℝ)) ^ (2 : ℕ) := by
    intro n
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num,
      Real.rpow_natCast]
  rw [hrp 2, hrp 3, hrp 4, hrp 8, hrp 9]
  have hlog2 := Real.log_two_gt_d9
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
    calc Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      _ < 3 := by norm_num
  push_cast
  nlinarith [hlog2, hlog3]

theorem exp_point_one_lt : Real.exp 0.1 < 1.106 := by
  have hb := Real.exp_bound (x := 0.1) (by norm_num)
    (n := 3) (by norm_num)
  have hsum : ∑ m ∈ Finset.range 3, (0.1 : ℝ) ^ m / m.factorial =
      1.105 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at hb
  have h2 := (abs_le.mp hb).2
  have herr : (|0.1| : ℝ) ^ 3 * ((3 : ℕ).succ /
      ((3 : ℕ).factorial * (3 : ℕ))) ≤ 0.000223 := by
    norm_num [Nat.factorial]
  linarith

theorem log_pi_gt_one_point_one : (1.1 : ℝ) < Real.log Real.pi := by
  rw [Real.lt_log_iff_exp_lt Real.pi_pos]
  have h1 : Real.exp 1.1 = Real.exp 1 * Real.exp 0.1 := by
    rw [← Real.exp_add]
    norm_num
  rw [h1]
  have he := Real.exp_one_lt_d9
  have h0 := exp_point_one_lt
  have hp1 := Real.exp_pos 1
  have hp0 := Real.exp_pos 0.1
  have hstep : Real.exp 1 * Real.exp 0.1 < 3.14 := by
    nlinarith
  exact hstep.trans Real.pi_gt_d2

theorem exp_point_six_lt : Real.exp 0.6 < 1.8232 := by
  have hb := Real.exp_bound (x := 0.6) (by norm_num)
    (n := 5) (by norm_num)
  have hsum : ∑ m ∈ Finset.range 5, (0.6 : ℝ) ^ m / m.factorial =
      1.8214 := by
    norm_num [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at hb
  have h2 := (abs_le.mp hb).2
  have herr : (|0.6| : ℝ) ^ 5 * ((5 : ℕ).succ /
      ((5 : ℕ).factorial * (5 : ℕ))) ≤ 0.0008 := by
    norm_num [Nat.factorial]
  linarith

theorem log_five_gt : (1.6 : ℝ) < Real.log 5 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 5)]
  have h1 : Real.exp 1.6 = Real.exp 1 * Real.exp 0.6 := by
    rw [← Real.exp_add]
    norm_num
  rw [h1]
  have he := Real.exp_one_lt_d9
  have h0 := exp_point_six_lt
  have hp1 := Real.exp_pos 1
  have hp0 := Real.exp_pos 0.6
  nlinarith

/-- Sharpened certified floor with the `5`-term:
`0.414 ≤ Σ′ Λ(n)/n²`. -/
theorem vonMangoldt_tsum_two_ge' :
    (0.414 : ℝ) ≤ ∑' n : ℕ,
      (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ (2 : ℝ) := by
  have hle := finiteSum_le_tsum_vonMangoldt
    (by norm_num : (1 : ℝ) < 2) ({2, 3, 4, 5, 8, 9} : Finset ℕ)
  refine le_trans ?_ hle
  rw [show ({2, 3, 4, 5, 8, 9} : Finset ℕ) =
      insert 2 (insert 3 (insert 4 (insert 5 (insert 8 {9})))) from rfl]
  rw [Finset.sum_insert (by norm_num), Finset.sum_insert (by norm_num),
    Finset.sum_insert (by norm_num), Finset.sum_insert (by norm_num),
    Finset.sum_insert (by norm_num), Finset.sum_singleton]
  have h2 := ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
  have h3 := ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three
  have h5 := ArithmeticFunction.vonMangoldt_apply_prime
    (by norm_num : Nat.Prime 5)
  have h4 : ArithmeticFunction.vonMangoldt 4 = Real.log 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 from by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), h2]
    norm_num
  have h8 : ArithmeticFunction.vonMangoldt 8 = Real.log 2 := by
    rw [show (8 : ℕ) = 2 ^ 3 from by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), h2]
    norm_num
  have h9 : ArithmeticFunction.vonMangoldt 9 = Real.log 3 := by
    rw [show (9 : ℕ) = 3 ^ 2 from by norm_num,
      ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), h3]
    norm_num
  rw [h2, h3, h4, h5, h8, h9]
  have hrp : ∀ n : ℕ, ((n : ℝ)) ^ (2 : ℝ) = ((n : ℝ)) ^ (2 : ℕ) := by
    intro n
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num,
      Real.rpow_natCast]
  rw [hrp 2, hrp 3, hrp 4, hrp 5, hrp 8, hrp 9]
  have hlog2 := Real.log_two_gt_d9
  have hlog3 : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
    calc Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
      _ < 3 := by norm_num
  have hlog5 := log_five_gt
  push_cast
  nlinarith [hlog2, hlog3, hlog5]

/-- The boundary self-symbol is the Ward response at the origin: the
centered part vanishes there. -/
theorem continuedXiAntiCausalWardResponse_zero :
    continuedXiAntiCausalWardResponse 0 =
      xiAntiCausalWardBoundarySelfSymbol := by
  rw [continuedXiAntiCausalWardResponse,
    continuedXiCenteredAntiCausalWardResponse]
  simp

/-- The interior probe avoids the rotated divisor: the probe value is
`xi(2) = Λ(2) ≠ 0`. -/
theorem XiC_probe_ne_zero :
    XiC (I * (((3 / 2 : ℝ) : ℂ) + I * ((0 : ℝ) : ℂ))) ≠ 0 := by
  have harg : XiC (I * (((3 / 2 : ℝ) : ℂ) + I * ((0 : ℝ) : ℂ))) =
      xi (-1) := by
    rw [XiC]
    norm_num
    rw [show ((1 : ℂ) / 2 + I * (3 / 2) * I) = -1 from by
      rw [show (I * (3 / 2 : ℂ) * I) = I * I * (3 / 2) from by ring,
        Complex.I_mul_I]
      norm_num]
  rw [harg, show ((-1 : ℂ)) = 1 - (2 : ℂ) from by norm_num, xi_one_sub]
  have h2 : xi 2 = 2 * (2 - 1) / 2 * completedRiemannZeta 2 :=
    xi_eq_mul_completedRiemannZeta (by norm_num) (by norm_num)
  rw [h2]
  have h3 : completedRiemannZeta 2 ≠ 0 :=
    completedRiemannZeta_ne_zero_of_one_lt_re (by norm_num)
  intro h
  apply h3
  have hco : ((2 : ℂ) * (2 - 1) / 2) = 1 := by norm_num
  rw [hco, one_mul] at h
  exact h

/-- The Euler–Mascheroni constant exceeds `1/2` (mathlib squeeze). -/
theorem one_half_lt_gamma :
    (1 / 2 : ℝ) < Real.eulerMascheroniConstant :=
  lt_trans Real.one_half_lt_eulerMascheroniSeq_six
    (Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 6)

/-- Certified evaluation of the interior arithmetic bound at the probe
`w₀ = 3/2`: at most `0.572` plus the central boundary contact. -/
theorem interiorBound_probe_le {β : ℝ}
    (hB : (xiAntiCausalWardBoundarySelfSymbol).re ≤ β) :
    xiWardInteriorArithmeticBound (((3 / 2 : ℝ) : ℂ) + I * ((0 : ℝ) : ℂ))
      ≤ 0.572 + β := by
  unfold xiWardInteriorArithmeticBound
  have hs : ((1 / 2 : ℂ) + (((3 / 2 : ℝ) : ℂ) + I * ((0 : ℝ) : ℂ))) =
      (2 : ℂ) := by
    norm_num
  rw [hs]
  have hΓ : logDeriv Complex.Gammaℝ (2 : ℂ) =
      -((Real.log Real.pi : ℂ) / 2) +
        -(((Real.eulerMascheroniConstant : ℝ) : ℂ)) / 2 := by
    rw [logDeriv_Gammaℝ_eq (by norm_num : (0 : ℝ) < ((2 : ℂ)).re)]
    rw [show ((2 : ℂ) / 2) = 1 by norm_num, Complex.digamma_one]
  have hL : LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
      (2 : ℂ) = ((∑' n : ℕ,
        (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ (2 : ℝ) :
          ℝ) : ℂ) := by
    rw [show ((2 : ℂ)) = (((2 : ℝ)) : ℂ) from by norm_num,
      LSeries_vonMangoldt_ofReal]
  rw [hΓ, hL]
  have hre : ((2 : ℂ) * ((2 : ℂ)⁻¹ + ((2 : ℂ) - 1)⁻¹ +
      (-((Real.log Real.pi : ℂ) / 2) +
        -(((Real.eulerMascheroniConstant : ℝ) : ℂ)) / 2) -
      ((∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) /
        (n : ℝ) ^ (2 : ℝ) : ℝ) : ℂ))).re =
      3 - Real.log Real.pi - Real.eulerMascheroniConstant -
        2 * (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) /
          (n : ℝ) ^ (2 : ℝ)) := by
    simp only [Complex.mul_re, Complex.add_re, Complex.sub_re,
      Complex.neg_re, Complex.div_re, Complex.inv_re, Complex.ofReal_re,
      Complex.re_ofNat, Complex.im_ofNat, Complex.one_re, Complex.one_im,
      Complex.add_im, Complex.sub_im, Complex.neg_im,
      Complex.div_im, Complex.inv_im, Complex.ofReal_im,
      Complex.normSq_apply]
    ring
  rw [hre]
  have hπ := log_pi_gt_one_point_one
  have hγ := one_half_lt_gamma
  have hLb := vonMangoldt_tsum_two_ge'
  linarith

/-- **CENTRAL-WINDOW CLEARING (boundary-conditional)**: if the central
boundary contact is at most `0.028`, then every strict-right pair has
height beyond `1` — the unit window at the origin is zero-free. -/
theorem xiWard_centralWindow_clearing
    (hB : (xiAntiCausalWardBoundarySelfSymbol).re ≤ 0.027)
    (q : XiRightUpperZeroCopy) :
    (1 : ℝ) < ((xiRightCenteredZero q.1).im) ^ 2 := by
  have hclear := xiWard_window_clearing (h := 3 / 2) (c := 0) (δ := 1)
    (by norm_num) XiC_probe_ne_zero
    (by
      have hbound := interiorBound_probe_le hB
      have hnum : (0.572 : ℝ) + 0.027 <
          2 * (3 / 2) / ((3 / 2 + 1 / 2) ^ 2 + 1 ^ 2) := by norm_num
      linarith) q
  simpa using hclear

end

end RHTower
