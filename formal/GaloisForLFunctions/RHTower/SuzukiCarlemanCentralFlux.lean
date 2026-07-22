import GaloisForLFunctions.RHTower.SuzukiCarlemanEvenPoleCarrier
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstMoment

/-!
# Suzuki central source-flux obstruction

The admissible two-shift characteristic is a product of two odd source characteristics.  When
their central zeros are simple, the product has a forced double zero at the functional-equation
fixed point.  The associated odd exterior Weyl quotient therefore has a central simple pole.

This file computes its residue in the Xi-real normalized coordinate.  It splits into the strictly
positive completed-Xi curvature `-XiC''(0) / XiC(0)` and one finite-aperture boundary-source flux.
A Herglotz
realization can have only nonpositive real residue at a real pole, so positivity forces the source
flux below the strictly negative threshold `XiC''(0) / XiC(0)`.  Thus the compact source cannot be
discarded, treated as a harmless normalization, or replaced by a finite Donoghue quotient.

The Neumann comparison channel can also be removed exactly from this obstruction.  Its physical
central right-triangle value depends only on the first moment of the odd source, hence is a fixed multiple
of the characteristic derivative.  Because that multiple is linear in the form shift, affine
sewing annihilates it.  The surviving central flux is therefore an Euler--Gamma source invariant,
not a consequence of positivity of the finite Neumann comparison operator.

No estimate, numerical computation, RH assumption, or unproved positivity premise is used.
-/

open Complex Filter Topology GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

private theorem tendsto_div_self_of_hasDerivAt_zero
    {F : ℂ → ℂ} {d : ℂ} (hF : HasDerivAt F d 0) (hF0 : F 0 = 0) :
    Tendsto (fun z : ℂ => F z / z) (𝓝[≠] 0) (𝓝 d) := by
  have hslope := hasDerivAt_iff_tendsto_slope.mp hF
  refine hslope.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z _hz
  rw [slope_def_field, hF0]
  simp

/-- A Herglotz function can only have nonpositive real residue at a real pole. -/
theorem residue_re_nonpos_of_upperHalfPlane_im_nonneg
    {m : ℂ → ℂ} {x : ℝ} {r : ℂ}
    (hHerglotz : ∀ z : ℂ, 0 < z.im → 0 ≤ (m z).im)
    (hresidue : Tendsto (fun z : ℂ => (z - (x : ℂ)) * m z)
      (𝓝[≠] (x : ℂ)) (𝓝 r)) :
    r.re ≤ 0 := by
  let path : ℝ → ℂ := fun y => (x : ℂ) + I * (y : ℂ)
  have hpathNhds : Tendsto path (𝓝[>] 0) (𝓝 (x : ℂ)) := by
    have hcont : ContinuousAt path 0 := by fun_prop
    simpa only [path, Complex.ofReal_zero, mul_zero, add_zero] using
      hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hpathMem : ∀ᶠ y : ℝ in 𝓝[>] 0, path y ∈ ({(x : ℂ)} : Set ℂ)ᶜ := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [Set.mem_Ioi] at hy
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, path]
    intro heq
    have him := congrArg Complex.im heq
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, I_re, zero_mul,
      I_im, one_mul, zero_add] at him
    exact hy.ne' him
  have hpath : Tendsto path (𝓝[>] 0) (𝓝[≠] (x : ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hpathNhds, hpathMem⟩
  have hlim := hresidue.comp hpath
  have hre : Tendsto
      (fun y : ℝ => ((path y - (x : ℂ)) * m (path y)).re)
      (𝓝[>] 0) (𝓝 r.re) :=
    (Complex.continuous_re.tendsto r).comp hlim
  exact isClosed_Iic.mem_of_tendsto hre (by
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hypos : 0 < y := hy
    have hnonneg := hHerglotz (path y) (by simp [path, hypos])
    change ((path y - (x : ℂ)) * m (path y)).re ≤ 0
    have hdiff : path y - (x : ℂ) = I * (y : ℂ) := by
      simp only [path, add_sub_cancel_left]
    rw [hdiff]
    simp only [Complex.mul_re, Complex.mul_im, I_re, I_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, mul_zero, one_mul, zero_add, sub_zero]
    simpa only [zero_sub] using
      (neg_nonpos.mpr (mul_nonneg hypos.le hnonneg)))

/-- Exact central residue of Suzuki's zero-shift reciprocal-Xi multiplier. -/
theorem tendsto_z_mul_suzukiZeroShiftMultiplier :
    Tendsto
      (fun z : ℂ => z * suzukiShiftedXiMultiplier 0 z)
      (𝓝[≠] 0)
      (𝓝 (deriv (deriv XiC) 0 / XiC 0)) := by
  have hXi1 : deriv XiC 0 = 0 := by
    have h := deriv_XiC_neg 0
    have h' : deriv XiC 0 = -deriv XiC 0 := by simpa only [neg_zero] using h
    have hsum : deriv XiC 0 + deriv XiC 0 = 0 :=
      eq_neg_iff_add_eq_zero.mp h'
    have htwo : (2 : ℂ) * deriv XiC 0 = 0 := by
      simpa only [two_mul] using hsum
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hXi2 : HasDerivAt (deriv XiC) (deriv (deriv XiC) 0) 0 :=
    ((XiC_analytic 0 (Set.mem_univ 0)).deriv).differentiableAt.hasDerivAt
  have hnum :
      Tendsto (fun z : ℂ => deriv XiC z / z) (𝓝[≠] 0)
        (𝓝 (deriv (deriv XiC) 0)) :=
    tendsto_div_self_of_hasDerivAt_zero hXi2 hXi1
  have hden : Tendsto XiC (𝓝[≠] 0) (𝓝 (XiC 0)) :=
    (XiC_analytic 0 (Set.mem_univ 0)).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds
  have hquot := hnum.div hden XiC_zero_ne
  refine hquot.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hden.eventually_ne XiC_zero_ne]
      with z hz hXiz
  have hz0 : z ≠ 0 := by simpa using hz
  change (deriv XiC z / z) / XiC z =
    z * suzukiShiftedXiMultiplier 0 z
  rw [suzukiShiftedXiMultiplier_eq]
  simp only [suzukiShiftedXiDenominator, zero_mul, sub_zero]
  field_simp [hz0, hXiz]

/-- Two simple central source zeros give the sewn characteristic its exact quadratic coefficient. -/
theorem tendsto_suzukiAffineSewnCharacteristic_div_sq
    {WAlpha WBeta : ℂ → ℂ} {a b : ℂ}
    (hWAlpha : HasDerivAt WAlpha a 0) (hWBeta : HasDerivAt WBeta b 0)
    (hWAlpha0 : WAlpha 0 = 0) (hWBeta0 : WBeta 0 = 0)
    (alpha beta : ℂ) :
    Tendsto
      (fun z : ℂ =>
        suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta z / z ^ 2)
      (𝓝[≠] 0)
      (𝓝 ((beta - alpha) * a * b)) := by
  have hA := tendsto_div_self_of_hasDerivAt_zero hWAlpha hWAlpha0
  have hB := tendsto_div_self_of_hasDerivAt_zero hWBeta hWBeta0
  have hconst : Tendsto (fun _ : ℂ => beta - alpha) (𝓝[≠] 0)
      (𝓝 (beta - alpha)) := tendsto_const_nhds
  have hlim := (hconst.mul hA).mul hB
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have hz0 : z ≠ 0 := by simpa using hz
  simp only [suzukiAffineSewnCharacteristic]
  field_simp [hz0]

/-- The odd part of the sewn right triangle has the exact first coefficient carried by boundary
values, not by derivatives of the triangles. -/
theorem tendsto_suzukiAffineSewnRightOddPart_div
    {WAlpha WBeta rightAlpha rightBeta : ℂ → ℂ} {a b : ℂ}
    (hWAlpha : HasDerivAt WAlpha a 0) (hWBeta : HasDerivAt WBeta b 0)
    (hWAlpha0 : WAlpha 0 = 0) (hWBeta0 : WBeta 0 = 0)
    (hRightAlpha : DifferentiableAt ℂ rightAlpha 0)
    (hRightBeta : DifferentiableAt ℂ rightBeta 0)
    (alpha beta : ℂ) :
    Tendsto
      (fun z : ℂ =>
        suzukiReflectionOddPart
          (suzukiAffineSewnIntervalPart alpha beta 0
            WAlpha WBeta rightAlpha rightBeta) z / z)
      (𝓝[≠] 0)
      (𝓝 (beta * b * rightAlpha 0 - alpha * a * rightBeta 0)) := by
  let J : ℂ → ℂ := suzukiAffineSewnIntervalPart alpha beta 0
    WAlpha WBeta rightAlpha rightBeta
  have hJ : HasDerivAt J
      (beta * b * rightAlpha 0 - alpha * a * rightBeta 0) 0 := by
    have hcalc := ((hWBeta.const_mul beta).mul hRightAlpha.hasDerivAt).sub
      ((hWAlpha.const_mul alpha).mul hRightBeta.hasDerivAt)
    have hfun : J =
        (fun y => beta * WBeta y) * rightAlpha -
          (fun y => alpha * WAlpha y) * rightBeta := by
      funext z
      simp only [J, suzukiAffineSewnIntervalPart, sub_zero, Pi.mul_apply,
        Pi.sub_apply]
    rw [hfun]
    simpa only [hWAlpha0, hWBeta0, mul_zero, zero_mul, add_zero] using hcalc
  have hneg : HasDerivAt (fun z : ℂ => J (-z))
      (-(beta * b * rightAlpha 0 - alpha * a * rightBeta 0)) 0 := by
    have hinner : HasDerivAt (fun z : ℂ => -z) (-1) 0 :=
      hasDerivAt_neg (0 : ℂ)
    have hcomp := hJ.comp_of_eq (0 : ℂ) hinner (by simp)
    simpa only [Function.comp_apply, mul_neg, mul_one] using hcomp
  have hodd : HasDerivAt (suzukiReflectionOddPart J)
      (beta * b * rightAlpha 0 - alpha * a * rightBeta 0) 0 := by
    rw [show suzukiReflectionOddPart J =
        fun z => (J z - J (-z)) / 2 by rfl]
    convert (hJ.sub hneg).div_const 2 using 1
    ring
  have hodd0 : suzukiReflectionOddPart J 0 = 0 := by
    simp [suzukiReflectionOddPart]
  exact tendsto_div_self_of_hasDerivAt_zero hodd hodd0

/-- Boundary-source contribution to the central residue of the admissible sewn Weyl quotient.
Its triangle arguments are interval values in the Xi-real `G_eta W-I` coordinate.  For a physical
Suzuki triangle `T`, this input is `-I*T`; see `SuzukiCarlemanCoordinatePhase`. -/
def suzukiAffineSewnCentralSourceFlux
    (alpha beta a b rightAlphaZero rightBetaZero : ℂ) : ℂ :=
  (beta * b * rightAlphaZero - alpha * a * rightBetaZero) /
    ((beta - alpha) * a * b)

/-- Central right-triangle value of the Neumann comparison kernel `r₀(t)=-|t|/2`, written in
terms of the first three moments of a compact source.  This is the expansion of
`-∫ (aperture-y)² v(y) dy / 4`. -/
def suzukiNeumannRightTriangleCentralMoment
    (aperture massZero massOne massTwo : ℂ) : ℂ :=
  -(aperture ^ 2 * massZero - 2 * aperture * massOne + massTwo) / 4

/-- For an odd source, its zeroth and second moments vanish, so the Neumann central triangle
collapses exactly to `aperture / 2` times its first moment. -/
theorem suzukiNeumannRightTriangleCentralMoment_of_odd
    (aperture massZero massOne massTwo : ℂ)
    (hZero : massZero = 0) (hTwo : massTwo = 0) :
    suzukiNeumannRightTriangleCentralMoment aperture massZero massOne massTwo =
      aperture / 2 * massOne := by
  simp only [suzukiNeumannRightTriangleCentralMoment, hZero, hTwo, mul_zero,
    add_zero]
  ring

/-- After Fourier differentiation, the physical Neumann triangle-to-characteristic ratio is the
universal scalar `aperture / (2i)`, independent of the odd source. -/
theorem suzukiNeumannRightTriangleCentralMoment_div_fourierFirstJet
    (aperture massZero massOne massTwo : ℂ)
    (hZero : massZero = 0) (hTwo : massTwo = 0) (hOne : massOne ≠ 0) :
    suzukiNeumannRightTriangleCentralMoment aperture massZero massOne massTwo /
        (I * massOne) =
      aperture / (2 * I) := by
  rw [suzukiNeumannRightTriangleCentralMoment_of_odd aperture massZero massOne massTwo
    hZero hTwo]
  field_simp [hOne, I_ne_zero]

/-- The four raw central germs enter only through the affine intercept at target shift zero of
the two normalized one-source triangle jets. -/
theorem suzukiAffineSewnCentralSourceFlux_eq_normalized_intercept
    {alpha beta a b rightAlphaZero rightBetaZero : ℂ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    suzukiAffineSewnCentralSourceFlux alpha beta a b rightAlphaZero rightBetaZero =
      (beta * (rightAlphaZero / a) - alpha * (rightBetaZero / b)) /
        (beta - alpha) := by
  simp only [suzukiAffineSewnCentralSourceFlux]
  field_simp [ha, hb]

/-- **Neumann-channel cancellation.** Any common boundary channel whose normalized central jet is
linear in the form shift cancels identically from the affine-sewn central flux.  The Neumann
comparison kernel supplies exactly such a channel by the preceding odd-moment law. -/
theorem suzukiAffineSewnCentralSourceFlux_linear_shift_channel_cancels
    (alpha beta a b gammaAlphaZero gammaBetaZero slope : ℂ) :
    suzukiAffineSewnCentralSourceFlux alpha beta a b
        (gammaAlphaZero + slope * alpha * a)
        (gammaBetaZero + slope * beta * b) =
      suzukiAffineSewnCentralSourceFlux alpha beta a b
        gammaAlphaZero gammaBetaZero := by
  simp only [suzukiAffineSewnCentralSourceFlux]
  congr 1
  ring

/-- Legacy full-symbol specialization in coordinate `eta=-I*lambda`: the normalized direct
Neumann channel has slope `I*aperture/2` in `eta` and disappears from the two-shift central flux.
The exact one-sided coordinate is `eta=-I*lambda/2`, where slope is `I*aperture`; see
`suzukiAffineSewnCentralSourceFlux_oneSided_neumann_channel_cancels`. -/
theorem suzukiAffineSewnCentralSourceFlux_neumann_channel_cancels
    (alpha beta a b gammaAlphaZero gammaBetaZero aperture : ℂ) :
    suzukiAffineSewnCentralSourceFlux alpha beta a b
        (gammaAlphaZero + (I * (aperture / 2)) * alpha * a)
        (gammaBetaZero + (I * (aperture / 2)) * beta * b) =
      suzukiAffineSewnCentralSourceFlux alpha beta a b
        gammaAlphaZero gammaBetaZero :=
  suzukiAffineSewnCentralSourceFlux_linear_shift_channel_cancels
    alpha beta a b gammaAlphaZero gammaBetaZero (I * (aperture / 2))

/-- Passing from real form shifts to legacy full-symbol centered parameters `-I*lambda` leaves
central flux formula unchanged: common factor cancels.  Same statement holds for exact one-sided
factor `-I/2`; see `SuzukiCarlemanCoordinatePhase`. -/
theorem suzukiAffineSewnCentralSourceFlux_centered_eq
    (alpha beta : ℝ) (a b rightAlphaZero rightBetaZero : ℂ) :
    suzukiAffineSewnCentralSourceFlux
        (suzukiCenteredShiftParameter alpha)
        (suzukiCenteredShiftParameter beta)
        a b rightAlphaZero rightBetaZero =
      (((beta : ℂ) * b * rightAlphaZero -
          (alpha : ℂ) * a * rightBetaZero) /
        (((beta : ℂ) - alpha) * a * b)) := by
  simp only [suzukiAffineSewnCentralSourceFlux, suzukiCenteredShiftParameter]
  rw [show -I * (beta : ℂ) - -I * (alpha : ℂ) =
      -I * ((beta : ℂ) - alpha) by ring]
  rw [show -I * (beta : ℂ) * b * rightAlphaZero -
      -I * (alpha : ℂ) * a * rightBetaZero =
      -I * ((beta : ℂ) * b * rightAlphaZero -
        (alpha : ℂ) * a * rightBetaZero) by ring]
  rw [mul_assoc]
  simpa only [mul_assoc] using
    (mul_div_mul_left
      ((beta : ℂ) * b * rightAlphaZero - (alpha : ℂ) * a * rightBetaZero)
      (((beta : ℂ) - alpha) * a * b)
      (neg_ne_zero.mpr I_ne_zero))

/-- **Central residue split.**  The admissible sewn exterior Weyl quotient has residue equal to a
fixed Xi-curvature term plus the source boundary flux. -/
theorem tendsto_z_mul_suzukiAffineSewnExteriorWeylQuotient
    {WAlpha WBeta rightAlpha rightBeta : ℂ → ℂ} {a b : ℂ}
    (hWAlpha : HasDerivAt WAlpha a 0) (hWBeta : HasDerivAt WBeta b 0)
    (hWAlpha0 : WAlpha 0 = 0) (hWBeta0 : WBeta 0 = 0)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hRightAlpha : DifferentiableAt ℂ rightAlpha 0)
    (hRightBeta : DifferentiableAt ℂ rightBeta 0)
    {alpha beta : ℂ} (hab : alpha ≠ beta) :
    Tendsto
      (fun z : ℂ => z *
        suzukiAffineSewnExteriorWeylQuotient alpha beta
          WAlpha WBeta rightAlpha rightBeta z)
      (𝓝[≠] 0)
      (𝓝
        (-(deriv (deriv XiC) 0 / XiC 0) +
          suzukiAffineSewnCentralSourceFlux alpha beta a b
            (rightAlpha 0) (rightBeta 0))) := by
  let P : ℂ → ℂ := suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta
  let J : ℂ → ℂ := suzukiAffineSewnIntervalPart alpha beta 0
    WAlpha WBeta rightAlpha rightBeta
  have hp0 : (beta - alpha) * a * b ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hab.symm) ha) hb
  have hM := tendsto_z_mul_suzukiZeroShiftMultiplier
  have hP : Tendsto (fun z : ℂ => P z / z ^ 2) (𝓝[≠] 0)
      (𝓝 ((beta - alpha) * a * b)) :=
    tendsto_suzukiAffineSewnCharacteristic_div_sq hWAlpha hWBeta
      hWAlpha0 hWBeta0 alpha beta
  have hJ : Tendsto (fun z : ℂ => suzukiReflectionOddPart J z / z)
      (𝓝[≠] 0)
      (𝓝 (beta * b * rightAlpha 0 - alpha * a * rightBeta 0)) :=
    tendsto_suzukiAffineSewnRightOddPart_div hWAlpha hWBeta
      hWAlpha0 hWBeta0 hRightAlpha hRightBeta alpha beta
  have hlim := hM.neg.add (hJ.div hP hp0)
  change Tendsto _ _ (𝓝
    (-(deriv (deriv XiC) 0 / XiC 0) +
      suzukiAffineSewnCentralSourceFlux alpha beta a b
        (rightAlpha 0) (rightBeta 0))) at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hP.eventually_ne hp0] with z hz hPz
  have hz0 : z ≠ 0 := by simpa using hz
  have hPz0 : P z ≠ 0 := by
    intro hzero
    apply hPz
    simp [hzero]
  dsimp [P, J] at hPz0 ⊢
  simp only [suzukiAffineSewnExteriorWeylQuotient,
    suzukiExteriorWeylQuotient, suzukiAffineSewnOddCarlemanPoleCarrier,
    suzukiOddCarlemanPoleCarrier]
  field_simp [hz0, hPz0]
  ring

/-- Upper-half-plane positivity forces the exact central source-flux inequality. -/
theorem suzukiAffineSewnCentralSourceFlux_re_le_XiC_curvature_of_herglotz
    {WAlpha WBeta rightAlpha rightBeta : ℂ → ℂ} {a b : ℂ}
    (hWAlpha : HasDerivAt WAlpha a 0) (hWBeta : HasDerivAt WBeta b 0)
    (hWAlpha0 : WAlpha 0 = 0) (hWBeta0 : WBeta 0 = 0)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hRightAlpha : DifferentiableAt ℂ rightAlpha 0)
    (hRightBeta : DifferentiableAt ℂ rightBeta 0)
    {alpha beta : ℂ} (hab : alpha ≠ beta)
    (hHerglotz : ∀ z : ℂ, 0 < z.im →
      0 ≤ (suzukiAffineSewnExteriorWeylQuotient alpha beta
        WAlpha WBeta rightAlpha rightBeta z).im) :
    (suzukiAffineSewnCentralSourceFlux alpha beta a b
      (rightAlpha 0) (rightBeta 0)).re ≤
      (deriv (deriv XiC) 0 / XiC 0).re := by
  have hres := tendsto_z_mul_suzukiAffineSewnExteriorWeylQuotient
    hWAlpha hWBeta hWAlpha0 hWBeta0 ha hb hRightAlpha hRightBeta hab
  have hnonpos := residue_re_nonpos_of_upperHalfPlane_im_nonneg
    (x := 0) hHerglotz (by simpa using hres)
  simp only [Complex.add_re, Complex.neg_re] at hnonpos
  linarith

/-- The fixed Xi central logarithmic curvature is strictly negative. -/
theorem XiC_secondDeriv_div_center_re_neg :
    (deriv (deriv XiC) 0 / XiC 0).re < 0 := by
  have hXi2 : deriv (deriv XiC) 0 =
      ((deriv (deriv Xi) 0 : ℝ) : ℂ) := by
    simpa using XiC_secondDeriv_ofReal 0
  have hXi0 : XiC 0 = ((Xi 0 : ℝ) : ℂ) := by
    simpa using XiC_ofReal 0
  rw [hXi2, hXi0]
  simpa using div_neg_of_neg_of_pos Xi_secondDeriv_zero_neg Xi_zero_pos

/-- Hence any Herglotz realization needs a strictly negative source boundary flux at the center. -/
theorem suzukiAffineSewnCentralSourceFlux_re_neg_of_herglotz
    {WAlpha WBeta rightAlpha rightBeta : ℂ → ℂ} {a b : ℂ}
    (hWAlpha : HasDerivAt WAlpha a 0) (hWBeta : HasDerivAt WBeta b 0)
    (hWAlpha0 : WAlpha 0 = 0) (hWBeta0 : WBeta 0 = 0)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hRightAlpha : DifferentiableAt ℂ rightAlpha 0)
    (hRightBeta : DifferentiableAt ℂ rightBeta 0)
    {alpha beta : ℂ} (hab : alpha ≠ beta)
    (hHerglotz : ∀ z : ℂ, 0 < z.im →
      0 ≤ (suzukiAffineSewnExteriorWeylQuotient alpha beta
        WAlpha WBeta rightAlpha rightBeta z).im) :
    (suzukiAffineSewnCentralSourceFlux alpha beta a b
      (rightAlpha 0) (rightBeta 0)).re < 0 :=
  lt_of_le_of_lt
    (suzukiAffineSewnCentralSourceFlux_re_le_XiC_curvature_of_herglotz
      hWAlpha hWBeta hWAlpha0 hWBeta0 ha hb hRightAlpha hRightBeta hab hHerglotz)
    XiC_secondDeriv_div_center_re_neg

end

end RHTower
