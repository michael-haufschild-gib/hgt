import GaloisForLFunctions.RHTower.SmoothAFEZetaResidueDecomposition
import GaloisForLFunctions.RHTower.HardyCarrier

/-!
# Confluent pole decomposition for Ingham's zeta-square Mellin integrand

Squaring zeta turns the shifted pole `z = 1-s` in the smooth Mellin contour from simple to double.
This file supplies the required Hermite, rather than Lagrange, principal-part decomposition.  For
an analytic numerator `N` and nonzero `a`, it decomposes

`N(z) / (z (z-a)^2)`

into a simple pole at zero, a double and a simple pole at `a`, and an analytic threefold divided-
difference remainder.  It then identifies the simple residue at zero of the literal
`Gamma(z) zeta(s+z)^2` integrand as `zeta(s)^2` on the critical line.
-/

noncomputable section

open Complex Set

namespace RHTower.Sieve

/-- Coefficient of the simple pole at zero in a `z (z-a)^2` quotient. -/
def confluentSimpleCoeff (N : ℂ → ℂ) (a : ℂ) : ℂ := N 0 / a ^ 2

/-- Coefficient of the double pole at `a` in a `z (z-a)^2` quotient. -/
def confluentDoubleCoeff (N : ℂ → ℂ) (a : ℂ) : ℂ := N a / a

/-- Residue of the double-pole packet at `a`. -/
def confluentResidueCoeff (N : ℂ → ℂ) (a : ℂ) : ℂ :=
  (deriv N a - confluentDoubleCoeff N a) / a

/-- Hermite principal-part numerator matching value at zero and value/derivative at `a`. -/
def confluentHermitePoly (N : ℂ → ℂ) (a z : ℂ) : ℂ :=
  confluentSimpleCoeff N a * (z - a) ^ 2 + confluentDoubleCoeff N a * z +
    confluentResidueCoeff N a * z * (z - a)

/-- Numerator after subtracting the confluent principal part. -/
def confluentVanishingNumerator (N : ℂ → ℂ) (a z : ℂ) : ℂ :=
  N z - confluentHermitePoly N a z

/-- Analytic quotient after removing one zero at zero and a double zero at `a`. -/
def confluentPoleRemainder (N : ℂ → ℂ) (a : ℂ) : ℂ → ℂ :=
  dslope (dslope (dslope (confluentVanishingNumerator N a) a) a) 0

theorem confluentVanishingNumerator_zero (N : ℂ → ℂ) {a : ℂ} (ha : a ≠ 0) :
    confluentVanishingNumerator N a 0 = 0 := by
  unfold confluentVanishingNumerator confluentHermitePoly confluentSimpleCoeff
  field_simp [ha]
  ring

theorem confluentVanishingNumerator_anchor (N : ℂ → ℂ) {a : ℂ} (ha : a ≠ 0) :
    confluentVanishingNumerator N a a = 0 := by
  unfold confluentVanishingNumerator confluentHermitePoly confluentDoubleCoeff
  field_simp [ha]
  ring

theorem deriv_confluentVanishingNumerator_anchor
    (N : ℂ → ℂ) {a : ℂ} (ha : a ≠ 0) (hN : DifferentiableAt ℂ N a) :
    deriv (confluentVanishingNumerator N a) a = 0 := by
  have hpoly : HasDerivAt (confluentHermitePoly N a)
      (2 * confluentSimpleCoeff N a * (a - a) + confluentDoubleCoeff N a +
        confluentResidueCoeff N a * ((a - a) + a)) a := by
    have hsum :=
      (((hasDerivAt_id a).sub_const a).pow 2 |>.const_mul (confluentSimpleCoeff N a)).add
        ((hasDerivAt_id a).const_mul (confluentDoubleCoeff N a)) |>.add
          (((hasDerivAt_id a).mul ((hasDerivAt_id a).sub_const a)).const_mul
            (confluentResidueCoeff N a))
    have hfun : confluentHermitePoly N a =
        (fun z => confluentSimpleCoeff N a * (z - a) ^ 2) +
          (fun z => confluentDoubleCoeff N a * z) +
          (fun z => confluentResidueCoeff N a * z * (z - a)) := by
      funext z
      rfl
    rw [hfun]
    convert hsum using 1
    case e'_4 => rfl
    case e'_5 => rfl
    case e'_8 =>
      funext z
      simp only [Pi.add_apply, Pi.mul_apply, Pi.pow_apply, id_eq]
      ring
    case e'_9 =>
      simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
      ring
  rw [show deriv (confluentVanishingNumerator N a) a =
      deriv N a - deriv (confluentHermitePoly N a) a by
    unfold confluentVanishingNumerator
    exact deriv_sub hN hpoly.differentiableAt]
  rw [hpoly.deriv]
  unfold confluentResidueCoeff confluentDoubleCoeff
  field_simp [ha]
  ring

/-- Off the two poles, the divided-difference remainder is the literal quotient by all three
vanishing factors. -/
theorem confluentPoleRemainder_eq_quotient
    (N : ℂ → ℂ) {a z : ℂ} (ha : a ≠ 0) (hz0 : z ≠ 0) (hza : z ≠ a)
    (hN : DifferentiableAt ℂ N a) :
    confluentPoleRemainder N a z =
      confluentVanishingNumerator N a z / (z * (z - a) ^ 2) := by
  have hK0 := confluentVanishingNumerator_zero N ha
  have hKa := confluentVanishingNumerator_anchor N ha
  have hK'a := deriv_confluentVanishingNumerator_anchor N ha hN
  have hD0a : dslope (confluentVanishingNumerator N a) a a = 0 := by
    rw [dslope_same, hK'a]
  have hD00 : dslope (confluentVanishingNumerator N a) a 0 = 0 := by
    rw [dslope_of_ne _ (Ne.symm ha), slope_def_field, hK0, hKa, sub_zero, zero_div]
  have hD1zero : dslope (dslope (confluentVanishingNumerator N a) a) a 0 = 0 := by
    rw [dslope_of_ne _ (Ne.symm ha), slope_def_field, hD00, hD0a, sub_zero, zero_div]
  unfold confluentPoleRemainder
  rw [dslope_of_ne _ hz0, slope_def_field, hD1zero, sub_zero,
    dslope_of_ne _ hza, slope_def_field, hD0a, sub_zero,
    dslope_of_ne _ hza, slope_def_field, hKa, sub_zero]
  field_simp [hz0, sub_ne_zero.mpr hza]
  ring

/-- Exact confluent two-pole decomposition.  The squared inverse is a zero-residue double-pole
term; `confluentResidueCoeff` is the only shifted-pole contribution to a closed contour. -/
theorem confluent_twoPole_decomposition
    (N : ℂ → ℂ) {a z : ℂ} (ha : a ≠ 0) (hz0 : z ≠ 0) (hza : z ≠ a)
    (hN : DifferentiableAt ℂ N a) :
    N z / (z * (z - a) ^ 2) =
      confluentSimpleCoeff N a * z⁻¹ +
        confluentDoubleCoeff N a * (z - a)⁻¹ ^ 2 +
        confluentResidueCoeff N a * (z - a)⁻¹ +
        confluentPoleRemainder N a z := by
  rw [confluentPoleRemainder_eq_quotient N ha hz0 hza hN]
  unfold confluentVanishingNumerator confluentHermitePoly
  field_simp [hz0, sub_ne_zero.mpr hza]
  ring

theorem differentiable_confluentPoleRemainder
    (N : ℂ → ℂ) (a : ℂ) (hN : Differentiable ℂ N) :
    Differentiable ℂ (confluentPoleRemainder N a) := by
  have hP : Differentiable ℂ (confluentHermitePoly N a) := by
    unfold confluentHermitePoly
    fun_prop
  have hK : Differentiable ℂ (confluentVanishingNumerator N a) := by
    unfold confluentVanishingNumerator
    exact hN.sub hP
  have hD0 : Differentiable ℂ (dslope (confluentVanishingNumerator N a) a) := by
    apply differentiableOn_univ.1
    rw [differentiableOn_dslope Filter.univ_mem]
    exact hK.differentiableOn
  have hD1 : Differentiable ℂ
      (dslope (dslope (confluentVanishingNumerator N a) a) a) := by
    apply differentiableOn_univ.1
    rw [differentiableOn_dslope Filter.univ_mem]
    exact hD0.differentiableOn
  apply differentiableOn_univ.1
  rw [confluentPoleRemainder, differentiableOn_dslope Filter.univ_mem]
  exact hD1.differentiableOn

/-- Local version used when the pole-filled numerator is analytic only on a contour strip. -/
theorem differentiableOn_confluentPoleRemainder
    {N : ℂ → ℂ} {a : ℂ} {U : Set ℂ}
    (hN : DifferentiableOn ℂ N U) (ha : U ∈ nhds a) (h0 : U ∈ nhds 0) :
    DifferentiableOn ℂ (confluentPoleRemainder N a) U := by
  have hP : Differentiable ℂ (confluentHermitePoly N a) := by
    unfold confluentHermitePoly
    fun_prop
  have hK : DifferentiableOn ℂ (confluentVanishingNumerator N a) U := by
    unfold confluentVanishingNumerator
    exact hN.sub hP.differentiableOn
  rw [confluentPoleRemainder, differentiableOn_dslope h0,
    differentiableOn_dslope ha, differentiableOn_dslope ha]
  exact hK

/-! ## Zeta-square specialization -/

/-- Pole-filled numerator of the exponential zeta-square Mellin integrand. -/
def inghamZetaSquarePoleNumerator (s : ℂ) (x : ℝ) (z : ℂ) : ℂ :=
  (x : ℂ) ^ (-z) * Complex.Gamma (z + 1) * regularizedRiemannZeta (s + z) ^ 2

/-- Literal exponential zeta-square Mellin integrand before pole filling. -/
def inghamZetaSquareMellinIntegrand (s : ℂ) (x : ℝ) (z : ℂ) : ℂ :=
  (x : ℂ) ^ (-z) * Complex.Gamma z * riemannZeta (s + z) ^ 2

/-- Open half-plane containing the full Ramachandra shift from `Re z=2` to any `c₁∈(-1,-1/2)`. -/
def inghamZetaSquareShiftDomain : Set ℂ := {z : ℂ | -1 < z.re}

theorem isOpen_inghamZetaSquareShiftDomain : IsOpen inghamZetaSquareShiftDomain :=
  isOpen_lt continuous_const Complex.continuous_re

theorem inghamZetaSquareMellinIntegrand_eq_poleQuotient
    {s z : ℂ} {x : ℝ} (hz0 : z ≠ 0) (hza : z ≠ 1 - s) :
    inghamZetaSquareMellinIntegrand s x z =
      inghamZetaSquarePoleNumerator s x z / (z * (z - (1 - s)) ^ 2) := by
  have hshift : s + z ≠ 1 := by
    intro h
    apply hza
    linear_combination h
  rw [inghamZetaSquareMellinIntegrand, inghamZetaSquarePoleNumerator,
    Complex.Gamma_add_one z hz0, regularizedRiemannZeta_of_ne_one hshift]
  have hcoord : s + z - 1 = z - (1 - s) := by ring
  rw [hcoord]
  field_simp [hz0, sub_ne_zero.mpr hza]

theorem differentiableAt_inghamZetaSquarePoleNumerator_shiftedPole
    (tau : ℝ) {x : ℝ} (hx : 0 < x) :
    DifferentiableAt ℂ (inghamZetaSquarePoleNumerator (linePt tau) x)
      (1 - linePt tau) := by
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hGamma : DifferentiableAt ℂ Complex.Gamma ((1 - linePt tau) + 1) := by
    apply Complex.differentiableAt_Gamma
    intro m hm
    have hre := congrArg Complex.re hm
    simp only [Complex.add_re, Complex.sub_re, Complex.one_re, linePt_re,
      Complex.neg_re, Complex.natCast_re] at hre
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    norm_num at hre
    linarith
  unfold inghamZetaSquarePoleNumerator
  have hpow : DifferentiableAt ℂ (fun z : ℂ => (x : ℂ) ^ (-z))
      (1 - linePt tau) :=
    ((hasDerivAt_id (1 - linePt tau)).neg.const_cpow
      (c := (x : ℂ)) (Or.inl hxC)).differentiableAt
  have hGammaComp : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z + 1))
      (1 - linePt tau) :=
    hGamma.comp (1 - linePt tau) (by fun_prop)
  have hreg : DifferentiableAt ℂ
      (fun z : ℂ => regularizedRiemannZeta (linePt tau + z))
      (1 - linePt tau) :=
    differentiable_regularizedRiemannZeta.differentiableAt.comp
      (1 - linePt tau) (by fun_prop)
  exact (hpow.mul hGammaComp).mul (hreg.pow 2)

/-- Pole-filled zeta-square numerator is holomorphic throughout the complete contour-shift
half-plane. -/
theorem differentiableOn_inghamZetaSquarePoleNumerator_shiftDomain
    (tau : ℝ) {x : ℝ} (hx : 0 < x) :
    DifferentiableOn ℂ (inghamZetaSquarePoleNumerator (linePt tau) x)
      inghamZetaSquareShiftDomain := by
  intro z hz
  have hxC : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hGamma : DifferentiableAt ℂ Complex.Gamma (z + 1) := by
    apply Complex.differentiableAt_Gamma
    intro m hm
    have hre := congrArg Complex.re hm
    have hzre : -1 < z.re := hz
    simp only [Complex.add_re, Complex.one_re, Complex.neg_re,
      Complex.natCast_re] at hre
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  unfold inghamZetaSquarePoleNumerator
  have hpow : DifferentiableAt ℂ (fun w : ℂ => (x : ℂ) ^ (-w)) z :=
    ((hasDerivAt_id z).neg.const_cpow (c := (x : ℂ)) (Or.inl hxC)).differentiableAt
  have hGammaComp : DifferentiableAt ℂ (fun w : ℂ => Complex.Gamma (w + 1)) z :=
    hGamma.comp z (by fun_prop)
  have hreg : DifferentiableAt ℂ
      (fun w : ℂ => regularizedRiemannZeta (linePt tau + w)) z :=
    differentiable_regularizedRiemannZeta.differentiableAt.comp z (by fun_prop)
  exact ((hpow.mul hGammaComp).mul (hreg.pow 2)).differentiableWithinAt

/-- The Hermite remainder is holomorphic on the entire contour-shift half-plane, not merely at the
two punctures. -/
theorem differentiableOn_inghamZetaSquareConfluentRemainder_shiftDomain
    (tau : ℝ) {x : ℝ} (hx : 0 < x) :
    DifferentiableOn ℂ
      (confluentPoleRemainder (inghamZetaSquarePoleNumerator (linePt tau) x)
        (1 - linePt tau)) inghamZetaSquareShiftDomain := by
  apply differentiableOn_confluentPoleRemainder
  · exact differentiableOn_inghamZetaSquarePoleNumerator_shiftDomain tau hx
  · apply isOpen_inghamZetaSquareShiftDomain.mem_nhds
    change -1 < (1 - linePt tau).re
    rw [Complex.sub_re, Complex.one_re, linePt_re]
    norm_num
  · apply isOpen_inghamZetaSquareShiftDomain.mem_nhds
    norm_num [inghamZetaSquareShiftDomain]

/-- The residue at the Gamma pole `z=0` is exactly the desired `zeta(s)^2` term. -/
theorem confluentSimpleCoeff_inghamZetaSquarePoleNumerator
    (tau : ℝ) (x : ℝ) :
    confluentSimpleCoeff (inghamZetaSquarePoleNumerator (linePt tau) x)
        (1 - linePt tau) = riemannZeta (linePt tau) ^ 2 := by
  have hs : linePt tau ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [linePt_re, Complex.one_re] at hre
    norm_num at hre
  rw [confluentSimpleCoeff, inghamZetaSquarePoleNumerator, add_zero,
    regularizedRiemannZeta_of_ne_one hs]
  simp only [neg_zero, cpow_zero, zero_add, Complex.Gamma_one, one_mul]
  have hsq : (linePt tau - 1) ^ 2 = (1 - linePt tau) ^ 2 := by ring
  rw [mul_pow, hsq]
  field_simp [sub_ne_zero.mpr (Ne.symm hs)]

/-- Exact principal-part decomposition of the critical zeta-square Mellin integrand. -/
theorem inghamZetaSquareMellinIntegrand_confluent_decomposition
    (tau : ℝ) {x : ℝ} (hx : 0 < x) {z : ℂ}
    (hz0 : z ≠ 0) (hza : z ≠ 1 - linePt tau) :
    inghamZetaSquareMellinIntegrand (linePt tau) x z =
      riemannZeta (linePt tau) ^ 2 * z⁻¹ +
        confluentDoubleCoeff (inghamZetaSquarePoleNumerator (linePt tau) x)
            (1 - linePt tau) * (z - (1 - linePt tau))⁻¹ ^ 2 +
        confluentResidueCoeff (inghamZetaSquarePoleNumerator (linePt tau) x)
            (1 - linePt tau) * (z - (1 - linePt tau))⁻¹ +
        confluentPoleRemainder (inghamZetaSquarePoleNumerator (linePt tau) x)
            (1 - linePt tau) z := by
  have ha : (1 : ℂ) - linePt tau ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [Complex.sub_re, Complex.one_re, linePt_re] at hre
    norm_num at hre
  rw [inghamZetaSquareMellinIntegrand_eq_poleQuotient hz0 hza,
    confluent_twoPole_decomposition _ ha hz0 hza
      (differentiableAt_inghamZetaSquarePoleNumerator_shiftedPole tau hx),
    confluentSimpleCoeff_inghamZetaSquarePoleNumerator]

end RHTower.Sieve
