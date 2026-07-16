import GaloisForLFunctions.RHTower.XiRelativeResolventFlux
import GaloisForLFunctions.RHTower.ZetaLogDerivResidue

/-!
# Strict-right localization of the completed squarefree fixed current

The positive squarefree partition function is `ζ(s) / ζ(2s)`.  Its logarithmic current is the
von Mangoldt current at `s` minus twice the current at `2s`.  The doubled correction is holomorphic
throughout `Re s > 1/2`, so replacing the prime current in the completed Xi flux changes no strict
right-half singularity.  The same module records the division-free Fisher numerator identity for
the moving squarefree overlap.
-/

open Complex

namespace GaloisForLFunctions

noncomputable section

/-- Positive squarefree partition function on its Euler half-plane, with its meromorphic formula
used globally. -/
def squarefreePartition (s : ℂ) : ℂ := riemannZeta s / riemannZeta (2 * s)

/-- Additive fixed current of the squarefree partition function. -/
def squarefreeFixedCurrent (s : ℂ) : ℂ :=
  RHTower.infinitePrimeFlux s - 2 * RHTower.infinitePrimeFlux (2 * s)

/-- Archimedean completion of the coefficient-two squarefree fixed current. -/
def completedSquarefreeFixedCurrent (s : ℂ) : ℂ :=
  2 * (squarefreeFixedCurrent s - logDeriv RHTower.archFactor s)

theorem squarefreePartition_ne_zero {s : ℂ} (hs : 1 < s.re) :
    squarefreePartition s ≠ 0 := by
  have h2re : 1 < (2 * s).re := by
    norm_num only [mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  exact div_ne_zero (riemannZeta_ne_zero_of_one_lt_re hs)
    (riemannZeta_ne_zero_of_one_lt_re h2re)

/-- On the strict right half-plane, the squarefree partition vanishes exactly where zeta does. -/
theorem squarefreePartition_eq_zero_iff_riemannZeta_eq_zero
    {s : ℂ} (hs : 1 / 2 < s.re) :
    squarefreePartition s = 0 ↔ riemannZeta s = 0 := by
  have h2re : 1 < (2 * s).re := by
    norm_num only [mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have hz2 : riemannZeta (2 * s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re h2re
  simp [squarefreePartition, hz2]

/-- Division by the doubled zeta factor preserves the complete local zeta divisor, including
multiplicity, at every strict-right point away from the Euler pole. -/
theorem squarefreePartition_meromorphicOrderAt_eq_riemannZeta
    {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s ≠ 1) :
    meromorphicOrderAt squarefreePartition s = meromorphicOrderAt riemannZeta s := by
  have h2re : 1 < (2 * s).re := by
    norm_num only [mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have h2one : 2 * s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num only [mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero,
      one_re] at hre
    linarith
  have hnum : AnalyticAt ℂ riemannZeta s := analyticOn_riemannZeta s hs1
  have hden : AnalyticAt ℂ (fun z : ℂ => riemannZeta (2 * z)) s :=
    (analyticOn_riemannZeta (2 * s) h2one).comp
      (show AnalyticAt ℂ (fun z : ℂ => 2 * z) s by fun_prop)
  have hz2 : riemannZeta (2 * s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re h2re
  change meromorphicOrderAt
    (fun z : ℂ => riemannZeta z / riemannZeta (2 * z)) s =
      meromorphicOrderAt riemannZeta s
  rw [fun_meromorphicOrderAt_div hnum.meromorphicAt hden.meromorphicAt,
    hnum.meromorphicOrderAt_eq, hden.meromorphicOrderAt_eq,
    hden.analyticOrderAt_eq_zero.mpr hz2]
  simp

theorem differentiableAt_squarefreePartition {s : ℂ} (hs : 1 < s.re) :
    DifferentiableAt ℂ squarefreePartition s := by
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have h2re : 1 < (2 * s).re := by
    norm_num only [mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have h2one : 2 * s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num only [mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero, one_re] at hre
    linarith
  unfold squarefreePartition
  exact (differentiableAt_riemannZeta hs1).div
    ((differentiableAt_riemannZeta h2one).comp s (by fun_prop))
    (riemannZeta_ne_zero_of_one_lt_re h2re)

/-- Exact squarefree logarithmic-current identity `-dlog(ζ/ζ₂) = A - 2 A₂`. -/
theorem neg_logDeriv_squarefreePartition_eq_squarefreeFixedCurrent
    {s : ℂ} (hs : 1 < s.re) :
    -logDeriv squarefreePartition s = squarefreeFixedCurrent s := by
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have h2re : 1 < (2 * s).re := by
    norm_num only [mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have h2one : 2 * s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num only [mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero, one_re] at hre
    linarith
  have hzs : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hz2 : riemannZeta (2 * s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re h2re
  have hds : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hd2 : DifferentiableAt ℂ (fun z : ℂ => riemannZeta (2 * z)) s :=
    (differentiableAt_riemannZeta h2one).comp s (by fun_prop)
  change -logDeriv (fun z : ℂ => riemannZeta z / riemannZeta (2 * z)) s =
    squarefreeFixedCurrent s
  rw [logDeriv_div (f := riemannZeta) (g := fun z : ℂ => riemannZeta (2 * z))
    s hzs hz2 hds hd2]
  have hcomp : logDeriv (fun z : ℂ => riemannZeta (2 * z)) s =
      2 * logDeriv riemannZeta (2 * s) := by
    have hchain := logDeriv_comp (f := riemannZeta) (g := fun z : ℂ => 2 * z)
      (differentiableAt_riemannZeta h2one) (show DifferentiableAt ℂ (fun z : ℂ => 2 * z) s by
        fun_prop)
    change logDeriv (fun z : ℂ => riemannZeta (2 * z)) s =
      logDeriv riemannZeta (2 * s) * deriv (fun z : ℂ => 2 * z) s at hchain
    have hderiv : deriv (fun z : ℂ => 2 * z) s = 2 := by simp
    rw [hderiv] at hchain
    linear_combination hchain
  rw [hcomp]
  simp only [squarefreeFixedCurrent, RHTower.infinitePrimeFlux]
  ring

/-- The doubled-zeta correction is holomorphic at every strict right-half point. -/
theorem differentiableAt_infinitePrimeFlux_two_mul
    {s : ℂ} (hs : 1 / 2 < s.re) :
    DifferentiableAt ℂ (fun z : ℂ => RHTower.infinitePrimeFlux (2 * z)) s := by
  have h2re : 1 < (2 * s).re := by
    norm_num only [mul_re, Complex.re_ofNat, Complex.im_ofNat, zero_mul, sub_zero]
    linarith
  have houter : DifferentiableAt ℂ RHTower.infinitePrimeFlux (2 * s) := by
    simpa only [RHTower.infinitePrimeFlux, logDeriv_apply, neg_div] using
      RHTower.differentiableAt_neg_logDeriv_riemannZeta_of_one_lt_re h2re
  exact houter.comp s (show DifferentiableAt ℂ (fun z : ℂ => 2 * z) s by fun_prop)

/-- The doubled-zeta correction is holomorphic on the full strict right half-plane. -/
theorem analyticOnNhd_infinitePrimeFlux_two_mul_rightHalf :
    AnalyticOnNhd ℂ (fun z : ℂ => RHTower.infinitePrimeFlux (2 * z))
      {s : ℂ | 1 / 2 < s.re} := by
  apply DifferentiableOn.analyticOnNhd _
    (isOpen_lt continuous_const Complex.continuous_re)
  intro s hs
  exact (differentiableAt_infinitePrimeFlux_two_mul hs).differentiableWithinAt

/-- On the Euler region, the coefficient-two completed Xi current differs from the completed
squarefree current by exactly the strict-right holomorphic correction `4 A(2s)`. -/
theorem completedXi_sub_completedSquarefree_eq_four_mul_infinitePrimeFlux_two
    {s : ℂ} (hs : 1 < s.re) :
    2 * RHTower.seamFluxCochain s - completedSquarefreeFixedCurrent s =
      4 * RHTower.infinitePrimeFlux (2 * s) := by
  have hsplit := RHTower.seamFluxCochain_eq_prime_add_archimedean_of_one_lt_re hs
  rw [hsplit]
  simp only [completedSquarefreeFixedCurrent, squarefreeFixedCurrent]
  ring

/-- Moving squarefree overlap on the source half-plane. -/
def squarefreeBoundaryOverlap (sigma epsilon u : ℂ) : ℂ :=
  squarefreePartition (sigma + u * epsilon) / squarefreePartition sigma

/-- Pointed squarefree Fisher score before division by the overlap. -/
def squarefreeFisherScore (sigma epsilon u : ℂ) : ℂ :=
  2 * (deriv (squarefreeBoundaryOverlap sigma epsilon) u +
    epsilon * squarefreeFixedCurrent sigma * squarefreeBoundaryOverlap sigma epsilon u)

theorem deriv_squarefreeBoundaryOverlap_eq_neg_mul_fixedCurrent
    {sigma epsilon u : ℂ} (hsigma : 1 < sigma.re)
    (hshift : 1 < (sigma + u * epsilon).re) :
    deriv (squarefreeBoundaryOverlap sigma epsilon) u =
      -epsilon * squarefreeBoundaryOverlap sigma epsilon u *
        squarefreeFixedCurrent (sigma + u * epsilon) := by
  let s := sigma + u * epsilon
  have hden : squarefreePartition sigma ≠ 0 := squarefreePartition_ne_zero hsigma
  have houter : HasDerivAt squarefreePartition (deriv squarefreePartition s) s :=
    (differentiableAt_squarefreePartition hshift).hasDerivAt
  have hinner : HasDerivAt (fun v : ℂ => sigma + v * epsilon) epsilon u := by
    convert (hasDerivAt_const (x := u) (c := sigma)).add
      ((hasDerivAt_id u).mul_const epsilon) using 1
    all_goals ring
  have hcomp : HasDerivAt (fun v : ℂ => squarefreePartition (sigma + v * epsilon))
      (deriv squarefreePartition s * epsilon) u := by
    simpa only [s] using houter.comp u hinner
  have hquot : HasDerivAt (squarefreeBoundaryOverlap sigma epsilon)
      ((deriv squarefreePartition s * epsilon) / squarefreePartition sigma) u := by
    simpa [squarefreeBoundaryOverlap] using hcomp.div_const (squarefreePartition sigma)
  rw [hquot.deriv]
  have hlog := neg_logDeriv_squarefreePartition_eq_squarefreeFixedCurrent hshift
  rw [logDeriv_apply] at hlog
  have hsne : squarefreePartition s ≠ 0 := squarefreePartition_ne_zero hshift
  have hratio : deriv squarefreePartition s / squarefreePartition s =
      -squarefreeFixedCurrent s := by
    linear_combination -hlog
  have hderiv : deriv squarefreePartition s =
      -squarefreeFixedCurrent s * squarefreePartition s :=
    (div_eq_iff hsne).mp hratio
  rw [hderiv]
  simp only [s, squarefreeBoundaryOverlap]
  field_simp [hden]

/-- Division-free Fisher numerator identity. -/
theorem epsilon_mul_overlap_mul_fixedCurrent_eq_neg_deriv
    {sigma epsilon u : ℂ} (hsigma : 1 < sigma.re)
    (hshift : 1 < (sigma + u * epsilon).re) :
    epsilon * squarefreeBoundaryOverlap sigma epsilon u *
        squarefreeFixedCurrent (sigma + u * epsilon) =
      -deriv (squarefreeBoundaryOverlap sigma epsilon) u := by
  rw [deriv_squarefreeBoundaryOverlap_eq_neg_mul_fixedCurrent hsigma hshift]
  ring

/-- The pointed Fisher score is the exact difference of the base and shifted squarefree fixed
currents, before any division by the overlap. -/
theorem squarefreeFisherScore_eq_fixedCurrent_difference
    {sigma epsilon u : ℂ} (hsigma : 1 < sigma.re)
    (hshift : 1 < (sigma + u * epsilon).re) :
    squarefreeFisherScore sigma epsilon u =
      2 * epsilon * squarefreeBoundaryOverlap sigma epsilon u *
        (squarefreeFixedCurrent sigma -
          squarefreeFixedCurrent (sigma + u * epsilon)) := by
  rw [squarefreeFisherScore,
    deriv_squarefreeBoundaryOverlap_eq_neg_mul_fixedCurrent hsigma hshift]
  ring

end

end GaloisForLFunctions
