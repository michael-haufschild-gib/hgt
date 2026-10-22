import GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticCochainComplex
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Poincare duality and the exact Hodge obligation

For the noncompact source complex, ordinary middle cohomology pairs canonically with compactly
supported middle cohomology.  Algebraically the latter is the dual of
`Entire(ℂ)/(XiC)`.  Evaluation gives a perfect pairing without choosing or enumerating zeros.

The dual Frobenius is forced by the weight-one cup derivation law:

`Theta_c ell = ell - ell ∘ Theta`.

Thus `B(Theta x,ell) + B(x,Theta_c ell) = B(x,ell)` identically.  The remaining Hodge problem is
now a single concrete object: a conjugate-linear, bijective map from ordinary to compactly
supported `H¹`, intertwining the two Frobenius actions and positive on the diagonal.  If such a
map is constructed, the exact source-spectrum theorem forces RH (in fact the nonreduced quotient
also forces semisimplicity).
-/

open Complex

namespace RHTower

noncomputable section

/-- Algebraic compact-support middle cohomology. -/
abbrev DeningerArithmeticH1Compact :=
  Module.Dual ℂ DeningerArithmeticH1

/-- Canonical Poincare pairing between ordinary and compact-support middle cohomology. -/
def deningerArithmeticPoincarePairing
    (x : DeningerArithmeticH1)
    (ell : DeningerArithmeticH1Compact) : ℂ :=
  ell x

/-- Poincare pairing is linear in ordinary cohomology. -/
theorem deningerArithmeticPoincarePairing_add_left
    (x y : DeningerArithmeticH1)
    (ell : DeningerArithmeticH1Compact) :
    deningerArithmeticPoincarePairing (x + y) ell =
      deningerArithmeticPoincarePairing x ell +
        deningerArithmeticPoincarePairing y ell := by
  exact ell.map_add x y

/-- Poincare pairing is linear in compact-support cohomology. -/
theorem deningerArithmeticPoincarePairing_add_right
    (x : DeningerArithmeticH1)
    (ell eta : DeningerArithmeticH1Compact) :
    deningerArithmeticPoincarePairing x (ell + eta) =
      deningerArithmeticPoincarePairing x ell +
        deningerArithmeticPoincarePairing x eta :=
  rfl

/-- The canonical pairing separates ordinary middle cohomology. -/
theorem deningerArithmeticPoincarePairing_separatingLeft
    {x : DeningerArithmeticH1}
    (hx : ∀ ell : DeningerArithmeticH1Compact,
      deningerArithmeticPoincarePairing x ell = 0) :
    x = 0 := by
  classical
  by_contra hx0
  let b := Module.Basis.ofVectorSpace ℂ DeningerArithmeticH1
  have hrepr : b.repr x ≠ 0 :=
    b.repr.map_eq_zero_iff.not.mpr hx0
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hrepr
  have hcoord : b.coord i x ≠ 0 := by
    simpa only [b.coord_apply] using! hi
  exact hcoord (hx (b.coord i))

/-- The canonical pairing separates compact-support middle cohomology. -/
theorem deningerArithmeticPoincarePairing_separatingRight
    {ell : DeningerArithmeticH1Compact}
    (hell : ∀ x : DeningerArithmeticH1,
      deningerArithmeticPoincarePairing x ell = 0) :
    ell = 0 := by
  apply LinearMap.ext
  intro x
  exact hell x

/--
Compact-support Frobenius forced by the requirement that the Poincare cup-trace have weight one.
-/
def deningerArithmeticThetaCompact :
    Module.End ℂ DeningerArithmeticH1Compact :=
  LinearMap.id - deningerEntireTheta.dualMap

@[simp]
theorem deningerArithmeticThetaCompact_apply
    (ell : DeningerArithmeticH1Compact)
    (x : DeningerArithmeticH1) :
    deningerArithmeticThetaCompact ell x =
      ell x - ell (deningerEntireTheta x) := by
  rfl

/-- Exact weight-one cup derivation law for ordinary/compact-support Poincare duality. -/
theorem deningerArithmeticTheta_poincare
    (x : DeningerArithmeticH1)
    (ell : DeningerArithmeticH1Compact) :
    deningerArithmeticPoincarePairing (deningerEntireTheta x) ell +
        deningerArithmeticPoincarePairing x
          (deningerArithmeticThetaCompact ell) =
      deningerArithmeticPoincarePairing x ell := by
  change
    ell (deningerEntireTheta x) +
        (ell x - ell (deningerEntireTheta x)) =
      ell x
  ring

/--
Exact source Hodge-star obligation.

`star x` is a compact-support class, so `star x y` is the Hodge metric.  Conjugate-linearity makes
that metric sesquilinear; positivity makes it definite.  Frobenius intertwining is precisely the
compatibility which turns the weight-one cup law into skew-symmetry around `1/2`.
-/
structure DeningerArithmeticHodgeStar where
  star :
    DeningerArithmeticH1 →ₗ⋆[ℂ] DeningerArithmeticH1Compact
  bijective : Function.Bijective star
  theta_star :
    ∀ x,
      deningerArithmeticThetaCompact (star x) =
        star (deningerEntireTheta x)
  positive :
    ∀ {x : DeningerArithmeticH1}, x ≠ 0 →
      0 < (star x x).re

namespace DeningerArithmeticHodgeStar

/-- Hodge compatibility forces every genuine Frobenius eigenvalue to have real part `1/2`. -/
theorem eigenvalue_re_eq_half
    (Hodge : DeningerArithmeticHodgeStar)
    {rho : ℂ} {x : DeningerArithmeticH1}
    (hx0 : x ≠ 0)
    (hx : deningerEntireTheta x = rho • x) :
    rho.re = 1 / 2 := by
  have hcup :=
    deningerArithmeticTheta_poincare x (Hodge.star x)
  rw [hx, Hodge.theta_star, hx] at hcup
  have hstar :
      Hodge.star (rho • x) =
        (starRingEnd ℂ) rho • Hodge.star x :=
    map_smulₛₗ Hodge.star rho x
  rw [hstar] at hcup
  change
    Hodge.star x (rho • x) +
        ((starRingEnd ℂ) rho • Hodge.star x) x =
      Hodge.star x x at hcup
  simp only [map_smul, LinearMap.smul_apply] at hcup
  have hmetric0 : Hodge.star x x ≠ 0 := by
    intro hzero
    have hpos := Hodge.positive hx0
    rw [hzero, zero_re] at hpos
    linarith
  have hweight :
      rho + (starRingEnd ℂ) rho = 1 := by
    apply mul_right_cancel₀ hmetric0
    linear_combination hcup
  have hre := congrArg Complex.re hweight
  simp only [add_re, conj_re, one_re] at hre
  linarith

/--
A source Hodge star on the constructed arithmetic cohomology proves the Riemann hypothesis.
The proof uses the source-defined exact point spectrum, not a divisor-defined Hilbert space.
-/
theorem riemannHypothesis
    (Hodge : DeningerArithmeticHodgeStar) :
    RiemannHypothesis := by
  have hreal :
      ∀ q : XiZeroCopy, ∃ t : ℝ, xiSpectralPoint q = (t : ℂ) := by
    intro q
    obtain ⟨x, hx0, hx⟩ :=
      exists_deningerEntireTheta_eigenvector q.1
    have hre :=
      Hodge.eigenvalue_re_eq_half hx0 hx
    have him :
        (xiSpectralPointSupport q.1).im = 0 := by
      norm_num [Complex.mul_re] at hre
      linarith
    refine ⟨(xiSpectralPoint q).re, ?_⟩
    apply Complex.ext
    · simp
    · rw [xiSpectralPoint_eq_support]
      simpa using him
  rw [rh_iff_xi_ne_zero_right]
  intro z hz hzero
  let rho : XiDivisorSupport :=
    ⟨z, mem_xi_divisor_support_of_eq_zero hzero⟩
  have hpos := xi_divisor_pos_on_support rho
  have hn :
      0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) (rho : ℂ)) := by
    omega
  let q : XiZeroCopy := ⟨rho, ⟨0, hn⟩⟩
  obtain ⟨t, ht⟩ := hreal q
  have him := congrArg Complex.im ht
  have hre : z.re = 1 / 2 := by
    dsimp only [q, rho, xiSpectralPoint] at him
    simp at him
    linarith
  exact (ne_of_gt (mem_rightHalf.mp hz)) hre

end DeningerArithmeticHodgeStar

end

end RHTower
