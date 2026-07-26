import GaloisForLFunctions.RHTower.KRealKernelCokernel
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Deninger's polarized weight-one arithmetic cohomology

This file formalizes the algebraic and Hilbert-space content of properties 2.1--2.7 in
Deninger's proposed cohomology of an arithmetic curve.

The degree-one data consist of:

* a Frobenius-flow generator `theta`;
* the scalar cup-trace pairing `H¹ × H¹ → H² ≃ ℂ(-1)`;
* an odd `KRealStructure`, i.e. an anti-linear Hodge star with square `-1`;
* the derivation identity saying that `theta` acts with weight one on `H²`;
* commutation of `theta` with the Hodge star;
* a positive Hilbert metric realized by cup product and Hodge star.

From these data Lean proves exactly Deninger's formal purity argument:

`⟪theta x, y⟫ + ⟪x, theta y⟫ = ⟪x,y⟫`.

Hence `theta - 1/2` is skew-symmetric and every genuine eigenvalue of `theta` has real part
`1/2`. The file also proves the cup-product selection rule `α + β = 1` and the conjugate
eigenvalue transport induced by the odd Hodge star.

This is an unconditional implication theorem. It does not construct the arithmetic cohomology,
identify its spectrum with zeta zeros, define a regularized determinant, or assume RH.
-/

noncomputable section

open scoped ComplexConjugate
open GaloisForLFunctions.RHTower

namespace RHTower

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/--
The polarized degree-one package in Deninger's arithmetic-cohomology formalism.

`cup_nondegenerate` records Poincaré nondegeneracy. The formula `theta_cup` is the trace of the
cup-product derivation law after identifying `H²` with the weight-one Tate line. Mathlib's inner
product is conjugate-linear in its first variable, so `inner_eq_cup_star` uses
`⟪x,y⟫ = tr(y ∪ star x)`.
-/
structure DeningerWeightOnePolarization where
  theta : Module.End ℂ H
  cupTrace : LinearMap.BilinForm ℂ H
  cup_nondegenerate : cupTrace.Nondegenerate
  star : KRealStructure true H
  theta_cup :
    ∀ x y, cupTrace (theta x) y + cupTrace x (theta y) = cupTrace x y
  star_theta : ∀ x, star.sigma (theta x) = theta (star.sigma x)
  inner_eq_cup_star :
    ∀ x y, @inner ℂ H _ x y = cupTrace y (star.sigma x)

namespace DeningerWeightOnePolarization

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/--
Deninger's cup-product selection rule: eigenvectors can pair only when their weights add to one.
-/
theorem cupTrace_eigenvectors_eq_zero_of_add_ne_one
    (P : DeningerWeightOnePolarization H)
    {α β : ℂ} {x y : H}
    (hx : P.theta x = α • x) (hy : P.theta y = β • y)
    (hab : α + β ≠ 1) :
    P.cupTrace x y = 0 := by
  have h := P.theta_cup x y
  rw [hx, hy] at h
  simp only [map_smul, LinearMap.smul_apply] at h
  by_contra hxy
  apply hab
  apply (mul_left_cancel₀ hxy)
  linear_combination h

/-- The anti-linear Hodge star transports a `theta`-eigenvalue to its complex conjugate. -/
theorem star_eigenvector
    (P : DeningerWeightOnePolarization H)
    {α : ℂ} {x : H} (hx : P.theta x = α • x) :
    P.theta (P.star.sigma x) = (starRingEnd ℂ) α • P.star.sigma x := by
  rw [← P.star_theta x, hx]
  exact map_smulₛₗ P.star.sigma α x

/--
The derivation law and the Hodge realization of the metric give the weight-one adjoint identity.
-/
theorem theta_inner_sum (P : DeningerWeightOnePolarization H) (x y : H) :
    @inner ℂ H _ (P.theta x) y + @inner ℂ H _ x (P.theta y) =
      @inner ℂ H _ x y := by
  rw [P.inner_eq_cup_star, P.inner_eq_cup_star, P.inner_eq_cup_star,
    P.star_theta]
  rw [add_comm]
  exact P.theta_cup y (P.star.sigma x)

/-- The centered Frobenius-flow generator `theta - 1/2`. -/
def shiftedTheta (P : DeningerWeightOnePolarization H) : Module.End ℂ H :=
  P.theta - (1 / 2 : ℂ) • LinearMap.id

/-- Deninger's centered generator is skew-symmetric for the positive Hodge metric. -/
theorem shiftedTheta_skewSymmetric
    (P : DeningerWeightOnePolarization H) (x y : H) :
    @inner ℂ H _ (P.shiftedTheta x) y =
      -@inner ℂ H _ x (P.shiftedTheta y) := by
  have h := P.theta_inner_sum x y
  simp only [shiftedTheta, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_coe, id_eq, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, map_div₀, map_one,
    Complex.conj_ofNat] at *
  linear_combination h

/--
Every eigenvalue of a polarized weight-one Frobenius-flow generator lies on the critical line.
-/
theorem eigenvalue_re_eq_half
    (P : DeningerWeightOnePolarization H) {ρ : ℂ} {v : H}
    (hv0 : v ≠ 0) (hv : P.theta v = ρ • v) :
    ρ.re = 1 / 2 := by
  have h := P.theta_inner_sum v v
  rw [hv, inner_smul_left, inner_smul_right] at h
  have hreal := congrArg Complex.re h
  have hqim := inner_self_im (𝕜 := ℂ) v
  change (@inner ℂ H _ v v).im = 0 at hqim
  rw [Complex.add_re, Complex.mul_re, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, hqim] at hreal
  ring_nf at hreal
  have hpos : 0 < (@inner ℂ H _ v v).re := by
    have hnorm := InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) v
    change ‖v‖ ^ 2 = (@inner ℂ H _ v v).re at hnorm
    exact lt_of_lt_of_eq (sq_pos_of_pos (norm_pos_iff.mpr hv0))
      hnorm
  nlinarith

/--
The positive weight-one polarization excludes a nontrivial Jordan chain of length two.

This is the finite-vector form of Deninger's semisimplicity consequence: if `u` is a
`rho`-eigenvector and `v` is a generalized eigenvector with
`(theta - rho) v = u`, then `u` vanishes.
-/
theorem jordan_chain_head_eq_zero
    (P : DeningerWeightOnePolarization H) {ρ : ℂ} {u v : H}
    (hu : P.theta u = ρ • u)
    (hv : P.theta v = ρ • v + u) :
    u = 0 := by
  by_contra hu0
  have hre : ρ.re = 1 / 2 := P.eigenvalue_re_eq_half hu0 hu
  have hconj : (starRingEnd ℂ) ρ + ρ = 1 := by
    apply Complex.ext
    · simp [hre]
      norm_num
    · simp
  have hconj' : (starRingEnd ℂ) ρ = 1 - ρ := by
    linear_combination hconj
  have h := P.theta_inner_sum v u
  rw [hv, hu, inner_add_left, inner_smul_left, inner_smul_right, hconj'] at h
  have huu : @inner ℂ H _ u u = 0 := by
    linear_combination h
  exact hu0 (inner_self_eq_zero.mp huu)

end DeningerWeightOnePolarization
end RHTower
