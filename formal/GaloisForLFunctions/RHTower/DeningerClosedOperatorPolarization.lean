import GaloisForLFunctions.RHTower.DeningerWeightOnePolarization
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-!
# Closed-operator form of Deninger's weight-one polarization

The arithmetic Frobenius generator on infinite-dimensional `H¹` is expected to be unbounded.
`DeningerWeightOnePolarization` records the bounded/algebraic calculation. This file places the
same calculation in the correct analytic category: a closed densely defined `LinearPMap`.

The cup derivation, Hodge-star commutation, skew-symmetry of `Theta - 1/2`, critical-line
eigenvalue theorem, and exclusion of length-two Jordan chains are all stated on the operator
domain. Closedness and density are fields of the structure, ready for a source realization.

No spectrum identification or positivity construction is assumed beyond the displayed polarized
cohomology data.
-/

noncomputable section

open scoped ComplexConjugate
open GaloisForLFunctions.RHTower

namespace RHTower

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Deninger's polarized degree-one package for a closed, densely defined generator. -/
structure DeningerClosedWeightOnePolarization where
  theta : H →ₗ.[ℂ] H
  theta_closed : theta.IsClosed
  theta_dense : Dense (theta.domain : Set H)
  cupTrace : LinearMap.BilinForm ℂ H
  cup_nondegenerate : cupTrace.Nondegenerate
  star : KRealStructure true H
  star_mem_domain : ∀ x : theta.domain, star.sigma (x : H) ∈ theta.domain
  theta_cup :
    ∀ x y : theta.domain,
      cupTrace (theta x) (y : H) + cupTrace (x : H) (theta y) =
        cupTrace (x : H) (y : H)
  star_theta :
    ∀ x : theta.domain,
      star.sigma (theta x) =
        theta ⟨star.sigma (x : H), star_mem_domain x⟩
  inner_eq_cup_star :
    ∀ x y : H, @inner ℂ H _ x y = cupTrace y (star.sigma x)

namespace DeningerClosedWeightOnePolarization

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The Hodge star transports the closed generator domain into itself. -/
def starDomain
    (P : DeningerClosedWeightOnePolarization H) :
    P.theta.domain → P.theta.domain :=
  fun x => ⟨P.star.sigma (x : H), P.star_mem_domain x⟩

/-- The closed-operator weight-one adjoint identity on the common domain. -/
theorem theta_inner_sum
    (P : DeningerClosedWeightOnePolarization H)
    (x y : P.theta.domain) :
    @inner ℂ H _ (P.theta x) (y : H) +
        @inner ℂ H _ (x : H) (P.theta y) =
      @inner ℂ H _ (x : H) (y : H) := by
  rw [P.inner_eq_cup_star, P.inner_eq_cup_star, P.inner_eq_cup_star,
    P.star_theta]
  rw [add_comm]
  exact P.theta_cup y (P.starDomain x)

/-- Value of the centered unbounded generator on its domain. -/
def shiftedThetaValue
    (P : DeningerClosedWeightOnePolarization H)
    (x : P.theta.domain) : H :=
  P.theta x - (1 / 2 : ℂ) • (x : H)

/-- `Theta - 1/2` is skew-symmetric on the closed generator domain. -/
theorem shiftedTheta_skewSymmetric
    (P : DeningerClosedWeightOnePolarization H)
    (x y : P.theta.domain) :
    @inner ℂ H _ (P.shiftedThetaValue x) (y : H) =
      -@inner ℂ H _ (x : H) (P.shiftedThetaValue y) := by
  have h := P.theta_inner_sum x y
  simp only [shiftedThetaValue, inner_sub_left, inner_sub_right,
    inner_smul_left, inner_smul_right, map_div₀, map_one,
    Complex.conj_ofNat] at *
  linear_combination h

/-- Every genuine eigenvalue of the closed polarized generator lies on the critical line. -/
theorem eigenvalue_re_eq_half
    (P : DeningerClosedWeightOnePolarization H)
    {rho : ℂ} {v : P.theta.domain}
    (hv0 : (v : H) ≠ 0)
    (hv : P.theta v = rho • (v : H)) :
    rho.re = 1 / 2 := by
  have h := P.theta_inner_sum v v
  rw [hv, inner_smul_left, inner_smul_right] at h
  have hreal := congrArg Complex.re h
  have hqim := inner_self_im (𝕜 := ℂ) (v : H)
  change (@inner ℂ H _ (v : H) (v : H)).im = 0 at hqim
  rw [Complex.add_re, Complex.mul_re, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, hqim] at hreal
  ring_nf at hreal
  have hpos : 0 < (@inner ℂ H _ (v : H) (v : H)).re := by
    have hnorm := InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (v : H)
    change ‖(v : H)‖ ^ 2 = (@inner ℂ H _ (v : H) (v : H)).re at hnorm
    exact lt_of_lt_of_eq (sq_pos_of_pos (norm_pos_iff.mpr hv0)) hnorm
  nlinarith

/-- A closed polarized generator has no nontrivial length-two Jordan chain. -/
theorem jordan_chain_head_eq_zero
    (P : DeningerClosedWeightOnePolarization H)
    {rho : ℂ} {u v : P.theta.domain}
    (hu : P.theta u = rho • (u : H))
    (hv : P.theta v = rho • (v : H) + (u : H)) :
    (u : H) = 0 := by
  by_contra hu0
  have hre : rho.re = 1 / 2 := P.eigenvalue_re_eq_half hu0 hu
  have hconj : (starRingEnd ℂ) rho + rho = 1 := by
    apply Complex.ext
    · simp [hre]
      norm_num
    · simp
  have hconj' : (starRingEnd ℂ) rho = 1 - rho := by
    linear_combination hconj
  have h := P.theta_inner_sum v u
  rw [hv, hu, inner_add_left, inner_smul_left, inner_smul_right, hconj'] at h
  have huu : @inner ℂ H _ (u : H) (u : H) = 0 := by
    linear_combination h
  exact hu0 (inner_self_eq_zero.mp huu)

end DeningerClosedWeightOnePolarization
end RHTower
