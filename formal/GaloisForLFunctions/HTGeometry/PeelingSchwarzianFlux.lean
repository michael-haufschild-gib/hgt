import GaloisForLFunctions.HTGeometry.SchwarzianProjectiveInvariant
import Mathlib.Tactic

/-!
# Peeling field and Schwarzian conformal flux

This module formalizes Okten--Turan, arXiv:2608.19244v1, equations `(4)`--`(8)` and
`(15)`--`(21)`.  The algebra is carried out in an arbitrary characteristic-zero differential field,
so it applies pointwise to every channel whenever the first derivative of the ray map is nonzero.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

/-- Channel peeling field `kappa = -p''/p'`, equations `(4)`--`(5)` and `(16)`. -/
def channelPeeling {K : Type*} [Field K] [Differential K] (x : K) : K :=
  -x′′ / x′

/-- Equations `(6)`--`(8)`: peeling is invariant under every differential-constant nondegenerate
affine reparametrization of the ingoing null coordinate. -/
theorem channelPeeling_affine
    {K : Type*} [Field K] [CharZero K] [Differential K]
    (x a b : K) (ha : a′ = 0) (hb : b′ = 0) (hax : a ≠ 0) (hx : x′ ≠ 0) :
    channelPeeling (a * x + b) = channelPeeling x := by
  have h1 : (a * x + b)′ = a * x′ := by
    simp only [map_add, Derivation.leibniz, ha, hb, smul_eq_mul, mul_zero, add_zero]
  have h2 : (a * x + b)′′ = a * x′′ := by
    rw [h1]
    simp only [Derivation.leibniz, ha, smul_eq_mul, mul_zero, add_zero]
  rw [channelPeeling, h2, h1, channelPeeling]
  field_simp

/-- Equation `(17)`: exact derivative of the peeling field. -/
theorem deriv_channelPeeling
    {K : Type*} [Field K] [CharZero K] [Differential K]
    (x : K) (hx : x′ ≠ 0) :
    (channelPeeling x)′ = -(x′′′ / x′) + (x′′ / x′) ^ 2 := by
  rw [channelPeeling, (Differential.deriv : Derivation ℤ K K).leibniz_div, map_neg]
  simp only [smul_eq_mul]
  field_simp
  ring

/-- Equation `(18)`: the Schwarzian is minus the peeling derivative minus half its square. -/
theorem schwarzian_eq_neg_deriv_channelPeeling_sub_half_sq
    {K : Type*} [Field K] [CharZero K] [Differential K]
    (x : K) (hx : x′ ≠ 0) :
    schwarzian x = -(channelPeeling x)′ - (1 / 2 : K) * channelPeeling x ^ 2 := by
  rw [deriv_channelPeeling x hx, schwarzian, channelPeeling]
  field_simp
  ring

/-- Conformal channel flux with `C = cCFT/(24*pi)`, equation `(13)`. -/
def channelConformalFlux {K : Type*} [Field K] [Differential K] (C x : K) : K :=
  -C * schwarzian x

/-- Quadratic reference flux, with `C = cCFT/(24*pi)`, equation `(20)`. -/
def channelQuadraticReferenceFlux {K : Type*} [Field K] [Differential K]
    (C x : K) : K :=
  C * (1 / 2 : K) * channelPeeling x ^ 2

/-- Equation `(19)`: exact conformal flux in peeling variables. -/
theorem channelConformalFlux_eq
    {K : Type*} [Field K] [CharZero K] [Differential K]
    (C x : K) (hx : x′ ≠ 0) :
    channelConformalFlux C x =
      C * ((channelPeeling x)′ + (1 / 2 : K) * channelPeeling x ^ 2) := by
  rw [channelConformalFlux, schwarzian_eq_neg_deriv_channelPeeling_sub_half_sq x hx]
  ring

/-- Equation `(21)`: subtracting the quadratic reference leaves exactly the peeling derivative. -/
theorem channelConformalFlux_sub_quadraticReferenceFlux
    {K : Type*} [Field K] [CharZero K] [Differential K]
    (C x : K) (hx : x′ ≠ 0) :
    channelConformalFlux C x - channelQuadraticReferenceFlux C x =
      C * (channelPeeling x)′ := by
  rw [channelConformalFlux_eq C x hx, channelQuadraticReferenceFlux]
  ring

end GaloisForLFunctions.HTGeometry
