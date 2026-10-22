import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekEndpointWindingPolynomialDarkSeparation
import Mathlib.LinearAlgebra.Vandermonde

/-!
# Finite PW endpoint-winding tomography

The literal finite-energy Parikh--Wilczek endpoint winding is not merely nonzero on the explicit
polynomial-dark packets isolated by the preceding no-go.  It faithfully recovers every finite
grade packet.

For a packet on grades `0,...,N-1`, sample the physical backreaction scale at
`epsilon_j = 1/(4(j+1))`.  The source-exact endpoint amplitude is then

`exp(-(j+1))^(k+1)`

in grade `k`.  Removing the nonzero row factor `exp(-(j+1))` leaves the ordinary Vandermonde
matrix on the distinct nodes `exp(-(j+1))`.  Consequently exactly `N` prescribed positive
backreaction samples separate all `N` coefficients.  This closes finite-support darkness for the
PW endpoint channel; no analytic continuation, generic nonlinear reporter, or RH premise enters.

`[NEW] [SOURCE-EXACT FINITE TOMOGRAPHY] [ARBITRARY FINITE PACKETS]
[VANDERMONDE RIGIDITY] [LEAN-PROVED]`
-/

open Matrix
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The `j`-th prescribed positive finite-mass scale used for endpoint tomography. -/
def schwarzschildParikhWilczekEndpointTomographyScale (j : ℕ) : ℝ :=
  1 / (4 * ((j : ℝ) + 1))

/-- Endpoint Laplace node at the `j`-th tomography scale. -/
def schwarzschildParikhWilczekEndpointTomographyNode (j : ℕ) : ℝ :=
  Real.exp (-((j : ℝ) + 1))

theorem schwarzschildParikhWilczekEndpointTomographyScale_pos (j : ℕ) :
    0 < schwarzschildParikhWilczekEndpointTomographyScale j := by
  rw [schwarzschildParikhWilczekEndpointTomographyScale]
  positivity

/-- At the prescribed physical scale, the endpoint Laplace base is the corresponding
Vandermonde node. -/
theorem schwarzschildParikhWilczekEndpointWindingLaplaceBase_sample
    (j : ℕ) :
    schwarzschildParikhWilczekEndpointWindingLaplaceBase
        (schwarzschildParikhWilczekEndpointTomographyScale j) =
      schwarzschildParikhWilczekEndpointTomographyNode j := by
  rw [schwarzschildParikhWilczekEndpointWindingLaplaceBase,
    schwarzschildParikhWilczekEndpointTomographyScale,
    schwarzschildParikhWilczekEndpointTomographyNode]
  congr 1
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  field_simp

/-- Response of an arbitrary `N`-grade packet at the `j`-th physical endpoint sample. -/
def schwarzschildParikhWilczekFinitePacketEndpointResponse
    {N : ℕ} (c : Fin N → ℝ) (j : Fin N) : ℝ :=
  ∑ k, c k *
    schwarzschildParikhWilczekWindingTerm k.val
      (schwarzschildParikhWilczekEndpointTomographyScale j.val)
      (schwarzschildParikhWilczekDimensionlessEnergyEndpoint
        (schwarzschildParikhWilczekEndpointTomographyScale j.val))

/-- The sampled source response is a shifted monomial Vandermonde row. -/
theorem schwarzschildParikhWilczekFinitePacketEndpointResponse_eq
    {N : ℕ} (c : Fin N → ℝ) (j : Fin N) :
    schwarzschildParikhWilczekFinitePacketEndpointResponse c j =
      ∑ k, c k *
        schwarzschildParikhWilczekEndpointTomographyNode j.val ^ (k.val + 1) := by
  rw [schwarzschildParikhWilczekFinitePacketEndpointResponse]
  simp_rw [schwarzschildParikhWilczekWindingTerm_energyEndpoint_eq_laplaceBase_pow _
    (schwarzschildParikhWilczekEndpointTomographyScale_pos j.val)]
  rw [schwarzschildParikhWilczekEndpointWindingLaplaceBase_sample]

/-- Distinct physical scales give distinct positive Laplace nodes. -/
theorem schwarzschildParikhWilczekEndpointTomographyNode_fin_injective
    (N : ℕ) :
    Function.Injective (fun j : Fin N =>
      schwarzschildParikhWilczekEndpointTomographyNode j.val) := by
  intro i j hij
  apply Fin.ext
  simp only [schwarzschildParikhWilczekEndpointTomographyNode] at hij
  have harg : -((i.val : ℝ) + 1) = -((j.val : ℝ) + 1) :=
    Real.exp_injective hij
  exact_mod_cast (by linarith : (i.val : ℝ) = (j.val : ℝ))

/-- **Finite source-exact PW tomography.**  An arbitrary packet supported on `N` grades vanishes
iff all its responses at the `N` prescribed positive endpoint scales vanish.  Thus the physical
endpoint winding has no nonzero finite-support dark packet. -/
theorem schwarzschildParikhWilczekFinitePacketEndpointResponse_eq_zero_iff
    {N : ℕ} (c : Fin N → ℝ) :
    (∀ j : Fin N, schwarzschildParikhWilczekFinitePacketEndpointResponse c j = 0) ↔
      c = 0 := by
  constructor
  · intro h
    let q : Fin N → ℝ := fun j =>
      schwarzschildParikhWilczekEndpointTomographyNode j.val
    have hsample (j : Fin N) :
        ∑ k, c k * q j ^ (k.val + 1) = 0 := by
      simpa [q, schwarzschildParikhWilczekFinitePacketEndpointResponse_eq] using h j
    have hpoly (j : Fin N) : ∑ k, c k * q j ^ k.val = 0 := by
      have hfactor : q j * (∑ k, c k * q j ^ k.val) = 0 := by
        calc
          q j * (∑ k, c k * q j ^ k.val) =
              ∑ k, c k * q j ^ (k.val + 1) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro k _
                rw [pow_succ]
                ring
          _ = 0 := hsample j
      exact (mul_eq_zero.mp hfactor).resolve_left (Real.exp_ne_zero _)
    have hq : Function.Injective q := by
      exact schwarzschildParikhWilczekEndpointTomographyNode_fin_injective N
    have hdet : (Matrix.vandermonde q).det ≠ 0 :=
      Matrix.det_vandermonde_ne_zero_iff.mpr hq
    have hmv : Matrix.vandermonde q *ᵥ c = 0 := by
      funext j
      simp only [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply, Pi.zero_apply]
      simpa only [mul_comm] using hpoly j
    exact Matrix.eq_zero_of_mulVec_eq_zero hdet hmv
  · rintro rfl
    simp [schwarzschildParikhWilczekFinitePacketEndpointResponse]

end

end RHTower
