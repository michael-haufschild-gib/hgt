import GaloisForLFunctions.HTGeometry.QuasiCauchyPolynomial

/-!
# The finite-level Nevanlinna identity at complex arguments

Reading the polynomial identity of link 191 through `aeval` and dividing out the linear factors gives
the identity in the form the Cauchy transform uses:

`P(z)·∑_ξ w_ξ/(ξ − z) = −s₀·(R_{n+1}(z) + t·Rₙ(z))`  for complex `z` off the node set.

Nothing analytic is involved: the nodes are finitely many and the sum is finite.
-/

open scoped BigOperators
open Polynomial

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The cofactor at a node, evaluated at a complex point off that node. -/
theorem aeval_quasiCofactor (n : ℕ) (t : ℝ) {ξ : ℝ} (hξ : ξ ∈ quasiNodes s n t) {z : ℂ}
    (hz : ((ξ : ℝ) : ℂ) ≠ z) :
    Polynomial.aeval z (quasiOrtho s n t /ₘ (X - C ξ))
      = Polynomial.aeval z (quasiOrtho s n t) / (z - ((ξ : ℝ) : ℂ)) := by
  have hroot : (quasiOrtho s n t).eval ξ = 0 := (mem_quasiNodes_iff n t ξ).mp hξ
  have hmod : (quasiOrtho s n t) %ₘ (X - C ξ) = 0 := by
    rw [Polynomial.modByMonic_X_sub_C_eq_C_eval, hroot, map_zero]
  have hadd := Polynomial.modByMonic_add_div (quasiOrtho s n t) (X - C ξ)
  rw [hmod, zero_add] at hadd
  have hev := congrArg (Polynomial.aeval z) hadd
  simp only [map_mul, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
    Complex.coe_algebraMap] at hev
  have hne : z - ((ξ : ℝ) : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  field_simp
  rw [← hev]
  ring

/-- **The finite-level Nevanlinna identity at a complex argument.** -/
theorem quasiCauchy_identity_complex (h : PositiveMomentForm s) (n : ℕ) (t : ℝ) {z : ℂ}
    (hz : ∀ ξ ∈ quasiNodes s n t, ((ξ : ℝ) : ℂ) ≠ z) :
    Polynomial.aeval z (quasiOrtho s n t) *
        ∑ ξ ∈ quasiNodes s n t, ((quasiWeight s n t ξ : ℝ) : ℂ) / (((ξ : ℝ) : ℂ) - z)
      = -((s 0 : ℝ) : ℂ) *
          (secondKindC s (n + 1) z + ((t : ℝ) : ℂ) * secondKindC s n z) := by
  classical
  have hsum : Polynomial.aeval z (quasiCofactorSum s n t)
      = Polynomial.aeval z (quasiOrtho s n t) *
        ∑ ξ ∈ quasiNodes s n t, ((quasiWeight s n t ξ : ℝ) : ℂ) / (z - ((ξ : ℝ) : ℂ)) := by
    rw [quasiCofactorSum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ξ hξ => ?_
    rw [map_mul, Polynomial.aeval_C, aeval_quasiCofactor n t hξ (hz ξ hξ)]
    simp only [Complex.coe_algebraMap]
    ring
  have hflip : ∀ ξ ∈ quasiNodes s n t,
      ((quasiWeight s n t ξ : ℝ) : ℂ) / (z - ((ξ : ℝ) : ℂ))
        = -(((quasiWeight s n t ξ : ℝ) : ℂ) / (((ξ : ℝ) : ℂ) - z)) := by
    intro ξ _
    rw [← div_neg]
    ring_nf
  rw [Finset.sum_congr rfl hflip] at hsum
  have hneg : ∑ ξ ∈ quasiNodes s n t,
      -(((quasiWeight s n t ξ : ℝ) : ℂ) / (((ξ : ℝ) : ℂ) - z))
      = -∑ ξ ∈ quasiNodes s n t, ((quasiWeight s n t ξ : ℝ) : ℂ) / (((ξ : ℝ) : ℂ) - z) := by
    simp
  rw [hneg] at hsum
  rw [quasiCofactorSum_aeval h n t z] at hsum
  have hfinal : Polynomial.aeval z (quasiOrtho s n t) *
      ∑ ξ ∈ quasiNodes s n t, ((quasiWeight s n t ξ : ℝ) : ℂ) / (((ξ : ℝ) : ℂ) - z)
      = -(((s 0 : ℝ) : ℂ) *
          (secondKindC s (n + 1) z + ((t : ℝ) : ℂ) * secondKindC s n z)) := by
    linear_combination hsum
  rw [hfinal]
  ring

end HTGeometry
