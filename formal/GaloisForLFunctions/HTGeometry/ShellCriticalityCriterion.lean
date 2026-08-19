/-
# The criticality criterion for a quantity satisfying a polynomial relation on the shell

A spectral action is not a polynomial in the shell coordinates, but it is a root of a polynomial
whose coefficients are.  Differentiating that relation along a coordinate line and using the
tangential criticality condition turns "the tangential gradient vanishes" into the vanishing of an
explicit polynomial expression in the coordinates and the action value.

Main results:
* `hasDerivAt_coordinate_line` — the coordinate line and its derivative.
* `shell_criticality_relation` — **the criticality criterion**.
-/
import GaloisForLFunctions.HTGeometry.PolynomialRelationImplicitDerivative
import GaloisForLFunctions.HTGeometry.PolynomialZeroSetDimension

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

/-- The coordinate line through a point, and its derivative. -/
theorem hasDerivAt_coordinate_line (θ₀ : Fin N → ℝ) (i j : Fin N) :
    HasDerivAt (fun t : ℝ => θ₀ j + (if j = i then t else 0)) (if j = i then (1 : ℝ) else 0) 0 := by
  by_cases hj : j = i
  · simp only [if_pos hj]
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (θ₀ j)
  · simp only [if_neg hj]
    simpa using hasDerivAt_const (0 : ℝ) (θ₀ j + 0)

/-- **The criticality criterion.**  If a quantity satisfies a polynomial relation with polynomial
coefficients, and its derivative along a coordinate line is the tangential-criticality value, then
an explicit polynomial expression in the coordinates and the value vanishes. -/
theorem shell_criticality_relation {m : ℕ} (c : ℕ → MvPolynomial (Fin N) ℝ)
    (φ : (Fin N → ℝ) → ℝ) (θ₀ : Fin N → ℝ) (i : Fin N)
    (hrel : ∀ θ : Fin N → ℝ,
      ∑ n ∈ Finset.range m, MvPolynomial.eval θ (c n) * (φ θ) ^ n = 0)
    (hcrit : HasDerivAt (fun t : ℝ => φ (fun j => θ₀ j + (if j = i then t else 0)))
      (φ θ₀ * θ₀ i) 0) :
    (∑ n ∈ Finset.range m,
        MvPolynomial.eval θ₀ (MvPolynomial.pderiv i (c n)) * (φ θ₀) ^ n)
      + (∑ n ∈ Finset.range m, (n : ℝ) * MvPolynomial.eval θ₀ (c n) * (φ θ₀) ^ (n - 1))
        * (φ θ₀ * θ₀ i) = 0 := by
  classical
  have hbase : (fun j : Fin N => θ₀ j + (if j = i then (0 : ℝ) else 0)) = θ₀ := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  have ha : ∀ n : ℕ,
      HasDerivAt (fun t : ℝ =>
          MvPolynomial.eval (fun j => θ₀ j + (if j = i then t else 0)) (c n))
        (MvPolynomial.eval θ₀ (MvPolynomial.pderiv i (c n))) 0 := by
    intro n
    have hchain := hasDerivAt_mvPolynomial_eval_curve_real (c n)
      (fun j => fun t : ℝ => θ₀ j + (if j = i then t else 0))
      (fun j => if j = i then (1 : ℝ) else 0) 0
      (fun j => hasDerivAt_coordinate_line θ₀ i j)
    rw [hbase] at hchain
    refine hchain.congr_deriv ?_
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg hj, mul_zero])
      (fun hc => absurd (Finset.mem_univ i) hc)]
    simp
  have hzero : ∀ᶠ t in 𝓝 (0 : ℝ),
      ∑ n ∈ Finset.range m,
        MvPolynomial.eval (fun j => θ₀ j + (if j = i then t else 0)) (c n)
          * (φ (fun j => θ₀ j + (if j = i then t else 0))) ^ n = 0 :=
    Filter.Eventually.of_forall fun t => hrel _
  have hmain := polyCurve_relation (m := m) ha hcrit hzero
  rw [hbase] at hmain
  exact hmain

end

end GaloisForLFunctions.HTGeometry
