/-
# The criticality expression factors through the tangential gradient

The criticality expression of a quantity satisfying a polynomial relation is not merely *zero* at a
critical point: implicit differentiation shows it is the derivative of the relation in the unknown
times the deviation of the true directional derivative from the radial one.  Summing the squares
over the coordinate directions therefore factors as a square times the squared norm of the
tangential gradient, which is exactly the factorisation `G = g · h` a sublevel bound consumes.

Main results:
* `criticalityLeading`, `criticalityValue` — the two factors and the expression itself.
* `tangentialGradNormSq` — the squared norm of the tangential gradient.
* `criticalityValue_eq_leading_mul_tangential` — **the factorisation in one direction**.
* `criticalitySquareSum_eq_leading_sq_mul` — **the factorisation of the square sum**.
* `eval_map_criticalitySquareSum_eq_leading_sq_mul` — the same read off the symmetrisable
  polynomial.
* `tangentialGradNormSq_eq_sub_sq_of_euler` — on the unit sphere the tangential norm is the full
  gradient norm minus the square of the value.
-/
import GaloisForLFunctions.HTGeometry.CriticalitySquareSum
import GaloisForLFunctions.HTGeometry.ShellCriticalityCriterion

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N : ℕ}

/-- The derivative of the defining relation in the unknown, evaluated at a point. -/
def criticalityLeading (m : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ) (θ : Fin N → ℝ) (y : ℝ) : ℝ :=
  ∑ n ∈ Finset.range m, (n : ℝ) * MvPolynomial.eval θ (c n) * y ^ (n - 1)

/-- The criticality expression in one coordinate direction, evaluated at a point and a value. -/
def criticalityValue (m : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ) (θ : Fin N → ℝ) (y : ℝ)
    (i : Fin N) : ℝ :=
  (∑ n ∈ Finset.range m, MvPolynomial.eval θ (MvPolynomial.pderiv i (c n)) * y ^ n)
    + criticalityLeading m c θ y * (y * θ i)

theorem eval_map_criticalityPoly_eq (m : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ) (i : Fin N)
    (θ : Fin N → ℝ) (y : ℝ) :
    Polynomial.eval y (Polynomial.map (MvPolynomial.eval θ) (criticalityPoly m c i))
      = criticalityValue m c θ y i := by
  rw [eval_map_criticalityPoly, criticalityValue, criticalityLeading]

/-- The squared norm of the tangential part of a gradient at a point of the unit sphere: the
gradient minus its radial component, the latter being the value itself by Euler's relation. -/
def tangentialGradNormSq (y : ℝ) (θ : Fin N → ℝ) (D : Fin N → ℝ) : ℝ :=
  ∑ i : Fin N, (D i - y * θ i) ^ 2

theorem tangentialGradNormSq_nonneg (y : ℝ) (θ D : Fin N → ℝ) :
    0 ≤ tangentialGradNormSq y θ D :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem tangentialGradNormSq_eq_zero_iff (y : ℝ) (θ D : Fin N → ℝ) :
    tangentialGradNormSq y θ D = 0 ↔ ∀ i, D i = y * θ i := by
  constructor
  · intro h i
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin N))) => sq_nonneg (D j - y * θ j))).mp h i
      (Finset.mem_univ i)
    have hz : D i - y * θ i = 0 := (pow_eq_zero_iff two_ne_zero).mp this
    linarith
  · intro h
    exact Finset.sum_eq_zero fun i _ => by rw [h i]; ring

/-- On the unit sphere, with the radial derivative equal to the value, the tangential norm is the
full gradient norm minus the square of the value. -/
theorem tangentialGradNormSq_eq_sub_sq_of_euler (y : ℝ) (θ D : Fin N → ℝ)
    (hunit : ∑ i : Fin N, θ i ^ 2 = 1) (heuler : ∑ i : Fin N, θ i * D i = y) :
    tangentialGradNormSq y θ D = (∑ i : Fin N, (D i) ^ 2) - y ^ 2 := by
  have hexp : ∀ i : Fin N, (D i - y * θ i) ^ 2
      = (D i) ^ 2 - 2 * y * (θ i * D i) + y ^ 2 * (θ i ^ 2) := fun i => by ring
  rw [tangentialGradNormSq, Finset.sum_congr rfl fun i _ => hexp i]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, heuler,
    hunit]
  ring

section Factorisation

variable {m : ℕ} {c : ℕ → MvPolynomial (Fin N) ℝ} {φ : (Fin N → ℝ) → ℝ} {θ₀ : Fin N → ℝ}

/-- The derivative of a polynomial coefficient along a coordinate line is its partial derivative. -/
theorem hasDerivAt_coeff_coordinate_line (p : MvPolynomial (Fin N) ℝ) (θ₀ : Fin N → ℝ)
    (i : Fin N) :
    HasDerivAt (fun t : ℝ => MvPolynomial.eval (fun j => θ₀ j + (if j = i then t else 0)) p)
      (MvPolynomial.eval θ₀ (MvPolynomial.pderiv i p)) 0 := by
  classical
  have hbase : (fun j : Fin N => θ₀ j + (if j = i then (0 : ℝ) else 0)) = θ₀ := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  have hchain := hasDerivAt_mvPolynomial_eval_curve_real p
    (fun j => fun t : ℝ => θ₀ j + (if j = i then t else 0))
    (fun j => if j = i then (1 : ℝ) else 0) 0
    (fun j => hasDerivAt_coordinate_line θ₀ i j)
  rw [hbase] at hchain
  refine hchain.congr_deriv ?_
  rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg hj, mul_zero])
    (fun hc => absurd (Finset.mem_univ i) hc)]
  simp

/-- **The factorisation in one direction.**  The criticality expression is the derivative of the
relation in the unknown times the deviation of the directional derivative from the radial one. -/
theorem criticalityValue_eq_leading_mul_tangential (D : Fin N → ℝ) (i : Fin N)
    (hrel : ∀ θ : Fin N → ℝ,
      ∑ n ∈ Finset.range m, MvPolynomial.eval θ (c n) * (φ θ) ^ n = 0)
    (hD : HasDerivAt (fun t : ℝ => φ (fun j => θ₀ j + (if j = i then t else 0))) (D i) 0) :
    criticalityValue m c θ₀ (φ θ₀) i
      = criticalityLeading m c θ₀ (φ θ₀) * (φ θ₀ * θ₀ i - D i) := by
  classical
  have hbase : (fun j : Fin N => θ₀ j + (if j = i then (0 : ℝ) else 0)) = θ₀ := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  have hzero : ∀ᶠ t in 𝓝 (0 : ℝ),
      ∑ n ∈ Finset.range m,
        MvPolynomial.eval (fun j => θ₀ j + (if j = i then t else 0)) (c n)
          * (φ (fun j => θ₀ j + (if j = i then t else 0))) ^ n = 0 :=
    Filter.Eventually.of_forall fun t => hrel _
  have hmain := polyCurve_relation (m := m)
    (fun n => hasDerivAt_coeff_coordinate_line (c n) θ₀ i) hD hzero
  rw [hbase] at hmain
  rw [criticalityValue, criticalityLeading]
  have hA : (∑ n ∈ Finset.range m,
      MvPolynomial.eval θ₀ (MvPolynomial.pderiv i (c n)) * (φ θ₀) ^ n)
      = -((∑ n ∈ Finset.range m,
        (n : ℝ) * MvPolynomial.eval θ₀ (c n) * (φ θ₀) ^ (n - 1)) * D i) := by
    linarith [hmain]
  rw [hA]
  ring

/-- **The factorisation of the square sum.**  Summing the squares over the coordinate directions
splits off the squared leading factor from the squared tangential gradient. -/
theorem criticalitySquareSum_eq_leading_sq_mul (D : Fin N → ℝ)
    (hrel : ∀ θ : Fin N → ℝ,
      ∑ n ∈ Finset.range m, MvPolynomial.eval θ (c n) * (φ θ) ^ n = 0)
    (hD : ∀ i : Fin N,
      HasDerivAt (fun t : ℝ => φ (fun j => θ₀ j + (if j = i then t else 0))) (D i) 0) :
    ∑ i : Fin N, (criticalityValue m c θ₀ (φ θ₀) i) ^ 2
      = (criticalityLeading m c θ₀ (φ θ₀)) ^ 2 * tangentialGradNormSq (φ θ₀) θ₀ D := by
  rw [tangentialGradNormSq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [criticalityValue_eq_leading_mul_tangential D i hrel (hD i), mul_pow]
  ring

/-- The factorisation read off the polynomial that the symmetrisation over labellings consumes. -/
theorem eval_map_criticalitySquareSum_eq_leading_sq_mul (D : Fin N → ℝ)
    (hrel : ∀ θ : Fin N → ℝ,
      ∑ n ∈ Finset.range m, MvPolynomial.eval θ (c n) * (φ θ) ^ n = 0)
    (hD : ∀ i : Fin N,
      HasDerivAt (fun t : ℝ => φ (fun j => θ₀ j + (if j = i then t else 0))) (D i) 0) :
    Polynomial.eval (φ θ₀) (Polynomial.map (MvPolynomial.eval θ₀) (criticalitySquareSum m c))
      = (criticalityLeading m c θ₀ (φ θ₀)) ^ 2 * tangentialGradNormSq (φ θ₀) θ₀ D := by
  rw [eval_map_criticalitySquareSum]
  rw [← criticalitySquareSum_eq_leading_sq_mul D hrel hD]
  exact Finset.sum_congr rfl fun i _ => by rw [eval_map_criticalityPoly_eq]

end Factorisation

end

end GaloisForLFunctions.HTGeometry
