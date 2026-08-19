/-
# Transferring a polynomial sublevel bound to a dominated observable

The shell sublevel bound holds for polynomials.  Any nonnegative observable which dominates a
nonzero homogeneous polynomial -- up to a constant -- inherits the same power-law sublevel bound,
because its sublevel sets are contained in the polynomial's.

This is the final step of the transversality tail: once elimination produces a nonzero homogeneous
polynomial bounded by the gradient observable, the power law follows.

Main results:
* `exists_toSphere_sublevel_le_of_dominated` — **the transferred power-law bound**.
* `exists_toSphere_sublevel_le_of_dominated_finite` — the same, simultaneously for a finite family.
-/
import GaloisForLFunctions.HTGeometry.PolynomialSublevelSphere

open Set MeasureTheory Metric
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {m : ℕ}

/-- **The transferred power-law sublevel bound.**  A nonnegative observable dominating a nonzero
homogeneous polynomial has the polynomial's power-law shell sublevel bound. -/
theorem exists_toSphere_sublevel_le_of_dominated {d : ℕ} (hd : 0 < d)
    (P : MvPolynomial (Fin (m + 1)) ℝ) (hP : P.IsHomogeneous d) (hP0 : P ≠ 0)
    {h : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 → ℝ} {C : ℝ} (hC : 0 < C)
    (hdom : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
      |MvPolynomial.eval (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (m + 1)))) P| ≤ C * h ω) :
    ∃ A : ℝ≥0∞, A ≠ ⊤ ∧ ∀ g : ℝ, 0 ≤ g →
      volume.toSphere {ω | h ω ≤ g} ≤ A * ENNReal.ofReal (g ^ ((1 : ℝ) / d)) := by
  obtain ⟨C₀, hC₀, hbound⟩ := exists_toSphere_sublevel_le hd P hP hP0
  refine ⟨C₀ * ENNReal.ofReal (C ^ ((1 : ℝ) / d)), ?_, fun g hg => ?_⟩
  · exact ENNReal.mul_ne_top hC₀ ENNReal.ofReal_ne_top
  · have hsub : {ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 | h ω ≤ g} ⊆
        {ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 |
          |MvPolynomial.eval (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (m + 1)))) P| ≤ C * g} := by
      intro ω hω
      exact le_trans (hdom ω) (mul_le_mul_of_nonneg_left (hω : h ω ≤ g) hC.le)
    have hCg : (0 : ℝ) ≤ C * g := mul_nonneg hC.le hg
    have hstep := hbound (C * g) hCg
    have hrpow : (C * g) ^ ((1 : ℝ) / d) = C ^ ((1 : ℝ) / d) * g ^ ((1 : ℝ) / d) :=
      Real.mul_rpow hC.le hg
    calc volume.toSphere {ω | h ω ≤ g}
        ≤ volume.toSphere {ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 |
            |MvPolynomial.eval (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (m + 1)))) P|
              ≤ C * g} := measure_mono hsub
      _ ≤ C₀ * ENNReal.ofReal ((C * g) ^ ((1 : ℝ) / d)) := hstep
      _ = C₀ * ENNReal.ofReal (C ^ ((1 : ℝ) / d)) * ENNReal.ofReal (g ^ ((1 : ℝ) / d)) := by
          rw [hrpow, ENNReal.ofReal_mul (Real.rpow_nonneg hC.le _), mul_assoc]

/-- **The transferred bound for a finite family**, with one exponent and one constant. -/
theorem exists_toSphere_sublevel_le_of_dominated_finite {ι : Type*} [Fintype ι] {d : ι → ℕ}
    (hd : ∀ a, 0 < d a) (P : ι → MvPolynomial (Fin (m + 1)) ℝ)
    (hP : ∀ a, (P a).IsHomogeneous (d a)) (hP0 : ∀ a, P a ≠ 0)
    {h : ι → sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 → ℝ} {C : ι → ℝ} (hC : ∀ a, 0 < C a)
    (hdom : ∀ (a : ι) (ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1),
      |MvPolynomial.eval (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (m + 1)))) (P a)|
        ≤ C a * h a ω) :
    ∀ a : ι, ∃ A : ℝ≥0∞, A ≠ ⊤ ∧ ∀ g : ℝ, 0 ≤ g →
      volume.toSphere {ω | h a ω ≤ g} ≤ A * ENNReal.ofReal (g ^ ((1 : ℝ) / d a)) := fun a =>
  exists_toSphere_sublevel_le_of_dominated (hd a) (P a) (hP a) (hP0 a) (hC a) (hdom a)

end

end GaloisForLFunctions.HTGeometry
