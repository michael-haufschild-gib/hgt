import GaloisForLFunctions.HTGeometry.ClockNullTransverseLift
import GaloisForLFunctions.HTGeometry.ConformalClockTwoSpeciesScaleLaw
import GaloisForLFunctions.HTGeometry.ClockProbeChartRiccati

/-!
# The effective potential of a scale function with coupled transverse dependence

The two-species law reads the conformal scale off the effective potentials `V_μ^σ = μ e^{2σ} - D_σ`,
where the geometric defect is `D_σ = a □σ + a² Γ(σ,σ)`. This file computes both ingredients for a
scale function of the two null coordinates and one transverse coordinate.

The carré du champ contributes `-4 ∂ξσ ∂ησ + (∂₂σ)²`: the two null directions pair with each other,
not with themselves, and the transverse one pairs with itself. Together with the d'Alembertian of the
previous chapter this makes the effective potential of such a scale function again a function of the
same three coordinates, given explicitly by the derivatives of the scale.

That is what turns the hypothesis of the scale law — that the effective potential is of the coupled
class — into an explicit condition on the scale function.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

variable {n : ℕ}

/-- A sum over the coordinate directions in which only the first three terms survive. -/
theorem sum_of_transverse_zero₃ {f : Fin (n + 3) → ℝ}
    (hz : ∀ i : Fin (n + 3), i ≠ 0 → i ≠ 1 → i ≠ 2 → f i = 0) :
    ∑ i, f i = f 0 + f 1 + f 2 := by
  rw [← Finset.sum_subset (Finset.subset_univ ({0, 1, 2} : Finset (Fin (n + 3))))]
  · rw [Finset.sum_insert (by simp [nullTrans_zero_ne_one n, nullTrans_zero_ne_two n]),
      Finset.sum_insert (by simp [nullTrans_one_ne_two n]), Finset.sum_singleton, add_assoc]
  · intro i _ hi
    exact hz i (fun hc => hi (by simp [hc])) (fun hc => hi (by simp [hc]))
      (fun hc => hi (by simp [hc]))

variable {u A B C : ℝ → ℝ → ℝ → ℝ} {Ω : Set ((ℝ × ℝ) × ℝ)}

/-- **The carré du champ of a field of the null and one transverse coordinate.** -/
theorem gradPair_nullTransLift (h : IsC1On3 u A B C Ω) {x : Fin (n + 3) → ℝ}
    (hx : nullTransCLM n x ∈ Ω) :
    (SmoothPseudoMetric.ofSignature (slabEps (n + 1))
        (slabEps_ne_zero (n + 1))).chart.gradPair (nullTransLift u n) (nullTransLift u n) x
      = -4 * (A (x 0 + x 1) (x 0 - x 1) (x 2) * B (x 0 + x 1) (x 0 - x 1) (x 2))
        + C (x 0 + x 1) (x 0 - x 1) (x 2) ^ 2 := by
  have hz : ∀ i : Fin (n + 3), i ≠ 0 → i ≠ 1 → i ≠ 2 →
      (slabEps (n + 1) i)⁻¹ * coordPartial i (nullTransLift u n) x
        * coordPartial i (nullTransLift u n) x = 0 := by
    intro i h0 h1 h2
    rw [coordPartial_nullTransLift_transverse h hx h0 h1 h2]
    ring
  rw [ofSignature_gradPair, sum_of_transverse_zero₃ hz,
    coordPartial_nullTransLift_zero h hx, coordPartial_nullTransLift_one h hx,
    coordPartial_nullTransLift_two h hx, slabEps_zero,
    slabEps_of_ne (n + 1) (Ne.symm (nullTrans_zero_ne_one n)),
    slabEps_of_ne (n + 1) (Ne.symm (nullTrans_zero_ne_two n))]
  ring

variable {Aa Ab Ac Ba Bb Bc Ca Cb Cc : ℝ → ℝ → ℝ → ℝ}

/-- The effective potential of a scale function of the two null coordinates and one transverse
coordinate, as a function of those coordinates. -/
noncomputable def conformalPotentialTri (a massSq : ℝ) (u A B C Ab Ba Cc : ℝ → ℝ → ℝ → ℝ) :
    ℝ → ℝ → ℝ → ℝ :=
  fun s t w => massSq * Real.exp (2 * u s t w)
    - a * (-2 * (Ab s t w + Ba s t w) + Cc s t w)
    - a ^ 2 * (-4 * (A s t w * B s t w) + C s t w ^ 2)

/-- **The effective potential of such a scale function is again a function of the same three
coordinates**, given explicitly by the derivatives of the scale. -/
theorem conformalPotential_nullTransLift (h : IsC1On3 u A B C Ω) (hA : IsC1On3 A Aa Ab Ac Ω)
    (hB : IsC1On3 B Ba Bb Bc Ω) (hC : IsC1On3 C Ca Cb Cc Ω) (a massSq : ℝ)
    {x : Fin (n + 3) → ℝ} (hx : nullTransCLM n x ∈ Ω) :
    (SmoothPseudoMetric.ofSignature (slabEps (n + 1))
        (slabEps_ne_zero (n + 1))).chart.conformalPotential a massSq (nullTransLift u n) x
      = nullTransLift (conformalPotentialTri a massSq u A B C Ab Ba Cc) n x := by
  show massSq * Real.exp (2 * nullTransLift u n x)
      - (a * (SmoothPseudoMetric.ofSignature (slabEps (n + 1))
          (slabEps_ne_zero (n + 1))).chart.dalembert (nullTransLift u n) x
        + a ^ 2 * (SmoothPseudoMetric.ofSignature (slabEps (n + 1))
          (slabEps_ne_zero (n + 1))).chart.gradPair (nullTransLift u n) (nullTransLift u n) x)
    = _
  rw [dalembert_nullTransLift h hA hB hC hx, gradPair_nullTransLift h hx]
  show massSq * Real.exp (2 * u (x 0 + x 1) (x 0 - x 1) (x 2))
      - (a * (-2 * (Ab (x 0 + x 1) (x 0 - x 1) (x 2) + Ba (x 0 + x 1) (x 0 - x 1) (x 2))
            + Cc (x 0 + x 1) (x 0 - x 1) (x 2))
        + a ^ 2 * (-4 * (A (x 0 + x 1) (x 0 - x 1) (x 2) * B (x 0 + x 1) (x 0 - x 1) (x 2))
            + C (x 0 + x 1) (x 0 - x 1) (x 2) ^ 2))
    = massSq * Real.exp (2 * u (x 0 + x 1) (x 0 - x 1) (x 2))
      - a * (-2 * (Ab (x 0 + x 1) (x 0 - x 1) (x 2) + Ba (x 0 + x 1) (x 0 - x 1) (x 2))
          + Cc (x 0 + x 1) (x 0 - x 1) (x 2))
      - a ^ 2 * (-4 * (A (x 0 + x 1) (x 0 - x 1) (x 2) * B (x 0 + x 1) (x 0 - x 1) (x 2))
          + C (x 0 + x 1) (x 0 - x 1) (x 2) ^ 2)
  ring

/-- **The effective potential, as an identity of fields on the region where the scale is
differentiable.** -/
theorem conformalPotential_eqOn_nullTransLift (h : IsC1On3 u A B C Ω) (hA : IsC1On3 A Aa Ab Ac Ω)
    (hB : IsC1On3 B Ba Bb Bc Ω) (hC : IsC1On3 C Ca Cb Cc Ω) (a massSq : ℝ) :
    ∀ x ∈ nullTransBox Ω n,
      (SmoothPseudoMetric.ofSignature (slabEps (n + 1))
          (slabEps_ne_zero (n + 1))).chart.conformalPotential a massSq (nullTransLift u n) x
        = nullTransLift (conformalPotentialTri a massSq u A B C Ab Ba Cc) n x :=
  fun _ hx => conformalPotential_nullTransLift h hA hB hC a massSq hx

end GaloisForLFunctions.HTGeometry
