import GaloisForLFunctions.HTGeometry.ClockNullMultiDalembert
import GaloisForLFunctions.HTGeometry.ConformalClockTwoSpeciesScaleLaw
import GaloisForLFunctions.HTGeometry.ClockProbeChartRiccati

/-!
# The effective potential of a scale function coupling several transverse coordinates

The two-species law reads the conformal scale off the effective potentials `V_μ^σ = μ e^{2σ} - D_σ`,
where the geometric defect is `D_σ = a □σ + a² Γ(σ,σ)`. This file computes both ingredients for a
scale function of the two null coordinates and `k` transverse ones.

The carré du champ contributes `-4 ∂ξσ ∂ησ + ∑ᵢ (∂ᵢσ)²`: the two null directions pair with each
other, not with themselves, and each transverse one pairs with itself. Together with the
d'Alembertian this makes the effective potential of such a scale function again a function of the
same coordinates, given explicitly by the derivatives of the scale.
-/

namespace GaloisForLFunctions.HTGeometry

open Set

variable {k n : ℕ} {u A B : ℝ → ℝ → (Fin k → ℝ) → ℝ} {C : Fin k → ℝ → ℝ → (Fin k → ℝ) → ℝ}
  {Ω : Set ((ℝ × ℝ) × (Fin k → ℝ))}

/-- **The carré du champ of a field of the null and finitely many transverse coordinates.** -/
theorem gradPair_nullMultiLift (h : IsC1OnMulti u A B C Ω) {x : Fin (k + n + 2) → ℝ}
    (hx : nullMultiCLM k n x ∈ Ω) :
    (SmoothPseudoMetric.ofSignature (slabEps (k + n))
        (slabEps_ne_zero (k + n))).chart.gradPair (nullMultiLift u n) (nullMultiLift u n) x
      = -4 * (A (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i))
          * B (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i)))
        + ∑ i : Fin k, C i (x 0 + x 1) (x 0 - x 1) (fun i' => x (transIdx k n i')) ^ (2 : ℕ) := by
  classical
  have hz : ∀ j : Fin (k + n + 2), j ≠ 0 → j ≠ 1 → (∀ i : Fin k, j ≠ transIdx k n i) →
      (slabEps (k + n) j)⁻¹ * coordPartial j (nullMultiLift u n) x
        * coordPartial j (nullMultiLift u n) x = 0 := by
    intro j h0 h1 ht
    rw [coordPartial_nullMultiLift_other h hx h0 h1 ht]
    ring
  rw [ofSignature_gradPair, sum_over_nullMultiIdx hz,
    coordPartial_nullMultiLift_zero h hx, coordPartial_nullMultiLift_one h hx,
    slabEps_zero, slabEps_of_ne (k + n) (Ne.symm (nullMulti_zero_ne_one k n))]
  have hsum : ∑ i : Fin k, (slabEps (k + n) (transIdx k n i))⁻¹
        * coordPartial (transIdx k n i) (nullMultiLift u n) x
        * coordPartial (transIdx k n i) (nullMultiLift u n) x
      = ∑ i : Fin k, C i (x 0 + x 1) (x 0 - x 1) (fun i' => x (transIdx k n i')) ^ (2 : ℕ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [slabEps_of_ne (k + n) (transIdx_ne_zero (n := n) i),
      coordPartial_nullMultiLift_trans h hx i]
    ring
  rw [hsum]
  ring

variable {Aa Ab Ba Bb : ℝ → ℝ → (Fin k → ℝ) → ℝ}
  {Ac Bc Ca Cb : Fin k → ℝ → ℝ → (Fin k → ℝ) → ℝ}
  {Cc : Fin k → Fin k → ℝ → ℝ → (Fin k → ℝ) → ℝ}

/-- The effective potential of a scale function of the two null coordinates and `k` transverse ones,
as a function of those coordinates. -/
noncomputable def conformalPotentialMulti (a massSq : ℝ)
    (u A B : ℝ → ℝ → (Fin k → ℝ) → ℝ) (C : Fin k → ℝ → ℝ → (Fin k → ℝ) → ℝ)
    (Ab Ba : ℝ → ℝ → (Fin k → ℝ) → ℝ) (Cc : Fin k → Fin k → ℝ → ℝ → (Fin k → ℝ) → ℝ) :
    ℝ → ℝ → (Fin k → ℝ) → ℝ :=
  fun s t y => massSq * Real.exp (2 * u s t y)
    - a * (-2 * (Ab s t y + Ba s t y) + ∑ i : Fin k, Cc i i s t y)
    - a ^ (2 : ℕ) * (-4 * (A s t y * B s t y) + ∑ i : Fin k, C i s t y ^ (2 : ℕ))

/-- **The effective potential of such a scale function is again a function of the same
coordinates**, given explicitly by the derivatives of the scale. -/
theorem conformalPotential_nullMultiLift (h : IsC1OnMulti u A B C Ω)
    (hA : IsC1OnMulti A Aa Ab Ac Ω) (hB : IsC1OnMulti B Ba Bb Bc Ω)
    (hC : ∀ i : Fin k, IsC1OnMulti (C i) (Ca i) (Cb i) (Cc i) Ω) (a massSq : ℝ)
    {x : Fin (k + n + 2) → ℝ} (hx : nullMultiCLM k n x ∈ Ω) :
    (SmoothPseudoMetric.ofSignature (slabEps (k + n))
        (slabEps_ne_zero (k + n))).chart.conformalPotential a massSq (nullMultiLift u n) x
      = nullMultiLift (conformalPotentialMulti a massSq u A B C Ab Ba Cc) n x := by
  show massSq * Real.exp (2 * nullMultiLift u n x)
      - (a * (SmoothPseudoMetric.ofSignature (slabEps (k + n))
          (slabEps_ne_zero (k + n))).chart.dalembert (nullMultiLift u n) x
        + a ^ (2 : ℕ) * (SmoothPseudoMetric.ofSignature (slabEps (k + n))
          (slabEps_ne_zero (k + n))).chart.gradPair (nullMultiLift u n) (nullMultiLift u n) x)
    = _
  rw [dalembert_nullMultiLift h hA hB hC hx, gradPair_nullMultiLift h hx]
  show massSq * Real.exp (2 * u (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i)))
      - (a * (-2 * (Ab (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i))
              + Ba (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i)))
            + ∑ i : Fin k, Cc i i (x 0 + x 1) (x 0 - x 1) (fun i' => x (transIdx k n i')))
        + a ^ (2 : ℕ) * (-4 * (A (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i))
              * B (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i)))
            + ∑ i : Fin k, C i (x 0 + x 1) (x 0 - x 1) (fun i' => x (transIdx k n i')) ^ (2 : ℕ)))
    = massSq * Real.exp (2 * u (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i)))
      - a * (-2 * (Ab (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i))
            + Ba (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i)))
          + ∑ i : Fin k, Cc i i (x 0 + x 1) (x 0 - x 1) (fun i' => x (transIdx k n i')))
      - a ^ (2 : ℕ) * (-4 * (A (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i))
            * B (x 0 + x 1) (x 0 - x 1) (fun i => x (transIdx k n i)))
          + ∑ i : Fin k, C i (x 0 + x 1) (x 0 - x 1) (fun i' => x (transIdx k n i')) ^ (2 : ℕ))
  ring

/-- **The effective potential, as an identity of fields on the region where the scale is
differentiable.** -/
theorem conformalPotential_eqOn_nullMultiLift (h : IsC1OnMulti u A B C Ω)
    (hA : IsC1OnMulti A Aa Ab Ac Ω) (hB : IsC1OnMulti B Ba Bb Bc Ω)
    (hC : ∀ i : Fin k, IsC1OnMulti (C i) (Ca i) (Cb i) (Cc i) Ω) (a massSq : ℝ) :
    ∀ x ∈ nullMultiBox (k := k) Ω n,
      (SmoothPseudoMetric.ofSignature (slabEps (k + n))
          (slabEps_ne_zero (k + n))).chart.conformalPotential a massSq (nullMultiLift u n) x
        = nullMultiLift (conformalPotentialMulti a massSq u A B C Ab Ba Cc) n x :=
  fun _ hx => conformalPotential_nullMultiLift h hA hB hC a massSq hx

end GaloisForLFunctions.HTGeometry
