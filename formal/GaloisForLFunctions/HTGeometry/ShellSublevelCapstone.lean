/-
# The transversality tail from a shell polynomial

Assembling the elimination chain: a nonzero polynomial on the shell whose evaluation scales like a
power and which factors as a continuous function times a nonnegative observable gives that
observable a power-law sublevel bound on the shell.  Homogeneity is read off the scaling, the
cofactor is bounded by compactness, and the polynomial sublevel bound does the rest.

Main results:
* `exists_toSphere_sublevel_le_of_shellPoly` — **the transversality tail**.
-/
import GaloisForLFunctions.HTGeometry.SublevelTransfer
import GaloisForLFunctions.HTGeometry.HomogeneousEvalCriterion

open Set MeasureTheory Metric
open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {m : ℕ}

/-- **The transversality tail.**  A nonnegative observable which is a continuous multiple of a
nonzero polynomial with power scaling has a power-law shell sublevel bound. -/
theorem exists_toSphere_sublevel_le_of_shellPoly {d : ℕ} (hd : 0 < d)
    (G : MvPolynomial (Fin (m + 1)) ℝ) (hG0 : G ≠ 0)
    (hGscale : ∀ (t : ℝ) (x : Fin (m + 1) → ℝ),
      MvPolynomial.eval (fun i => t * x i) G = t ^ d * MvPolynomial.eval x G)
    {h g : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 → ℝ}
    (hh : ∀ ω, 0 ≤ h ω) (hg : Continuous g)
    (hfac : ∀ ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1,
      MvPolynomial.eval (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (m + 1)))) G = g ω * h ω) :
    ∃ A : ℝ≥0∞, A ≠ ⊤ ∧ ∀ ε : ℝ, 0 ≤ ε →
      volume.toSphere {ω | h ω ≤ ε} ≤ A * ENNReal.ofReal (ε ^ ((1 : ℝ) / d)) := by
  haveI : CompactSpace (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
  haveI : Nonempty (sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1) :=
    Set.Nonempty.to_subtype (NormedSpace.sphere_nonempty.mpr zero_le_one)
  have hhom : G.IsHomogeneous d := isHomogeneous_of_eval_smul hGscale
  obtain ⟨C, hC, hCbound⟩ :=
    exists_bound_of_continuous_cofactor
      (X := sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1)
      (F := fun ω : sphere (0 : EuclideanSpace ℝ (Fin (m + 1))) 1 =>
        MvPolynomial.eval (WithLp.ofLp (ω : EuclideanSpace ℝ (Fin (m + 1)))) G)
      (h := h) (g := g) hg hh hfac
  exact exists_toSphere_sublevel_le_of_dominated hd G hhom hG0 hC hCbound

end

end GaloisForLFunctions.HTGeometry
