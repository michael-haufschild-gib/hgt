import GaloisForLFunctions.RHTower.XiShiftedHardEdgeParityJet

/-!
# The root-division law at the hard edge

A real zero of the squared-variable boundary state supplies an admissible same-type variation:
dividing the state by that zero improves the real tail by two powers and keeps the logarithmic
Paley--Wiener form domain.  Substituting the quotient in the null equation of the state turns the
apparent real-axis singularity into an exact signed barycentre identity, with the polar atom
carried along.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

/-- **(HHWB.16)/(HHWB.20) The root-division Cauchy law.**  If the state `(u - r)·G` is null for the
literal hard-edge form and that form is nonnegative on the one-parameter family it spans with its
divided quotient, then the signed measure has vanishing first moment against `(u - r)G²`. -/
theorem routeUHardEdge_rootDivision (σ : ℝ) (G : ℝ → ℝ) (r : ℝ)
    (hFF : IntegrableOn (fun u : ℝ =>
      ((u - r) * G u) * ((u - r) * G u) * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u)
      (Ioi 0))
    (hFG : IntegrableOn (fun u : ℝ =>
      ((u - r) * G u) * G u * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u) (Ioi 0))
    (hGG : IntegrableOn (fun u : ℝ =>
      G u * G u * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u) (Ioi 0))
    (hpsd : ∀ t : ℝ, 0 ≤ routeUHardEdgeEvenForm σ
      (fun u => (u - r) * G u + t * G u) (fun u => (u - r) * G u + t * G u))
    (hnull : routeUHardEdgeEvenForm σ (fun u => (u - r) * G u) (fun u => (u - r) * G u) = 0) :
    routeUHardEdgePairing σ (fun u => (u - r) * G u ^ 2) = 0 := by
  have h := routeUEvenForm_eq_zero_of_diag σ (fun u => (u - r) * G u) G hFF hFG hGG hpsd hnull
  have heq : (fun u : ℝ => ((u - r) * G u) * G u) = fun u => (u - r) * G u ^ 2 := by
    funext u
    ring
  rw [routeUHardEdgeEvenForm, heq] at h
  exact h

/-- The same law written as the vanishing of every divided moment of the state itself. -/
theorem routeUHardEdge_rootDivision_jetMoment (σ : ℝ) (G : ℝ → ℝ) (r : ℝ)
    (hFF : IntegrableOn (fun u : ℝ =>
      ((u - r) * G u) * ((u - r) * G u) * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u)
      (Ioi 0))
    (hFG : IntegrableOn (fun u : ℝ =>
      ((u - r) * G u) * G u * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u) (Ioi 0))
    (hGG : IntegrableOn (fun u : ℝ =>
      G u * G u * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u) (Ioi 0))
    (hpsd : ∀ t : ℝ, 0 ≤ routeUHardEdgeEvenForm σ
      (fun u => (u - r) * G u + t * G u) (fun u => (u - r) * G u + t * G u))
    (hnull : routeUHardEdgeEvenForm σ (fun u => (u - r) * G u) (fun u => (u - r) * G u) = 0) :
    routeUJetMoment σ G r 1 = 0 := by
  have h := routeUHardEdge_rootDivision σ G r hFF hFG hGG hpsd hnull
  rw [routeUJetMoment]
  have heq : (fun u : ℝ => (u - r) ^ 1 * G u ^ 2) = fun u => (u - r) * G u ^ 2 := by
    funext u
    rw [pow_one]
  rw [heq]
  exact h

end RHTower

end
