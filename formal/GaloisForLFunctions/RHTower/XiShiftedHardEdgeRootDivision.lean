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
    routeUHardEdgePairing σ (fun u => (u - r) * G u ^ (2 : ℕ)) = 0 := by
  have h := routeUEvenForm_eq_zero_of_diag σ (fun u => (u - r) * G u) G hFF hFG hGG hpsd hnull
  have heq : (fun u : ℝ => ((u - r) * G u) * G u) = fun u => (u - r) * G u ^ (2 : ℕ) := by
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
  have heq : (fun u : ℝ => (u - r) ^ (1 : ℕ) * G u ^ (2 : ℕ)) = fun u => (u - r) * G u ^ (2 : ℕ) := by
    funext u
    rw [pow_one]
  rw [heq]
  exact h

/-- At a nonnegative squared root, critical even positivity and nullity orient the divided odd
descendant without any incoming-wall inequality. -/
theorem routeUHardEdgeOddForm_divided_nonneg_of_nonnegative_root
    (σ : ℝ) (G : ℝ → ℝ) (r : ℝ)
    (hFF : IntegrableOn (fun u : ℝ =>
      ((u - r) * G u) * ((u - r) * G u) *
        routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u) (Ioi 0))
    (hFG : IntegrableOn (fun u : ℝ =>
      ((u - r) * G u) * G u *
        routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u) (Ioi 0))
    (hGG : IntegrableOn (fun u : ℝ =>
      G u * G u * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u) (Ioi 0))
    (hpsd : ∀ t : ℝ, 0 ≤ routeUHardEdgeEvenForm σ
      (fun u => (u - r) * G u + t * G u)
      (fun u => (u - r) * G u + t * G u))
    (hnull : routeUHardEdgeEvenForm σ
      (fun u => (u - r) * G u) (fun u => (u - r) * G u) = 0)
    (hr : 0 ≤ r)
    (hGnonneg : 0 ≤ routeUHardEdgeEvenForm σ G G) :
    0 ≤ routeUHardEdgeOddForm σ G G := by
  have hvanish : routeUJetMoment σ G r 1 = 0 :=
    routeUHardEdge_rootDivision_jetMoment σ G r hFF hFG hGG hpsd hnull
  have h1 : IntegrableOn (fun u : ℝ =>
      (u - r) ^ (1 : ℕ) * G u ^ (2 : ℕ) * routeUHardEdgeDensity σ (Real.sqrt u) /
        Real.sqrt u) (Ioi 0) := by
    refine hFG.congr_fun ?_ measurableSet_Ioi
    intro u _
    ring
  have h2 : IntegrableOn (fun u : ℝ =>
      r * ((u - r) ^ (0 : ℕ) * G u ^ (2 : ℕ)) * routeUHardEdgeDensity σ (Real.sqrt u) /
        Real.sqrt u) (Ioi 0) := by
    refine (hGG.const_mul r).congr (ae_of_all _ fun u => ?_)
    ring
  have hterminal := routeUOddForm_terminal σ G r 0 h1 h2 hvanish
  have hdesc : routeUJetDescendant 0 r G 0 = G := by
    funext u
    simp [routeUJetDescendant]
  have hm0 : routeUJetMoment σ G r 0 = routeUHardEdgeEvenForm σ G G := by
    rw [routeUJetMoment, routeUHardEdgeEvenForm]
    congr 1
    funext u
    ring
  rw [hdesc, hm0] at hterminal
  rw [hterminal]
  exact mul_nonneg hr hGnonneg

/-- A symmetric real Fourier-zero pair has squared root `c² ≥ 0`; therefore the simple divided
odd branch cannot be negative once the even quotient is admitted to the critical positive form. -/
theorem routeUHardEdgeOddForm_divided_nonneg_of_symmetric_real_roots
    (σ : ℝ) (G : ℝ → ℝ) (c : ℝ)
    (hFF : IntegrableOn (fun u : ℝ =>
      ((u - c ^ (2 : ℕ)) * G u) * ((u - c ^ (2 : ℕ)) * G u) *
        routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u) (Ioi 0))
    (hFG : IntegrableOn (fun u : ℝ =>
      ((u - c ^ (2 : ℕ)) * G u) * G u *
        routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u) (Ioi 0))
    (hGG : IntegrableOn (fun u : ℝ =>
      G u * G u * routeUHardEdgeDensity σ (Real.sqrt u) / Real.sqrt u) (Ioi 0))
    (hpsd : ∀ t : ℝ, 0 ≤ routeUHardEdgeEvenForm σ
      (fun u => (u - c ^ (2 : ℕ)) * G u + t * G u)
      (fun u => (u - c ^ (2 : ℕ)) * G u + t * G u))
    (hnull : routeUHardEdgeEvenForm σ
      (fun u => (u - c ^ (2 : ℕ)) * G u) (fun u => (u - c ^ (2 : ℕ)) * G u) = 0)
    (hGnonneg : 0 ≤ routeUHardEdgeEvenForm σ G G) :
    0 ≤ routeUHardEdgeOddForm σ G G :=
  routeUHardEdgeOddForm_divided_nonneg_of_nonnegative_root
    σ G (c ^ (2 : ℕ)) hFF hFG hGG hpsd hnull (sq_nonneg c) hGnonneg

end RHTower

end
