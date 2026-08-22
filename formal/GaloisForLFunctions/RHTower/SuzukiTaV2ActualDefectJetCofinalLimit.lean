import GaloisForLFunctions.RHTower.SuzukiTaV2ActualDefectJet
import GaloisForLFunctions.RHTower.SuzukiTaV2LivsicUpperHalfPlaneCofinalLimit

/-!
# Cofinal transport of Suzuki's actual covariance defect coefficient

Global Schur compactness and the finite coefficient identity are combined on one literal canonical
aperture subsequence.  The actual completed covariance even/odd defect angles converge to the
first anchored jet of the resulting whole-upper-half-plane limit, with exact Cayley Jacobian
`2 i`.  No projective gauge or target-identification premise is introduced.
-/

open Complex Metric Set Filter Topology

noncomputable section
namespace RHTower

open GaloisForLFunctions.RHTower

theorem exists_suzukiTaV2CanonicalCofinalActualDefectJetLimit :
    ∃ (phi : ℕ → ℕ) (theta : ℂ → ℂ), StrictMono phi ∧
      Tendsto (fun k => (suzukiTaV2CanonicalAperture (phi k)).1) atTop atTop ∧
      TendstoLocallyUniformlyOn
        (fun k => suzukiTaV2Livsic (suzukiTaV2CanonicalAperture (phi k)))
        theta atTop {z : ℂ | 0 < z.im} ∧
      DifferentiableOn ℂ theta {z : ℂ | 0 < z.im} ∧
      (∀ z : ℂ, 0 < z.im → ‖theta z‖ ≤ 1) ∧
      theta I = 0 ∧
      Tendsto
        (fun k => (suzukiDefectAngle
          (suzukiTaCoalescingEvenEnergy
            (suzukiTaV2CanonicalAperture (phi k)) 1)
          (suzukiTaCoalescingOddEnergy
            (suzukiTaV2CanonicalAperture (phi k)) 1) : ℂ))
        atTop (nhds (2 * I * deriv theta I)) := by
  obtain ⟨phi, theta, hphi, hcofinal, hconv, htheta, hbound, hanchor, hjets⟩ :=
    exists_suzukiTaV2CanonicalCofinalLivsicLimit_on_upperHalfPlane
  have hjetPoint := (hjets 1).tendsto_at (show 0 < (I : ℂ).im by norm_num)
  have hderiv : Tendsto
      (fun k => deriv
        (suzukiTaV2Livsic (suzukiTaV2CanonicalAperture (phi k))) I)
      atTop (nhds (deriv theta I)) := by
    simpa only [iteratedDeriv_one] using hjetPoint
  have hscaled : Tendsto
      (fun k => 2 * I * deriv
        (suzukiTaV2Livsic (suzukiTaV2CanonicalAperture (phi k))) I)
      atTop (nhds (2 * I * deriv theta I)) :=
    tendsto_const_nhds.mul hderiv
  have hangle : Tendsto
      (fun k => (suzukiDefectAngle
        (suzukiTaCoalescingEvenEnergy
          (suzukiTaV2CanonicalAperture (phi k)) 1)
        (suzukiTaCoalescingOddEnergy
          (suzukiTaV2CanonicalAperture (phi k)) 1) : ℂ))
      atTop (nhds (2 * I * deriv theta I)) := by
    simpa only [suzukiTaV2_coalescingDefectAngle_eq_two_I_mul_deriv] using hscaled
  exact ⟨phi, theta, hphi, hcofinal, hconv, htheta, hbound, hanchor, hangle⟩

end RHTower
