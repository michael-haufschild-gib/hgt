import GaloisForLFunctions.RHTower.Suzuki.SuzukiTaV2ActualSecondDefectJet
import GaloisForLFunctions.RHTower.Suzuki.SuzukiTaV2LivsicUpperHalfPlaneCofinalLimit

/-!
# Joint cofinal transport of Suzuki's first two actual defect coordinates

One canonical aperture subsequence transports both literal completed-source coefficients.  First
coordinate is covariance-energy imbalance; second is endpoint torque.  Second disk coordinate
retains both upper-half-plane jets through exact Cayley acceleration, so compactness cannot erase
it by first-jet scalarization.
-/

open Complex Metric Set Filter Topology

noncomputable section
namespace RHTower

open GaloisForLFunctions.RHTower

/-- Exact second-order Cayley transport at Suzuki's anchor. -/
theorem iteratedDeriv_two_comp_suzukiUpperCayleyInv_zero
    {theta : ℂ → ℂ} (htheta : ContDiffAt ℂ 2 theta I) :
    iteratedDeriv 2 (fun w => theta (suzukiUpperCayleyInv w)) 0 =
      iteratedDeriv 2 theta I * (2 * I) ^ (2 : ℕ) + deriv theta I * (4 * I) := by
  have hinv : ContDiffAt ℂ 2 suzukiUpperCayleyInv 0 := by
    change ContDiffAt ℂ 2 (fun w : ℂ => I * ((1 + w) / (1 - w))) 0
    fun_prop (disch := norm_num)
  have htheta' : ContDiffAt ℂ 2 theta (suzukiUpperCayleyInv 0) := by
    simpa [suzukiUpperCayleyInv] using htheta
  have hcomp := iteratedDeriv_comp_two htheta' hinv
  change iteratedDeriv 2 (fun w => theta (suzukiUpperCayleyInv w)) 0 = _ at hcomp
  rw [hcomp]
  simp only [suzukiUpperCayleyInv, add_zero, sub_zero, div_one, mul_one,
    deriv_suzukiUpperCayleyInv_zero,
    iteratedDeriv_two_suzukiUpperCayleyInv_zero]

/-- Actual endpoint torque is precisely the Cayley-transported pair of first and second
upper-half-plane jets. -/
theorem suzukiTaV2EndpointSecondTorque_eq_upperHalfPlaneJets
    (a : SuzukiPositiveAperture) :
    suzukiTaV2EndpointSecondTorque a =
      iteratedDeriv 2 (suzukiTaV2Livsic a) I * (2 * I) ^ (2 : ℕ) +
        deriv (suzukiTaV2Livsic a) I * (4 * I) := by
  let U : Set ℂ := {z : ℂ | 0 < z.im}
  have hdiffOn : DifferentiableOn ℂ (suzukiTaV2Livsic a) U :=
    differentiableOn_suzukiLivsicQuotient_upperHalfPlane
      (differentiable_suzukiTaV2CharacteristicA a)
      (differentiable_suzukiTaV2CharacteristicE a)
      (suzukiTaV2CharacteristicA_I a)
      (suzukiTaV2_allAngleRealZeros a)
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_im
  have hI : I ∈ U := by simp [U]
  have htheta : ContDiffAt ℂ 2 (suzukiTaV2Livsic a) I :=
    (hdiffOn.analyticAt (hUopen.mem_nhds hI)).contDiffAt
  rw [← iteratedDeriv_two_comp_suzukiUpperCayleyInv_zero htheta]
  exact (iteratedDeriv_two_suzukiTaV2Livsic_disk_zero_eq_endpointSecondTorque a).symm

/-- A single literal canonical subsequence jointly transports Suzuki's first two completed-source
coordinates.  No Xi-identification premise occurs. -/
theorem exists_suzukiTaV2CanonicalCofinalActualFirstSecondDefectJetLimit :
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
        atTop (nhds (2 * I * deriv theta I)) ∧
      Tendsto
        (fun k => suzukiTaV2EndpointSecondTorque
          (suzukiTaV2CanonicalAperture (phi k)))
        atTop (nhds
          (iteratedDeriv 2 theta I * (2 * I) ^ (2 : ℕ) + deriv theta I * (4 * I))) := by
  obtain ⟨phi, theta, hphi, hcofinal, hconv, htheta, hbound, hanchor, hjets⟩ :=
    exists_suzukiTaV2CanonicalCofinalLivsicLimit_on_upperHalfPlane
  have hjetOne := (hjets 1).tendsto_at (show 0 < (I : ℂ).im by norm_num)
  have hderiv : Tendsto
      (fun k => deriv
        (suzukiTaV2Livsic (suzukiTaV2CanonicalAperture (phi k))) I)
      atTop (nhds (deriv theta I)) := by
    simpa only [iteratedDeriv_one] using hjetOne
  have hangle : Tendsto
      (fun k => (suzukiDefectAngle
        (suzukiTaCoalescingEvenEnergy
          (suzukiTaV2CanonicalAperture (phi k)) 1)
        (suzukiTaCoalescingOddEnergy
          (suzukiTaV2CanonicalAperture (phi k)) 1) : ℂ))
      atTop (nhds (2 * I * deriv theta I)) := by
    simpa only [suzukiTaV2_coalescingDefectAngle_eq_two_I_mul_deriv] using
      (tendsto_const_nhds.mul hderiv : Tendsto
        (fun k => 2 * I * deriv
          (suzukiTaV2Livsic (suzukiTaV2CanonicalAperture (phi k))) I)
        atTop (nhds (2 * I * deriv theta I)))
  have hjetTwo := (hjets 2).tendsto_at (show 0 < (I : ℂ).im by norm_num)
  have htorqueJets : Tendsto
      (fun k =>
        iteratedDeriv 2
            (suzukiTaV2Livsic (suzukiTaV2CanonicalAperture (phi k))) I *
            (2 * I) ^ (2 : ℕ) +
          deriv (suzukiTaV2Livsic (suzukiTaV2CanonicalAperture (phi k))) I *
            (4 * I))
      atTop (nhds
        (iteratedDeriv 2 theta I * (2 * I) ^ (2 : ℕ) + deriv theta I * (4 * I))) :=
    (hjetTwo.mul tendsto_const_nhds).add (hderiv.mul tendsto_const_nhds)
  have htorque : Tendsto
      (fun k => suzukiTaV2EndpointSecondTorque
        (suzukiTaV2CanonicalAperture (phi k)))
      atTop (nhds
        (iteratedDeriv 2 theta I * (2 * I) ^ (2 : ℕ) + deriv theta I * (4 * I))) := by
    simpa only [suzukiTaV2EndpointSecondTorque_eq_upperHalfPlaneJets] using htorqueJets
  exact ⟨phi, theta, hphi, hcofinal, hconv, htheta, hbound, hanchor, hangle, htorque⟩

end RHTower
end
