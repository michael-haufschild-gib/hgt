import GaloisForLFunctions.RHTower.UpperHalfPlaneMontel
import GaloisForLFunctions.RHTower.Suzuki.SuzukiTaV2LivsicCharacteristic
import GaloisForLFunctions.HTGeometry.HolomorphicJetReturn

/-!
# Global cofinal limits of literal Suzuki v2 Livsic coordinates

The literal finite-aperture Schur functions admit a single cofinal subsequence converging locally
uniformly on the whole upper half-plane.  All holomorphic jets converge on that same subsequence.
This source compactness layer is independent of Xi-target projectivization.
-/

open Complex Metric Set Filter Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions.RHTower

@[simp] theorem suzukiTaV2Livsic_I (a : SuzukiPositiveAperture) :
    suzukiTaV2Livsic a I = 0 := by
  exact suzukiLivsicQuotient_I_eq_zero (suzukiTaV2CharacteristicA_I a)

/-- Canonical actual Suzuki Livsic coordinates admit one cofinal locally uniform limit on the
entire upper half-plane.  The limit remains Schur, stays anchored at zero, and all of its
holomorphic jets are the limits of the literal finite-aperture jets. -/
theorem exists_suzukiTaV2CanonicalCofinalLivsicLimit_on_upperHalfPlane :
    ∃ (phi : ℕ → ℕ) (theta : ℂ → ℂ), StrictMono phi ∧
      Tendsto (fun k => (suzukiTaV2CanonicalAperture (phi k)).1) atTop atTop ∧
      TendstoLocallyUniformlyOn
        (fun k => suzukiTaV2Livsic (suzukiTaV2CanonicalAperture (phi k)))
        theta atTop {z : ℂ | 0 < z.im} ∧
      DifferentiableOn ℂ theta {z : ℂ | 0 < z.im} ∧
      (∀ z : ℂ, 0 < z.im → ‖theta z‖ ≤ 1) ∧
      theta I = 0 ∧
      ∀ j : ℕ, TendstoLocallyUniformlyOn
        (fun k => iteratedDeriv j
          (suzukiTaV2Livsic (suzukiTaV2CanonicalAperture (phi k))))
        (iteratedDeriv j theta) atTop {z : ℂ | 0 < z.im} := by
  have hdiff : ∀ n, DifferentiableOn ℂ
      (suzukiTaV2Livsic (suzukiTaV2CanonicalAperture n))
      {z : ℂ | 0 < z.im} := by
    intro n
    exact differentiableOn_suzukiLivsicQuotient_upperHalfPlane
      (differentiable_suzukiTaV2CharacteristicA
        (suzukiTaV2CanonicalAperture n))
      (differentiable_suzukiTaV2CharacteristicE
        (suzukiTaV2CanonicalAperture n))
      (suzukiTaV2CharacteristicA_I (suzukiTaV2CanonicalAperture n))
      (suzukiTaV2_allAngleRealZeros (suzukiTaV2CanonicalAperture n))
  obtain ⟨phi, theta, hphi, hconv, htheta, hbound⟩ :=
    exists_subseq_tendstoLocallyUniformlyOn_upperHalfPlane
      hdiff
      (fun n z hz => (norm_suzukiTaV2Livsic_lt_one
        (suzukiTaV2CanonicalAperture n) hz).le)
  have hcofinal : Tendsto
      (fun k => (suzukiTaV2CanonicalAperture (phi k)).1) atTop atTop :=
    tendsto_suzukiTaV2CanonicalAperture_atTop.comp hphi.tendsto_atTop
  have hanchorPoint := hconv.tendsto_at (show 0 < (I : ℂ).im by norm_num)
  have hzero : Tendsto
      (fun k => suzukiTaV2Livsic (suzukiTaV2CanonicalAperture (phi k)) I)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds (x := (0 : ℂ))
  have hanchor : theta I = 0 := tendsto_nhds_unique hanchorPoint hzero
  have hjets : ∀ j : ℕ, TendstoLocallyUniformlyOn
      (fun k => iteratedDeriv j
        (suzukiTaV2Livsic (suzukiTaV2CanonicalAperture (phi k))))
      (iteratedDeriv j theta) atTop {z : ℂ | 0 < z.im} := by
    exact GaloisForLFunctions.iteratedDeriv_tendstoLocallyUniformlyOn_of_locallyUniform
      (isOpen_lt continuous_const Complex.continuous_im) hconv
      (Eventually.of_forall fun k => hdiff (phi k))
  exact ⟨phi, theta, hphi, hcofinal, hconv, htheta, hbound, hanchor, hjets⟩

end RHTower

end
