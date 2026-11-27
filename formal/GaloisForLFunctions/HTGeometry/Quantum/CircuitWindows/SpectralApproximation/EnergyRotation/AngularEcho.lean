import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.EnergyRotation.PhysicalEcho
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AngularError.Products

/-! # Angular form of the energy rotation obstruction -/
open Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EnergyRotation
noncomputable section
open private flow_add flow_split price_of_peak from GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.EnergyRotation.PhysicalEcho
open private phase_unitary from GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.AngularError.Products
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ

private theorem angular_flow {n : ℕ} (H : selfAdjoint (Reg n)) (V : unitaryGroup (Fin n → Bool) ℂ)
    (t s : ℝ) (z : ℂ) (hz : ‖z‖=1) {θ : ℝ} (hθ : 0 ≤ θ) (ht : 2*θ ≤ π/2)
    (hfit : ‖unitaryEvolution H.val t-z • V.val‖ ≤ 2*sin θ) :
    ‖unitaryEvolution H.val s-unitaryEvolution (V.val*H.val*star V.val) s‖ ≤ 2*sin (2*θ) := by
  let U := unitaryEvolution H.val
  let P := z • V.val
  have hU := unitaryEvolution_mem_unitary H.2 s
  have hT := unitaryEvolution_mem_unitary H.2 t
  have hP : P∈unitary (Reg n) := phase_unitary V.property hz
  have hm : U s*U t=U t*U s := (flow_add H s t).trans (by rw [add_comm,←flow_add])
  have hx : ‖U s*P-U s*U t‖ ≤ 2*sin θ := by
    rw [←mul_sub,CStarRing.norm_mem_unitary_mul _ hU,norm_sub_rev]
    exact hfit
  have hy : ‖P*U s-U s*U t‖ ≤ 2*sin θ := by
    rw [hm,←sub_mul,CStarRing.norm_mul_mem_unitary _ hU,norm_sub_rev]
    exact hfit
  have hh := AngularError.common_unitary_chord (mul_mem hU hP) (mul_mem hU hT) (mul_mem hP hU) hθ ht hx hy
  have he : U s*P-P*U s=z • (U s*V.val-V.val*U s) := by rw [P,Matrix.mul_smul,Matrix.smul_mul,smul_sub]
  rw [he,norm_smul,hz,one_mul] at hh
  have hu : IsUnit V.val := ⟨⟨V.val,star V.val,V.property.2,V.property.1⟩,rfl⟩
  have hinv := inv_eq_star_of_mem_unitary V.property
  rw [←hinv,unitaryEvolution_conj V.val H.val hu s,hinv]
  have hrew : U s-V.val*U s*star V.val=(U s*V.val-V.val*U s)*star V.val := by
    rw [sub_mul,mul_assoc (U s) V.val,V.property.2,mul_one]
  change ‖U s-V.val*U s*star V.val‖ ≤ _
  have hstar : star V.val∈unitary (Reg n) := (V⁻¹).property
  rwa [hrew,CStarRing.norm_mul_mem_unitary _ hstar]

/-- Two points on the same unitary chord have separation at most twice
the sine of the doubled angle. The resulting test remains nontrivial
for all fitting errors strictly below √2. -/
theorem angular_energy_rotation {n : ℕ} (H : selfAdjoint (Reg n))
    (V : unitaryGroup (Fin n → Bool) ℂ) (t : ℝ) (z : ℂ) (hz : ‖z‖=1)
    {θ : ℝ} (hθ : 0 ≤ θ) (ht : 2*θ ≤ π/2) (hfit : ‖unitaryEvolution H.val t-z • V.val‖ ≤ 2*sin θ) :
    let B := V.val*H.val*star V.val
    4*(1-sin (2*θ))*‖H.val-B‖^2 ≤ π^2*‖H.val*B-B*H.val‖ := by
  intro B
  have hB : IsSelfAdjoint B := by
    dsimp only [IsSelfAdjoint,B]; rw [star_mul,star_mul,star_star,H.2.star_eq,mul_assoc]
  let A : selfAdjoint (Reg n) := ⟨H.val-B,H.2.sub hB⟩
  by_cases hN : ‖A.val‖=0
  · change _*‖A.val‖^2 ≤ _
    rw [hN,zero_pow (by decide),mul_zero]
    positivity
  have hpos := lt_of_le_of_ne (norm_nonneg A.val) (Ne.symm hN)
  let s := π/‖A.val‖
  let U := unitaryEvolution H.val s
  let R := unitaryEvolution B (-s)
  have hcan : unitaryEvolution B s*R=1 := by
    simpa only [R,add_neg_cancel,unitaryEvolution,zero_smul,NormedSpace.exp_zero] using flow_add ⟨B,hB⟩ s (-s)
  have hrel : ‖U*R-1‖ ≤ 2*sin (2*θ) := by
    rw [←hcan,←sub_mul,CStarRing.norm_mul_mem_unitary _ (unitaryEvolution_mem_unitary hB (-s))]
    exact angular_flow H V t s z hz hθ ht hfit
  have herr := flow_split H.val B H.2 hB s (div_pos pi_pos hpos).le
  have h := (spectral_peak A hpos).trans (norm_sub_le_norm_sub_add_norm_sub _ (U*R) _)
  rw [norm_sub_rev (unitaryEvolution A.val s)] at h
  exact price_of_peak hpos (h.trans (add_le_add herr hrel))

#print axioms angular_energy_rotation
end
end GaloisForLFunctions.HTGeometry.EnergyRotation
