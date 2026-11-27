import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.EnergyRotation.Splitting
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.EnergyRotation.SpectralPeak
import GaloisForLFunctions.HTGeometry.ProjectiveContinuousCircuitConeLaw

/-! # An all-time energy rotation test for a proposed circuit -/
open Matrix NormedSpace Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.EnergyRotation
noncomputable section
private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ
local instance (n : ℕ) : CStarAlgebra (Reg n) where

private theorem flow_add {n : ℕ} (H : selfAdjoint (Reg n)) (s t : ℝ) :
    unitaryEvolution H.val s*unitaryEvolution H.val t=unitaryEvolution H.val (s+t) := by
  simpa only [add_sub_cancel_right] using unitaryEvolution_sub_mul H (s+t) t

private theorem rotated_flow {n : ℕ} (H : selfAdjoint (Reg n))
    (V : unitaryGroup (Fin n → Bool) ℂ) (t s : ℝ) (z : ℂ) (hz : ‖z‖=1) :
    ‖unitaryEvolution H.val s-unitaryEvolution (V.val*H.val*star V.val) s‖ ≤
      2*‖unitaryEvolution H.val t-z • V.val‖ := by
  let U := unitaryEvolution H.val
  have hs := unitaryEvolution_mem_unitary H.2 s
  have he : U s*U t=U t*U s := (flow_add H s t).trans (by rw [add_comm,←flow_add])
  have hc : z • (U s*V.val-V.val*U s)=
      (U t-z • V.val)*U s-U s*(U t-z • V.val) := by
    rw [sub_mul,mul_sub,Matrix.smul_mul,Matrix.mul_smul,he,smul_sub]
    abel
  have hle := norm_sub_le ((U t-z • V.val)*U s) (U s*(U t-z • V.val))
  rw [←hc,norm_smul,hz,one_mul,CStarRing.norm_mul_mem_unitary _ hs,
    CStarRing.norm_mem_unitary_mul _ hs,←two_mul] at hle
  have hu : IsUnit V.val := ⟨⟨V.val,star V.val,V.property.2,V.property.1⟩,rfl⟩
  have hinv := inv_eq_star_of_mem_unitary V.property
  rw [←hinv,unitaryEvolution_conj V.val H.val hu s,hinv]
  have hrew : U s-V.val*U s*star V.val=(U s*V.val-V.val*U s)*star V.val := by
    rw [sub_mul,mul_assoc (U s) V.val,V.property.2,mul_one]
  change ‖U s-V.val*U s*star V.val‖≤_
  have hstar : star V.val∈unitary (Reg n) := (V⁻¹).property
  rw [hrew,CStarRing.norm_mul_mem_unitary _ hstar]
  exact hle

private theorem flow_split {n : ℕ} (H B : Reg n) (hH : IsSelfAdjoint H) (hB : IsSelfAdjoint B)
    (s : ℝ) (hs : 0 ≤ s) :
    ‖unitaryEvolution H s*unitaryEvolution B (-s)-unitaryEvolution (H-B) s‖ ≤
      s^2/2*‖H*B-B*H‖ := by
  let x := (-Complex.I) • H
  let y := Complex.I • B
  have hx : x∈skewAdjoint (Reg n) := by rw [skewAdjoint.mem_iff,star_smul,hH.star_eq]; simp [x]
  have hy : y∈skewAdjoint (Reg n) := by rw [skewAdjoint.mem_iff,star_smul,hB.star_eq]; simp [y]
  have hsum : x+y=(-Complex.I) • (H-B) := by simp only [x,y,smul_sub,neg_smul,sub_neg_eq_add]
  have hcomm : x*y-y*x=H*B-B*H := by
    dsimp only [x,y]
    simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul,neg_mul,mul_neg,Complex.I_mul_I,
      neg_neg,one_smul]
  have hneg : unitaryEvolution B (-s)=NormedSpace.exp (s • y) := by
    simp only [y,unitaryEvolution,neg_smul,smul_neg,neg_neg]
  rw [hneg]
  change ‖NormedSpace.exp (s • x)*NormedSpace.exp (s • y)-NormedSpace.exp (s • ((-Complex.I) • (H-B)))‖ ≤ _
  rw [←hsum,←hcomm]
  exact split_error x y hx hy s hs

private theorem price_of_peak {N d c : ℝ} (hN : 0<N)
    (h : 2≤(π/N)^2/2*c+2*d) : 4*(1-d)*N^2≤π^2*c := by
  rw [div_pow] at h
  field_simp [hN.ne'] at h
  linarith only [h]

/-- For a physical fit at any date, the squared operator norm of the
Hamiltonian change is controlled by its commutator with the old Hamiltonian.
The right side can be estimated using only overlapping interactions. -/
theorem physical_energy_rotation {n : ℕ} (H : selfAdjoint (Reg n))
    (V : unitaryGroup (Fin n → Bool) ℂ) (t : ℝ) (z : ℂ) (hz : ‖z‖=1) :
    let B := V.val*H.val*star V.val
    4*(1-‖unitaryEvolution H.val t-z • V.val‖)*‖H.val-B‖^2≤π^2*‖H.val*B-B*H.val‖ := by
  intro B
  have hB : IsSelfAdjoint B := by
    dsimp only [IsSelfAdjoint,B]; rw [star_mul,star_mul,star_star,H.2.star_eq,mul_assoc]
  let A : selfAdjoint (Reg n) := ⟨H.val-B,H.2.sub hB⟩
  by_cases hN : ‖A.val‖=0
  · change _*‖A.val‖^2≤_
    rw [hN,zero_pow (by decide),mul_zero]
    positivity
  have hpos := lt_of_le_of_ne (norm_nonneg A.val) (Ne.symm hN)
  let s := π/‖A.val‖
  have hcan : unitaryEvolution B s*unitaryEvolution B (-s)=1 := by
    simpa only [add_neg_cancel,unitaryEvolution,zero_smul,NormedSpace.exp_zero] using flow_add ⟨B,hB⟩ s (-s)
  let U := unitaryEvolution H.val s
  let R := unitaryEvolution B (-s)
  have hrel : ‖U*R-1‖≤2*‖unitaryEvolution H.val t-z • V.val‖ := by
    rw [←hcan,←sub_mul,CStarRing.norm_mul_mem_unitary _ (unitaryEvolution_mem_unitary hB (-s))]
    exact rotated_flow H V t s z hz
  have herr : ‖U*R-unitaryEvolution A.val s‖ ≤ s^2/2*‖H.val*B-B*H.val‖ := by
    exact flow_split H.val B H.2 hB s (div_pos pi_pos hpos).le
  have h := (spectral_peak A hpos).trans (norm_sub_le_norm_sub_add_norm_sub _ (U*R) _)
  rw [norm_sub_rev (unitaryEvolution A.val s)] at h
  have hfinal := h.trans (add_le_add herr hrel)
  exact price_of_peak hpos hfinal

#print axioms physical_energy_rotation
end
end GaloisForLFunctions.HTGeometry.EnergyRotation
