import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.DensityWitnesses.Packet
import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension

/-! # Mixed-state witnesses at specified physical dates -/
open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralApproximation.DensityWitnesses
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- The witness retains the complex energy coefficients. Taking the
modulus removes the global phase after summation. -/
theorem physical_packet (H : selfAdjoint (Mat I)) (W : unitaryGroup I ℂ)
    (ρ : Mat I) (hρ : ρ.PosSemidef) (htr : ρ.trace=1) (t : ℝ) (z : ℂ) (hz : ‖z‖=1) :
    let B := H.2.isHermitian.eigenvectorUnitary
    let V := B⁻¹*W*B
    let φ i := Complex.exp (-(Complex.I*((t:ℂ)*(H.2.isHermitian.eigenvalues i:ℂ))))
    2-2*‖∑ i, weight ρ V.val i*φ i‖ ≤ ‖z • unitaryEvolution H.val t-W.val‖^2 := by
  intro B V φ
  have hu i : ‖φ i‖=1 := by simp [φ,Complex.norm_exp,Complex.mul_re,Complex.mul_im]
  have hv : W.val=B.val*V.val*star B.val := by
    have h : B*V*B⁻¹=W := by simp only [V,mul_inv_cancel_left,mul_inv_cancel_right]
    exact (congrArg Subtype.val h).symm
  have he : ‖z • unitaryEvolution H.val t-W.val‖ = ‖diagonal (z • φ)-V.val‖ := by
    rw [unitaryEvolution_spectral H.2.isHermitian,hv,Matrix.diagonal_smul]
    change ‖z • (B.val*diagonal φ*star B.val)-_‖=_
    rw [←Matrix.smul_mul,←Matrix.mul_smul,←Matrix.sub_mul,←Matrix.mul_sub,l2_opNorm_unitary_conj_eq B.property]
  rw [he]
  have hb := packet_bound V ρ hρ htr (z • φ) (fun i => by change ‖z*φ i‖=1; rw [norm_mul,hz,hu,mul_one])
  have hs : (∑ i, weight ρ V.val i*(z • φ) i)=z*∑ i, weight ρ V.val i*φ i := by
    rw [mul_sum]
    exact sum_congr rfl fun i _ => by change _*(z*φ i)=z*(_*φ i); ring
  rw [hs] at hb
  have hr := Complex.re_le_norm (z*∑ i, weight ρ V.val i*φ i)
  rw [norm_mul,hz,one_mul] at hr
  linarith only [hr,hb]

#print axioms physical_packet
end
end GaloisForLFunctions.HTGeometry.SpectralApproximation.DensityWitnesses
