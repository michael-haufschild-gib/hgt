import GaloisForLFunctions.HTGeometry.SpectralObservedOrbitDimension
import GaloisForLFunctions.HTGeometry.UnitaryL2OperatorNorm
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! # A bounded Hermitian logarithm for every orbit time -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Wrap the eigenphases independently into angles of magnitude at most π.
The resulting Hermitian generator reproduces the propagator at time one,
uniformly over the original generator and elapsed time. -/
theorem exists_bounded_unit_time_generator {d : Type*} [Fintype d] [DecidableEq d]
    (H : selfAdjoint (Matrix d d ℂ)) (t : ℝ) :
    ∃ K : selfAdjoint (Matrix d d ℂ), ‖K.val‖ ≤ Real.pi ∧
      unitaryEvolution K.val 1 = unitaryEvolution H.val t := by
  classical
  cases isEmpty_or_nonempty d with
  | inl he =>
    letI := he
    exact ⟨0,by simpa using Real.pi_pos.le,Subsingleton.elim _ _⟩
  | inr hd =>
    letI := hd
    let V := H.2.isHermitian.eigenvectorUnitary
    let p (i : d) := Complex.exp (-(Complex.I*((t:ℂ)*(H.2.isHermitian.eigenvalues i:ℂ))))
    let θ (i : d) := -(p i).arg
    let D : Matrix d d ℂ := Matrix.diagonal (fun i => (θ i:ℂ))
    have hD : IsSelfAdjoint D := by
      change Dᴴ = D
      simp [D,Matrix.conjTranspose_diagonal]
    let K : Matrix d d ℂ := (V : Matrix d d ℂ)*D*star (V : Matrix d d ℂ)
    have hK : IsSelfAdjoint K := by
      change star ((V : Matrix d d ℂ)*D*star (V : Matrix d d ℂ)) = _
      rw [star_mul,star_mul,star_star,hD.star_eq,mul_assoc]
    refine ⟨⟨K,hK⟩,?_,?_⟩
    · change ‖(V : Matrix d d ℂ)*D*star (V : Matrix d d ℂ)‖ ≤ _
      rw [l2_opNorm_unitary_conj_eq V.2]
      change ‖Matrix.diagonal (fun i => (θ i:ℂ))‖ ≤ _
      rw [Matrix.l2_opNorm_diagonal]
      apply (pi_norm_le_iff_of_nonneg Real.pi_pos.le).mpr
      intro i
      simpa [θ] using Complex.abs_arg_le_pi (p i)
    · change unitaryEvolution ((V : Matrix d d ℂ)*Matrix.diagonal (fun i => (θ i:ℂ))*star (V : Matrix d d ℂ)) 1 = _
      rw [unitaryEvolution_conj_diagonal _ V.2,unitaryEvolution_spectral H.2.isHermitian]
      suffices he : (fun i => Complex.exp (-(Complex.I*((1:ℂ)*(θ i:ℂ))))) = p by rw [he]
      funext i
      have hp : ‖p i‖ = 1 := by simp [p,Complex.norm_exp]
      have h := Complex.norm_mul_exp_arg_mul_I (p i)
      rw [hp,Complex.ofReal_one,one_mul] at h
      convert h using 2
      simp [θ,mul_comm]

#print axioms exists_bounded_unit_time_generator
end
end GaloisForLFunctions.HTGeometry
