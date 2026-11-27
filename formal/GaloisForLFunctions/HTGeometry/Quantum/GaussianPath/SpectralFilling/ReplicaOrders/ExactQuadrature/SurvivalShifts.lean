import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.ExactQuadrature.ShiftTests
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.ExactQuadrature.ReplicaMoment

/-! # One survival observable characterizes exact replica quadrature -/
open Finset
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
noncomputable section
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]

/-- It suffices to calibrate all translates of the survival fidelity
with a single strictly positive spectral weight. This forces every
individual occupation-energy difference to be integrated exactly. -/
theorem survival_shifts_iff (w E : I → ℝ) (hw : ∀ i, 0<w i) (q : ℕ) (p t : J → ℝ) :
    (∀ u, ∑ j, (p j:ℂ)*twistedFiniteSpectralFidelity w E (fun _ => 1) (u+t j)^q=
      average (frequencies E q).toList (fun s => twistedFiniteSpectralFidelity w E (fun _ => 1) s^q) 0) ↔
    ∀ l∈univ.piAntidiag q, ∀ k∈univ.piAntidiag q,
      ∑ j, (p j:ℂ)*wave (replicaMultiplicityEnergy E l-replicaMultiplicityEnergy E k) (t j)=
        if replicaMultiplicityEnergy E l=replicaMultiplicityEnergy E k then 1 else 0 := by
  classical
  let S := (univ : Finset I).piAntidiag q
  let d (x : (I → ℕ)×(I → ℕ)) := replicaMultiplicityEnergy E x.1-replicaMultiplicityEnergy E x.2
  let b (x : (I → ℕ)×(I → ℕ)) := fidelityReplicaMultiplicityWeight w x.1 x.2
  have hb (x) (_ : x∈S×ˢS) : 0<b x := fidelityReplicaMultiplicityWeight_pos hw _ _
  have twist (x y : I → ℕ) : replicaMultiplicityTwist (fun _ => 1) x y=1 := by
    simp [replicaMultiplicityTwist]
  have hex (s : ℝ) : polynomial (S×ˢS) d b s=twistedFiniteSpectralFidelity w E (fun _ => 1) s^q := by
    rw [polynomial,sum_product,twistedFiniteSpectralFidelity_pow_expansion]
    simp only [S,d,b,twist,mul_one,wave,mul_comm s]
  have mean : (∑ x∈S×ˢS, if d x=0 then (b x:ℂ) else 0)=
      average (frequencies E q).toList (fun s => twistedFiniteSpectralFidelity w E (fun _ => 1) s^q) 0 := by
    rw [sum_product,exact_replica_moment]
    simp only [S,d,sub_eq_zero,b,twist,mul_one]
  have h := shifted_clock_iff (S×ˢS) d b hb p t
  simp only [hex,mean] at h
  refine h.trans ⟨?_,?_⟩
  · intro hh l hl k hk
    simpa only [d,sub_eq_zero] using hh (l,k) (mem_product.mpr ⟨hl,hk⟩)
  · rintro hh ⟨l,k⟩ hmem
    simpa only [d,sub_eq_zero] using hh l (mem_product.mp hmem).1 k (mem_product.mp hmem).2

#print axioms survival_shifts_iff
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ExactQuadrature
