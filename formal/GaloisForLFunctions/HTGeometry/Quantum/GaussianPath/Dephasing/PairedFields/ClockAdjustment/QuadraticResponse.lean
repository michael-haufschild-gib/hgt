import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.ClockAdjustment.Retiming

/-! # A quadratic energy observable after an arbitrary change of clock -/

open Matrix Finset
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.ClockAdjustment
open SpectralEdge FirstGate.ResponseWeights
noncomputable section

/-- Unnormalized trace of the square of the physical Hamiltonian against one Pauli. -/
def squareTrace {n : ℕ} (h : Coeff n) (p : PathLabel n) : ℝ :=
  (((generator h).val ^ 2 * finitePauliMatrix (pathWord p)).trace).re

/-- The second energy moment measures a quadratic polynomial in the original couplings. -/
theorem squareTrace_eq_energy_sum {n : ℕ} (h : Coeff n) (p : PathLabel n) :
    let E := (generator h).2.isHermitian.eigenvalues
    squareTrace h p = ∑ j, E j^2*localMean (WithLp.toLp 2 h) p j := by
  intro E
  let A := (generator h).val
  let V : Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ := (generator h).2.isHermitian.eigenvectorUnitary
  let D := diagonal (fun j => (E j:ℂ))
  let P := finitePauliMatrix (pathWord p)
  have hV : star V*V=1 := (Unitary.mem_iff.mp (generator h).2.isHermitian.eigenvectorUnitary.2).1
  have hs : A=V*D*star V := isHermitian_eq_conj_diagonal (generator h).2.isHermitian
  have hsq : A^2=V*(D*D)*star V := by
    rw [sq,hs]
    calc
      _ = V*D*(star V*V)*D*star V := by simp only [mul_assoc]
      _ = _ := by rw [hV,mul_one]; simp only [mul_assoc]
  have ht : (A^2*P).trace=((D*D)*(star V*P*V)).trace := by
    rw [hsq]
    calc
      _ = (V*((D*D)*(star V*P))).trace := by simp only [mul_assoc]
      _ = (((D*D)*(star V*P))*V).trace := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [mul_assoc]
  change (A^2*P).trace.re=_
  rw [ht]
  simp only [D,Matrix.diagonal_mul_diagonal,Matrix.trace,Matrix.diag_apply,Matrix.diagonal_mul,
    Complex.re_sum,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,mul_zero,add_zero,sub_zero,localMean,V,P,sq]
  rfl

/-- Rotating a pair of local coefficients differentiates along a sphere of fixed energy variance. -/
def pairField {n : ℕ} (h : Coeff n) (p q : PathLabel n) : Coeff n :=
  fun i => (if i=q then h p else 0)-(if i=p then h q else 0)

private theorem pair_test {n : ℕ} (h v : Coeff n) (p q : PathLabel n) :
    (∑ i, pairField h p q i*v i)=h p*v q-h q*v p := by
  simp [pairField,sub_mul,ite_mul,sum_sub_distrib]

/-- The trace determinant gives a lower bound on the squared response of a physical field
rotation, uniform over every correction to the observation time and the global phase. -/
theorem retimed_pair_response {n : ℕ} (h : Coeff n) (p q : PathLabel n) (t φ : ℝ) :
    let E := (generator h).2.isHermitian.eigenvalues
    let g := pairField h p q
    (h p*squareTrace h q-h q*squareTrace h p)^2 ≤
      (∑ j, E j^4)*(∑ j, (localSlope h g j+t*E j+φ)^2) := by
  intro E g
  have hperp : (∑ i, h i*g i)=0 := by
    simp_rw [mul_comm (h _) (g _)]
    rw [pair_test, mul_comm (h p) (h q),sub_self]
  have hret := optimal_retiming h g t φ
  dsimp only at hret
  simp only [hperp,zero_div,zero_mul,sub_zero,add_zero] at hret
  have hnon : 0 ≤ (2:ℝ)^(n+2)*((∑ l, h l^2)*t^2+φ^2) := by positivity
  have hres : (∑ j, localSlope h g j^2) ≤ ∑ j, (localSlope h g j+t*E j+φ)^2 := by
    rw [hret]
    exact le_add_of_nonneg_right hnon
  have hmoment : (∑ j, E j^2*localSlope h g j)=h p*squareTrace h q-h q*squareTrace h p := by
    simp_rw [show ∀ j, localSlope h g j=h p*localMean (WithLp.toLp 2 h) q j-
      h q*localMean (WithLp.toLp 2 h) p j from fun j => pair_test h _ p q,mul_sub,sum_sub_distrib]
    rw [squareTrace_eq_energy_sum,squareTrace_eq_energy_sum,mul_sum,mul_sum]
    exact congrArg₂ (·-·) (sum_congr rfl fun j _ => by ring) (sum_congr rfl fun j _ => by ring)
  rw [←hmoment]
  have hcs := sum_mul_sq_le_sq_mul_sq univ (fun j => E j^2) (localSlope h g)
  simp_rw [show ∀ j, (E j^2)^2=E j^4 from fun j => by ring] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_left hres (sum_nonneg fun j _ => by positivity))

#print axioms retimed_pair_response
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.ClockAdjustment
