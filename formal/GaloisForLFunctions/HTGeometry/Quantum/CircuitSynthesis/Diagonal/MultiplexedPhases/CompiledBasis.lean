import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.MultiplexedPhases.Commuting

/-! # Uniform gate cap near a separated generator with a compiled basis -/
open Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.DiagonalSynthesis.MultiplexedPhases
open CommutatorBounds
noncomputable section

/-- A change of basis and its inverse cost 2q gates. Perturbation error
is measured in operator norm and is uniform over the entire evolution. -/
theorem compiled_basis_orbit {n q : ℕ} (hn : 2 ≤ n) (H : selfAdjoint (Register n))
    (V : unitaryGroup (Fin n→Bool) ℂ) (hcost : Realizes q (V : Register n)) (d : (Fin n→Bool)→ℝ)
    {g : ℝ} (hg : 0 < g) (hsep : ∀ i j, i≠j → g ≤ |d i-d j|) (t : ℝ) :
    let D := diagonal fun i => (d i:ℂ)
    HasProjectiveCircuitApproximation n (4*sqrt packConstant/g*‖H.val-(V : Register n)*D*star (V : Register n)‖)
      (q+2^n*3+q) (unitaryEvolution H.val t) := by
  intro D
  let W : Register n := V
  let U := unitaryEvolution H.val t
  let T (A : Register n) := star W*A*W
  have hW := Unitary.mem_iff.mp V.property
  have hw : star W∈unitary (Register n) := (V⁻¹).property
  have hprod (A B : Register n) : T A*T B=T (A*B) := by
    calc T A*T B = star W*(A*(W*star W)*B)*W := by simp only [T,mul_assoc]
         _ = T (A*B) := by rw [show W*star W=1 from hW.2,mul_one]
  have hU : T U ∈ unitary (Register n) := mul_mem (mul_mem hw (unitaryEvolution_mem_unitary H.property t)) V.property
  have hc : T H.val*T U=T U*T H.val := by
    rw [hprod,hprod,show H.val*U=U*H.val from unitaryEvolution_commutes_generator H.val t]
  obtain ⟨p,hp,_,herr⟩ := commuting_diagonal_approximation (T H.val) (T U) hU hc d hg hsep
  have hback (A B : Register n) : T (A-W*B*star W)=T A-B := by
    have h : T (W*B*star W)=B := calc
      _ = (star W*W)*B*(star W*W) := by simp only [T,mul_assoc]
      _ = B := by rw [show star W*W=1 from hW.1,one_mul,mul_one]
    exact (show T (A-W*B*star W)=T A-T (W*B*star W) by simp only [T,mul_sub,sub_mul]).trans
      (congrArg (T A-·) h)
  have hiso (A : Register n) : ‖T A‖=‖A‖ := by
    dsimp only [T]; rw [CStarRing.norm_mul_mem_unitary _ V.property,CStarRing.norm_mem_unitary_mul _ hw]
  have herr' : ‖U-W*diagonal p*star W‖ ≤ 4*sqrt packConstant/g*‖H.val-W*D*star W‖ := by
    rw [←hiso (U-_),←hiso (H.val-_),hback,hback]
    exact herr
  obtain ⟨z,hz,C,hC,hfit⟩ := (hcost.mul (full_register_phases hn p hp)).mul hcost.adjoint
  exact ⟨z,hz,C,hC,hfit ▸ herr'⟩

#print axioms compiled_basis_orbit
end
end GaloisForLFunctions.HTGeometry.DiagonalSynthesis.MultiplexedPhases
