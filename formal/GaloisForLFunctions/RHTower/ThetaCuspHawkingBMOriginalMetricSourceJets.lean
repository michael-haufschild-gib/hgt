import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalMetricForcingMatch

open Set Filter Topology
open scoped ContDiff
namespace RHTower.D4BMOriginalMetricSourceJets
open GaloisForLFunctions.HTGeometry ScalarTwoJet
open D4BMJointSource D4BMJointWave D4BMModularCore D4BMOriginalCausalPotential D4BMAngularSeries
open D4BMOriginalAngularCurrent D4BMOriginalBaseCircleJets D4BMOriginalReaderCuspBounds
open D4BMOriginalPrincipalHorizonBounds D4BMOriginalContactCusp
noncomputable section
set_option autoImplicit false

private theorem coordinate_update {n : ℕ} (F : (Fin n → ℝ) → ℂ)
    (z : Fin n → ℝ) (i : Fin n) (hF : DifferentiableAt ℝ F z) :
    coordDeriv i F z=deriv (fun t => F (Function.update z i t)) (z i) := by
  have hF' : HasFDerivAt F (fderiv ℝ F z) (Function.update z i (z i)) := by
    simpa only [Function.update_eq_self] using hF.hasFDerivAt
  have h := hF'.comp_hasDerivAt (z i) (hasDerivAt_update z i (z i))
  simpa only [Function.update_eq_self,coordDeriv,Function.comp_def] using h.deriv.symm

private theorem first0 (F : (Fin 2 → ℝ) → ℂ) (hF : ContDiff ℝ ∞ F) (x k : ℝ) :
    coordDeriv 0 F ![x,k]=deriv (fun t => F ![t,k]) x := by
  have he (t : ℝ) : Function.update (![x,k] : Fin 2 → ℝ) 0 t=![t,k] := by
    ext i
    fin_cases i <;> simp
  simpa only [he,Matrix.cons_val] using
    coordinate_update F ![x,k] 0 (hF.contDiffAt.differentiableAt (by simp))

private theorem first1 (F : (Fin 2 → ℝ) → ℂ) (hF : ContDiff ℝ ∞ F) (x k : ℝ) :
    coordDeriv 1 F ![x,k]=deriv (fun t => F ![x,t]) k := by
  have he (t : ℝ) : Function.update (![x,k] : Fin 2 → ℝ) 1 t=![x,t] := by
    ext i
    fin_cases i <;> simp
  simpa only [he,Matrix.cons_val] using
    coordinate_update F ![x,k] 1 (hF.contDiffAt.differentiableAt (by simp))

/-- Canonical coordinate jets are the genuine ordinary base derivatives. -/
theorem coordinate_base_jets (F : (Fin 2 → ℝ) → ℂ) (hF : ContDiff ℝ ∞ F) (x k : ℝ) :
    D4BMSquareCuspJets.coordinateJet [1] F ![x,k]=baseOperator 1 (fun x k => F ![x,k]) x k ∧
    D4BMSquareCuspJets.coordinateJet [0,0] F ![x,k]=baseOperator 2 (fun x k => F ![x,k]) x k ∧
    D4BMSquareCuspJets.coordinateJet [1,1] F ![x,k]=baseOperator 3 (fun x k => F ![x,k]) x k := by
  have hD (i : Fin 2) : ContDiff ℝ ∞ (coordDeriv i F) :=
    contDiff_iff_contDiffAt.mpr (fun _ => coordDeriv_contDiffAt hF.contDiffAt (by simp) i)
  simp only [D4BMSquareCuspJets.coordinateJet,baseOperator,Matrix.cons_val]
  refine ⟨first1 F hF x k,?_,?_⟩
  · rw [first0 (coordDeriv 0 F) (hD 0)]
    simp_rw [first0 F hF]
  · rw [first1 (coordDeriv 1 F) (hD 1)]
    simp_rw [first1 F hF]

private theorem remainder_smooth (q : XiZeroCopy) (br : Bool) (amp : ℂ) (p v : ℝ) :
    ContDiff ℝ ∞ (D4BMOriginalCuspJets.remainder q br amp p v) := by
  have hF := (originalPotential_angular_smooth q br amp p v).comp
    (show ContDiff ℝ ∞ (fun z : Fin 2 → ℝ => (z 0,z 1)) by fun_prop)
  have hP : ContDiff ℝ ∞ (D4BMOriginalCuspJets.principal q br amp p v) := by
    unfold D4BMOriginalCuspJets.principal
    apply ContDiff.sum
    intro i _
    exact contDiff_const.mul ((contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
      (contDiff_apply ℝ ℝ (1:Fin 2)))).cexp)
  exact hF.sub hP

private theorem exp_normal_sum (a K : Fin 3 → ℂ) (k : ℝ) :
    Complex.exp (-(k:ℂ))*(∑ i : Fin 3,a i*Complex.exp (K i*(k:ℂ)))=
      ∑ i : Fin 3,a i*Complex.exp ((K i-1)*(k:ℂ)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_left_comm,← Complex.exp_add]
  congr 1
  ring

/-- Actual angular height derivative of the full causal source in base coordinates. -/
theorem source_normal_base (q : XiZeroCopy) (br : Bool) (amp : ℂ) (p L x k : ℝ) :
    coordDeriv 1 (D4BMOriginalAngularGreen.source q br amp p (p+L)) ![x,Real.exp k]=
      Complex.exp (-(k:ℂ))*baseOperator 1 (originalPotential q br amp p (p+L)) x k := by
  have hj := (coordinate_base_jets (D4BMOriginalCuspJets.remainder q br amp p (p+L))
    (remainder_smooth q br amp p (p+L)) x k).1
  change D4BMSquareCuspJets.coordinateJet [1] (D4BMOriginalCuspJets.remainder q br amp p (p+L)) ![x,k]=
    sourceJet q br amp 1 p L x k at hj
  have h := (D4BMOriginalCuspFlux.original_source_logarithmic_remainders q br amp p (p+L) x k).2.1
  dsimp only at h
  change coordDeriv 1 (D4BMOriginalAngularGreen.source q br amp p (p+L)) ![x,Real.exp k]=_ at h
  rw [hj] at h
  have hb := original_source_jet_expansion q br amp 1 p L x k
  simp only [jetMultiplier,Matrix.cons_val,D4BMOriginalPrincipalHorizonBounds.coefficient] at hb
  rw [h,hb,mul_add,exp_normal_sum]
  simp only [Fin.sum_univ_three]
  ring

/-- Actual angular Laplacian of the full source, retaining the horizontal weight. -/
theorem source_laplacian_base (q : XiZeroCopy) (br : Bool) (amp : ℂ) (p L x k : ℝ) :
    hyperbolicLaplacian (D4BMOriginalAngularGreen.source q br amp p (p+L)) ![x,Real.exp k]=
      Complex.exp (2*(k:ℂ))*baseOperator 2 (originalPotential q br amp p (p+L)) x k+
        baseOperator 3 (originalPotential q br amp p (p+L)) x k-
          baseOperator 1 (originalPotential q br amp p (p+L)) x k := by
  obtain ⟨h1,h00,h11⟩ := coordinate_base_jets (D4BMOriginalCuspJets.remainder q br amp p (p+L))
    (remainder_smooth q br amp p (p+L)) x k
  change D4BMSquareCuspJets.coordinateJet [1] (D4BMOriginalCuspJets.remainder q br amp p (p+L)) ![x,k]=
    sourceJet q br amp 1 p L x k at h1
  change D4BMSquareCuspJets.coordinateJet [0,0] (D4BMOriginalCuspJets.remainder q br amp p (p+L)) ![x,k]=
    sourceJet q br amp 2 p L x k at h00
  change D4BMSquareCuspJets.coordinateJet [1,1] (D4BMOriginalCuspJets.remainder q br amp p (p+L)) ![x,k]=
    sourceJet q br amp 3 p L x k at h11
  have h := (D4BMOriginalCuspFlux.original_source_logarithmic_remainders q br amp p (p+L) x k).2.2
  dsimp only at h
  change hyperbolicLaplacian (D4BMOriginalAngularGreen.source q br amp p (p+L)) ![x,Real.exp k]=_ at h
  rw [h1,h00,h11] at h
  rw [h,original_source_jet_expansion q br amp 2 p L x k,
    original_source_jet_expansion q br amp 3 p L x k,original_source_jet_expansion q br amp 1 p L x k]
  simp only [jetMultiplier,Matrix.cons_val,D4BMOriginalPrincipalHorizonBounds.coefficient,Fin.sum_univ_three]
  ring

/-- The full radius-reconstructed source and its two required angular operations. -/
theorem physical_source_operations (q : XiZeroCopy) (br : Bool) (amp : ℂ)
    (p L x k : ℝ) (hp : 0<p) (hL : 0<L) :
    let R := tortoiseRadius (-L/2)
    let U := originalPotential q br amp p (p+L)
    sourceScalar q br amp ![p,R,x,Real.exp k]=(R:ℂ)*baseOperator 0 U x k ∧
    coordDeriv 3 (sourceScalar q br amp) ![p,R,x,Real.exp k]=
      (R:ℂ)*Complex.exp (-(k:ℂ))*baseOperator 1 U x k ∧
    angularLap (sourceScalar q br amp) ![p,R,x,Real.exp k]=
      (R:ℂ)*(Complex.exp (2*(k:ℂ))*baseOperator 2 U x k+baseOperator 3 U x k-baseOperator 1 U x k) := by
  dsimp only
  let R := tortoiseRadius (-L/2)
  have hR : 1<R := tortoiseRadius_exterior (-L/2) (by linarith)
  have ht : D4BMIngoingCoordinates.tortoise R=-L/2 := tortoise_original_inverse (-L/2) (by linarith)
  have hv : p-2*D4BMIngoingCoordinates.tortoise R=p+L := by rw [ht];ring
  have hv0 : p-2*D4BMIngoingCoordinates.tortoise (tortoiseRadius (-L/2))=p+L := hv
  refine ⟨?_,?_,?_⟩
  · simp only [sourceScalar,D4BMActualIngoingCurrent.originalIngoingPotential,baseOperator,
      Matrix.cons_val,Real.log_exp,hv0]
  · have h := original_source_normal q br amp p R ![x,Real.exp k] hp hR (Real.exp_pos k)
    simp only [Matrix.cons_val,hv] at h
    rw [h,source_normal_base]
    ring
  · have h := source_angular_restriction q br amp p R ![x,Real.exp k] hp hR (Real.exp_pos k)
    simpa only [Matrix.cons_val,hv,source_laplacian_base] using h

end
end RHTower.D4BMOriginalMetricSourceJets
