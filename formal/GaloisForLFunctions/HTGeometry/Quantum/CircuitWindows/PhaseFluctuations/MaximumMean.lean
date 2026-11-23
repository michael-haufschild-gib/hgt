import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseFluctuations.HaarGateCount
import GaloisForLFunctions.HTGeometry.Quantum.AttainedOrbitCircuitMaximum
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.OrbitMaximumAtError
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Phase maxima bounded by the sum of two Haar means -/
open Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseFluctuations
noncomputable section
private abbrev Config (n : ℕ) := Fin n → Bool
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩

private theorem phase_mul {n d : ℕ} (e : Config n ≃ Fin (d+1))
    (V : unitaryGroup (Config n) ℂ) (x y : Fin d → UnitAddCircle) :
    projectiveSpectralMatrix e V x * projectiveSpectralMatrix e V y =
      projectiveSpectralMatrix e V (x+y) := by
  let p (x : Fin d → UnitAddCircle) (i : Config n) :=
    fourier 1 (RHTower.zeroAnchoredPhase d x (e i))
  have ha (i : Fin (d+1)) : RHTower.zeroAnchoredPhase d (x+y) i =
      RHTower.zeroAnchoredPhase d x i+RHTower.zeroAnchoredPhase d y i := by
    exact Fin.cases (zero_add _).symm (fun _ => rfl) i
  have hp : (fun i => p x i*p y i)=p (x+y) := by
    funext i
    simp only [p,ha,fourier_one,AddCircle.toCircle_add,Circle.coe_mul]
  change (V.val*diagonal (p x)*star V.val)*(V.val*diagonal (p y)*star V.val)=_
  calc _ = V.val*(diagonal (p x)*(star V.val*V.val)*diagonal (p y))*star V.val := by
         simp only [mul_assoc]
       _ = _ := by rw [V.property.1,mul_one,diagonal_mul_diagonal,hp]; rfl

/-- Split any target phase into a uniform phase and its reflection.
Both factors have Haar law, and their circuit errors add. -/
theorem phaseCost_le_sum_means {n d : ℕ} (hn : 2 ≤ n) (e : Config n ≃ Fin (d+1))
    (V : unitaryGroup (Config n) ℂ) {ε δ : ℝ} (hε : 0≤ε) (hδ : 0≤δ)
    (z : Fin d → UnitAddCircle) :
    (phaseCost hn e V (add_nonneg hε hδ) z:ℝ) ≤ meanCost hn e V hε+meanCost hn e V hδ := by
  let f (x : Fin d → UnitAddCircle) : ℝ := phaseCost hn e V hε x
  let g (x : Fin d → UnitAddCircle) : ℝ := phaseCost hn e V hδ x
  let c : ℝ := phaseCost hn e V (add_nonneg hε hδ) z
  have hs (x : Fin d → UnitAddCircle) : c ≤ f x+g (z-x) := by
    let y := z-x
    have hU : projectiveSpectralMatrix e V y ∈ unitary (DiagonalSynthesis.Register n) :=
      mul_mem (mul_mem V.property (StaticLocalLaboratoryComplexityGrowthLaw.mem_unitaryGroup_diagonal_general _
        (fun _ => by rw [fourier_apply,Circle.norm_coe]))) (V⁻¹).property
    have h := LocalPatches.approx_product hU ((phaseCost_le hn e V hε x).mp le_rfl)
      ((phaseCost_le hn e V hδ y).mp le_rfl)
    rw [phase_mul,show x+y=z by dsimp only [y]; abel] at h
    change (phaseCost hn e V (add_nonneg hε hδ) z:ℝ) ≤
      (phaseCost hn e V hε x:ℝ)+(phaseCost hn e V hδ y:ℝ)
    exact_mod_cast (phaseCost_le hn e V (add_nonneg hε hδ) z).mpr h
  have hf : Integrable f volume := integrable_phaseCost hn e V hε
  have hg : Integrable g volume := integrable_phaseCost hn e V hδ
  letI : (volume : Measure (Fin d → UnitAddCircle)).IsNegInvariant :=
    ⟨(volume_preserving_pi (fun _ : Fin d => volume.measurePreserving_neg (G:=UnitAddCircle))).map_eq⟩
  have hT := volume.measurePreserving_sub_left z
  have hr : Integrable (fun x => g (z-x)) volume := hT.integrable_comp_of_integrable hg
  have h := integral_mono (μ:=volume) (integrable_const c) (hf.add hr) hs
  change (∫ _ : Fin d → UnitAddCircle, c) ≤ ∫ x, f x+g (z-x) at h
  rwa [integral_const,probReal_univ,one_smul,integral_add hf hr,integral_sub_left_eq_self] at h

/-- The actual recurrent orbit maximum at the sum of the two errors
cannot exceed the sum of the corresponding means on its eigenbasis. -/
theorem orbitMaximum_le_sum_means {n d : ℕ} (hn : 2 ≤ n) (e : Config n ≃ Fin (d+1))
    (H : selfAdjoint (DiagonalSynthesis.Register n)) {m : ℕ} {ε δ : ℝ}
    (hε : 0≤ε) (hδ : 0≤δ) (hm : IsRecurrentOrbitCircuitMaximumAt H (ε+δ) m) :
    let V := hermitianEigenbasisUnitary H.2.isHermitian
    (m:ℝ) ≤ meanCost hn e V hε+meanCost hn e V hδ := by
  intro V
  obtain ⟨_,w,_,hw,hvisit⟩ := hm.2
  obtain ⟨t,_,ht⟩ := hvisit 0
  let x := RHTower.projectivePhysicalPhaseFlow (fun i => H.2.isHermitian.eigenvalues (e.symm i)) t
  let s := phaseCost hn e V (add_nonneg hε hδ) x
  have hs := (physical_circuit_approximation_iff_spectral_capture e H s (ε+δ) t).mpr
    ((mem_projectiveContinuousCircuitCaptureTarget_iff e V s (ε+δ) x).mpr
      ((phaseCost_le hn e V (add_nonneg hε hδ) x).mp le_rfl))
  obtain ⟨z,hz,C,hC,hfit⟩ := hs
  exact (Nat.cast_le.mpr ((ht t ⟨le_rfl,le_add_of_nonneg_right hw.le⟩ z hz C hfit).trans hC)).trans
    (phaseCost_le_sum_means hn e V hε hδ x)

#print axioms orbitMaximum_le_sum_means
end
end GaloisForLFunctions.HTGeometry.PhaseFluctuations
