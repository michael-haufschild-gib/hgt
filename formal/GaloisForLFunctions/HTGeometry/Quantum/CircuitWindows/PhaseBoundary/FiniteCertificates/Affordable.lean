import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.Witnesses
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.VariableAccuracy.Affordable
import GaloisForLFunctions.HTGeometry.HaferkampContinuousCircuitImageCompactness

/-! # A finite certificate family for all gate layouts of bounded size -/

open Set Filter Topology Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates
noncomputable section

/-- Each fixed gate layout has finitely many projected certificates.
Taking their finite union covers every architecture of cost at most s. -/
theorem affordable_finite {A X : Type*} [CommRing A] [TopologicalSpace X] {ρ : X → A →+* ℝ}
    {N : ℕ} (hc : ∀ a, Continuous fun x => ρ x a) {U : X → Square (Bits N)} (hU : MatrixRep ρ U)
    (s : ℕ) (ε : X → ℝ) (hr : Represents ρ (fun x => ε x^2)) (hε : ∀ x, 0≤ε x) :
    FinitelyCertified ρ {x | HasProjectiveCircuitApproximation N (ε x) s (U x)} := by
  classical
  let J := (g : Fin (s+1)) × TwoQubitArchitecture N g.val
  letI : Fintype J := Fintype.ofFinite J
  let F (b : J) (e : Equation N b.1.val) (p : X × (Coord N b.1.val → ℝ)) :=
    residual b.2 (U p.1) (ε p.1) p.2 e
  have cert (b : J) := finite_complex_system ρ hc (F b) (VariableAccuracy.residual_rep b.2 hU hr)
  choose T hT using cert
  refine ⟨Finset.univ.biUnion T,?_⟩
  rintro x ⟨z,hz,C,hC,he⟩
  let b : J := ⟨⟨C.gateCount,Nat.lt_succ_of_le hC⟩,C.architecture⟩
  have hw : ∃ w, ∀ e, F b e (x,w)=0 :=
    (architecture_iff b.2 (U x) (hε x)).mp ⟨z,hz,C.gates,he⟩
  obtain ⟨p,hp,hzero,hlocal⟩ := hT b x hw
  refine ⟨p,Finset.mem_biUnion.mpr ⟨b,Finset.mem_univ b,hp⟩,hzero,?_⟩
  filter_upwards [hlocal] with y hy h
  obtain ⟨z',hz',G,hG⟩ := (architecture_iff b.2 (U y) (hε y)).mpr (hy h)
  exact ⟨z',hz',⟨C.gateCount,C.architecture,G⟩,hC,hG⟩

#print axioms affordable_finite
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates
