import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.Architecture
import GaloisForLFunctions.HTGeometry.ProjectiveSpectralTorusContinuousCircuitHardnessLaw

/-! # Local polynomial certificates for physical circuit affordability -/
open Matrix Set Filter Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary
noncomputable section
variable {A X : Type*} [CommRing A] [TopologicalSpace X] {ρ : X → A →+* ℝ}

omit [TopologicalSpace X] in
private theorem residual_rep {N g : ℕ} (D : TwoQubitArchitecture N g) {U : X → Square (Bits N)}
    (hU : MatrixRep ρ U) {ε : ℝ} (hε : Represents ρ (fun _ => ε)) (e : Equation N g) :
    ComplexRep (witnessEval ρ) (fun z : X × (Coord N g → ℝ) => residual D (U z.1) ε z.2 e) := by
  let φ := @witnessEval A X (Coord N g) _ ρ
  have hvar (i : ComplexVars N g) : ComplexRep φ (fun z => readVar z.2 i) :=
    ⟨witness_coordinate ρ (i,false),witness_coordinate ρ (i,true)⟩
  have hp : ComplexRep φ (fun z => phaseVar z.2) := hvar (.inl ())
  have hg (k : Fin g) : MatrixRep φ (fun z => gateVar z.2 k) := fun i j => hvar (.inr (.inl (k,i,j)))
  have hb : MatrixRep φ (fun z => slackVar z.2) := fun i j => hvar (.inr (.inr (i,j)))
  rcases e with v|⟨k,v|⟨i,j⟩⟩|⟨i,j⟩
  · exact (hp.star.mul hp).sub ComplexRep.one
  · exact (hg k).det.sub ComplexRep.one
  · exact (((hg k).star.mul (hg k)).sub MatrixRep.one) i j
  · have hu : MatrixRep φ (fun z => U z.1) := fun i j => (hU i j).on_base
    have hM := hu.sub (MatrixRep.smul hp (rawWord_rep D hg))
    have hreal : ComplexRep φ (fun _ => ((ε:ℝ):ℂ)) := ⟨hε.on_base,Represents.zero⟩
    have hS : MatrixRep φ (fun _ => (ε^2) • (1 : Square (Bits N))) := by
      intro v w
      by_cases h : v=w
      · subst w
        simp only [Matrix.smul_apply,Matrix.one_apply_eq,Complex.real_smul,mul_one,sq,Complex.ofReal_mul]
        exact hreal.mul hreal
      · simp only [Matrix.smul_apply,Matrix.one_apply_ne h,smul_zero]
        exact ComplexRep.zero
    exact ((hS.sub (hM.star.mul hM)).sub (hb.star.mul hb)) i j

/-- Every affordable target has a local certificate for the same architecture.
The certificate also covers boundary budgets and zero tolerance. -/
theorem affordable_certified {N : ℕ} (hc : ∀ a, Continuous fun x => ρ x a)
    {U : X → Square (Bits N)} (hU : MatrixRep ρ U) (s : ℕ) (ε : ℝ)
    (hr : Represents ρ (fun _ => ε)) :
    LocallyCertified ρ {x | HasProjectiveCircuitApproximation N ε s (U x)} := by
  intro x hx
  obtain ⟨z,hz,C,hC,he⟩ := hx
  have hε := (norm_nonneg _).trans he
  let D := C.architecture
  let F := fun e (p : X × (Coord N C.gateCount → ℝ)) => residual D (U p.1) ε p.2 e
  have hw : ∃ w, ∀ e, F e (x,w) = 0 := (architecture_iff D (U x) hε).mp ⟨z,hz,C.gates,he⟩
  obtain ⟨a,ha,hlocal⟩ := certified_complex_system ρ hc F (residual_rep D hU hr) x hw
  refine ⟨a,ha,?_⟩
  filter_upwards [hlocal] with y hy h
  obtain ⟨z',hz',G,hG⟩ := (architecture_iff D (U y) hε).mpr (hy h)
  exact ⟨z',hz',⟨C.gateCount,D,G⟩,hC,hG⟩

end
end GaloisForLFunctions.HTGeometry.PhaseBoundary
