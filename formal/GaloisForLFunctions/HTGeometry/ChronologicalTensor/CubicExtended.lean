import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicFlow

/-!
# The forced six-coordinate observation space

Three concrete triangular probes prove independence of the three decaying
coordinates. Ring probes separate the remaining coordinates. The extended
six-coordinate readout is faithful and closed under the retraction flow;
the added cubic mode cannot be any original pairing observation.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set

def cubicExtendedReadout (A B C D E F : ℝ) (g : Fin 5 → ℝ) : ℝ :=
  cubicReadout A B C D E g+F*(g 2)^3

def cubicDecayWitness : Fin 3 → (Fin 5 → ℝ) :=
  ![![1/4,0,1/2,0,1/4],![1/2,0,1/2,0,0],![0,0,1,0,0]]

theorem cubicDecayWitness_mem (j : Fin 3) : cubicDecayWitness j ∈ cubicProbeSection := by
  fin_cases j
  all_goals refine ⟨?_,?_,?_,?_,?_,?_⟩
  all_goals first
    | (intro q; fin_cases q <;> simp [cubicDecayWitness])
    | (simp [cubicDecayWitness] <;> ring)

theorem cubicDecayWitness_readout (A E F : ℝ) :
    (fun j => cubicDecayReadout A E F (cubicDecayWitness j))=
      ![A/32+E/4+F/8,E/4+F/8,E+F] := by
  funext j
  fin_cases j <;> simp [cubicDecayReadout,cubicDecayWitness] <;> ring

theorem cubicDecayReadout_kernel (A E F : ℝ) :
    EqOn (cubicDecayReadout A E F) (fun _ => 0) cubicProbeSection ↔ A=0 ∧ E=0 ∧ F=0 := by
  constructor
  · intro h
    have h0 := h (cubicDecayWitness_mem 0)
    have h1 := h (cubicDecayWitness_mem 1)
    have h2 := h (cubicDecayWitness_mem 2)
    have hv := cubicDecayWitness_readout A E F
    have hv0 := congrFun hv 0
    have hv1 := congrFun hv 1
    have hv2 := congrFun hv 2
    change cubicDecayReadout A E F (cubicDecayWitness 0)=0 at h0
    change cubicDecayReadout A E F (cubicDecayWitness 1)=0 at h1
    change cubicDecayReadout A E F (cubicDecayWitness 2)=0 at h2
    change cubicDecayReadout A E F (cubicDecayWitness 0)=A/32+E/4+F/8 at hv0
    change cubicDecayReadout A E F (cubicDecayWitness 1)=E/4+F/8 at hv1
    change cubicDecayReadout A E F (cubicDecayWitness 2)=E+F at hv2
    exact ⟨by linarith,by linarith,by linarith⟩
  · rintro ⟨rfl,rfl,rfl⟩
    intro g _
    simp [cubicDecayReadout]

theorem cubicExtendedReadout_split (A B C D E F : ℝ) :
    EqOn (cubicExtendedReadout A B C D E F)
      (fun g => cubicReadout 0 B C D 0 g+cubicDecayReadout A E F g) cubicProbeSection := by
  intro g hg
  dsimp only
  unfold cubicExtendedReadout
  rw [cubicReadout_split,cubicDecayReadout_pairing A E hg]
  simp [cubicDecayReadout]
  ring

theorem cubicExtendedReadout_kernel (A B C D E F : ℝ) :
    EqOn (cubicExtendedReadout A B C D E F) (fun _ => 0) cubicProbeSection ↔
      A=0 ∧ B=0 ∧ C=0 ∧ D=0 ∧ E=0 ∧ F=0 := by
  constructor
  · intro h
    have hr : EqOn (cubicReadout A B C D E) (fun _ => 0) cubicRingSection := by
      intro g hg
      have he := h hg.1
      simpa [cubicExtendedReadout,hg.2] using he
    rcases (cubicRing_readout_kernel A B C D E).mp hr with ⟨hB,hC,hD⟩
    have hd : EqOn (cubicDecayReadout A E F) (fun _ => 0) cubicProbeSection := by
      intro g hg
      have he := h hg
      change cubicExtendedReadout A B C D E F g=0 at he
      rw [cubicExtendedReadout_split A B C D E F hg] at he
      simpa [cubicReadout,hB,hC,hD] using he
    rcases (cubicDecayReadout_kernel A E F).mp hd with ⟨hA,hE,hF⟩
    exact ⟨hA,hB,hC,hD,hE,hF⟩
  · rintro ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩
    intro g _
    simp [cubicExtendedReadout,cubicReadout]

theorem cubicExtendedReadout_flow (q : Icc (0:ℝ) 1) (A B C D E F : ℝ) :
    EqOn (fun g => cubicExtendedReadout A B C D E F (cubicFlow q g))
      (cubicExtendedReadout (q.val*A) B C D (q.val^2*E+q.val*(1-q.val)*A/2)
        (q.val^3*F-q.val*(1-q.val^2)*A/4)) cubicProbeSection := by
  intro g hg
  dsimp only
  rw [cubicExtendedReadout_split A B C D E F (cubicFlow_preserves q q.property hg)]
  dsimp only
  have hr := cubicFlow_retained q B C D hg
  have hd := cubicDecayReadout_flow q A E F hg
  dsimp only at hr hd
  rw [hr,hd]
  exact (cubicExtendedReadout_split _ B C D _ _ hg).symm

theorem cubicDecayMode_not_pairing :
    ¬ ∃ A B C D E : ℝ,
      EqOn (cubicDecayMode 2) (cubicReadout A B C D E) cubicProbeSection := by
  rintro ⟨A,B,C,D,E,h⟩
  have hz : EqOn (cubicExtendedReadout A B C D E (-1)) (fun _ => 0) cubicProbeSection := by
    intro g hg
    have he := h hg
    change (g 2)^3=cubicReadout A B C D E g at he
    simp [cubicExtendedReadout,← he]
  have hfalse := ((cubicExtendedReadout_kernel A B C D E (-1)).mp hz).2.2.2.2.2
  linarith

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
