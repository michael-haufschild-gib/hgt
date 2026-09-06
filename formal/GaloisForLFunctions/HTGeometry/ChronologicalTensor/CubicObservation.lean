import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicRetraction
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.SixPoint

/-!
# The exact observation loss of the cubic retraction

The five explicit cubic pairing readouts split into a retained three-coordinate
part and a lost two-coordinate part. The homotopy preserves the former and
its endpoint annihilates the latter. Three ring probes show that no further
linear readout is lost. The amplification seed lies entirely in the lost part.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set

def cubicReadout (A B C D E : ℝ) (g : Fin 5 → ℝ) : ℝ :=
  A*g 0*g 2*g 4+B*g 0*g 3*(g 2+g 3+g 4)+
  C*g 1*g 4*(g 0+g 1+g 2)+D*(g 0+g 1+g 2+g 3+g 4)*g 1*g 3+
  E*(g 0+g 1+g 2+g 3+g 4)*g 2*(g 1+g 2+g 3)

theorem cubicReadout_seed (g : Fin 5 → ℝ) :
    cubicReadout 27 0 0 0 1 g=sixResponse (g 0) (g 1) (g 2) (g 3) (g 4) := by
  unfold cubicReadout sixResponse separatedThree rainbowThree
  ring

theorem cubicCollapse_retained (t B C D : ℝ) :
    Set.EqOn (fun g => cubicReadout 0 B C D 0 (cubicCollapse t g))
      (cubicReadout 0 B C D 0) cubicProbeSection := by
  intro g hg
  change cubicReadout 0 B C D 0 (cubicCollapse t g)=cubicReadout 0 B C D 0 g
  by_cases h2 : g 2=0
  · rw [cubicCollapse_fixed t ⟨hg,h2⟩]
    rfl
  · have h1 : g 1=0 := (mul_eq_zero.mp hg.2.2.2.1).resolve_right h2
    have h3 : g 3=0 := (mul_eq_zero.mp hg.2.2.2.2.1).resolve_left h2
    simp [cubicReadout,cubicCollapse,h1,h3]

theorem cubicCollapse_lost (A E : ℝ) (g : Fin 5 → ℝ) :
    cubicReadout A 0 0 0 E (cubicCollapse 1 g)=0 := by
  simp [cubicReadout,cubicCollapse]

theorem cubicReadout_split (A B C D E : ℝ) (g : Fin 5 → ℝ) :
    cubicReadout A B C D E g=cubicReadout A 0 0 0 E g+cubicReadout 0 B C D 0 g := by
  unfold cubicReadout
  ring

theorem cubicCollapse_projection (A B C D E : ℝ) :
    Set.EqOn (fun g => cubicReadout A B C D E (cubicCollapse 1 g))
      (cubicReadout 0 B C D 0) cubicProbeSection := by
  intro g hg
  change cubicReadout A B C D E (cubicCollapse 1 g)=cubicReadout 0 B C D 0 g
  rw [cubicReadout_split,cubicCollapse_lost,zero_add]
  exact cubicCollapse_retained 1 B C D hg

theorem cubicCollapse_seed_zero (g : Fin 5 → ℝ) :
    sixResponse ((cubicCollapse 1 g) 0) ((cubicCollapse 1 g) 1)
      ((cubicCollapse 1 g) 2) ((cubicCollapse 1 g) 3) ((cubicCollapse 1 g) 4)=0 := by
  rw [← cubicReadout_seed]
  exact cubicCollapse_lost 27 1 g

def cubicRingWitness : Fin 3 → (Fin 5 → ℝ) :=
  ![![1/2,0,0,1/2,0],![0,1/2,0,0,1/2],![0,1/2,0,1/2,0]]

theorem cubicRingWitness_mem (j : Fin 3) : cubicRingWitness j ∈ cubicRingSection := by
  fin_cases j
  all_goals refine ⟨⟨?_,?_,?_,?_,?_,?_⟩,?_⟩
  all_goals first
    | (intro q; fin_cases q <;> simp [cubicRingWitness])
    | (change (1/2 : ℝ)+0+0+1/2+0=1; ring)
    | (change (0 : ℝ)+1/2+0+0+1/2=1; ring)
    | (change (0 : ℝ)+1/2+0+1/2+0=1; ring)
    | rfl
    | exact mul_zero _
    | exact zero_mul _

theorem cubicRingWitness_readout (A B C D E : ℝ) :
    (fun j => cubicReadout A B C D E (cubicRingWitness j))=![B/8,C/8,D/4] := by
  ext j
  fin_cases j
  all_goals simp [cubicReadout,cubicRingWitness]
  all_goals ring

theorem cubicRing_readout_kernel (A B C D E : ℝ) :
    Set.EqOn (cubicReadout A B C D E) (fun _ => 0) cubicRingSection ↔
      B=0 ∧ C=0 ∧ D=0 := by
  constructor
  · intro h
    have hB := h (cubicRingWitness_mem 0)
    have hC := h (cubicRingWitness_mem 1)
    have hD := h (cubicRingWitness_mem 2)
    have hval := cubicRingWitness_readout A B C D E
    have hb := congrFun hval 0
    have hc := congrFun hval 1
    have hd := congrFun hval 2
    change cubicReadout A B C D E (cubicRingWitness 0)=B/8 at hb
    change cubicReadout A B C D E (cubicRingWitness 1)=C/8 at hc
    change cubicReadout A B C D E (cubicRingWitness 2)=D/4 at hd
    exact ⟨by linarith only [hB,hb],by linarith only [hC,hc],by linarith only [hD,hd]⟩
  · rintro ⟨rfl,rfl,rfl⟩ g hg
    simp [cubicReadout,hg.2]

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
