import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicNormLaws

/-!
# The retraction semigroup and its decaying observations

The surviving middle-gap fraction is a multiplicative flow parameter. The
original lost pairing plane expands under intermediate pullback by a forced
cubic coordinate. Three explicit modes have weights 1, 2, and 3, obey the cusp
relation, and recover the new coordinate from a single half-flow observation.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set

def cubicFlow (q : ℝ) : (Fin 5 → ℝ) → (Fin 5 → ℝ) := cubicCollapse (1-q)

theorem cubicFlow_one (g : Fin 5 → ℝ) : cubicFlow 1 g=g := by
  simpa [cubicFlow] using cubicCollapse_zero g

theorem cubicFlow_zero (g : Fin 5 → ℝ) : cubicFlow 0 g=cubicCollapse 1 g := by
  simp [cubicFlow]

theorem cubicFlow_mul (q r : ℝ) (g : Fin 5 → ℝ) :
    cubicFlow q (cubicFlow r g)=cubicFlow (q*r) g := by
  ext i
  fin_cases i <;> simp [cubicFlow,cubicCollapse] <;> ring

theorem cubicFlow_preserves :
    ∀ q ∈ Icc (0:ℝ) 1, MapsTo (cubicFlow q) cubicProbeSection cubicProbeSection := by
  intro q hq
  apply cubicCollapse_preserves
  constructor <;> linarith [hq.1,hq.2]

theorem cubicFlow_retained (q B C D : ℝ) :
    EqOn (fun g => cubicReadout 0 B C D 0 (cubicFlow q g))
      (cubicReadout 0 B C D 0) cubicProbeSection :=
  cubicCollapse_retained (1-q) B C D

def cubicDecayReadout (A E F : ℝ) (g : Fin 5 → ℝ) : ℝ :=
  A*g 0*g 2*g 4+E*(g 2)^2+F*(g 2)^3

def cubicDecayMode : Fin 3 → (Fin 5 → ℝ) → ℝ :=
  ![fun g => g 2*(1-(g 0-g 4)^2)/4,fun g => (g 2)^2,fun g => (g 2)^3]

theorem cubicDecayReadout_pairing (A E : ℝ) :
    EqOn (cubicReadout A 0 0 0 E) (cubicDecayReadout A E 0) cubicProbeSection := by
  intro g hg
  by_cases hc : g 2=0
  · simp [cubicReadout,cubicDecayReadout,hc]
  have hb : g 1=0 := (mul_eq_zero.mp hg.2.2.2.1).resolve_right hc
  have hd : g 3=0 := (mul_eq_zero.mp hg.2.2.2.2.1).resolve_left hc
  unfold cubicReadout
  rw [hg.2.1]
  simp [cubicDecayReadout,hb,hd]
  ring

theorem cubicDecayReadout_flow (q A E F : ℝ) :
    EqOn (fun g => cubicDecayReadout A E F (cubicFlow q g))
      (cubicDecayReadout (q*A) (q^2*E+q*(1-q)*A/2)
        (q^3*F-q*(1-q^2)*A/4)) cubicProbeSection := by
  intro g hg
  change cubicDecayReadout A E F (cubicFlow q g)=_
  by_cases hc : g 2=0
  · simp [cubicDecayReadout,cubicFlow,cubicCollapse,hc]
  have hb : g 1=0 := (mul_eq_zero.mp hg.2.2.2.1).resolve_right hc
  have hd : g 3=0 := (mul_eq_zero.mp hg.2.2.2.2.1).resolve_left hc
  have hs : g 0+g 2+g 4=1 := by simpa [hb,hd] using hg.2.1
  simp [cubicDecayReadout,cubicFlow,cubicCollapse]
  linear_combination (A*q*(1-q)*(g 2)^2/2)*hs

theorem cubicDecayMode_spectrum (q : ℝ) (j : Fin 3) (g : Fin 5 → ℝ) :
    cubicDecayMode j (cubicFlow q g)=q^(j.val+1)*cubicDecayMode j g := by
  fin_cases j <;> simp [cubicDecayMode,cubicFlow,cubicCollapse] <;> ring

theorem cubicDecayMode_cusp (g : Fin 5 → ℝ) :
    (cubicDecayMode 2 g)^2=(cubicDecayMode 1 g)^3 := by
  simp [cubicDecayMode]
  ring

theorem cubicDecayReadout_spectral (A E F : ℝ) :
    EqOn (cubicDecayReadout A E F)
      (fun g => A*cubicDecayMode 0 g+(E-A/2)*cubicDecayMode 1 g+
        (F+A/4)*cubicDecayMode 2 g) cubicProbeSection := by
  intro g hg
  by_cases hc : g 2=0
  · simp [cubicDecayReadout,cubicDecayMode,hc]
  have hb : g 1=0 := (mul_eq_zero.mp hg.2.2.2.1).resolve_right hc
  have hd : g 3=0 := (mul_eq_zero.mp hg.2.2.2.2.1).resolve_left hc
  have hs : g 0+g 2+g 4=1 := by simpa [hb,hd] using hg.2.1
  have he : g 4=1-g 0-g 2 := by linarith
  simp [cubicDecayReadout,cubicDecayMode,he]
  ring

theorem cubicDecayReadout_recover_cubic :
    EqOn (cubicDecayMode 2)
      (fun g => (32/3)*((1/2)*cubicDecayReadout 1 0 0 g+
        (1/8)*cubicDecayMode 1 g-cubicDecayReadout 1 0 0 (cubicFlow (1/2) g)))
      cubicProbeSection := by
  intro g hg
  have h := cubicDecayReadout_flow (1/2) 1 0 0 hg
  change cubicDecayReadout 1 0 0 (cubicFlow (1/2) g)=_ at h
  dsimp only
  rw [h]
  simp [cubicDecayMode,cubicDecayReadout]
  ring

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
