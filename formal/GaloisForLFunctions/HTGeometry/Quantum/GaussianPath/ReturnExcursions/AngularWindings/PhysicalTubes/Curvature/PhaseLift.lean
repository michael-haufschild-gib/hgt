import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.PhysicalTubes.Components

/-! # Improving the fitting scalar preserves the relative winding at a fixed date -/

open Matrix Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
open SharpOccupation
open private column turn_lift from
  GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.PhysicalTubes.CoordinateLift
open private unique_index from
  GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.PhysicalTubes.Components
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- If two phases fit at the same date, their integer lifts differ by one
common integer. Hence a stricter fit realizes its actual error in the
original winding, including its original coordinate bounds. -/
theorem improve_phase_in_word (W : unitary (Mat I)) (A : I → ℝ) (m : I → ℤ) {t ε η : ℝ}
    (he : ε∈Ioo (0:ℝ) (sqrt 2)) (hle : η≤ε)
    (hm : t∈wordDates W A (circuitTurns W) m (physicalArc ε) ε)
    (hfit : t∈circuitDates W A η) : t∈wordDates W A (circuitTurns W) m (physicalArc ε) η := by
  obtain ⟨p,hp,_⟩ := hm
  obtain ⟨q,hq⟩ := hfit
  let d := circuitTurns W
  let x := physicalArc ε
  let n (i : I) := round (t*A i-q-d i)
  have hn (i : I) : |t*A i-(d i+(n i:ℝ))-q|≤x/2 := by
    rw [show t*A i-(d i+(n i:ℝ))-q=t*A i-q-d i-(n i:ℝ) by ring]
    exact turn_lift (t*A i-q) (d i) he (column W _ he.2 (hq.trans hle) i)
  have hnear (i : I) : |(q-p)-((m i-n i:ℤ):ℝ)|≤x := by
    rw [Int.cast_sub]
    obtain ⟨h₁,h₂⟩ := abs_le.mp (hp i)
    obtain ⟨h₃,h₄⟩ := abs_le.mp (hn i)
    change -(x/2)≤t*A i-(d i+(m i:ℝ))-p at h₁
    change t*A i-(d i+(m i:ℝ))-p≤x/2 at h₂
    exact abs_le.mpr ⟨by linarith only [h₁,h₄],by linarith only [h₂,h₃]⟩
  let j := Classical.arbitrary I
  let l := m j-n j
  have hl (i : I) : m i-n i=l := unique_index (physicalArc_spec he.1 he.2).1.2 (hnear i) (hnear j)
  have hreal (i : I) : (m i:ℝ)-(n i:ℝ)=(l:ℝ) := by exact_mod_cast hl i
  refine ⟨q-(l:ℝ),fun i => ?_,?_⟩
  · change |t*A i-(d i+(m i:ℝ))-(q-(l:ℝ))|≤x/2
    rw [show t*A i-(d i+(m i:ℝ))-(q-(l:ℝ))=t*A i-(d i+(n i:ℝ))-q by linarith only [hreal i]]
    exact hn i
  · have hangle (i : I) : t*A i-(m i:ℝ)-(q-(l:ℝ))=t*A i-(n i:ℝ)-q := by linarith only [hreal i]
    simp only [hangle,packet_lift]
    exact hq

#print axioms improve_phase_in_word
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
