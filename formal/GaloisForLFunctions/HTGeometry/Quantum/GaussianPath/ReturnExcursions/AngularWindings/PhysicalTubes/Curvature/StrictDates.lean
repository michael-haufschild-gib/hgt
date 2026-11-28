import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.PhysicalTubes.Curvature.StrictChart
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.AngularWindings.PhysicalTubes.Curvature.PhaseLift

/-! # A strict midpoint at distinct dates of a single physical winding -/

open Matrix Real Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
open SharpOccupation
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- On a simple physical spectrum, two distinct fitting dates on one winding
admit a strictly better fit of the same circuit at their midpoint. -/
theorem strict_winding_midpoint (W : unitary (Mat I)) (A : I → ℝ) (hA : Function.Injective A)
    (m : I → ℤ) {u v ε : ℝ} (huv : u≠v) (he : ε∈Ioo (0:ℝ) (sqrt 2)) :
    let x := physicalArc ε
    u∈wordDates W A (circuitTurns W) m x ε → v∈wordDates W A (circuitTurns W) m x ε →
      ∃ η∈Ico (0:ℝ) ε, (u+v)/2∈wordDates W A (circuitTurns W) m x η := by
  intro x hu hv
  obtain ⟨p,hp,h₀⟩ := hu
  obtain ⟨q,hq,h₁⟩ := hv
  let a (i : I) := 2*π*(u*A i-(m i:ℝ)-p)
  let b (i : I) := 2*π*(v*A i-(m i:ℝ)-q)
  let t := (u+v)/2
  have hx := (physicalArc_spec he.1 he.2).1.2.le
  have hcut : ε^2<2 := (pow_lt_pow_left₀ he.2 he.1.le (by decide : (2:ℕ)≠0)).trans_eq (sq_sqrt (by norm_num))
  have hspan (i : I) : |b i-a i|≤π := by
    have hl := abs_le.mp (hp i)
    have hr := abs_le.mp (hq i)
    have hh : |(v*A i-(m i:ℝ)-q)-(u*A i-(m i:ℝ)-p)|≤x :=
      abs_le.mpr ⟨by linarith only [hl.2,hr.1],by linarith only [hl.1,hr.2]⟩
    dsimp only [a,b]
    rw [←mul_sub,abs_mul,abs_of_pos two_pi_pos]
    linarith only [mul_le_mul_of_nonneg_left (hh.trans hx) two_pi_pos.le]
  have hfixed (i j : I) (hi : b i=a i) (hj : b j=a j) : i=j := by
    have hstrip (k : I) (hk : b k=a k) : (v-u)*A k=q-p := by
      have hh := mul_left_cancel₀ two_pi_pos.ne' hk
      linarith only [show v*A k-(m k:ℝ)-q=u*A k-(m k:ℝ)-p from hh]
    exact hA (mul_left_cancel₀ (sub_ne_zero.mpr huv.symm) ((hstrip i hi).trans (hstrip j hj).symm))
  obtain ⟨δ,hbetter⟩ := strict_angle_midpoint W a b he.1 hcut hspan hfixed h₀ h₁
  let P := (p+q)/2-δ/(2*π)
  have hangle (i : I) : (a i+b i)/2+δ=2*π*(t*A i-(m i:ℝ)-P) := by
    dsimp only [a,b,t,P]
    field_simp [pi_ne_zero]
    ring
  simp only [hangle,packet_lift] at hbetter
  let η := ‖(anglePacket fun i => 2*π*(t*A i-P)).val-W.val‖
  refine ⟨η,⟨norm_nonneg _,hbetter⟩,?_⟩
  apply improve_phase_in_word W A m he hbetter.le _ ⟨P,le_rfl⟩
  have h := wordDates_convex W A (circuitTurns W) m hx hcut
    (show u∈wordDates W A (circuitTurns W) m x ε from ⟨p,hp,h₀⟩)
    (show v∈wordDates W A (circuitTurns W) m x ε from ⟨q,hq,h₁⟩)
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (0:ℝ)≤1/2) (by norm_num)
  change (1/2:ℝ)*u+(1/2:ℝ)*v∈_ at h
  rwa [show (u+v)/2=(1/2:ℝ)*u+(1/2:ℝ)*v by ring]

#print axioms strict_winding_midpoint
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.AngularWindings.PhysicalTubes
