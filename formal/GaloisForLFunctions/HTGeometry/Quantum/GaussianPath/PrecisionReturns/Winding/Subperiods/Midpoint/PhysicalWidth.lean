import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.Subperiods.Midpoint.DividedArcs
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrecisionReturns.Winding.Subperiods.Midpoint.Width

/-! # Width of the physical spectrum at a subdivision of the first empty return -/

open Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.Subperiods.Midpoint
open EmptyVisitFlux SharpOccupation
noncomputable section

/-- A primitive winding at the return excludes short enclosing arcs
at every one-dth subdivision. For d=2 the two bounds meet at a semicircle
when the return error tends to zero. -/
theorem width_at_division {N : ℕ} (H : selfAdjoint (Register N)) {t r : ℝ}
    (hr : r∈Icc (0:ℝ) 1) {d : ℕ} (hd : 2≤d)
    {b : Fin N → Bool} {z : (Fin N → Bool) → ℤ}
    (h : Anchored (fun j => -H.2.isHermitian.eigenvalues j/(2*π)) t r b z)
    (hprimitive : ¬ ∀ j, (d:ℤ) ∣ z j) :
    turnWidth H (t/d) ∈ Icc ((1-r)/d) (((d:ℝ)-1+r)/d) := by
  have hd0 : 0<d := by omega
  have hpos := Nat.cast_pos (α:=ℝ).mpr hd0
  have hone : (1:ℝ)≤d := by exact_mod_cast (show 1≤d by omega)
  let v := t/(d:ℝ)
  let p := turnWidth H v
  let upper := ((d:ℝ)-1+r)/d
  have hu : upper∈Icc (0:ℝ) 1 :=
    ⟨div_nonneg (by linarith only [hone,hr.1]) hpos.le,(div_le_one hpos).mpr (by linarith only [hr.2])⟩
  have hp := turnWidth_range H v
  obtain ⟨c,y,hy⟩ := (anchored_iff hp.1).mp ((arc_iff_width H v ⟨p,hp.1,hp.2.le⟩).mpr le_rfl)
  constructor
  · apply (div_le_iff₀ hpos).mpr
    by_contra! hc
    apply hprimitive
    apply divisible_of_short_division h hd0 hy
    change (d:ℝ)*turnWidth H v+r<1
    change turnWidth H v*(d:ℝ)<1-r at hc
    rw [mul_comm]
    linarith only [hc]
  · apply (arc_iff_width H v ⟨upper,hu⟩).mp
    exact (anchored_iff hu.1).mpr ⟨b,_,divided_upper h hd0⟩

/-- The first actual return after a is primitive for every subdivision
once its absolute date is at least twice a. -/
theorem first_division_width {N : ℕ} (H : selfAdjoint (Register N)) {a ε : ℝ}
    (ha : 0<a) (hε : ε∈Ioo (0:ℝ) (sqrt 2)) (hv : 2*a≤firstVisit H a 0 ε) {d : ℕ} (hd : 2≤d) :
    turnWidth H (firstVisit H a 0 ε/d) ∈
      Icc ((1-physicalArc ε)/d) (((d:ℝ)-1+physicalArc ε)/d) := by
  obtain ⟨⟨b,z,hz⟩,h⟩ := first_winding_primitive H ha hε hv
  have hr := (physicalArc_spec hε.1 hε.2).1
  exact width_at_division H ⟨hr.1.le,hr.2.le.trans (by norm_num)⟩ hd hz (h b z hz d hd)

#print axioms first_division_width
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding.Subperiods.Midpoint
