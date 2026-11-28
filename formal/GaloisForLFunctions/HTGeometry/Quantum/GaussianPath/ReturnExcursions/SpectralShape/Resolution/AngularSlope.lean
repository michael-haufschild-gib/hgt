import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.Resolution.Coordinate
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.PhysicalSublevel

/-! # A resolved onsite slope of every proposed squared skewness -/

open Finset MeasureTheory Set WithLp
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
open Dephasing.PairedFields Dephasing.PairedFields.ClockAdjustment
noncomputable section

/-- Regularity involves only the physical fields. The bound for the cubic trace
and the adjacent rotation applies simultaneously to every proposed target. -/
def resolvedEdge {n : ℕ} (h : Coeff n) (e : Fin (n+1)) (r : ℝ) : Prop :=
  r^3/2≤|thirdMoment (toLp 2 h)| ∧
    2*(2:ℝ)^(n+2)*r^3≤|edgeResponse h e 0 0|

/-- The exceptional probability is uniform in the chosen edge and prefix size. -/
theorem gaussian_resolved_edge {n : ℕ} (e : Fin (n+1)) {r : ℝ} (hr : 0<r) :
    (fieldLaw n).real {h | ¬resolvedEdge h e r}≤18*r := by
  let A := {h : Coeff n | |skewConstraint 0 (toLp 2 h)|<(2/3)*r^6}
  let B := {h : Coeff n | |edgeResponse h e 0 0|<2*(2:ℝ)^(n+2)*r^3}
  have hsub : {h | ¬resolvedEdge h e r} ⊆ A ∪ B := by
    intro h hh
    by_cases hB : h∈B
    · exact Or.inr hB
    · have hm : |thirdMoment (toLp 2 h)|<r^3/2 :=
        lt_of_not_ge (fun hg => hh ⟨hg,le_of_not_gt hB⟩)
      left
      change |skewConstraint 0 (toLp 2 h)|<_
      simp only [skewConstraint,zero_mul,sub_zero,abs_of_nonneg (sq_nonneg (thirdMoment (toLp 2 h)))]
      have hs := pow_lt_pow_left₀ hm (abs_nonneg _) (by decide : (2:ℕ)≠0)
      rw [sq_abs] at hs
      nlinarith only [hs,pow_pos hr 6]
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans ((measureReal_union_le A B).trans
    ((add_le_add (physical_skew_price n 0 r hr) (gaussian_edge_response e 0 0 r hr)).trans_eq (by ring)))

/-- At least one of the two ordinary coordinate derivatives resolves the
constraint, uniformly in the target. Rotating the pair cancels its radial term. -/
theorem large_coordinate_slope {n : ℕ} (h : Coeff n) (e : Fin (n+1)) {r : ℝ}
    (hr : 0<r) (hreg : resolvedEdge h e r)
    (hV : ‖toLp 2 h‖^2≤13*((n+2:ℕ):ℝ)) (c : ℝ) :
    let B := 1+13*((n+2:ℕ):ℝ)
    r^6/B≤|shapeSlope c h (leftSite e 0)| ∨ r^6/B≤|shapeSlope c h (rightSite e 0)| := by
  intro B
  let p := leftSite e 0
  let q := rightSite e 0
  let D := (2:ℝ)^(n+2)
  let u := shapeSlope c h p
  let v := shapeSlope c h q
  have hB : 0<B := by dsimp only [B]; positivity
  have hD : 0<D := pow_pos (by norm_num) _
  have hfield (i) : |h i|≤B := by
    rw [EuclideanSpace.real_norm_sq_eq] at hV
    have hi : h i^2≤∑ j, h j^2 := single_le_sum (fun j _ => sq_nonneg (h j)) (mem_univ _)
    dsimp only [B]
    nlinarith only [hi.trans hV,sq_nonneg (|h i|-1),sq_abs (h i),abs_nonneg (h i)]
  have hlarge : 6*r^6≤|h p*v-h q*u| := by
    rw [show h p*v-h q*u=_ from rotation_slope c h e,abs_div,abs_of_pos hD,abs_mul,abs_mul,
      abs_of_pos (by norm_num : (0:ℝ)<6),le_div_iff₀ hD]
    have hh := mul_le_mul hreg.1 hreg.2 (by positivity) (abs_nonneg _)
    nlinarith only [hh]
  by_contra! hsmall
  obtain ⟨hp,hq⟩ := hsmall
  have h₁ := mul_le_mul (hfield p) hq.le (abs_nonneg _) hB.le
  have h₂ := mul_le_mul (hfield q) hp.le (abs_nonneg _) hB.le
  have htri := abs_sub (h p*v) (h q*u)
  rw [abs_mul,abs_mul] at htri
  rw [show B*(r^6/B)=r^6 by field_simp [hB.ne']] at h₁ h₂
  linarith only [hlarge,htri,h₁,h₂,pow_pos hr 6]

#print axioms gaussian_resolved_edge
#print axioms large_coordinate_slope
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
