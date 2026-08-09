import GaloisForLFunctions.RHTower.BaezDuarteDistance

/-!
# The Mellin-vanishing criterion, as a template

The Nyman--Beurling chain built in `BaezDuarteL2Carrier` … `BaezDuarteDistance` uses one mechanism, and it
does not care that the generators are Báez-Duarte's.  All it needs is a family in the carrier whose Mellin
transforms vanish at the detector points attached to a hypothetical off-line zero, together with a target
whose transform does not.  This file isolates that mechanism so a new family — Beurling's dilations, a
Möbius-weighted system, a Balazard--Saias variant — can be plugged in without redoing the argument.

The single hypothesis `MellinAnnihilated G x` packages exactly the input: at every zero of `ζ` in the right
half of the critical strip, the detector kills every member of `G` and not `x`.  From it:

* `riemannHypothesis_of_mem_closedSpan_of_mellinAnnihilated` — closed-span membership forces RH;
* `dist_floor_of_mellinAnnihilated` — and if RH fails, a positive floor under every distance, so the
  approximation is obstructed rather than slow;
* `riemannHypothesis_of_infDist_eq_zero_of_mellinAnnihilated` — the same in metric form.

The Báez-Duarte family satisfies the hypothesis (`mellinAnnihilated_bdGen`), so the whole chain of that
lane is recovered as one instance.
-/

open MeasureTheory Set Complex Metric
open scoped InnerProductSpace

noncomputable section

namespace RHTower

/-- **The input of the criterion.**  At every zero of `ζ` with `½ < Re ρ < 1`, the Mellin detector at
`s = 1 − ρ` annihilates every generator and does not annihilate the target. -/
def MellinAnnihilated {I : Type*} (G : I → BDCarrier) (x : BDCarrier) : Prop :=
  ∀ ρ : ℂ, ∀ hρ : 1 / 2 < ρ.re, ρ.re < 1 → riemannZeta ρ = 0 →
    (∀ i, inner ℂ (bdDetector (one_sub_re_lt hρ)) (G i) = 0) ∧
      inner ℂ (bdDetector (one_sub_re_lt hρ)) x ≠ 0

/-- **The criterion.**  If the target lies in the closed span of a Mellin-annihilated family, the Riemann
hypothesis holds. -/
theorem riemannHypothesis_of_mem_closedSpan_of_mellinAnnihilated {I : Type*} (G : I → BDCarrier)
    (x : BDCarrier) (hGx : MellinAnnihilated G x)
    (h : x ∈ (Submodule.span ℂ (Set.range G)).topologicalClosure) : RiemannHypothesis := by
  by_contra hRH
  obtain ⟨ρ, hzero, hρ, hρ1⟩ := exists_zetaZero_re_gt_half_of_not_riemannHypothesis hRH
  obtain ⟨hann, hne⟩ := hGx ρ hρ hρ1 hzero
  exact hne (GaloisForLFunctions.HTGeometry.continuousLinearMap_eq_zero_on_closedSpan
    (innerSL ℂ (bdDetector (one_sub_re_lt hρ))) G hann h)

/-- **The floor.**  At a zero in the right half of the strip, every element of the closed span stays
`√(2Re ρ − 1)/|ρ|` away from the target — provided the target's own transform is the one the carrier
computes, `1/ρ`.  The general statement replaces that value by the transform of `x`. -/
theorem dist_floor_of_mellinAnnihilated {I : Type*} (G : I → BDCarrier) (x : BDCarrier)
    (hGx : MellinAnnihilated G x) {ρ : ℂ} (hρ : 1 / 2 < ρ.re) (hρ1 : ρ.re < 1)
    (hzero : riemannZeta ρ = 0) {y : BDCarrier}
    (hy : y ∈ (Submodule.span ℂ (Set.range G)).topologicalClosure) :
    ‖inner ℂ (bdDetector (one_sub_re_lt hρ)) x‖ * Real.sqrt (2 * ρ.re - 1) ≤ ‖x - y‖ := by
  obtain ⟨hann, _⟩ := hGx ρ hρ hρ1 hzero
  have hker : inner ℂ (bdDetector (one_sub_re_lt hρ)) y = 0 :=
    GaloisForLFunctions.HTGeometry.continuousLinearMap_eq_zero_on_closedSpan
      (innerSL ℂ (bdDetector (one_sub_re_lt hρ))) G hann hy
  have hkey := dist_innerKer_ge (bdDetector (one_sub_re_lt hρ)) x
    (bdDetector_ne_zero (one_sub_re_lt hρ)) hker
  have hpos : (0 : ℝ) < 2 * ρ.re - 1 := by linarith
  have hv : ‖bdDetector (one_sub_re_lt hρ)‖ = 1 / Real.sqrt (2 * ρ.re - 1) := by
    rw [norm_bdDetector (one_sub_re_lt hρ)]
    congr 2
    rw [Complex.sub_re, Complex.one_re]
    ring
  rw [hv] at hkey
  refine le_trans (le_of_eq ?_) hkey
  have hsne : Real.sqrt (2 * ρ.re - 1) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  field_simp

/-- The criterion in metric form. -/
theorem riemannHypothesis_of_infDist_eq_zero_of_mellinAnnihilated {I : Type*} (G : I → BDCarrier)
    (x : BDCarrier) (hGx : MellinAnnihilated G x)
    (h : Metric.infDist x ((Submodule.span ℂ (Set.range G) : Submodule ℂ BDCarrier) : Set BDCarrier)
      = 0) :
    RiemannHypothesis := by
  refine riemannHypothesis_of_mem_closedSpan_of_mellinAnnihilated G x hGx ?_
  have hne : ((Submodule.span ℂ (Set.range G) : Submodule ℂ BDCarrier) : Set BDCarrier).Nonempty :=
    ⟨0, Submodule.zero_mem _⟩
  have hmem : x ∈ closure ((Submodule.span ℂ (Set.range G) : Submodule ℂ BDCarrier) :
      Set BDCarrier) := (Metric.mem_closure_iff_infDist_zero hne).mpr h
  rwa [← Submodule.topologicalClosure_coe] at hmem

/-! ## The Báez-Duarte family is an instance -/

theorem mellinAnnihilated_bdGen {I : Type*} (θ : I → ℝ) (hθ : ∀ i, 0 < θ i ∧ θ i ≤ 1) :
    MellinAnnihilated (fun i => bdGen (θ i)) bdTarget := by
  intro ρ hρ hρ1 hzero
  refine ⟨fun i => ?_, ?_⟩
  · rw [inner_bdDetector_bdGen hρ hρ1 (hθ i).1 (hθ i).2, hzero]
    simp
  · rw [inner_bdDetector_bdTarget hρ]
    refine one_div_ne_zero ?_
    intro h
    rw [h, Complex.zero_re] at hρ
    linarith

/-- The Báez-Duarte criterion recovered from the template. -/
theorem riemannHypothesis_of_bdTarget_mem_closedSpan_template {I : Type*} (θ : I → ℝ)
    (hθ : ∀ i, 0 < θ i ∧ θ i ≤ 1)
    (h : bdTarget ∈
      (Submodule.span ℂ (Set.range (fun i : I => bdGen (θ i)))).topologicalClosure) :
    RiemannHypothesis :=
  riemannHypothesis_of_mem_closedSpan_of_mellinAnnihilated _ _ (mellinAnnihilated_bdGen θ hθ) h

end RHTower

end
