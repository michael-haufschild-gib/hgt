import GaloisForLFunctions.RHTower.SmoothAFEZetaGeneral

/-!
# Dual synthesis forced by Gaussian-AFE self-recurrence

For two points in the open AFE strip, subtracting the exact Gaussian
approximate functional equations shows what the moving dual edge must do if
both the zeta value and the direct edge recur. When the moving pole residue
vanishes, the dual edge must approach the base dual edge plus the base pole
residue; making the moving dual term small is the wrong target.
-/

noncomputable section

namespace RHTower

open Complex Filter Topology

/-- Exact two-point balance forced by the general Gaussian AFE. -/
theorem smoothAFEZetaDualMellinGeneral_sub_base_add_residue_eq
    {x : ℝ} (hx : 0 < x) {s t : ℂ}
    (hs : s ≠ 1) (hs0 : 0 < s.re) (hs2 : s.re < 2)
    (ht : t ≠ 1) (ht0 : 0 < t.re) (ht2 : t.re < 2) :
    smoothAFEZetaDualMellinGeneral t x -
        (smoothAFEZetaDualMellinGeneral s x + smoothAFEZetaShiftedPoleResidue s x) =
      (smoothAFEZetaMellinAt 1 t x - smoothAFEZetaMellinAt 1 s x) -
        (riemannZeta t - riemannZeta s) - smoothAFEZetaShiftedPoleResidue t x := by
  have hbase :=
    riemannZeta_eq_smoothAFEZetaMellin_sub_dual_sub_residue_general hx hs hs0 hs2
  have hmove :=
    riemannZeta_eq_smoothAFEZetaMellin_sub_dual_sub_residue_general hx ht ht0 ht2
  rw [hbase, hmove]
  ring

/-- Quantitative form: direct-edge recurrence, zeta recurrence, and decay of
the moving pole residue force synthesis of the base dual-plus-pole target. -/
theorem norm_smoothAFEZetaDualMellinGeneral_sub_base_add_residue_le
    {x : ℝ} (hx : 0 < x) {s t : ℂ}
    (hs : s ≠ 1) (hs0 : 0 < s.re) (hs2 : s.re < 2)
    (ht : t ≠ 1) (ht0 : 0 < t.re) (ht2 : t.re < 2) :
    ‖smoothAFEZetaDualMellinGeneral t x -
        (smoothAFEZetaDualMellinGeneral s x + smoothAFEZetaShiftedPoleResidue s x)‖ ≤
      ‖smoothAFEZetaMellinAt 1 t x - smoothAFEZetaMellinAt 1 s x‖ +
        ‖riemannZeta t - riemannZeta s‖ + ‖smoothAFEZetaShiftedPoleResidue t x‖ := by
  rw [smoothAFEZetaDualMellinGeneral_sub_base_add_residue_eq hx hs hs0 hs2 ht ht0 ht2]
  calc
    ‖(smoothAFEZetaMellinAt 1 t x - smoothAFEZetaMellinAt 1 s x) -
          (riemannZeta t - riemannZeta s) - smoothAFEZetaShiftedPoleResidue t x‖
        ≤ ‖(smoothAFEZetaMellinAt 1 t x - smoothAFEZetaMellinAt 1 s x) -
            (riemannZeta t - riemannZeta s)‖ +
          ‖smoothAFEZetaShiftedPoleResidue t x‖ := norm_sub_le _ _
    _ ≤ (‖smoothAFEZetaMellinAt 1 t x - smoothAFEZetaMellinAt 1 s x‖ +
            ‖riemannZeta t - riemannZeta s‖) +
          ‖smoothAFEZetaShiftedPoleResidue t x‖ := by
      gcongr
      exact norm_sub_le _ _
    _ = _ := by ring

/-- Exact converse balance: recurrence of the direct edge and synthesis of the
base dual-plus-pole target leave only the moving pole residue in the zeta
difference. -/
theorem riemannZeta_sub_eq_smoothAFE_direct_sub_dualTarget_sub_pole
    {x : ℝ} (hx : 0 < x) {s t : ℂ}
    (hs : s ≠ 1) (hs0 : 0 < s.re) (hs2 : s.re < 2)
    (ht : t ≠ 1) (ht0 : 0 < t.re) (ht2 : t.re < 2) :
    riemannZeta t - riemannZeta s =
      (smoothAFEZetaMellinAt 1 t x - smoothAFEZetaMellinAt 1 s x) -
        (smoothAFEZetaDualMellinGeneral t x -
          (smoothAFEZetaDualMellinGeneral s x +
            smoothAFEZetaShiftedPoleResidue s x)) -
        smoothAFEZetaShiftedPoleResidue t x := by
  have hbase :=
    riemannZeta_eq_smoothAFEZetaMellin_sub_dual_sub_residue_general hx hs hs0 hs2
  have hmove :=
    riemannZeta_eq_smoothAFEZetaMellin_sub_dual_sub_residue_general hx ht ht0 ht2
  rw [hbase, hmove]
  ring

/-- Quantitative sufficiency: direct-edge recurrence, dual target synthesis,
and decay of the moving pole residue imply zeta recurrence. -/
theorem norm_riemannZeta_sub_le_direct_add_dualTarget_add_pole
    {x : ℝ} (hx : 0 < x) {s t : ℂ}
    (hs : s ≠ 1) (hs0 : 0 < s.re) (hs2 : s.re < 2)
    (ht : t ≠ 1) (ht0 : 0 < t.re) (ht2 : t.re < 2) :
    ‖riemannZeta t - riemannZeta s‖ ≤
      ‖smoothAFEZetaMellinAt 1 t x - smoothAFEZetaMellinAt 1 s x‖ +
        ‖smoothAFEZetaDualMellinGeneral t x -
          (smoothAFEZetaDualMellinGeneral s x +
            smoothAFEZetaShiftedPoleResidue s x)‖ +
        ‖smoothAFEZetaShiftedPoleResidue t x‖ := by
  rw [riemannZeta_sub_eq_smoothAFE_direct_sub_dualTarget_sub_pole
    hx hs hs0 hs2 ht ht0 ht2]
  calc
    ‖(smoothAFEZetaMellinAt 1 t x - smoothAFEZetaMellinAt 1 s x) -
          (smoothAFEZetaDualMellinGeneral t x -
            (smoothAFEZetaDualMellinGeneral s x +
              smoothAFEZetaShiftedPoleResidue s x)) -
          smoothAFEZetaShiftedPoleResidue t x‖
        ≤ ‖(smoothAFEZetaMellinAt 1 t x - smoothAFEZetaMellinAt 1 s x) -
            (smoothAFEZetaDualMellinGeneral t x -
              (smoothAFEZetaDualMellinGeneral s x +
                smoothAFEZetaShiftedPoleResidue s x))‖ +
          ‖smoothAFEZetaShiftedPoleResidue t x‖ := norm_sub_le _ _
    _ ≤ (‖smoothAFEZetaMellinAt 1 t x - smoothAFEZetaMellinAt 1 s x‖ +
            ‖smoothAFEZetaDualMellinGeneral t x -
              (smoothAFEZetaDualMellinGeneral s x +
                smoothAFEZetaShiftedPoleResidue s x)‖) +
          ‖smoothAFEZetaShiftedPoleResidue t x‖ := by
      gcongr
      exact norm_sub_le _ _
    _ = _ := by ring

/-- Limit form of the forced synthesis law along an arbitrary filter. -/
theorem tendsto_smoothAFEZetaDualMellinGeneral_base_add_residue_of_recurrence
    {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hs : s ≠ 1) (hs0 : 0 < s.re) (hs2 : s.re < 2)
    {ι : Type*} {l : Filter ι} {u : ι → ℂ}
    (hu : ∀ᶠ a in l, u a ≠ 1 ∧ 0 < (u a).re ∧ (u a).re < 2)
    (hdirect : Tendsto (fun a => smoothAFEZetaMellinAt 1 (u a) x) l
      (nhds (smoothAFEZetaMellinAt 1 s x)))
    (hzeta : Tendsto (fun a => riemannZeta (u a)) l (nhds (riemannZeta s)))
    (hpole : Tendsto (fun a => smoothAFEZetaShiftedPoleResidue (u a) x) l (nhds 0)) :
    Tendsto (fun a => smoothAFEZetaDualMellinGeneral (u a) x) l
      (nhds (smoothAFEZetaDualMellinGeneral s x + smoothAFEZetaShiftedPoleResidue s x)) := by
  have hlim := (hdirect.sub hzeta).sub hpole
  have hbase :=
    riemannZeta_eq_smoothAFEZetaMellin_sub_dual_sub_residue_general hx hs hs0 hs2
  have htarget :
      smoothAFEZetaMellinAt 1 s x - riemannZeta s - 0 =
        smoothAFEZetaDualMellinGeneral s x + smoothAFEZetaShiftedPoleResidue s x := by
    rw [hbase]
    ring
  rw [htarget] at hlim
  refine hlim.congr' ?_
  filter_upwards [hu] with a ha
  have hmove :=
    riemannZeta_eq_smoothAFEZetaMellin_sub_dual_sub_residue_general
      hx ha.1 ha.2.1 ha.2.2
  rw [hmove]
  ring

/-- Limit-form converse: the exact dual target is sufficient for zeta
self-recurrence along an arbitrary filter. -/
theorem tendsto_riemannZeta_of_smoothAFE_direct_dual_synthesis
    {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hs : s ≠ 1) (hs0 : 0 < s.re) (hs2 : s.re < 2)
    {ι : Type*} {l : Filter ι} {u : ι → ℂ}
    (hu : ∀ᶠ a in l, u a ≠ 1 ∧ 0 < (u a).re ∧ (u a).re < 2)
    (hdirect : Tendsto (fun a => smoothAFEZetaMellinAt 1 (u a) x) l
      (nhds (smoothAFEZetaMellinAt 1 s x)))
    (hdual : Tendsto (fun a => smoothAFEZetaDualMellinGeneral (u a) x) l
      (nhds (smoothAFEZetaDualMellinGeneral s x +
        smoothAFEZetaShiftedPoleResidue s x)))
    (hpole : Tendsto (fun a => smoothAFEZetaShiftedPoleResidue (u a) x) l (nhds 0)) :
    Tendsto (fun a => riemannZeta (u a)) l (nhds (riemannZeta s)) := by
  have hlim := (hdirect.sub hdual).sub hpole
  have hbase :=
    riemannZeta_eq_smoothAFEZetaMellin_sub_dual_sub_residue_general hx hs hs0 hs2
  have htarget :
      smoothAFEZetaMellinAt 1 s x -
          (smoothAFEZetaDualMellinGeneral s x +
            smoothAFEZetaShiftedPoleResidue s x) - 0 =
        riemannZeta s := by
    rw [hbase]
    ring
  rw [htarget] at hlim
  refine hlim.congr' ?_
  filter_upwards [hu] with a ha
  have hmove :=
    riemannZeta_eq_smoothAFEZetaMellin_sub_dual_sub_residue_general
      hx ha.1 ha.2.1 ha.2.2
  rw [hmove]

end RHTower
