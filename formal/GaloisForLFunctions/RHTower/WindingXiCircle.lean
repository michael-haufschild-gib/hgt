/-
Finiteness of ξ-zeros in a disc, and the winding number of ξ around a zero-avoiding circle.

The zeros of the completed ζ-function `xi` in any compact disc are finite (`xi_zeros_closedBall_finite`):
`xi` is analytic and not identically zero (it is nonzero on `Re ≥ 1`), so its zero set is codiscrete,
and a codiscrete set meets a compact set in a finite set.

Consequently the `hzeros` hypothesis of `windingNumber_xi_disc` is dischargeable: for a circle of
radius `r` carrying no ξ-zero, the winding number of `xi` around it is the sum of the orders of the
(finitely many) ξ-zeros strictly inside (`windingNumber_xi_circle`).  The radius of the peeling disc
is slid into the gap between the circle and the next zero-radius, which exists because the zeros are
finite in a slightly larger disc.
-/
import GaloisForLFunctions.RHTower.WindingXi

open Complex Set Metric Filter

namespace RHTower

/-- **The ξ-zeros in a compact disc are finite.**  `xi` is analytic on `ℂ` and not identically zero
(nonzero on `Re ≥ 1`), so its zero set is codiscrete; a codiscrete set meets the compact `closedBall`
in a finite set. -/
theorem xi_zeros_closedBall_finite (c : ℂ) (R : ℝ) :
    {z ∈ Metric.closedBall c R | xi z = 0}.Finite := by
  have hcod : (xi ⁻¹' {0}ᶜ) ∈ codiscreteWithin (Set.univ : Set ℂ) :=
    xi_analyticOnNhd_univ.preimage_zero_mem_codiscreteWithin
      (x := 2) (xi_ne_zero_of_one_le_re (by norm_num)) (Set.mem_univ 2) isConnected_univ
  have hcodK : (xi ⁻¹' {0}ᶜ) ∈ codiscreteWithin (Metric.closedBall c R) :=
    Filter.codiscreteWithin_mono (Set.subset_univ _) hcod
  refine ((isCompact_closedBall c R).finite_diff_of_mem_codiscreteWithin hcodK).subset ?_
  intro z hz
  rw [Set.mem_sep_iff] at hz
  exact ⟨hz.1, by simp [Set.mem_preimage, hz.2]⟩

/-- **The winding number of ξ around a zero-avoiding circle is the enclosed order.**  If the circle
`|z − c| = r` carries no ξ-zero, there is a finite set `t` of exactly the ξ-zeros strictly inside it,
and the winding number of `xi` around the circle is `Σ_{w ∈ t} ord_w xi`.  (`hzeros` of
`windingNumber_xi_disc` is discharged; the circle must avoid zeros — a loop through a zero has no
winding number.) -/
theorem windingNumber_xi_circle (c : ℂ) {r : ℝ} (hr : 0 < r)
    (havoid : ∀ z, ‖z - c‖ = r → xi z ≠ 0) :
    ∃ t : Finset ℂ, (∀ w, w ∈ t ↔ ‖w - c‖ < r ∧ xi w = 0) ∧
      windingNumber (fun θ => xi (c + ↑r * exp (I * ↑θ))) 0 (2 * Real.pi)
        = ∑ w ∈ t, ((analyticOrderAt xi w).toNat : ℤ) := by
  classical
  set Z₀ : Finset ℂ := (xi_zeros_closedBall_finite c (r + 1)).toFinset with hZ₀
  have hmemZ₀ : ∀ z, z ∈ Z₀ ↔ z ∈ Metric.closedBall c (r + 1) ∧ xi z = 0 := by
    intro z; rw [hZ₀, Set.Finite.mem_toFinset, Set.mem_sep_iff]
  set t : Finset ℂ := Z₀.filter (fun z => ‖z - c‖ < r) with ht
  have hmemt : ∀ w, w ∈ t ↔ ‖w - c‖ < r ∧ xi w = 0 := by
    intro w; rw [ht, Finset.mem_filter, hmemZ₀]
    constructor
    · rintro ⟨⟨_, hxi⟩, hlt⟩; exact ⟨hlt, hxi⟩
    · rintro ⟨hlt, hxi⟩
      exact ⟨⟨by rw [Metric.mem_closedBall, dist_eq_norm]; linarith, hxi⟩, hlt⟩
  refine ⟨t, hmemt, ?_⟩
  set Zpos : Finset ℂ := Z₀.filter (fun z => r < ‖z - c‖) with hZpos
  obtain ⟨R, hrR, hRle, hgap⟩ : ∃ R, r < R ∧ R ≤ r + 1 ∧ ∀ z ∈ Zpos, R ≤ ‖z - c‖ := by
    rcases Zpos.eq_empty_or_nonempty with he | hne
    · exact ⟨r + 1, by linarith, le_refl _, fun z hz => absurd (he ▸ hz) (by simp)⟩
    · have hlt : r < Zpos.inf' hne (fun z => ‖z - c‖) := by
        rw [Finset.lt_inf'_iff]; intro z hz; rw [hZpos, Finset.mem_filter] at hz; exact hz.2
      have hle : Zpos.inf' hne (fun z => ‖z - c‖) ≤ r + 1 := by
        obtain ⟨z₀, hz₀⟩ := hne
        refine le_trans (Finset.inf'_le _ hz₀) ?_
        rw [hZpos, Finset.mem_filter, hmemZ₀, Metric.mem_closedBall, dist_eq_norm] at hz₀
        exact hz₀.1.1
      refine ⟨(r + Zpos.inf' hne (fun z => ‖z - c‖)) / 2, by linarith, by linarith, fun z hz => ?_⟩
      have := Finset.inf'_le (fun z => ‖z - c‖) hz; linarith
  have htU : ∀ w ∈ t, w ∈ Metric.ball c R := fun w hw => by
    rw [Metric.mem_ball, dist_eq_norm]; linarith [(hmemt w).mp hw |>.1]
  have hzeros : ∀ z ∈ Metric.ball c R, xi z = 0 → z ∈ t := by
    intro z hz hxi
    rw [Metric.mem_ball, dist_eq_norm] at hz
    rw [hmemt]; refine ⟨?_, hxi⟩
    by_contra hge
    rw [not_lt] at hge
    have hgt : r < ‖z - c‖ := lt_of_le_of_ne hge (fun heq => havoid z heq.symm hxi)
    have hzZpos : z ∈ Zpos := by
      rw [hZpos, Finset.mem_filter, hmemZ₀]
      exact ⟨⟨by rw [Metric.mem_closedBall, dist_eq_norm]; linarith, hxi⟩, hgt⟩
    linarith [hgap z hzZpos]
  have hin : ∀ w ∈ t, ‖w - c‖ < r := fun w hw => ((hmemt w).mp hw).1
  exact windingNumber_xi_disc c hrR hr t htU hzeros hin

end RHTower
