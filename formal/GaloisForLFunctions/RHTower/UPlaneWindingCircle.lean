/-
# Unconditional circle winding for the descended completed zeta

`UPlaneWinding` proves the argument-principle formula after a caller supplies a finite census of
all `xiDescent` zeros in a larger ball. The same module already proves that these zeros are locally
finite. This file closes the interface: on a zero-avoiding circle it constructs the exact finite
interior census and chooses a slightly larger zero-free radius internally.

No zero-census, containing-ball, or analytic-order hypothesis remains in the public circle
theorems.
-/
import GaloisForLFunctions.RHTower.UPlaneWinding

open Complex Set Metric Filter

namespace RHTower

/-- **Unconditional descended winding census.** The winding number of `xiDescent` around a
zero-avoiding circle is the total order of precisely the zeros strictly inside. -/
theorem windingNumber_xiDescent_circle (c : ℂ) {r : ℝ} (hr : 0 < r)
    (havoid : ∀ z, ‖z - c‖ = r → xiDescent z ≠ 0) :
    ∃ t : Finset ℂ, (∀ w, w ∈ t ↔ ‖w - c‖ < r ∧ xiDescent w = 0) ∧
      windingNumber (fun θ => xiDescent (c + ↑r * exp (I * ↑θ))) 0 (2 * Real.pi)
        = ∑ w ∈ t, ((analyticOrderAt xiDescent w).toNat : ℤ) := by
  classical
  set Z₀ : Finset ℂ := (xiDescent_zeros_finite_ball c (r + 1)).toFinset with hZ₀
  have hmemZ₀ : ∀ z, z ∈ Z₀ ↔ z ∈ Metric.ball c (r + 1) ∧ xiDescent z = 0 := by
    intro z
    rw [hZ₀, Set.Finite.mem_toFinset, Set.mem_sep_iff]
  set t : Finset ℂ := Z₀.filter (fun z => ‖z - c‖ < r) with ht
  have hmemt : ∀ w, w ∈ t ↔ ‖w - c‖ < r ∧ xiDescent w = 0 := by
    intro w
    rw [ht, Finset.mem_filter, hmemZ₀]
    constructor
    · rintro ⟨⟨_, hxi⟩, hlt⟩
      exact ⟨hlt, hxi⟩
    · rintro ⟨hlt, hxi⟩
      exact ⟨⟨by rw [Metric.mem_ball, dist_eq_norm]; linarith, hxi⟩, hlt⟩
  refine ⟨t, hmemt, ?_⟩
  set Zpos : Finset ℂ := Z₀.filter (fun z => r < ‖z - c‖) with hZpos
  obtain ⟨R, hrR, hRlt, hgap⟩ :
      ∃ R, r < R ∧ R < r + 1 ∧ ∀ z ∈ Zpos, R ≤ ‖z - c‖ := by
    rcases Zpos.eq_empty_or_nonempty with he | hne
    · exact ⟨r + 1 / 2, by linarith, by linarith,
        fun z hz => absurd (he ▸ hz) (by simp)⟩
    · have hlt : r < Zpos.inf' hne (fun z => ‖z - c‖) := by
        rw [Finset.lt_inf'_iff]
        intro z hz
        rw [hZpos, Finset.mem_filter] at hz
        exact hz.2
      have hltTop : Zpos.inf' hne (fun z => ‖z - c‖) < r + 1 := by
        obtain ⟨z₀, hz₀⟩ := hne
        refine lt_of_le_of_lt (Finset.inf'_le _ hz₀) ?_
        rw [hZpos, Finset.mem_filter, hmemZ₀, Metric.mem_ball, dist_eq_norm] at hz₀
        exact hz₀.1.1
      refine ⟨(r + Zpos.inf' hne (fun z => ‖z - c‖)) / 2,
        by linarith, by linarith, fun z hz => ?_⟩
      have := Finset.inf'_le (fun z => ‖z - c‖) hz
      linarith
  have htU : ∀ w ∈ t, w ∈ Metric.ball c R := fun w hw => by
    rw [Metric.mem_ball, dist_eq_norm]
    linarith [(hmemt w).mp hw |>.1]
  have hzeros : ∀ z ∈ Metric.ball c R, xiDescent z = 0 → z ∈ t := by
    intro z hz hxi
    rw [Metric.mem_ball, dist_eq_norm] at hz
    rw [hmemt]
    refine ⟨?_, hxi⟩
    by_contra hge
    rw [not_lt] at hge
    have hgt : r < ‖z - c‖ :=
      lt_of_le_of_ne hge (fun heq => havoid z heq.symm hxi)
    have hzZpos : z ∈ Zpos := by
      rw [hZpos, Finset.mem_filter, hmemZ₀]
      exact ⟨⟨by rw [Metric.mem_ball, dist_eq_norm]; linarith, hxi⟩, hgt⟩
    linarith [hgap z hzZpos]
  have hin : ∀ w ∈ t, ‖w - c‖ < r := fun w hw => ((hmemt w).mp hw).1
  exact windingNumber_xiDescent_disc c hrR hr t htU hzeros hin

/-- **Unconditional descended loop charge.** The rung-`k` loop charge on a zero-avoiding circle is
the reduction of the total enclosed `xiDescent` order. -/
theorem loopCharge_xiDescent_circle (c : ℂ) {r : ℝ} (hr : 0 < r)
    (havoid : ∀ z, ‖z - c‖ = r → xiDescent z ≠ 0) (k : ℕ) :
    ∃ t : Finset ℂ, (∀ w, w ∈ t ↔ ‖w - c‖ < r ∧ xiDescent w = 0) ∧
      loopCharge k (fun θ => xiDescent (c + ↑r * exp (I * ↑θ))) 0 (2 * Real.pi)
        = wCharge (2 ^ k) (∑ w ∈ t, ((analyticOrderAt xiDescent w).toNat : ℤ)) := by
  rcases windingNumber_xiDescent_circle c hr havoid with ⟨t, ht, hwind⟩
  refine ⟨t, ht, ?_⟩
  rw [loopCharge, hwind]

end RHTower
