/-
The winding number of ξ around a zero is its ladder charge.

Instantiating the argument principle (`windingNumber_argument_principle`) on the completed ζ-function
`xi` via its local single-zero factorisation `xi = (·−ρ₀)^{m}·h` (`xi_peel_ball`, `h` analytic and
nowhere zero on a small disc): the winding number of `xi` around a small circle about `ρ₀` is the
vanishing order `m = ord_{ρ₀} xi` (`windingNumber_xi_zero`), so the loop deck charge of that circle is
the ladder charge `ladderCharge k ρ₀` (`loopCharge_xi_zero`).

This is the contour (winding) realisation of the ξ deck charge — the topological twin of the
logarithmic-derivative residue `m_ρ = Res_{ρ}(xi'/xi)` — welding the winding-number calculus to the
`RH_{2^k}` ladder: the winding number of ξ around an off-line zero is exactly its rung-`k` charge.
-/
import GaloisForLFunctions.RHTower.WindingFull
import GaloisForLFunctions.RHTower.DeckChargeLadder
import GaloisForLFunctions.RHTower.XiDeck
import GaloisForLFunctions.RHTower.DiscWindow

open Complex Set Metric

namespace RHTower

/-- **The winding number of ξ around a zero is its order.**  There is a small disc about `ρ₀` such
that, for every circle of positive radius `r` inside it, the winding number of `xi` around that
circle equals `ord_{ρ₀} xi`. -/
theorem windingNumber_xi_zero (ρ₀ : ℂ) :
    ∃ R₀ > 0, ∀ r : ℝ, 0 < r → r < R₀ →
      windingNumber (fun θ => xi (ρ₀ + ↑r * exp (I * ↑θ))) 0 (2 * Real.pi)
        = ((analyticOrderAt xi ρ₀).toNat : ℤ) := by
  obtain ⟨R₀, hR₀, h, hha, hh0, hfact⟩ := xi_peel_ball ρ₀
  refine ⟨R₀, hR₀, fun r hr hrR => ?_⟩
  have hap := windingNumber_argument_principle ({()} : Finset Unit) (fun _ => ρ₀)
    (fun _ => (analyticOrderAt xi ρ₀).toNat) (f := xi) (g := h) (c := ρ₀) (r := r) (R := R₀)
    hrR hr (fun i _ => by rw [sub_self, norm_zero]; exact hr) hha.continuousOn hh0
    (fun z hz => by rw [Finset.prod_singleton]; exact hfact z hz)
  rwa [Finset.sum_singleton] at hap

/-- **The winding number of ξ around a zero is its ladder charge.**  The loop deck charge of a small
circle about `ρ₀` is `ladderCharge k ρ₀` — the winding-number realisation of the `RH_{2^k}` ladder
invariant. -/
theorem loopCharge_xi_zero (ρ₀ : ℂ) (k : ℕ) :
    ∃ R₀ > 0, ∀ r : ℝ, 0 < r → r < R₀ →
      loopCharge k (fun θ => xi (ρ₀ + ↑r * exp (I * ↑θ))) 0 (2 * Real.pi) = ladderCharge k ρ₀ := by
  obtain ⟨R₀, hR₀, hw⟩ := windingNumber_xi_zero ρ₀
  exact ⟨R₀, hR₀, fun r hr hrR => by rw [loopCharge, hw r hr hrR, ladderCharge]⟩

/-- **The winding number of ξ around a disc is the total enclosed order.**  If `t` collects all the
ξ-zeros of `ball c R`, all strictly inside the circle of radius `r < R`, the winding number of `xi`
around that circle is `Σ_{w ∈ t} ord_w xi` — the census of enclosed orders. -/
theorem windingNumber_xi_disc (c : ℂ) {r R : ℝ} (hrR : r < R) (hr : 0 < r)
    (t : Finset ℂ) (htU : ∀ w ∈ t, w ∈ Metric.ball c R)
    (hzeros : ∀ z ∈ Metric.ball c R, xi z = 0 → z ∈ t)
    (hin : ∀ w ∈ t, ‖w - c‖ < r) :
    windingNumber (fun θ => xi (c + ↑r * exp (I * ↑θ))) 0 (2 * Real.pi)
      = ∑ w ∈ t, ((analyticOrderAt xi w).toNat : ℤ) := by
  obtain ⟨h, hha, hh0, hfact⟩ := exists_multi_peel_orders (f := xi) isOpen_ball
    (xi_analyticOnNhd_univ.mono (Set.subset_univ _)) t htU hzeros (fun w _ => xi_orderAt_ne_top w)
  exact windingNumber_argument_principle t (fun w => w)
    (fun w => (analyticOrderAt xi w).toNat) (f := xi) (g := h) (c := c) (r := r) (R := R)
    hrR hr hin hha.continuousOn hh0 hfact

/-- The loop deck charge of a boundary circle of ξ is the reduction of the total enclosed order — the
winding-number realisation of the box census deck charge (`Σ` of enclosed `ladderCharge`s). -/
theorem loopCharge_xi_disc (c : ℂ) {r R : ℝ} (hrR : r < R) (hr : 0 < r)
    (t : Finset ℂ) (htU : ∀ w ∈ t, w ∈ Metric.ball c R)
    (hzeros : ∀ z ∈ Metric.ball c R, xi z = 0 → z ∈ t)
    (hin : ∀ w ∈ t, ‖w - c‖ < r) (k : ℕ) :
    loopCharge k (fun θ => xi (c + ↑r * exp (I * ↑θ))) 0 (2 * Real.pi)
      = wCharge (2 ^ k) (∑ w ∈ t, ((analyticOrderAt xi w).toNat : ℤ)) := by
  rw [loopCharge, windingNumber_xi_disc c hrR hr t htU hzeros hin]

end RHTower
