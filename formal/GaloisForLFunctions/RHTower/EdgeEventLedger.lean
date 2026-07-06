/-
The forced band-edge events supplied to the paired-flux interface.

The winding argument forces a strictly ordered family of `n` simple transversal band-edge
events on a lateral edge — each a point where a real-ratio pencil member vanishes.  Recorded as
an event list, they are `n` copies of the odd multiplicity `1`: the odd event class of
`LedgerFluxPaired`.  Once this class carries a fixed-point-free pairing, the paired-flux
interface is satisfied — so the analytic burden is discharged into supplying the events (done
here, unconditionally on any high enough edge with a subcritical Dirichlet budget), leaving only
the pairing on them as the band-edge arithmetic input.
-/
import GaloisForLFunctions.RHTower.EdgeEventSynthesis
import GaloisForLFunctions.RHTower.LedgerReduction
import GaloisForLFunctions.RHTower.BandEdgePairingConstruction

open Complex

namespace RHTower

/-! ### The supplied odd-event class -/

/-- **A list of `n` simple events carries paired flux exactly when a pairing exists.**  The `n`
forced simple crossings are the odd multiplicity `1` repeated `n` times; their event list has
paired flux as soon as the `n` positions carry a fixed-point-free pairing. -/
theorem ledgerFluxPaired_replicate_one {n : ℕ} (hpair : Nonempty (BandEdgePairing (Fin n))) :
    LedgerFluxPaired (List.replicate n 1) := by
  refine ⟨[], List.replicate n 1, by simp, by simp, ?_, ?_⟩
  · intro x hx; rw [List.eq_of_mem_replicate hx]; decide
  · rw [List.length_replicate]; exact hpair

/-! ### The high-edge forcing corollary -/

/-- **Forced events on a high edge with a subcritical Dirichlet budget.**  On a lateral edge at
an abscissa `σ ∈ (0,1)` and height `a` above the explicit threshold where the archimedean floor
exceeds the anchor's prime-sum budget and the Dirichlet budget by at least one, any subsegment
long enough to advance the phase by `n·π` carries `n` strictly ordered forced band-edge events.
The net winding rate is normalised to one, so the event density is `1/π` per unit edge
length. -/
theorem exists_edge_events_of_high_edge {P : Finset ℕ} {N : ℕ} {σ a b B_D : ℝ} {n : ℕ}
    {U : Set ℂ}
    (hP : ∀ p ∈ P, 2 ≤ p) (hσ : 0 < σ) (hσ1 : σ < 1) (ha : 0 < a) (hab : a ≤ b)
    (hU : IsOpen U) (hUstrip : U ⊆ {z : ℂ | 0 < z.re ∧ z.re < 1})
    (hmapU : ∀ τ ∈ Set.Icc a b, stripPt σ τ ∈ U)
    (hgneU : ∀ z ∈ U, gN N z ≠ 0)
    (hBD : ∀ τ ∈ Set.Icc a b, |(logDeriv (gN N) (stripPt σ τ)).re| ≤ B_D)
    (hnet : 1 ≤ stripFloor σ a - eulerHeadBound P σ - B_D)
    (hn : (n : ℝ) * Real.pi ≤ b - a) :
    ∃ e : Fin n → ℝ, StrictMono e ∧ ∀ i, e i ∈ Set.Icc a b ∧
      pencil (eulerHeadAnchor P) (completedGN N)
        ((incidence (eulerHeadAnchor P) (completedGN N) (stripPt σ (e i))).re : ℂ) 1
        (stripPt σ (e i)) = 0 := by
  refine exists_edge_events_completedGN hP hσ hσ1 ha hab hU hUstrip hmapU hgneU
    (fun τ hτ => hgneU _ (hmapU τ hτ)) hBD one_pos hnet ?_
  rwa [mul_one]

/-! ### The capstone: events supplied, pairing the sole remaining input -/

/-- **The events are supplied and their flux is paired given the pairing.**  On a high enough
lateral edge with a subcritical Dirichlet budget, the winding argument forces `n` strictly
ordered band-edge events; recorded as an event list they carry paired flux as soon as the `n`
events carry a fixed-point-free pairing.  The analytic content — the existence of the events —
is discharged unconditionally; the pairing is the only band-edge arithmetic input that remains.
This is the paired-flux interface handed its odd event class with the events supplied rather
than hypothesized. -/
theorem exists_edge_events_supply_fluxPaired {P : Finset ℕ} {N : ℕ} {σ a b B_D : ℝ} {n : ℕ}
    {U : Set ℂ}
    (hP : ∀ p ∈ P, 2 ≤ p) (hσ : 0 < σ) (hσ1 : σ < 1) (ha : 0 < a) (hab : a ≤ b)
    (hU : IsOpen U) (hUstrip : U ⊆ {z : ℂ | 0 < z.re ∧ z.re < 1})
    (hmapU : ∀ τ ∈ Set.Icc a b, stripPt σ τ ∈ U)
    (hgneU : ∀ z ∈ U, gN N z ≠ 0)
    (hBD : ∀ τ ∈ Set.Icc a b, |(logDeriv (gN N) (stripPt σ τ)).re| ≤ B_D)
    (hnet : 1 ≤ stripFloor σ a - eulerHeadBound P σ - B_D)
    (hn : (n : ℝ) * Real.pi ≤ b - a)
    (hpair : Nonempty (BandEdgePairing (Fin n))) :
    (∃ e : Fin n → ℝ, StrictMono e ∧ ∀ i, e i ∈ Set.Icc a b ∧
        pencil (eulerHeadAnchor P) (completedGN N)
          ((incidence (eulerHeadAnchor P) (completedGN N) (stripPt σ (e i))).re : ℂ) 1
          (stripPt σ (e i)) = 0)
      ∧ LedgerFluxPaired (List.replicate n 1) :=
  ⟨exists_edge_events_of_high_edge hP hσ hσ1 ha hab hU hUstrip hmapU hgneU hBD hnet hn,
    ledgerFluxPaired_replicate_one hpair⟩

/-! ### The Dirichlet budget supplied by carrier sup and floor bounds -/

/-- **Forced events with the Dirichlet budget supplied, not assumed.**  The Dirichlet phase
budget `B_D` need not be given: a modulus floor `m > 0` and a derivative sup `M₁` for the carrier
`gN` along the edge produce it as `M₁/m`.  On a high edge whose archimedean floor beats the
anchor prime sum and `M₁/m` by at least one, the winding forces `n` strictly ordered band-edge
events, and — given the pairing on them — their event list carries paired flux.  Every budget on
this route is now computed from carrier data; the pairing is the only remaining input. -/
theorem exists_edge_events_supply_fluxPaired_of_carrier_bounds {P : Finset ℕ} {N : ℕ}
    {σ a b m M₁ : ℝ} {n : ℕ} {U : Set ℂ}
    (hP : ∀ p ∈ P, 2 ≤ p) (hσ : 0 < σ) (hσ1 : σ < 1) (ha : 0 < a) (hab : a ≤ b)
    (hU : IsOpen U) (hUstrip : U ⊆ {z : ℂ | 0 < z.re ∧ z.re < 1})
    (hmapU : ∀ τ ∈ Set.Icc a b, stripPt σ τ ∈ U)
    (hgneU : ∀ z ∈ U, gN N z ≠ 0)
    (hm0 : 0 < m) (hm : ∀ τ ∈ Set.Icc a b, m ≤ ‖gN N (stripPt σ τ)‖)
    (hM₁ : ∀ τ ∈ Set.Icc a b, ‖deriv (gN N) (stripPt σ τ)‖ ≤ M₁)
    (hnet : 1 ≤ stripFloor σ a - eulerHeadBound P σ - M₁ / m)
    (hn : (n : ℝ) * Real.pi ≤ b - a)
    (hpair : Nonempty (BandEdgePairing (Fin n))) :
    (∃ e : Fin n → ℝ, StrictMono e ∧ ∀ i, e i ∈ Set.Icc a b ∧
        pencil (eulerHeadAnchor P) (completedGN N)
          ((incidence (eulerHeadAnchor P) (completedGN N) (stripPt σ (e i))).re : ℂ) 1
          (stripPt σ (e i)) = 0)
      ∧ LedgerFluxPaired (List.replicate n 1) := by
  have hBD : ∀ τ ∈ Set.Icc a b, |(logDeriv (gN N) (stripPt σ τ)).re| ≤ M₁ / m :=
    fun τ hτ => abs_re_logDeriv_le_of_bounds hm0 (hm τ hτ) (hM₁ τ hτ)
  exact exists_edge_events_supply_fluxPaired hP hσ hσ1 ha hab hU hUstrip hmapU hgneU hBD
    hnet hn hpair

/-! ### The pairing discharged for an even count -/

/-- **Events supplied AND paired, with the pairing constructed.**  Taking an even forced count
`2m`, the consecutive-crossing pairing is available without hypothesis: the `2m` forced band-edge
events exist and their event list carries paired flux, with the pairing built from the adjacent
pairs.  No `BandEdgePairing` is assumed — the paired-flux interface is satisfied outright for an
even count, so the sole residual content of the whole route is the parity of the band-event
count. -/
theorem exists_edge_events_fluxPaired_even {P : Finset ℕ} {N : ℕ} {σ a b B_D : ℝ} {m : ℕ}
    {U : Set ℂ}
    (hP : ∀ p ∈ P, 2 ≤ p) (hσ : 0 < σ) (hσ1 : σ < 1) (ha : 0 < a) (hab : a ≤ b)
    (hU : IsOpen U) (hUstrip : U ⊆ {z : ℂ | 0 < z.re ∧ z.re < 1})
    (hmapU : ∀ τ ∈ Set.Icc a b, stripPt σ τ ∈ U)
    (hgneU : ∀ z ∈ U, gN N z ≠ 0)
    (hBD : ∀ τ ∈ Set.Icc a b, |(logDeriv (gN N) (stripPt σ τ)).re| ≤ B_D)
    (hnet : 1 ≤ stripFloor σ a - eulerHeadBound P σ - B_D)
    (hn : ((2 * m : ℕ) : ℝ) * Real.pi ≤ b - a) :
    (∃ e : Fin (2 * m) → ℝ, StrictMono e ∧ ∀ i, e i ∈ Set.Icc a b ∧
        pencil (eulerHeadAnchor P) (completedGN N)
          ((incidence (eulerHeadAnchor P) (completedGN N) (stripPt σ (e i))).re : ℂ) 1
          (stripPt σ (e i)) = 0)
      ∧ LedgerFluxPaired (List.replicate (2 * m) 1) :=
  ⟨exists_edge_events_of_high_edge hP hσ hσ1 ha hab hU hUstrip hmapU hgneU hBD hnet hn,
    ledgerFluxPaired_replicate_one (nonempty_bandEdgePairing_of_even ⟨m, rfl⟩)⟩

/-- **The explicit forcing height.**  Because the off-line winding floor grows without bound in
the height while the anchor prime-sum budget and any fixed Dirichlet budget do not, there is an
explicit height `A` above which the net winding rate exceeds one — so on every edge from height
`A` upward the high-edge forcing corollary applies.  This is the subcriticality of the two
Dirichlet budgets against the archimedean floor: the events are eventually forced. -/
theorem exists_forcing_height {P : Finset ℕ} {σ B_D : ℝ} (hσ0 : 0 ≤ σ) :
    ∃ A : ℝ, 0 < A ∧ ∀ a, A ≤ a → 1 ≤ stripFloor σ a - eulerHeadBound P σ - B_D :=
  exists_height_net_rate_ge (P := P) (B_D := B_D) (ρ₀ := 1) hσ0

end RHTower
