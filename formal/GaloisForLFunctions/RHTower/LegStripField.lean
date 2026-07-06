/-
# The discrete equilibrium field: the exact deviation identity

The edge law `(½ − θ_max)√d → 1/π` is the asymptotics of an **exact** identity for the equilibrium
position. On a pole-free gap `(a,b)` the field `F = cothField s t` is strictly decreasing with
`F' = −2W`, where `W = spurLatticeEnergy s t = ¼Σ csch²` is the reduced energy. For the equilibrium
`x*` at level `L` (`F(x*) = L`) and any reference point `m` in the gap, the mean value theorem gives a
point `ξ` between them with

> `x* − m = (F(m) − L) / (2·W(ξ))`.

Taking `m` the gap midpoint and `L = −(pole count)`, the numerator `F(m) − L` is the exact
midpoint excess `2(behind − ahead) + …` (`cothField_midpoint_split`) and `2W(ξ)` is the exact
field steepness. The normalized deviation `½ − θ*` (with `θ* = (b − x*)/(b − a)` measured from the
ahead pole) is then

> `½ − θ* = (F(m) − L) / (2·W(ξ)·(b − a))`,

an **exact** equation whose two asymptotic factors — the local steepness `2W(ξ)(b−a) → π²·i`
(local factor `κ = 2/π²`) and the excess `F(m) − L = 2g(i) → 2(i/d + (π²/16)/i)·i` (the truncation
against the shell correction) — are the inputs the edge-law reduction (`edge_law_reduction`) consumes.
This file makes the exact identity a theorem, so that decomposition is grounded in the field, not
assumed. `cothField_slope_mvt`, `cothField_energy_pos_of_nonempty`, `cothField_deviation` (general
reference point), `cothField_midpoint_deviation` (the `½ − θ*` form).
-/
import GaloisForLFunctions.RHTower.LegStripThreshold
open Real Set Filter Topology
noncomputable section
namespace RHTower

/-- **The mean-value slope on a pole-free gap.** For two points `p < q` inside the gap `(a,b)`, the
field increment equals `−2W(ξ)·(q − p)` at some `ξ` strictly between them (`F' = −2W`, MVT). -/
theorem cothField_slope_mvt {ι : Type*} (s : Finset ι) (t : ι → ℝ) {a b : ℝ}
    (hpoles : ∀ k ∈ s, t k ≤ a ∨ b ≤ t k) {p q : ℝ} (hp : p ∈ Ioo a b) (hq : q ∈ Ioo a b)
    (hpq : p < q) :
    ∃ ξ ∈ Ioo p q, cothField s t q - cothField s t p
      = (-2 * spurLatticeEnergy s t ξ) * (q - p) := by
  have hsub : Icc p q ⊆ Ioo a b := by
    simp only [mem_Ioo] at hp hq
    exact Icc_subset_Ioo hp.1 hq.2
  have hcont : ContinuousOn (cothField s t) (Icc p q) :=
    (cothField_continuousOn s t hpoles).mono hsub
  have hderiv : ∀ x ∈ Ioo p q, HasDerivAt (cothField s t) (-2 * spurLatticeEnergy s t x) x := by
    intro x hx
    exact cothField_hasDerivAt s t hpoles (hsub (Ioo_subset_Icc_self hx))
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (cothField s t)
    (fun x => -2 * spurLatticeEnergy s t x) hpq hcont hderiv
  refine ⟨ξ, hξ, ?_⟩
  rw [hslope, div_mul_cancel₀]
  linarith [hpq]

/-- The reduced energy is strictly positive at any interior point of a pole-free gap when the charge
set is nonempty: every `csch²((x − t_k)/2)` is positive there. -/
theorem cothField_energy_pos_of_nonempty {ι : Type*} (s : Finset ι) (t : ι → ℝ) {a b : ℝ}
    (hne : s.Nonempty) (hpoles : ∀ k ∈ s, t k ≤ a ∨ b ≤ t k) {x : ℝ} (hx : x ∈ Ioo a b) :
    0 < spurLatticeEnergy s t x := by
  simp only [mem_Ioo] at hx
  rw [spurLatticeEnergy]
  apply mul_pos (by norm_num)
  apply Finset.sum_pos _ hne
  intro k hk
  have hne0 : (x - t k) / 2 ≠ 0 := by
    rcases hpoles k hk with h | h
    · exact ne_of_gt (by have := hx.1; linarith)
    · exact ne_of_lt (by have := hx.2; linarith)
  have : rcsch ((x - t k) / 2) ≠ 0 := by
    rw [rcsch]; exact one_div_ne_zero (Real.sinh_ne_zero.mpr hne0)
  positivity

/-- **The exact deviation identity.** For the equilibrium `x*` at level `L` (`F(x*) = L`) and any
reference point `m` in a pole-free gap, the displacement is exactly `x* − m = (F(m) − L)/(2W(ξ))` for
some interior `ξ`, with `W(ξ) > 0`. The equilibrium sits to the right of `m` iff `m` under-shoots the
level (`F(m) > L`). -/
theorem cothField_deviation {ι : Type*} (s : Finset ι) (t : ι → ℝ) {a b : ℝ}
    (hne : s.Nonempty) (hpoles : ∀ k ∈ s, t k ≤ a ∨ b ≤ t k)
    {x m L : ℝ} (hx : x ∈ Ioo a b) (hm : m ∈ Ioo a b) (hroot : cothField s t x = L) :
    ∃ ξ ∈ Ioo a b, 0 < spurLatticeEnergy s t ξ
      ∧ x - m = (cothField s t m - L) / (2 * spurLatticeEnergy s t ξ) := by
  -- produce ξ with the symmetric increment identity F(m) − F(x) = −2W(ξ)·(m − x)
  obtain ⟨ξ, hξmem, hWpos, hid⟩ :
      ∃ ξ ∈ Ioo a b, 0 < spurLatticeEnergy s t ξ
        ∧ cothField s t m - cothField s t x = (-2 * spurLatticeEnergy s t ξ) * (m - x) := by
    rcases lt_trichotomy x m with hlt | heq | hgt
    · obtain ⟨ξ, hξ, hslope⟩ := cothField_slope_mvt s t hpoles hx hm hlt
      exact ⟨ξ, Ioo_subset_Ioo_right hm.2.le (Ioo_subset_Ioo_left hx.1.le hξ),
        cothField_energy_pos_of_nonempty s t hne hpoles
          (Ioo_subset_Ioo_right hm.2.le (Ioo_subset_Ioo_left hx.1.le hξ)),
        hslope⟩
    · refine ⟨m, hm, cothField_energy_pos_of_nonempty s t hne hpoles hm, ?_⟩
      rw [heq]; ring
    · obtain ⟨ξ, hξ, hslope⟩ := cothField_slope_mvt s t hpoles hm hx hgt
      have hmem : ξ ∈ Ioo a b := Ioo_subset_Ioo_right hx.2.le (Ioo_subset_Ioo_left hm.1.le hξ)
      refine ⟨ξ, hmem, cothField_energy_pos_of_nonempty s t hne hpoles hmem, ?_⟩
      have : cothField s t x - cothField s t m = (-2 * spurLatticeEnergy s t ξ) * (x - m) := hslope
      linarith [this]
  refine ⟨ξ, hξmem, hWpos, ?_⟩
  rw [hroot] at hid
  have h2W : (2 : ℝ) * spurLatticeEnergy s t ξ ≠ 0 := by positivity
  field_simp
  linarith [hid]

/-- **The normalized deviation `½ − θ*` in exact form.** With `θ* = (b − x*)/(b − a)` measured from the
ahead pole `b` and the gap midpoint `m = (a + b)/2`, the deviation of the equilibrium from `½` is
exactly `(F(m) − L)/(2·W(ξ)·(b − a))`. The sign of `F(m) − L` (the midpoint field excess over the
level) decides inner (`θ* > ½`) vs. outer (`θ* < ½`); its `√d`-edge asymptotics against the local
steepness `2W(ξ)(b − a)` are the edge law. -/
theorem cothField_midpoint_deviation {ι : Type*} (s : Finset ι) (t : ι → ℝ) {a b : ℝ}
    (hne : s.Nonempty) (hab : a < b) (hpoles : ∀ k ∈ s, t k ≤ a ∨ b ≤ t k)
    {x L : ℝ} (hx : x ∈ Ioo a b) (hroot : cothField s t x = L) :
    ∃ ξ ∈ Ioo a b, 0 < spurLatticeEnergy s t ξ
      ∧ (1/2 - (b - x)/(b - a))
        = (cothField s t ((a + b)/2) - L) / (2 * spurLatticeEnergy s t ξ * (b - a)) := by
  have hmid : (a + b)/2 ∈ Ioo a b := by constructor <;> [linarith; linarith]
  obtain ⟨ξ, hξ, hWpos, hdev⟩ := cothField_deviation s t hne hpoles hx hmid hroot
  refine ⟨ξ, hξ, hWpos, ?_⟩
  have hbane : b - a ≠ 0 := by linarith
  have h2W : (2 : ℝ) * spurLatticeEnergy s t ξ ≠ 0 := by positivity
  -- ½ − (b−x)/(b−a) = (x − m)/(b−a),  m = (a+b)/2
  have hrw : 1/2 - (b - x)/(b - a) = (x - (a + b)/2)/(b - a) := by
    field_simp; ring
  rw [hrw, hdev]
  field_simp

/-- **The midpoint excess is `2g`.** At level `−(pole count)` the midpoint field excess over the level
is `F(m) + card = 2·(behind + BehindEx − AheadEx)`, where `behind` is the number of poles left of `m`,
`BehindEx = Σ poleExcess(m − t_k)` (behind), `AheadEx = Σ poleExcess(t_k − m)` (ahead). This is `2g(i)`
in the harmonic model (`behind = i`, `AheadEx − BehindEx = A − B`, so `g = i − (A − B)`): the exact
log-cancellation residue of §15, now the deviation numerator. -/
theorem midpoint_excess_eq {ι : Type*} (s : Finset ι) (t : ι → ℝ) (m : ℝ)
    (hnem : ∀ k ∈ s, t k ≠ m) :
    cothField s t m + (s.card : ℝ)
      = 2 * (((s.filter (fun k => t k < m)).card : ℝ)
          + (∑ k ∈ s.filter (fun k => t k < m), poleExcess (m - t k))
          - ∑ k ∈ s.filter (fun k => m < t k), poleExcess (t k - m)) := by
  classical
  have hsplit : s.filter (fun k => t k < m) ∪ s.filter (fun k => m < t k) = s := by
    rw [← Finset.filter_or]
    apply Finset.filter_true_of_mem
    intro k hk
    rcases lt_trichotomy (t k) m with h | h | h
    · exact Or.inl h
    · exact absurd h (hnem k hk)
    · exact Or.inr h
  have hdisj : Disjoint (s.filter (fun k => t k < m)) (s.filter (fun k => m < t k)) := by
    rw [Finset.disjoint_filter]; intro k _ hlt; exact not_lt.mpr (le_of_lt hlt)
  have hcard : ((s.filter (fun k => t k < m)).card : ℝ)
      + ((s.filter (fun k => m < t k)).card : ℝ) = (s.card : ℝ) := by
    rw [← Nat.cast_add, ← Finset.card_union_of_disjoint hdisj, hsplit]
  rw [cothField_midpoint_split s t m hnem]
  linarith [hcard]

/-- **The exact discrete deviation of `θ*` from `½`.** For the equilibrium `x*` at level `−(pole
count)`, with `θ* = (b − x*)/(b − a)` measured from the ahead pole, the deviation is exactly
`½ − θ* = (behind + BehindEx − AheadEx) / (W(ξ)·(b − a))` at an interior mean-value point `ξ`. In the
harmonic model this is `½ − θ*(i) = g(i)/(W(ξ)·δ_i) = 2g(i)/(|F'(ξ)|·δ_i)` — the exact form whose two
asymptotic factors (`W(ξ)δ_i/i → π²/2`, i.e. local factor `κ = 2/π²`; and `g(i)/i → i/d + (π²/16)/i`)
are the edge-law inputs. Nothing about the decomposition is assumed: it is read off the field. -/
theorem cothField_theta_deviation {ι : Type*} (s : Finset ι) (t : ι → ℝ) {a b : ℝ}
    (hne : s.Nonempty) (hab : a < b) (hpoles : ∀ k ∈ s, t k ≤ a ∨ b ≤ t k)
    (hnem : ∀ k ∈ s, t k ≠ (a + b)/2)
    {x : ℝ} (hx : x ∈ Ioo a b) (hroot : cothField s t x = -(s.card : ℝ)) :
    ∃ ξ ∈ Ioo a b, 0 < spurLatticeEnergy s t ξ
      ∧ 1/2 - (b - x)/(b - a)
        = (((s.filter (fun k => t k < (a + b)/2)).card : ℝ)
            + (∑ k ∈ s.filter (fun k => t k < (a + b)/2), poleExcess ((a + b)/2 - t k))
            - ∑ k ∈ s.filter (fun k => (a + b)/2 < t k), poleExcess (t k - (a + b)/2))
          / (spurLatticeEnergy s t ξ * (b - a)) := by
  obtain ⟨ξ, hξ, hW, hdev⟩ := cothField_midpoint_deviation s t hne hab hpoles hx hroot
  refine ⟨ξ, hξ, hW, ?_⟩
  rw [hdev, show cothField s t ((a + b)/2) - (-(s.card : ℝ))
      = cothField s t ((a + b)/2) + (s.card : ℝ) by ring,
    midpoint_excess_eq s t ((a + b)/2) hnem]
  have hW' : spurLatticeEnergy s t ξ ≠ 0 := ne_of_gt hW
  have hba : b - a ≠ 0 := by linarith
  field_simp

end RHTower
end
