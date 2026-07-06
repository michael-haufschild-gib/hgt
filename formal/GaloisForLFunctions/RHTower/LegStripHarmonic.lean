/-
# The discrete `θ*(i)` field on the harmonic pole model

The harmonic carrier is the pole configuration `T_j = c·H_{j−1}` (`H_{j−1} = Σ_{l<j} 1/(l+1)`),
`j = 0,…,d−1`, at level `−d`. This is the concrete field whose equilibrium positions the strip
threshold and edge law describe. Here it is built as an actual `Finset`-indexed `cothField`, and the
exact deviation identity (`cothField_theta_deviation`) is instantiated on it:

> `½ − θ*(i) = ((i+1) + BehindEx − AheadEx) / (W(ξ)·δ_i)`,  `δ_i = c/(i+1)`,

where `θ*(i) = (T_{i+1} − x*)/δ_i` is measured from the ahead pole, `x*` the equilibrium in gap `i`,
`W(ξ)` the reduced energy at an interior mean-value point, and `BehindEx − AheadEx` the exact
log-cancellation excess of §15. The numerator `(i+1) + BehindEx − AheadEx = g(i)` is exactly the
finite-`d` residue whose asymptotics `g(i)/i → i/d + (π²/16)/i` and `W(ξ)δ_i/i → π²/2` are the
edge-law inputs — so the whole decomposition is read off this field, not assumed.

`harmPole`, `harmPole_strictMono`, `harmPole_gap_width`, `harmonic_behind_card`,
`harmonic_theta_deviation` (the exact discrete deviation).
-/
import GaloisForLFunctions.RHTower.LegStripField
open Real Set Filter Topology
noncomputable section
namespace RHTower

/-- The harmonic pole location `T_{j+1} = c·H_j = c·Σ_{l<j} 1/(l+1)` (`harmPole c 0 = 0`). -/
def harmPole (c : ℝ) (j : ℕ) : ℝ := c * ∑ l ∈ Finset.range j, 1/((l:ℝ)+1)

/-- Consecutive harmonic poles are spaced `harmPole c (j+1) − harmPole c j = c/(j+1)`. -/
theorem harmPole_succ (c : ℝ) (j : ℕ) :
    harmPole c (j+1) = harmPole c j + c/((j:ℝ)+1) := by
  rw [harmPole, harmPole, Finset.sum_range_succ, mul_add]; ring

/-- The harmonic poles are strictly increasing (spacing `c/(j+1) > 0`). -/
theorem harmPole_strictMono {c : ℝ} (hc : 0 < c) : StrictMono (harmPole c) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [harmPole_succ]
  have : (0:ℝ) < c/((n:ℝ)+1) := by positivity
  linarith

/-- The gap width `δ_i = T_{i+1} − T_i = c/(i+1)`. -/
theorem harmPole_gap_width (c : ℝ) (i : ℕ) :
    harmPole c (i+1) - harmPole c i = c/((i:ℝ)+1) := by
  rw [harmPole_succ]; ring

/-- The number of poles left of the gap-`i` midpoint is `i+1` (poles `T_0,…,T_i`). -/
theorem harmonic_behind_card {c : ℝ} (hc : 0 < c) {d i : ℕ} (hid : i + 1 < d) :
    ((Finset.range d).filter
      (fun j => harmPole c j < (harmPole c i + harmPole c (i+1))/2)).card = i + 1 := by
  have hlt : harmPole c i < harmPole c (i+1) := harmPole_strictMono hc (by omega)
  have hset : (Finset.range d).filter
      (fun j => harmPole c j < (harmPole c i + harmPole c (i+1))/2) = Finset.range (i+1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨_, hjlt⟩
      rcases Nat.lt_or_ge j (i+1) with h | h
      · exact h
      · exfalso
        have : harmPole c (i+1) ≤ harmPole c j := (harmPole_strictMono hc).monotone h
        linarith
    · intro hj
      refine ⟨by omega, ?_⟩
      have : harmPole c j ≤ harmPole c i := (harmPole_strictMono hc).monotone (by omega)
      linarith
  rw [hset, Finset.card_range]

/-- **The exact discrete `θ*(i)` deviation on the harmonic model.** For the equilibrium `x*` in gap
`i` at level `−d` (`cothField (range d) (harmPole c) x* = −d`), with `θ*(i) = (T_{i+1} − x*)/δ_i` from
the ahead pole and `δ_i = c/(i+1)`,

> `½ − θ*(i) = ((i+1) + BehindEx − AheadEx) / (W(ξ)·δ_i)`

for a mean-value point `ξ` with `W(ξ) > 0`. `BehindEx = Σ_{j≤i} poleExcess(m − T_j)`,
`AheadEx = Σ_{j>i} poleExcess(T_j − m)`, `m` the midpoint. The numerator is the exact §15 residue
`g(i)`; the identity is the deviation whose `√d`-edge asymptotics are the edge law. -/
theorem harmonic_theta_deviation {c : ℝ} (hc : 0 < c) {d i : ℕ} (hid : i + 1 < d)
    {x : ℝ} (hx : x ∈ Ioo (harmPole c i) (harmPole c (i+1)))
    (hroot : cothField (Finset.range d) (harmPole c) x = -(d : ℝ)) :
    ∃ ξ ∈ Ioo (harmPole c i) (harmPole c (i+1)),
      0 < spurLatticeEnergy (Finset.range d) (harmPole c) ξ
      ∧ 1/2 - (harmPole c (i+1) - x)/(c/((i:ℝ)+1))
        = ((i + 1 : ℝ)
            + (∑ j ∈ (Finset.range d).filter
                (fun j => harmPole c j < (harmPole c i + harmPole c (i+1))/2),
                poleExcess ((harmPole c i + harmPole c (i+1))/2 - harmPole c j))
            - ∑ j ∈ (Finset.range d).filter
                (fun j => (harmPole c i + harmPole c (i+1))/2 < harmPole c j),
                poleExcess (harmPole c j - (harmPole c i + harmPole c (i+1))/2))
          / (spurLatticeEnergy (Finset.range d) (harmPole c) ξ * (c/((i:ℝ)+1))) := by
  have hab : harmPole c i < harmPole c (i+1) := harmPole_strictMono hc (by omega)
  have hne : (Finset.range d).Nonempty := Finset.nonempty_range_iff.mpr (by omega)
  have hpoles : ∀ j ∈ Finset.range d,
      harmPole c j ≤ harmPole c i ∨ harmPole c (i+1) ≤ harmPole c j := by
    intro j _
    rcases Nat.lt_or_ge j (i+1) with h | h
    · exact Or.inl ((harmPole_strictMono hc).monotone (by omega : j ≤ i))
    · exact Or.inr ((harmPole_strictMono hc).monotone h)
  have hnem : ∀ j ∈ Finset.range d, harmPole c j ≠ (harmPole c i + harmPole c (i+1))/2 := by
    intro j _
    rcases Nat.lt_or_ge j (i+1) with h | h
    · have : harmPole c j ≤ harmPole c i := (harmPole_strictMono hc).monotone (by omega : j ≤ i)
      intro hc'; rw [hc'] at this; linarith
    · have : harmPole c (i+1) ≤ harmPole c j := (harmPole_strictMono hc).monotone h
      intro hc'; rw [hc'] at this; linarith
  have hrootc : cothField (Finset.range d) (harmPole c) x
      = -((Finset.range d).card : ℝ) := by rw [Finset.card_range]; exact hroot
  obtain ⟨ξ, hξ, hW, hdev⟩ :=
    cothField_theta_deviation (Finset.range d) (harmPole c) hne hab hpoles hnem hx hrootc
  refine ⟨ξ, hξ, hW, ?_⟩
  rw [harmPole_gap_width] at hdev
  rw [hdev, harmonic_behind_card hc hid]
  push_cast
  ring

/-- **The W-response room on the harmonic model.** The room `δ_i/2 − s* = δ_i/2 − (T_{i+1} − x*)` in
which the `(S-mono)` mechanism operates is exactly `g(i)/W(ξ)`, with `g(i) = (i+1) + BehindEx − AheadEx`
the §15 residue and `W(ξ)` the reduced energy at a mean-value point. The room is positive iff `g(i) > 0`
(the strip is empty at gap `i`); at `c = 2` its `√d`-rate is the edge law. -/
theorem harmonic_room_eq {c : ℝ} (hc : 0 < c) {d i : ℕ} (hid : i + 1 < d)
    {x : ℝ} (hx : x ∈ Ioo (harmPole c i) (harmPole c (i+1)))
    (hroot : cothField (Finset.range d) (harmPole c) x = -(d : ℝ)) :
    ∃ ξ ∈ Ioo (harmPole c i) (harmPole c (i+1)),
      0 < spurLatticeEnergy (Finset.range d) (harmPole c) ξ
      ∧ (c/((i:ℝ)+1))/2 - (harmPole c (i+1) - x)
        = ((i + 1 : ℝ)
            + (∑ j ∈ (Finset.range d).filter
                (fun j => harmPole c j < (harmPole c i + harmPole c (i+1))/2),
                poleExcess ((harmPole c i + harmPole c (i+1))/2 - harmPole c j))
            - ∑ j ∈ (Finset.range d).filter
                (fun j => (harmPole c i + harmPole c (i+1))/2 < harmPole c j),
                poleExcess (harmPole c j - (harmPole c i + harmPole c (i+1))/2))
          / spurLatticeEnergy (Finset.range d) (harmPole c) ξ := by
  obtain ⟨ξ, hξ, hW, hdev⟩ := harmonic_theta_deviation hc hid hx hroot
  refine ⟨ξ, hξ, hW, ?_⟩
  have hδ : (0:ℝ) < c/((i:ℝ)+1) := by positivity
  set δ := c/((i:ℝ)+1) with hδdef
  have hδ' : δ ≠ 0 := ne_of_gt hδ
  set W := spurLatticeEnergy (Finset.range d) (harmPole c) ξ with hWdef
  rw [show δ/2 - (harmPole c (i+1) - x) = δ * (1/2 - (harmPole c (i+1) - x)/δ) by field_simp,
    hdev, mul_comm W δ, ← mul_div_assoc, mul_div_mul_left _ _ hδ']

end RHTower
end
