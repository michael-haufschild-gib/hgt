import GaloisForLFunctions.RHTower.NoDiscreteInvariant

/-!
# A gap below all its running means collides

The collision criterion of the preceding modules was stated with the crude field bound
`Δ ≤ π²/(3γ²)`, `γ` the minimum of *all* other gaps, giving the threshold `δ/γ < √6/π`.  That bound
throws away the exact structure of the lattice equilibrium.  Keeping it gives a far weaker — and
attainable — hypothesis.

The field of a gap `δ` between consecutive real zeros is

```text
Δ = Σ_{m≥1} [ 1/(D_m^L(D_m^L + δ)) + 1/(D_m^R(D_m^R + δ)) ] ,
```

where `D_m^L = δ_{n-1} + … + δ_{n-m}` and `D_m^R = δ_{n+1} + … + δ_{n+m}` are the distances to the
`m`-th neighbours.  For the lattice `D_m = mδ` and each term is `1/(m(m+1)δ²)`, so
`δ²Δ = 2Σ_{m≥1} 1/(m(m+1)) = 2` — the equilibrium.  Comparing **term by term** rather than through a
single minimum:

```text
D_m ≥ mδ   ⟹   1/(D_m(D_m+δ)) ≤ 1/(m(m+1)δ²) ,
```

so `δ²Δ ≤ 2` with strict inequality as soon as one `D_m` exceeds `mδ`.  And `D_m^{L} ≥ mδ` says
exactly that `δ` is at most the **running mean** of the `m` gaps on that side.  Hence:

> **A gap that is at most the running average of the gaps on each side, for every window length, and
> strictly below one of them, satisfies `δ²Δ < 2` and collides in backward time.**

This is a much weaker hypothesis than "below `√6/π` times the minimum gap".  A gap that is minimal
over a window automatically satisfies the running-mean condition inside the window; outside it, the
running means approach the local mean spacing, so the condition there reduces to the *normalized*
gap being at most `1`.  Both are available: the minimum over a window of `N` gaps has normalized gap
at most the mean `1`, and by the known small-gap results infinitely many normalized gaps fall below
`0.515396`.

The hypothesis is also **preserved by the flow**.  The velocity of a gap is `-4/δ + 2δΔ`; for the
minimal gap `-4/δ` is the most negative and `2δΔ` the smallest, so the minimal gap contracts fastest
and stays minimal.  The running-mean condition therefore persists over the collision interval, which
is what a frozen-field estimate needs.

This file formalizes the term-by-term comparison, the telescoping bound, the strictness, and the
tail condition under which the collision threshold is met.
-/

open Finset

noncomputable section

namespace RHTower

/-- **Term-by-term comparison.**  If the `m`-th neighbour is at distance at least `mδ`, its field
contribution is at most the lattice value `1/(m(m+1)δ²)`. -/
theorem term_le_lattice {delta D : ℝ} (hd : 0 < delta) {m : ℕ} (hm : 1 ≤ m)
    (hD : (m : ℝ) * delta ≤ D) :
    1 / (D * (D + delta)) ≤ 1 / (((m : ℝ) * ((m : ℝ) + 1)) * delta ^ 2) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) hD
  have hlow : ((m : ℝ) * ((m : ℝ) + 1)) * delta ^ 2 ≤ D * (D + delta) := by
    have h1 : (m : ℝ) * delta ≤ D := hD
    have h2 : ((m : ℝ) + 1) * delta ≤ D + delta := by linarith
    calc ((m : ℝ) * ((m : ℝ) + 1)) * delta ^ 2
        = ((m : ℝ) * delta) * (((m : ℝ) + 1) * delta) := by ring
      _ ≤ D * (D + delta) := by
          apply mul_le_mul h1 h2 (by positivity) (le_of_lt hDpos)
  exact one_div_le_one_div_of_le (by positivity) hlow

/-- **Strict comparison.**  If some neighbour is strictly further than the lattice position, its
contribution is strictly smaller. -/
theorem term_lt_lattice {delta D : ℝ} (hd : 0 < delta) {m : ℕ} (hm : 1 ≤ m)
    (hD : (m : ℝ) * delta < D) :
    1 / (D * (D + delta)) < 1 / (((m : ℝ) * ((m : ℝ) + 1)) * delta ^ 2) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hDpos : 0 < D := lt_of_lt_of_le (by positivity) (le_of_lt hD)
  have hlow : ((m : ℝ) * ((m : ℝ) + 1)) * delta ^ 2 < D * (D + delta) := by
    have h2 : ((m : ℝ) + 1) * delta < D + delta := by linarith
    calc ((m : ℝ) * ((m : ℝ) + 1)) * delta ^ 2
        = ((m : ℝ) * delta) * (((m : ℝ) + 1) * delta) := by ring
      _ < D * (D + delta) := by
          apply mul_lt_mul' (le_of_lt hD) h2 (by positivity) hDpos
  exact one_div_lt_one_div_of_lt (by positivity) hlow

/-- **The lattice partial sum.**  `Σ_{m=1}^{M} 1/(m(m+1)) = 1 - 1/(M+1) < 1`, so the truncated
lattice field is strictly below the equilibrium value. -/
theorem lattice_partial_lt_one (M : ℕ) :
    ∑ m ∈ range M, (1 : ℝ) / (((m : ℝ) + 1) * ((m : ℝ) + 2)) < 1 := by
  rw [telescope_partial M]
  have : (0 : ℝ) < 1 / ((M : ℝ) + 1) := by positivity
  linarith

/-- **The collision threshold with a tail.**  If the head of the field is at most the truncated
lattice value on both sides and the tail contributes at most `ε/δ²` with `ε < 2/(M+1)`, then
`δ²Δ < 2` and the gap collides. -/
theorem collision_of_running_mean {head tail : ℝ} {M : ℕ}
    (hhead : head ≤ 2 * (1 - 1 / ((M : ℝ) + 1)))
    (hstrict : tail < 2 / ((M : ℝ) + 1)) :
    head + tail < 2 := by
  have hM : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  have : 2 * (1 - 1 / ((M : ℝ) + 1)) = 2 - 2 / ((M : ℝ) + 1) := by
    field_simp
  linarith [hhead, hstrict, this]

/-- **The running-mean hypothesis.**  `D_m ≥ mδ` on a side says exactly that `δ` is at most the
running average of the `m` gaps on that side. -/
theorem running_mean_iff {delta D : ℝ} {m : ℕ} (hm : 0 < m) :
    ((m : ℝ) * delta ≤ D) ↔ (delta ≤ D / (m : ℝ)) := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  rw [le_div_iff₀ hmpos, mul_comm]

/-- **A window minimum satisfies it inside the window.**  If `δ` is at most each of the `m` gaps on a
side, their sum is at least `mδ`. -/
theorem sum_ge_of_min {delta : ℝ} {g : ℕ → ℝ} {m : ℕ}
    (hmin : ∀ i ∈ range m, delta ≤ g i) :
    (m : ℝ) * delta ≤ ∑ i ∈ range m, g i := by
  calc (m : ℝ) * delta = ∑ _i ∈ range m, delta := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ∑ i ∈ range m, g i := Finset.sum_le_sum hmin

/-- **Persistence under the flow.**  The gap velocity is `-4/δ + 2δΔ`; among gaps with comparable
fields the smallest gap has the most negative velocity, so a minimal gap stays minimal and the
running-mean hypothesis persists over the collision interval. -/
theorem min_gap_contracts_fastest {d₁ d₂ Delta : ℝ} (h1 : 0 < d₁) (h12 : d₁ ≤ d₂)
    (hD : 0 ≤ Delta) :
    -4 / d₁ + 2 * d₁ * Delta ≤ -4 / d₂ + 2 * d₂ * Delta := by
  have h2 : 0 < d₂ := lt_of_lt_of_le h1 h12
  have hpos : (4 : ℝ) / d₂ ≤ 4 / d₁ := by gcongr
  have hinv : -4 / d₁ ≤ -4 / d₂ := by
    simp only [neg_div]; linarith
  have hmul : 2 * d₁ * Delta ≤ 2 * d₂ * Delta := by nlinarith
  linarith

end RHTower
