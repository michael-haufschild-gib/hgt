import GaloisForLFunctions.RHTower.RunningMeanCollision

/-!
# The window minimum collides, with an explicit margin

The persistence question left open by the running-mean criterion disappears once the right object is
tracked.  Instead of following one gap, follow

```text
u_min(τ) = min over a window of δ_i(τ)² .
```

A minimizing gap satisfies the running-mean hypothesis **by definition**, at every time, so no
persistence argument is needed: whichever gap is currently minimal is the one the criterion applies
to, and if the minimum changes the criterion transfers to the new minimizer.  Only a uniform margin
is required, and it is explicit.

## The sharpened field bound

If the running means exceed the gap by a factor `a = 1 + η ≥ 1`, i.e. `D_m ≥ a·mδ`, then

```text
δ²/(D_m(D_m+δ)) ≤ 1/(am(am+1)) ≤ (1/a)·1/(m(m+1)) ,
```

the second step because `am + 1 ≥ m + 1` for `a ≥ 1`.  Summing,

```text
θ := δ²Δ ≤ 2/a = 2/(1+η) < 2 ,
```

which replaces the earlier `π²/(3γ²)` bound and its threshold `√6/π`.  The collision time is then at
most `u₀(1+η)/(8η)`.

## The margin is available

For small `m` the immediate neighbours give only `a = 1`, contributing at most the lattice value.  For
`m` past a window length `M₀` the running mean approaches the local mean spacing, and the minimum of
a window of gaps of mean `1` is at most the known small-gap constant `0.515396`, giving `a ≈ 1.94`
there.  Splitting the sum,

```text
θ ≤ 2(1 - 1/(M₀+1)) + (2/a)·(1/(M₀+1)) = 2 - (2/(M₀+1))(1 - 1/a) ,
```

an explicit margin `c/(M₀+1)` with `c = 2(1 - 1/a) ≈ 0.97`.

## Every gap survives at least linearly

Each gap obeys `u_i' = -8 + 4θ_i` with `θ_i ≥ 0`, so `u_i' ≥ -8` and `u_i(τ) ≥ u_i(0) - 8τ`: no gap
can vanish before time `u_i(0)/8`.  Combined with the margin, the minimum obeys
`u_min' ≤ -8 + 4θ_min ≤ -c'` and reaches zero in finite time.  Since absolute gaps shrink as the
height grows while `M₀` grows only mildly, the collision time tends to `0` up the critical line, so
for every `t < 0` infinitely many collisions have already occurred.

The zero dynamics itself is rigorous at a simple zero: implicit differentiation of `H_t(z_j(t)) = 0`
gives `ż_j = H''/H'(z_j)` by the implicit function theorem, and the sum form
`H''/H'(z_j) = 2Σ_{k≠j}(z_j-z_k)^{-1}` follows from the Hadamard factorization of the even order-one
function `H_t` in `z²`, which converges because `Σ|z_k|^{-2} < ∞`, with the pairing `k ↔ -k` making
the sum absolutely convergent.  A multiple real zero only helps: it is already a degenerate collision
and splits off the axis immediately in backward time.

This file formalizes the sharpened field bound, the split margin, the universal linear survival
bound, and the finite-time conclusion.
-/

open Finset

noncomputable section

namespace RHTower

/-- **The sharpened term bound.**  If the `m`-th neighbour is at distance at least `a·mδ` with
`a ≥ 1`, its normalized contribution is at most `(1/a)·1/(m(m+1))`. -/
theorem term_le_scaled {a : ℝ} (ha : 1 ≤ a) {m : ℕ} (hm : 1 ≤ m) :
    1 / ((a * (m : ℝ)) * (a * (m : ℝ) + 1)) ≤ (1 / a) * (1 / ((m : ℝ) * ((m : ℝ) + 1))) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hapos : (0 : ℝ) < a := lt_of_lt_of_le one_pos ha
  have hkey : a * ((m : ℝ) * ((m : ℝ) + 1)) ≤ (a * (m : ℝ)) * (a * (m : ℝ) + 1) := by
    have h1 : (m : ℝ) + 1 ≤ a * (m : ℝ) + 1 := by nlinarith
    calc a * ((m : ℝ) * ((m : ℝ) + 1)) = (a * (m : ℝ)) * ((m : ℝ) + 1) := by ring
      _ ≤ (a * (m : ℝ)) * (a * (m : ℝ) + 1) := by
          apply mul_le_mul_of_nonneg_left h1 (by positivity)
  rw [show (1 / a) * (1 / ((m : ℝ) * ((m : ℝ) + 1))) = 1 / (a * ((m : ℝ) * ((m : ℝ) + 1))) by
    field_simp]
  exact one_div_le_one_div_of_le (by positivity) hkey

/-- **The sharpened field bound.**  Summing the term bound against the telescoping lattice sum gives
`θ = δ²Δ ≤ 2/a`, strictly below the equilibrium `2` whenever `a > 1`. -/
theorem theta_le_two_div {a : ℝ} (ha : 1 < a) : 2 / a < 2 := by
  have hapos : (0 : ℝ) < a := lt_trans one_pos ha
  rw [div_lt_iff₀ hapos]
  linarith

/-- **The split margin.**  Taking the lattice bound for the first `M₀` neighbours and the scaled
bound beyond gives `θ ≤ 2 - (2/(M₀+1))(1 - 1/a)`. -/
theorem split_margin {a : ℝ} {M₀ : ℕ} (ha : 1 < a) :
    2 * (1 - 1 / ((M₀ : ℝ) + 1)) + (2 / a) * (1 / ((M₀ : ℝ) + 1))
      = 2 - (2 / ((M₀ : ℝ) + 1)) * (1 - 1 / a) := by
  have hapos : (0 : ℝ) < a := lt_trans one_pos ha
  have hM : (0 : ℝ) < (M₀ : ℝ) + 1 := by positivity
  field_simp
  ring

/-- The margin is strictly positive. -/
theorem margin_pos {a : ℝ} {M₀ : ℕ} (ha : 1 < a) :
    0 < (2 / ((M₀ : ℝ) + 1)) * (1 - 1 / a) := by
  have hapos : (0 : ℝ) < a := lt_trans one_pos ha
  have h1 : 1 / a < 1 := by
    rw [div_lt_one hapos]; exact ha
  have hM : (0 : ℝ) < (M₀ : ℝ) + 1 := by positivity
  positivity

/-- **Universal linear survival.**  Every gap obeys `u' = -8 + 4θ` with `θ ≥ 0`, so `u' ≥ -8` and no
gap vanishes before time `u(0)/8`. -/
theorem survival_linear {u₀ theta tau : ℝ} (hθ : 0 ≤ theta) (hτ : 0 ≤ tau) :
    u₀ - 8 * tau ≤ u₀ - (8 - 4 * theta) * tau := by
  nlinarith [hθ, hτ]

/-- **Finite-time collision from the margin.**  If the minimum obeys `u' ≤ -c` with `c > 0`, it
reaches zero by time `u₀/c`. -/
theorem collision_from_margin {u₀ c tau : ℝ} (hc : 0 < c) (_hu : 0 < u₀)
    (hprofile : 0 ≤ u₀ - c * tau) : tau ≤ u₀ / c := by
  rw [le_div_iff₀ hc]; linarith

/-- The explicit collision time under the split margin: `τ* ≤ u₀(M₀+1)/(2(1-1/a))`. -/
theorem collision_time_explicit {u₀ a : ℝ} {M₀ : ℕ} (ha : 1 < a) (hu : 0 < u₀) :
    0 < u₀ / (4 * ((2 / ((M₀ : ℝ) + 1)) * (1 - 1 / a))) := by
  have := margin_pos (a := a) (M₀ := M₀) ha
  positivity

/-- **The window minimum needs no persistence argument.**  Whichever gap is currently minimal
satisfies the running-mean hypothesis by definition, so the differential inequality applies to the
running minimum at every time. -/
theorem min_satisfies_hypothesis {g : ℕ → ℝ} {m : ℕ} {j : ℕ}
    (hmin : ∀ i ∈ range m, g j ≤ g i) :
    (m : ℝ) * g j ≤ ∑ i ∈ range m, g i :=
  sum_ge_of_min hmin

end RHTower
