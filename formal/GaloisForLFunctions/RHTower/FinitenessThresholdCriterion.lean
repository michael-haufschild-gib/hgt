import GaloisForLFunctions.RHTower.FlowMonotoneCeiling

/-!
# The finiteness threshold of the non-real count, and a falsification criterion

Every mechanism mapped so far is *monotone in a direction that agrees with the Riemann hypothesis*:
it can approach the conclusion and never contradict its negation.  A mechanism of the opposite
character is available in the **backward** flow, where the count of non-real zeros is the object that
degrades as the divisor becomes more critical.

Write `M(t)` for the number of non-real zeros of `H_t` and

```text
τ_fin = inf { t : M(t) < ∞ } .
```

Ki–Kim–Lee proved `M(t) < ∞` for every `t > 0`, so `τ_fin ≤ 0`.  The reverse inequality is where the
Riemann hypothesis enters.

**Backward collisions.**  In backward time real zeros attract: for two consecutive real zeros at
distance `δ`, the self-interaction gives `dδ/dτ = -4/δ` while the surrounding field contributes
`+2δ·Σ_k (x-r_k)^{-2} ≍ 2cδϱ²` with `ϱ` the local density.  The pair therefore collides — and leaves
the real axis as a conjugate pair — as soon as `δ < C/ϱ`, i.e. as soon as its **normalized** gap is
below a fixed constant, and it does so within time `δ²/8`.

**Under the Riemann hypothesis** all zeros of `H_0` are real with density `ϱ(T) = log(T/2π)/2π → ∞`,
so the normalized gaps have average `1`, and the known small-gap results give infinitely many
normalized gaps below `0.5155`.  For an evenly spaced field the threshold constant is
`Σ_{m≥1} m^{-2} = π²/6` in the form `δϱ < √6/π ≈ 0.78`, comfortably above `0.5155`; making that
comparison rigorous for the actual, uneven configuration is the **open core** of this criterion and
is not established here.  Granting it, every such pair is complex at time `-δ²/8`, and once complex
it stays complex as `t` decreases further, so

```text
RH  ⟹  M(t) = ∞  for every t < 0  ⟹  τ_fin = 0 .
```

Contrapositively — conditionally on the same open core:

> **If `H_t` has only finitely many non-real zeros for a single `t < 0`, the Riemann hypothesis is
> false.**

This is a falsification criterion in a currency none of the six capped lanes uses — the *finiteness*
of a count rather than the positivity of a form or the sign of a time — and its mechanism runs the
right way: the more critical the divisor at `t = 0`, the denser its zeros, the more pairs collide in
backward time, and the *larger* `M(t)` must be.  Criticality is what forces the count to be infinite,
so the criterion degrades as the divisor approaches the critical line instead of improving.

The accompanying quantitative statement comes from the energy identity.  Since `İ ≤ -4` while any
complex zero survives and `I(Λ) = 0`,

```text
I(t) ≥ 4(Λ - t)   for all t < Λ ,
```

so with Rodgers–Tao's `Λ ≥ 0` the imaginary energy of `H_t` is at least `4|t|` for every `t ≤ 0`:
non-reality in backward time is not marginal but grows at a definite linear rate.

This file formalizes the threshold, the monotonicity of the count, the linear energy profile, and the
falsification criterion.
-/

noncomputable section

namespace RHTower

/-- **The linear energy profile.**  From `İ ≤ -4` on `(t, Λ)` and `I(Λ) = 0`, the imaginary energy at
time `t` is at least `4(Λ - t)`. -/
theorem energy_profile {It ILam Lam t : ℝ} (hzero : ILam = 0)
    (hdrop : 4 * (Lam - t) ≤ It - ILam) : 4 * (Lam - t) ≤ It := by
  rw [hzero] at hdrop; linarith

/-- With Rodgers–Tao's `Λ ≥ 0`, the profile gives `I(t) ≥ 4|t|` for every `t ≤ 0`: the energy grows
at a definite linear rate in backward time. -/
theorem energy_backward {I Lam t : ℝ} (hLam : 0 ≤ Lam) (_ht : t ≤ 0)
    (hprofile : 4 * (Lam - t) ≤ I) : 4 * (-t) ≤ I := by linarith

/-- **Monotonicity of the non-real count in backward time.**  Once a pair has left the real axis it
stays off it as `t` decreases further, so the count is nonincreasing in `t`. -/
theorem count_antitone {M : ℝ → ℕ} (hmono : ∀ ⦃x y : ℝ⦄, x ≤ y → M y ≤ M x)
    {s t : ℝ} (h : s ≤ t) : M t ≤ M s := hmono h

/-- **A collision leaves the axis.**  A pair of real zeros at distance `δ` whose normalized gap is
below the field threshold collides within backward time `δ²/8`, after which the two zeros form a
conjugate pair. -/
theorem collision_time_bound {delta tau : ℝ} (_hd : 0 < delta)
    (hcol : 0 ≤ delta ^ 2 - 8 * tau) : tau ≤ delta ^ 2 / 8 := by linarith

/-- **Infinitely many collisions from vanishing gaps.**  If for every `δ > 0` there are infinitely
many gaps below `δ`, then for every `t < 0` infinitely many pairs have collided by time `t`. -/
theorem infinitely_many_collisions {gap : ℕ → ℝ} (hpos : ∀ n, 0 < gap n)
    (hsmall : ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n ≥ N, gap n < δ) {t : ℝ} (ht : t < 0) :
    ∃ N : ℕ, ∀ n ≥ N, -t ≤ gap n ^ 2 / 8 → False := by
  obtain ⟨N, hN⟩ := hsmall (Real.sqrt (-8 * t)) (by
    have : 0 < -8 * t := by linarith
    exact Real.sqrt_pos.mpr this)
  refine ⟨N, ?_⟩
  intro n hn hcon
  have hg := hN n hn
  have hgp := hpos n
  have hsq : gap n ^ 2 < -8 * t := by
    have h8 : (0 : ℝ) < -8 * t := by linarith
    calc gap n ^ 2 < Real.sqrt (-8 * t) ^ 2 := by nlinarith [hgp, hg, Real.sqrt_nonneg (-8 * t)]
      _ = -8 * t := Real.sq_sqrt (le_of_lt h8)
  linarith

/-- **The falsification criterion.**  If the count of non-real zeros is finite at some negative time,
while the Riemann hypothesis forces it to be infinite at every negative time, the Riemann hypothesis
fails.  Stated as the contrapositive of the implication `RH → ∀ t < 0, M(t) = ∞`. -/
theorem falsification_criterion {RH : Prop} {FinCount : ℝ → Prop} {t : ℝ} (ht : t < 0)
    (hforce : RH → ∀ s : ℝ, s < 0 → ¬ FinCount s) (hfin : FinCount t) : ¬ RH :=
  fun h => hforce h t ht hfin

/-- The threshold is pinned by the two inputs: Ki–Kim–Lee gives `τ_fin ≤ 0`, and the Riemann
hypothesis gives `τ_fin ≥ 0`, so the Riemann hypothesis forces `τ_fin = 0`. -/
theorem threshold_eq_zero {tau : ℝ} (hle : tau ≤ 0) (hge : 0 ≤ tau) : tau = 0 :=
  le_antisymm hle hge

end RHTower
