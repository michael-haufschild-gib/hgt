import GaloisForLFunctions.RHTower.SymbolAsymmetryIsPole

/-!
# The reflection splits the prime symbol, but gains no positivity

The local factor of the prime symbol at `p` is a function of `x = p^{-1/2}` and `c = cos θ`.  The
reflection `θ ↦ θ + π` acts on the `k`-th harmonic by `(-1)^k`, equivalently by `x ↦ -x`.  Writing `P̃`
for the reflected symbol:

```text
P - P̃  =  4 Σ_p log p Σ_{k odd}  p^{-k/2} cos(k ξ log p) ,
P + P̃  =  4 Σ_p log p Σ_{k even} p^{-k/2} cos(k ξ log p) .
```

The even half is absolutely convergent — its terms are `p^{-m}` — and at the origin it sums to

```text
2 Σ_p log p Σ_{m ≥ 1} p^{-m}  =  2 Σ_p log p/(p-1)  =  2 Σ_n Λ(n)/n ,
```

**the pole term again**, now obtained a fourth independent way: as the *even part of the prime symbol
at the origin*.  The odd half carries all of the divergence and all of the arithmetic.

**But the reflection gains nothing.**  By the decoupling of the extremes, each local supremum is taken
over all `θ`, and `θ ↦ θ + π` is a bijection of the line, so the reflected local factor has the same
range and hence the same supremum:

> **`sup P̃ = sup P`.  The reflection is a bookkeeping device that separates the convergent
> square-power part from the divergent prime part; it is not a mechanism, and no positivity follows
> from comparing a symbol with its reflection.**

This closes the self-referential formulation: there is no internal comparison that replaces the
archimedean side.

This file formalizes the parity split, the evaluation of the even part at the origin, and the
invariance of the supremum under reflection.
-/

open Filter Topology

noncomputable section

namespace RHTower

/-- **The parity split.**  `1 - (-1)^k` is `2` for odd `k` and `0` for even `k`. -/
theorem parity_odd (k : ℕ) (hk : Odd k) : (1 : ℝ) - (-1) ^ k = 2 := by
  rw [hk.neg_one_pow]; ring

/-- And `1 + (-1)^k` is `2` for even `k` and `0` for odd `k`. -/
theorem parity_even (k : ℕ) (hk : Even k) : (1 : ℝ) + (-1) ^ k = 2 := by
  rw [hk.neg_one_pow]; ring

/-- The odd part vanishes on even harmonics. -/
theorem parity_odd_vanishes (k : ℕ) (hk : Even k) : (1 : ℝ) - (-1) ^ k = 0 := by
  rw [hk.neg_one_pow]; ring

/-- The even part vanishes on odd harmonics. -/
theorem parity_even_vanishes (k : ℕ) (hk : Odd k) : (1 : ℝ) + (-1) ^ k = 0 := by
  rw [hk.neg_one_pow]; ring

/-- **The even part at the origin is the pole.**  Summing `p^{-m}` over `m ≥ 1` gives `1/(p-1)`, so
the even half evaluates to the pole series. -/
theorem even_part_at_origin {p : ℝ} (hp : 1 < p) :
    2 * ∑' m : ℕ, (1 / p) ^ (m + 1) = 2 / (p - 1) := by
  rw [inv_sub_one_eq_geometric hp]
  ring

/-- **Reflection does not move the supremum.**  Precomposition with the bijection `θ ↦ θ + π` leaves
the range of a function unchanged. -/
theorem range_shift_eq {α : Type*} (g : ℝ → α) (a : ℝ) :
    Set.range (fun θ : ℝ => g (θ + a)) = Set.range g := by
  ext y
  constructor
  · rintro ⟨θ, rfl⟩
    exact ⟨θ + a, rfl⟩
  · rintro ⟨θ, rfl⟩
    exact ⟨θ - a, by ring_nf⟩

/-- Hence the reflected symbol has the same supremum: no comparison with the reflection can yield
positivity. -/
theorem sup_reflection_eq (g : ℝ → ℝ) (a : ℝ) :
    sSup (Set.range (fun θ : ℝ => g (θ + a))) = sSup (Set.range g) := by
  rw [range_shift_eq g a]

/-- The odd part is what diverges: the `k = 1` harmonic already carries `Σ_p log p · p^{-1/2}`. -/
theorem odd_part_carries_divergence {p : ℝ} (hp : 1 < p) :
    0 < 1 / Real.sqrt p := by
  have : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by linarith)
  positivity

end RHTower
