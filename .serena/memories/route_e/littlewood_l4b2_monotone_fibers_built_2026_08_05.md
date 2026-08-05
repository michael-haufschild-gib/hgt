# L4b-ii built: monotone-fibre interval splitting (2026-08-05)

`formal/GaloisForLFunctions/RHTower/Sieve/MonotoneFibers.lean` — wired, built (8693 jobs),
axioms clean, zero warnings. `KuzminLandauInterval.lean` span weakened to `Icc x₀ (x₀+M)`
(the D2 fibres only control g' up to the last sample point) and re-audited clean.

Contents (namespace `RHTower.Sieve`):
- `sum_eq_sum_image_fibers`, `norm_sum_le_sum_image_fibers` — split ∑_{n<N} f n over fibres
  of any K : ℕ → ℤ (`Finset.sum_fiberwise_of_maps_to`).
- `filter_eq_Ico_of_monotone` — hypothesis is the *localized* monotonicity
  `∀ a b, a ≤ b → b < N → K a ≤ K b` (NOT `Monotone K`); fibre = `Ico min' (max'+1)`.
- `card_image_le_of_monotone` (needs `1 ≤ N`) — `(card image : ℝ) ≤ (K(N−1) − K 0 : ℤ) + 1`.

## Lean traps
- `Int.toNat_of_nonneg` bridge to ℝ: `push_cast at this ⊢` mangles the `toNat` coercion
  inconsistently between hypothesis and goal (linarith then fails). Fix: lift the ℤ-equation
  first via `exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h`, then `rw`, `push_cast; ring`.
- `Int.card_Icc` gives `(b + 1 - a).toNat`; combine with `Finset.card_le_card` of
  `image ⊆ Icc (K 0) (K (N-1))`.

## Next: L4b-iii, the (D2) assembly (design frozen)
Region index `I(y) = ⌊y−δ⌋ + ⌊y+δ⌋`, monotone in y ⇒ `K n := I (g' (x₀+n))` satisfies the
localized monotonicity when g' is monotone on the span. Even value v = band
`[m+δ, m+1−δ)`, m = v/2 → `kuzminLandau_interval` per fibre (≤ 3/(2δ)+1 each). Odd value =
gap → fibre card ≤ 2δ/λ + 1 from the g''-slope lower bound λ at the fibre's integer
endpoints (no measure theory). Value count ≤ 2Nhλ + 3 via `card_image_le_of_monotone`
(I(g'(x₀+N−1)) − I(g'(x₀)) ≤ 2·variation + 2). δ = √λ/2. Target: ‖S‖ ≤ 12hN√λ + 18/√λ
for λ ≤ g'' ≤ hλ.
